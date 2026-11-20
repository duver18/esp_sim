#include <ctype.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/gpio.h"
#include "driver/uart.h"
#include "esp_log.h"
#include "esp_err.h"
#include "mqtt_secrets.h"

#define MODEM_UART          UART_NUM_2
#define MODEM_RX            GPIO_NUM_16
#define MODEM_TX            GPIO_NUM_17
#define RELAY1_GPIO         GPIO_NUM_25
#define RELAY2_GPIO         GPIO_NUM_26

// Configura tras verificar el módulo con carga de baja tensión: 1=activo HIGH,
// 0=activo LOW. El valor inicial es HIGH y debe confirmarse antes de conectar
// el módulo de relés. Añade resistencias externas que mantengan el nivel OFF
// durante el arranque, cuando los GPIO aún son entradas.
#ifndef RELAY_ACTIVE_LEVEL
#define RELAY_ACTIVE_LEVEL 1
#endif
#define RELAY_OFF_LEVEL (RELAY_ACTIVE_LEVEL ? 0 : 1)
#define AUTHORIZED_NUMBER "+573058020199"
#define MQTT_HOST "k226c23b.ala.eu-central-1.emqxsl.com"
#define MQTT_PORT 8883
#define MQTT_COMMAND_TOPIC "esp_sim/relays/cmd"
#define MQTT_STATE_TOPIC "esp_sim/relays/state"
#define MQTT_ACK_TOPIC "esp_sim/relays/ack"
#define MQTT_RETRY_MS 30000
#define MODEM_BAUD 115200
#define MODEM_LINE_CAP 256
#define AT_TIMEOUT_MS 4000
#define REG_POLL_MS 15000
// Modo temporal de pruebas: cualquier móvil colombiano normalizado puede
// controlar los relés por SMS o llamada. Volver a 0 al terminar las pruebas.
#define TEMP_ALLOW_ANY_CONTROL 1

static const char *TAG = "esp_sim";
extern const uint8_t emqxsl_ca_pem_start[] asm("_binary_emqxsl_ca_pem_start");
extern const uint8_t emqxsl_ca_pem_end[] asm("_binary_emqxsl_ca_pem_end");
static bool relay1_on;
static bool relay2_on;
static bool modem_armed;
static bool mqtt_connected;
static bool mqtt_started;
static bool mqtt_client_acquired;
static bool mqtt_certificate_uploaded;
static bool mqtt_state_publish_pending;
static bool mqtt_topic_next;
static bool mqtt_payload_next;
static bool suppress_at_error_log;
static bool log_data_profile_lines;
static bool log_at_response_lines;
static bool sms_body_next;
static bool call_seen;
static bool call_clip_handled;
static bool authorized_call_pending;
static bool unauthorized_call_pending;
static char sms_sender[32];
static char sms_reply_to[16];
static char sms_reply[160];
static char mqtt_rx_topic[128];
static char mqtt_rx_payload[160];
static char mqtt_ack_pending[96];
static size_t mqtt_rx_topic_used;
static size_t mqtt_rx_payload_used;
static char rx_line[MODEM_LINE_CAP];
static size_t rx_used;

static void set_relay_states(bool light1, bool light2)
{
    relay1_on = light1;
    relay2_on = light2;
    gpio_set_level(RELAY1_GPIO, light1 ? RELAY_ACTIVE_LEVEL : RELAY_OFF_LEVEL);
    gpio_set_level(RELAY2_GPIO, light2 ? RELAY_ACTIVE_LEVEL : RELAY_OFF_LEVEL);
    mqtt_state_publish_pending = true;
    ESP_LOGI(TAG, "Relés: luz1=%s, luz2=%s", light1 ? "ON" : "OFF",
             light2 ? "ON" : "OFF");
}

static void init_relays(void)
{
    // Cargar el nivel apagado antes de habilitar la salida.
    gpio_set_level(RELAY1_GPIO, RELAY_OFF_LEVEL);
    gpio_set_level(RELAY2_GPIO, RELAY_OFF_LEVEL);
    const gpio_config_t io = {
        .pin_bit_mask = (1ULL << RELAY1_GPIO) | (1ULL << RELAY2_GPIO),
        .mode = GPIO_MODE_OUTPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE
    };
    ESP_ERROR_CHECK(gpio_config(&io));
    set_relay_states(false, false);
}

// Normaliza números móviles colombianos en formato internacional o local,
// quitando espacios, guiones y paréntesis. La autorización se compara aparte.
static bool normalize_number(const char *src, char *dst, size_t cap)
{
    char digits[24];
    size_t n = 0;
    if (!src) return false;
    while (*src && n < sizeof(digits) - 1) {
        if (isdigit((unsigned char)*src)) digits[n++] = *src;
        else if (*src != '+' && *src != ' ' && *src != '-' && *src != '(' &&
                 *src != ')' && *src != '\t') return false;
        ++src;
    }
    if (*src) return false;
    digits[n] = '\0';
    const char *national = digits;
    if (n == 12 && digits[0] == '5' && digits[1] == '7') national += 2;
    if (strlen(national) != 10 || national[0] != '3' || cap < 13) return false;
    snprintf(dst, cap, "+57%s", national);
    return true;
}

static int registration_stat(const char *line)
{
    const char *p = strchr(line, ':');
    if (!p) return -1;
    ++p;
    while (isspace((unsigned char)*p)) ++p;
    char *end = NULL;
    long first = strtol(p, &end, 10);
    if (end == p) return -1;
    p = end;
    while (isspace((unsigned char)*p)) ++p;
    if (*p == ',') {
        ++p;
        while (isspace((unsigned char)*p)) ++p;
        char *second_end = NULL;
        long second = strtol(p, &second_end, 10);
        // Respuesta a AT+CEREG? lleva <n>,<stat>; la notificación suele
        // llevar <stat>,"<tac>". Solo la primera forma tiene dos enteros.
        if (second_end != p) return (int)second;
    }
    return (int)first;
}

static void trim(char *s)
{
    size_t n = strlen(s);
    while (n && isspace((unsigned char)s[n - 1])) s[--n] = '\0';
    size_t start = 0;
    while (s[start] && isspace((unsigned char)s[start])) ++start;
    if (start) memmove(s, s + start, strlen(s + start) + 1);
}

static void queue_sms_reply(const char *recipient, const char *msg)
{
    snprintf(sms_reply_to, sizeof(sms_reply_to), "%s", recipient);
    snprintf(sms_reply, sizeof(sms_reply), "%s", msg);
}

static void handle_sms(const char *sender, const char *body)
{
    char normalized[16];
    if (!normalize_number(sender, normalized, sizeof(normalized))) {
        ESP_LOGW(TAG, "SMS ignorado: formato de remitente no válido");
        return;
    }
    char cmd[MODEM_LINE_CAP];
    snprintf(cmd, sizeof(cmd), "%s", body);
    trim(cmd);
    for (char *p = cmd; *p; ++p) *p = (char)toupper((unsigned char)*p);
#if TEMP_ALLOW_ANY_CONTROL
    const bool may_control = true;
#else
    const bool may_control = strcmp(normalized, AUTHORIZED_NUMBER) == 0;
#endif
    if (!may_control) {
        ESP_LOGW(TAG, "SMS ignorado: remitente no autorizado para cambiar relés");
        return;
    }
    if (!modem_armed) {
        queue_sms_reply(normalized, "Sistema sin registro celular; salidas bloqueadas.");
        return;
    }
    if (!strcmp(cmd, "ON1")) set_relay_states(true, relay2_on);
    else if (!strcmp(cmd, "OFF1")) set_relay_states(false, relay2_on);
    else if (!strcmp(cmd, "ON2")) set_relay_states(relay1_on, true);
    else if (!strcmp(cmd, "OFF2")) set_relay_states(relay1_on, false);
    else if (!strcmp(cmd, "ALLON")) set_relay_states(true, true);
    else if (!strcmp(cmd, "ALLOFF")) set_relay_states(false, false);
    else if (!strcmp(cmd, "STATUS")) {
        char status[96];
        snprintf(status, sizeof(status), "Luz1=%s; Luz2=%s",
                 relay1_on ? "ON" : "OFF", relay2_on ? "ON" : "OFF");
        queue_sms_reply(normalized, status);
        return;
    } else {
        ESP_LOGW(TAG, "Comando SMS no reconocido");
        return;
    }
    char result[96];
    snprintf(result, sizeof(result), "Comando aplicado. Luz1=%s; Luz2=%s",
             relay1_on ? "ON" : "OFF", relay2_on ? "ON" : "OFF");
    queue_sms_reply(normalized, result);
}

static bool parse_quoted_number(const char *line, char *out, size_t cap)
{
    const char *a = strchr(line, '"');
    if (!a) return false;
    const char *b = strchr(a + 1, '"');
    if (!b || (size_t)(b - a - 1) >= cap) return false;
    memcpy(out, a + 1, (size_t)(b - a - 1));
    out[b - a - 1] = '\0';
    return true;
}

static void handle_mqtt_message(void)
{
    if (strcmp(mqtt_rx_topic, MQTT_COMMAND_TOPIC) != 0) return;
    trim(mqtt_rx_payload);
    for (char *p = mqtt_rx_payload; *p; ++p) *p = (char)toupper((unsigned char)*p);
    if (!modem_armed) {
        snprintf(mqtt_ack_pending, sizeof(mqtt_ack_pending), "ERROR: sin registro celular");
        return;
    }
    if (!strcmp(mqtt_rx_payload, "ON1")) set_relay_states(true, relay2_on);
    else if (!strcmp(mqtt_rx_payload, "OFF1")) set_relay_states(false, relay2_on);
    else if (!strcmp(mqtt_rx_payload, "ON2")) set_relay_states(relay1_on, true);
    else if (!strcmp(mqtt_rx_payload, "OFF2")) set_relay_states(relay1_on, false);
    else if (!strcmp(mqtt_rx_payload, "ALLON")) set_relay_states(true, true);
    else if (!strcmp(mqtt_rx_payload, "ALLOFF")) set_relay_states(false, false);
    else if (strcmp(mqtt_rx_payload, "STATUS") != 0) {
        snprintf(mqtt_ack_pending, sizeof(mqtt_ack_pending), "ERROR: comando desconocido");
        return;
    }
    snprintf(mqtt_ack_pending, sizeof(mqtt_ack_pending), "OK: Luz1=%s; Luz2=%s",
             relay1_on ? "ON" : "OFF", relay2_on ? "ON" : "OFF");
}

static void append_mqtt_data(char *dst, size_t cap, size_t *used, const char *src)
{
    size_t n = strlen(src);
    if (n > cap - 1 - *used) n = cap - 1 - *used;
    memcpy(dst + *used, src, n);
    *used += n;
    dst[*used] = '\0';
}

// Interpreta notificaciones asíncronas; no ejecuta comandos AT aquí.
static void handle_line(char *line)
{
    trim(line);
    if (!line[0]) return;
    if (mqtt_topic_next) {
        mqtt_topic_next = false;
        append_mqtt_data(mqtt_rx_topic, sizeof(mqtt_rx_topic), &mqtt_rx_topic_used, line);
        return;
    }
    if (mqtt_payload_next) {
        mqtt_payload_next = false;
        append_mqtt_data(mqtt_rx_payload, sizeof(mqtt_rx_payload), &mqtt_rx_payload_used, line);
        return;
    }
    if (!strncmp(line, "+CMQTTRXSTART:", 13)) {
        mqtt_rx_topic[0] = '\0';
        mqtt_rx_payload[0] = '\0';
        mqtt_rx_topic_used = 0;
        mqtt_rx_payload_used = 0;
        return;
    }
    if (!strncmp(line, "+CMQTTRXTOPIC:", 14)) {
        mqtt_topic_next = true;
        return;
    }
    if (!strncmp(line, "+CMQTTRXPAYLOAD:", 16)) {
        mqtt_payload_next = true;
        return;
    }
    if (!strncmp(line, "+CMQTTRXEND:", 12)) {
        handle_mqtt_message();
        return;
    }
    if (!strncmp(line, "+CMQTTCONNLOST:", 15)) {
        mqtt_connected = false;
        ESP_LOGW(TAG, "Conexión MQTT perdida; se reintentará");
        return;
    }
    if (log_data_profile_lines &&
        (!strncmp(line, "+CGDCONT:", 9) || !strncmp(line, "+CGACT:", 7)))
        ESP_LOGI(TAG, "Perfil de datos del módem: %s", line);
    if (log_at_response_lines && strcmp(line, "OK") != 0)
        ESP_LOGI(TAG, "Respuesta AT de diagnóstico: %s", line);
    if (sms_body_next) {
        sms_body_next = false;
        handle_sms(sms_sender, line);
        sms_sender[0] = '\0';
        return;
    }
    if (!strncmp(line, "+CMT:", 5)) {
        sms_body_next = parse_quoted_number(line, sms_sender, sizeof(sms_sender));
        if (!sms_body_next) ESP_LOGW(TAG, "Cabecera SMS inválida; se descarta");
        return;
    }
    if (!strncmp(line, "+CMTI:", 6)) {
        // El modo configurado es entrega directa (+CNMI=2,2,...). No se lee
        // almacenamiento para evitar tocar mensajes ajenos al sistema.
        ESP_LOGW(TAG, "SMS almacenado +CMTI inesperado; no se borra ni se procesa");
        return;
    }
    if (!strcmp(line, "RING")) {
        if (!call_seen) {
            ESP_LOGI(TAG, "Llamada entrante; esperando identificador");
            call_seen = true;
            call_clip_handled = false;
        }
        return;
    }
    if (!strncmp(line, "+CLIP:", 6)) {
        char caller[32], normalized[16];
        if (call_clip_handled) return;
        call_seen = true;
        call_clip_handled = true;
        if (parse_quoted_number(line, caller, sizeof(caller)) &&
            normalize_number(caller, normalized, sizeof(normalized)) &&
            (TEMP_ALLOW_ANY_CONTROL || strcmp(normalized, AUTHORIZED_NUMBER) == 0))
            authorized_call_pending = true;
        else
            unauthorized_call_pending = true;
        return;
    }
    if (!strncmp(line, "+CEREG:", 7)) {
        int stat = registration_stat(line);
        modem_armed = (stat == 1 || stat == 5);
        if (!modem_armed) {
            if (relay1_on || relay2_on) set_relay_states(false, false);
            ESP_LOGW(TAG, "Módem sin registro celular (CEREG stat=%d)", stat);
        }
    }
    if (!suppress_at_error_log &&
        (!strcmp(line, "ERROR") || !strncmp(line, "+CME ERROR", 10)))
        ESP_LOGW(TAG, "El módem informó un error AT");
}

static bool read_line(char *out, size_t cap, uint32_t timeout_ms)
{
    const TickType_t start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(timeout_ms)) {
        uint8_t c;
        int n = uart_read_bytes(MODEM_UART, &c, 1, pdMS_TO_TICKS(100));
        if (n <= 0) continue;
        if (c == '\n') {
            rx_line[rx_used] = '\0';
            snprintf(out, cap, "%s", rx_line);
            rx_used = 0;
            if (out[0] == '\r') out[0] = '\0';
            return true;
        }
        if (c == '\r') continue;
        if (rx_used + 1 < sizeof(rx_line)) rx_line[rx_used++] = (char)c;
        else rx_used = 0;
    }
    return false;
}

static bool at_command(const char *cmd, const char *prefix, char *answer, size_t answer_cap)
{
    char line[MODEM_LINE_CAP];
    if (cmd) {
        ESP_LOGI(TAG, "AT -> %s", cmd);
        uart_write_bytes(MODEM_UART, cmd, strlen(cmd));
        uart_write_bytes(MODEM_UART, "\r\n", 2);
    }
    bool got_expected = (prefix == NULL);
    TickType_t start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(AT_TIMEOUT_MS)) {
        if (!read_line(line, sizeof(line), 250)) continue;
        handle_line(line);
        if (prefix && !strncmp(line, prefix, strlen(prefix))) {
            if (answer && answer_cap) snprintf(answer, answer_cap, "%s", line);
            got_expected = true;
        }
        if (!strcmp(line, "ERROR") || !strncmp(line, "+CME ERROR", 10)) {
            ESP_LOGW(TAG, "Respuesta AT del módem: %s", line);
            return false;
        }
        if (!strcmp(line, "OK")) return got_expected;
    }
    ESP_LOGW(TAG, "Tiempo de espera agotado para comando AT");
    return false;
}

static bool send_sms(const char *number, const char *text)
{
    char cmd[64], line[MODEM_LINE_CAP];
    snprintf(cmd, sizeof(cmd), "AT+CMGS=\"%s\"", number);
    uart_write_bytes(MODEM_UART, cmd, strlen(cmd));
    uart_write_bytes(MODEM_UART, "\r\n", 2);
    bool prompt = false;
    TickType_t start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(10000)) {
        uint8_t c;
        if (uart_read_bytes(MODEM_UART, &c, 1, pdMS_TO_TICKS(100)) <= 0) continue;
        if (c == '>') { prompt = true; break; }
        if (c == '\n') {
            rx_line[rx_used] = '\0';
            snprintf(line, sizeof(line), "%s", rx_line);
            rx_used = 0;
            handle_line(line);
        } else if (c != '\r' && rx_used + 1 < sizeof(rx_line)) rx_line[rx_used++] = (char)c;
    }
    if (!prompt) { ESP_LOGW(TAG, "No llegó el prompt de AT+CMGS"); return false; }
    uart_write_bytes(MODEM_UART, text, strlen(text));
    const uint8_t ctrl_z = 0x1A;
    uart_write_bytes(MODEM_UART, &ctrl_z, 1);
    bool sent = false;
    start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(30000)) {
        if (!read_line(line, sizeof(line), 250)) continue;
        handle_line(line);
        if (!strncmp(line, "+CMGS:", 6)) sent = true;
        if (!strcmp(line, "OK")) return sent;
        if (!strcmp(line, "ERROR") || !strncmp(line, "+CMS ERROR", 10)) return false;
    }
    return false;
}

static bool wait_for_prompt(uint32_t timeout_ms)
{
    TickType_t start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(timeout_ms)) {
        uint8_t c;
        if (uart_read_bytes(MODEM_UART, &c, 1, pdMS_TO_TICKS(100)) <= 0) continue;
        if (c == '>') return true;
        if (c == '\n') {
            rx_line[rx_used] = '\0';
            handle_line(rx_line);
            rx_used = 0;
        } else if (c != '\r' && rx_used + 1 < sizeof(rx_line)) {
            rx_line[rx_used++] = (char)c;
        }
    }
    return false;
}

static bool mqtt_input_data(const char *command, const void *data, size_t length)
{
    uart_write_bytes(MODEM_UART, command, strlen(command));
    uart_write_bytes(MODEM_UART, "\r\n", 2);
    if (!wait_for_prompt(10000)) {
        ESP_LOGW(TAG, "El módem no solicitó datos para el comando MQTT");
        return false;
    }
    if (uart_write_bytes(MODEM_UART, data, length) != (int)length) return false;
    return at_command(NULL, NULL, NULL, 0);
}

static bool mqtt_wait_urc_command(const char *command, const char *urc_prefix,
                                  const char *success_suffix, uint32_t timeout_ms)
{
    char line[MODEM_LINE_CAP];
    bool got_ok = false;
    bool got_success = false;
    ESP_LOGI(TAG, "AT -> comando MQTT (sin credenciales en el registro)");
    uart_write_bytes(MODEM_UART, command, strlen(command));
    uart_write_bytes(MODEM_UART, "\r\n", 2);
    TickType_t start = xTaskGetTickCount();
    while ((xTaskGetTickCount() - start) < pdMS_TO_TICKS(timeout_ms)) {
        if (!read_line(line, sizeof(line), 250)) continue;
        handle_line(line);
        if (!strcmp(line, "OK")) got_ok = true;
        if (urc_prefix && !strncmp(line, urc_prefix, strlen(urc_prefix)) &&
            success_suffix && strstr(line, success_suffix)) got_success = true;
        if (!strcmp(line, "ERROR") || !strncmp(line, "+CME ERROR", 10)) {
            ESP_LOGW(TAG, "Respuesta AT del módem durante MQTT: %s", line);
            return false;
        }
        if (got_ok && got_success) return true;
    }
    ESP_LOGW(TAG, "Tiempo de espera en respuesta MQTT del módem");
    return false;
}

static bool mqtt_upload_ca(void)
{
    if (mqtt_certificate_uploaded) return true;
    const size_t cert_len = strlen((const char *)emqxsl_ca_pem_start);
    char command[96];
    (void)at_command("AT+CCERTDELE=\"emqxsl-ca.pem\"", NULL, NULL, 0);
    snprintf(command, sizeof(command), "AT+CCERTDOWN=\"emqxsl-ca.pem\",%u",
             (unsigned)cert_len);
    uart_write_bytes(MODEM_UART, command, strlen(command));
    uart_write_bytes(MODEM_UART, "\r\n", 2);
    if (!wait_for_prompt(10000)) {
        ESP_LOGE(TAG, "No se pudo iniciar la carga del certificado CA al módem");
        return false;
    }
    if (uart_write_bytes(MODEM_UART, emqxsl_ca_pem_start, cert_len) != (int)cert_len ||
        !at_command(NULL, NULL, NULL, 0)) {
        ESP_LOGE(TAG, "Falló la carga del certificado CA al módem");
        return false;
    }
    mqtt_certificate_uploaded = true;
    ESP_LOGI(TAG, "Certificado CA de EMQX cargado al módem");
    return true;
}

static bool mqtt_send_topic_and_payload(const char *topic, const char *payload)
{
    char command[96];
    size_t topic_len = strlen(topic), payload_len = strlen(payload);
    snprintf(command, sizeof(command), "AT+CMQTTTOPIC=0,%u", (unsigned)topic_len);
    if (!mqtt_input_data(command, topic, topic_len)) return false;
    snprintf(command, sizeof(command), "AT+CMQTTPAYLOAD=0,%u", (unsigned)payload_len);
    if (!mqtt_input_data(command, payload, payload_len)) return false;
    return mqtt_wait_urc_command("AT+CMQTTPUB=0,0,60", "+CMQTTPUB: 0,", ",0", 30000);
}

static bool mqtt_publish_state(void)
{
    char payload[96];
    snprintf(payload, sizeof(payload), "{\"luz1\":\"%s\",\"luz2\":\"%s\"}",
             relay1_on ? "ON" : "OFF", relay2_on ? "ON" : "OFF");
    return mqtt_send_topic_and_payload(MQTT_STATE_TOPIC, payload);
}

static bool mqtt_publish_ack(void)
{
    return mqtt_send_topic_and_payload(MQTT_ACK_TOPIC, mqtt_ack_pending);
}

static bool mqtt_subscribe_commands(void)
{
    char command[96];
    size_t topic_len = strlen(MQTT_COMMAND_TOPIC);
    snprintf(command, sizeof(command), "AT+CMQTTSUBTOPIC=0,%u,1", (unsigned)topic_len);
    if (!mqtt_input_data(command, MQTT_COMMAND_TOPIC, topic_len)) return false;
    return mqtt_wait_urc_command("AT+CMQTTSUB=0,1", "+CMQTTSUB: 0,", ",0", 30000);
}

static void log_packet_data_status(void)
{
    char line[MODEM_LINE_CAP];
    log_at_response_lines = true;
    (void)at_command("AT+CGMR", NULL, NULL, 0);
    log_at_response_lines = false;
    if (at_command("AT+CGATT?", "+CGATT:", line, sizeof(line)))
        ESP_LOGI(TAG, "Adjunto a datos móviles: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+CGATT?");
    log_data_profile_lines = true;
    if (at_command("AT+CGDCONT?", "+CGDCONT:", line, sizeof(line)))
        ESP_LOGI(TAG, "Perfil APN/PDP: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+CGDCONT?");
    if (at_command("AT+CGACT?", "+CGACT:", line, sizeof(line)))
        ESP_LOGI(TAG, "Contexto PDP activo: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+CGACT?");
    if (at_command("AT+CGPADDR=1", "+CGPADDR:", line, sizeof(line)))
        ESP_LOGI(TAG, "Dirección IP de datos: %s", line);
    else
        ESP_LOGW(TAG, "El módem no informó una IP para el contexto PDP 1");
    log_data_profile_lines = false;
}

static void mqtt_stop(void)
{
    // El módem puede seguir alimentado cuando solo se reinicia la ESP32; su
    // servicio MQTT y el cliente pueden quedar activos aunque estas banderas
    // hayan vuelto a cero. Intenta limpiar siempre el estado remoto; se ignoran
    // los ERROR esperables cuando aún no había una sesión MQTT.
    suppress_at_error_log = true;
    (void)at_command("AT+CMQTTDISC=0,60", NULL, NULL, 0);
    mqtt_connected = false;
    (void)at_command("AT+CMQTTREL=0", NULL, NULL, 0);
    mqtt_client_acquired = false;
    (void)at_command("AT+CMQTTSTOP", NULL, NULL, 0);
    suppress_at_error_log = false;
    mqtt_started = false;
}

static bool mqtt_connect(void)
{
    char command[512];
    if (!modem_armed) return false;
    mqtt_stop();
    if (!mqtt_upload_ca()) return false;
    if (!mqtt_wait_urc_command("AT+CMQTTSTART", "+CMQTTSTART:", "0", 30000)) {
        ESP_LOGW(TAG, "AT+CMQTTSTART no inició el servicio; consultando estado de datos");
        log_packet_data_status();
        return false;
    }
    mqtt_started = true;
    if (!at_command("AT+CMQTTACCQ=0,\"esp_sim_esp32\",1", NULL, NULL, 0)) goto fail;
    mqtt_client_acquired = true;
    if (!at_command("AT+CSSLCFG=\"sslversion\",0,4", NULL, NULL, 0) ||
        !at_command("AT+CSSLCFG=\"authmode\",0,1", NULL, NULL, 0) ||
        !at_command("AT+CSSLCFG=\"cacert\",0,\"emqxsl-ca.pem\"", NULL, NULL, 0) ||
        !at_command("AT+CSSLCFG=\"enableSNI\",0,1", NULL, NULL, 0) ||
        !at_command("AT+CMQTTSSLCFG=0,0", NULL, NULL, 0)) goto fail;
    snprintf(command, sizeof(command),
             "AT+CMQTTCONNECT=0,\"tcp://%s:%d\",60,1,\"%s\",\"%s\"",
             MQTT_HOST, MQTT_PORT, MQTT_USERNAME, MQTT_PASSWORD);
    if (!mqtt_wait_urc_command(command, "+CMQTTCONNECT: 0,", ",0", 90000)) goto fail;
    mqtt_connected = true;
    if (!mqtt_subscribe_commands()) goto fail;
    mqtt_state_publish_pending = true;
    ESP_LOGI(TAG, "MQTT conectado a EMQX por TLS; suscrito a comandos");
    return true;
fail:
    ESP_LOGW(TAG, "No se pudo completar la conexión MQTT; se reintentará");
    mqtt_stop();
    return false;
}

static bool get_registration(void)
{
    char line[MODEM_LINE_CAP];
    if (!at_command("AT+CEREG?", "+CEREG:", line, sizeof(line))) return false;
    int stat = registration_stat(line);
    return stat == 1 || stat == 5;
}

static void service_pending(void)
{
    if (authorized_call_pending || unauthorized_call_pending) {
        bool authorized = authorized_call_pending;
        authorized_call_pending = false;
        unauthorized_call_pending = false;
        call_seen = false;
        (void)at_command("ATH", NULL, NULL, 0);
        if (authorized && modem_armed) {
            // En estados mixtos se apagan ambas luces para dejar un resultado
            // predecible y seguro; en estados iguales se invierte el conjunto.
            bool turn_on = !(relay1_on || relay2_on);
            set_relay_states(turn_on, turn_on);
            ESP_LOGI(TAG, "Llamada autorizada procesada una sola vez");
        } else if (!authorized) ESP_LOGW(TAG, "Llamada no autorizada rechazada");
    }
    if (sms_reply[0] && sms_reply_to[0]) {
        char reply[sizeof(sms_reply)];
        char recipient[sizeof(sms_reply_to)];
        snprintf(reply, sizeof(reply), "%s", sms_reply);
        snprintf(recipient, sizeof(recipient), "%s", sms_reply_to);
        sms_reply[0] = '\0';
        sms_reply_to[0] = '\0';
        if (!send_sms(recipient, reply)) ESP_LOGW(TAG, "No se pudo enviar SMS de confirmación");
    }
    if (mqtt_connected && mqtt_state_publish_pending) {
        mqtt_state_publish_pending = false;
        if (!mqtt_publish_state()) {
            mqtt_connected = false;
            ESP_LOGW(TAG, "No se pudo publicar el estado MQTT");
        }
    }
    if (mqtt_connected && mqtt_ack_pending[0]) {
        if (!mqtt_publish_ack()) {
            mqtt_connected = false;
            ESP_LOGW(TAG, "No se pudo publicar la confirmación MQTT");
        } else mqtt_ack_pending[0] = '\0';
    }
}

static bool init_modem(void)
{
    char line[MODEM_LINE_CAP];
    // El módem puede tardar varios segundos más que el ESP32 en arrancar.
    vTaskDelay(pdMS_TO_TICKS(8000));
    if (!at_command("AT", NULL, NULL, 0)) return false;
    (void)at_command("ATE0", NULL, NULL, 0);
    (void)at_command("AT+CMEE=2", NULL, NULL, 0);
    if (!at_command("AT+CPIN?", "+CPIN:", line, sizeof(line)) || !strstr(line, "READY")) {
        ESP_LOGE(TAG, "SIM no lista; revisa SIM y PIN");
        return false;
    }
    if (!at_command("AT+CMGF=1", NULL, NULL, 0)) return false;
    // Entrega SMS nuevos directamente por +CMT con encabezado y cuerpo.
    if (!at_command("AT+CNMI=2,2,0,0,0", NULL, NULL, 0)) return false;
    if (!at_command("AT+CLIP=1", NULL, NULL, 0)) return false;
    if (!at_command("AT+CEREG=2", NULL, NULL, 0)) return false;
    ESP_LOGI(TAG, "SIM lista (AT+CPIN? respondió READY)");
    if (!at_command("AT+CSQ", "+CSQ:", line, sizeof(line)))
        ESP_LOGW(TAG, "No se pudo consultar CSQ");
    else {
        int rssi = -1, ber = -1;
        if (sscanf(line, "+CSQ: %d,%d", &rssi, &ber) == 2) {
            if (rssi == 99) ESP_LOGW(TAG, "CSQ=99: señal desconocida/no válida");
            else ESP_LOGI(TAG, "CSQ RSSI=%d, BER=%d", rssi, ber);
        }
    }
    // Diagnóstico recomendado por SIMCom: función de radio, operador
    // seleccionado, bandas configuradas y registro de voz/GSM.
    if (at_command("AT+CFUN?", "+CFUN:", line, sizeof(line)))
        ESP_LOGI(TAG, "Estado de radio: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+CFUN?");
    if (at_command("AT+COPS?", "+COPS:", line, sizeof(line)))
        ESP_LOGI(TAG, "Operador seleccionado: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+COPS?");
    if (at_command("AT+CBAND?", "+CBAND:", line, sizeof(line)))
        ESP_LOGI(TAG, "Bandas configuradas: %s", line);
    else
        ESP_LOGW(TAG, "AT+CBAND? no disponible o sin respuesta");
    if (at_command("AT+CREG?", "+CREG:", line, sizeof(line)))
        ESP_LOGI(TAG, "Registro de red GSM: %s", line);
    else
        ESP_LOGW(TAG, "No se pudo consultar AT+CREG?");
    modem_armed = get_registration();
    if (!modem_armed) ESP_LOGW(TAG, "Sin registro de red; relés bloqueados hasta registrarse");
    else ESP_LOGI(TAG, "Módem registrado en red celular");
    return true;
}

void app_main(void)
{
    init_relays();
    const uart_config_t config = {
        .baud_rate = MODEM_BAUD,
        .data_bits = UART_DATA_8_BITS,
        .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
        .source_clk = UART_SCLK_DEFAULT
    };
    ESP_ERROR_CHECK(uart_driver_install(MODEM_UART, 2048, 0, 0, NULL, 0));
    ESP_ERROR_CHECK(uart_param_config(MODEM_UART, &config));
    ESP_ERROR_CHECK(uart_set_pin(MODEM_UART, MODEM_TX, MODEM_RX,
                                 UART_PIN_NO_CHANGE, UART_PIN_NO_CHANGE));
    ESP_LOGI(TAG, "Consola ESP-IDF por UART0; módem dedicado a UART2 GPIO16/17");

    TickType_t last_reg_check = 0;
    TickType_t last_mqtt_attempt = xTaskGetTickCount() - pdMS_TO_TICKS(MQTT_RETRY_MS);
    bool modem_ready = init_modem();
    for (;;) {
        service_pending();
        char line[MODEM_LINE_CAP];
        if (read_line(line, sizeof(line), 100)) handle_line(line);
        service_pending();

        TickType_t now = xTaskGetTickCount();
        if (!modem_ready) {
            // Recuperación moderada: reintenta la inicialización, sin reinicios
            // eléctricos ni bucles rápidos sobre el módem.
            vTaskDelay(pdMS_TO_TICKS(10000));
            modem_ready = init_modem();
            last_reg_check = xTaskGetTickCount();
        } else if ((now - last_reg_check) >= pdMS_TO_TICKS(REG_POLL_MS)) {
            last_reg_check = now;
            bool registered = get_registration();
            if (!registered && modem_armed) {
                modem_armed = false;
                mqtt_stop();
                set_relay_states(false, false);
                ESP_LOGW(TAG, "Se perdió el registro; relés apagados");
            } else if (registered && !modem_armed) {
                modem_armed = true;
                ESP_LOGI(TAG, "Registro recuperado; control habilitado");
            }
        }
        now = xTaskGetTickCount();
        if (modem_ready && modem_armed && !mqtt_connected &&
            (now - last_mqtt_attempt) >= pdMS_TO_TICKS(MQTT_RETRY_MS)) {
            last_mqtt_attempt = now;
            (void)mqtt_connect();
        }
    }
}
