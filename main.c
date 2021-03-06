#include <stdint.h>
#include <string.h>
#include "nordic_common.h"
#include "nrf.h"
#include "ble_hci.h"
#include "ble_advdata.h"
#include "ble_advertising.h"
#include "ble_conn_params.h"
#include "softdevice_handler.h"
#include "app_timer.h"
#include "app_button.h"
#include "ble_nus.h"
#include "app_uart.h"
#include "app_util_platform.h"
#include "bsp.h"
#include "bsp_btn_ble.h"

#include "nrf_drv_timer.h"
#include "nrf_delay.h"
#include "nrf_drv_twi.h"


#define IS_SRVC_CHANGED_CHARACT_PRESENT 0                                           /**< Include the service_changed characteristic. If not enabled, the server's database cannot be changed for the lifetime of the device. */

#if (NRF_SD_BLE_API_VERSION == 3)
#define NRF_BLE_MAX_MTU_SIZE            GATT_MTU_SIZE_DEFAULT                       /**< MTU size used in the softdevice enabling and to reply to a BLE_GATTS_EVT_EXCHANGE_MTU_REQUEST event. */
#endif

#define APP_FEATURE_NOT_SUPPORTED       BLE_GATT_STATUS_ATTERR_APP_BEGIN + 2        /**< Reply when unsupported features are requested. */

#define CENTRAL_LINK_COUNT              0                                           /**< Number of central links used by the application. When changing this number remember to adjust the RAM settings*/
#define PERIPHERAL_LINK_COUNT           1                                           /**< Number of peripheral links used by the application. When changing this number remember to adjust the RAM settings*/

#define DEVICE_NAME                     "NTP"                               /**< Name of device. Will be included in the advertising data. */
#define NUS_SERVICE_UUID_TYPE           BLE_UUID_TYPE_VENDOR_BEGIN                  /**< UUID type for the Nordic UART Service (vendor specific). */

#define APP_ADV_INTERVAL                64                                          /**< The advertising interval (in units of 0.625 ms. This value corresponds to 40 ms). */
#define APP_ADV_TIMEOUT_IN_SECONDS      0//180                                         /**< The advertising timeout (in units of seconds). */

#define APP_TIMER_PRESCALER             0                                           /**< Value of the RTC1 PRESCALER register. */
#define APP_TIMER_OP_QUEUE_SIZE         4                                           /**< Size of timer operation queues. */

#define MIN_CONN_INTERVAL               MSEC_TO_UNITS(7.5, UNIT_1_25_MS)             /**< Minimum acceptable connection interval (20 ms), Connection interval uses 1.25 ms units. */
#define MAX_CONN_INTERVAL               MSEC_TO_UNITS(7.5, UNIT_1_25_MS)             /**< Maximum acceptable connection interval (75 ms), Connection interval uses 1.25 ms units. */
#define SLAVE_LATENCY                   0                                           /**< Slave latency. */
#define CONN_SUP_TIMEOUT                MSEC_TO_UNITS(4000, UNIT_10_MS)             /**< Connection supervisory timeout (4 seconds), Supervision Timeout uses 10 ms units. */
#define FIRST_CONN_PARAMS_UPDATE_DELAY  APP_TIMER_TICKS(5000, APP_TIMER_PRESCALER)  /**< Time from initiating event (connect or start of notification) to first time sd_ble_gap_conn_param_update is called (5 seconds). */
#define NEXT_CONN_PARAMS_UPDATE_DELAY   APP_TIMER_TICKS(30000, APP_TIMER_PRESCALER) /**< Time between each call to sd_ble_gap_conn_param_update after the first call (30 seconds). */
#define MAX_CONN_PARAMS_UPDATE_COUNT    3                                           /**< Number of attempts before giving up the connection parameter negotiation. */

#define DEAD_BEEF                       0xDEADBEEF                                  /**< Value used as error code on stack dump, can be used to identify stack location on stack unwind. */

#define UART_TX_BUF_SIZE                256                                         /**< UART TX buffer size. */
#define UART_RX_BUF_SIZE                256                                         /**< UART RX buffer size. */

static ble_nus_t                        m_nus;                                      /**< Structure to identify the Nordic UART Service. */
static uint16_t                         m_conn_handle = BLE_CONN_HANDLE_INVALID;    /**< Handle of the current connection. */

static ble_uuid_t                       m_adv_uuids[] = {{BLE_UUID_NUS_SERVICE, NUS_SERVICE_UUID_TYPE}};  /**< Universally unique service identifier. */

/**********************************************************************
*                               DS3231                                
**********************************************************************/
#define DS3231
#ifdef	DS3231

/* TWI instance ID. */
#define TWI_INSTANCE_ID     0

/* TWI instance. */
static const nrf_drv_twi_t m_twi = NRF_DRV_TWI_INSTANCE(TWI_INSTANCE_ID);	

uint8_t DS3231_ADDR			= 0x68;
uint8_t DS3231_SECONDS[2]	= {0x00, 0x00};		// Range 00~59
uint8_t DS3231_MINUTES[2]	= {0x01, 0x00};		// Range 00~59
uint8_t DS3231_HOURS[2]		= {0x02, 0x00};		// Range 00~23
uint8_t DS3231_DAY[2]		= {0x03, 0x01};		// Range 1~7
uint8_t DS3231_DATE[2]		= {0x04, 0x00};		// Range 1~31
uint8_t DS3231_MONTH[2]		= {0x05, 0x00};		// Range 1~12
uint8_t DS3231_YEAR[2]		= {0x06, 0x00};		// Range 00~99(Doesn't include century)
uint8_t DS3231_CR[2]		= {0x0E, 0x60};		// Control Register (Should be set 0x60, BBSQW and CONV set 1; INTCN need set 0; output frequency is 1 Hz)
uint8_t DS3231_SR[2]		= {0x0F, 0x00};		// Status Register (Should be set 0x00, because we don't need enable 32kHz clock)
uint8_t DS3231_TR_UP[2]		= {0x11, 0x00};		// Temperture Register(Upper Byte)
uint8_t DS3231_TR_LO[2]		= {0x12, 0x00};		// Temperture Register(lowwer Byte)

#endif
/*		End #ifdef DS3231		*/


/**********************************************************************
*                               GPS                                
**********************************************************************/
#define	GPS
#ifdef	GPS

int gpsDataReady=20;//9;

#define BOOL char
//Queue
#define IOP_LF_DATA 0x0A  //\r
#define IOP_CR_DATA 0x0D  //\n
#define IOP_START_DBG 0x23  //#
#define IOP_START_NMEA 0x24  //$
#define IOP_START_HBD1 'H'
#define IOP_START_HBD2 'B'
#define IOP_START_HBD3 'D'
#define NMEA_ID_QUE_SIZE 64//256 //customer can configure it according to detail resource condition
#define NMEA_RX_QUE_SIZE 512//1024  //customer can configure it according to detail resource condition

#define MAX_I2C_PKT_LEN 255
#define MAX_NMEA_STN_LEN 256

typedef enum        
{
  RXS_DAT_HBD,            // receive HBD data
  RXS_PRM_HBD2,           // receive HBD preamble 2
  RXS_PRM_HBD3,           // receive HBD preamble 3 
  RXS_DAT,                // receive NMEA data
  RXS_DAT_DBG,            // receive DBG data
  RXS_ETX,                // End-of-packet
}RX_SYNC_STATE_T ;

typedef struct 
{
    short   inst_id;  // 1 - NMEA, 2 - DBG, 3 - HBD
    short   dat_idx;
    short   dat_siz;
} id_que_def;

char rx_que[NMEA_RX_QUE_SIZE];
id_que_def id_que[NMEA_ID_QUE_SIZE];

unsigned short id_que_head;
unsigned short id_que_tail;
unsigned short rx_que_head;
RX_SYNC_STATE_T rx_state;
unsigned int u4SyncPkt;
unsigned int u4OverflowPkt;
unsigned int u4PktInQueue;

bool bNMEASenDone;

#define MTK_TXBUF_SIZE 255
#define TRUE 1
#define FALSE 0
#define MTK_I2C_SLAVE_ADDR 0x10  // 7bit slave address

int val;
char SendBuf[16];

uint16_t GTOP_I2C_Read (uint8_t deviceAddr, uint8_t *data, uint16_t len);
void GTOP_I2C_Write (uint8_t deviceAddr, uint8_t *data, uint16_t len);
bool iop_init_pcrx(void);
bool iop_inst_avail(unsigned short* inst_id, unsigned short* dat_idx,unsigned short* dat_siz);
void iop_get_inst(short idx, short size, void *data);
void iop_pcrx_nmea( unsigned char data );
void iop_pcrx_nmea_dbg_hbd_bytes(unsigned char aData[], int i4NumByte);
int iop_parse_uart2bytes(char* ccmddata) ;


#endif
/*		End #ifdef GPS		*/





#define TimeStamp

#ifdef	TimeStamp
#endif

							


/**@brief Function for assert macro callback.
 *
 * @details This function will be called in case of an assert in the SoftDevice.
 *
 * @warning This handler is an example only and does not fit a final product. You need to analyse
 *          how your product is supposed to react in case of Assert.
 * @warning On assert from the SoftDevice, the system can only recover on reset.
 *
 * @param[in] line_num    Line number of the failing ASSERT call.
 * @param[in] p_file_name File name of the failing ASSERT call.
 */
void assert_nrf_callback(uint16_t line_num, const uint8_t * p_file_name)
{
    app_error_handler(DEAD_BEEF, line_num, p_file_name);
}


/**@brief Function for the GAP initialization.
 *
 * @details This function will set up all the necessary GAP (Generic Access Profile) parameters of
 *          the device. It also sets the permissions and appearance.
 */
static void gap_params_init(void)
{
    uint32_t                err_code;
    ble_gap_conn_params_t   gap_conn_params;
    ble_gap_conn_sec_mode_t sec_mode;

    BLE_GAP_CONN_SEC_MODE_SET_OPEN(&sec_mode);

    err_code = sd_ble_gap_device_name_set(&sec_mode,
                                          (const uint8_t *) DEVICE_NAME,
                                          strlen(DEVICE_NAME));
    APP_ERROR_CHECK(err_code);

    memset(&gap_conn_params, 0, sizeof(gap_conn_params));

    gap_conn_params.min_conn_interval = MIN_CONN_INTERVAL;
    gap_conn_params.max_conn_interval = MAX_CONN_INTERVAL;
    gap_conn_params.slave_latency     = SLAVE_LATENCY;
    gap_conn_params.conn_sup_timeout  = CONN_SUP_TIMEOUT;

    err_code = sd_ble_gap_ppcp_set(&gap_conn_params);
    APP_ERROR_CHECK(err_code);
}

/**@brief Function for handling the data from the Nordic UART Service.
 *
 * @details This function will process the data received from the Nordic UART BLE Service and send
 *          it to the UART module.
 *
 * @param[in] p_nus    Nordic UART Service structure.
 * @param[in] p_data   Data to be send to UART module.
 * @param[in] length   Length of the data.
 */
/**@snippet [Handling the data received over BLE] */
static void nus_data_handler(ble_nus_t * p_nus, uint8_t * p_data, uint16_t length)
{
}
/**@snippet [Handling the data received over BLE] */


/**@brief Function for initializing services that will be used by the application.
 */
static void services_init(void)
{
    uint32_t       err_code;
    ble_nus_init_t nus_init;

    memset(&nus_init, 0, sizeof(nus_init));

    nus_init.data_handler = nus_data_handler;

    err_code = ble_nus_init(&m_nus, &nus_init);
    APP_ERROR_CHECK(err_code);
}


/**@brief Function for handling an event from the Connection Parameters Module.
 *
 * @details This function will be called for all events in the Connection Parameters Module
 *          which are passed to the application.
 *
 * @note All this function does is to disconnect. This could have been done by simply setting
 *       the disconnect_on_fail config parameter, but instead we use the event handler
 *       mechanism to demonstrate its use.
 *
 * @param[in] p_evt  Event received from the Connection Parameters Module.
 */
static void on_conn_params_evt(ble_conn_params_evt_t * p_evt)
{
    uint32_t err_code;

    if (p_evt->evt_type == BLE_CONN_PARAMS_EVT_FAILED)
    {
        err_code = sd_ble_gap_disconnect(m_conn_handle, BLE_HCI_CONN_INTERVAL_UNACCEPTABLE);
        APP_ERROR_CHECK(err_code);
    }
}


/**@brief Function for handling errors from the Connection Parameters module.
 *
 * @param[in] nrf_error  Error code containing information about what went wrong.
 */
static void conn_params_error_handler(uint32_t nrf_error)
{
    APP_ERROR_HANDLER(nrf_error);
}


/**@brief Function for initializing the Connection Parameters module.
 */
static void conn_params_init(void)
{
    uint32_t               err_code;
    ble_conn_params_init_t cp_init;

    memset(&cp_init, 0, sizeof(cp_init));

    cp_init.p_conn_params                  = NULL;
    cp_init.first_conn_params_update_delay = FIRST_CONN_PARAMS_UPDATE_DELAY;
    cp_init.next_conn_params_update_delay  = NEXT_CONN_PARAMS_UPDATE_DELAY;
    cp_init.max_conn_params_update_count   = MAX_CONN_PARAMS_UPDATE_COUNT;
    cp_init.start_on_notify_cccd_handle    = BLE_GATT_HANDLE_INVALID;
    cp_init.disconnect_on_fail             = false;
    cp_init.evt_handler                    = on_conn_params_evt;
    cp_init.error_handler                  = conn_params_error_handler;

    err_code = ble_conn_params_init(&cp_init);
    APP_ERROR_CHECK(err_code);
}


/**@brief Function for putting the chip into sleep mode.
 *
 * @note This function will not return.
 */
static void sleep_mode_enter(void)
{
    uint32_t err_code = bsp_indication_set(BSP_INDICATE_IDLE);
    APP_ERROR_CHECK(err_code);

    // Prepare wakeup buttons.
    err_code = bsp_btn_ble_sleep_mode_prepare();
    APP_ERROR_CHECK(err_code);

    // Go to system-off mode (this function will not return; wakeup will cause a reset).
    err_code = sd_power_system_off();
    APP_ERROR_CHECK(err_code);
}


/**@brief Function for handling advertising events.
 *
 * @details This function will be called for advertising events which are passed to the application.
 *
 * @param[in] ble_adv_evt  Advertising event.
 */
static void on_adv_evt(ble_adv_evt_t ble_adv_evt)
{
    uint32_t err_code;

    switch (ble_adv_evt)
    {
        case BLE_ADV_EVT_FAST:
            err_code = bsp_indication_set(BSP_INDICATE_ADVERTISING);
            APP_ERROR_CHECK(err_code);
            break;
        case BLE_ADV_EVT_IDLE:
            sleep_mode_enter();
            break;
        default:
            break;
    }
}



/**@brief Function for initializing the Advertising functionality.
 */
static void advertising_init(void)
{
    uint32_t               err_code;
    ble_advdata_t          advdata;
    ble_advdata_t          scanrsp;
    ble_adv_modes_config_t options;

    // Build advertising data struct to pass into @ref ble_advertising_init.
    memset(&advdata, 0, sizeof(advdata));
    advdata.name_type          = BLE_ADVDATA_FULL_NAME;
    advdata.include_appearance = false;
    advdata.flags              = BLE_GAP_ADV_FLAGS_LE_ONLY_GENERAL_DISC_MODE;//BLE_GAP_ADV_FLAGS_LE_ONLY_LIMITED_DISC_MODE;

    memset(&scanrsp, 0, sizeof(scanrsp));
    scanrsp.uuids_complete.uuid_cnt = sizeof(m_adv_uuids) / sizeof(m_adv_uuids[0]);
    scanrsp.uuids_complete.p_uuids  = m_adv_uuids;

    memset(&options, 0, sizeof(options));
    options.ble_adv_fast_enabled  = true;
    options.ble_adv_fast_interval = APP_ADV_INTERVAL;
    options.ble_adv_fast_timeout  = APP_ADV_TIMEOUT_IN_SECONDS;

    err_code = ble_advertising_init(&advdata, &scanrsp, &options, on_adv_evt, NULL);
    APP_ERROR_CHECK(err_code);
}


/**@brief Function for the application's SoftDevice event handler.
 *
 * @param[in] p_ble_evt SoftDevice event.
 */
static void on_ble_evt(ble_evt_t * p_ble_evt)
{
    uint32_t err_code;

    switch (p_ble_evt->header.evt_id)
    {
        case BLE_GAP_EVT_CONNECTED:
            err_code = bsp_indication_set(BSP_INDICATE_CONNECTED);
            APP_ERROR_CHECK(err_code);
            m_conn_handle = p_ble_evt->evt.gap_evt.conn_handle;
			printf("=============== Connect ===============\r\n");
            break; // BLE_GAP_EVT_CONNECTED

        case BLE_GAP_EVT_DISCONNECTED:
            err_code = bsp_indication_set(BSP_INDICATE_IDLE);
            APP_ERROR_CHECK(err_code);
            m_conn_handle = BLE_CONN_HANDLE_INVALID;
		
			advertising_init();
			err_code = ble_advertising_start(BLE_ADV_MODE_FAST);		//?_?u???A???s?}???s??
			APP_ERROR_CHECK(err_code);
			printf("=============== Disconnect ============\r\n");
            break; // BLE_GAP_EVT_DISCONNECTED

        case BLE_GAP_EVT_SEC_PARAMS_REQUEST:
            // Pairing not supported
            err_code = sd_ble_gap_sec_params_reply(m_conn_handle, BLE_GAP_SEC_STATUS_PAIRING_NOT_SUPP, NULL, NULL);
            APP_ERROR_CHECK(err_code);
            break; // BLE_GAP_EVT_SEC_PARAMS_REQUEST

        case BLE_GATTS_EVT_SYS_ATTR_MISSING:
            // No system attributes have been stored.
            err_code = sd_ble_gatts_sys_attr_set(m_conn_handle, NULL, 0, 0);
            APP_ERROR_CHECK(err_code);
            break; // BLE_GATTS_EVT_SYS_ATTR_MISSING

        case BLE_GATTC_EVT_TIMEOUT:
            // Disconnect on GATT Client timeout event.
            err_code = sd_ble_gap_disconnect(p_ble_evt->evt.gattc_evt.conn_handle,
                                             BLE_HCI_REMOTE_USER_TERMINATED_CONNECTION);
            APP_ERROR_CHECK(err_code);
            break; // BLE_GATTC_EVT_TIMEOUT

        case BLE_GATTS_EVT_TIMEOUT:
            // Disconnect on GATT Server timeout event.
            err_code = sd_ble_gap_disconnect(p_ble_evt->evt.gatts_evt.conn_handle,
                                             BLE_HCI_REMOTE_USER_TERMINATED_CONNECTION);
            APP_ERROR_CHECK(err_code);
            break; // BLE_GATTS_EVT_TIMEOUT

        case BLE_EVT_USER_MEM_REQUEST:
            err_code = sd_ble_user_mem_reply(p_ble_evt->evt.gattc_evt.conn_handle, NULL);
            APP_ERROR_CHECK(err_code);
            break; // BLE_EVT_USER_MEM_REQUEST

        case BLE_GATTS_EVT_RW_AUTHORIZE_REQUEST:
        {
            ble_gatts_evt_rw_authorize_request_t  req;
            ble_gatts_rw_authorize_reply_params_t auth_reply;

            req = p_ble_evt->evt.gatts_evt.params.authorize_request;

            if (req.type != BLE_GATTS_AUTHORIZE_TYPE_INVALID)
            {
                if ((req.request.write.op == BLE_GATTS_OP_PREP_WRITE_REQ)     ||
                    (req.request.write.op == BLE_GATTS_OP_EXEC_WRITE_REQ_NOW) ||
                    (req.request.write.op == BLE_GATTS_OP_EXEC_WRITE_REQ_CANCEL))
                {
                    if (req.type == BLE_GATTS_AUTHORIZE_TYPE_WRITE)
                    {
                        auth_reply.type = BLE_GATTS_AUTHORIZE_TYPE_WRITE;
                    }
                    else
                    {
                        auth_reply.type = BLE_GATTS_AUTHORIZE_TYPE_READ;
                    }
                    auth_reply.params.write.gatt_status = APP_FEATURE_NOT_SUPPORTED;
                    err_code = sd_ble_gatts_rw_authorize_reply(p_ble_evt->evt.gatts_evt.conn_handle,
                                                               &auth_reply);
                    APP_ERROR_CHECK(err_code);
                }
            }
        } break; // BLE_GATTS_EVT_RW_AUTHORIZE_REQUEST

#if (NRF_SD_BLE_API_VERSION == 3)
        case BLE_GATTS_EVT_EXCHANGE_MTU_REQUEST:
            err_code = sd_ble_gatts_exchange_mtu_reply(p_ble_evt->evt.gatts_evt.conn_handle,
                                                       NRF_BLE_MAX_MTU_SIZE);
            APP_ERROR_CHECK(err_code);
            break; // BLE_GATTS_EVT_EXCHANGE_MTU_REQUEST
#endif

        default:
            // No implementation needed.
            break;
    }
}


/**@brief Function for dispatching a SoftDevice event to all modules with a SoftDevice
 *        event handler.
 *
 * @details This function is called from the SoftDevice event interrupt handler after a
 *          SoftDevice event has been received.
 *
 * @param[in] p_ble_evt  SoftDevice event.
 */
static void ble_evt_dispatch(ble_evt_t * p_ble_evt)
{
    ble_conn_params_on_ble_evt(p_ble_evt);
    ble_nus_on_ble_evt(&m_nus, p_ble_evt);
    on_ble_evt(p_ble_evt);
    ble_advertising_on_ble_evt(p_ble_evt);
    bsp_btn_ble_on_ble_evt(p_ble_evt);

}


/**@brief Function for the SoftDevice initialization.
 *
 * @details This function initializes the SoftDevice and the BLE event interrupt.
 */
static void ble_stack_init(void)
{
    uint32_t err_code;

    nrf_clock_lf_cfg_t clock_lf_cfg = NRF_CLOCK_LFCLKSRC;

    // Initialize SoftDevice.
    SOFTDEVICE_HANDLER_INIT(&clock_lf_cfg, NULL);

    ble_enable_params_t ble_enable_params;
    err_code = softdevice_enable_get_default_config(CENTRAL_LINK_COUNT,
                                                    PERIPHERAL_LINK_COUNT,
                                                    &ble_enable_params);
    APP_ERROR_CHECK(err_code);

    //Check the ram settings against the used number of links
    CHECK_RAM_START_ADDR(CENTRAL_LINK_COUNT,PERIPHERAL_LINK_COUNT);

    // Enable BLE stack.
#if (NRF_SD_BLE_API_VERSION == 3)
    ble_enable_params.gatt_enable_params.att_mtu = NRF_BLE_MAX_MTU_SIZE;
#endif
    err_code = softdevice_enable(&ble_enable_params);
    APP_ERROR_CHECK(err_code);

    // Subscribe for BLE events.
    err_code = softdevice_ble_evt_handler_set(ble_evt_dispatch);
    APP_ERROR_CHECK(err_code);
}

/**@brief   Function for handling app_uart events.
 *
 * @details This function will receive a single character from the app_uart module and append it to
 *          a string. The string will be be sent over BLE when the last character received was a
 *          'new line' i.e '\r\n' (hex 0x0D) or if the string has reached a length of
 *          @ref NUS_MAX_DATA_LENGTH.
 */
/**@snippet [Handling the data received over UART] */
void uart_event_handle(app_uart_evt_t * p_event)
{
//    static uint8_t data_array[BLE_NUS_MAX_DATA_LEN];
//    static uint8_t index = 0;
//    uint32_t       err_code;

    switch (p_event->evt_type)
    {
        case APP_UART_DATA_READY:
//            UNUSED_VARIABLE(app_uart_get(&data_array[index]));
//            index++;

//            if ((data_array[index - 1] == '\n') || (index >= (BLE_NUS_MAX_DATA_LEN)))
//            {
//                err_code = ble_nus_string_send(&m_nus, data_array, index);
//                if (err_code != NRF_ERROR_INVALID_STATE)
//                {
//                    APP_ERROR_CHECK(err_code);
//                }

//                index = 0;
//            }
            break;

        case APP_UART_COMMUNICATION_ERROR:
            APP_ERROR_HANDLER(p_event->data.error_communication);
            break;

        case APP_UART_FIFO_ERROR:
            APP_ERROR_HANDLER(p_event->data.error_code);
            break;

        default:
            break;
    }
}
/**@snippet [Handling the data received over UART] */


/**@brief  Function for initializing the UART module.
 */
/**@snippet [UART Initialization] */
static void uart_init(void)
{
    uint32_t                     err_code;
    const app_uart_comm_params_t comm_params =
    {
        RX_PIN_NUMBER,
        TX_PIN_NUMBER,
        RTS_PIN_NUMBER,
        CTS_PIN_NUMBER,
        APP_UART_FLOW_CONTROL_DISABLED,
        false,
        UART_BAUDRATE_BAUDRATE_Baud115200
    };

    APP_UART_FIFO_INIT( &comm_params,
                       UART_RX_BUF_SIZE,
                       UART_TX_BUF_SIZE,
                       uart_event_handle,
                       APP_IRQ_PRIORITY_LOWEST,
                       err_code);
    APP_ERROR_CHECK(err_code);
}
/**@snippet [UART Initialization] */


void twi_init (void)
{
    ret_code_t err_code;

    const nrf_drv_twi_config_t twi_config = {
       .scl                = ARDUINO_SCL_PIN,
       .sda                = ARDUINO_SDA_PIN,
       .frequency          = NRF_TWI_FREQ_100K,
       .interrupt_priority = APP_IRQ_PRIORITY_HIGH,
       .clear_bus_init     = false
    };

    err_code = nrf_drv_twi_init(&m_twi, &twi_config, NULL, NULL);
    APP_ERROR_CHECK(err_code);

    nrf_drv_twi_enable(&m_twi);
}

/**@brief Function for initializing buttons and leds.
 *
 * @param[out] p_erase_bonds  Will be true if the clear bonding button was pressed to wake the application up.
 */
static void buttons_leds_init(bool * p_erase_bonds)
{
    bsp_event_t startup_event;

//    uint32_t err_code = bsp_init(BSP_INIT_LED | BSP_INIT_BUTTONS,
//                                 APP_TIMER_TICKS(100, APP_TIMER_PRESCALER),
//                                 bsp_event_handler);
    uint32_t err_code = bsp_init(BSP_INIT_LED | BSP_INIT_BUTTONS,
                                 APP_TIMER_TICKS(100, APP_TIMER_PRESCALER),
                                 NULL);
    APP_ERROR_CHECK(err_code);

bsp_board_led_off(BSP_BOARD_LED_1);		
	
    err_code = bsp_btn_ble_init(NULL, &startup_event);
    APP_ERROR_CHECK(err_code);

    *p_erase_bonds = (startup_event == BSP_EVENT_CLEAR_BONDING_DATA);
}


/**@brief Function for placing the application in low power state while waiting for events.
 */
static void power_manage(void)
{
    uint32_t err_code = sd_app_evt_wait();
    APP_ERROR_CHECK(err_code);
}

static void ppi_init(void)
{
    // Configure PPI channel 0 to toggle GPIO_OUTPUT_PIN on every TIMER1 COMPARE[3] match (200 ms)
    NRF_PPI->CH[0].EEP = (uint32_t)& (NRF_TIMER1->EVENTS_COMPARE[2]);//NRF_PPI->CH[0].EEP = (uint32_t)& (NRF_TIMER1->EVENTS_COMPARE[3]);
    NRF_PPI->CH[0].TEP = (uint32_t)& (NRF_ADC->TASKS_START);

    NRF_PPI->CHEN = (PPI_CHEN_CH0_Enabled << PPI_CHEN_CH0_Pos);
}

void adc_init(void)
{
	/* Enable interrupt on ADC sample ready event*/		
	NRF_ADC->INTENSET = ADC_INTENSET_END_Msk;
	NVIC_SetPriority(ADC_IRQn, APP_IRQ_PRIORITY_HIGH);//NVIC_SetPriority(ADC_IRQn, APP_IRQ_PRIORITY_LOWEST);
	NVIC_EnableIRQ(ADC_IRQn);	
	
	NRF_ADC->CONFIG	= (ADC_CONFIG_EXTREFSEL_None << ADC_CONFIG_EXTREFSEL_Pos) 				/* Bits 17..16 : ADC external reference pin selection. */
					| (ADC_CONFIG_PSEL_AnalogInput4 << ADC_CONFIG_PSEL_Pos)					/*!< Use analog input 6 as analog input (P0.05). */
					| (ADC_CONFIG_REFSEL_VBG << ADC_CONFIG_REFSEL_Pos)						/*!< Use internal 1.2V bandgap voltage as reference for conversion. */
					| (ADC_CONFIG_INPSEL_AnalogInputOneThirdPrescaling << ADC_CONFIG_INPSEL_Pos) 	/*!< Analog input specified by PSEL with no prescaling used as input for the conversion. */
					| (ADC_CONFIG_RES_10bit << ADC_CONFIG_RES_Pos);							/*!< 10bit ADC resolution. */ 	

	NRF_ADC->ENABLE = ADC_ENABLE_ENABLE_Enabled;   
}

void timer_init(void)
{
	APP_TIMER_INIT(APP_TIMER_PRESCALER, APP_TIMER_OP_QUEUE_SIZE, false);
	
   // Start 16 MHz crystal oscillator.
    NRF_CLOCK->EVENTS_HFCLKSTARTED = 0;
    NRF_CLOCK->TASKS_HFCLKSTART    = 1;

    // Wait for the external oscillator to start.
    while (NRF_CLOCK->EVENTS_HFCLKSTARTED == 0) 
    {
        // Do nothing.
    }	
	
    // Clear TIMER1
    NRF_TIMER1->TASKS_CLEAR = 1;

    // Configure TIMER1 for compare[3] event every 200 ms.
    NRF_TIMER1->PRESCALER = 3;              // Prescaler 3 results in 1 tick equals 0.5 microsecond.
	NRF_TIMER1->CC[2]     = 2000;			// 0.5us * 2000 = 1ms

	NRF_TIMER1->MODE      = TIMER_MODE_MODE_Timer;
    NRF_TIMER1->BITMODE   = TIMER_BITMODE_BITMODE_32Bit;
    NRF_TIMER1->SHORTS    = (TIMER_SHORTS_COMPARE2_CLEAR_Enabled << TIMER_SHORTS_COMPARE2_CLEAR_Pos);//NRF_TIMER1->SHORTS    = (TIMER_SHORTS_COMPARE3_CLEAR_Enabled << TIMER_SHORTS_COMPARE3_CLEAR_Pos);
	NRF_TIMER1->TASKS_START = 1;  // Start event generation.
}

void ADC_IRQHandler(void)		// 1m seceond per ADC interrupt
{	
	/* Clear dataready event */
    NRF_ADC->EVENTS_END = 0;	
	
	int inverSignal = 1024 - NRF_ADC->RESULT;	// Inverting the signal value

}


#ifdef GPS

uint16_t GTOP_I2C_Read (uint8_t deviceAddr, uint8_t *data, uint16_t len)
{
    uint16_t res = 0;
	
    //Wire.requestFrom(deviceAddr, len);    // request len bytes from slave deviceAddr

    nrf_drv_twi_rx(&m_twi, deviceAddr, data, sizeof(data));
	
	while(*data != NULL)
	{
      data++;
      res++;
	}
	
    return res;
}

void GTOP_I2C_Write (uint8_t deviceAddr, uint8_t *data, uint16_t len)
{
	nrf_drv_twi_tx(&m_twi, deviceAddr, data, len, true);
	
    return ;
}

bool iop_init_pcrx( void )
{
    /*----------------------------------------------------------
    variables
    ----------------------------------------------------------*/
    short   i;

    /*----------------------------------------------------------
    initialize queue indexes
    ----------------------------------------------------------*/
    id_que_head = 0;
    id_que_tail = 0;
    rx_que_head = 0;

    /*----------------------------------------------------------
    initialize identification queue
    ----------------------------------------------------------*/
    for( i=0; i< NMEA_ID_QUE_SIZE; i++)
    {
        id_que[i].inst_id = -1;
        id_que[i].dat_idx =  0;
    }

    /*----------------------------------------------------------
    initialize receive state
    ----------------------------------------------------------*/
    rx_state = RXS_ETX;

    /*----------------------------------------------------------
    initialize statistic information
    ----------------------------------------------------------*/
    u4SyncPkt = 0;
    u4OverflowPkt = 0;
    u4PktInQueue = 0;

    return TRUE;
}

/*********************************************************************
*   PROCEDURE NAME:
*       iop_inst_avail - Get available NMEA sentence information
*
*   DESCRIPTION:
*     inst_id - NMEA sentence type
*     dat_idx - start data index in queue
*     dat_siz - NMEA sentence size
*********************************************************************/
bool iop_inst_avail(unsigned short *inst_id, unsigned short *dat_idx, 
                    unsigned short *dat_siz)
{
    /*----------------------------------------------------------
    variables
    ----------------------------------------------------------*/
    BOOL inst_avail;

    /*----------------------------------------------------------
    if packet is available then return id and index
    ----------------------------------------------------------*/
    if ( id_que_tail != id_que_head )
    {
        *inst_id = id_que[ id_que_tail ].inst_id;
        *dat_idx = id_que[ id_que_tail ].dat_idx;
        *dat_siz = id_que[ id_que_tail ].dat_siz;
        id_que[ id_que_tail ].inst_id = -1;
        id_que_tail = ++id_que_tail & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
        inst_avail = TRUE;

        if (u4PktInQueue > 0)
        {
            u4PktInQueue--;
        }
    }
    else
    {
        inst_avail = FALSE;
    }
    return ( inst_avail );
}   /* iop_inst_avail() end */


/*********************************************************************
*   PROCEDURE NAME:
*       iop_get_inst - Get available NMEA sentence from queue
*
*   DESCRIPTION:
*     idx - start data index in queue
*     size - NMEA sentence size
*     data - data buffer used to save NMEA sentence
*********************************************************************/
void iop_get_inst(short idx, short size, void *data)
{
    /*----------------------------------------------------------
    variables
    ----------------------------------------------------------*/
    short i;
    unsigned char *ptr;

    /*----------------------------------------------------------
    copy data from the receive queue to the data buffer
    ----------------------------------------------------------*/
    ptr = (unsigned char *)data;
    for (i = 0; i < size; i++)
    {
        *ptr = rx_que[idx];
        ptr++;
        idx = ++idx & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
    }
}   /* iop_get_inst() end */


/*********************************************************************
*   PROCEDURE NAME:
*       iop_pcrx_nmea - Receive NMEA code
*
*   DESCRIPTION:
*     The procedure fetch the characters between/includes '$' and <CR>.
*     That is, character <CR><LF> is skipped.
*     and the maximum size of the sentence fetched by this procedure is 256
*     $xxxxxx*AA
*
*********************************************************************/
void iop_pcrx_nmea( unsigned char data )
{
    /*----------------------------------------------------------
    determine the receive state
    ----------------------------------------------------------*/
    if (data == IOP_LF_DATA){
        return;
    }
    
	nrf_delay_ms(50);
	
    switch (rx_state)
    {
      case RXS_DAT:
        switch (data)
        {
          case IOP_CR_DATA:
            // count total number of sync packets
            u4SyncPkt += 1;

            id_que_head = ++id_que_head & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
            if (id_que_tail == id_que_head)
            {
              // count total number of overflow packets
              u4OverflowPkt += 1;

              id_que_tail = ++id_que_tail & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
            }
            else
            {
              u4PktInQueue++;
            }

            rx_state = RXS_ETX;
            /*----------------------------------------------------------
            set RxEvent signaled
            ----------------------------------------------------------*/
            //SetEvent(hRxEvent);
             bNMEASenDone = TRUE;
            break;

          case IOP_START_NMEA:
          {
            // Restart NMEA sentence collection
            rx_state = RXS_DAT;
            id_que[id_que_head].inst_id = 1;
            id_que[id_que_head].dat_idx = rx_que_head;
            id_que[id_que_head].dat_siz = 0;
            rx_que[rx_que_head] = data;
            rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
            id_que[id_que_head].dat_siz++;
  
            break;
          }

          default:
            rx_que[rx_que_head] = data;
            rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
            id_que[id_que_head].dat_siz++;

            // if NMEA sentence length > 256, stop NMEA sentence collection
            if (id_que[id_que_head].dat_siz == MAX_NMEA_STN_LEN)
            {
                id_que[id_que_head].inst_id = -1;
                
                rx_state = RXS_ETX;
            }
            break;
        }
        break;

      case RXS_ETX:
        if (data == IOP_START_NMEA)
        {
            rx_state = RXS_DAT;
            id_que[id_que_head].inst_id = 1;
            id_que[id_que_head].dat_idx = rx_que_head;
            id_que[id_que_head].dat_siz = 0;
            rx_que[rx_que_head] = data;
            rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
            id_que[id_que_head].dat_siz++;
        }
        break;

      default:
        rx_state = RXS_ETX;

        break;
    }
}   /* iop_pcrx_nmea() end */


/*********************************************************************
*   PROCEDURE NAME:
*       void iop_pcrx_nmea_dbg_hbd_bytes(unsigned char aData[], int i4NumByte)
*       - Receive NMEA and debug log code
*
*   DESCRIPTION:
*     The procedure fetch the characters between/includes '$' and <CR>.
*     That is, character <CR><LF> is skipped.
*     and the maximum size of the sentence fetched by this procedure is 256
*     $xxxxxx*AA
*
*********************************************************************/
void iop_pcrx_nmea_dbg_hbd_bytes(unsigned char aData[], int i4NumByte)
{
    int i;
    unsigned char data;


    for (i = 0; i < i4NumByte; i++)
    {
      data = aData[i];
      if (data == IOP_LF_DATA){
          continue;
      }

      /*----------------------------------------------------------
      determine the receive state
      ----------------------------------------------------------*/
      switch (rx_state)
      {
          case RXS_DAT:
              switch (data)
              {
                  case IOP_CR_DATA:
                      // count total number of sync packets
                      u4SyncPkt += 1;
  
                      id_que_head = ++id_que_head & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      if (id_que_tail == id_que_head)
                      {
                        // count total number of overflow packets
                        u4OverflowPkt += 1;
  
                        id_que_tail = ++id_que_tail & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      }
                      else
                      {
                        u4PktInQueue++;
                      }
  
                      rx_state = RXS_ETX;
                      /*----------------------------------------------------------
                      set RxEvent signaled
                      ----------------------------------------------------------*/
                      bNMEASenDone = TRUE;
                      break;
  
                  case IOP_START_NMEA:
                  {
  
                    // Restart NMEA sentence collection
                    rx_state = RXS_DAT;
                    id_que[id_que_head].inst_id = 1;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  case IOP_START_DBG:
                  {
                    // Restart DBG sentence collection
                    rx_state = RXS_DAT_DBG;
                    id_que[id_que_head].inst_id = 2;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  default:
                      rx_que[rx_que_head] = data;
                      rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                      id_que[id_que_head].dat_siz++;
  
                      // if NMEA sentence length > 256, stop NMEA sentence collection
                      if (id_que[id_que_head].dat_siz == MAX_NMEA_STN_LEN)
                      {
                          id_que[id_que_head].inst_id = -1;
                          
                          rx_state = RXS_ETX;
                      }
                      
                      break;
              }
              break;
  
          case RXS_DAT_DBG:
              switch (data)
              {
                  case IOP_CR_DATA:
                      // count total number of sync packets
                      u4SyncPkt += 1;
  
                      id_que_head = ++id_que_head & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      if (id_que_tail == id_que_head)
                      {
                        // count total number of overflow packets
                        u4OverflowPkt += 1;
  
                        id_que_tail = ++id_que_tail & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      }
                      else
                      {
                        u4PktInQueue++;
                      }
  
                      rx_state = RXS_ETX;
                      /*----------------------------------------------------------
                      set RxEvent signaled
                      ----------------------------------------------------------*/
                      bNMEASenDone = TRUE;;
                      break;
  
                  case IOP_START_NMEA:
                  {
  
                    // Restart NMEA sentence collection
                    rx_state = RXS_DAT;
                    id_que[id_que_head].inst_id = 1;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  case IOP_START_DBG:
                  {
                    // Restart DBG sentence collection
                    rx_state = RXS_DAT_DBG;
                    id_que[id_que_head].inst_id = 2;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  default:
                      rx_que[rx_que_head] = data;
                      rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                      id_que[id_que_head].dat_siz++;
  
                      // if NMEA sentence length > 256, stop NMEA sentence collection
                      if (id_que[id_que_head].dat_siz == MAX_NMEA_STN_LEN)
                      {
                          id_que[id_que_head].inst_id = -1;
                          
                          rx_state = RXS_ETX;
                      }
  
                      break;
              }
              break;
  
          case RXS_DAT_HBD:
              switch (data)
              {
                  case IOP_CR_DATA:
                      // count total number of sync packets
                      u4SyncPkt += 1;
  
                      id_que_head = ++id_que_head & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      if (id_que_tail == id_que_head)
                      {
                        // count total number of overflow packets
                        u4OverflowPkt += 1;
  
                        id_que_tail = ++id_que_tail & (unsigned short)(NMEA_ID_QUE_SIZE - 1);
                      }
                      else
                      {
                        u4PktInQueue++;
                      }
  
                      rx_state = RXS_ETX;
                      /*----------------------------------------------------------
                      set RxEvent signaled
                      ----------------------------------------------------------*/
                      bNMEASenDone = TRUE;
                      break;
  
                  case IOP_START_NMEA:
                  {
                    // Restart NMEA sentence collection
                    rx_state = RXS_DAT;
                    id_que[id_que_head].inst_id = 1;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  case IOP_START_DBG:
                  {
                    // Restart DBG sentence collection
                    rx_state = RXS_DAT_DBG;
                    id_que[id_que_head].inst_id = 2;
                    id_que[id_que_head].dat_idx = rx_que_head;
                    id_que[id_que_head].dat_siz = 0;
                    rx_que[rx_que_head] = data;
                    rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                    id_que[id_que_head].dat_siz++;
                    break;
                  }
  
                  default:
                      rx_que[rx_que_head] = data;
                      rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                      id_que[id_que_head].dat_siz++;
  
                      // if NMEA sentence length > 256, stop NMEA sentence collection
                      if (id_que[id_que_head].dat_siz == MAX_NMEA_STN_LEN)
                      {
                          id_que[id_que_head].inst_id = -1;
                          
                          rx_state = RXS_ETX;
                      }
  
                      break;
              }
              break;
  
  
          case RXS_ETX:
              if (data == IOP_START_NMEA)
              {
                  rx_state = RXS_DAT;
                  id_que[id_que_head].inst_id = 1;
                  id_que[id_que_head].dat_idx = rx_que_head;
                  id_que[id_que_head].dat_siz = 0;
                  rx_que[rx_que_head] = data;
                  rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                  id_que[id_que_head].dat_siz++;
              }
              else if (data == IOP_START_DBG)
              {
                  rx_state = RXS_DAT_DBG;
                  id_que[id_que_head].inst_id = 2;
                  id_que[id_que_head].dat_idx = rx_que_head;
                  id_que[id_que_head].dat_siz = 0;
                  rx_que[rx_que_head] = data;
                  rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                  id_que[id_que_head].dat_siz++;
              }
              else if (data == IOP_START_HBD1)
              {
                  rx_state = RXS_PRM_HBD2;
              }
              break;
  
          case RXS_PRM_HBD2:
              if (data == IOP_START_HBD2)
              {
                  rx_state = RXS_PRM_HBD3;
              }
              else
              {
                rx_state = RXS_ETX;
              }
              break;
  
          case RXS_PRM_HBD3:
              if (data == IOP_START_HBD3)
              {
                  rx_state = RXS_DAT_HBD;
  
                  // Start to collect the packet
                  id_que[id_que_head].inst_id = 3;
                  id_que[id_que_head].dat_idx = rx_que_head;
                  id_que[id_que_head].dat_siz = 0;
                  rx_que[rx_que_head] = IOP_START_HBD1;
                  rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                  id_que[id_que_head].dat_siz++;
                  rx_que[rx_que_head] = IOP_START_HBD2;
                  rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                  id_que[id_que_head].dat_siz++;
                  rx_que[rx_que_head] = IOP_START_HBD3;
                  rx_que_head = ++rx_que_head & (unsigned short)(NMEA_RX_QUE_SIZE - 1);
                  id_que[id_que_head].dat_siz++;
              }
              else
              {
                rx_state = RXS_ETX;
              }
              break;
  
          default:
              rx_state = RXS_ETX;    
              break;
      }
    }
}   /* iop_pcrx_nmea_dbg_hbd_bytes() end */

#endif
/*		End #ifdef GPS		*/


/**@brief Application main function.
 */
int main(void)
{
    uint32_t err_code;
    bool erase_bonds;

    // Initialize.
    uart_init();
	twi_init();
	adc_init();
	timer_init();
	ppi_init(); 

	
    buttons_leds_init(&erase_bonds);
    ble_stack_init();
    gap_params_init();
    services_init();
    advertising_init();
    conn_params_init();

    printf("\r\nNTP Start!!!\r\n");
    err_code = ble_advertising_start(BLE_ADV_MODE_FAST);
    APP_ERROR_CHECK(err_code);

//#define DS3231_CONFIG
#ifdef DS3231_CONFIG		// Setting register data again, if the battery of DS3231 modual is running out, the inside of register data will be cleaned.
	uint8_t TWI_BUFFER = 0;

	nrf_drv_twi_tx(&m_twi, DS3231_ADDR, DS3231_CR, 2, true);		// Write Control Register data
		
	nrf_drv_twi_tx(&m_twi, DS3231_ADDR, DS3231_CR, 1, true);		// Read Control Register data 
    nrf_drv_twi_rx(&m_twi, DS3231_ADDR, &TWI_BUFFER, sizeof(TWI_BUFFER));	
	
	printf("Control Register is = 0x%x\r\n", TWI_BUFFER);
	
	nrf_drv_twi_tx(&m_twi, DS3231_ADDR, DS3231_SR, 2, true);		// Write Status Register data
		
	nrf_drv_twi_tx(&m_twi, DS3231_ADDR, DS3231_SR, 1, true);		// Read Status Register data 
    nrf_drv_twi_rx(&m_twi, DS3231_ADDR, &TWI_BUFFER, sizeof(TWI_BUFFER));
	printf("Status Register is = 0x%x\r\n", TWI_BUFFER);
#endif
/*		End #ifdef DS3231_CONFIG		*/

#ifdef GPS
	uint16_t ii;
	uint16_t recLen;
	char Data[MAX_NMEA_STN_LEN];
	unsigned char areadBuf[MTK_TXBUF_SIZE];
	unsigned short i2PacketType;  // 1: NMEA,  2: DEBUG, 3: HBD
	unsigned short i2PacketSize;
	unsigned short i2DataIdx; 
	uint8_t *readBuf= (uint8_t *)(areadBuf);
	if (readBuf == NULL) {
	 printf("single page mode: readBuf allocation error");
	}
#endif
/*		End #ifdef GPS		*/

    // Enter main loop.
    for (;;)
    {
        power_manage();

#ifdef GPS
		recLen = GTOP_I2C_Read(MTK_I2C_SLAVE_ADDR, readBuf, MTK_TXBUF_SIZE);
	  
		//Process I2C pakcets, extract NMEA data and discard garbage bytes
		iop_pcrx_nmea_dbg_hbd_bytes(readBuf, recLen);
		//Entire NMEA data of one second  have been received over or not?
		// The last three bytes in buffer are <LF><LF><LF>, it means Entire NMEA data of one second received over

		if ((readBuf[MAX_I2C_PKT_LEN - 3] == IOP_LF_DATA) && (readBuf[MAX_I2C_PKT_LEN - 2] == IOP_LF_DATA) && (readBuf[MAX_I2C_PKT_LEN - 1] == IOP_LF_DATA))
		{
		  //Entire NMEA packet of one second was received, wait 100ms.
		  nrf_delay_ms(500);
		}
		else
		{
		  nrf_delay_ms(2); // wait MT333x upload I2C data into hardware buffer.
		}
		//		}

		if(bNMEASenDone)
		{
			memset(Data, 0, MAX_NMEA_STN_LEN);
			while (iop_inst_avail(&i2PacketType, &i2DataIdx, &i2PacketSize))//get available NMEA sentence
			{
				//Get one NMEA Sentence, save in buffer 
			   iop_get_inst(i2DataIdx, i2PacketSize, &Data[0]);
				
				/*******************************
				*		Catch the UTC time
				*******************************/
				if(	Data[0] == '$' && 
					Data[1] == 'G' &&
					Data[2] == 'N' &&
					Data[3]	== 'G' &&
					Data[4] == 'G' &&
					Data[5]	== 'A')
				{
					bsp_board_led_on(BSP_BOARD_LED_1);	
					nrf_delay_ms(300);
					bsp_board_led_off(BSP_BOARD_LED_1);	
					
					printf("!!!!!! ");
					for(int i = 7; i < 13; i++)		printf("%c", Data[i]);		// Print UTC time
					printf(" !!!!!!\r\n");
				}	/*		Catch the UTC time end		*/
				
				
			   for (ii=0;ii<i2PacketSize;ii++)
			   {
					printf("%c", Data[ii]);
				   //delay(1);
			   }
			   printf("|\r");
			   //delay(1);
			   printf("|\n");
			   nrf_delay_ms(1);
			}
			bNMEASenDone = FALSE;
		}
		 
#endif
/*		End #ifdef GPS		*/

	}
}


/**
 * @}
 */
