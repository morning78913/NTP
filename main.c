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


#define IS_SRVC_CHANGED_CHARACT_PRESENT 0                                           /**< Include the service_changed characteristic. If not enabled, the server's database cannot be changed for the lifetime of the device. */

#if (NRF_SD_BLE_API_VERSION == 3)
#define NRF_BLE_MAX_MTU_SIZE            GATT_MTU_SIZE_DEFAULT                       /**< MTU size used in the softdevice enabling and to reply to a BLE_GATTS_EVT_EXCHANGE_MTU_REQUEST event. */
#endif

#define APP_FEATURE_NOT_SUPPORTED       BLE_GATT_STATUS_ATTERR_APP_BEGIN + 2        /**< Reply when unsupported features are requested. */

#define CENTRAL_LINK_COUNT              0                                           /**< Number of central links used by the application. When changing this number remember to adjust the RAM settings*/
#define PERIPHERAL_LINK_COUNT           1                                           /**< Number of peripheral links used by the application. When changing this number remember to adjust the RAM settings*/

#define DEVICE_NAME                     "Slave"                               /**< Name of device. Will be included in the advertising data. */
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

//static uint8_t							INDEX = 20;
//uint8_t  								HeartRate_RAW[BLE_NUS_MAX_DATA_LEN] = {	1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 
//																				1, 1, 1, 1, 1, 1, 1, 1, 1, 1 };

uint8_t									TimeSocket[10] = {0};
uint8_t 	adc_cnt = 0;	
uint16_t	cal_cnt = 0;			

uint16_t	test = 0;

//============================================================================================= Time Stamp Start	
#define TimeStamp

#ifdef	TimeStamp

//#include "touchsync.h"

#define BUF_SIZE 500//2048 // size of the circular buffer to store SEP samples
#define WORKING_BUF_SIZE 500 // size of the working buffer to store a selected SEP signal segment
typedef uint16_t timestamp_t;//typedef unsigned long timestamp_t; // timestamp data type
typedef uint16_t sigval_t;//int sigval_t; // SEP signal value data type
typedef signed long offset_t; // clock offset data type

#define PI 3.1415926535
#define SIGNAL_T 20000
#define INF 65535
#define PRECISION_TAG 1000000 // for Z1 it is 32768
#define ENABLE_PLL 0//1// // turn on/off PLL. 1: on; 0: off

// some global variables for solving ambiguity equation
#define MAX_IJ 20  // define the maximum i+j
#define MAX_EPSILON_ERROR 3000
#define IS_PRIOR_KNOWLEDGE_USED 1 // whether use the assymetry knowledge of transmission


timestamp_t sep_timestamp[BUF_SIZE]; // circular buffer to store timestamps of SEP samples
sigval_t sep_signal[BUF_SIZE]; // circular buffer to store SEP sample values


#ifdef TimeStamp
timestamp_t zcr[100];//timestamp_t zcr[WORKING_BUF_SIZE];
//	timestamp_t zcr_timestamp[100] = { 0 };

float ybpf[WORKING_BUF_SIZE] = { 0.0 }; /*Store the filtered data*/
offset_t delta_q,delta_solution[MAX_IJ], delta_candidate[MAX_IJ];
timestamp_t tau_solution[MAX_IJ], tau_candidate[MAX_IJ], theta_q, theta_p, tau_q, rtt;
int solve_count = 0; // record the number of solutions
int candidate_count = 0; // record the number of solutions
int session_count = 0; // record the number of sessions
int ijscale;

//timestamp_t t1, t2, t3, t4; // synchronization packet timestamps (see paper)
timestamp_t phi1, phi2, phi3, phi4; // elapsed time from the last impulse (see paper)

#endif
int buf_index = 0; // the circular bufffer position to be written

//////////////PLL related
struct STATE {
	double tau1, tau2;
	double w0;
	int UB, K0;
	double t;
	double uc;
	double phi2;
	int Q;
	int u1;
	double uf;
};

struct PLL_PARAMETER {
	double wn;
	double zeta;
	double K;
	double v0;
	double v1;
	double v2;
};
/////////////////////////


int stop_sampling = 0; // used by the main thread to notify the sampling thread to stop
//timestamp_t t0;  // store starting timestamp
bool sep_start,time_start,pwm_start = false;

	float BPF_b[] = { 0.0864434747516911, 0.0, -0.0864434747516911 };
	float BPF_a[] = { 1, -0.8773459643074454, 1.2271130504966180 };//{ 1, -1.0773459643074454, 0.8271130504966180 };//

	float BPF_z[2] = { 0.0 }; /* size = max(len(a),len(b))*/
	float y_prev = 0.0; // current filtered results, the latest filtered results
	uint16_t x_prev = 0; // the input data, the previous input data
	float ybpf_prev = 0.0;

#define 	LFCLK			(30.517578125*1e-6)
//uint32_t 	us;
uint32_t 	pre_us;
uint32_t 	diff_us;
double		count_us;
int32_t		total_us;
uint32_t	sim_mSec = 0;
	
bool 		ADC_START = false;
bool		NTP_START = false;
bool		FOLLOW_UP = false;
bool		FOLLOW_UP_START = false;
bool		BUTTON_1_PRESS = false;
	
struct	TIME
{
	uint16_t	year;
	uint8_t 	month;
	uint8_t		day;
	uint8_t		hour;
	uint8_t 	minute;
	uint8_t 	second;
	uint32_t	us;
}t0,t1,t2,t3,t4,temp;
struct TIME sys_time = {2020, 8, 8, 3, 14, 44}; 
bool Receive_Reply1	= false;
bool Receive_Reply2_t2 = false;
bool Receive_Reply2_t3 = false;

uint32_t	base_time = 0;

#endif
//============================================================================================= Time Stamp End							
							


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

void write_data(struct TIME t, char message[])
{
	uint32_t err_code;
	
	if(message[0] == '\0')
	{
		TimeSocket[0]	= t.year >> 8;
		TimeSocket[1]	= t.year & 0x00FF;
		TimeSocket[2]	= t.month;
		TimeSocket[3]	= t.day;
		TimeSocket[4]	= t.hour;
		TimeSocket[5]	= t.minute;
		TimeSocket[6]	= t.second;
		TimeSocket[7]	= (uint32_t)t.us >> 16;
		TimeSocket[8]	= ((uint32_t)t.us & 0x00FF00) >> 8;
		TimeSocket[9]	= (uint32_t)t.us & 0x0000FF;
		
		err_code = ble_nus_string_send(&m_nus, TimeSocket, 10);
		if (err_code != NRF_ERROR_INVALID_STATE)		
		{
			APP_ERROR_CHECK(err_code);
		}
		
		printf("[Send]%04d/%02d/%02d %02d:%02d:%02d %10d\r\n", t.year, t.month, t.day, t.hour, t.minute, t.second, t.us);
	}
	else
	{
		uint8_t WriteSocket[8] = {0};

		strcpy(WriteSocket, message);
		
		err_code = ble_nus_string_send(&m_nus, WriteSocket, 8);
		if (err_code != NRF_ERROR_INVALID_STATE)		
		{
			APP_ERROR_CHECK(err_code);
		}
		printf("[Send]");
		for(int i = 0; i < WriteSocket[i] != '\0'; i++)		printf("%c", WriteSocket[i]);
		printf("\r\n");
	}
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
	if(length >= 10)
	{
		if(Receive_Reply2_t2)
		{
			Receive_Reply2_t2 = false;
			
			printf("\r\n[Master][t2]");
			printf("%04d/%02d/%02d %02d:%02d:%02d %10d\r\n",  		p_data[0] << 8	|	
																	p_data[1],
																	p_data[2],
																	p_data[3],
																	p_data[4],
																	p_data[5],
																	p_data[6],
																	p_data[7] << 16	|
																	p_data[8] << 8	|
																	p_data[9]			);
			
			Receive_Reply2_t3 = true;
		}
		else if(Receive_Reply2_t3)
		{
			Receive_Reply2_t3 = false;
			
			printf("\r\n[Master][t3]");
			printf("%04d/%02d/%02d %02d:%02d:%02d %10d\r\n",  		p_data[0] << 8	|	
																	p_data[1],
																	p_data[2],
																	p_data[3],
																	p_data[4],
																	p_data[5],
																	p_data[6],
																	p_data[7] << 16	|
																	p_data[8] << 8	|
																	p_data[9]			);
			//nrf_delay_ms(1000);	// wait one second before the next synchronization session

		}
		else
		{
			printf("\r\n[Master]");
			printf("%04d/%02d/%02d %02d:%02d:%02d %10d\r\n",  		p_data[0] << 8	|	
																	p_data[1],
																	p_data[2],
																	p_data[3],
																	p_data[4],
																	p_data[5],
																	p_data[6],
																	p_data[7] << 16	|
																	p_data[8] << 8	|
																	p_data[9]			);
		}

	}
	else
	{
		printf("[Master]");
		for(int i = 0; i < length; i++)		printf("%c", p_data[i]);
		printf("\r\n");

		if( p_data[0] == 'r' &&
			p_data[1] == 'e' &&		
			p_data[2] == 'p' &&
			p_data[3] == 'l' &&
			p_data[4] == 'y' &&
			p_data[5] == '1' 	)	
		{	
			Receive_Reply1 = true;
		}
	
		if( p_data[0] == 'D' &&
			p_data[1] == 'e' &&		
			p_data[2] == 'l' &&
			p_data[3] == 'a' &&
			p_data[4] == 'y' &&
			p_data[5] == 'R' &&
			p_data[6] == 'e' &&
			p_data[7] == 'q' 	)	
		{	
			write_data(sys_time, "Delay");
			time_start = true;
			pwm_start = true;
		}	
		
	}
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
			err_code = ble_advertising_start(BLE_ADV_MODE_FAST);		//斷線後再重新開啟廣播
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

bsp_board_led_on(BSP_BOARD_LED_1);		
	
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
	
//****************************************************************************************************** Start
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
	
//	bsp_board_led_invert(BSP_BOARD_LED_2);
	
	
	if(adc_cnt == 3 && ADC_START)
	{
		adc_cnt = 0;

		//Reverse Signal
		int inverSignal = 1024 - NRF_ADC->RESULT;	// Inverting the signal value
		

#ifdef TimeStamp	
		sep_signal[buf_index] = (sigval_t)inverSignal;//(sigval_t)RAW_HR[simcnt];//
		sep_timestamp[buf_index] = (app_timer_cnt_get()*LFCLK)*1000;//sim_mSec;		// Converter to mini second
		
			// IIR frequency transfer
			ybpf[buf_index] = BPF_b[0] * sep_signal[buf_index] + BPF_z[0];
			// calcualte the recursive equations: y[n] = b0*x[0] + ((b2*x[n-1] - a2*y[n-1]) + (b1*x[1] - a1*y[n]))
			BPF_z[1] = BPF_b[2] * x_prev - BPF_a[2] * y_prev; // z[1, m - 1]
			BPF_z[0] = BPF_z[1] - BPF_a[1] * ybpf[buf_index];  // z[0, m]
			x_prev = sep_signal[buf_index];
			y_prev = ybpf[buf_index];
#endif	
		
		buf_index++;

		if(buf_index == BUF_SIZE)	
		{
			buf_index = 0;
			
			BPF_z[0] = 0;
			BPF_z[1] = 0;
			x_prev = 0;
			y_prev = 0;
			
			sep_start = true;
			ADC_START = false;
		}
	}
	
	if(cal_cnt == 1000)		// i tick is 1ms
	{
		cal_cnt = 0;
		time_start = true;
		
		pre_us = sys_time.us;
		sys_time.us = app_timer_cnt_get();
		
		// To prevent RTC1 overflow(24-bits)
		if(sys_time.us < pre_us)		diff_us = sys_time.us + (16777215 - pre_us);
		else							diff_us = sys_time.us - pre_us;
		
		// To calculate the subtraction of milis
		if(diff_us < 32768)				total_us += (32768 - diff_us);
		else 							total_us += (diff_us - 32768);
		
		//count_milis = total_milis * LFCLK;//count_milis = diff_milis * LFCLK;
		
		if(BUTTON_1_PRESS)		
		{
			BUTTON_1_PRESS = false;
			NTP_START = true;
		}
		if(FOLLOW_UP)
		{
			FOLLOW_UP = false;
			FOLLOW_UP_START = true;
		}
		if(pwm_start)
		{
			pwm_start = false;
			
			for(char i = 0; i < 3; i++)
			{
				bsp_board_led_invert(BSP_BOARD_LED_1);
				nrf_delay_us(5);
				bsp_board_led_invert(BSP_BOARD_LED_1);
				nrf_delay_us(50);
			}
			nrf_delay_us(150);
			for(char i = 0; i < 2; i++)
			{
				bsp_board_led_invert(BSP_BOARD_LED_1);
				nrf_delay_us(5);
				bsp_board_led_invert(BSP_BOARD_LED_1);
				nrf_delay_us(50);
			}
			nrf_delay_us(150);
			
			bsp_board_led_invert(BSP_BOARD_LED_1);
			nrf_delay_us(5);
			bsp_board_led_invert(BSP_BOARD_LED_1);
		}
		
		base_time = app_timer_cnt_get(); 

		sys_time.second++;
		if(sys_time.second == 60)
		{
			sys_time.second = 0;
			
			sys_time.minute++;
			if(sys_time.minute == 60)
			{
				sys_time.minute = 0;
				
				sys_time.hour++;
				if(sys_time.hour == 24)
				{
					sys_time.hour = 0;
					
					sys_time.day++;
					if(sys_time.day == 30)
					{
						sys_time.day = 0;
						
						sys_time.month++;
						
						if(sys_time.month == 12)
						{
							sys_time.month = 0;
							
							sys_time.year++;
						}
					}
				}
			}
		}
	}
	adc_cnt++;
	cal_cnt++;
	
//	sim_mSec++;
//	if(sim_mSec >= 4294900000)		sim_mSec = 0;
}

void EZCR(uint16_t len, uint16_t * zcr_len)
{
	uint16_t i, j;
	/* Rising edge detection */
	// Should be global, the signal processing is real-time
	uint8_t negative_cur = 1;
	uint8_t negative_prev = 1;


	float timestamp_prev = 0.0;

	/* Zero-Crossing Detection */
//	timestamp_t zcr_timestamp[150] = { 0 };



	/* BPF related */
	// Init
	// 727Hz, [45Hz,55Hz], butter
	// float BPF_b[] ={0.04143578, 0., -0.04143578};
	// float BPF_a[] = {1., -1.74262779, 0.91712843};

	// 364Hz, [45Hz,55Hz], butter
	//float BPF_b[] = { 0.07963244, 0., -0.7963244 };
	//float BPF_a[] = { 1., -1.2011403, 0.84073512 };

	// 333Hz, [45Hz,55Hz], butter
//	float BPF_b[] = { 0.0864434747516911, 0.0, -0.0864434747516911 };
//	float BPF_a[] = { 1, -1.0773459643074454, 0.8271130504966180 };

//	float BPF_z[2] = { 0.0 }; /* size = max(len(a),len(b))*/
//	float y_prev = 0.0; // current filtered results, the latest filtered results
//	uint16_t x_prev = 0; // the input data, the previous input data
//	//float ybpf[WORKING_BUF_SIZE] = { 0.0 }; /*Store the filtered data*/
//	float ybpf_prev = 0.0;

	/* PLL related*/
//	timestamp_t prev_u2_timestamp = 0;
//	timestamp_t prev_zcr_timestamp = 0;
//	float phi = 0.0, last_phi = 0.0, phi_prev = 0.0;
//	float phi_hat = 0.0, phi_hat_prev = 0.0, phi_hat_prev2 = 0.0;
//	float delta_phi;
//	float zcr_interval_current;
//	uint16_t k, cnt2 = 0; // 512 maximum for uint8_t
//	uint8_t cnt_compensateClock; // 512 maximum
//	float compensateClockCycle = 0.02;
//	float PLL_v0 = 0.0, PLL_v1 = 0.0, PLL_v2 = 0.0;
//	//float PLL_a0;
//	float PLL_a1, PLL_a2;
//	float PLL_b0, PLL_b1, PLL_b2;
//	//struct PLL_PARAMETER * pll_para = (struct PLL_PARAMETER *)malloc(sizeof(struct PLL_PARAMETER));
//	struct PLL_PARAMETER pll_para[1];

	// BPF processing
	//currentTicksH = call LocalTime.get();
	//printfz1("BPF %lu\n", currentTicksH);
	/* band-pass filter IIR
	* input v: original sample
	* output ybpf: filtered sample
	*/
//	for (i = 0; i < len; i++) {
//		ybpf[i] = BPF_b[0] * sep_signal[i] + BPF_z[0];
//		// calcualte the recursive equations
//		BPF_z[1] = BPF_b[2] * x_prev - BPF_a[2] * y_prev; // z[1, m - 1]
//		BPF_z[0] = BPF_z[1] - BPF_a[1] * ybpf[i];  // z[0, m]
//		x_prev = sep_signal[i];
//		y_prev = ybpf[i];
//	}
	
	///////// Overhead monitorint (Z1) ////////
	// currentTicksH = call LocalTime.get();
	// printfz1("ZCR %lu\n", currentTicksH);
	//////////////////////////////////////////

	// uint8_t deadzone = SAMPLING_RATE * 0.0075
	//         fs = 333Hz, deadzone = 2
	j = 0;
	for (i = 0; i < len; i++) 
	{
		//printf("ybpf[%d] = %f\n", i, ybpf[i]);
		if (ybpf[i] > 0.0) 
		{
			negative_cur = 0;
			if (negative_prev == 1) {
				// linear interpolation
				//printf("%d\n",i);
				zcr[j] = timestamp_prev + ybpf_prev * ((sep_timestamp[i] - sep_timestamp[0]) * 1.0 - timestamp_prev) / (ybpf_prev - ybpf[i]);//zcr_timestamp[j] = timestamp_prev + ybpf_prev * ((sep_timestamp[i] - sep_timestamp[0]) * 1.0 - timestamp_prev) / (ybpf_prev - ybpf[i]);
				//printf("[%u]\tBPF %luticks\t%luticks\n", j, zcr_timestamp[j], (zcr_timestamp[j] - prev_zcr_timestamp));
//				prev_zcr_timestamp = zcr_timestamp[j]; // should be comment if the above printf is disabled
				i = i + 2; // use deadzone to avoid jitter
				j++;
			}
		}
		else 
		{
			negative_cur = 1;
			timestamp_prev = sep_timestamp[i] - sep_timestamp[0];
			ybpf_prev = ybpf[i];
		}
		negative_prev = negative_cur;
	}

//	if (ENABLE_PLL) {
//		// PLL parameter init
//		// This part could be replaced once all the paramters are finalized
//		pll_para->wn = 0.03;
//		pll_para->zeta = 0.9;
//		pll_para->K = 1000.0;
//		pll_para->v0 = 0.0;
//		pll_para->v1 = 0.0;
//		pll_para->v2 = 0.0;

//		// PLL processing
//		//currentTicksH = call LocalTime.get();
//		//printfz1("PLL %lu\n", currentTicksH);
//		/* if ZCR found in this batch */
//        /* If more than 1 ZCRs are found in this batch*/
//		if (j > 1) {
//			/* assign the timestamp for each zero crossing point */
//			// note on the definition of 20ms
//			// create the 20ms ZCR

//			float tau1 = 0.0, tau2 = 0.0;

//			// PLL parameter init
//			// This part could be replaced once all the paramters are finalized
//			// compute the coefficients
//			tau1 = pll_para->K / pll_para->wn / pll_para->wn;
//			tau2 = 2 * pll_para->zeta / pll_para->wn;

//			PLL_b0 = 4 * pll_para->K / tau1*(1 + tau2 / 2);
//			PLL_b1 = 8 * pll_para->K / tau1;
//			PLL_b2 = 4 * pll_para->K / tau1 * (1 - tau2 / 2);
//			//PLL_a0 = 1.0;
//			PLL_a1 = -2.0;
//			PLL_a2 = 1.0;

//			// PLL processing
//			for (i = 1; i < j; i++) {
//				phi = ((zcr_timestamp[i] - zcr_timestamp[1]) * 1.0 / PRECISION_TAG); // potentional last digit precision loss


//				last_phi = phi; // push

//				delta_phi = phi - phi_hat;
//				zcr_interval_current = phi - phi_prev;

//				/////////////////////ZCR compensation//////////////////////////////////////
//				if (zcr_interval_current > 0.025) {
//					cnt_compensateClock = (phi - phi_prev) / 0.02; // use integer part only
//					phi = phi_prev;
//					k = 0;
//					while (k < cnt_compensateClock) {
//						phi = phi + compensateClockCycle;
//						delta_phi = phi - phi_hat;

//						//printf("%u\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\t", cnt2, phi, (phi - phi_prev), phi_hat, (phi_hat - phi_hat_prev2), ((phi_hat - phi_hat_prev2) - (phi - phi_prev)), delta_phi);
//						zcr[cnt2] = phi_hat * PRECISION_TAG + zcr_timestamp[1];

//						//printf("PLL %luus\t%luus\n", zcr[cnt2], (zcr[cnt2] - prev_u2_timestamp));
////                        prev_u2_timestamp = zcr[cnt2]; // should be comment if corresponding printf is/are disabled
//                        //fprintf(fpOutput, "%u\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\n", cnt2, phi, (phi - phi_prev), phi_hat, (phi_hat - phi_hat_prev2), ((phi_hat - phi_hat_prev2) - (phi - phi_prev)), delta_phi);

//						cnt2++;

//						//////// PLL computing
//						// advance buffer
//						PLL_v2 = PLL_v1;  // shift center register to upper register
//						PLL_v1 = PLL_v0;  // shift lower register to center register
//										  // compute new lower register
//						PLL_v0 = delta_phi - PLL_v1*PLL_a1 - PLL_v2*PLL_a2;
//						// compute new output
//						phi_hat = PLL_v0*PLL_b0 + PLL_v1*PLL_b1 + PLL_v2*PLL_b2;

//						phi_prev = phi;
////						phi_hat_prev2 = phi_hat_prev; // should be comment if corresponding printf is/are disabled
//						phi_hat_prev = phi_hat;
//						///////////////////////

//						k++;
//					}
//				}
//				////////////////// -END- ZCR compensation  ////////////////////////////


//				phi = last_phi; // pop

//                //printf("%u\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\t%.8f\t", cnt2, phi, (phi - phi_prev), phi_hat, (phi_hat - phi_hat_prev2), ((phi_hat - phi_hat_prev2) - (phi - phi_prev)), delta_phi);

//				//zcr[cnt2] = (phi_hat * PRECISION_TAG + zcr_timestamp[1]) * 1000 / PRECISION_TAG;
//				//printfz1("PLL %lums\t%lums\n", zcr[cnt2], (zcr[cnt2] - prev_u2_timestamp));

//				// output ticks
//				zcr[cnt2] = phi_hat * PRECISION_TAG + zcr_timestamp[1];
//				//printf("t[0] = %ld\tsum=%ld\n",t[0],(phi_hat*PRECISION_TAG + zcr_timestamp[1] + t[0]));
////				printf("PLL %ldticks\t%ldticks\n", zcr[cnt2], (zcr[cnt2] - prev_u2_timestamp));
////				prev_u2_timestamp = zcr[cnt2]; // should be comment if corresponding printf is/are disabled
//				cnt2 = cnt2 + 1;

//				//////// PLL computing
//				// advance buffer
//				PLL_v2 = PLL_v1;  // shift center register to upper register
//				PLL_v1 = PLL_v0;  // shift lower register to center register
//								  // compute new lower register
//				PLL_v0 = delta_phi - PLL_v1*PLL_a1 - PLL_v2*PLL_a2;
//				// compute new output
//				phi_hat = PLL_v0*PLL_b0 + PLL_v1*PLL_b1 + PLL_v2*PLL_b2;

//				phi_prev = phi;
////				phi_hat_prev2 = phi_hat_prev; // should be comment if corresponding printf is/are disabled
//				phi_hat_prev = phi_hat;
//				///////////////////////
//			}
//			//////// -End- PLL processing //////////////////////
//		}
//		///////////// -END- PLL and missing ZCR compensation //////////////////

//		*zcr_len = cnt2;
//	}
//	else {
//		for (i = 0; i < j; i++) {
//			zcr[i] = zcr_timestamp[i];
//		}
//		*zcr_len = j;
//	}
//	
	// Print ADC result to UART
//	for(int i=0; i<len; i++)	
//	{ 
////		if(i < 150)		printf("%f\t%f\t%f\n", sep_signal[i], ybpf[i], zcr_timestamp[i]);
////		else 			printf("%f\t%f\n", sep_signal[i], ybpf[i]);
//		//printf("%f\t%f\n", sep_signal[i], ybpf[i]);
//		//printf("%f\t\n", (float)sep_signal[i]);
//		printf("%f\t\n", (float)ybpf[i]);
//		//printf("%f\t\n", (float)zcr_timestamp[i]);
//		//printf("%f\t\n", (float)zcr[i]);
//	}	
	
//	NRF_PPI->CHEN = (PPI_CHEN_CH0_Enabled << PPI_CHEN_CH0_Pos);
}

void signal_processing_algorithms()
{
	int len = BUF_SIZE;//int len;
//	int i;
	uint16_t zcr_len = 0;	
	
	EZCR(len, &zcr_len);

	phi2 = INF;
	phi3 = INF;
//	for (i = 1; i < zcr_len; i++)
//	{
////		printf("t2=%lu, t3=%lu\t", t2, t3);
////		printf("zcr[i-1] + t[0]:%lu,\tzcr[i] + t[0]:%lu\r\n", zcr[i - 1] + sep_timestamp[0], zcr[i] + sep_timestamp[0]);
//		if (phi2 == INF)
//		{
//			if ((t2 >= zcr[i - 1] + sep_timestamp[0]) && (t2 < zcr[i] + sep_timestamp[0]))
//			{
//				phi2 = t2 - zcr[i - 1] - sep_timestamp[0];
////				printf("phi2:%lu\r\n", phi2);
//			}
//		}
//		if (phi3 == INF)
//		{
//			if ((t3 >= zcr[i - 1] + sep_timestamp[0]) && (t3 < zcr[i] + sep_timestamp[0]))
//			{
//				phi3 = t3 - zcr[i - 1] - sep_timestamp[0];
////				printf("phi3:%lu\r\n", phi3);
//			}
//		}
//	}
//	printf("phi2:%lu ,phi3:%lu\r\n", phi2, phi3);
//	printf("--------------------");
}

/**@brief Application main function.
 */
int main(void)
{
    uint32_t err_code;
    bool erase_bonds;

    // Initialize.
    uart_init();
	adc_init();
	timer_init();
	ppi_init(); 

	
    buttons_leds_init(&erase_bonds);
    ble_stack_init();
    gap_params_init();
    services_init();
    advertising_init();
    conn_params_init();

    printf("\r\nSlave Start!!!\r\n");
    err_code = ble_advertising_start(BLE_ADV_MODE_FAST);
    APP_ERROR_CHECK(err_code);

    // Enter main loop.
    for (;;)
    {
        power_manage();
		
		if(sep_start)
		{
			sep_start = false;
			//bsp_board_led_invert(BSP_BOARD_LED_1);
			signal_processing_algorithms();
			
//			err_code = ble_nus_string_send(&m_nus, HeartRate_RAW, INDEX);
//			if (err_code != NRF_ERROR_INVALID_STATE)
//			{
//				APP_ERROR_CHECK(err_code);
//			}
			
//			printf("\r\n%d/%d/%d %d:%d:%d.%lu\r\n", year, month, day, hour, minute, second, app_timer_cnt_get());
		}		
		
		if(time_start)
		{
			time_start = false;
			
			TimeSocket[0]	= sys_time.year >> 8;
			TimeSocket[1]	= sys_time.year & 0x00FF;
			TimeSocket[2]	= sys_time.month;
			TimeSocket[3]	= sys_time.day;
			TimeSocket[4]	= sys_time.hour;
			TimeSocket[5]	= sys_time.minute;
			TimeSocket[6]	= sys_time.second;
			TimeSocket[7]	= (uint32_t)total_us >> 16;//(uint32_t)milis >> 16;
			TimeSocket[8]	= ((uint32_t)total_us & 0x00FF00) >> 8;//((uint32_t)milis & 0x00FF00) >> 8;
			TimeSocket[9]	= (uint32_t)total_us & 0x0000FF;//(uint32_t)milis & 0x0000FF;

			printf("%04d/%02d/%02d %02d:%02d:%02d\r\n", sys_time.year, sys_time.month, sys_time.day, sys_time.hour, sys_time.minute, sys_time.second);//printf("%04d/%02d/%02d %02d:%02d:%02d %10d\r\n", sys_time.year, sys_time.month, sys_time.day, sys_time.hour, sys_time.minute, sys_time.second, sys_time.us);//printf("%04d/%02d/%02d %02d:%02d:%02d %10d %10f %10d\r\n", sys_time.year, sys_time.month, sys_time.day, sys_time.hour, sys_time.minute, sys_time.second, total_us, total_us*LFCLK, us);
		}
			
		// Let sample start!
		if(!nrf_gpio_pin_read(BUTTON_4) && !ADC_START)
		{
			ADC_START = true;
			
			//nrf_delay_ms(60);		// Wait until the adc buffer has been filled with some data	
			
			t0		= sys_time;
			t0.us	= app_timer_cnt_get();
			printf("\r\n[t0] %04d/%02d/%02d %02d:%02d:%02d %10d\r\n", t0.year, t0.month, t0.day, t0.hour, t0.minute, t0.second, t0.us);
			
//			t1		= sys_time;
			t1.us	= app_timer_cnt_get();
			//nrf_delay_ms(100);	// simulate a random packet transmission delay that is uniformly distributed within [0,100ms]
			write_data(sys_time, "request");
			t1.year		= sys_time.year;
			t1.month	= sys_time.month;
			t1.day		= sys_time.day;
			t1.hour		= sys_time.hour;
			t1.minute	= sys_time.minute;
			t1.second	= sys_time.second;
			printf("[t1] %04d/%02d/%02d %02d:%02d:%02d %10d\r\n", t1.year, t1.month, t1.day, t1.hour, t1.minute, t1.second, t1.us);
		}
		while(Receive_Reply1)
		{			
			Receive_Reply1 = false;

//			t4		= sys_time;
			//nrf_delay_ms(100);	// simulate a random packet transmission delay that is uniformly distributed within [0,100ms]
			t4.us	= app_timer_cnt_get();
			t4.year		= sys_time.year;
			t4.month	= sys_time.month;
			t4.day		= sys_time.day;
			t4.hour		= sys_time.hour;
			t4.minute	= sys_time.minute;
			t4.second	= sys_time.second;
			printf("[t4] %04d/%02d/%02d %02d:%02d:%02d %10d\r\n\r\n", t4.year, t4.month, t4.day, t4.hour, t4.minute, t4.second, t4.us);	
			printf("========== t = %fms(%d) ==========\r\n", (t4.us-t1.us)*1000*LFCLK, t4.us-t1.us);
			
			//nrf_delay_ms(60);	// simulate a random packet transmission delay that is uniformly distributed within [0,100ms]
			
			signal_processing_algorithms();
			
			Receive_Reply2_t2 = true;
		}
		
		if(!nrf_gpio_pin_read(BUTTON_3) && !ADC_START)
		{
			ADC_START = true;
			
			write_data(sys_time, "");
		}  

		if(!nrf_gpio_pin_read(BUTTON_2) && !ADC_START)
		{
			ADC_START = true;
			
			write_data(sys_time, "error");
		}  
		
		// NTP Protocol source
		if(!nrf_gpio_pin_read(BUTTON_1))		
		{
			BUTTON_1_PRESS = true;
			time_start = false;
		}
		if(NTP_START)
		{
			NTP_START = false;
			
			// Sync message
			temp.us = app_timer_cnt_get() - base_time;
			write_data(sys_time, "Sync");
			temp.year		= sys_time.year;
			temp.month		= sys_time.month;
			temp.day		= sys_time.day;
			temp.hour		= sys_time.hour;
			temp.minute		= sys_time.minute;
			temp.second		= sys_time.second;

			FOLLOW_UP = true;	
		}
		if(FOLLOW_UP_START)
		{
			FOLLOW_UP_START = false;
			
			// Follow up message
			write_data(temp, "");
//			pwm_start = true;
		}
		

	}
}


/**
 * @}
 */
