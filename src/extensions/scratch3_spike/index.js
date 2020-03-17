const ArgumentType = require('../../extension-support/argument-type');
const BlockType = require('../../extension-support/block-type');
const Cast = require('../../util/cast');
const formatMessage = require('format-message');
const uid = require('../../util/uid');
const BT = require('../../io/bt');
const Base64Util = require('../../util/base64-util');
const MathUtil = require('../../util/math-util');
const RateLimiter = require('../../util/rateLimiter.js');
const log = require('../../util/log');

/**
 * Icon svg to be displayed at the left edge of each extension block, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const blockIconURI = 'data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iVVRGLTgiPz4KPHN2ZyB3aWR0aD0iNDBweCIgaGVpZ2h0PSI0MHB4IiB2aWV3Qm94PSIwIDAgNDAgNDAiIHZlcnNpb249IjEuMSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIiB4bWxuczp4bGluaz0iaHR0cDovL3d3dy53My5vcmcvMTk5OS94bGluayI+CiAgICA8IS0tIEdlbmVyYXRvcjogU2tldGNoIDU5LjEgKDg2MTQ0KSAtIGh0dHBzOi8vc2tldGNoLmNvbSAtLT4KICAgIDx0aXRsZT5zcGlrZS1zbWFsbDwvdGl0bGU+CiAgICA8ZGVzYz5DcmVhdGVkIHdpdGggU2tldGNoLjwvZGVzYz4KICAgIDxnIGlkPSJzcGlrZS1zbWFsbCIgc3Ryb2tlPSJub25lIiBzdHJva2Utd2lkdGg9IjEiIGZpbGw9Im5vbmUiIGZpbGwtcnVsZT0iZXZlbm9kZCI+CiAgICAgICAgPHJlY3QgZmlsbD0iI0ZGRDUwMCIgeD0iMCIgeT0iMCIgd2lkdGg9IjQwIiBoZWlnaHQ9IjQwIj48L3JlY3Q+CiAgICAgICAgPGcgaWQ9Ikdyb3VwLUNvcHkiIHRyYW5zZm9ybT0idHJhbnNsYXRlKDEuMDAwMDAwLCAxLjAwMDAwMCkiIGZpbGw9IiNGRkZGRkYiPgogICAgICAgICAgICA8cG9seWdvbiBpZD0iUmVjdGFuZ2xlIiBwb2ludHM9IjggOCAxNCA4IDE0IDE0IDggMTQiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5IiBwb2ludHM9IjggNC45OTYwMDM2MWUtMTYgMTQgMi40OTgwMDE4MWUtMTYgMTQgNiA4IDYiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTMiIHBvaW50cz0iMTYgMTYgMjIgMTYgMjIgMjIgMTYgMjIiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTQiIHBvaW50cz0iMTYgMjQgMjIgMjQgMjIgMzAgMTYgMzAiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTEzIiBwb2ludHM9IjI0IDI0IDMwIDI0IDMwIDMwIDI0IDMwIj48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS0xMiIgcG9pbnRzPSIxNiAzMiAyMiAzMiAyMiAzOCAxNiAzOCI+PC9wb2x5Z29uPgogICAgICAgICAgICA8cG9seWdvbiBpZD0iUmVjdGFuZ2xlLUNvcHktMTEiIHBvaW50cz0iOCAxNiAxNCAxNiAxNCAyMiA4IDIyIj48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS0xMCIgcG9pbnRzPSI4IDI0IDE0IDI0IDE0IDMwIDggMzAiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTIiIHBvaW50cz0iMTYgOCAyMiA4IDIyIDE0IDE2IDE0Ij48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS05IiBwb2ludHM9IjAgMTYgNiAxNiA2IDIyIDAgMjIiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTgiIHBvaW50cz0iMCA4IDYgOCA2IDE0IDAgMTQiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTciIHBvaW50cz0iMjQgOCAzMCA4IDMwIDE0IDI0IDE0Ij48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS02IiBwb2ludHM9IjI0IDE2IDMwIDE2IDMwIDIyIDI0IDIyIj48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS0xNSIgcG9pbnRzPSIzMiA4IDM4IDggMzggMTQgMzIgMTQiPjwvcG9seWdvbj4KICAgICAgICAgICAgPHBvbHlnb24gaWQ9IlJlY3RhbmdsZS1Db3B5LTE0IiBwb2ludHM9IjMyIDE2IDM4IDE2IDM4IDIyIDMyIDIyIj48L3BvbHlnb24+CiAgICAgICAgICAgIDxwb2x5Z29uIGlkPSJSZWN0YW5nbGUtQ29weS01IiBwb2ludHM9IjI0IDQuOTk2MDAzNjFlLTE2IDMwIDIuNDk4MDAxODFlLTE2IDMwIDYgMjQgNiI+PC9wb2x5Z29uPgogICAgICAgIDwvZz4KICAgIDwvZz4KPC9zdmc+';

/**
 * A maximum number of BT message sends per second, to be enforced by the rate limiter.
 * @type {number}
 */
const BTSendRateMax = 40;

/**
 * Enum for Ev3 parameter encodings of various argument and return values.
 * Found in the 'EV3 Firmware Developer Kit', section4, page 9, at
 * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
 *
 * The format for these values is:
 * 0xxxxxxx for Short Format
 * 1ttt-bbb for Long Format
 *
 * @readonly
 * @enum {number}
 */
const Ev3Encoding = {
    ONE_BYTE: 0x81, // = 0b1000-001, "1 byte to follow"
    TWO_BYTES: 0x82, // = 0b1000-010, "2 bytes to follow"
    FOUR_BYTES: 0x83, // = 0b1000-011, "4 bytes to follow"
    GLOBAL_VARIABLE_ONE_BYTE: 0xE1, // = 0b1110-001, "1 byte to follow"
    GLOBAL_CONSTANT_INDEX_0: 0x20, // = 0b00100000
    GLOBAL_VARIABLE_INDEX_0: 0x60 // = 0b01100000
};

/**
 * Enum for Ev3 direct command types.
 * Found in the 'EV3 Communication Developer Kit', section 4, page 24, at
 * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
 * @readonly
 * @enum {number}
 */
const Ev3Command = {
    DIRECT_COMMAND_REPLY: 0x00,
    DIRECT_COMMAND_NO_REPLY: 0x80,
    DIRECT_REPLY: 0x02
};

/**
 * Enum for Ev3 commands opcodes.
 * Found in the 'EV3 Firmware Developer Kit', section 4, page 10, at
 * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
 * @readonly
 * @enum {number}
 */
const Ev3Opcode = {
    OPOUTPUT_STEP_SPEED: 0xAE,
    OPOUTPUT_TIME_SPEED: 0xAF,
    OPOUTPUT_STOP: 0xA3,
    OPOUTPUT_RESET: 0xA2,
    OPOUTPUT_STEP_SYNC: 0xB0,
    OPOUTPUT_TIME_SYNC: 0xB1,
    OPOUTPUT_GET_COUNT: 0xB3,
    OPSOUND: 0x94,
    OPSOUND_CMD_TONE: 1,
    OPSOUND_CMD_STOP: 0,
    OPINPUT_DEVICE_LIST: 0x98,
    OPINPUT_READSI: 0x9D
};

/**
 * Enum for Ev3 values used as arguments to various opcodes.
 * Found in the 'EV3 Firmware Developer Kit', section4, page 10-onwards, at
 * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
 * @readonly
 * @enum {number}
 */
const Ev3Args = {
    LAYER: 0, // always 0, chained EV3s not supported
    COAST: 0,
    BRAKE: 1,
    RAMP: 50, // time in milliseconds
    DO_NOT_CHANGE_TYPE: 0,
    MAX_DEVICES: 32 // 'Normally 32' from pg. 46
};

const SpikeOrientation = {
    any: 0,
    front: 1,
    back: 2,
    up: 3,
    down: 4,
    rightside: 5,
    leftside: 6
};

/**
 * Manage power, direction, and timers for one EV3 motor.
 */
class EV3Motor {

    /**
     * Construct a EV3 Motor instance, which could be of type 'largeMotor' or
     * 'mediumMotor'.
     *
     * @param {EV3} parent - the EV3 peripheral which owns this motor.
     * @param {int} index - the zero-based index of this motor on its parent peripheral.
     * @param {string} type - the type of motor (i.e. 'largeMotor' or 'mediumMotor').
     */
    constructor(parent, index, type) {
        /**
         * The EV3 peripheral which owns this motor.
         * @type {EV3}
         * @private
         */
        this._parent = parent;

        /**
         * The zero-based index of this motor on its parent peripheral.
         * @type {int}
         * @private
         */
        this._index = index;

        /**
         * The type of EV3 motor this could be: 'largeMotor' or 'mediumMotor'.
         * @type {string}
         * @private
         */
        this._type = type;

        /**
         * This motor's current direction: 1 for "clockwise" or -1 for "counterclockwise"
         * @type {number}
         * @private
         */
        this._direction = 1;

        /**
         * This motor's current power level, in the range [0,100].
         * @type {number}
         * @private
         */
        this._power = 50;

        /**
         * This motor's current position, in the range [0,360].
         * @type {number}
         * @private
         */
        this._position = 0;

        /**
         * An ID for the current coast command, to help override multiple coast
         * commands sent in succession.
         * @type {number}
         * @private
         */
        this._commandID = null;

        /**
         * A delay, in milliseconds, to add to coasting, to make sure that a brake
         * first takes effect if one was sent.
         * @type {number}
         * @private
         */
        this._coastDelay = 1000;
    }

    /**
     * @return {string} - this motor's type: 'largeMotor' or 'mediumMotor'
     */
    get type() {
        return this._type;
    }

    /**
     * @param {string} value - this motor's new type: 'largeMotor' or 'mediumMotor'
     */
    set type(value) {
        this._type = value;
    }

    /**
     * @return {int} - this motor's current direction: 1 for "clockwise" or -1 for "counterclockwise"
     */
    get direction() {
        return this._direction;
    }

    /**
     * @param {int} value - this motor's new direction: 1 for "clockwise" or -1 for "counterclockwise"
     */
    set direction(value) {
        if (value < 0) {
            this._direction = -1;
        } else {
            this._direction = 1;
        }
    }

    /**
     * @return {int} - this motor's current power level, in the range [0,100].
     */
    get power() {
        return this._power;
    }

    /**
     * @param {int} value - this motor's new power level, in the range [0,100].
     */
    set power(value) {
        this._power = value;
    }

    /**
     * @return {int} - this motor's current position, in the range [-inf,inf].
     */
    get position() {
        return this._position;
    }

    /**
     * @param {int} array - this motor's new position, in the range [0,360].
     */
    set position(array) {
        // tachoValue from Paula
        let value = array[0] + (array[1] * 256) + (array[2] * 256 * 256) + (array[3] * 256 * 256 * 256);
        if (value > 0x7fffffff) {
            value = value - 0x100000000;
        }
        this._position = value;
    }

    /**
     * Turn this motor on for a specific duration.
     * Found in the 'EV3 Firmware Developer Kit', page 56, at
     * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
     *
     * Opcode arguments:
     * (Data8) LAYER – Specify chain layer number [0 - 3]
     * (Data8) NOS – Output bit field [0x00 – 0x0F]
     * (Data8) SPEED – Power level, [-100 – 100]
     * (Data32) STEP1 – Time in milliseconds for ramp up
     * (Data32) STEP2 – Time in milliseconds for continues run
     * (Data32) STEP3 – Time in milliseconds for ramp down
     * (Data8) BRAKE - Specify break level [0: Float, 1: Break]
     *
     * @param {number} milliseconds - run the motor for this long.
     */
    turnOnFor(milliseconds) {
        if (this._power === 0) return;

        const port = this._portMask(this._index);
        let n = milliseconds;
        let speed = this._power * this._direction;
        const ramp = Ev3Args.RAMP;

        let byteCommand = [];
        byteCommand[0] = Ev3Opcode.OPOUTPUT_TIME_SPEED;

        // If speed is less than zero, make it positive and multiply the input
        // value by -1
        if (speed < 0) {
            speed = -1 * speed;
            n = -1 * n;
        }
        // If the input value is less than 0
        const dir = (n < 0) ? 0x100 - speed : speed; // step negative or positive
        n = Math.abs(n);
        // Setup motor run duration and ramping behavior
        let rampup = ramp;
        let rampdown = ramp;
        let run = n - (ramp * 2);
        if (run < 0) {
            rampup = Math.floor(n / 2);
            run = 0;
            rampdown = n - rampup;
        }
        // Generate motor command values
        const runcmd = this._runValues(run);
        byteCommand = byteCommand.concat([
            Ev3Args.LAYER,
            port,
            Ev3Encoding.ONE_BYTE,
            dir & 0xff,
            Ev3Encoding.ONE_BYTE,
            rampup
        ]).concat(runcmd.concat([
            Ev3Encoding.ONE_BYTE,
            rampdown,
            Ev3Args.BRAKE
        ]));

        const cmd = this._parent.generateCommand(
            Ev3Command.DIRECT_COMMAND_NO_REPLY,
            byteCommand
        );

        this._parent.send(cmd);

        this.coastAfter(milliseconds);
    }

    /**
     * Set the motor to coast after a specified amount of time.
     * @param {number} time - the time in milliseconds.
     */
    coastAfter(time) {
        if (this._power === 0) return;

        // Set the motor command id to check before starting coast
        const commandId = uid();
        this._commandID = commandId;

        // Send coast message
        setTimeout(() => {
            // Do not send coast if another motor command changed the command id.
            if (this._commandID === commandId) {
                this.coast();
                this._commandID = null;
            }
        }, time + this._coastDelay); // add a delay so the brake takes effect
    }

    /**
     * Set the motor to coast.
     */
    coast() {
        if (this._power === 0) return;

        const cmd = this._parent.generateCommand(
            Ev3Command.DIRECT_COMMAND_NO_REPLY,
            [
                Ev3Opcode.OPOUTPUT_STOP,
                Ev3Args.LAYER,
                this._portMask(this._index), // port output bit field
                Ev3Args.COAST
            ]
        );

        this._parent.send(cmd, false); // don't use rate limiter to ensure motor stops
    }

    /**
     * Generate motor run values for a given input.
     * @param  {number} run - run input.
     * @return {array} - run values as a byte array.
     */
    _runValues(run) {
        // If run duration is less than max 16-bit integer
        if (run < 0x7fff) {
            return [
                Ev3Encoding.TWO_BYTES,
                run & 0xff,
                (run >> 8) & 0xff
            ];
        }

        // Run forever
        return [
            Ev3Encoding.FOUR_BYTES,
            run & 0xff,
            (run >> 8) & 0xff,
            (run >> 16) & 0xff,
            (run >> 24) & 0xff
        ];
    }

    /**
     * Return a port value for the EV3 that is in the format for 'output bit field'
     * as 1/2/4/8, generally needed for motor ports, instead of the typical 0/1/2/3.
     * The documentation in the 'EV3 Firmware Developer Kit' for motor port arguments
     * is sometimes mistaken, but we believe motor ports are mostly addressed this way.
     * @param {number} port - the port number to convert to an 'output bit field'.
     * @return {number} - the converted port number.
     */
    _portMask(port) {
        return Math.pow(2, port);
    }
}

class Spike {

    constructor(runtime, extensionId) {

        /**
         * The Scratch 3.0 runtime used to trigger the green flag button.
         * @type {Runtime}
         * @private
         */
        this._runtime = runtime;
        this._runtime.on('PROJECT_STOP_ALL', this.stopAll.bind(this));

        /**
         * The id of the extension this peripheral belongs to.
         */
        this._extensionId = extensionId;

        /**
         * A list of the names of the sensors connected in ports 1,2,3,4.
         * @type {string[]}
         * @private
         */
        this._sensorPorts = [];

        /**
         * A list of the names of the motors connected in ports A,B,C,D.
         * @type {string[]}
         * @private
         */
        this._motorPorts = [];

        /**
         * The state of all sensor values.
         * @type {string[]}
         * @private
         */
        this._sensors = {
            distance: 0,
            brightness: 0,
            buttons: [0, 0, 0, 0],
            angle: {
                pitch: 0,
                roll: 0,
                yaw: 0
            },
            orientation: SpikeOrientation.front
        };

        /**
         * The motors which this EV3 could possibly have connected.
         * @type {string[]}
         * @private
         */
        this._motors = [null, null, null, null];

        this._pixelBrightness = 100;

        /**
         * The Bluetooth socket connection for reading/writing peripheral data.
         * @type {BT}
         * @private
         */
        this._bt = null;
        this._runtime.registerPeripheralExtension(extensionId, this);

        /**
         * A rate limiter utility, to help limit the rate at which we send BT messages
         * over the socket to Scratch Link to a maximum number of sends per second.
         * @type {RateLimiter}
         * @private
         */
        this._rateLimiter = new RateLimiter(BTSendRateMax);

        this.reset = this.reset.bind(this);
        this._onConnect = this._onConnect.bind(this);
        this._onMessage = this._onMessage.bind(this);

        this._openRequests = {};
    }

    get distance() {
        let value = this._sensors.distance > 100 ? 100 : this._sensors.distance;
        value = value < 0 ? 0 : value;
        value = Math.round(100 * value) / 100;

        return value;
    }

    get brightness() {
        return this._sensors.brightness;
    }

    get angle() {
        return this._sensors.angle;
    }

    get orientation() {
        return this._sensors.orientation;
    }

    get pixelBrightness() {
        return this._pixelBrightness;
    }

    set pixelBrightness(value) {
        this._pixelBrightness = value;
    }

    /**
     * Access a particular motor on this peripheral.
     * @param {int} index - the zero-based index of the desired motor.
     * @return {EV3Motor} - the EV3Motor instance, if any, at that index.
     */
    motor(index) {
        return this._motors[index];
    }

    isButtonPressed(port) {
        return this._sensors.buttons[port] === 1;
    }

    beep(freq, time) {
        const cmd = this.generateCommand(
            Ev3Command.DIRECT_COMMAND_NO_REPLY,
            [
                Ev3Opcode.OPSOUND,
                Ev3Opcode.OPSOUND_CMD_TONE,
                Ev3Encoding.ONE_BYTE,
                2,
                Ev3Encoding.TWO_BYTES,
                freq,
                freq >> 8,
                Ev3Encoding.TWO_BYTES,
                time,
                time >> 8
            ]
        );

        this.send(cmd);
    }

    stopAll() {
        /*
        this.stopAllMotors();
        this.stopSound();
        */
    }

    stopSound() {
        const cmd = this.generateCommand(
            Ev3Command.DIRECT_COMMAND_NO_REPLY,
            [
                Ev3Opcode.OPSOUND,
                Ev3Opcode.OPSOUND_CMD_STOP
            ]
        );

        this.send(cmd, false); // don't use rate limiter to ensure sound stops
    }

    stopAllMotors() {
        this._motors.forEach(motor => {
            if (motor) {
                motor.coast();
            }
        });
    }

    /**
     * Called by the runtime when user wants to scan for an EV3 peripheral.
     */
    scan() {
        if (this._bt) {
            this._bt.disconnect();
        }
        this._bt = new BT(this._runtime, this._extensionId, {
            majorDeviceClass: 8,
            minorDeviceClass: 1
        }, this._onConnect, this.reset, this._onMessage);
    }

    /**
     * Called by the runtime when user wants to connect to a certain EV3 peripheral.
     * @param {number} id - the id of the peripheral to connect to.
     */
    connect(id) {
        if (this._bt) {
            this._bt.connectPeripheral(id);
        }
    }

    /**
     * Called by the runtime when user wants to disconnect from the EV3 peripheral.
     */
    disconnect() {
        if (this._bt) {
            this._bt.disconnect();
        }

        this.reset();
    }

    /**
     * Reset all the state and timeout/interval ids.
     */
    reset() {
        this._sensorPorts = [];
        this._motorPorts = [];
        this._sensors = {
            distance: 0,
            brightness: 0,
            buttons: [0, 0, 0, 0],
            angle: {
                pitch: 0,
                roll: 0,
                yaw: 0
            },
            orientation: SpikeOrientation.front
        };
        this._motors = [null, null, null, null];
    }

    /**
     * Called by the runtime to detect whether the EV3 peripheral is connected.
     * @return {boolean} - the connected state.
     */
    isConnected() {
        let connected = false;
        if (this._bt) {
            connected = this._bt.isConnected();
        }
        return connected;
    }

    /**
     * Send a message to the peripheral BT socket.
     * @param {Uint8Array} message - the message to send.
     * @param {boolean} [useLimiter=true] - if true, use the rate limiter
     * @return {Promise} - a promise result of the send operation.
     */
    send(message, useLimiter = true) {
        console.trace('Called send() function');
    }

    sendJSON(json, useLimiter = true) {
        const jsonText = JSON.stringify(json);
        console.log('> ' + jsonText);

        if (!this.isConnected()) return Promise.resolve();

        if (useLimiter) {
            if (!this._rateLimiter.okayToSend()) return Promise.resolve();
        }

        const id = json.i;
        if (id != null) {
            const promise = new Promise((resolve, reject) => {
                this._openRequests[id] = { resolve, reject };
            });

            this._bt.sendMessage({
                message: jsonText + '\r'
            });

            return promise;
        } else {
            return this._bt.sendMessage({
                message: jsonText + '\r'
            })
        }
    }

    sendCommand(method, params, needsResponse = true) {
        if (needsResponse) {
            const id = Math.random().toString(36).slice(-4);

            return this.sendJSON({
                i: id,
                m: method,
                p: params
            });
        } else {
            return this.sendJSON({
                m: method,
                p: params
            });
        }
    }

    /**
     * Genrates direct commands that are sent to the EV3 as a single or compounded byte arrays.
     * See 'EV3 Communication Developer Kit', section 4, page 24 at
     * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits.
     *
     * Direct commands are one of two types:
     * DIRECT_COMMAND_NO_REPLY = a direct command where no reply is expected
     * DIRECT_COMMAND_REPLY = a direct command where a reply is expected, and the
     * number and length of returned values needs to be specified.
     *
     * The direct command byte array sent takes the following format:
     * Byte 0 - 1: Command size, Little Endian. Command size not including these 2 bytes
     * Byte 2 - 3: Message counter, Little Endian. Forth running counter
     * Byte 4:     Command type. Either DIRECT_COMMAND_REPLY or DIRECT_COMMAND_NO_REPLY
     * Byte 5 - 6: Reservation (allocation) of global and local variables using a compressed format
     *             (globals reserved in byte 5 and the 2 lsb of byte 6, locals reserved in the upper
     *             6 bits of byte 6) – see documentation for more details.
     * Byte 7 - n: Byte codes as a single command or compound commands (I.e. more commands composed
     *             as a small program)
     *
     * @param {number} type - the direct command type.
     * @param {string} byteCommands - a compound array of EV3 Opcode + arguments.
     * @param {number} allocation - the allocation of global and local vars needed for replies.
     * @return {array} - generated complete command byte array, with header and compounded commands.
     */
    generateCommand(type, byteCommands, allocation = 0) {

        // Header (Bytes 0 - 6)
        let command = [];
        command[2] = 0; // Message counter unused for now
        command[3] = 0; // Message counter unused for now
        command[4] = type;
        command[5] = allocation & 0xFF;
        command[6] = allocation >> 8 && 0xFF;

        // Bytecodes (Bytes 7 - n)
        command = command.concat(byteCommands);

        // Calculate command length minus first two header bytes
        const len = command.length - 2;
        command[0] = len & 0xFF;
        command[1] = len >> 8 && 0xFF;

        return command;
    }

    /**
     * When the EV3 peripheral connects
     * @private
     */
    _onConnect() {
        this.sendCommand('trigger_current_state', {}, false);
    }

    /**
     * Message handler for incoming EV3 reply messages, either a list of connected
     * devices (sensors and motors) or the values of the connected sensors and motors.
     *
     * See 'EV3 Communication Developer Kit', section 4.1, page 24 at
     * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits
     * for more details on direct reply formats.
     *
     * The direct reply byte array sent takes the following format:
     * Byte 0 – 1: Reply size, Little Endian. Reply size not including these 2 bytes
     * Byte 2 – 3: Message counter, Little Endian. Equals the Direct Command
     * Byte 4:     Reply type. Either DIRECT_REPLY or DIRECT_REPLY_ERROR
     * Byte 5 - n: Resonse buffer. I.e. the content of the by the Command reserved global variables.
     *             I.e. if the command reserved 64 bytes, these bytes will be placed in the reply
     *             packet as the bytes 5 to 68.
     *
     * See 'EV3 Firmware Developer Kit', section 4.8, page 56 at
     * https://education.lego.com/en-us/support/mindstorms-ev3/developer-kits
     * for direct response buffer formats for various commands.
     *
     * @param {object} params - incoming message parameters
     * @private
     */
    _onMessage(params) {
        const message = params.message;
        const data = Base64Util.base64ToUint8Array(message);
        const text = (new TextDecoder).decode(data);
        const responses = text.trim().split('\r');

        try {
            responses.forEach((jsonText) => {
                const json = JSON.parse(jsonText);
                if (json.m != 0 || json.i != null) {
                    console.log('< ' + jsonText);
                }
                this.parseResponse(json);
            });
        } catch (error) {
            console.log(text);
        }
    }

    parseResponse(response) {
        if (response.m != null) {
            switch (response.m) {
                case 0:
                    // Hub (Ports, Acceleration, Gyro Rate, Tilt Angle, LED Matrix, Timer)
                    const angle = response.p[8];
                    this._sensors.angle.yaw = angle[0];
                    this._sensors.angle.pitch = angle[1];
                    this._sensors.angle.roll = angle[2];
                    break;
                case 1:
                    // Strage
                    // {"m":1,"p":{"storage": {"available": 31056, "total": 31744, "pct": 3.16734, "unit": "kb", "free": 31056}, "slots": {"1": {"created": 1579238598349, "id": 5626, "size": 2778, "modified": 1579240679453, "name": "Report Test"}, "0": {"created": 1579137873835, "id": 22622, "size": 3010, "modified": 1579236837793, "name": "Key Code"}}}}
                    break;
                case 2:
                    // Battery
                    // {"m":2,"p":[8.316, 100]}
                    break;
                case 3:
                    // Button
                    // {"m":3,"p":["right", 0]}
                    break;
                case 4:
                    // Event (Orientation, Gesture)
                    if (SpikeOrientation[response.p]) {
                        this._sensors.orientation = SpikeOrientation[response.p];
                    }
                    break;
                default:
                    break;
            }
        }

        if (response.i != null) {
            const openRequest = this._openRequests[response.i];
            delete this._openRequests[response.i];

            if (openRequest) {
                openRequest.resolve();
            }
        }
    }
}

/**
 * Enum for port names.
 * Note: if changed, will break compatibility with previously saved projects.
 * @readonly
 * @enum {string}
 */
const SpikePorts = ['A', 'B', 'C', 'D', 'E', 'F'];

class Scratch3SpikeBlocks {

    /**
     * The ID of the extension.
     * @return {string} the id
     */
    static get EXTENSION_ID() {
        return 'spike';
    }

    /**
     * Creates a new instance of the EV3 extension.
     * @param  {object} runtime VM runtime
     * @constructor
     */
    constructor(runtime) {
        /**
         * The Scratch 3.0 runtime.
         * @type {Runtime}
         */
        this.runtime = runtime;

        // Create a new EV3 peripheral instance
        this._peripheral = new Spike(this.runtime, Scratch3SpikeBlocks.EXTENSION_ID);

        this._playNoteForPicker = this._playNoteForPicker.bind(this);
        this.runtime.on('PLAY_NOTE', this._playNoteForPicker);
    }

    /**
     * Define the EV3 extension.
     * @return {object} Extension description.
     */
    getInfo() {
        return {
            id: Scratch3SpikeBlocks.EXTENSION_ID,
            name: 'LEGO SPIKE Prime',
            blockIconURI: blockIconURI,
            showStatusButton: true,
            blocks: [
                {
                    opcode: 'displayImageFor',
                    text: formatMessage({
                        id: 'spike.displayImageFor',
                        default: 'turn on [MATRIX] for [DURATION] seconds',
                        description: 'display a pattern on the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MATRIX: {
                            type: ArgumentType.MATRIX,
                            defaultValue: '1101111011000001000101110'
                        },
                        DURATION: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 2
                        }
                    }
                },
                {
                    opcode: 'displayImage',
                    text: formatMessage({
                        id: 'spike.displayImage',
                        default: 'turn on [MATRIX]',
                        description: 'display a pattern on the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MATRIX: {
                            type: ArgumentType.MATRIX,
                            defaultValue: '1101111011000001000101110'
                        }
                    }
                },
                {
                    opcode: 'displayText',
                    text: formatMessage({
                        id: 'spike.displayText',
                        default: 'write [TEXT]',
                        description: 'display text on the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        TEXT: {
                            type: ArgumentType.STRING,
                            defaultValue: 'Hello'
                        }
                    }
                },
                {
                    opcode: 'displayClear',
                    text: formatMessage({
                        id: 'spike.displayClear',
                        default: 'turn off pixels',
                        description: 'display nothing on the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND
                },
                {
                    opcode: 'displaySetBrightness',
                    text: formatMessage({
                        id: 'spike.displaySetBrightness',
                        default: 'set pixel brightness to [BRIGHTNESS] %',
                        description: 'set the pixel brightness for the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        BRIGHTNESS: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 75
                        }
                    }
                },
                {
                    opcode: 'displaySetPixel',
                    text: formatMessage({
                        id: 'spike.displaySetPixel',
                        default: 'set pixel at [X] , [Y] to [BRIGHTNESS] %',
                        description: 'set a pixel brightness for the SPIKE Hub display'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        X: {
                            type: ArgumentType.STRING,
                            menu: 'coordinate',
                            defaultValue: '1'
                        },
                        Y: {
                            type: ArgumentType.STRING,
                            menu: 'coordinate',
                            defaultValue: '1'
                        },
                        BRIGHTNESS: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        }
                    }
                },
                '---',
                {
                    opcode: 'getOrientation',
                    text: formatMessage({
                        id: 'spike.getOrientation',
                        default: 'orientation',
                        description: 'the orientation returned by the tilt sensor'
                    }),
                    blockType: BlockType.REPORTER
                },
                {
                    opcode: 'getAngle',
                    text: formatMessage({
                        id: 'spike.getAngle',
                        default: '[AXIS] angle',
                        description: 'the angles returned by the tilt sensor'
                    }),
                    blockType: BlockType.REPORTER,
                    arguments: {
                        AXIS: {
                            type: ArgumentType.STRING,
                            menu: 'axis',
                            defaultValue: 'pitch'
                        }
                    }
                }
            ],
            menus: {
                port: {
                    acceptReporters: true,
                    items: SpikePorts
                },
                coordinate: {
                    acceptReporters: true,
                    items: ['1', '2', '3', '4', '5']
                },
                axis: {
                    acceptReporters: false,
                    items: ['pitch', 'roll', 'yaw']
                }
            }
        };
    }

    displayImageFor(args) {
        const brightness = Math.round(9 * this._peripheral.pixelBrightness / 100);
        const symbol = (Cast.toString(args.MATRIX).replace(/\D/g, '') + '0'.repeat(25)).slice(0, 25);
        const image = symbol.replace(/1/g, brightness).match(/.{5}/g).join(':');
        let duration = Cast.toNumber(args.DURATION) * 1000;
        duration = MathUtil.clamp(duration, 0, 60000);

        return this._peripheral.sendCommand('scratch.display_image_for', {
            image: image,
            duration: duration
        });
    }

    displayImage(args) {
        const brightness = Math.round(9 * this._peripheral.pixelBrightness / 100);
        const symbol = (Cast.toString(args.MATRIX).replace(/\D/g, '') + '0'.repeat(25)).slice(0, 25);
        const image = symbol.replace(/1/g, brightness).match(/.{5}/g).join(':');

        return this._peripheral.sendCommand('scratch.display_image', {
            image: image
        });
    }

    displayText(args) {
        const text = Cast.toString(args.TEXT);

        return this._peripheral.sendCommand('scratch.display_text', {
            text: text
        });
    }

    displayClear(args) {
        return this._peripheral.sendCommand('scratch.display_clear', {});
    }

    displaySetBrightness(args) {
        const brightness = MathUtil.clamp(Cast.toNumber(args.BRIGHTNESS), 0, 100);

        this._peripheral.pixelBrightness = brightness;
    }

    displaySetPixel(args) {
        const x = Cast.toNumber(args.X);
        if (x < 1 || x > 5) {
            return Promise.resolve();
        }
        const y = Cast.toNumber(args.Y);
        if (y < 1 || y > 5) {
            return Promise.resolve();
        }
        let brightness = MathUtil.clamp(Cast.toNumber(args.BRIGHTNESS), 0, 100);
        brightness = Math.round(9 * brightness / 100);

        return this._peripheral.sendCommand('scratch.display_set_pixel', {
            x: x - 1,
            y: y - 1,
            brightness: brightness
        });
    }

    getOrientation() {
        return this._peripheral.orientation;
    }

    getAngle(args) {
        const axis = Cast.toString(args.AXIS);

        return this._peripheral.angle[axis];
    }

    motorTurnClockwise(args) {
        const port = Cast.toNumber(args.PORT);
        let time = Cast.toNumber(args.TIME) * 1000;
        time = MathUtil.clamp(time, 0, 15000);

        return new Promise(resolve => {
            this._forEachMotor(port, motorIndex => {
                const motor = this._peripheral.motor(motorIndex);
                if (motor) {
                    motor.direction = 1;
                    motor.turnOnFor(time);
                }
            });

            // Run for some time even when no motor is connected
            setTimeout(resolve, time);
        });
    }

    motorTurnCounterClockwise(args) {
        const port = Cast.toNumber(args.PORT);
        let time = Cast.toNumber(args.TIME) * 1000;
        time = MathUtil.clamp(time, 0, 15000);

        return new Promise(resolve => {
            this._forEachMotor(port, motorIndex => {
                const motor = this._peripheral.motor(motorIndex);
                if (motor) {
                    motor.direction = -1;
                    motor.turnOnFor(time);
                }
            });

            // Run for some time even when no motor is connected
            setTimeout(resolve, time);
        });
    }

    motorSetPower(args) {
        const port = Cast.toNumber(args.PORT);
        const power = MathUtil.clamp(Cast.toNumber(args.POWER), 0, 100);

        this._forEachMotor(port, motorIndex => {
            const motor = this._peripheral.motor(motorIndex);
            if (motor) {
                motor.power = power;
            }
        });
    }

    getMotorPosition(args) {
        const port = Cast.toNumber(args.PORT);

        if (![0, 1, 2, 3].includes(port)) {
            return;
        }

        const motor = this._peripheral.motor(port);
        let position = 0;
        if (motor) {
            position = MathUtil.wrapClamp(motor.position, 0, 360);
        }

        return position;
    }

    whenButtonPressed(args) {
        const port = Cast.toNumber(args.PORT);

        if (![0, 1, 2, 3].includes(port)) {
            return;
        }

        return this._peripheral.isButtonPressed(port);
    }

    whenDistanceLessThan(args) {
        const distance = MathUtil.clamp(Cast.toNumber(args.DISTANCE), 0, 100);

        return this._peripheral.distance < distance;
    }

    whenBrightnessLessThan(args) {
        const brightness = MathUtil.clamp(Cast.toNumber(args.DISTANCE), 0, 100);

        return this._peripheral.brightness < brightness;
    }

    buttonPressed(args) {
        const port = Cast.toNumber(args.PORT);

        if (![0, 1, 2, 3].includes(port)) {
            return;
        }

        return this._peripheral.isButtonPressed(port);
    }

    getDistance() {
        return this._peripheral.distance;
    }

    getBrightness() {
        return this._peripheral.brightness;
    }

    _playNoteForPicker(note, category) {
        if (category !== this.getInfo().name) return;
        this.beep({
            NOTE: note,
            TIME: 0.25
        });
    }

    beep(args) {
        const note = MathUtil.clamp(Cast.toNumber(args.NOTE), 47, 99); // valid EV3 sounds
        let time = Cast.toNumber(args.TIME) * 1000;
        time = MathUtil.clamp(time, 0, 3000);

        if (time === 0) {
            return; // don't send a beep time of 0
        }

        return new Promise(resolve => {
            // https://en.wikipedia.org/wiki/MIDI_tuning_standard#Frequency_values
            const freq = Math.pow(2, ((note - 69 + 12) / 12)) * 440;
            this._peripheral.beep(freq, time);

            // Run for some time even when no piezo is connected.
            setTimeout(resolve, time);
        });
    }

    /**
     * Call a callback for each motor indexed by the provided motor ID.
     *
     * Note: This way of looping through motors is currently unnecessary, but could be
     * useful if an 'all motors' option is added in the future (see WeDo2 extension).
     *
     * @param {MotorID} motorID - the ID specifier.
     * @param {Function} callback - the function to call with the numeric motor index for each motor.
     * @private
     */
    _forEachMotor(motorID, callback) {
        let motors;
        switch (motorID) {
            case 0:
                motors = [0];
                break;
            case 1:
                motors = [1];
                break;
            case 2:
                motors = [2];
                break;
            case 3:
                motors = [3];
                break;
            default:
                log.warn(`Invalid motor ID: ${motorID}`);
                motors = [];
                break;
        }
        for (const index of motors) {
            callback(index);
        }
    }

    /**
     * Formats menus into a format suitable for block menus, and loading previously
     * saved projects:
     * [
     *   {
     *    text: label,
     *    value: index
     *   },
     *   {
     *    text: label,
     *    value: index
     *   },
     *   etc...
     * ]
     *
     * @param {array} menu - a menu to format.
     * @return {object} - a formatted menu as an object.
     * @private
     */
    _formatMenu(menu) {
        const m = [];
        for (let i = 0; i < menu.length; i++) {
            const obj = {};
            obj.text = menu[i];
            obj.value = i.toString();
            m.push(obj);
        }
        return m;
    }
}

module.exports = Scratch3SpikeBlocks;
