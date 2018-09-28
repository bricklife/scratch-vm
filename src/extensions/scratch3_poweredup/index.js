const ArgumentType = require('../../extension-support/argument-type');
const BlockType = require('../../extension-support/block-type');
const Cast = require('../../util/cast');
const formatMessage = require('format-message');
const color = require('../../util/color');
const log = require('../../util/log');
const BLESession = require('../../io/bleSession');
const Base64Util = require('../../util/base64-util');
const MathUtil = require('../../util/math-util');
const RateLimiter = require('../../util/rateLimiter.js');

/**
 * Icon svg to be displayed at the left edge of each extension block, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const iconURI = 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAYAAACOEfKtAAAABGdBTUEAALGPC/xhBQAAACBjSFJNAAB6JgAAgIQAAPoAAACA6AAAdTAAAOpgAAA6mAAAF3CculE8AAAACXBIWXMAABYlAAAWJQFJUiTwAAABWWlUWHRYTUw6Y29tLmFkb2JlLnhtcAAAAAAAPHg6eG1wbWV0YSB4bWxuczp4PSJhZG9iZTpuczptZXRhLyIgeDp4bXB0az0iWE1QIENvcmUgNS40LjAiPgogICA8cmRmOlJERiB4bWxuczpyZGY9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkvMDIvMjItcmRmLXN5bnRheC1ucyMiPgogICAgICA8cmRmOkRlc2NyaXB0aW9uIHJkZjphYm91dD0iIgogICAgICAgICAgICB4bWxuczp0aWZmPSJodHRwOi8vbnMuYWRvYmUuY29tL3RpZmYvMS4wLyI+CiAgICAgICAgIDx0aWZmOk9yaWVudGF0aW9uPjE8L3RpZmY6T3JpZW50YXRpb24+CiAgICAgIDwvcmRmOkRlc2NyaXB0aW9uPgogICA8L3JkZjpSREY+CjwveDp4bXBtZXRhPgpMwidZAAAB0UlEQVR4Ae3Yv03DQBiHYRuFjoYFWIEW0cIMFFAhShYIEkiRQCILUCIqKNiBFtGyAgswAEgmjrjIRez3ztYVsd40vvh3//zki05yUfhRQAEFFFBAAQUUUEABBRRQQAEFFFBAAQUUUEABBRRQQIG8AmXK9LP5695v9fNYFuVBVVQfk3L7YjY9+Rrr/RibrZhOoU+Nt2gfL/B26uv/92Ks98Nzd12xAq/vn6uuCcae3V2ddRolVeDYsfo83yR20O30NLZrUr+b+cuyf675kzbT6Bz21bi1thkNWI+OmTRApPRdu7MNuelfeOAPlVSBYa3D/d3QXF3fP79X7WYjpW9z3Ka0O0+Y+iE8hT2FsxZz9F/48vwoy0Yent6W8+aav++mw75ovIcICUEuIABRLCAJQS4gAFEsIAlBLiAAUSwgCUEuIABRLCAJQS4gAFEsIAlBLiAAUSwgCUEuIABRLCAJQR79PjD2/Ris1xrnnr914YGBFTgQMLoCc70xDpWXa/6+PmFfNN4KJCHIBQQgigUkIcgFBCCKBSQhyKNP4dhTCdZrjXPP37rwwMAKHAjocAUUUEABBRRQQAEFFFBAAQUUUEABBRRQQAEFFFBAAQUUyC3wB8F0/UisWMI9AAAAAElFTkSuQmCC';

const UUID = {
    DEVICE_SERVICE: '00001623-1212-efde-1623-785feabcd123',
    IO_SERVICE: '00001623-1212-efde-1623-785feabcd123',
    ATTACHED_IO: '00001624-1212-efde-1623-785feabcd123',
    INPUT_VALUES: '00001624-1212-efde-1623-785feabcd123',
    INPUT_COMMAND: '00001624-1212-efde-1623-785feabcd123',
    OUTPUT_COMMAND: '00001624-1212-efde-1623-785feabcd123'
};

/**
 * A time interval to wait (in milliseconds) while a block that sends a BLE message is running.
 * @type {number}
 */
const BLESendInterval = 100;

/**
 * A maximum number of BLE message sends per second, to be enforced by the rate limiter.
 * @type {number}
 */
const BLESendRateMax = 20;

/**
 * Enum for WeDo 2.0 sensor and output types.
 * @readonly
 * @enum {number}
 */
const PoweredUpTypes = {
    MOTOR: 1,
    TRAIN_MOTOR: 2,
    LED_LIGHT: 8,
    PIEZO: 22,
    LED: 23,
    TILT: 34,
    DISTANCE: 35
};

/**
 * Enum for connection/port ids assigned to internal PoweredUp output devices.
 * @readonly
 * @enum {number}
 */
const PoweredUpConnectIDs = {
    LED: 6,
    PIEZO: 5
};

/**
 * Enum for ids for various output commands on the PoweredUp.
 * @readonly
 * @enum {number}
 */
const PoweredUpCommands = {
    MOTOR_POWER: 1,
    PLAY_TONE: 2,
    STOP_TONE: 3,
    WRITE_RGB: 4,
    SET_VOLUME: 255
};

/**
 * Enum for modes for input sensors on the PoweredUp.
 * @enum {number}
 */
const PoweredUpModes = {
    TILT: 0, // angle
    DISTANCE: 0 // detect
};

/**
 * Enum for units for input sensors on the PoweredUp.
 * @enum {number}
 */
const PoweredUpUnits = {
    TILT: 0, // raw
    DISTANCE: 1 // percent
};

/**
 * Manage power, direction, and timers for one WeDo 2.0 motor.
 */
class PoweredUpMotor {
    /**
     * Construct a PoweredUpMotor instance.
     * @param {PoweredUp} parent - the WeDo 2.0 device which owns this motor.
     * @param {int} index - the zero-based index of this motor on its parent device.
     */
    constructor (parent, index) {
        /**
         * The WeDo 2.0 device which owns this motor.
         * @type {PoweredUp}
         * @private
         */
        this._parent = parent;

        /**
         * The zero-based index of this motor on its parent device.
         * @type {int}
         * @private
         */
        this._index = index;

        /**
         * This motor's current direction: 1 for "this way" or -1 for "that way"
         * @type {number}
         * @private
         */
        this._direction = 1;

        /**
         * This motor's current power level, in the range [0,100].
         * @type {number}
         * @private
         */
        this._power = 100;

        /**
         * Is this motor currently moving?
         * @type {boolean}
         * @private
         */
        this._isOn = false;

        /**
         * If the motor has been turned on or is actively braking for a specific duration, this is the timeout ID for
         * the end-of-action handler. Cancel this when changing plans.
         * @type {Object}
         * @private
         */
        this._pendingTimeoutId = null;

        /**
         * The starting time for the pending timeout.
         * @type {Object}
         * @private
         */
        this._pendingTimeoutStartTime = null;

        /**
         * The delay/duration of the pending timeout.
         * @type {Object}
         * @private
         */
        this._pendingTimeoutDelay = null;

        this.startBraking = this.startBraking.bind(this);
        this.setMotorOff = this.setMotorOff.bind(this);
    }

    /**
     * @return {number} - the duration of active braking after a call to startBraking(). Afterward, turn the motor off.
     * @constructor
     */
    static get BRAKE_TIME_MS () {
        return 1000;
    }

    /**
     * @return {int} - this motor's current direction: 1 for "this way" or -1 for "that way"
     */
    get direction () {
        return this._direction;
    }

    /**
     * @param {int} value - this motor's new direction: 1 for "this way" or -1 for "that way"
     */
    set direction (value) {
        if (value < 0) {
            this._direction = -1;
        } else {
            this._direction = 1;
        }
    }

    /**
     * @return {int} - this motor's current power level, in the range [-100,100].
     */
    get power () {
        return this._power;
    }

    /**
     * @param {int} value - this motor's new power level, in the range [-100,100].
     */
    set power (value) {
        this._power = Math.max(-100, Math.min(value, 100));
    }

    /**
     * @return {boolean} - true if this motor is currently moving, false if this motor is off or braking.
     */
    get isOn () {
        return this._isOn;
    }

    /**
     * @return {boolean} - time, in milliseconds, of when the pending timeout began.
     */
    get pendingTimeoutStartTime () {
        return this._pendingTimeoutStartTime;
    }

    /**
     * @return {boolean} - delay, in milliseconds, of the pending timeout.
     */
    get pendingTimeoutDelay () {
        return this._pendingTimeoutDelay;
    }

    /**
     * Turn this motor on indefinitely.
     */
    setMotorOn () {
        const cmd = new Uint8Array(8);
        cmd[0] = 0x08;
        cmd[1] = 0x00;
        cmd[2] = 0x81;
        cmd[3] = this._index; // connect id
        cmd[4] = 0x11;
        cmd[5] = 0x51;
        cmd[6] = 0x00;
        cmd[7] = this._power; // power in range -100 - 100

        this._parent._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));

        this._isOn = true;
        this._clearTimeout();
    }

    /**
     * Turn this motor on for a specific duration.
     * @param {number} milliseconds - run the motor for this long.
     */
    setMotorOnFor (milliseconds) {
        milliseconds = Math.max(0, milliseconds);
        this.setMotorOn();
        this._setNewTimeout(this.startBraking, milliseconds);
    }

    /**
     * Start active braking on this motor. After a short time, the motor will turn off.
     */
    startBraking () {
        const cmd = new Uint8Array(8);
        cmd[0] = 0x08;
        cmd[1] = 0x00;
        cmd[2] = 0x81;
        cmd[3] = this._index; // connect id
        cmd[4] = 0x11;
        cmd[5] = 0x51;
        cmd[6] = 0x00;
        cmd[7] = 0x7f; // power

        this._parent._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));

        this._isOn = false;
        this._setNewTimeout(this.setMotorOff, PoweredUpMotor.BRAKE_TIME_MS);
    }

    /**
     * Turn this motor off.
     * @param {boolean} [useLimiter=true] - if true, use the rate limiter
     */
    setMotorOff (useLimiter = true) {
        const cmd = new Uint8Array(8);
        cmd[0] = 0x08;
        cmd[1] = 0x00;
        cmd[2] = 0x81;
        cmd[3] = this._index; // connect id
        cmd[4] = 0x11;
        cmd[5] = 0x51;
        cmd[6] = 0x00;
        cmd[7] = 0x00; // power

        this._parent._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd), useLimiter);

        this._isOn = false;
    }

    /**
     * Clear the motor action timeout, if any. Safe to call even when there is no pending timeout.
     * @private
     */
    _clearTimeout () {
        if (this._pendingTimeoutId !== null) {
            clearTimeout(this._pendingTimeoutId);
            this._pendingTimeoutId = null;
            this._pendingTimeoutStartTime = null;
            this._pendingTimeoutDelay = null;
        }
    }

    /**
     * Set a new motor action timeout, after clearing an existing one if necessary.
     * @param {Function} callback - to be called at the end of the timeout.
     * @param {int} delay - wait this many milliseconds before calling the callback.
     * @private
     */
    _setNewTimeout (callback, delay) {
        this._clearTimeout();
        const timeoutID = setTimeout(() => {
            if (this._pendingTimeoutId === timeoutID) {
                this._pendingTimeoutId = null;
            }
            callback();
        }, delay);
        this._pendingTimeoutId = timeoutID;
        this._pendingTimeoutStartTime = Date.now();
        this._pendingTimeoutDelay = delay;
    }
}

/**
 * Manage communication with a WeDo 2.0 device over a Bluetooth Low Energy client socket.
 */
class PoweredUp {

    constructor (runtime, extensionId) {

        /**
         * The Scratch 3.0 runtime used to trigger the green flag button.
         * @type {Runtime}
         * @private
         */
        this._runtime = runtime;
        this._runtime.on('PROJECT_STOP_ALL', this._stopAll.bind(this));

        /**
         * The device ports that connect to motors and sensors.
         * @type {string[]}
         * @private
         */
        this._ports = {}; // TODO: rename?

        /**
         * The motors which this WeDo 2.0 could possibly have.
         * @type {PoweredUpMotor[]}
         * @private
         */
        this._motors = [null, null];

        /**
         * The most recently received value for each sensor.
         * @type {Object.<string, number>}
         * @private
         */
        this._sensors = {
            tiltX: 0,
            tiltY: 0,
            distance: 0
        };

        /**
         * The Bluetooth connection session for reading/writing device data.
         * @type {BLESession}
         * @private
         */
        this._ble = null;
        this._runtime.registerExtensionDevice(extensionId, this);

        this._onConnect = this._onConnect.bind(this);
        this._onMessage = this._onMessage.bind(this);

        /**
         * A rate limiter utility, to help limit the rate at which we send BLE messages
         * over the socket to Scratch Link to a maximum number of sends per second.
         * @type {RateLimiter}
         * @private
         */
        this._rateLimiter = new RateLimiter(BLESendRateMax);
    }

    /**
     * @return {number} - the latest value received for the tilt sensor's tilt about the X axis.
     */
    get tiltX () {
        return this._sensors.tiltX;
    }

    /**
     * @return {number} - the latest value received for the tilt sensor's tilt about the Y axis.
     */
    get tiltY () {
        return this._sensors.tiltY;
    }

    /**
     * @return {number} - the latest value received from the distance sensor.
     */
    get distance () {
        return this._sensors.distance;
    }

    /**
     * Access a particular motor on this device.
     * @param {int} index - the zero-based index of the desired motor.
     * @return {PoweredUpMotor} - the PoweredUpMotor instance, if any, at that index.
     */
    motor (index) {
        return this._motors[index];
    }

    /**
     * Stop all the motors that are currently running.
     */
    stopAllMotors () {
        this._motors.forEach(motor => {
            if (motor) {
                // Send the motor off command without using the rate limiter.
                // This allows the stop button to stop motors even if we are
                // otherwise flooded with commands.
                motor.setMotorOff(false);
            }
        });
    }

    /**
     * Set the WeDo 2.0 hub's LED to a specific color.
     * @param {int} rgb - a 24-bit RGB color in 0xRRGGBB format.
     * @return {Promise} - a promise of the completion of the set led send operation.
     */
    setLED (rgb) {
        const cmd = new Uint8Array(6);
        cmd[0] = PoweredUpConnectIDs.LED; // connect id
        cmd[1] = PoweredUpCommands.WRITE_RGB; // command
        cmd[2] = 3; // 3 bytes to follow
        cmd[3] = (rgb >> 16) & 0x000000FF;
        cmd[4] = (rgb >> 8) & 0x000000FF;
        cmd[5] = (rgb) & 0x000000FF;

        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    /**
     * Switch off the LED on the PoweredUp.
     * @return {Promise} - a promise of the completion of the stop led send operation.
     */
    stopLED () {
        const cmd = new Uint8Array(6);
        cmd[0] = PoweredUpConnectIDs.LED; // connect id
        cmd[1] = PoweredUpCommands.WRITE_RGB; // command
        cmd[2] = 3; // 3 bytes to follow
        cmd[3] = 0x000000; // off
        cmd[4] = 0x000000;
        cmd[5] = 0x000000;

        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    /**
     * Play a tone from the WeDo 2.0 hub for a specific amount of time.
     * @param {int} tone - the pitch of the tone, in Hz.
     * @param {int} milliseconds - the duration of the note, in milliseconds.
     * @return {Promise} - a promise of the completion of the play tone send operation.
     */
    playTone (tone, milliseconds) {
        const cmd = new Uint8Array(7);
        cmd[0] = PoweredUpConnectIDs.PIEZO; // connect id
        cmd[1] = PoweredUpCommands.PLAY_TONE; // command
        cmd[2] = 4; // 4 bytes to follow
        cmd[3] = tone;
        cmd[4] = tone >> 8;
        cmd[5] = milliseconds;
        cmd[6] = milliseconds >> 8;

        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    /**
     * Stop the tone playing from the WeDo 2.0 hub, if any.
     * @return {Promise} - a promise that the command sent.
     */
    stopTone () {
        const cmd = new Uint8Array(2);
        cmd[0] = PoweredUpConnectIDs.PIEZO; // connect id
        cmd[1] = PoweredUpCommands.STOP_TONE; // command

        // Send this command without using the rate limiter, because it is only triggered
        // by the stop button.
        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd), false);
    }

    /**
     * Called by the runtime when user wants to scan for a device.
     */
    // TODO: rename scan?
    startDeviceScan () {
        this._ble = new BLESession(this._runtime, {
            filters: [{services: [UUID.DEVICE_SERVICE]}]
        }, this._onConnect);
    }

    /**
     * Called by the runtime when user wants to connect to a certain device.
     * @param {number} id - the id of the device to connect to.
     */
    // TODO: rename connect?
    connectDevice (id) {
        this._ble.connectDevice(id);
    }

    /**
     * Disconnects from the current BLE session.
     */
    // TODO: rename disconnect?
    disconnectSession () {
        this._ports = {};
        this._motors = [null, null];
        this._sensors = {
            tiltX: 0,
            tiltY: 0,
            distance: 0
        };

        this._ble.disconnectSession();
    }

    /**
     * Called by the runtime to detect whether the device is connected.
     * @return {boolean} - the connected state.
     */
    // TODO: rename isConnected
    getPeripheralIsConnected () {
        let connected = false;
        if (this._ble) {
            connected = this._ble.getPeripheralIsConnected();
        }
        return connected;
    }

    /**
     * Sets LED mode and initial color and starts reading data from device after BLE has connected.
     * @private
     */
    _onConnect () {
        this._ble.startNotifications(UUID.DEVICE_SERVICE, UUID.ATTACHED_IO, this._onMessage);
    }

    /**
     * Write a message to the device BLE session.
     * @param {number} uuid - the UUID of the characteristic to write to
     * @param {Uint8Array} message - the message to write.
     * @param {boolean} [useLimiter=true] - if true, use the rate limiter
     * @return {Promise} - a promise result of the write operation
     * @private
     */
    _send (uuid, message, useLimiter = true) {
        if (!this.getPeripheralIsConnected()) return Promise.resolve();

        if (useLimiter) {
            if (!this._rateLimiter.okayToSend()) return Promise.resolve();
        }

        return this._ble.write(UUID.IO_SERVICE, uuid, message, 'base64');
    }

    /**
     * Process the sensor data from the incoming BLE characteristic.
     * @param {object} base64 - the incoming BLE data.
     * @private
     */
    _onMessage (base64) {
        const data = Base64Util.base64ToUint8Array(base64);
        // log.info(data);

        switch (data[2]) {
        case 0x04: {
            const connectID = data[3];
            if (data[4] === 0) {
                // clear sensor or motor
                this._clearPort(connectID);
            } else {
                // register sensor or motor
                this._registerSensorOrMotor(connectID, data[5]);
            }
            break;
        }
        case 0x45: {
            // read incoming sensor value
            const connectID = data[1];
            const type = this._ports[connectID];
            if (type === PoweredUpTypes.DISTANCE) {
                this._sensors.distance = data[2];
            }
            if (type === PoweredUpTypes.TILT) {
                this._sensors.tiltX = data[2];
                this._sensors.tiltY = data[3];
            }
            break;
        }
        default: {
            break;
        }
        }
    }

    /**
     * Clear the sensor or motor present at port 1 or 2.
     * @param {number} connectID - the port to clear.
     * @private
     */
    _clearPort (connectID) {
        const type = this._ports[connectID];
        if (type === PoweredUpTypes.TILT) {
            this._sensors.tiltX = this._sensors.tiltY = 0;
        }
        if (type === PoweredUpTypes.DISTANCE) {
            this._sensors.distance = 0;
        }
        delete this._ports[connectID];
        this._motors[connectID] = null;
    }

    /**
     * Register a new sensor or motor connected at a port.  Store the type of
     * sensor or motor internally, and then register for notifications on input
     * values if it is a sensor.
     * @param {number} connectID - the port to register a sensor or motor on.
     * @param {number} type - the type ID of the sensor or motor
     */
    _registerSensorOrMotor (connectID, type) {
        // Record which port is connected to what type of device
        this._ports[connectID] = type;

        // Register motor
        if (type === PoweredUpTypes.MOTOR || type === PoweredUpTypes.TRAIN_MOTOR || type === PoweredUpTypes.LED_LIGHT) {
            this._motors[connectID] = new PoweredUpMotor(this, connectID);
        } else {
            return;
            // Register tilt or distance sensor
            const typeString = type === PoweredUpTypes.DISTANCE ? 'DISTANCE' : 'TILT';
            const cmd = new Uint8Array(11);
            cmd[0] = 1; // sensor format
            cmd[1] = 2; // command type: write
            cmd[2] = connectID; // connect id
            cmd[3] = type; // type
            cmd[4] = PoweredUpModes[typeString]; // mode
            cmd[5] = 1; // delta interval, 4 bytes, 1 = continuous updates
            cmd[6] = 0;
            cmd[7] = 0;
            cmd[8] = 0;
            cmd[9] = PoweredUpUnits[typeString]; // unit
            cmd[10] = 1; // notifications enabled: true

            this._send(UUID.INPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd))
                .then(() => {
                    this._ble.startNotifications(UUID.IO_SERVICE, UUID.INPUT_VALUES, this._onMessage);
                });
        }
    }

    /**
     * Sets the input mode of the LED to RGB.
     * @return {Promise} - a promise returned by the send operation.
     * @private
     */
    _setLEDMode () {
        const cmd = new Uint8Array(11);
        cmd[0] = 1; // sensor format
        cmd[1] = 2; // command type: 2 = write
        cmd[2] = PoweredUpConnectIDs.LED; // port
        cmd[3] = PoweredUpTypes.LED; // type
        cmd[4] = 1; // mode
        cmd[5] = 0; // delta interval, 4 bytes
        cmd[6] = 0;
        cmd[7] = 0;
        cmd[8] = 0;
        cmd[9] = 0; // unit = raw
        cmd[10] = 0; // notifications enabled: false

        return this._send(UUID.INPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    /**
     * Stop the tone playing and motors on the WeDo 2.0 hub.
     */
    _stopAll () {
        if (!this.getPeripheralIsConnected()) return;
        this.stopTone()
            .then(() => {
                this.stopAllMotors();
            });
    }
}

/**
 * Enum for motor specification.
 * @readonly
 * @enum {string}
 */
const MotorID = {
    A: 'port A',
    B: 'port B',
    ALL: 'all ports'
};

/**
 * Enum for motor direction specification.
 * @readonly
 * @enum {string}
 */
const MotorDirection = {
    FORWARD: 'this way',
    BACKWARD: 'that way',
    REVERSE: 'reverse'
};

/**
 * Enum for tilt sensor direction.
 * @readonly
 * @enum {string}
 */
const TiltDirection = {
    UP: 'up',
    DOWN: 'down',
    LEFT: 'left',
    RIGHT: 'right',
    ANY: 'any'
};

/**
 * Scratch 3.0 blocks to interact with a LEGO WeDo 2.0 device.
 */
class Scratch3PoweredUpBlocks {

    /**
     * @return {string} - the ID of this extension.
     */
    static get EXTENSION_ID () {
        return 'poweredup';
    }

    /**
     * @return {number} - the tilt sensor counts as "tilted" if its tilt angle meets or exceeds this threshold.
     */
    static get TILT_THRESHOLD () {
        return 15;
    }

    /**
     * Construct a set of WeDo 2.0 blocks.
     * @param {Runtime} runtime - the Scratch 3.0 runtime.
     */
    constructor (runtime) {
        /**
         * The Scratch 3.0 runtime.
         * @type {Runtime}
         */
        this.runtime = runtime;

        // Create a new PoweredUp device instance
        this._device = new PoweredUp(this.runtime, Scratch3PoweredUpBlocks.EXTENSION_ID);
    }

    /**
     * @returns {object} metadata for this extension and its blocks.
     */
    getInfo () {
        return {
            id: Scratch3PoweredUpBlocks.EXTENSION_ID,
            name: 'Powered Up',
            blockIconURI: iconURI,
            showStatusButton: true,
            blocks: [
                {
                    opcode: 'startMotorPowerFor',
                    text: formatMessage({
                        id: 'wedo2.startMotorPowerFor',
                        default: 'set [MOTOR_ID] power to [POWER] for [DURATION] sec',
                        description: 'set the motor\'s power and turn it on for some time'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MOTOR_ID: {
                            type: ArgumentType.STRING,
                            menu: 'MOTOR_ID',
                            defaultValue: MotorID.A
                        },
                        POWER: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        },
                        DURATION: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 1
                        }
                    }
                },
                {
                    opcode: 'startMotorPower',
                    text: formatMessage({
                        id: 'poweredup.startMotorPower',
                        default: 'set [MOTOR_ID] power to [POWER]',
                        description: 'set the motor\'s power and turn it on'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MOTOR_ID: {
                            type: ArgumentType.STRING,
                            menu: 'MOTOR_ID',
                            defaultValue: MotorID.A
                        },
                        POWER: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        }
                    }
                },
                {
                    opcode: 'motorOff',
                    text: formatMessage({
                        id: 'poweredup.motorOff',
                        default: 'turn [MOTOR_ID] off',
                        description: 'turn a motor off'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        MOTOR_ID: {
                            type: ArgumentType.STRING,
                            menu: 'MOTOR_ID',
                            defaultValue: MotorID.A
                        }
                    }
                }
            ],
            menus: {
                MOTOR_ID: [MotorID.A, MotorID.B, MotorID.ALL],
                MOTOR_DIRECTION: [MotorDirection.FORWARD, MotorDirection.BACKWARD, MotorDirection.REVERSE],
                TILT_DIRECTION: [TiltDirection.UP, TiltDirection.DOWN, TiltDirection.LEFT, TiltDirection.RIGHT],
                TILT_DIRECTION_ANY:
                    [TiltDirection.UP, TiltDirection.DOWN, TiltDirection.LEFT, TiltDirection.RIGHT, TiltDirection.ANY],
                OP: ['<', '>']
            }
        };
    }

    /**
     * Turn specified motor(s) on for a specified duration.
     * @param {object} args - the block's arguments.
     * @property {MotorID} MOTOR_ID - the motor(s) to activate.
     * @property {int} DURATION - the amount of time to run the motors.
     * @return {Promise} - a promise which will resolve at the end of the duration.
     */
    motorOnFor (args) {
        let durationMS = Cast.toNumber(args.DURATION) * 1000;
        durationMS = MathUtil.clamp(durationMS, 0, 15000);
        return new Promise(resolve => {
            this._forEachMotor(args.MOTOR_ID, motorIndex => {
                const motor = this._device.motor(motorIndex);
                if (motor) {
                    motor.setMotorOnFor(durationMS);
                }
            });

            // Ensure this block runs for a fixed amount of time even when no device is connected.
            setTimeout(resolve, durationMS);
        });
    }

    startMotorPowerFor (args) {
        let durationMS = Cast.toNumber(args.DURATION) * 1000;
        durationMS = MathUtil.clamp(durationMS, 0, 15000);
        return new Promise(resolve => {
            this._forEachMotor(args.MOTOR_ID, motorIndex => {
                const motor = this._device.motor(motorIndex);
                if (motor) {
                    motor.power = MathUtil.clamp(Cast.toNumber(args.POWER), -100, 100);
                    motor.setMotorOnFor(durationMS);
                }
            });

            // Ensure this block runs for a fixed amount of time even when no device is connected.
            setTimeout(resolve, durationMS);
        });
    }

    /**
     * Turn specified motor(s) on indefinitely.
     * @param {object} args - the block's arguments.
     * @property {MotorID} MOTOR_ID - the motor(s) to activate.
     * @return {Promise} - a Promise that resolves after some delay.
     */
    motorOn (args) {
        this._forEachMotor(args.MOTOR_ID, motorIndex => {
            const motor = this._device.motor(motorIndex);
            if (motor) {
                motor.setMotorOn();
            }
        });

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Turn specified motor(s) off.
     * @param {object} args - the block's arguments.
     * @property {MotorID} MOTOR_ID - the motor(s) to deactivate.
     * @return {Promise} - a Promise that resolves after some delay.
     */
    motorOff (args) {
        this._forEachMotor(args.MOTOR_ID, motorIndex => {
            const motor = this._device.motor(motorIndex);
            if (motor) {
                motor.setMotorOff();
            }
        });

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Turn specified motor(s) off.
     * @param {object} args - the block's arguments.
     * @property {MotorID} MOTOR_ID - the motor(s) to be affected.
     * @property {int} POWER - the new power level for the motor(s).
     * @return {Promise} - a Promise that resolves after some delay.
     */
    startMotorPower (args) {
        this._forEachMotor(args.MOTOR_ID, motorIndex => {
            const motor = this._device.motor(motorIndex);
            if (motor) {
                motor.power = MathUtil.clamp(Cast.toNumber(args.POWER), -100, 100);
                motor.setMotorOn();
            }
        });

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Set the direction of rotation for specified motor(s).
     * If the direction is 'reverse' the motor(s) will be reversed individually.
     * @param {object} args - the block's arguments.
     * @property {MotorID} MOTOR_ID - the motor(s) to be affected.
     * @property {MotorDirection} MOTOR_DIRECTION - the new direction for the motor(s).
     * @return {Promise} - a Promise that resolves after some delay.
     */
    setMotorDirection (args) {
        this._forEachMotor(args.MOTOR_ID, motorIndex => {
            const motor = this._device.motor(motorIndex);
            if (motor) {
                switch (args.MOTOR_DIRECTION) {
                case MotorDirection.FORWARD:
                    motor.direction = 1;
                    break;
                case MotorDirection.BACKWARD:
                    motor.direction = -1;
                    break;
                case MotorDirection.REVERSE:
                    motor.direction = -motor.direction;
                    break;
                default:
                    log.warn(`Unknown motor direction in setMotorDirection: ${args.DIRECTION}`);
                    break;
                }
                // keep the motor on if it's running, and update the pending timeout if needed
                if (motor.isOn) {
                    if (motor.pendingTimeoutDelay) {
                        motor.setMotorOnFor(motor.pendingTimeoutStartTime + motor.pendingTimeoutDelay - Date.now());
                    } else {
                        motor.setMotorOn();
                    }
                }
            }
        });

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Set the LED's hue.
     * @param {object} args - the block's arguments.
     * @property {number} HUE - the hue to set, in the range [0,100].
     * @return {Promise} - a Promise that resolves after some delay.
     */
    setLightHue (args) {
        // Convert from [0,100] to [0,360]
        let inputHue = Cast.toNumber(args.HUE);
        inputHue = MathUtil.wrapClamp(inputHue, 0, 100);
        const hue = inputHue * 360 / 100;

        const rgbObject = color.hsvToRgb({h: hue, s: 1, v: 1});

        const rgbDecimal = color.rgbToDecimal(rgbObject);

        this._device.setLED(rgbDecimal);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    /**
     * Make the WeDo 2.0 hub play a MIDI note for the specified duration.
     * @param {object} args - the block's arguments.
     * @property {number} NOTE - the MIDI note to play.
     * @property {number} DURATION - the duration of the note, in seconds.
     * @return {Promise} - a promise which will resolve at the end of the duration.
     */
    playNoteFor (args) {
        let durationMS = Cast.toNumber(args.DURATION) * 1000;
        durationMS = MathUtil.clamp(durationMS, 0, 3000);
        const note = MathUtil.clamp(Cast.toNumber(args.NOTE), 25, 125); // valid PoweredUp sounds
        if (durationMS === 0) return; // PoweredUp plays duration '0' forever
        return new Promise(resolve => {
            const tone = this._noteToTone(note);
            this._device.playTone(tone, durationMS);

            // Ensure this block runs for a fixed amount of time even when no device is connected.
            setTimeout(resolve, durationMS);
        });
    }

    /**
     * Compare the distance sensor's value to a reference.
     * @param {object} args - the block's arguments.
     * @property {string} OP - the comparison operation: '<' or '>'.
     * @property {number} REFERENCE - the value to compare against.
     * @return {boolean} - the result of the comparison, or false on error.
     */
    whenDistance (args) {
        switch (args.OP) {
        case '<':
        case '&lt;':
            return this._device.distance < Cast.toNumber(args.REFERENCE);
        case '>':
        case '&gt;':
            return this._device.distance > Cast.toNumber(args.REFERENCE);
        default:
            log.warn(`Unknown comparison operator in whenDistance: ${args.OP}`);
            return false;
        }
    }

    /**
     * Test whether the tilt sensor is currently tilted.
     * @param {object} args - the block's arguments.
     * @property {TiltDirection} TILT_DIRECTION_ANY - the tilt direction to test (up, down, left, right, or any).
     * @return {boolean} - true if the tilt sensor is tilted past a threshold in the specified direction.
     */
    whenTilted (args) {
        return this._isTilted(args.TILT_DIRECTION_ANY);
    }

    /**
     * @return {number} - the distance sensor's value, scaled to the [0,100] range.
     */
    getDistance () {
        return this._device.distance;
    }

    /**
     * Test whether the tilt sensor is currently tilted.
     * @param {object} args - the block's arguments.
     * @property {TiltDirection} TILT_DIRECTION_ANY - the tilt direction to test (up, down, left, right, or any).
     * @return {boolean} - true if the tilt sensor is tilted past a threshold in the specified direction.
     */
    isTilted (args) {
        return this._isTilted(args.TILT_DIRECTION_ANY);
    }

    /**
     * @param {object} args - the block's arguments.
     * @property {TiltDirection} TILT_DIRECTION - the direction (up, down, left, right) to check.
     * @return {number} - the tilt sensor's angle in the specified direction.
     * Note that getTiltAngle(up) = -getTiltAngle(down) and getTiltAngle(left) = -getTiltAngle(right).
     */
    getTiltAngle (args) {
        return this._getTiltAngle(args.TILT_DIRECTION);
    }

    /**
     * Test whether the tilt sensor is currently tilted.
     * @param {TiltDirection} direction - the tilt direction to test (up, down, left, right, or any).
     * @return {boolean} - true if the tilt sensor is tilted past a threshold in the specified direction.
     * @private
     */
    _isTilted (direction) {
        switch (direction) {
        case TiltDirection.ANY:
            return (Math.abs(this._device.tiltX) >= Scratch3PoweredUpBlocks.TILT_THRESHOLD) ||
                (Math.abs(this._device.tiltY) >= Scratch3PoweredUpBlocks.TILT_THRESHOLD);
        default:
            return this._getTiltAngle(direction) >= Scratch3PoweredUpBlocks.TILT_THRESHOLD;
        }
    }

    /**
     * @param {TiltDirection} direction - the direction (up, down, left, right) to check.
     * @return {number} - the tilt sensor's angle in the specified direction.
     * Note that getTiltAngle(up) = -getTiltAngle(down) and getTiltAngle(left) = -getTiltAngle(right).
     * @private
     */
    _getTiltAngle (direction) {
        switch (direction) {
        case TiltDirection.UP:
            return this._device.tiltY > 45 ? 256 - this._device.tiltY : -this._device.tiltY;
        case TiltDirection.DOWN:
            return this._device.tiltY > 45 ? this._device.tiltY - 256 : this._device.tiltY;
        case TiltDirection.LEFT:
            return this._device.tiltX > 45 ? 256 - this._device.tiltX : -this._device.tiltX;
        case TiltDirection.RIGHT:
            return this._device.tiltX > 45 ? this._device.tiltX - 256 : this._device.tiltX;
        default:
            log.warn(`Unknown tilt direction in _getTiltAngle: ${direction}`);
        }
    }

    /**
     * Call a callback for each motor indexed by the provided motor ID.
     * @param {MotorID} motorID - the ID specifier.
     * @param {Function} callback - the function to call with the numeric motor index for each motor.
     * @private
     */
    _forEachMotor (motorID, callback) {
        let motors;
        switch (motorID) {
        case MotorID.A:
            motors = [0];
            break;
        case MotorID.B:
            motors = [1];
            break;
        case MotorID.ALL:
            motors = [0, 1];
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
     * @param {number} midiNote - the MIDI note value to convert.
     * @return {number} - the frequency, in Hz, corresponding to that MIDI note value.
     * @private
     */
    _noteToTone (midiNote) {
        // Note that MIDI note 69 is A4, 440 Hz
        return 440 * Math.pow(2, (midiNote - 69) / 12);
    }
}

module.exports = Scratch3PoweredUpBlocks;
