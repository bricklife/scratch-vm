const ArgumentType = require('../../extension-support/argument-type');
const BlockType = require('../../extension-support/block-type');
const Cast = require('../../util/cast');
const formatMessage = require('format-message');
const color = require('../../util/color');
const BLE = require('../../io/ble');
const Base64Util = require('../../util/base64-util');
const MathUtil = require('../../util/math-util');
const RateLimiter = require('../../util/rateLimiter.js');
const log = require('../../util/log');

/**
 * Icon svg to be displayed at the left edge of each extension block, encoded as a data URI.
 * @type {string}
 */
// eslint-disable-next-line max-len
const iconURI = 'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAYAAACOEfKtAAAAAXNSR0IArs4c6QAABDtJREFUeAHtm01IVFEUx88bxzIdi4xamFa4CDJIohBapOBCGTFok0RtI2jTwk0JBYJBtahtEG5zYZugcNBFkJs2RSRY0EIqzSDSvkYtG33dM+Ot8fHOu+f53jg+Ow/kzjv33HPu/b3//ZgPAeQSAkJACAgBISAEhIAQEAJCQAgIASEgBISAEBACkSFg+enpk4dgu/k3n4BsHFO9W9uo22JRH0Cx+29UIKWqteq4Vvda5fObRxTol5jDP+64J2+bjpFVBakYeVqQsKEHFQUGRMpWYFQUYeIxWOF+kmifzZ0kTO2d9aJAJxGf98ZdWMfTTy7J1qxu6a9MZXL+TkUMbYXk0iLcVQfRGreIaiCTsRI43/YdUm71qQp4ptoecavTNhXjeXIWjup7ThkZBXrBw4EiWPQhBx3zqNONOD7ad7kssJ4c2QLcauVRMwCVq33c0pSVQf/Pebhl25BoKgGoWJ57s6rRyCKAZUEafeCHW2vaFgpAPe3oNO41FAz01kuGs6UpF9Vufu5fJATmvJDnwi84rgrXJcDpr+8jM4V1hwtVLillei4BROJQFKhjz6XzHrM2upTliXIX60qTlzpXeoZzZ1oCqCyiQIoM0y4AmaAoNwFIkWHaBSATFOUmACkyTLsAZIKi3AQgRYZpF4BMUJSbAKTIMO2hvhPhvMNg9isybqLAgI8qFAWu9fvWgGMOtbkoMCDOUBQYsA+uzU2f+7k2CsGoP090fqVAhRYFUmSY9nWnwGKvp36VLwpkKo1yE4AUGaZdADJBUW4CkCLDtAtAJijKbfnrZaoa4Mr1e+qr5//3utZ91pORKDCgNtjnwNT9mwFTRat58tQlVoeNCrTASmOkkngpK+BGcNJj1WP3GhNDgfZ7FaC+cttO+Do95RUrUnWPBoc5/U30dnu7GRWofraUzVSz75B3pP+0lqFA6FPb0MXauobYx4nXMP3p3YZA1dHe6jqOHbv2QmPzafy975ISj1E1RgX2Xj4zZltwB7M1NHYAJtioF44Nx4gXjhnHbhorR4EQryvtyoxnDmzekmjBpzMx/hIm345C+ttnyGQWTDnWdT1uGLi+4xKlZlmur5b1OF4X7+J03POQmB+gZ2BgU2b8923LhgvqZG1Ubn7bqLzGaYvKQ8H0dHaylMEGqCFcvdF/UL0+B7bdqpLVqt/VVuq6KJa5o4o6aeQ2yz7OtM0fp2+A+Y3xdRaobY+iKk+2HYbd1VVOlxX3H6Zm4MHQi7+LtN8Orwi2DvIHnor5m8zwyBggIOrCOvTBi7tIU7G0vdj5WZuI7ixV6k1mbn6hBdVVv786+1e1PZFtMvMlDa/eTGX/sgYfizSVM99ezPyBp7AeCGeTWc0ireObymLlDw2gHmD+JqP++2JPzr76RVrH5ZbFzs/tp/gJASEgBISAEBACQkAICAEhIASEgBAQAkJACKyGwB8od0IZW+SbHgAAAABJRU5ErkJggg==';

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
 * Enum for Duplo Train sensor and output types.
 * @readonly
 * @enum {number}
 */
const DuploTrainTypes = {
    LED: 0x17,
    MOTOR: 0x29,
    SPEAKER: 0x2a,
    COLOR: 0x2b,
    SPEEDOMETER: 0x2c
};

/**
 * Enum for connection/port ids assigned to internal DuploTrain output devices.
 * @readonly
 * @enum {number}
 */
const DuploTrainConnectIDs = {
    SPEAKER: 0x01,
    LED: 0x11
};

/**
 * Manage power, direction, and timers for one Duplo Train motor.
 */
class DuploTrainMotor {
    /**
     * Construct a DuploTrainMotor instance.
     * @param {DuploTrain} parent - the Duplo Train device which owns this motor.
     * @param {int} index - the zero-based index of this motor on its parent device.
     */
    constructor (parent, index) {
        /**
         * The Duplo Train device which owns this motor.
         * @type {DuploTrain}
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
        this._setNewTimeout(this.setMotorOff, DuploTrainMotor.BRAKE_TIME_MS);
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
 * Manage communication with a Duplo Train device over a Bluetooth Low Energy client socket.
 */
class DuploTrain {

    constructor (runtime, extensionId) {

        /**
         * The Scratch 3.0 runtime used to trigger the green flag button.
         * @type {Runtime}
         * @private
         */
        this._runtime = runtime;
        this._runtime.on('PROJECT_STOP_ALL', this._stopAll.bind(this));

        /**
         * The id of the extension this peripheral belongs to.
         */
        this._extensionId = extensionId;

        /**
         * The device ports that connect to motors and sensors.
         * @type {string[]}
         * @private
         */
        this._ports = {}; // TODO: rename?

        /**
         * The motors which this Duplo Train could possibly have.
         * @type {DuploTrainMotor[]}
         * @private
         */
        this._motors = [null, null];

        /**
         * The most recently received value for each sensor.
         * @type {Object.<string, number>}
         * @private
         */
        this._sensors = {
            color: -1
        };

        /**
         * The Bluetooth connection session for reading/writing device data.
         * @type {BLESession}
         * @private
         */
        this._ble = null;
        this._runtime.registerPeripheralExtension(extensionId, this);

        /**
         * A rate limiter utility, to help limit the rate at which we send BLE messages
         * over the socket to Scratch Link to a maximum number of sends per second.
         * @type {RateLimiter}
         * @private
         */
        this._rateLimiter = new RateLimiter(BLESendRateMax);

        this.reset = this.reset.bind(this);
        this._onConnect = this._onConnect.bind(this);
        this._onMessage = this._onMessage.bind(this);
    }

    /**
     * @return {number} - the latest value received from the color sensor.
     */
    get color () {
        return this._sensors.color;
    }

    /**
     * Access a particular motor on this device.
     * @param {int} index - the zero-based index of the desired motor.
     * @return {DuploTrainMotor} - the DuploTrainMotor instance, if any, at that index.
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

    setLED (color) {
        let index = allColors.indexOf(color);
        if (index < 0) {
            index = Cast.toNumber(color);
        }
        
        const cmd = new Uint8Array(8);
        cmd[0] = 0x08;
        cmd[1] = 0x00;
        cmd[2] = 0x81;
        cmd[3] = DuploTrainConnectIDs.LED; // connect id
        cmd[4] = 0x11;
        cmd[5] = 0x51;
        cmd[6] = 0x00;
        cmd[7] = index;

        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    playSound (sound) {
        let index = this._soundIndex(sound);
        if (index == null) {
            index = Cast.toNumber(sound);
        }
        
        const cmd = new Uint8Array(8);
        cmd[0] = 0x08;
        cmd[1] = 0x00;
        cmd[2] = 0x81;
        cmd[3] = DuploTrainConnectIDs.SPEAKER; // connect id
        cmd[4] = 0x11;
        cmd[5] = 0x51;
        cmd[6] = 0x01;
        cmd[7] = index;
    
        return this._send(UUID.OUTPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
    }

    _soundIndex (sound) {
        switch (sound) {
        case Sound.BRAKE:
            return 0x03;
        case Sound.DEPARTURE:
            return 0x05;
        case Sound.REFILL:
            return 0x07;
        case Sound.HORN:
            return 0x09;
        case Sound.STEAM:
            return 0x0a;
        default:
            return null;
        }
    }
    
    /**
     * Called by the runtime when user wants to scan for a device.
     */
    scan () {
        if (this._ble) {
            this._ble.disconnect();
        }
        this._ble = new BLE(this._runtime, this._extensionId, {
            filters: [{
                services: [UUID.DEVICE_SERVICE]
            }]
        }, this._onConnect, this.reset);
    }

    /**
     * Called by the runtime when user wants to connect to a certain device.
     * @param {number} id - the id of the device to connect to.
     */
    connect (id) {
        this._ble.connectPeripheral(id);
    }

    /**
     * Disconnects from the current BLE session.
     */
    disconnect () {
        if (this._ble) {
            this._ble.disconnect();
        }

        this.reset();
    }

    /**
     * Reset all the state and timeout/interval ids.
     */
    reset () {
        this._ports = {};
        this._motors = [null, null];
        this._sensors = {
            color: -1
        };
    }

    /**
     * Called by the runtime to detect whether the device is connected.
     * @return {boolean} - the connected state.
     */
    isConnected () {
        let connected = false;
        if (this._ble) {
            connected = this._ble.isConnected();
        }
        return connected;
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
        if (!this.isConnected()) return Promise.resolve();

        if (useLimiter) {
            if (!this._rateLimiter.okayToSend()) return Promise.resolve();
        }

        return this._ble.write(UUID.IO_SERVICE, uuid, message, 'base64');
    }

    /**
     * Sets LED mode and initial color and starts reading data from device after BLE has connected.
     * @private
     */
    _onConnect () {
        this._ble.startNotifications(UUID.DEVICE_SERVICE, UUID.ATTACHED_IO, this._onMessage);
    }

    /**
     * Process the sensor data from the incoming BLE characteristic.
     * @param {object} base64 - the incoming BLE data.
     * @private
     */
    _onMessage (base64) {
        const data = Base64Util.base64ToUint8Array(base64);
        // log.info(`> [${data}]`);

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
            const connectID = data[3];
            const type = this._ports[connectID];
            switch (type) {
            case DuploTrainTypes.COLOR:
                this._sensors.color = data[4];
                break;
            default:
                break;
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
        if (type === DuploTrainTypes.COLOR) {
            this._sensors.color = -1;
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
        if (type === DuploTrainTypes.MOTOR) {
            this._motors[connectID] = new DuploTrainMotor(this, connectID);
        } else {
            let mode = this._sensorMode(type);
            if (mode != null) {
                // Register sensors
                const cmd = new Uint8Array(10);
                cmd[0] = 0x0a;
                cmd[1] = 0x00;
                cmd[2] = 0x41;
                cmd[3] = connectID;
                cmd[4] = mode;
                cmd[5] = 0x01
                cmd[6] = 0x00;
                cmd[7] = 0x00;
                cmd[8] = 0x00;
                cmd[9] = 0x01; // notifications enabled: true

                setTimeout(() => {
                    this._send(UUID.INPUT_COMMAND, Base64Util.uint8ArrayToBase64(cmd));
                }, 100);
            }
        }
    }

    _sensorMode (type) {
        switch (type) {
        case DuploTrainTypes.SPEAKER:
            return 1; // ??
        case DuploTrainTypes.COLOR:
            return 0; // Color
        default:
            return null;
        }
    }

    /**
     * Stop the tone playing and motors on the Duplo Train hub.
     */
    _stopAll () {
        if (!this.isConnected()) return;
        this.stopAllMotors();
    }
}

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

const Color = {
    BLACK: 'black',
    PINK: 'pink',
    PURPLE: 'purple',
    BLUE: 'blue',
    LIGHTBLUE: 'light blue',
    LIGHTGREEN: 'light green',
    GREEN: 'green',
    YELLOW: 'yellow',
    ORANGE: 'orange',
    RED: 'red',
    WHITE: 'white',
    NONE: 'none'
};

const allColors = [
    Color.BLACK,
    Color.PINK,
    Color.PURPLE,
    Color.BLUE,
    Color.LIGHTBLUE,
    Color.LIGHTGREEN,
    Color.GREEN,
    Color.YELLOW,
    Color.ORANGE,
    Color.RED,
    Color.WHITE
];

const Sound = {
    BRAKE: 'brake',
    DEPARTURE: 'departure',
    REFILL: 'refill',
    HORN: 'horn',
    STEAM: 'steam'
};

/**
 * Scratch 3.0 blocks to interact with a LEGO Duplo Train device.
 */
class Scratch3DuploTrainBlocks {

    /**
     * @return {string} - the ID of this extension.
     */
    static get EXTENSION_ID () {
        return 'duploTrain';
    }

    /**
     * Construct a set of Duplo Train blocks.
     * @param {Runtime} runtime - the Scratch 3.0 runtime.
     */
    constructor (runtime) {
        /**
         * The Scratch 3.0 runtime.
         * @type {Runtime}
         */
        this.runtime = runtime;

        // Create a new DuploTrain device instance
        this._peripheral = new DuploTrain(this.runtime, Scratch3DuploTrainBlocks.EXTENSION_ID);
    }

    /**
     * @returns {object} metadata for this extension and its blocks.
     */
    getInfo () {
        return {
            id: Scratch3DuploTrainBlocks.EXTENSION_ID,
            name: 'Duplo Train',
            blockIconURI: iconURI,
            showStatusButton: true,
            blocks: [
                {
                    opcode: 'startMotorPowerFor',
                    text: formatMessage({
                        id: 'duploTrain.startMotorPowerFor',
                        default: 'set motor power to [POWER] for [DURATION] sec',
                        description: 'set the motor\'s power and turn it on for some time'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
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
                        id: 'duploTrain.startMotorPower',
                        default: 'set motor power to [POWER]',
                        description: 'set the motor\'s power and turn it on'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        POWER: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        }
                    }
                },
                {
                    opcode: 'motorOff',
                    text: formatMessage({
                        id: 'duploTrain.motorOff',
                        default: 'turn motor off',
                        description: 'turn a motor off'
                    }),
                    blockType: BlockType.COMMAND
                },
                {
                    opcode: 'setLEDColor',
                    text: formatMessage({
                        id: 'duploTrain.setLEDColor',
                        default: 'set LED color to [LED_COLOR]',
                        description: 'set the LED color'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        LED_COLOR: {
                            type: ArgumentType.STRING,
                            menu: 'LED_COLOR',
                            defaultValue: Color.BLUE
                        }
                    }
                },
                {
                    opcode: 'playSound',
                    text: formatMessage({
                        id: 'duploTrain.playSound',
                        default: 'play [SOUND] sound',
                        description: 'play the sound'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        SOUND: {
                            type: ArgumentType.STRING,
                            menu: 'SOUND',
                            defaultValue: Sound.BRAKE
                        }
                    }
                },
                {
                    opcode: 'whenColor',
                    text: formatMessage({
                        id: 'duploTrain.whenColor',
                        default: 'when sensor color is [SENSOR_COLOR]',
                        description: 'check when sensor color changed to a certain color'
                    }),
                    blockType: BlockType.HAT,
                    arguments: {
                        SENSOR_COLOR: {
                            type: ArgumentType.STRING,
                            menu: 'SENSOR_COLOR',
                            defaultValue: Color.NONE
                        }
                    }
                },
                {
                    opcode: 'isColor',
                    text: formatMessage({
                        id: 'duploTrain.isColor',
                        default: 'sensor color is [SENSOR_COLOR]?',
                        description: 'whether sensor color is a certain color'
                    }),
                    blockType: BlockType.BOOLEAN,
                    arguments: {
                        SENSOR_COLOR: {
                            type: ArgumentType.STRING,
                            menu: 'SENSOR_COLOR',
                            defaultValue: Color.NONE
                        }
                    }
                },
                {
                    opcode: 'getColor',
                    text: formatMessage({
                        id: 'duploTrain.getColor',
                        default: 'color',
                        description: 'the value returned by the color sensor'
                    }),
                    blockType: BlockType.REPORTER
                }
            ],
            menus: {
                MOTOR_DIRECTION: [MotorDirection.FORWARD, MotorDirection.BACKWARD, MotorDirection.REVERSE],
                LED_COLOR: allColors,
                SOUND: [Sound.BRAKE, Sound.DEPARTURE, Sound.REFILL, Sound.HORN, Sound.STEAM],
                SENSOR_COLOR: [
                    Color.NONE,
                    Color.BLACK,
                    Color.BLUE,
                    Color.LIGHTGREEN,
                    Color.YELLOW,
                    Color.RED,
                    Color.WHITE
                ],
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
                const motor = this._peripheral.motor(motorIndex);
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
                const motor = this._peripheral.motor(motorIndex);
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
            const motor = this._peripheral.motor(motorIndex);
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
            const motor = this._peripheral.motor(motorIndex);
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
            const motor = this._peripheral.motor(motorIndex);
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
            const motor = this._peripheral.motor(motorIndex);
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

    setLEDColor (args) {
        this._peripheral.setLED(args.LED_COLOR);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    playSound (args) {
        this._peripheral.playSound(args.SOUND);

        return new Promise(resolve => {
            window.setTimeout(() => {
                resolve();
            }, BLESendInterval);
        });
    }

    whenColor (args) {
        return this._isColor(args.SENSOR_COLOR);
    }

    isColor (args) {
        return this._isColor(args.SENSOR_COLOR);
    }

    getColor () {
        let color = allColors[this._peripheral.color];
        if (color == null) {
            return Color.NONE;
        }
        return color;
    }

    _isColor (color) {
        let index = allColors.indexOf(color);
        if (index < 0) {
            if (color == Color.NONE) {
                index == -1;
            } else {
                return false;
            }
        }
        return this._peripheral.color == index;
    }

    /**
     * Call a callback for each motor indexed by the provided motor ID.
     * @param {MotorID} motorID - the ID specifier.
     * @param {Function} callback - the function to call with the numeric motor index for each motor.
     * @private
     */
    _forEachMotor (motorID, callback) {
        callback(0);
    }
}

module.exports = Scratch3DuploTrainBlocks;
