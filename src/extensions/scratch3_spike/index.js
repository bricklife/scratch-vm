const ArgumentType = require('../../extension-support/argument-type');
const BlockType = require('../../extension-support/block-type');
const Cast = require('../../util/cast');
const formatMessage = require('format-message');
const BT = require('../../io/bt');
const Base64Util = require('../../util/base64-util');
const MathUtil = require('../../util/math-util');
const RateLimiter = require('../../util/rateLimiter.js');

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

const SpikeOrientation = {
    front: 1,
    back: 2,
    up: 3,
    down: 4,
    rightside: 5,
    leftside: 6
};

const SpikeMotorStopMode = {
    float: 0,
    brake: 1,
    hold: 2
};

class SpikeMotorSetting {

    constructor () {
        this._speed = 75;
        this._stopMode = SpikeMotorStopMode.brake;
        this._stallDetection = true;
    }

    get speed () {
        return this._speed;
    }

    set speed (value) {
        this._speed = MathUtil.clamp(value, -100, 100);
    }

    get stopMode () {
        return this._stopMode;
    }

    set stopMode (value) {
        if (value < 0 || value > 2) {
            return;
        }

        this._stopMode = value;
    }

    get stallDetection () {
        return this._stallDetection;
    }

    set stallDetection (value) {
        this._stallDetection = value;
    }
}

class Spike {

    constructor (runtime, extensionId) {

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
         * The state of all sensor values.
         * @type {string[]}
         * @private
         */
        this._sensors = {
            buttons: [0, 0, 0, 0],
            angle: {
                pitch: 0,
                roll: 0,
                yaw: 0
            },
            orientation: SpikeOrientation.front
        };

        this._pixelBrightness = 100;

        this._motorSettings = {
            A: new SpikeMotorSetting(),
            B: new SpikeMotorSetting(),
            C: new SpikeMotorSetting(),
            D: new SpikeMotorSetting(),
            E: new SpikeMotorSetting(),
            F: new SpikeMotorSetting()
        };

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

    get angle () {
        return this._sensors.angle;
    }

    get orientation () {
        return this._sensors.orientation;
    }

    get pixelBrightness () {
        return this._pixelBrightness;
    }

    set pixelBrightness (value) {
        this._pixelBrightness = value;
    }

    get motorSettings () {
        return this._motorSettings;
    }

    beep (freq, time) {
        console.log(`freq: ${freq}, time: ${time}`);
    }

    stopAll () {
        this.stopAllMotors();
        this.stopSound();
    }

    stopSound () {
        // this.send(cmd, false); // don't use rate limiter to ensure sound stops
    }

    stopAllMotors () {
    }

    /**
     * Called by the runtime when user wants to scan for an SPIKE Hub.
     */
    scan () {
        if (this._bt) {
            this._bt.disconnect();
        }
        this._bt = new BT(this._runtime, this._extensionId, {
            majorDeviceClass: 8,
            minorDeviceClass: 1
        }, this._onConnect, this.reset, this._onMessage);
    }

    /**
     * Called by the runtime when user wants to connect to a certain SPIKE Hub.
     * @param {number} id - the id of the peripheral to connect to.
     */
    connect (id) {
        if (this._bt) {
            this._bt.connectPeripheral(id);
        }
    }

    /**
     * Called by the runtime when user wants to disconnect from the SPIKE Hub.
     */
    disconnect () {
        if (this._bt) {
            this._bt.disconnect();
        }

        this.reset();
    }

    /**
     * Reset all the state and timeout/interval ids.
     */
    reset () {
        this._sensors = {
            buttons: [0, 0, 0, 0],
            angle: {
                pitch: 0,
                roll: 0,
                yaw: 0
            },
            orientation: SpikeOrientation.front
        };
    }

    /**
     * Called by the runtime to detect whether the SPIKE Hub is connected.
     * @return {boolean} - the connected state.
     */
    isConnected () {
        let connected = false;
        if (this._bt) {
            connected = this._bt.isConnected();
        }
        return connected;
    }

    sendJSON (json, useLimiter = false) {
        const jsonText = JSON.stringify(json);
        console.log('> ' + jsonText);

        if (!this.isConnected()) return Promise.resolve();

        if (useLimiter) {
            if (!this._rateLimiter.okayToSend()) return Promise.resolve();
        }

        if (!json.hasOwnProperty('i')) {
            return this._bt.sendMessage({
                message: `${jsonText}\r`
            });
        }

        const promise = new Promise((resolve, reject) => {
            this._openRequests[json.i] = {resolve, reject};
        });

        this._bt.sendMessage({
            message: `${jsonText}\r`
        });

        return promise;
    }

    sendCommand (method, params, needsResponse = true) {
        if (needsResponse) {
            const id = Math.random().toString(36)
                .slice(-4);

            return this.sendJSON({
                i: id,
                m: method,
                p: params
            });
        }

        return this.sendJSON({
            m: method,
            p: params
        });
    }

    /**
     * When the SPIKE Hub connects
     * @private
     */
    _onConnect () {
        this.sendCommand('trigger_current_state', {}, false);
    }

    /**
     * Message handler for incoming SPIKE Hub reply messages
     *
     * @param {object} params - incoming message parameters
     * @private
     */
    _onMessage (params) {
        const message = params.message;
        const data = Base64Util.base64ToUint8Array(message);
        const text = (new TextDecoder()).decode(data);
        const responses = text.trim().split('\r');

        try {
            responses.forEach(jsonText => {
                const json = JSON.parse(jsonText);
                if (json.hasOwnProperty('i') || json.m !== 0) {
                    console.log('< ' + jsonText);
                }
                this.parseResponse(json);
            });
        } catch (error) {
            console.log(text);
        }
    }

    parseResponse (response) {
        if (response.hasOwnProperty('m')) {
            switch (response.m) {
            case 0:
                // Hub (Ports, Acceleration, Gyro Rate, Tilt Angle, LED Matrix, Timer)
                {
                    const angle = response.p[8];
                    this._sensors.angle.yaw = angle[0];
                    this._sensors.angle.pitch = angle[1];
                    this._sensors.angle.roll = angle[2];
                }
                break;
            case 1:
                // Strage
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
                if (SpikeOrientation.hasOwnProperty(response.p)) {
                    this._sensors.orientation = SpikeOrientation[response.p];
                }
                break;
            default:
                break;
            }
        }

        if (response.hasOwnProperty('i')) {
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
    static get EXTENSION_ID () {
        return 'spike';
    }

    /**
     * Creates a new instance of the SPIKE Prime extension.
     * @param  {object} runtime VM runtime
     * @constructor
     */
    constructor (runtime) {
        /**
         * The Scratch 3.0 runtime.
         * @type {Runtime}
         */
        this.runtime = runtime;

        // Create a new SPIKE Hub instance
        this._peripheral = new Spike(this.runtime, Scratch3SpikeBlocks.EXTENSION_ID);

        this._playNoteForPicker = this._playNoteForPicker.bind(this);
        this.runtime.on('PLAY_NOTE', this._playNoteForPicker);
    }

    /**
     * Define the SPIKE Prime extension.
     * @return {object} Extension description.
     */
    getInfo () {
        return {
            id: Scratch3SpikeBlocks.EXTENSION_ID,
            name: 'LEGO SPIKE Prime',
            blockIconURI: blockIconURI,
            showStatusButton: true,
            blocks: [
                {
                    opcode: 'motorGoDirectionToPosition',
                    text: formatMessage({
                        id: 'spike.motorGoDirectionToPosition',
                        default: '[PORT] go [DIRECTION] to position [POSITION]',
                        description: 'NEEDS DESCRIPTION'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        PORT: {
                            type: ArgumentType.STRING,
                            menu: 'port',
                            defaultValue: 'A'
                        },
                        DIRECTION: {
                            type: ArgumentType.STRING,
                            menu: 'position_direction',
                            defaultValue: 'shortest'
                        },
                        POSITION: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 0
                        }
                    }
                },
                {
                    opcode: 'motorStart',
                    text: formatMessage({
                        id: 'spike.motorStart',
                        default: '[PORT] start motor [DIRECTION]',
                        description: 'NEEDS DESCRIPTION'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        PORT: {
                            type: ArgumentType.STRING,
                            menu: 'port',
                            defaultValue: 'A'
                        },
                        DIRECTION: {
                            type: ArgumentType.NUMBER,
                            menu: 'direction',
                            defaultValue: 1
                        }
                    }
                },
                {
                    opcode: 'motorStop',
                    text: formatMessage({
                        id: 'spike.motorStop',
                        default: '[PORT] stop motor',
                        description: 'NEEDS DESCRIPTION'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        PORT: {
                            type: ArgumentType.STRING,
                            menu: 'port',
                            defaultValue: 'A'
                        }
                    }
                },
                {
                    opcode: 'motorSetSpeed',
                    text: formatMessage({
                        id: 'spike.motorSetSpeed',
                        default: '[PORT] set speed to [SPEED] %',
                        description: 'NEEDS DESCRIPTION'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        PORT: {
                            type: ArgumentType.STRING,
                            menu: 'port',
                            defaultValue: 'A'
                        },
                        SPEED: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 75
                        }
                    }
                },
                '---',
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
                {
                    opcode: 'centerButtonLights',
                    text: formatMessage({
                        id: 'spike.centerButtonLights',
                        default: 'set center button light to [COLOR]',
                        description: 'set the center button light'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        COLOR: {
                            type: ArgumentType.STRING,
                            menu: 'center_button_colors',
                            defaultValue: 9
                        }
                    }
                },
                {
                    opcode: 'ultrasonicLightUp',
                    text: formatMessage({
                        id: 'spike.ultrasonicLightUp',
                        default: '[PORT] light up [LIGHT0] [LIGHT1] [LIGHT2] [LIGHT3]',
                        description: 'set the ultrasonic sensor light'
                    }),
                    blockType: BlockType.COMMAND,
                    arguments: {
                        PORT: {
                            type: ArgumentType.STRING,
                            menu: 'port',
                            defaultValue: 'A'
                        },
                        LIGHT0: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        },
                        LIGHT1: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        },
                        LIGHT2: {
                            type: ArgumentType.NUMBER,
                            defaultValue: 100
                        },
                        LIGHT3: {
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
                },
                center_button_colors: {
                    acceptReporters: true,
                    items: [
                        {
                            text: 'violet',
                            value: 1
                        },
                        {
                            text: 'blue',
                            value: 3
                        },
                        {
                            text: 'azure',
                            value: 4
                        },
                        {
                            text: 'green',
                            value: 5
                        },
                        {
                            text: 'yellow',
                            value: 7
                        },
                        {
                            text: 'red',
                            value: 9
                        },
                        {
                            text: 'white',
                            value: 10
                        },
                        {
                            text: 'no color',
                            value: -1
                        }
                    ]
                },
                direction: {
                    acceptReporters: false,
                    items: [
                        {
                            text: 'clockwise',
                            value: 1
                        },
                        {
                            text: 'counterclockwise',
                            value: -1
                        }
                    ]
                },
                position_direction: {
                    acceptReporters: false,
                    items: [
                        {
                            text: 'shortest path',
                            value: 'shortest'
                        },
                        {
                            text: 'clockwise',
                            value: 'clockwise'
                        },
                        {
                            text: 'counterclockwise',
                            value: 'counterclockwise'
                        }
                    ]
                }
            }
        };
    }

    motorGoDirectionToPosition (args) {
        const direction = args.DIRECTION;
        const position = Math.round(Cast.toNumber(args.POSITION));

        const ports = this._validatePorts(Cast.toString(args.PORT));
        const settings = this._peripheral.motorSettings;

        const promises = ports.map(port => {
            const setting = settings[port];
            return this._peripheral.sendCommand('scratch.motor_go_direction_to_position', {
                port: port,
                direction: direction,
                position: position,
                speed: setting.speed,
                stop: setting.stopMode,
                stall: setting.stallDetection
            });
        });

        return Promise.all(promises).then(() => {});
    }

    motorStart (args) {
        const direction = args.DIRECTION;

        const ports = this._validatePorts(Cast.toString(args.PORT));
        const settings = this._peripheral.motorSettings;

        const promises = ports.map(port => {
            const setting = settings[port];
            return this._peripheral.sendCommand('scratch.motor_start', {
                port: port,
                speed: setting.speed * direction,
                stall: setting.stallDetection
            });
        });

        return Promise.all(promises).then(() => {});
    }

    motorStop (args) {
        const ports = this._validatePorts(Cast.toString(args.PORT));
        const settings = this._peripheral.motorSettings;

        const promises = ports.map(port => {
            const setting = settings[port];
            return this._peripheral.sendCommand('scratch.motor_stop', {
                port: port,
                stop: setting.stopMode
            });
        });

        return Promise.all(promises).then(() => {});
    }

    motorSetSpeed (args) {
        const speed = Cast.toNumber(args.SPEED);

        const ports = this._validatePorts(Cast.toString(args.PORT));
        const settings = this._peripheral.motorSettings;

        ports.forEach(port => {
            settings[port].speed = speed;
        });
    }

    displayImageFor (args) {
        const brightness = Math.round(9 * this._peripheral.pixelBrightness / 100);
        const symbol = (Cast.toString(args.MATRIX).replace(/\D/g, '') + '0'.repeat(25)).slice(0, 25);
        const image = symbol.replace(/1/g, brightness).match(/.{5}/g)
            .join(':');
        let duration = Cast.toNumber(args.DURATION) * 1000;
        duration = MathUtil.clamp(duration, 0, 60000);

        return this._peripheral.sendCommand('scratch.display_image_for', {
            image: image,
            duration: duration
        });
    }

    displayImage (args) {
        const brightness = Math.round(9 * this._peripheral.pixelBrightness / 100);
        const symbol = (Cast.toString(args.MATRIX).replace(/\D/g, '') + '0'.repeat(25)).slice(0, 25);
        const image = symbol.replace(/1/g, brightness).match(/.{5}/g)
            .join(':');

        return this._peripheral.sendCommand('scratch.display_image', {
            image: image
        });
    }

    displayText (args) {
        const text = Cast.toString(args.TEXT);

        return this._peripheral.sendCommand('scratch.display_text', {
            text: text
        });
    }

    displayClear () {
        return this._peripheral.sendCommand('scratch.display_clear', {});
    }

    displaySetBrightness (args) {
        const brightness = MathUtil.clamp(Cast.toNumber(args.BRIGHTNESS), 0, 100);

        this._peripheral.pixelBrightness = brightness;
    }

    displaySetPixel (args) {
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

    centerButtonLights (args) {
        const color = Cast.toNumber(args.COLOR);

        return this._peripheral.sendCommand('scratch.center_button_lights', {
            color: color
        });
    }

    ultrasonicLightUp (args) {
        const port = Cast.toString(args.PORT).trim()
            .toUpperCase();
        if (!SpikePorts.includes(port)) {
            return Promise.resolve();
        }

        const lights = [];
        for (let i = 0; i < 4; i++) {
            lights.push(MathUtil.clamp(Cast.toNumber(args[`LIGHT${i}`]), 0, 100));
        }

        return this._peripheral.sendCommand('scratch.ultrasonic_light_up', {
            port: port,
            lights: lights
        });
    }

    getOrientation () {
        return this._peripheral.orientation;
    }

    getAngle (args) {
        const axis = Cast.toString(args.AXIS);

        return this._peripheral.angle[axis];
    }

    _playNoteForPicker (note, category) {
        if (category !== this.getInfo().name) return;
        this.beep({
            NOTE: note,
            TIME: 0.25
        });
    }

    beep (args) {
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

    _validatePorts (text) {
        return text.toUpperCase().replace(/[^ABCDEF]/g, '')
            .split('')
            .filter((x, i, self) => self.indexOf(x) === i)
            .sort();
    }
}

module.exports = Scratch3SpikeBlocks;
