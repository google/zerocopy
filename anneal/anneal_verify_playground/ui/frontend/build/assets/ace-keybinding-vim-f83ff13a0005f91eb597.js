(globalThis["webpackChunkui"] = globalThis["webpackChunkui"] || []).push([["ace-keybinding-vim"],{

/***/ "./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-vim.js"
/*!*******************************************************************************************************!*\
  !*** ./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-vim.js ***!
  \*******************************************************************************************************/
(module, __unused_webpack_exports, __webpack_require__) {

/* module decorator */ module = __webpack_require__.nmd(module);
ace.define("ace/ext/hardwrap",["require","exports","module","ace/range","ace/editor","ace/config"], function(require, exports, module){/**
 * ## Text hard wrapping extension for automatic line breaking and text formatting.
 *
 * Provides intelligent line wrapping functionality that breaks long lines at configurable column limits while
 * preserving indentation and optionally merging short adjacent lines. Supports both automatic wrapping during text
 * input and manual formatting of selected text ranges.
 *
 * **Enable:** `editor.setOption("hardWrap", true)`
 * or configure it during editor initialization in the options object.
 * @module
 */
"use strict";
var Range = require("../range").Range;
function hardWrap(editor, options) {
    var max = options.column || editor.getOption("printMarginColumn");
    var allowMerge = options.allowMerge != false;
    var row = Math.min(options.startRow, options.endRow);
    var endRow = Math.max(options.startRow, options.endRow);
    var session = editor.session;
    while (row <= endRow) {
        var line = session.getLine(row);
        if (line.length > max) {
            var space = findSpace(line, max, 5);
            if (space) {
                var indentation = /^\s*/.exec(line)[0];
                session.replace(new Range(row, space.start, row, space.end), "\n" + indentation);
            }
            endRow++;
        }
        else if (allowMerge && /\S/.test(line) && row != endRow) {
            var nextLine = session.getLine(row + 1);
            if (nextLine && /\S/.test(nextLine)) {
                var trimmedLine = line.replace(/\s+$/, "");
                var trimmedNextLine = nextLine.replace(/^\s+/, "");
                var mergedLine = trimmedLine + " " + trimmedNextLine;
                var space = findSpace(mergedLine, max, 5);
                if (space && space.start > trimmedLine.length || mergedLine.length < max) {
                    var replaceRange = new Range(row, trimmedLine.length, row + 1, nextLine.length - trimmedNextLine.length);
                    session.replace(replaceRange, " ");
                    row--;
                    endRow--;
                }
                else if (trimmedLine.length < line.length) {
                    session.remove(new Range(row, trimmedLine.length, row, line.length));
                }
            }
        }
        row++;
    }
    function findSpace(line, max, min) {
        if (line.length < max)
            return;
        var before = line.slice(0, max);
        var after = line.slice(max);
        var spaceAfter = /^(?:(\s+)|(\S+)(\s+))/.exec(after);
        var spaceBefore = /(?:(\s+)|(\s+)(\S+))$/.exec(before);
        var start = 0;
        var end = 0;
        if (spaceBefore && !spaceBefore[2]) {
            start = max - spaceBefore[1].length;
            end = max;
        }
        if (spaceAfter && !spaceAfter[2]) {
            if (!start)
                start = max;
            end = max + spaceAfter[1].length;
        }
        if (start) {
            return {
                start: start,
                end: end
            };
        }
        if (spaceBefore && spaceBefore[2] && spaceBefore.index > min) {
            return {
                start: spaceBefore.index,
                end: spaceBefore.index + spaceBefore[2].length
            };
        }
        if (spaceAfter && spaceAfter[2]) {
            start = max + spaceAfter[2].length;
            return {
                start: start,
                end: start + spaceAfter[3].length
            };
        }
    }
}
function wrapAfterInput(e) {
    if (e.command.name == "insertstring" && /\S/.test(e.args)) {
        var editor = e.editor;
        var cursor = editor.selection.cursor;
        if (cursor.column <= editor.renderer.$printMarginColumn)
            return;
        var lastDelta = editor.session.$undoManager.$lastDelta;
        hardWrap(editor, {
            startRow: cursor.row, endRow: cursor.row,
            allowMerge: false
        });
        if (lastDelta != editor.session.$undoManager.$lastDelta)
            editor.session.markUndoGroup();
    }
}
var Editor = require("../editor").Editor;
require("../config").defineOptions(Editor.prototype, "editor", {
    hardWrap: {
        set: function (val) {
            if (val) {
                this.commands.on("afterExec", wrapAfterInput);
            }
            else {
                this.commands.off("afterExec", wrapAfterInput);
            }
        },
        value: false
    }
});
exports.hardWrap = hardWrap;

});

ace.define("ace/keyboard/vim",["require","exports","module","ace/range","ace/lib/event_emitter","ace/lib/dom","ace/lib/oop","ace/lib/keys","ace/lib/event","ace/search","ace/lib/useragent","ace/search_highlight","ace/commands/multi_select_commands","ace/mode/text","ace/ext/hardwrap","ace/multi_select"], function(require, exports, module){// CodeMirror, copyright (c) by Marijn Haverbeke and others
'use strict';
function log() {
    var d = "";
    function format(p) {
        if (typeof p != "object")
            return p + "";
        if ("line" in p) {
            return p.line + ":" + p.ch;
        }
        if ("anchor" in p) {
            return format(p.anchor) + "->" + format(p.head);
        }
        if (Array.isArray(p))
            return "[" + p.map(function (x) {
                return format(x);
            }) + "]";
        return JSON.stringify(p);
    }
    for (var i = 0; i < arguments.length; i++) {
        var p = arguments[i];
        var f = format(p);
        d += f + "  ";
    }
    console.log(d);
}
var Range = require("../range").Range;
var EventEmitter = require("../lib/event_emitter").EventEmitter;
var domLib = require("../lib/dom");
var oop = require("../lib/oop");
var KEYS = require("../lib/keys");
var event = require("../lib/event");
var Search = require("../search").Search;
var useragent = require("../lib/useragent");
var SearchHighlight = require("../search_highlight").SearchHighlight;
var multiSelectCommands = require("../commands/multi_select_commands");
var TextModeTokenRe = require("../mode/text").Mode.prototype.tokenRe;
var hardWrap = require("../ext/hardwrap").hardWrap;
require("../multi_select");
var CodeMirror = function (ace) {
    this.ace = ace;
    this.state = {};
    this.marks = {};
    this.options = {};
    this.$uid = 0;
    this.onChange = this.onChange.bind(this);
    this.onSelectionChange = this.onSelectionChange.bind(this);
    this.onBeforeEndOperation = this.onBeforeEndOperation.bind(this);
    this.ace.on('change', this.onChange);
    this.ace.on('changeSelection', this.onSelectionChange);
    this.ace.on('beforeEndOperation', this.onBeforeEndOperation);
};
CodeMirror.Pos = function (line, ch) {
    if (!(this instanceof Pos))
        return new Pos(line, ch);
    this.line = line;
    this.ch = ch;
};
CodeMirror.defineOption = function (name, val, setter) { };
CodeMirror.commands = {
    redo: function (cm) { cm.ace.redo(); },
    undo: function (cm) { cm.ace.undo(); },
    newlineAndIndent: function (cm) { cm.ace.insert("\n"); },
    goLineLeft: function (cm) { cm.ace.selection.moveCursorLineStart(); },
    goLineRight: function (cm) { cm.ace.selection.moveCursorLineEnd(); }
};
CodeMirror.keyMap = {};
CodeMirror.addClass = CodeMirror.rmClass = function () { };
CodeMirror.e_stop = CodeMirror.e_preventDefault = event.stopEvent;
CodeMirror.keyName = function (e) {
    var key = (KEYS[e.keyCode] || e.key || "");
    if (key.length == 1)
        key = key.toUpperCase();
    key = event.getModifierString(e).replace(/(^|-)\w/g, function (m) {
        return m.toUpperCase();
    }) + key;
    return key;
};
CodeMirror.keyMap['default'] = function (key) {
    return function (cm) {
        var cmd = cm.ace.commands.commandKeyBinding[key.toLowerCase()];
        return cmd && cm.ace.execCommand(cmd) !== false;
    };
};
CodeMirror.lookupKey = function lookupKey(key, map, handle) {
    if (!map)
        map = "default";
    if (typeof map == "string")
        map = CodeMirror.keyMap[map] || CodeMirror.keyMap['default'];
    var found = typeof map == "function" ? map(key) : map[key];
    if (found === false)
        return "nothing";
    if (found === "...")
        return "multi";
    if (found != null && handle(found))
        return "handled";
    if (map.fallthrough) {
        if (!Array.isArray(map.fallthrough))
            return lookupKey(key, map.fallthrough, handle);
        for (var i = 0; i < map.fallthrough.length; i++) {
            var result = lookupKey(key, map.fallthrough[i], handle);
            if (result)
                return result;
        }
    }
};
CodeMirror.findMatchingTag = function (cm, head) {
    return cm.findMatchingTag(head);
};
CodeMirror.findEnclosingTag = function (cm, head) {
};
CodeMirror.signal = function (o, name, e) { return o._signal(name, e); };
CodeMirror.on = event.addListener;
CodeMirror.off = event.removeListener;
CodeMirror.isWordChar = function (ch) {
    if (ch < "\x7f")
        return /^\w$/.test(ch);
    TextModeTokenRe.lastIndex = 0;
    return TextModeTokenRe.test(ch);
};
(function () {
    oop.implement(CodeMirror.prototype, EventEmitter);
    this.destroy = function () {
        this.ace.off('change', this.onChange);
        this.ace.off('changeSelection', this.onSelectionChange);
        this.ace.off('beforeEndOperation', this.onBeforeEndOperation);
        this.removeOverlay();
    };
    this.virtualSelectionMode = function () {
        return this.ace.inVirtualSelectionMode && this.ace.selection.index;
    };
    this.onChange = function (delta) {
        if (this.$lineHandleChanges) {
            this.$lineHandleChanges.push(delta);
        }
        var change = { text: delta.action[0] == 'i' ? delta.lines : [] };
        var curOp = this.curOp = this.curOp || {};
        if (!curOp.changeHandlers)
            curOp.changeHandlers = this._eventRegistry["change"] && this._eventRegistry["change"].slice();
        if (!curOp.lastChange) {
            curOp.lastChange = curOp.change = change;
        }
        else {
            curOp.lastChange.next = curOp.lastChange = change;
        }
        this.$updateMarkers(delta);
    };
    this.onSelectionChange = function () {
        var curOp = this.curOp = this.curOp || {};
        if (!curOp.cursorActivityHandlers)
            curOp.cursorActivityHandlers = this._eventRegistry["cursorActivity"] && this._eventRegistry["cursorActivity"].slice();
        this.curOp.cursorActivity = true;
        if (this.ace.inMultiSelectMode) {
            this.ace.keyBinding.removeKeyboardHandler(multiSelectCommands.keyboardHandler);
        }
    };
    this.operation = function (fn, force) {
        if (!force && this.curOp || force && this.curOp && this.curOp.force) {
            return fn();
        }
        if (force || !this.ace.curOp) {
            if (this.curOp)
                this.onBeforeEndOperation();
        }
        if (!this.ace.curOp) {
            var prevOp = this.ace.prevOp;
            this.ace.startOperation({
                command: { name: "vim", scrollIntoView: "cursor" }
            });
        }
        var curOp = this.curOp = this.curOp || {};
        this.curOp.force = force;
        var result = fn();
        if (this.ace.curOp && this.ace.curOp.command.name == "vim") {
            if (this.state.dialog)
                this.ace.curOp.command.scrollIntoView = this.ace.curOp.vimDialogScroll;
            this.ace.endOperation();
            if (!curOp.cursorActivity && !curOp.lastChange && prevOp)
                this.ace.prevOp = prevOp;
        }
        if (force || !this.ace.curOp) {
            if (this.curOp)
                this.onBeforeEndOperation();
        }
        return result;
    };
    this.onBeforeEndOperation = function () {
        var op = this.curOp;
        if (op) {
            if (op.change) {
                this.signal("change", op.change, op);
            }
            if (op && op.cursorActivity) {
                this.signal("cursorActivity", null, op);
            }
            this.curOp = null;
        }
    };
    this.signal = function (eventName, e, handlers) {
        var listeners = handlers ? handlers[eventName + "Handlers"]
            : (this._eventRegistry || {})[eventName];
        if (!listeners)
            return;
        listeners = listeners.slice();
        for (var i = 0; i < listeners.length; i++)
            listeners[i](this, e);
    };
    this.firstLine = function () { return 0; };
    this.lastLine = function () { return this.ace.session.getLength() - 1; };
    this.lineCount = function () { return this.ace.session.getLength(); };
    this.setCursor = function (line, ch) {
        if (typeof line === 'object') {
            ch = line.ch;
            line = line.line;
        }
        var shouldScroll = !this.curOp && !this.ace.inVirtualSelectionMode;
        if (!this.ace.inVirtualSelectionMode)
            this.ace.exitMultiSelectMode();
        this.ace.session.unfold({ row: line, column: ch });
        this.ace.selection.moveTo(line, ch);
        if (shouldScroll) {
            this.ace.renderer.scrollCursorIntoView();
            this.ace.endOperation();
        }
    };
    this.getCursor = function (p) {
        var sel = this.ace.selection;
        var pos = p == 'anchor' ? (sel.isEmpty() ? sel.lead : sel.anchor) :
            p == 'head' || !p ? sel.lead : sel.getRange()[p];
        return toCmPos(pos);
    };
    this.listSelections = function (p) {
        var ranges = this.ace.multiSelect.rangeList.ranges;
        if (!ranges.length || this.ace.inVirtualSelectionMode)
            return [{ anchor: this.getCursor('anchor'), head: this.getCursor('head') }];
        return ranges.map(function (r) {
            return {
                anchor: this.clipPos(toCmPos(r.cursor == r.end ? r.start : r.end)),
                head: this.clipPos(toCmPos(r.cursor))
            };
        }, this);
    };
    this.setSelections = function (p, primIndex) {
        var sel = this.ace.multiSelect;
        var ranges = p.map(function (x) {
            var anchor = toAcePos(x.anchor);
            var head = toAcePos(x.head);
            var r = Range.comparePoints(anchor, head) < 0
                ? new Range.fromPoints(anchor, head)
                : new Range.fromPoints(head, anchor);
            r.cursor = Range.comparePoints(r.start, head) ? r.end : r.start;
            return r;
        });
        if (this.ace.inVirtualSelectionMode) {
            this.ace.selection.fromOrientedRange(ranges[0]);
            return;
        }
        if (!primIndex) {
            ranges = ranges.reverse();
        }
        else if (ranges[primIndex]) {
            ranges.push(ranges.splice(primIndex, 1)[0]);
        }
        sel.toSingleRange(ranges[0].clone());
        var session = this.ace.session;
        for (var i = 0; i < ranges.length; i++) {
            var range = session.$clipRangeToDocument(ranges[i]); // todo why ace doesn't do this?
            sel.addRange(range);
        }
    };
    this.setSelection = function (a, h, options) {
        var sel = this.ace.selection;
        sel.moveTo(a.line, a.ch);
        sel.selectTo(h.line, h.ch);
        if (options && options.origin == '*mouse') {
            this.onBeforeEndOperation();
        }
    };
    this.somethingSelected = function (p) {
        return !this.ace.selection.isEmpty();
    };
    this.clipPos = function (p) {
        var pos = this.ace.session.$clipPositionToDocument(p.line, p.ch);
        return toCmPos(pos);
    };
    this.foldCode = function (pos) {
        this.ace.session.$toggleFoldWidget(pos.line, {});
    };
    this.markText = function (cursor) {
        return { clear: function () { }, find: function () { } };
    };
    this.$updateMarkers = function (delta) {
        var isInsert = delta.action == "insert";
        var start = delta.start;
        var end = delta.end;
        var rowShift = (end.row - start.row) * (isInsert ? 1 : -1);
        var colShift = (end.column - start.column) * (isInsert ? 1 : -1);
        if (isInsert)
            end = start;
        for (var i in this.marks) {
            var point = this.marks[i];
            var cmp = Range.comparePoints(point, start);
            if (cmp < 0) {
                continue; // delta starts after the range
            }
            if (cmp === 0) {
                if (isInsert) {
                    if (!point.$insertRight) {
                        cmp = 1;
                    }
                    else if (point.bias == 1) {
                        cmp = 1;
                    }
                    else {
                        point.bias = -1;
                        continue;
                    }
                }
            }
            var cmp2 = isInsert ? cmp : Range.comparePoints(point, end);
            if (cmp2 > 0) {
                point.row += rowShift;
                point.column += point.row == end.row ? colShift : 0;
                continue;
            }
            if (!isInsert && cmp2 <= 0) {
                point.row = start.row;
                point.column = start.column;
                if (cmp2 === 0)
                    point.bias = 1;
            }
        }
    };
    var Marker = function (cm, id, row, column) {
        this.cm = cm;
        this.id = id;
        this.row = row;
        this.column = column;
        cm.marks[this.id] = this;
    };
    Marker.prototype.clear = function () { delete this.cm.marks[this.id]; };
    Marker.prototype.find = function () { return toCmPos(this); };
    this.setBookmark = function (cursor, options) {
        var bm = new Marker(this, this.$uid++, cursor.line, cursor.ch);
        if (!options || !options.insertLeft)
            bm.$insertRight = true;
        this.marks[bm.id] = bm;
        return bm;
    };
    this.moveH = function (increment, unit) {
        if (unit == 'char') {
            var sel = this.ace.selection;
            sel.clearSelection();
            sel.moveCursorBy(0, increment);
        }
    };
    this.findPosV = function (start, amount, unit, goalColumn) {
        if (unit == 'page') {
            var renderer = this.ace.renderer;
            var config = renderer.layerConfig;
            amount = amount * Math.floor(config.height / config.lineHeight);
            unit = 'line';
        }
        if (unit == 'line') {
            var screenPos = this.ace.session.documentToScreenPosition(start.line, start.ch);
            if (goalColumn != null)
                screenPos.column = goalColumn;
            screenPos.row += amount;
            screenPos.row = Math.min(Math.max(0, screenPos.row), this.ace.session.getScreenLength() - 1);
            var pos = this.ace.session.screenToDocumentPosition(screenPos.row, screenPos.column);
            return toCmPos(pos);
        }
        else {
            debugger;
        }
    };
    this.charCoords = function (pos, mode) {
        if (mode == 'div' || !mode) {
            var sc = this.ace.session.documentToScreenPosition(pos.line, pos.ch);
            return { left: sc.column, top: sc.row };
        }
        if (mode == 'local') {
            var renderer = this.ace.renderer;
            var sc = this.ace.session.documentToScreenPosition(pos.line, pos.ch);
            var lh = renderer.layerConfig.lineHeight;
            var cw = renderer.layerConfig.characterWidth;
            var top = lh * sc.row;
            return { left: sc.column * cw, top: top, bottom: top + lh };
        }
    };
    this.coordsChar = function (pos, mode) {
        var renderer = this.ace.renderer;
        if (mode == 'local') {
            var row = Math.max(0, Math.floor(pos.top / renderer.lineHeight));
            var col = Math.max(0, Math.floor(pos.left / renderer.characterWidth));
            var ch = renderer.session.screenToDocumentPosition(row, col);
            return toCmPos(ch);
        }
        else if (mode == 'div') {
            throw "not implemented";
        }
    };
    this.getSearchCursor = function (query, pos, caseFold) {
        var caseSensitive = false;
        var isRegexp = false;
        if (query instanceof RegExp && !query.global) {
            caseSensitive = !query.ignoreCase;
            query = query.source;
            isRegexp = true;
        }
        if (query == "\\n") {
            query = "\n";
            isRegexp = false;
        }
        var search = new Search();
        if (pos.ch == undefined)
            pos.ch = Number.MAX_VALUE;
        var acePos = { row: pos.line, column: pos.ch };
        var cm = this;
        var last = null;
        return {
            findNext: function () { return this.find(false); },
            findPrevious: function () { return this.find(true); },
            find: function (back) {
                search.setOptions({
                    needle: query,
                    caseSensitive: caseSensitive,
                    wrap: false,
                    backwards: back,
                    regExp: isRegexp,
                    start: last || acePos
                });
                var range = search.find(cm.ace.session);
                last = range;
                return last && [!last.isEmpty()];
            },
            from: function () { return last && toCmPos(last.start); },
            to: function () { return last && toCmPos(last.end); },
            replace: function (text) {
                if (last) {
                    last.end = cm.ace.session.doc.replace(last, text);
                }
            }
        };
    };
    this.scrollTo = function (x, y) {
        var renderer = this.ace.renderer;
        var config = renderer.layerConfig;
        var maxHeight = config.maxHeight;
        maxHeight -= (renderer.$size.scrollerHeight - renderer.lineHeight) * renderer.$scrollPastEnd;
        if (y != null)
            this.ace.session.setScrollTop(Math.max(0, Math.min(y, maxHeight)));
        if (x != null)
            this.ace.session.setScrollLeft(Math.max(0, Math.min(x, config.width)));
    };
    this.scrollInfo = function () { return 0; };
    this.scrollIntoView = function (pos, margin) {
        if (pos) {
            var renderer = this.ace.renderer;
            var viewMargin = { "top": 0, "bottom": margin };
            renderer.scrollCursorIntoView(toAcePos(pos), (renderer.lineHeight * 2) / renderer.$size.scrollerHeight, viewMargin);
        }
    };
    this.getLine = function (row) { return this.ace.session.getLine(row); };
    this.getRange = function (s, e) {
        return this.ace.session.getTextRange(new Range(s.line, s.ch, e.line, e.ch));
    };
    this.replaceRange = function (text, s, e) {
        if (!e)
            e = s;
        var range = new Range(s.line, s.ch, e.line, e.ch);
        this.ace.session.$clipRangeToDocument(range);
        return this.ace.session.replace(range, text);
    };
    this.replaceSelection =
        this.replaceSelections = function (p) {
            var strings = Array.isArray(p) && p;
            var sel = this.ace.selection;
            if (this.ace.inVirtualSelectionMode) {
                this.ace.session.replace(sel.getRange(), strings ? p[0] || "" : p);
                return;
            }
            sel.inVirtualSelectionMode = true;
            var ranges = sel.rangeList.ranges;
            if (!ranges.length)
                ranges = [this.ace.multiSelect.getRange()];
            for (var i = ranges.length; i--;)
                this.ace.session.replace(ranges[i], strings ? p[i] || "" : p);
            sel.inVirtualSelectionMode = false;
        };
    this.getSelection = function () {
        return this.ace.getSelectedText();
    };
    this.getSelections = function () {
        return this.listSelections().map(function (x) {
            return this.getRange(x.anchor, x.head);
        }, this);
    };
    this.getInputField = function () {
        return this.ace.textInput.getElement();
    };
    this.getWrapperElement = function () {
        return this.ace.container;
    };
    var optMap = {
        indentWithTabs: "useSoftTabs",
        indentUnit: "tabSize",
        tabSize: "tabSize",
        firstLineNumber: "firstLineNumber",
        readOnly: "readOnly"
    };
    this.setOption = function (name, val) {
        this.state[name] = val;
        switch (name) {
            case 'indentWithTabs':
                name = optMap[name];
                val = !val;
                break;
            case 'keyMap':
                this.state.$keyMap = val;
                return;
                // removed by dead control flow

            default:
                name = optMap[name];
        }
        if (name)
            this.ace.setOption(name, val);
    };
    this.getOption = function (name) {
        var val;
        var aceOpt = optMap[name];
        if (aceOpt)
            val = this.ace.getOption(aceOpt);
        switch (name) {
            case 'indentWithTabs':
                name = optMap[name];
                return !val;
            case 'keyMap':
                return this.state.$keyMap || 'vim';
        }
        return aceOpt ? val : this.state[name];
    };
    this.toggleOverwrite = function (on) {
        this.state.overwrite = on;
        return this.ace.setOverwrite(on);
    };
    this.addOverlay = function (o) {
        if (!this.$searchHighlight || !this.$searchHighlight.session) {
            var highlight = new SearchHighlight(null, "ace_highlight-marker", "text");
            var marker = this.ace.session.addDynamicMarker(highlight);
            highlight.id = marker.id;
            highlight.session = this.ace.session;
            highlight.destroy = function (o) {
                highlight.session.off("change", highlight.updateOnChange);
                highlight.session.off("changeEditor", highlight.destroy);
                highlight.session.removeMarker(highlight.id);
                highlight.session = null;
            };
            highlight.updateOnChange = function (delta) {
                var row = delta.start.row;
                if (row == delta.end.row)
                    highlight.cache[row] = undefined;
                else
                    highlight.cache.splice(row, highlight.cache.length);
            };
            highlight.session.on("changeEditor", highlight.destroy);
            highlight.session.on("change", highlight.updateOnChange);
        }
        var re = new RegExp(o.query.source, "gmi");
        this.$searchHighlight = o.highlight = highlight;
        this.$searchHighlight.setRegexp(re);
        this.ace.renderer.updateBackMarkers();
    };
    this.removeOverlay = function (o) {
        if (this.$searchHighlight && this.$searchHighlight.session) {
            this.$searchHighlight.destroy();
        }
    };
    this.getScrollInfo = function () {
        var renderer = this.ace.renderer;
        var config = renderer.layerConfig;
        return {
            left: renderer.scrollLeft,
            top: renderer.scrollTop,
            height: config.maxHeight,
            width: config.width,
            clientHeight: config.height,
            clientWidth: config.width
        };
    };
    this.getValue = function () {
        return this.ace.getValue();
    };
    this.setValue = function (v) {
        return this.ace.setValue(v, -1);
    };
    this.getTokenTypeAt = function (pos) {
        var token = this.ace.session.getTokenAt(pos.line, pos.ch);
        return token && /comment|string/.test(token.type) ? "string" : "";
    };
    this.findMatchingBracket = function (pos) {
        var m = this.ace.session.findMatchingBracket(toAcePos(pos));
        return { to: m && toCmPos(m) };
    };
    this.findMatchingTag = function (pos) {
        var m = this.ace.session.getMatchingTags(toAcePos(pos));
        if (!m)
            return;
        return {
            open: {
                from: toCmPos(m.openTag.start),
                to: toCmPos(m.openTag.end)
            },
            close: {
                from: toCmPos(m.closeTag.start),
                to: toCmPos(m.closeTag.end)
            }
        };
    };
    this.indentLine = function (line, method) {
        if (method === true)
            this.ace.session.indentRows(line, line, "\t");
        else if (method === false)
            this.ace.session.outdentRows(new Range(line, 0, line, 0));
    };
    this.indexFromPos = function (pos) {
        return this.ace.session.doc.positionToIndex(toAcePos(pos));
    };
    this.posFromIndex = function (index) {
        return toCmPos(this.ace.session.doc.indexToPosition(index));
    };
    this.focus = function (index) {
        return this.ace.textInput.focus();
    };
    this.blur = function (index) {
        return this.ace.blur();
    };
    this.defaultTextHeight = function (index) {
        return this.ace.renderer.layerConfig.lineHeight;
    };
    this.scanForBracket = function (pos, dir, _, options) {
        var re = options.bracketRegex.source;
        var tokenRe = /paren|text|operator|tag/;
        if (dir == 1) {
            var m = this.ace.session.$findClosingBracket(re.slice(1, 2), toAcePos(pos), tokenRe);
        }
        else {
            var m = this.ace.session.$findOpeningBracket(re.slice(-2, -1), { row: pos.line, column: pos.ch + 1 }, tokenRe);
            if (!m && options.bracketRegex && options.bracketRegex.test(this.getLine(pos.line)[pos.ch - 1])) {
                m = { row: pos.line, column: pos.ch - 1 };
            }
        }
        return m && { pos: toCmPos(m) };
    };
    this.refresh = function () {
        return this.ace.resize(true);
    };
    this.getMode = function () {
        return { name: this.getOption("mode") };
    };
    this.execCommand = function (name) {
        if (CodeMirror.commands.hasOwnProperty(name))
            return CodeMirror.commands[name](this);
        if (name == "indentAuto")
            return this.ace.execCommand("autoindent");
        console.log(name + " is not implemented");
    };
    this.getLineNumber = function (handle) {
        var deltas = this.$lineHandleChanges;
        if (!deltas)
            return null;
        var row = handle.row;
        for (var i = 0; i < deltas.length; i++) {
            var delta = deltas[i];
            if (delta.start.row != delta.end.row) {
                if (delta.action[0] == "i") {
                    if (delta.start.row < row)
                        row += delta.end.row - delta.start.row;
                }
                else {
                    if (delta.start.row < row) {
                        if (row < delta.end.row || row == delta.end.row && delta.start.column > 0) {
                            return null;
                        }
                        row -= delta.end.row - delta.start.row;
                    }
                }
            }
        }
        return row;
    };
    this.getLineHandle = function (row) {
        if (!this.$lineHandleChanges)
            this.$lineHandleChanges = [];
        return { text: this.ace.session.getLine(row), row: row };
    };
    this.releaseLineHandles = function () {
        this.$lineHandleChanges = undefined;
    };
    this.getLastEditEnd = function () {
        var undoManager = this.ace.session.$undoManager;
        if (undoManager && undoManager.$lastDelta)
            return toCmPos(undoManager.$lastDelta.end);
    };
}).call(CodeMirror.prototype);
function toAcePos(cmPos) {
    return { row: cmPos.line, column: cmPos.ch };
}
function toCmPos(acePos) {
    return new Pos(acePos.row, acePos.column);
}
var StringStream = CodeMirror.StringStream = function (string, tabSize) {
    this.pos = this.start = 0;
    this.string = string;
    this.tabSize = tabSize || 8;
    this.lastColumnPos = this.lastColumnValue = 0;
    this.lineStart = 0;
};
StringStream.prototype = {
    eol: function () { return this.pos >= this.string.length; },
    sol: function () { return this.pos == this.lineStart; },
    peek: function () { return this.string.charAt(this.pos) || undefined; },
    next: function () {
        if (this.pos < this.string.length)
            return this.string.charAt(this.pos++);
    },
    eat: function (match) {
        var ch = this.string.charAt(this.pos);
        if (typeof match == "string")
            var ok = ch == match;
        else
            var ok = ch && (match.test ? match.test(ch) : match(ch));
        if (ok) {
            ++this.pos;
            return ch;
        }
    },
    eatWhile: function (match) {
        var start = this.pos;
        while (this.eat(match)) { }
        return this.pos > start;
    },
    eatSpace: function () {
        var start = this.pos;
        while (/[\s\u00a0]/.test(this.string.charAt(this.pos)))
            ++this.pos;
        return this.pos > start;
    },
    skipToEnd: function () { this.pos = this.string.length; },
    skipTo: function (ch) {
        var found = this.string.indexOf(ch, this.pos);
        if (found > -1) {
            this.pos = found;
            return true;
        }
    },
    backUp: function (n) { this.pos -= n; },
    column: function () {
        throw "not implemented";
    },
    indentation: function () {
        throw "not implemented";
    },
    match: function (pattern, consume, caseInsensitive) {
        if (typeof pattern == "string") {
            var cased = function (str) { return caseInsensitive ? str.toLowerCase() : str; };
            var substr = this.string.substr(this.pos, pattern.length);
            if (cased(substr) == cased(pattern)) {
                if (consume !== false)
                    this.pos += pattern.length;
                return true;
            }
        }
        else {
            var match = this.string.slice(this.pos).match(pattern);
            if (match && match.index > 0)
                return null;
            if (match && consume !== false)
                this.pos += match[0].length;
            return match;
        }
    },
    current: function () { return this.string.slice(this.start, this.pos); },
    hideFirstChars: function (n, inner) {
        this.lineStart += n;
        try {
            return inner();
        }
        finally {
            this.lineStart -= n;
        }
    }
};
CodeMirror.defineExtension = function (name, fn) {
    CodeMirror.prototype[name] = fn;
};
domLib.importCssString(".normal-mode .ace_cursor{\n    border: none;\n    background-color: rgba(255,0,0,0.5);\n}\n.normal-mode .ace_hidden-cursors .ace_cursor{\n  background-color: transparent;\n  border: 1px solid red;\n  opacity: 0.7\n}\n.ace_dialog {\n  position: absolute;\n  left: 0; right: 0;\n  background: inherit;\n  z-index: 15;\n  padding: .1em .8em;\n  overflow: hidden;\n  color: inherit;\n}\n.ace_dialog-top {\n  border-bottom: 1px solid #444;\n  top: 0;\n}\n.ace_dialog-bottom {\n  border-top: 1px solid #444;\n  bottom: 0;\n}\n.ace_dialog input {\n  border: none;\n  outline: none;\n  background: transparent;\n  width: 20em;\n  color: inherit;\n  font-family: monospace;\n}", "vimMode", false);
(function () {
    function dialogDiv(cm, template, bottom) {
        var wrap = cm.ace.container;
        var dialog;
        dialog = wrap.appendChild(document.createElement("div"));
        if (bottom)
            dialog.className = "ace_dialog ace_dialog-bottom";
        else
            dialog.className = "ace_dialog ace_dialog-top";
        if (typeof template == "string") {
            dialog.innerHTML = template;
        }
        else { // Assuming it's a detached DOM element.
            dialog.appendChild(template);
        }
        return dialog;
    }
    function closeNotification(cm, newVal) {
        if (cm.state.currentNotificationClose)
            cm.state.currentNotificationClose();
        cm.state.currentNotificationClose = newVal;
    }
    CodeMirror.defineExtension("openDialog", function (template, callback, options) {
        if (this.virtualSelectionMode())
            return;
        if (!options)
            options = {};
        closeNotification(this, null);
        var dialog = dialogDiv(this, template, options.bottom);
        var closed = false, me = this;
        this.state.dialog = dialog;
        function close(newVal) {
            if (typeof newVal == 'string') {
                inp.value = newVal;
            }
            else {
                if (closed)
                    return;
                if (newVal && newVal.type == "blur") {
                    if (document.activeElement === inp)
                        return;
                }
                if (me.state.dialog == dialog) {
                    me.state.dialog = null;
                    me.focus();
                }
                closed = true;
                dialog.remove();
                if (options.onClose)
                    options.onClose(dialog);
                var cm = me;
                if (cm.state.vim) {
                    cm.state.vim.status = null;
                    cm.ace._signal("changeStatus");
                    cm.ace.renderer.$loop.schedule(cm.ace.renderer.CHANGE_CURSOR);
                }
            }
        }
        var inp = dialog.getElementsByTagName("input")[0], button;
        if (inp) {
            if (options.value) {
                inp.value = options.value;
                if (options.selectValueOnOpen !== false)
                    inp.select();
            }
            if (options.onInput)
                CodeMirror.on(inp, "input", function (e) { options.onInput(e, inp.value, close); });
            if (options.onKeyUp)
                CodeMirror.on(inp, "keyup", function (e) { options.onKeyUp(e, inp.value, close); });
            CodeMirror.on(inp, "keydown", function (e) {
                if (options && options.onKeyDown && options.onKeyDown(e, inp.value, close)) {
                    return;
                }
                if (e.keyCode == 13)
                    callback(inp.value);
                if (e.keyCode == 27 || (options.closeOnEnter !== false && e.keyCode == 13)) {
                    CodeMirror.e_stop(e);
                    close();
                }
            });
            if (options.closeOnBlur !== false)
                CodeMirror.on(inp, "blur", close);
            inp.focus();
        }
        else if (button = dialog.getElementsByTagName("button")[0]) {
            CodeMirror.on(button, "click", function () {
                close();
                me.focus();
            });
            if (options.closeOnBlur !== false)
                CodeMirror.on(button, "blur", close);
            button.focus();
        }
        return close;
    });
    CodeMirror.defineExtension("openNotification", function (template, options) {
        if (this.virtualSelectionMode())
            return;
        closeNotification(this, close);
        var dialog = dialogDiv(this, template, options && options.bottom);
        var closed = false, doneTimer;
        var duration = options && typeof options.duration !== "undefined" ? options.duration : 5000;
        function close() {
            if (closed)
                return;
            closed = true;
            clearTimeout(doneTimer);
            dialog.remove();
        }
        CodeMirror.on(dialog, 'click', function (e) {
            CodeMirror.e_preventDefault(e);
            close();
        });
        if (duration)
            doneTimer = setTimeout(close, duration);
        return close;
    });
})();
var Pos = CodeMirror.Pos;
function updateSelectionForSurrogateCharacters(cm, curStart, curEnd) {
    if (curStart.line === curEnd.line && curStart.ch >= curEnd.ch - 1) {
        var text = cm.getLine(curStart.line);
        var charCode = text.charCodeAt(curStart.ch);
        if (0xD800 <= charCode && charCode <= 0xD8FF) {
            curEnd.ch += 1;
        }
    }
    return { start: curStart, end: curEnd };
}
var defaultKeymap = [
    { keys: '<Left>', type: 'keyToKey', toKeys: 'h' },
    { keys: '<Right>', type: 'keyToKey', toKeys: 'l' },
    { keys: '<Up>', type: 'keyToKey', toKeys: 'k' },
    { keys: '<Down>', type: 'keyToKey', toKeys: 'j' },
    { keys: 'g<Up>', type: 'keyToKey', toKeys: 'gk' },
    { keys: 'g<Down>', type: 'keyToKey', toKeys: 'gj' },
    { keys: '<Space>', type: 'keyToKey', toKeys: 'l' },
    { keys: '<BS>', type: 'keyToKey', toKeys: 'h' },
    { keys: '<Del>', type: 'keyToKey', toKeys: 'x' },
    { keys: '<C-Space>', type: 'keyToKey', toKeys: 'W' },
    { keys: '<C-BS>', type: 'keyToKey', toKeys: 'B' },
    { keys: '<S-Space>', type: 'keyToKey', toKeys: 'w' },
    { keys: '<S-BS>', type: 'keyToKey', toKeys: 'b' },
    { keys: '<C-n>', type: 'keyToKey', toKeys: 'j' },
    { keys: '<C-p>', type: 'keyToKey', toKeys: 'k' },
    { keys: '<C-[>', type: 'keyToKey', toKeys: '<Esc>' },
    { keys: '<C-c>', type: 'keyToKey', toKeys: '<Esc>' },
    { keys: '<C-[>', type: 'keyToKey', toKeys: '<Esc>', context: 'insert' },
    { keys: '<C-c>', type: 'keyToKey', toKeys: '<Esc>', context: 'insert' },
    { keys: '<C-Esc>', type: 'keyToKey', toKeys: '<Esc>' }, // ipad keyboard sends C-Esc instead of C-[
    { keys: '<C-Esc>', type: 'keyToKey', toKeys: '<Esc>', context: 'insert' },
    { keys: 's', type: 'keyToKey', toKeys: 'cl', context: 'normal' },
    { keys: 's', type: 'keyToKey', toKeys: 'c', context: 'visual' },
    { keys: 'S', type: 'keyToKey', toKeys: 'cc', context: 'normal' },
    { keys: 'S', type: 'keyToKey', toKeys: 'VdO', context: 'visual' },
    { keys: '<Home>', type: 'keyToKey', toKeys: '0' },
    { keys: '<End>', type: 'keyToKey', toKeys: '$' },
    { keys: '<PageUp>', type: 'keyToKey', toKeys: '<C-b>' },
    { keys: '<PageDown>', type: 'keyToKey', toKeys: '<C-f>' },
    { keys: '<CR>', type: 'keyToKey', toKeys: 'j^', context: 'normal' },
    { keys: '<Ins>', type: 'keyToKey', toKeys: 'i', context: 'normal' },
    { keys: '<Ins>', type: 'action', action: 'toggleOverwrite', context: 'insert' },
    { keys: 'H', type: 'motion', motion: 'moveToTopLine', motionArgs: { linewise: true, toJumplist: true } },
    { keys: 'M', type: 'motion', motion: 'moveToMiddleLine', motionArgs: { linewise: true, toJumplist: true } },
    { keys: 'L', type: 'motion', motion: 'moveToBottomLine', motionArgs: { linewise: true, toJumplist: true } },
    { keys: 'h', type: 'motion', motion: 'moveByCharacters', motionArgs: { forward: false } },
    { keys: 'l', type: 'motion', motion: 'moveByCharacters', motionArgs: { forward: true } },
    { keys: 'j', type: 'motion', motion: 'moveByLines', motionArgs: { forward: true, linewise: true } },
    { keys: 'k', type: 'motion', motion: 'moveByLines', motionArgs: { forward: false, linewise: true } },
    { keys: 'gj', type: 'motion', motion: 'moveByDisplayLines', motionArgs: { forward: true } },
    { keys: 'gk', type: 'motion', motion: 'moveByDisplayLines', motionArgs: { forward: false } },
    { keys: 'w', type: 'motion', motion: 'moveByWords', motionArgs: { forward: true, wordEnd: false } },
    { keys: 'W', type: 'motion', motion: 'moveByWords', motionArgs: { forward: true, wordEnd: false, bigWord: true } },
    { keys: 'e', type: 'motion', motion: 'moveByWords', motionArgs: { forward: true, wordEnd: true, inclusive: true } },
    { keys: 'E', type: 'motion', motion: 'moveByWords', motionArgs: { forward: true, wordEnd: true, bigWord: true, inclusive: true } },
    { keys: 'b', type: 'motion', motion: 'moveByWords', motionArgs: { forward: false, wordEnd: false } },
    { keys: 'B', type: 'motion', motion: 'moveByWords', motionArgs: { forward: false, wordEnd: false, bigWord: true } },
    { keys: 'ge', type: 'motion', motion: 'moveByWords', motionArgs: { forward: false, wordEnd: true, inclusive: true } },
    { keys: 'gE', type: 'motion', motion: 'moveByWords', motionArgs: { forward: false, wordEnd: true, bigWord: true, inclusive: true } },
    { keys: '{', type: 'motion', motion: 'moveByParagraph', motionArgs: { forward: false, toJumplist: true } },
    { keys: '}', type: 'motion', motion: 'moveByParagraph', motionArgs: { forward: true, toJumplist: true } },
    { keys: '(', type: 'motion', motion: 'moveBySentence', motionArgs: { forward: false } },
    { keys: ')', type: 'motion', motion: 'moveBySentence', motionArgs: { forward: true } },
    { keys: '<C-f>', type: 'motion', motion: 'moveByPage', motionArgs: { forward: true } },
    { keys: '<C-b>', type: 'motion', motion: 'moveByPage', motionArgs: { forward: false } },
    { keys: '<C-d>', type: 'motion', motion: 'moveByScroll', motionArgs: { forward: true, explicitRepeat: true } },
    { keys: '<C-u>', type: 'motion', motion: 'moveByScroll', motionArgs: { forward: false, explicitRepeat: true } },
    { keys: 'gg', type: 'motion', motion: 'moveToLineOrEdgeOfDocument', motionArgs: { forward: false, explicitRepeat: true, linewise: true, toJumplist: true } },
    { keys: 'G', type: 'motion', motion: 'moveToLineOrEdgeOfDocument', motionArgs: { forward: true, explicitRepeat: true, linewise: true, toJumplist: true } },
    { keys: "g$", type: "motion", motion: "moveToEndOfDisplayLine" },
    { keys: "g^", type: "motion", motion: "moveToStartOfDisplayLine" },
    { keys: "g0", type: "motion", motion: "moveToStartOfDisplayLine" },
    { keys: '0', type: 'motion', motion: 'moveToStartOfLine' },
    { keys: '^', type: 'motion', motion: 'moveToFirstNonWhiteSpaceCharacter' },
    { keys: '+', type: 'motion', motion: 'moveByLines', motionArgs: { forward: true, toFirstChar: true } },
    { keys: '-', type: 'motion', motion: 'moveByLines', motionArgs: { forward: false, toFirstChar: true } },
    { keys: '_', type: 'motion', motion: 'moveByLines', motionArgs: { forward: true, toFirstChar: true, repeatOffset: -1 } },
    { keys: '$', type: 'motion', motion: 'moveToEol', motionArgs: { inclusive: true } },
    { keys: '%', type: 'motion', motion: 'moveToMatchedSymbol', motionArgs: { inclusive: true, toJumplist: true } },
    { keys: 'f<character>', type: 'motion', motion: 'moveToCharacter', motionArgs: { forward: true, inclusive: true } },
    { keys: 'F<character>', type: 'motion', motion: 'moveToCharacter', motionArgs: { forward: false } },
    { keys: 't<character>', type: 'motion', motion: 'moveTillCharacter', motionArgs: { forward: true, inclusive: true } },
    { keys: 'T<character>', type: 'motion', motion: 'moveTillCharacter', motionArgs: { forward: false } },
    { keys: ';', type: 'motion', motion: 'repeatLastCharacterSearch', motionArgs: { forward: true } },
    { keys: ',', type: 'motion', motion: 'repeatLastCharacterSearch', motionArgs: { forward: false } },
    { keys: '\'<register>', type: 'motion', motion: 'goToMark', motionArgs: { toJumplist: true, linewise: true } },
    { keys: '`<register>', type: 'motion', motion: 'goToMark', motionArgs: { toJumplist: true } },
    { keys: ']`', type: 'motion', motion: 'jumpToMark', motionArgs: { forward: true } },
    { keys: '[`', type: 'motion', motion: 'jumpToMark', motionArgs: { forward: false } },
    { keys: ']\'', type: 'motion', motion: 'jumpToMark', motionArgs: { forward: true, linewise: true } },
    { keys: '[\'', type: 'motion', motion: 'jumpToMark', motionArgs: { forward: false, linewise: true } },
    { keys: ']p', type: 'action', action: 'paste', isEdit: true, actionArgs: { after: true, isEdit: true, matchIndent: true } },
    { keys: '[p', type: 'action', action: 'paste', isEdit: true, actionArgs: { after: false, isEdit: true, matchIndent: true } },
    { keys: ']<character>', type: 'motion', motion: 'moveToSymbol', motionArgs: { forward: true, toJumplist: true } },
    { keys: '[<character>', type: 'motion', motion: 'moveToSymbol', motionArgs: { forward: false, toJumplist: true } },
    { keys: '|', type: 'motion', motion: 'moveToColumn' },
    { keys: 'o', type: 'motion', motion: 'moveToOtherHighlightedEnd', context: 'visual' },
    { keys: 'O', type: 'motion', motion: 'moveToOtherHighlightedEnd', motionArgs: { sameLine: true }, context: 'visual' },
    { keys: 'd', type: 'operator', operator: 'delete' },
    { keys: 'y', type: 'operator', operator: 'yank' },
    { keys: 'c', type: 'operator', operator: 'change' },
    { keys: '=', type: 'operator', operator: 'indentAuto' },
    { keys: '>', type: 'operator', operator: 'indent', operatorArgs: { indentRight: true } },
    { keys: '<', type: 'operator', operator: 'indent', operatorArgs: { indentRight: false } },
    { keys: 'g~', type: 'operator', operator: 'changeCase' },
    { keys: 'gu', type: 'operator', operator: 'changeCase', operatorArgs: { toLower: true }, isEdit: true },
    { keys: 'gU', type: 'operator', operator: 'changeCase', operatorArgs: { toLower: false }, isEdit: true },
    { keys: 'n', type: 'motion', motion: 'findNext', motionArgs: { forward: true, toJumplist: true } },
    { keys: 'N', type: 'motion', motion: 'findNext', motionArgs: { forward: false, toJumplist: true } },
    { keys: 'gn', type: 'motion', motion: 'findAndSelectNextInclusive', motionArgs: { forward: true } },
    { keys: 'gN', type: 'motion', motion: 'findAndSelectNextInclusive', motionArgs: { forward: false } },
    { keys: 'gq', type: 'operator', operator: 'hardWrap' },
    { keys: 'gw', type: 'operator', operator: 'hardWrap', operatorArgs: { keepCursor: true } },
    { keys: 'x', type: 'operatorMotion', operator: 'delete', motion: 'moveByCharacters', motionArgs: { forward: true }, operatorMotionArgs: { visualLine: false } },
    { keys: 'X', type: 'operatorMotion', operator: 'delete', motion: 'moveByCharacters', motionArgs: { forward: false }, operatorMotionArgs: { visualLine: true } },
    { keys: 'D', type: 'operatorMotion', operator: 'delete', motion: 'moveToEol', motionArgs: { inclusive: true }, context: 'normal' },
    { keys: 'D', type: 'operator', operator: 'delete', operatorArgs: { linewise: true }, context: 'visual' },
    { keys: 'Y', type: 'operatorMotion', operator: 'yank', motion: 'expandToLine', motionArgs: { linewise: true }, context: 'normal' },
    { keys: 'Y', type: 'operator', operator: 'yank', operatorArgs: { linewise: true }, context: 'visual' },
    { keys: 'C', type: 'operatorMotion', operator: 'change', motion: 'moveToEol', motionArgs: { inclusive: true }, context: 'normal' },
    { keys: 'C', type: 'operator', operator: 'change', operatorArgs: { linewise: true }, context: 'visual' },
    { keys: '~', type: 'operatorMotion', operator: 'changeCase', motion: 'moveByCharacters', motionArgs: { forward: true }, operatorArgs: { shouldMoveCursor: true }, context: 'normal' },
    { keys: '~', type: 'operator', operator: 'changeCase', context: 'visual' },
    { keys: '<C-u>', type: 'operatorMotion', operator: 'delete', motion: 'moveToStartOfLine', context: 'insert' },
    { keys: '<C-w>', type: 'operatorMotion', operator: 'delete', motion: 'moveByWords', motionArgs: { forward: false, wordEnd: false }, context: 'insert' },
    { keys: '<C-w>', type: 'idle', context: 'normal' },
    { keys: '<C-i>', type: 'action', action: 'jumpListWalk', actionArgs: { forward: true } },
    { keys: '<C-o>', type: 'action', action: 'jumpListWalk', actionArgs: { forward: false } },
    { keys: '<C-e>', type: 'action', action: 'scroll', actionArgs: { forward: true, linewise: true } },
    { keys: '<C-y>', type: 'action', action: 'scroll', actionArgs: { forward: false, linewise: true } },
    { keys: 'a', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'charAfter' }, context: 'normal' },
    { keys: 'A', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'eol' }, context: 'normal' },
    { keys: 'A', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'endOfSelectedArea' }, context: 'visual' },
    { keys: 'i', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'inplace' }, context: 'normal' },
    { keys: 'gi', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'lastEdit' }, context: 'normal' },
    { keys: 'I', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'firstNonBlank' }, context: 'normal' },
    { keys: 'gI', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'bol' }, context: 'normal' },
    { keys: 'I', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { insertAt: 'startOfSelectedArea' }, context: 'visual' },
    { keys: 'o', type: 'action', action: 'newLineAndEnterInsertMode', isEdit: true, interlaceInsertRepeat: true, actionArgs: { after: true }, context: 'normal' },
    { keys: 'O', type: 'action', action: 'newLineAndEnterInsertMode', isEdit: true, interlaceInsertRepeat: true, actionArgs: { after: false }, context: 'normal' },
    { keys: 'v', type: 'action', action: 'toggleVisualMode' },
    { keys: 'V', type: 'action', action: 'toggleVisualMode', actionArgs: { linewise: true } },
    { keys: '<C-v>', type: 'action', action: 'toggleVisualMode', actionArgs: { blockwise: true } },
    { keys: '<C-q>', type: 'action', action: 'toggleVisualMode', actionArgs: { blockwise: true } },
    { keys: 'gv', type: 'action', action: 'reselectLastSelection' },
    { keys: 'J', type: 'action', action: 'joinLines', isEdit: true },
    { keys: 'gJ', type: 'action', action: 'joinLines', actionArgs: { keepSpaces: true }, isEdit: true },
    { keys: 'p', type: 'action', action: 'paste', isEdit: true, actionArgs: { after: true, isEdit: true } },
    { keys: 'P', type: 'action', action: 'paste', isEdit: true, actionArgs: { after: false, isEdit: true } },
    { keys: 'r<character>', type: 'action', action: 'replace', isEdit: true },
    { keys: '@<register>', type: 'action', action: 'replayMacro' },
    { keys: 'q<register>', type: 'action', action: 'enterMacroRecordMode' },
    { keys: 'R', type: 'action', action: 'enterInsertMode', isEdit: true, actionArgs: { replace: true }, context: 'normal' },
    { keys: 'R', type: 'operator', operator: 'change', operatorArgs: { linewise: true, fullLine: true }, context: 'visual', exitVisualBlock: true },
    { keys: 'u', type: 'action', action: 'undo', context: 'normal' },
    { keys: 'u', type: 'operator', operator: 'changeCase', operatorArgs: { toLower: true }, context: 'visual', isEdit: true },
    { keys: 'U', type: 'operator', operator: 'changeCase', operatorArgs: { toLower: false }, context: 'visual', isEdit: true },
    { keys: '<C-r>', type: 'action', action: 'redo' },
    { keys: 'm<register>', type: 'action', action: 'setMark' },
    { keys: '"<register>', type: 'action', action: 'setRegister' },
    { keys: '<C-r><register>', type: 'action', action: 'insertRegister', context: 'insert', isEdit: true },
    { keys: '<C-o>', type: 'action', action: 'oneNormalCommand', context: 'insert' },
    { keys: 'zz', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'center' } },
    { keys: 'z.', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'center' }, motion: 'moveToFirstNonWhiteSpaceCharacter' },
    { keys: 'zt', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'top' } },
    { keys: 'z<CR>', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'top' }, motion: 'moveToFirstNonWhiteSpaceCharacter' },
    { keys: 'zb', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'bottom' } },
    { keys: 'z-', type: 'action', action: 'scrollToCursor', actionArgs: { position: 'bottom' }, motion: 'moveToFirstNonWhiteSpaceCharacter' },
    { keys: '.', type: 'action', action: 'repeatLastEdit' },
    { keys: '<C-a>', type: 'action', action: 'incrementNumberToken', isEdit: true, actionArgs: { increase: true, backtrack: false } },
    { keys: '<C-x>', type: 'action', action: 'incrementNumberToken', isEdit: true, actionArgs: { increase: false, backtrack: false } },
    { keys: '<C-t>', type: 'action', action: 'indent', actionArgs: { indentRight: true }, context: 'insert' },
    { keys: '<C-d>', type: 'action', action: 'indent', actionArgs: { indentRight: false }, context: 'insert' },
    { keys: 'a<register>', type: 'motion', motion: 'textObjectManipulation' },
    { keys: 'i<register>', type: 'motion', motion: 'textObjectManipulation', motionArgs: { textObjectInner: true } },
    { keys: '/', type: 'search', searchArgs: { forward: true, querySrc: 'prompt', toJumplist: true } },
    { keys: '?', type: 'search', searchArgs: { forward: false, querySrc: 'prompt', toJumplist: true } },
    { keys: '*', type: 'search', searchArgs: { forward: true, querySrc: 'wordUnderCursor', wholeWordOnly: true, toJumplist: true } },
    { keys: '#', type: 'search', searchArgs: { forward: false, querySrc: 'wordUnderCursor', wholeWordOnly: true, toJumplist: true } },
    { keys: 'g*', type: 'search', searchArgs: { forward: true, querySrc: 'wordUnderCursor', toJumplist: true } },
    { keys: 'g#', type: 'search', searchArgs: { forward: false, querySrc: 'wordUnderCursor', toJumplist: true } },
    { keys: ':', type: 'ex' }
];
var defaultKeymapLength = defaultKeymap.length;
var defaultExCommandMap = [
    { name: 'colorscheme', shortName: 'colo' },
    { name: 'map' },
    { name: 'imap', shortName: 'im' },
    { name: 'nmap', shortName: 'nm' },
    { name: 'vmap', shortName: 'vm' },
    { name: 'omap', shortName: 'om' },
    { name: 'noremap', shortName: 'no' },
    { name: 'nnoremap', shortName: 'nn' },
    { name: 'vnoremap', shortName: 'vn' },
    { name: 'inoremap', shortName: 'ino' },
    { name: 'onoremap', shortName: 'ono' },
    { name: 'unmap' },
    { name: 'mapclear', shortName: 'mapc' },
    { name: 'nmapclear', shortName: 'nmapc' },
    { name: 'vmapclear', shortName: 'vmapc' },
    { name: 'imapclear', shortName: 'imapc' },
    { name: 'omapclear', shortName: 'omapc' },
    { name: 'write', shortName: 'w' },
    { name: 'undo', shortName: 'u' },
    { name: 'redo', shortName: 'red' },
    { name: 'set', shortName: 'se' },
    { name: 'setlocal', shortName: 'setl' },
    { name: 'setglobal', shortName: 'setg' },
    { name: 'sort', shortName: 'sor' },
    { name: 'substitute', shortName: 's', possiblyAsync: true },
    { name: 'startinsert', shortName: 'start' },
    { name: 'nohlsearch', shortName: 'noh' },
    { name: 'yank', shortName: 'y' },
    { name: 'delmarks', shortName: 'delm' },
    { name: 'registers', shortName: 'reg', excludeFromCommandHistory: true },
    { name: 'vglobal', shortName: 'v' },
    { name: 'delete', shortName: 'd' },
    { name: 'join', shortName: 'j' },
    { name: 'normal', shortName: 'norm' },
    { name: 'global', shortName: 'g' }
];
var langmap = parseLangmap('');
function enterVimMode(cm) {
    cm.setOption('disableInput', true);
    cm.setOption('showCursorWhenSelecting', false);
    CodeMirror.signal(cm, "vim-mode-change", { mode: "normal" });
    cm.on('cursorActivity', onCursorActivity);
    maybeInitVimState(cm);
    CodeMirror.on(cm.getInputField(), 'paste', getOnPasteFn(cm));
}
function leaveVimMode(cm) {
    cm.setOption('disableInput', false);
    cm.off('cursorActivity', onCursorActivity);
    CodeMirror.off(cm.getInputField(), 'paste', getOnPasteFn(cm));
    cm.state.vim = null;
    if (highlightTimeout)
        clearTimeout(highlightTimeout);
}
function getOnPasteFn(cm) {
    var vim = cm.state.vim;
    if (!vim.onPasteFn) {
        vim.onPasteFn = function () {
            if (!vim.insertMode) {
                cm.setCursor(offsetCursor(cm.getCursor(), 0, 1));
                actions.enterInsertMode(cm, {}, vim);
            }
        };
    }
    return vim.onPasteFn;
}
var numberRegex = /[\d]/;
var wordCharTest = [CodeMirror.isWordChar, function (ch) {
        return ch && !CodeMirror.isWordChar(ch) && !/\s/.test(ch);
    }], bigWordCharTest = [function (ch) {
        return /\S/.test(ch);
    }];
var validMarks = ['<', '>'];
var validRegisters = ['-', '"', '.', ':', '_', '/', '+'];
var latinCharRegex = /^\w$/;
var upperCaseChars;
try {
    upperCaseChars = new RegExp("^[\\p{Lu}]$", "u");
}
catch (_) {
    upperCaseChars = /^[A-Z]$/;
}
function isLine(cm, line) {
    return line >= cm.firstLine() && line <= cm.lastLine();
}
function isLowerCase(k) {
    return (/^[a-z]$/).test(k);
}
function isMatchableSymbol(k) {
    return '()[]{}'.indexOf(k) != -1;
}
function isNumber(k) {
    return numberRegex.test(k);
}
function isUpperCase(k) {
    return upperCaseChars.test(k);
}
function isWhiteSpaceString(k) {
    return (/^\s*$/).test(k);
}
function isEndOfSentenceSymbol(k) {
    return '.?!'.indexOf(k) != -1;
}
function inArray(val, arr) {
    for (var i = 0; i < arr.length; i++) {
        if (arr[i] == val) {
            return true;
        }
    }
    return false;
}
var options = {};
function defineOption(name, defaultValue, type, aliases, callback) {
    if (defaultValue === undefined && !callback) {
        throw Error('defaultValue is required unless callback is provided');
    }
    if (!type) {
        type = 'string';
    }
    options[name] = {
        type: type,
        defaultValue: defaultValue,
        callback: callback
    };
    if (aliases) {
        for (var i = 0; i < aliases.length; i++) {
            options[aliases[i]] = options[name];
        }
    }
    if (defaultValue) {
        setOption(name, defaultValue);
    }
}
function setOption(name, value, cm, cfg) {
    var option = options[name];
    cfg = cfg || {};
    var scope = cfg.scope;
    if (!option) {
        return new Error('Unknown option: ' + name);
    }
    if (option.type == 'boolean') {
        if (value && value !== true) {
            return new Error('Invalid argument: ' + name + '=' + value);
        }
        else if (value !== false) {
            value = true;
        }
    }
    if (option.callback) {
        if (scope !== 'local') {
            option.callback(value, undefined);
        }
        if (scope !== 'global' && cm) {
            option.callback(value, cm);
        }
    }
    else {
        if (scope !== 'local') {
            option.value = option.type == 'boolean' ? !!value : value;
        }
        if (scope !== 'global' && cm) {
            cm.state.vim.options[name] = { value: value };
        }
    }
}
function getOption(name, cm, cfg) {
    var option = options[name];
    cfg = cfg || {};
    var scope = cfg.scope;
    if (!option) {
        return new Error('Unknown option: ' + name);
    }
    if (option.callback) {
        var local = cm && option.callback(undefined, cm);
        if (scope !== 'global' && local !== undefined) {
            return local;
        }
        if (scope !== 'local') {
            return option.callback();
        }
        return;
    }
    else {
        var local = (scope !== 'global') && (cm && cm.state.vim.options[name]);
        return (local || (scope !== 'local') && option || {}).value;
    }
}
defineOption('filetype', undefined, 'string', ['ft'], function (name, cm) {
    if (cm === undefined) {
        return;
    }
    if (name === undefined) {
        var mode = cm.getOption('mode');
        return mode == 'null' ? '' : mode;
    }
    else {
        var mode = name == '' ? 'null' : name;
        cm.setOption('mode', mode);
    }
});
defineOption('textwidth', 80, 'number', ['tw'], function (width, cm) {
    if (cm === undefined) {
        return;
    }
    if (width === undefined) {
        var value = cm.getOption('textwidth');
        return value;
    }
    else {
        var column = Math.round(width);
        if (column > 1) {
            cm.setOption('textwidth', column);
        }
    }
});
var createCircularJumpList = function () {
    var size = 100;
    var pointer = -1;
    var head = 0;
    var tail = 0;
    var buffer = new Array(size);
    function add(cm, oldCur, newCur) {
        var current = pointer % size;
        var curMark = buffer[current];
        function useNextSlot(cursor) {
            var next = ++pointer % size;
            var trashMark = buffer[next];
            if (trashMark) {
                trashMark.clear();
            }
            buffer[next] = cm.setBookmark(cursor);
        }
        if (curMark) {
            var markPos = curMark.find();
            if (markPos && !cursorEqual(markPos, oldCur)) {
                useNextSlot(oldCur);
            }
        }
        else {
            useNextSlot(oldCur);
        }
        useNextSlot(newCur);
        head = pointer;
        tail = pointer - size + 1;
        if (tail < 0) {
            tail = 0;
        }
    }
    function move(cm, offset) {
        pointer += offset;
        if (pointer > head) {
            pointer = head;
        }
        else if (pointer < tail) {
            pointer = tail;
        }
        var mark = buffer[(size + pointer) % size];
        if (mark && !mark.find()) {
            var inc = offset > 0 ? 1 : -1;
            var newCur;
            var oldCur = cm.getCursor();
            do {
                pointer += inc;
                mark = buffer[(size + pointer) % size];
                if (mark &&
                    (newCur = mark.find()) &&
                    !cursorEqual(oldCur, newCur)) {
                    break;
                }
            } while (pointer < head && pointer > tail);
        }
        return mark;
    }
    function find(cm, offset) {
        var oldPointer = pointer;
        var mark = move(cm, offset);
        pointer = oldPointer;
        return mark && mark.find();
    }
    return {
        cachedCursor: undefined, //used for # and * jumps
        add: add,
        find: find,
        move: move
    };
};
var createInsertModeChanges = function (c) {
    if (c) {
        return {
            changes: c.changes,
            expectCursorActivityForChange: c.expectCursorActivityForChange
        };
    }
    return {
        changes: [],
        expectCursorActivityForChange: false
    };
};
function MacroModeState() {
    this.latestRegister = undefined;
    this.isPlaying = false;
    this.isRecording = false;
    this.replaySearchQueries = [];
    this.onRecordingDone = undefined;
    this.lastInsertModeChanges = createInsertModeChanges();
}
MacroModeState.prototype = {
    exitMacroRecordMode: function () {
        var macroModeState = vimGlobalState.macroModeState;
        if (macroModeState.onRecordingDone) {
            macroModeState.onRecordingDone(); // close dialog
        }
        macroModeState.onRecordingDone = undefined;
        macroModeState.isRecording = false;
    },
    enterMacroRecordMode: function (cm, registerName) {
        var register = vimGlobalState.registerController.getRegister(registerName);
        if (register) {
            register.clear();
            this.latestRegister = registerName;
            if (cm.openDialog) {
                var template = dom('span', { class: 'cm-vim-message' }, 'recording @' + registerName);
                this.onRecordingDone = cm.openDialog(template, null, { bottom: true });
            }
            this.isRecording = true;
        }
    }
};
function maybeInitVimState(cm) {
    if (!cm.state.vim) {
        cm.state.vim = {
            inputState: new InputState(),
            lastEditInputState: undefined,
            lastEditActionCommand: undefined,
            lastHPos: -1,
            lastHSPos: -1,
            lastMotion: null,
            marks: {},
            insertMode: false,
            insertModeReturn: false,
            insertModeRepeat: undefined,
            visualMode: false,
            visualLine: false,
            visualBlock: false,
            lastSelection: null,
            lastPastedText: null,
            sel: {},
            options: {},
            expectLiteralNext: false
        };
    }
    return cm.state.vim;
}
var vimGlobalState;
function resetVimGlobalState() {
    vimGlobalState = {
        searchQuery: null,
        searchIsReversed: false,
        lastSubstituteReplacePart: undefined,
        jumpList: createCircularJumpList(),
        macroModeState: new MacroModeState,
        lastCharacterSearch: { increment: 0, forward: true, selectedCharacter: '' },
        registerController: new RegisterController({}),
        searchHistoryController: new HistoryController(),
        exCommandHistoryController: new HistoryController()
    };
    for (var optionName in options) {
        var option = options[optionName];
        option.value = option.defaultValue;
    }
}
var lastInsertModeKeyTimer;
var vimApi = {
    enterVimMode: enterVimMode,
    leaveVimMode: leaveVimMode,
    buildKeyMap: function () {
    },
    getRegisterController: function () {
        return vimGlobalState.registerController;
    },
    resetVimGlobalState_: resetVimGlobalState,
    getVimGlobalState_: function () {
        return vimGlobalState;
    },
    maybeInitVimState_: maybeInitVimState,
    suppressErrorLogging: false,
    InsertModeKey: InsertModeKey,
    map: function (lhs, rhs, ctx) {
        exCommandDispatcher.map(lhs, rhs, ctx);
    },
    unmap: function (lhs, ctx) {
        return exCommandDispatcher.unmap(lhs, ctx);
    },
    noremap: function (lhs, rhs, ctx) {
        exCommandDispatcher.map(lhs, rhs, ctx, true);
    },
    mapclear: function (ctx) {
        var actualLength = defaultKeymap.length, origLength = defaultKeymapLength;
        var userKeymap = defaultKeymap.slice(0, actualLength - origLength);
        defaultKeymap = defaultKeymap.slice(actualLength - origLength);
        if (ctx) {
            for (var i = userKeymap.length - 1; i >= 0; i--) {
                var mapping = userKeymap[i];
                if (ctx !== mapping.context) {
                    if (mapping.context) {
                        this._mapCommand(mapping);
                    }
                    else {
                        var contexts = ['normal', 'insert', 'visual'];
                        for (var j in contexts) {
                            if (contexts[j] !== ctx) {
                                var newMapping = {};
                                for (var key in mapping) {
                                    newMapping[key] = mapping[key];
                                }
                                newMapping.context = contexts[j];
                                this._mapCommand(newMapping);
                            }
                        }
                    }
                }
            }
        }
    },
    langmap: updateLangmap,
    vimKeyFromEvent: vimKeyFromEvent,
    setOption: setOption,
    getOption: getOption,
    defineOption: defineOption,
    defineEx: function (name, prefix, func) {
        if (!prefix) {
            prefix = name;
        }
        else if (name.indexOf(prefix) !== 0) {
            throw new Error('(Vim.defineEx) "' + prefix + '" is not a prefix of "' + name + '", command not registered');
        }
        exCommands[name] = func;
        exCommandDispatcher.commandMap_[prefix] = { name: name, shortName: prefix, type: 'api' };
    },
    handleKey: function (cm, key, origin) {
        var command = this.findKey(cm, key, origin);
        if (typeof command === 'function') {
            return command();
        }
    },
    multiSelectHandleKey: multiSelectHandleKey,
    findKey: function (cm, key, origin) {
        var vim = maybeInitVimState(cm);
        function handleMacroRecording() {
            var macroModeState = vimGlobalState.macroModeState;
            if (macroModeState.isRecording) {
                if (key == 'q') {
                    macroModeState.exitMacroRecordMode();
                    clearInputState(cm);
                    return true;
                }
                if (origin != 'mapping') {
                    logKey(macroModeState, key);
                }
            }
        }
        function handleEsc() {
            if (key == '<Esc>') {
                if (vim.visualMode) {
                    exitVisualMode(cm);
                }
                else if (vim.insertMode) {
                    exitInsertMode(cm);
                }
                else {
                    return;
                }
                clearInputState(cm);
                return true;
            }
        }
        function handleKeyInsertMode() {
            if (handleEsc()) {
                return true;
            }
            vim.inputState.keyBuffer.push(key);
            var keys = vim.inputState.keyBuffer.join("");
            var keysAreChars = key.length == 1;
            var match = commandDispatcher.matchCommand(keys, defaultKeymap, vim.inputState, 'insert');
            var changeQueue = vim.inputState.changeQueue;
            if (match.type == 'none') {
                clearInputState(cm);
                return false;
            }
            else if (match.type == 'partial') {
                if (match.expectLiteralNext)
                    vim.expectLiteralNext = true;
                if (lastInsertModeKeyTimer) {
                    window.clearTimeout(lastInsertModeKeyTimer);
                }
                lastInsertModeKeyTimer = keysAreChars && window.setTimeout(function () { if (vim.insertMode && vim.inputState.keyBuffer.length) {
                    clearInputState(cm);
                } }, getOption('insertModeEscKeysTimeout'));
                if (keysAreChars) {
                    var selections = cm.listSelections();
                    if (!changeQueue || changeQueue.removed.length != selections.length)
                        changeQueue = vim.inputState.changeQueue = new ChangeQueue;
                    changeQueue.inserted += key;
                    for (var i = 0; i < selections.length; i++) {
                        var from = cursorMin(selections[i].anchor, selections[i].head);
                        var to = cursorMax(selections[i].anchor, selections[i].head);
                        var text = cm.getRange(from, cm.state.overwrite ? offsetCursor(to, 0, 1) : to);
                        changeQueue.removed[i] = (changeQueue.removed[i] || "") + text;
                    }
                }
                return !keysAreChars;
            }
            vim.expectLiteralNext = false;
            if (lastInsertModeKeyTimer) {
                window.clearTimeout(lastInsertModeKeyTimer);
            }
            if (match.command && changeQueue) {
                var selections = cm.listSelections();
                for (var i = 0; i < selections.length; i++) {
                    var here = selections[i].head;
                    cm.replaceRange(changeQueue.removed[i] || "", offsetCursor(here, 0, -changeQueue.inserted.length), here, '+input');
                }
                vimGlobalState.macroModeState.lastInsertModeChanges.changes.pop();
            }
            if (!match.command)
                clearInputState(cm);
            return match.command;
        }
        function handleKeyNonInsertMode() {
            if (handleMacroRecording() || handleEsc()) {
                return true;
            }
            vim.inputState.keyBuffer.push(key);
            var keys = vim.inputState.keyBuffer.join("");
            if (/^[1-9]\d*$/.test(keys)) {
                return true;
            }
            var keysMatcher = /^(\d*)(.*)$/.exec(keys);
            if (!keysMatcher) {
                clearInputState(cm);
                return false;
            }
            var context = vim.visualMode ? 'visual' :
                'normal';
            var mainKey = keysMatcher[2] || keysMatcher[1];
            if (vim.inputState.operatorShortcut && vim.inputState.operatorShortcut.slice(-1) == mainKey) {
                mainKey = vim.inputState.operatorShortcut;
            }
            var match = commandDispatcher.matchCommand(mainKey, defaultKeymap, vim.inputState, context);
            if (match.type == 'none') {
                clearInputState(cm);
                return false;
            }
            else if (match.type == 'partial') {
                if (match.expectLiteralNext)
                    vim.expectLiteralNext = true;
                return true;
            }
            else if (match.type == 'clear') {
                clearInputState(cm);
                return true;
            }
            vim.expectLiteralNext = false;
            vim.inputState.keyBuffer.length = 0;
            keysMatcher = /^(\d*)(.*)$/.exec(keys);
            if (keysMatcher[1] && keysMatcher[1] != '0') {
                vim.inputState.pushRepeatDigit(keysMatcher[1]);
            }
            return match.command;
        }
        var command;
        if (vim.insertMode) {
            command = handleKeyInsertMode();
        }
        else {
            command = handleKeyNonInsertMode();
        }
        if (command === false) {
            return !vim.insertMode && key.length === 1 ? function () { return true; } : undefined;
        }
        else if (command === true) {
            return function () { return true; };
        }
        else {
            return function () {
                if ((command.operator || command.isEdit) && cm.getOption('readOnly'))
                    return; // ace_patch
                return cm.operation(function () {
                    cm.curOp.isVimOp = true;
                    try {
                        if (command.type == 'keyToKey') {
                            doKeyToKey(cm, command.toKeys, command);
                        }
                        else {
                            commandDispatcher.processCommand(cm, vim, command);
                        }
                    }
                    catch (e) {
                        cm.state.vim = undefined;
                        maybeInitVimState(cm);
                        if (!vimApi.suppressErrorLogging) {
                            console['log'](e);
                        }
                        throw e;
                    }
                    return true;
                });
            };
        }
    },
    handleEx: function (cm, input) {
        exCommandDispatcher.processCommand(cm, input);
    },
    defineMotion: defineMotion,
    defineAction: defineAction,
    defineOperator: defineOperator,
    mapCommand: mapCommand,
    _mapCommand: _mapCommand,
    defineRegister: defineRegister,
    exitVisualMode: exitVisualMode,
    exitInsertMode: exitInsertMode
};
var keyToKeyStack = [];
var noremap = false;
var virtualPrompt;
function sendKeyToPrompt(key) {
    if (key[0] == "<") {
        var lowerKey = key.toLowerCase().slice(1, -1);
        var parts = lowerKey.split('-');
        lowerKey = parts.pop() || '';
        if (lowerKey == 'lt')
            key = '<';
        else if (lowerKey == 'space')
            key = ' ';
        else if (lowerKey == 'cr')
            key = '\n';
        else if (vimToCmKeyMap[lowerKey]) {
            var value = virtualPrompt.value;
            var event = {
                key: vimToCmKeyMap[lowerKey],
                target: {
                    value: value,
                    selectionEnd: value.length,
                    selectionStart: value.length
                }
            };
            if (virtualPrompt.onKeyDown) {
                virtualPrompt.onKeyDown(event, virtualPrompt.value, close);
            }
            if (virtualPrompt && virtualPrompt.onKeyUp) {
                virtualPrompt.onKeyUp(event, virtualPrompt.value, close);
            }
            return;
        }
    }
    if (key == '\n') {
        var prompt = virtualPrompt;
        virtualPrompt = null;
        prompt.onClose && prompt.onClose(prompt.value);
    }
    else {
        virtualPrompt.value = (virtualPrompt.value || '') + key;
    }
    function close(value) {
        if (typeof value == 'string') {
            virtualPrompt.value = value;
        }
        else {
            virtualPrompt = null;
        }
    }
}
function doKeyToKey(cm, keys, fromKey) {
    var noremapBefore = noremap;
    if (fromKey) {
        if (keyToKeyStack.indexOf(fromKey) != -1)
            return;
        keyToKeyStack.push(fromKey);
        noremap = fromKey.noremap != false;
    }
    try {
        var vim = maybeInitVimState(cm);
        var keyRe = /<(?:[CSMA]-)*\w+>|./gi;
        var match;
        while ((match = keyRe.exec(keys))) {
            var key = match[0];
            var wasInsert = vim.insertMode;
            if (virtualPrompt) {
                sendKeyToPrompt(key);
                continue;
            }
            var result = vimApi.handleKey(cm, key, 'mapping');
            if (!result && wasInsert && vim.insertMode) {
                if (key[0] == "<") {
                    var lowerKey = key.toLowerCase().slice(1, -1);
                    var parts = lowerKey.split('-');
                    lowerKey = parts.pop() || '';
                    if (lowerKey == 'lt')
                        key = '<';
                    else if (lowerKey == 'space')
                        key = ' ';
                    else if (lowerKey == 'cr')
                        key = '\n';
                    else if (vimToCmKeyMap.hasOwnProperty(lowerKey)) {
                        key = vimToCmKeyMap[lowerKey];
                        sendCmKey(cm, key);
                        continue;
                    }
                    else {
                        key = key[0];
                        keyRe.lastIndex = match.index + 1;
                    }
                }
                cm.replaceSelection(key);
            }
        }
    }
    finally {
        keyToKeyStack.pop();
        noremap = keyToKeyStack.length ? noremapBefore : false;
        if (!keyToKeyStack.length && virtualPrompt) {
            var promptOptions = virtualPrompt;
            virtualPrompt = null;
            showPrompt(cm, promptOptions);
        }
    }
}
var specialKey = {
    Return: 'CR', Backspace: 'BS', 'Delete': 'Del', Escape: 'Esc', Insert: 'Ins',
    ArrowLeft: 'Left', ArrowRight: 'Right', ArrowUp: 'Up', ArrowDown: 'Down',
    Enter: 'CR', ' ': 'Space'
};
var ignoredKeys = { Shift: 1, Alt: 1, Command: 1, Control: 1,
    CapsLock: 1, AltGraph: 1, Dead: 1, Unidentified: 1 };
var vimToCmKeyMap = {};
'Left|Right|Up|Down|End|Home'.split('|').concat(Object.keys(specialKey)).forEach(function (x) {
    vimToCmKeyMap[(specialKey[x] || '').toLowerCase()]
        = vimToCmKeyMap[x.toLowerCase()] = x;
});
function vimKeyFromEvent(e, vim) {
    var key = e.key;
    if (ignoredKeys[key])
        return;
    if (key.length > 1 && key[0] == "n") {
        key = key.replace("Numpad", "");
    }
    key = specialKey[key] || key;
    var name = '';
    if (e.ctrlKey) {
        name += 'C-';
    }
    if (e.altKey) {
        name += 'A-';
    }
    if (e.metaKey) {
        name += 'M-';
    }
    if (CodeMirror.isMac && e.altKey && !e.metaKey && !e.ctrlKey) {
        name = name.slice(2);
    }
    if ((name || key.length > 1) && e.shiftKey) {
        name += 'S-';
    }
    if (vim && !vim.expectLiteralNext && key.length == 1) {
        if (langmap.keymap && key in langmap.keymap) {
            if (langmap.remapCtrl != false || !name)
                key = langmap.keymap[key];
        }
        else if (key.charCodeAt(0) > 255) {
            var code = e.code && e.code.slice(-1) || "";
            if (!e.shiftKey)
                code = code.toLowerCase();
            if (code)
                key = code;
        }
    }
    name += key;
    if (name.length > 1) {
        name = '<' + name + '>';
    }
    return name;
}
;
function updateLangmap(langmapString, remapCtrl) {
    if (langmap.string !== langmapString) {
        langmap = parseLangmap(langmapString);
    }
    langmap.remapCtrl = remapCtrl;
}
function parseLangmap(langmapString) {
    var keymap = {};
    if (!langmapString)
        return { keymap: keymap, string: '' };
    function getEscaped(list) {
        return list.split(/\\?(.)/).filter(Boolean);
    }
    langmapString.split(/((?:[^\\,]|\\.)+),/).map(function (part) {
        if (!part)
            return;
        var semicolon = part.split(/((?:[^\\;]|\\.)+);/);
        if (semicolon.length == 3) {
            var from = getEscaped(semicolon[1]);
            var to = getEscaped(semicolon[2]);
            if (from.length !== to.length)
                return; // skip over malformed part
            for (var i = 0; i < from.length; ++i)
                keymap[from[i]] = to[i];
        }
        else if (semicolon.length == 1) {
            var pairs = getEscaped(part);
            if (pairs.length % 2 !== 0)
                return; // skip over malformed part
            for (var i = 0; i < pairs.length; i += 2)
                keymap[pairs[i]] = pairs[i + 1];
        }
    });
    return { keymap: keymap, string: langmapString };
}
defineOption('langmap', undefined, 'string', ['lmap'], function (name, cm) {
    if (name === undefined) {
        return langmap.string;
    }
    else {
        updateLangmap(name);
    }
});
function InputState() {
    this.prefixRepeat = [];
    this.motionRepeat = [];
    this.operator = null;
    this.operatorArgs = null;
    this.motion = null;
    this.motionArgs = null;
    this.keyBuffer = []; // For matching multi-key commands.
    this.registerName = null; // Defaults to the unnamed register.
    this.changeQueue = null; // For restoring text used by insert mode keybindings
}
InputState.prototype.pushRepeatDigit = function (n) {
    if (!this.operator) {
        this.prefixRepeat = this.prefixRepeat.concat(n);
    }
    else {
        this.motionRepeat = this.motionRepeat.concat(n);
    }
};
InputState.prototype.getRepeat = function () {
    var repeat = 0;
    if (this.prefixRepeat.length > 0 || this.motionRepeat.length > 0) {
        repeat = 1;
        if (this.prefixRepeat.length > 0) {
            repeat *= parseInt(this.prefixRepeat.join(''), 10);
        }
        if (this.motionRepeat.length > 0) {
            repeat *= parseInt(this.motionRepeat.join(''), 10);
        }
    }
    return repeat;
};
function clearInputState(cm, reason) {
    cm.state.vim.inputState = new InputState();
    cm.state.vim.expectLiteralNext = false;
    CodeMirror.signal(cm, 'vim-command-done', reason);
}
function ChangeQueue() {
    this.removed = [];
    this.inserted = "";
}
function Register(text, linewise, blockwise) {
    this.clear();
    this.keyBuffer = [text || ''];
    this.insertModeChanges = [];
    this.searchQueries = [];
    this.linewise = !!linewise;
    this.blockwise = !!blockwise;
}
Register.prototype = {
    setText: function (text, linewise, blockwise) {
        this.keyBuffer = [text || ''];
        this.linewise = !!linewise;
        this.blockwise = !!blockwise;
    },
    pushText: function (text, linewise) {
        if (linewise) {
            if (!this.linewise) {
                this.keyBuffer.push('\n');
            }
            this.linewise = true;
        }
        this.keyBuffer.push(text);
    },
    pushInsertModeChanges: function (changes) {
        this.insertModeChanges.push(createInsertModeChanges(changes));
    },
    pushSearchQuery: function (query) {
        this.searchQueries.push(query);
    },
    clear: function () {
        this.keyBuffer = [];
        this.insertModeChanges = [];
        this.searchQueries = [];
        this.linewise = false;
    },
    toString: function () {
        return this.keyBuffer.join('');
    }
};
function defineRegister(name, register) {
    var registers = vimGlobalState.registerController.registers;
    if (!name || name.length != 1) {
        throw Error('Register name must be 1 character');
    }
    registers[name] = register;
    validRegisters.push(name);
}
function RegisterController(registers) {
    this.registers = registers;
    this.unnamedRegister = registers['"'] = new Register();
    registers['.'] = new Register();
    registers[':'] = new Register();
    registers['/'] = new Register();
    registers['+'] = new Register();
}
RegisterController.prototype = {
    pushText: function (registerName, operator, text, linewise, blockwise) {
        if (registerName === '_')
            return;
        if (linewise && text.charAt(text.length - 1) !== '\n') {
            text += '\n';
        }
        var register = this.isValidRegister(registerName) ?
            this.getRegister(registerName) : null;
        if (!register) {
            switch (operator) {
                case 'yank':
                    this.registers['0'] = new Register(text, linewise, blockwise);
                    break;
                case 'delete':
                case 'change':
                    if (text.indexOf('\n') == -1) {
                        this.registers['-'] = new Register(text, linewise);
                    }
                    else {
                        this.shiftNumericRegisters_();
                        this.registers['1'] = new Register(text, linewise);
                    }
                    break;
            }
            this.unnamedRegister.setText(text, linewise, blockwise);
            return;
        }
        var append = isUpperCase(registerName);
        if (append) {
            register.pushText(text, linewise);
        }
        else {
            register.setText(text, linewise, blockwise);
        }
        if (registerName === '+' && typeof navigator !== 'undefined' &&
            typeof navigator.clipboard !== 'undefined' &&
            typeof navigator.clipboard.readText === 'function') {
            navigator.clipboard.writeText(text);
        }
        this.unnamedRegister.setText(register.toString(), linewise);
    },
    getRegister: function (name) {
        if (!this.isValidRegister(name)) {
            return this.unnamedRegister;
        }
        name = name.toLowerCase();
        if (!this.registers[name]) {
            this.registers[name] = new Register();
        }
        return this.registers[name];
    },
    isValidRegister: function (name) {
        return name && (inArray(name, validRegisters) || latinCharRegex.test(name));
    },
    shiftNumericRegisters_: function () {
        for (var i = 9; i >= 2; i--) {
            this.registers[i] = this.getRegister('' + (i - 1));
        }
    }
};
function HistoryController() {
    this.historyBuffer = [];
    this.iterator = 0;
    this.initialPrefix = null;
}
HistoryController.prototype = {
    nextMatch: function (input, up) {
        var historyBuffer = this.historyBuffer;
        var dir = up ? -1 : 1;
        if (this.initialPrefix === null)
            this.initialPrefix = input;
        for (var i = this.iterator + dir; up ? i >= 0 : i < historyBuffer.length; i += dir) {
            var element = historyBuffer[i];
            for (var j = 0; j <= element.length; j++) {
                if (this.initialPrefix == element.substring(0, j)) {
                    this.iterator = i;
                    return element;
                }
            }
        }
        if (i >= historyBuffer.length) {
            this.iterator = historyBuffer.length;
            return this.initialPrefix;
        }
        if (i < 0)
            return input;
    },
    pushInput: function (input) {
        var index = this.historyBuffer.indexOf(input);
        if (index > -1)
            this.historyBuffer.splice(index, 1);
        if (input.length)
            this.historyBuffer.push(input);
    },
    reset: function () {
        this.initialPrefix = null;
        this.iterator = this.historyBuffer.length;
    }
};
var commandDispatcher = {
    matchCommand: function (keys, keyMap, inputState, context) {
        var matches = commandMatches(keys, keyMap, context, inputState);
        if (!matches.full && !matches.partial) {
            return { type: 'none' };
        }
        else if (!matches.full && matches.partial) {
            return {
                type: 'partial',
                expectLiteralNext: matches.partial.length == 1 && matches.partial[0].keys.slice(-11) == '<character>' // langmap literal logic
            };
        }
        var bestMatch;
        for (var i = 0; i < matches.full.length; i++) {
            var match = matches.full[i];
            if (!bestMatch) {
                bestMatch = match;
            }
        }
        if (bestMatch.keys.slice(-11) == '<character>' || bestMatch.keys.slice(-10) == '<register>') {
            var character = lastChar(keys);
            if (!character || character.length > 1)
                return { type: 'clear' };
            inputState.selectedCharacter = character;
        }
        return { type: 'full', command: bestMatch };
    },
    processCommand: function (cm, vim, command) {
        vim.inputState.repeatOverride = command.repeatOverride;
        switch (command.type) {
            case 'motion':
                this.processMotion(cm, vim, command);
                break;
            case 'operator':
                this.processOperator(cm, vim, command);
                break;
            case 'operatorMotion':
                this.processOperatorMotion(cm, vim, command);
                break;
            case 'action':
                this.processAction(cm, vim, command);
                break;
            case 'search':
                this.processSearch(cm, vim, command);
                break;
            case 'ex':
            case 'keyToEx':
                this.processEx(cm, vim, command);
                break;
            default:
                break;
        }
    },
    processMotion: function (cm, vim, command) {
        vim.inputState.motion = command.motion;
        vim.inputState.motionArgs = copyArgs(command.motionArgs);
        this.evalInput(cm, vim);
    },
    processOperator: function (cm, vim, command) {
        var inputState = vim.inputState;
        if (inputState.operator) {
            if (inputState.operator == command.operator) {
                inputState.motion = 'expandToLine';
                inputState.motionArgs = { linewise: true };
                this.evalInput(cm, vim);
                return;
            }
            else {
                clearInputState(cm);
            }
        }
        inputState.operator = command.operator;
        inputState.operatorArgs = copyArgs(command.operatorArgs);
        if (command.keys.length > 1) {
            inputState.operatorShortcut = command.keys;
        }
        if (command.exitVisualBlock) {
            vim.visualBlock = false;
            updateCmSelection(cm);
        }
        if (vim.visualMode) {
            this.evalInput(cm, vim);
        }
    },
    processOperatorMotion: function (cm, vim, command) {
        var visualMode = vim.visualMode;
        var operatorMotionArgs = copyArgs(command.operatorMotionArgs);
        if (operatorMotionArgs) {
            if (visualMode && operatorMotionArgs.visualLine) {
                vim.visualLine = true;
            }
        }
        this.processOperator(cm, vim, command);
        if (!visualMode) {
            this.processMotion(cm, vim, command);
        }
    },
    processAction: function (cm, vim, command) {
        var inputState = vim.inputState;
        var repeat = inputState.getRepeat();
        var repeatIsExplicit = !!repeat;
        var actionArgs = copyArgs(command.actionArgs) || {};
        if (inputState.selectedCharacter) {
            actionArgs.selectedCharacter = inputState.selectedCharacter;
        }
        if (command.operator) {
            this.processOperator(cm, vim, command);
        }
        if (command.motion) {
            this.processMotion(cm, vim, command);
        }
        if (command.motion || command.operator) {
            this.evalInput(cm, vim);
        }
        actionArgs.repeat = repeat || 1;
        actionArgs.repeatIsExplicit = repeatIsExplicit;
        actionArgs.registerName = inputState.registerName;
        clearInputState(cm);
        vim.lastMotion = null;
        if (command.isEdit) {
            this.recordLastEdit(vim, inputState, command);
        }
        actions[command.action](cm, actionArgs, vim);
    },
    processSearch: function (cm, vim, command) {
        if (!cm.getSearchCursor) {
            return;
        }
        var forward = command.searchArgs.forward;
        var wholeWordOnly = command.searchArgs.wholeWordOnly;
        getSearchState(cm).setReversed(!forward);
        var promptPrefix = (forward) ? '/' : '?';
        var originalQuery = getSearchState(cm).getQuery();
        var originalScrollPos = cm.getScrollInfo();
        function handleQuery(query, ignoreCase, smartCase) {
            vimGlobalState.searchHistoryController.pushInput(query);
            vimGlobalState.searchHistoryController.reset();
            try {
                updateSearchQuery(cm, query, ignoreCase, smartCase);
            }
            catch (e) {
                showConfirm(cm, 'Invalid regex: ' + query);
                clearInputState(cm);
                return;
            }
            commandDispatcher.processMotion(cm, vim, {
                type: 'motion',
                motion: 'findNext',
                motionArgs: { forward: true, toJumplist: command.searchArgs.toJumplist }
            });
        }
        function onPromptClose(query) {
            handleQuery(query, true /** ignoreCase */, true /** smartCase */);
            var macroModeState = vimGlobalState.macroModeState;
            if (macroModeState.isRecording) {
                logSearchQuery(macroModeState, query);
            }
        }
        function onPromptKeyUp(e, query, close) {
            var keyName = vimKeyFromEvent(e), up, offset;
            if (keyName == '<Up>' || keyName == '<Down>') {
                up = keyName == '<Up>' ? true : false;
                offset = e.target ? e.target.selectionEnd : 0;
                query = vimGlobalState.searchHistoryController.nextMatch(query, up) || '';
                close(query);
                if (offset && e.target)
                    e.target.selectionEnd = e.target.selectionStart = Math.min(offset, e.target.value.length);
            }
            else if (keyName && keyName != '<Left>' && keyName != '<Right>') {
                vimGlobalState.searchHistoryController.reset();
            }
            var parsedQuery;
            try {
                parsedQuery = updateSearchQuery(cm, query, true /** ignoreCase */, true /** smartCase */);
            }
            catch (e) {
            }
            if (parsedQuery) {
                cm.scrollIntoView(findNext(cm, !forward, parsedQuery), 30);
            }
            else {
                clearSearchHighlight(cm);
                cm.scrollTo(originalScrollPos.left, originalScrollPos.top);
            }
        }
        function onPromptKeyDown(e, query, close) {
            var keyName = vimKeyFromEvent(e);
            if (keyName == '<Esc>' || keyName == '<C-c>' || keyName == '<C-[>' ||
                (keyName == '<BS>' && query == '')) {
                vimGlobalState.searchHistoryController.pushInput(query);
                vimGlobalState.searchHistoryController.reset();
                updateSearchQuery(cm, originalQuery);
                clearSearchHighlight(cm);
                cm.scrollTo(originalScrollPos.left, originalScrollPos.top);
                CodeMirror.e_stop(e);
                clearInputState(cm);
                close();
                cm.focus();
            }
            else if (keyName == '<Up>' || keyName == '<Down>') {
                CodeMirror.e_stop(e);
            }
            else if (keyName == '<C-u>') {
                CodeMirror.e_stop(e);
                close('');
            }
        }
        switch (command.searchArgs.querySrc) {
            case 'prompt':
                var macroModeState = vimGlobalState.macroModeState;
                if (macroModeState.isPlaying) {
                    var query = macroModeState.replaySearchQueries.shift();
                    handleQuery(query, true /** ignoreCase */, false /** smartCase */);
                }
                else {
                    showPrompt(cm, {
                        onClose: onPromptClose,
                        prefix: promptPrefix,
                        desc: '(JavaScript regexp)',
                        onKeyUp: onPromptKeyUp,
                        onKeyDown: onPromptKeyDown
                    });
                }
                break;
            case 'wordUnderCursor':
                var word = expandWordUnderCursor(cm, { noSymbol: true });
                var isKeyword = true;
                if (!word) {
                    word = expandWordUnderCursor(cm, { noSymbol: false });
                    isKeyword = false;
                }
                if (!word) {
                    showConfirm(cm, 'No word under cursor');
                    clearInputState(cm);
                    return;
                }
                var query = cm.getLine(word.start.line).substring(word.start.ch, word.end.ch);
                if (isKeyword && wholeWordOnly) {
                    query = '\\b' + query + '\\b';
                }
                else {
                    query = escapeRegex(query);
                }
                vimGlobalState.jumpList.cachedCursor = cm.getCursor();
                cm.setCursor(word.start);
                handleQuery(query, true /** ignoreCase */, false /** smartCase */);
                break;
        }
    },
    processEx: function (cm, vim, command) {
        function onPromptClose(input) {
            vimGlobalState.exCommandHistoryController.pushInput(input);
            vimGlobalState.exCommandHistoryController.reset();
            exCommandDispatcher.processCommand(cm, input);
            if (cm.state.vim)
                clearInputState(cm);
        }
        function onPromptKeyDown(e, input, close) {
            var keyName = vimKeyFromEvent(e), up, offset;
            if (keyName == '<Esc>' || keyName == '<C-c>' || keyName == '<C-[>' ||
                (keyName == '<BS>' && input == '')) {
                vimGlobalState.exCommandHistoryController.pushInput(input);
                vimGlobalState.exCommandHistoryController.reset();
                CodeMirror.e_stop(e);
                clearInputState(cm);
                close();
                cm.focus();
            }
            if (keyName == '<Up>' || keyName == '<Down>') {
                CodeMirror.e_stop(e);
                up = keyName == '<Up>' ? true : false;
                offset = e.target ? e.target.selectionEnd : 0;
                input = vimGlobalState.exCommandHistoryController.nextMatch(input, up) || '';
                close(input);
                if (offset && e.target)
                    e.target.selectionEnd = e.target.selectionStart = Math.min(offset, e.target.value.length);
            }
            else if (keyName == '<C-u>') {
                CodeMirror.e_stop(e);
                close('');
            }
            else if (keyName && keyName != '<Left>' && keyName != '<Right>') {
                vimGlobalState.exCommandHistoryController.reset();
            }
        }
        if (command.type == 'keyToEx') {
            exCommandDispatcher.processCommand(cm, command.exArgs.input);
        }
        else {
            if (vim.visualMode) {
                showPrompt(cm, { onClose: onPromptClose, prefix: ':', value: '\'<,\'>',
                    onKeyDown: onPromptKeyDown, selectValueOnOpen: false });
            }
            else {
                showPrompt(cm, { onClose: onPromptClose, prefix: ':',
                    onKeyDown: onPromptKeyDown });
            }
        }
    },
    evalInput: function (cm, vim) {
        var inputState = vim.inputState;
        var motion = inputState.motion;
        var motionArgs = inputState.motionArgs || {};
        var operator = inputState.operator;
        var operatorArgs = inputState.operatorArgs || {};
        var registerName = inputState.registerName;
        var sel = vim.sel;
        var origHead = copyCursor(vim.visualMode ? clipCursorToContent(cm, sel.head) : cm.getCursor('head'));
        var origAnchor = copyCursor(vim.visualMode ? clipCursorToContent(cm, sel.anchor) : cm.getCursor('anchor'));
        var oldHead = copyCursor(origHead);
        var oldAnchor = copyCursor(origAnchor);
        var newHead, newAnchor;
        var repeat;
        if (operator) {
            this.recordLastEdit(vim, inputState);
        }
        if (inputState.repeatOverride !== undefined) {
            repeat = inputState.repeatOverride;
        }
        else {
            repeat = inputState.getRepeat();
        }
        if (repeat > 0 && motionArgs.explicitRepeat) {
            motionArgs.repeatIsExplicit = true;
        }
        else if (motionArgs.noRepeat ||
            (!motionArgs.explicitRepeat && repeat === 0)) {
            repeat = 1;
            motionArgs.repeatIsExplicit = false;
        }
        if (inputState.selectedCharacter) {
            motionArgs.selectedCharacter = operatorArgs.selectedCharacter =
                inputState.selectedCharacter;
        }
        motionArgs.repeat = repeat;
        clearInputState(cm);
        if (motion) {
            var motionResult = motions[motion](cm, origHead, motionArgs, vim, inputState);
            vim.lastMotion = motions[motion];
            if (!motionResult) {
                return;
            }
            if (motionArgs.toJumplist) {
                if (!operator && cm.ace.curOp != null)
                    cm.ace.curOp.command.scrollIntoView = "center-animate"; // ace_patch
                var jumpList = vimGlobalState.jumpList;
                var cachedCursor = jumpList.cachedCursor;
                if (cachedCursor) {
                    recordJumpPosition(cm, cachedCursor, motionResult);
                    delete jumpList.cachedCursor;
                }
                else {
                    recordJumpPosition(cm, origHead, motionResult);
                }
            }
            if (motionResult instanceof Array) {
                newAnchor = motionResult[0];
                newHead = motionResult[1];
            }
            else {
                newHead = motionResult;
            }
            if (!newHead) {
                newHead = copyCursor(origHead);
            }
            if (vim.visualMode) {
                if (!(vim.visualBlock && newHead.ch === Infinity)) {
                    newHead = clipCursorToContent(cm, newHead, oldHead);
                }
                if (newAnchor) {
                    newAnchor = clipCursorToContent(cm, newAnchor);
                }
                newAnchor = newAnchor || oldAnchor;
                sel.anchor = newAnchor;
                sel.head = newHead;
                updateCmSelection(cm);
                updateMark(cm, vim, '<', cursorIsBefore(newAnchor, newHead) ? newAnchor
                    : newHead);
                updateMark(cm, vim, '>', cursorIsBefore(newAnchor, newHead) ? newHead
                    : newAnchor);
            }
            else if (!operator) {
                if (cm.ace.curOp)
                    cm.ace.curOp.vimDialogScroll = "center-animate"; // ace_patch
                newHead = clipCursorToContent(cm, newHead, oldHead);
                cm.setCursor(newHead.line, newHead.ch);
            }
        }
        if (operator) {
            if (operatorArgs.lastSel) {
                newAnchor = oldAnchor;
                var lastSel = operatorArgs.lastSel;
                var lineOffset = Math.abs(lastSel.head.line - lastSel.anchor.line);
                var chOffset = Math.abs(lastSel.head.ch - lastSel.anchor.ch);
                if (lastSel.visualLine) {
                    newHead = new Pos(oldAnchor.line + lineOffset, oldAnchor.ch);
                }
                else if (lastSel.visualBlock) {
                    newHead = new Pos(oldAnchor.line + lineOffset, oldAnchor.ch + chOffset);
                }
                else if (lastSel.head.line == lastSel.anchor.line) {
                    newHead = new Pos(oldAnchor.line, oldAnchor.ch + chOffset);
                }
                else {
                    newHead = new Pos(oldAnchor.line + lineOffset, oldAnchor.ch);
                }
                vim.visualMode = true;
                vim.visualLine = lastSel.visualLine;
                vim.visualBlock = lastSel.visualBlock;
                sel = vim.sel = {
                    anchor: newAnchor,
                    head: newHead
                };
                updateCmSelection(cm);
            }
            else if (vim.visualMode) {
                operatorArgs.lastSel = {
                    anchor: copyCursor(sel.anchor),
                    head: copyCursor(sel.head),
                    visualBlock: vim.visualBlock,
                    visualLine: vim.visualLine
                };
            }
            var curStart, curEnd, linewise, mode;
            var cmSel;
            if (vim.visualMode) {
                curStart = cursorMin(sel.head, sel.anchor);
                curEnd = cursorMax(sel.head, sel.anchor);
                linewise = vim.visualLine || operatorArgs.linewise;
                mode = vim.visualBlock ? 'block' :
                    linewise ? 'line' :
                        'char';
                var newPositions = updateSelectionForSurrogateCharacters(cm, curStart, curEnd);
                cmSel = makeCmSelection(cm, {
                    anchor: newPositions.start,
                    head: newPositions.end
                }, mode);
                if (linewise) {
                    var ranges = cmSel.ranges;
                    if (mode == 'block') {
                        for (var i = 0; i < ranges.length; i++) {
                            ranges[i].head.ch = lineLength(cm, ranges[i].head.line);
                        }
                    }
                    else if (mode == 'line') {
                        ranges[0].head = new Pos(ranges[0].head.line + 1, 0);
                    }
                }
            }
            else {
                curStart = copyCursor(newAnchor || oldAnchor);
                curEnd = copyCursor(newHead || oldHead);
                if (cursorIsBefore(curEnd, curStart)) {
                    var tmp = curStart;
                    curStart = curEnd;
                    curEnd = tmp;
                }
                linewise = motionArgs.linewise || operatorArgs.linewise;
                if (linewise) {
                    expandSelectionToLine(cm, curStart, curEnd);
                }
                else if (motionArgs.forward) {
                    clipToLine(cm, curStart, curEnd);
                }
                mode = 'char';
                var exclusive = !motionArgs.inclusive || linewise;
                var newPositions = updateSelectionForSurrogateCharacters(cm, curStart, curEnd);
                cmSel = makeCmSelection(cm, {
                    anchor: newPositions.start,
                    head: newPositions.end
                }, mode, exclusive);
            }
            cm.setSelections(cmSel.ranges, cmSel.primary);
            vim.lastMotion = null;
            operatorArgs.repeat = repeat; // For indent in visual mode.
            operatorArgs.registerName = registerName;
            operatorArgs.linewise = linewise;
            var operatorMoveTo = operators[operator](cm, operatorArgs, cmSel.ranges, oldAnchor, newHead);
            if (vim.visualMode) {
                exitVisualMode(cm, operatorMoveTo != null);
            }
            if (operatorMoveTo) {
                cm.setCursor(operatorMoveTo);
            }
        }
    },
    recordLastEdit: function (vim, inputState, actionCommand) {
        var macroModeState = vimGlobalState.macroModeState;
        if (macroModeState.isPlaying) {
            return;
        }
        vim.lastEditInputState = inputState;
        vim.lastEditActionCommand = actionCommand;
        macroModeState.lastInsertModeChanges.changes = [];
        macroModeState.lastInsertModeChanges.expectCursorActivityForChange = false;
        macroModeState.lastInsertModeChanges.visualBlock = vim.visualBlock ? vim.sel.head.line - vim.sel.anchor.line : 0;
    }
};
var motions = {
    moveToTopLine: function (cm, _head, motionArgs) {
        var line = getUserVisibleLines(cm).top + motionArgs.repeat - 1;
        return new Pos(line, findFirstNonWhiteSpaceCharacter(cm.getLine(line)));
    },
    moveToMiddleLine: function (cm) {
        var range = getUserVisibleLines(cm);
        var line = Math.floor((range.top + range.bottom) * 0.5);
        return new Pos(line, findFirstNonWhiteSpaceCharacter(cm.getLine(line)));
    },
    moveToBottomLine: function (cm, _head, motionArgs) {
        var line = getUserVisibleLines(cm).bottom - motionArgs.repeat + 1;
        return new Pos(line, findFirstNonWhiteSpaceCharacter(cm.getLine(line)));
    },
    expandToLine: function (_cm, head, motionArgs) {
        var cur = head;
        return new Pos(cur.line + motionArgs.repeat - 1, Infinity);
    },
    findNext: function (cm, _head, motionArgs) {
        var state = getSearchState(cm);
        var query = state.getQuery();
        if (!query) {
            return;
        }
        var prev = !motionArgs.forward;
        prev = (state.isReversed()) ? !prev : prev;
        highlightSearchMatches(cm, query);
        return findNext(cm, prev /** prev */, query, motionArgs.repeat);
    },
    findAndSelectNextInclusive: function (cm, _head, motionArgs, vim, prevInputState) {
        var state = getSearchState(cm);
        var query = state.getQuery();
        if (!query) {
            return;
        }
        var prev = !motionArgs.forward;
        prev = (state.isReversed()) ? !prev : prev;
        var next = findNextFromAndToInclusive(cm, prev, query, motionArgs.repeat, vim);
        if (!next) {
            return;
        }
        if (prevInputState.operator) {
            return next;
        }
        var from = next[0];
        var to = new Pos(next[1].line, next[1].ch - 1);
        if (vim.visualMode) {
            if (vim.visualLine || vim.visualBlock) {
                vim.visualLine = false;
                vim.visualBlock = false;
                CodeMirror.signal(cm, "vim-mode-change", { mode: "visual", subMode: "" });
            }
            var anchor = vim.sel.anchor;
            if (anchor) {
                if (state.isReversed()) {
                    if (motionArgs.forward) {
                        return [anchor, from];
                    }
                    return [anchor, to];
                }
                else {
                    if (motionArgs.forward) {
                        return [anchor, to];
                    }
                    return [anchor, from];
                }
            }
        }
        else {
            vim.visualMode = true;
            vim.visualLine = false;
            vim.visualBlock = false;
            CodeMirror.signal(cm, "vim-mode-change", { mode: "visual", subMode: "" });
        }
        return prev ? [to, from] : [from, to];
    },
    goToMark: function (cm, _head, motionArgs, vim) {
        var pos = getMarkPos(cm, vim, motionArgs.selectedCharacter);
        if (pos) {
            return motionArgs.linewise ? { line: pos.line, ch: findFirstNonWhiteSpaceCharacter(cm.getLine(pos.line)) } : pos;
        }
        return null;
    },
    moveToOtherHighlightedEnd: function (cm, _head, motionArgs, vim) {
        if (vim.visualBlock && motionArgs.sameLine) {
            var sel = vim.sel;
            return [
                clipCursorToContent(cm, new Pos(sel.anchor.line, sel.head.ch)),
                clipCursorToContent(cm, new Pos(sel.head.line, sel.anchor.ch))
            ];
        }
        else {
            return ([vim.sel.head, vim.sel.anchor]);
        }
    },
    jumpToMark: function (cm, head, motionArgs, vim) {
        var best = head;
        for (var i = 0; i < motionArgs.repeat; i++) {
            var cursor = best;
            for (var key in vim.marks) {
                if (!isLowerCase(key)) {
                    continue;
                }
                var mark = vim.marks[key].find();
                var isWrongDirection = (motionArgs.forward) ?
                    cursorIsBefore(mark, cursor) : cursorIsBefore(cursor, mark);
                if (isWrongDirection) {
                    continue;
                }
                if (motionArgs.linewise && (mark.line == cursor.line)) {
                    continue;
                }
                var equal = cursorEqual(cursor, best);
                var between = (motionArgs.forward) ?
                    cursorIsBetween(cursor, mark, best) :
                    cursorIsBetween(best, mark, cursor);
                if (equal || between) {
                    best = mark;
                }
            }
        }
        if (motionArgs.linewise) {
            best = new Pos(best.line, findFirstNonWhiteSpaceCharacter(cm.getLine(best.line)));
        }
        return best;
    },
    moveByCharacters: function (_cm, head, motionArgs) {
        var cur = head;
        var repeat = motionArgs.repeat;
        var ch = motionArgs.forward ? cur.ch + repeat : cur.ch - repeat;
        return new Pos(cur.line, ch);
    },
    moveByLines: function (cm, head, motionArgs, vim) {
        var cur = head;
        var endCh = cur.ch;
        switch (vim.lastMotion) {
            case this.moveByLines:
            case this.moveByDisplayLines:
            case this.moveByScroll:
            case this.moveToColumn:
            case this.moveToEol:
                endCh = vim.lastHPos;
                break;
            default:
                vim.lastHPos = endCh;
        }
        var repeat = motionArgs.repeat + (motionArgs.repeatOffset || 0);
        var line = motionArgs.forward ? cur.line + repeat : cur.line - repeat;
        var first = cm.firstLine();
        var last = cm.lastLine();
        if (line < first && cur.line == first) {
            return this.moveToStartOfLine(cm, head, motionArgs, vim);
        }
        else if (line > last && cur.line == last) {
            return moveToEol(cm, head, motionArgs, vim, true);
        }
        var fold = cm.ace.session.getFoldLine(line);
        if (fold) {
            if (motionArgs.forward) {
                if (line > fold.start.row)
                    line = fold.end.row + 1;
            }
            else {
                line = fold.start.row;
            }
        }
        if (motionArgs.toFirstChar) {
            endCh = findFirstNonWhiteSpaceCharacter(cm.getLine(line));
            vim.lastHPos = endCh;
        }
        vim.lastHSPos = cm.charCoords(new Pos(line, endCh), 'div').left;
        return new Pos(line, endCh);
    },
    moveByDisplayLines: function (cm, head, motionArgs, vim) {
        var cur = head;
        switch (vim.lastMotion) {
            case this.moveByDisplayLines:
            case this.moveByScroll:
            case this.moveByLines:
            case this.moveToColumn:
            case this.moveToEol:
                break;
            default:
                vim.lastHSPos = cm.charCoords(cur, 'div').left;
        }
        var repeat = motionArgs.repeat;
        var res = cm.findPosV(cur, (motionArgs.forward ? repeat : -repeat), 'line', vim.lastHSPos);
        if (res.hitSide) {
            if (motionArgs.forward) {
                var lastCharCoords = cm.charCoords(res, 'div');
                var goalCoords = { top: lastCharCoords.top + 8, left: vim.lastHSPos };
                var res = cm.coordsChar(goalCoords, 'div');
            }
            else {
                var resCoords = cm.charCoords(new Pos(cm.firstLine(), 0), 'div');
                resCoords.left = vim.lastHSPos;
                res = cm.coordsChar(resCoords, 'div');
            }
        }
        vim.lastHPos = res.ch;
        return res;
    },
    moveByPage: function (cm, head, motionArgs) {
        var curStart = head;
        var repeat = motionArgs.repeat;
        return cm.findPosV(curStart, (motionArgs.forward ? repeat : -repeat), 'page');
    },
    moveByParagraph: function (cm, head, motionArgs) {
        var dir = motionArgs.forward ? 1 : -1;
        return findParagraph(cm, head, motionArgs.repeat, dir);
    },
    moveBySentence: function (cm, head, motionArgs) {
        var dir = motionArgs.forward ? 1 : -1;
        return findSentence(cm, head, motionArgs.repeat, dir);
    },
    moveByScroll: function (cm, head, motionArgs, vim) {
        var scrollbox = cm.getScrollInfo();
        var curEnd = null;
        var repeat = motionArgs.repeat;
        if (!repeat) {
            repeat = scrollbox.clientHeight / (2 * cm.defaultTextHeight());
        }
        var orig = cm.charCoords(head, 'local');
        motionArgs.repeat = repeat;
        curEnd = motions.moveByDisplayLines(cm, head, motionArgs, vim);
        if (!curEnd) {
            return null;
        }
        var dest = cm.charCoords(curEnd, 'local');
        cm.scrollTo(null, scrollbox.top + dest.top - orig.top);
        return curEnd;
    },
    moveByWords: function (cm, head, motionArgs) {
        return moveToWord(cm, head, motionArgs.repeat, !!motionArgs.forward, !!motionArgs.wordEnd, !!motionArgs.bigWord);
    },
    moveTillCharacter: function (cm, head, motionArgs) {
        var repeat = motionArgs.repeat;
        var curEnd = moveToCharacter(cm, repeat, motionArgs.forward, motionArgs.selectedCharacter, head);
        var increment = motionArgs.forward ? -1 : 1;
        recordLastCharacterSearch(increment, motionArgs);
        if (!curEnd)
            return null;
        curEnd.ch += increment;
        return curEnd;
    },
    moveToCharacter: function (cm, head, motionArgs) {
        var repeat = motionArgs.repeat;
        recordLastCharacterSearch(0, motionArgs);
        return moveToCharacter(cm, repeat, motionArgs.forward, motionArgs.selectedCharacter, head) || head;
    },
    moveToSymbol: function (cm, head, motionArgs) {
        var repeat = motionArgs.repeat;
        return findSymbol(cm, repeat, motionArgs.forward, motionArgs.selectedCharacter) || head;
    },
    moveToColumn: function (cm, head, motionArgs, vim) {
        var repeat = motionArgs.repeat;
        vim.lastHPos = repeat - 1;
        vim.lastHSPos = cm.charCoords(head, 'div').left;
        return moveToColumn(cm, repeat);
    },
    moveToEol: function (cm, head, motionArgs, vim) {
        return moveToEol(cm, head, motionArgs, vim, false);
    },
    moveToFirstNonWhiteSpaceCharacter: function (cm, head) {
        var cursor = head;
        return new Pos(cursor.line, findFirstNonWhiteSpaceCharacter(cm.getLine(cursor.line)));
    },
    moveToMatchedSymbol: function (cm, head) {
        var cursor = head;
        var line = cursor.line;
        var ch = cursor.ch;
        var lineText = cm.getLine(line);
        var symbol;
        for (; ch < lineText.length; ch++) {
            symbol = lineText.charAt(ch);
            if (symbol && isMatchableSymbol(symbol)) {
                var style = cm.getTokenTypeAt(new Pos(line, ch + 1));
                if (style !== "string" && style !== "comment") {
                    break;
                }
            }
        }
        if (ch < lineText.length) {
            var re = /[<>]/.test(lineText[ch]) ? /[(){}[\]<>]/ : /[(){}[\]]/; //ace_patch?
            var matched = cm.findMatchingBracket(new Pos(line, ch + 1), { bracketRegex: re });
            return matched.to;
        }
        else {
            return cursor;
        }
    },
    moveToStartOfLine: function (_cm, head) {
        return new Pos(head.line, 0);
    },
    moveToLineOrEdgeOfDocument: function (cm, _head, motionArgs) {
        var lineNum = motionArgs.forward ? cm.lastLine() : cm.firstLine();
        if (motionArgs.repeatIsExplicit) {
            lineNum = motionArgs.repeat - cm.getOption('firstLineNumber');
        }
        return new Pos(lineNum, findFirstNonWhiteSpaceCharacter(cm.getLine(lineNum)));
    },
    moveToStartOfDisplayLine: function (cm) {
        cm.execCommand("goLineLeft");
        return cm.getCursor();
    },
    moveToEndOfDisplayLine: function (cm) {
        cm.execCommand("goLineRight");
        var head = cm.getCursor();
        if (head.sticky == "before")
            head.ch--;
        return head;
    },
    textObjectManipulation: function (cm, head, motionArgs, vim) {
        var mirroredPairs = { '(': ')', ')': '(',
            '{': '}', '}': '{',
            '[': ']', ']': '[',
            '<': '>', '>': '<' };
        var selfPaired = { '\'': true, '"': true, '`': true };
        var character = motionArgs.selectedCharacter;
        if (character == 'b') {
            character = '(';
        }
        else if (character == 'B') {
            character = '{';
        }
        var inclusive = !motionArgs.textObjectInner;
        var tmp, move;
        if (mirroredPairs[character]) {
            move = true;
            tmp = selectCompanionObject(cm, head, character, inclusive);
            if (!tmp) {
                var sc = cm.getSearchCursor(new RegExp("\\" + character, "g"), head);
                if (sc.find()) {
                    tmp = selectCompanionObject(cm, sc.from(), character, inclusive);
                }
            }
        }
        else if (selfPaired[character]) {
            move = true;
            tmp = findBeginningAndEnd(cm, head, character, inclusive);
        }
        else if (character === 'W' || character === 'w') {
            var repeat = motionArgs.repeat || 1;
            while (repeat-- > 0) {
                var repeated = expandWordUnderCursor(cm, {
                    inclusive: inclusive,
                    innerWord: !inclusive,
                    bigWord: character === 'W',
                    noSymbol: character === 'W',
                    multiline: true
                }, tmp && tmp.end);
                if (repeated) {
                    if (!tmp)
                        tmp = repeated;
                    tmp.end = repeated.end;
                }
            }
        }
        else if (character === 'p') {
            tmp = findParagraph(cm, head, motionArgs.repeat, 0, inclusive);
            motionArgs.linewise = true;
            if (vim.visualMode) {
                if (!vim.visualLine) {
                    vim.visualLine = true;
                }
            }
            else {
                var operatorArgs = vim.inputState.operatorArgs;
                if (operatorArgs) {
                    operatorArgs.linewise = true;
                }
                tmp.end.line--;
            }
        }
        else if (character === 't') {
            tmp = expandTagUnderCursor(cm, head, inclusive);
        }
        else if (character === 's') {
            var content = cm.getLine(head.line);
            if (head.ch > 0 && isEndOfSentenceSymbol(content[head.ch])) {
                head.ch -= 1;
            }
            var end = getSentence(cm, head, motionArgs.repeat, 1, inclusive);
            var start = getSentence(cm, head, motionArgs.repeat, -1, inclusive);
            if (isWhiteSpaceString(cm.getLine(start.line)[start.ch])
                && isWhiteSpaceString(cm.getLine(end.line)[end.ch - 1])) {
                start = { line: start.line, ch: start.ch + 1 };
            }
            tmp = { start: start, end: end };
        }
        if (!tmp) {
            return null;
        }
        if (!cm.state.vim.visualMode) {
            return [tmp.start, tmp.end];
        }
        else {
            return expandSelection(cm, tmp.start, tmp.end, move);
        }
    },
    repeatLastCharacterSearch: function (cm, head, motionArgs) {
        var lastSearch = vimGlobalState.lastCharacterSearch;
        var repeat = motionArgs.repeat;
        var forward = motionArgs.forward === lastSearch.forward;
        var increment = (lastSearch.increment ? 1 : 0) * (forward ? -1 : 1);
        cm.moveH(-increment, 'char');
        motionArgs.inclusive = forward ? true : false;
        var curEnd = moveToCharacter(cm, repeat, forward, lastSearch.selectedCharacter);
        if (!curEnd) {
            cm.moveH(increment, 'char');
            return head;
        }
        curEnd.ch += increment;
        return curEnd;
    }
};
function defineMotion(name, fn) {
    motions[name] = fn;
}
function fillArray(val, times) {
    var arr = [];
    for (var i = 0; i < times; i++) {
        arr.push(val);
    }
    return arr;
}
var operators = {
    change: function (cm, args, ranges) {
        var finalHead, text;
        var vim = cm.state.vim;
        var anchor = ranges[0].anchor, head = ranges[0].head;
        if (!vim.visualMode) {
            text = cm.getRange(anchor, head);
            var lastState = vim.lastEditInputState || {};
            if (lastState.motion == "moveByWords" && !isWhiteSpaceString(text)) {
                var match = (/\s+$/).exec(text);
                if (match && lastState.motionArgs && lastState.motionArgs.forward) {
                    head = offsetCursor(head, 0, -match[0].length);
                    text = text.slice(0, -match[0].length);
                }
            }
            if (args.linewise) {
                anchor = new Pos(anchor.line, findFirstNonWhiteSpaceCharacter(cm.getLine(anchor.line)));
                if (head.line > anchor.line) {
                    head = new Pos(head.line - 1, Number.MAX_VALUE);
                }
            }
            cm.replaceRange('', anchor, head);
            finalHead = anchor;
        }
        else if (args.fullLine) {
            head.ch = Number.MAX_VALUE;
            head.line--;
            cm.setSelection(anchor, head);
            text = cm.getSelection();
            cm.replaceSelection("");
            finalHead = anchor;
        }
        else {
            text = cm.getSelection();
            var replacement = fillArray('', ranges.length);
            cm.replaceSelections(replacement);
            finalHead = cursorMin(ranges[0].head, ranges[0].anchor);
        }
        vimGlobalState.registerController.pushText(args.registerName, 'change', text, args.linewise, ranges.length > 1);
        actions.enterInsertMode(cm, { head: finalHead }, cm.state.vim);
    },
    'delete': function (cm, args, ranges) {
        var finalHead, text;
        var vim = cm.state.vim;
        if (!vim.visualBlock) {
            var anchor = ranges[0].anchor, head = ranges[0].head;
            if (args.linewise &&
                head.line != cm.firstLine() &&
                anchor.line == cm.lastLine() &&
                anchor.line == head.line - 1) {
                if (anchor.line == cm.firstLine()) {
                    anchor.ch = 0;
                }
                else {
                    anchor = new Pos(anchor.line - 1, lineLength(cm, anchor.line - 1));
                }
            }
            text = cm.getRange(anchor, head);
            cm.replaceRange('', anchor, head);
            finalHead = anchor;
            if (args.linewise) {
                finalHead = motions.moveToFirstNonWhiteSpaceCharacter(cm, anchor);
            }
        }
        else {
            text = cm.getSelection();
            var replacement = fillArray('', ranges.length);
            cm.replaceSelections(replacement);
            finalHead = cursorMin(ranges[0].head, ranges[0].anchor);
        }
        vimGlobalState.registerController.pushText(args.registerName, 'delete', text, args.linewise, vim.visualBlock);
        return clipCursorToContent(cm, finalHead);
    },
    indent: function (cm, args, ranges) {
        var vim = cm.state.vim;
        var repeat = (vim.visualMode) ? args.repeat : 1;
        if (vim.visualBlock) {
            var tabSize = cm.getOption('tabSize');
            var indent = cm.getOption('indentWithTabs') ? '\t' : ' '.repeat(tabSize);
            var cursor;
            for (var i = ranges.length - 1; i >= 0; i--) {
                cursor = cursorMin(ranges[i].anchor, ranges[i].head);
                if (args.indentRight) {
                    cm.replaceRange(indent.repeat(repeat), cursor, cursor);
                }
                else {
                    var text = cm.getLine(cursor.line);
                    var end = 0;
                    for (var j = 0; j < repeat; j++) {
                        var ch = text[cursor.ch + end];
                        if (ch == '\t') {
                            end++;
                        }
                        else if (ch == ' ') {
                            end++;
                            for (var k = 1; k < indent.length; k++) {
                                ch = text[cursor.ch + end];
                                if (ch !== ' ')
                                    break;
                                end++;
                            }
                        }
                        else {
                            break;
                        }
                    }
                    cm.replaceRange('', cursor, offsetCursor(cursor, 0, end));
                }
            }
            return cursor;
        }
        else if (cm.indentMore) {
            for (var j = 0; j < repeat; j++) {
                if (args.indentRight)
                    cm.indentMore();
                else
                    cm.indentLess();
            }
        }
        else {
            var startLine = ranges[0].anchor.line;
            var endLine = vim.visualBlock ?
                ranges[ranges.length - 1].anchor.line :
                ranges[0].head.line;
            if (args.linewise) {
                endLine--;
            }
            for (var i = startLine; i <= endLine; i++) {
                for (var j = 0; j < repeat; j++) {
                    cm.indentLine(i, args.indentRight);
                }
            }
        }
        return motions.moveToFirstNonWhiteSpaceCharacter(cm, ranges[0].anchor);
    },
    indentAuto: function (cm, _args, ranges) {
        cm.execCommand("indentAuto");
        return motions.moveToFirstNonWhiteSpaceCharacter(cm, ranges[0].anchor);
    },
    hardWrap: function (cm, operatorArgs, ranges, oldAnchor, newHead) {
        if (!cm.hardWrap)
            return;
        var from = ranges[0].anchor.line;
        var to = ranges[0].head.line;
        if (operatorArgs.linewise)
            to--;
        var endRow = cm.hardWrap({ from: from, to: to });
        if (endRow > from && operatorArgs.linewise)
            endRow--;
        return operatorArgs.keepCursor ? oldAnchor : new Pos(endRow, 0);
    },
    changeCase: function (cm, args, ranges, oldAnchor, newHead) {
        var selections = cm.getSelections();
        var swapped = [];
        var toLower = args.toLower;
        for (var j = 0; j < selections.length; j++) {
            var toSwap = selections[j];
            var text = '';
            if (toLower === true) {
                text = toSwap.toLowerCase();
            }
            else if (toLower === false) {
                text = toSwap.toUpperCase();
            }
            else {
                for (var i = 0; i < toSwap.length; i++) {
                    var character = toSwap.charAt(i);
                    text += isUpperCase(character) ? character.toLowerCase() :
                        character.toUpperCase();
                }
            }
            swapped.push(text);
        }
        cm.replaceSelections(swapped);
        if (args.shouldMoveCursor) {
            return newHead;
        }
        else if (!cm.state.vim.visualMode && args.linewise && ranges[0].anchor.line + 1 == ranges[0].head.line) {
            return motions.moveToFirstNonWhiteSpaceCharacter(cm, oldAnchor);
        }
        else if (args.linewise) {
            return oldAnchor;
        }
        else {
            return cursorMin(ranges[0].anchor, ranges[0].head);
        }
    },
    yank: function (cm, args, ranges, oldAnchor) {
        var vim = cm.state.vim;
        var text = cm.getSelection();
        var endPos = vim.visualMode
            ? cursorMin(vim.sel.anchor, vim.sel.head, ranges[0].head, ranges[0].anchor)
            : oldAnchor;
        vimGlobalState.registerController.pushText(args.registerName, 'yank', text, args.linewise, vim.visualBlock);
        return endPos;
    }
};
function defineOperator(name, fn) {
    operators[name] = fn;
}
var actions = {
    jumpListWalk: function (cm, actionArgs, vim) {
        if (vim.visualMode) {
            return;
        }
        var repeat = actionArgs.repeat;
        var forward = actionArgs.forward;
        var jumpList = vimGlobalState.jumpList;
        var mark = jumpList.move(cm, forward ? repeat : -repeat);
        var markPos = mark ? mark.find() : undefined;
        markPos = markPos ? markPos : cm.getCursor();
        cm.setCursor(markPos);
        cm.ace.curOp.command.scrollIntoView = "center-animate"; // ace_patch
    },
    scroll: function (cm, actionArgs, vim) {
        if (vim.visualMode) {
            return;
        }
        var repeat = actionArgs.repeat || 1;
        var lineHeight = cm.defaultTextHeight();
        var top = cm.getScrollInfo().top;
        var delta = lineHeight * repeat;
        var newPos = actionArgs.forward ? top + delta : top - delta;
        var cursor = copyCursor(cm.getCursor());
        var cursorCoords = cm.charCoords(cursor, 'local');
        if (actionArgs.forward) {
            if (newPos > cursorCoords.top) {
                cursor.line += (newPos - cursorCoords.top) / lineHeight;
                cursor.line = Math.ceil(cursor.line);
                cm.setCursor(cursor);
                cursorCoords = cm.charCoords(cursor, 'local');
                cm.scrollTo(null, cursorCoords.top);
            }
            else {
                cm.scrollTo(null, newPos);
            }
        }
        else {
            var newBottom = newPos + cm.getScrollInfo().clientHeight;
            if (newBottom < cursorCoords.bottom) {
                cursor.line -= (cursorCoords.bottom - newBottom) / lineHeight;
                cursor.line = Math.floor(cursor.line);
                cm.setCursor(cursor);
                cursorCoords = cm.charCoords(cursor, 'local');
                cm.scrollTo(null, cursorCoords.bottom - cm.getScrollInfo().clientHeight);
            }
            else {
                cm.scrollTo(null, newPos);
            }
        }
    },
    scrollToCursor: function (cm, actionArgs) {
        var lineNum = cm.getCursor().line;
        var charCoords = cm.charCoords(new Pos(lineNum, 0), 'local');
        var height = cm.getScrollInfo().clientHeight;
        var y = charCoords.top;
        switch (actionArgs.position) {
            case 'center':
                y = charCoords.bottom - height / 2;
                break;
            case 'bottom':
                var lineLastCharPos = new Pos(lineNum, cm.getLine(lineNum).length - 1);
                var lineLastCharCoords = cm.charCoords(lineLastCharPos, 'local');
                var lineHeight = lineLastCharCoords.bottom - y;
                y = y - height + lineHeight;
                break;
        }
        cm.scrollTo(null, y);
    },
    replayMacro: function (cm, actionArgs, vim) {
        var registerName = actionArgs.selectedCharacter;
        var repeat = actionArgs.repeat;
        var macroModeState = vimGlobalState.macroModeState;
        if (registerName == '@') {
            registerName = macroModeState.latestRegister;
        }
        else {
            macroModeState.latestRegister = registerName;
        }
        while (repeat--) {
            executeMacroRegister(cm, vim, macroModeState, registerName);
        }
    },
    enterMacroRecordMode: function (cm, actionArgs) {
        var macroModeState = vimGlobalState.macroModeState;
        var registerName = actionArgs.selectedCharacter;
        if (vimGlobalState.registerController.isValidRegister(registerName)) {
            macroModeState.enterMacroRecordMode(cm, registerName);
        }
    },
    toggleOverwrite: function (cm) {
        if (!cm.state.overwrite) {
            cm.toggleOverwrite(true);
            cm.setOption('keyMap', 'vim-replace');
            CodeMirror.signal(cm, "vim-mode-change", { mode: "replace" });
        }
        else {
            cm.toggleOverwrite(false);
            cm.setOption('keyMap', 'vim-insert');
            CodeMirror.signal(cm, "vim-mode-change", { mode: "insert" });
        }
    },
    enterInsertMode: function (cm, actionArgs, vim) {
        if (cm.getOption('readOnly')) {
            return;
        }
        vim.insertMode = true;
        vim.insertModeRepeat = actionArgs && actionArgs.repeat || 1;
        var insertAt = (actionArgs) ? actionArgs.insertAt : null;
        var sel = vim.sel;
        var head = actionArgs.head || cm.getCursor('head');
        var height = cm.listSelections().length;
        if (insertAt == 'eol') {
            head = new Pos(head.line, lineLength(cm, head.line));
        }
        else if (insertAt == 'bol') {
            head = new Pos(head.line, 0);
        }
        else if (insertAt == 'charAfter') {
            var newPosition = updateSelectionForSurrogateCharacters(cm, head, offsetCursor(head, 0, 1));
            head = newPosition.end;
        }
        else if (insertAt == 'firstNonBlank') {
            var newPosition = updateSelectionForSurrogateCharacters(cm, head, motions.moveToFirstNonWhiteSpaceCharacter(cm, head));
            head = newPosition.end;
        }
        else if (insertAt == 'startOfSelectedArea') {
            if (!vim.visualMode)
                return;
            if (!vim.visualBlock) {
                if (sel.head.line < sel.anchor.line) {
                    head = sel.head;
                }
                else {
                    head = new Pos(sel.anchor.line, 0);
                }
            }
            else {
                head = new Pos(Math.min(sel.head.line, sel.anchor.line), Math.min(sel.head.ch, sel.anchor.ch));
                height = Math.abs(sel.head.line - sel.anchor.line) + 1;
            }
        }
        else if (insertAt == 'endOfSelectedArea') {
            if (!vim.visualMode)
                return;
            if (!vim.visualBlock) {
                if (sel.head.line >= sel.anchor.line) {
                    head = offsetCursor(sel.head, 0, 1);
                }
                else {
                    head = new Pos(sel.anchor.line, 0);
                }
            }
            else {
                head = new Pos(Math.min(sel.head.line, sel.anchor.line), Math.max(sel.head.ch, sel.anchor.ch) + 1);
                height = Math.abs(sel.head.line - sel.anchor.line) + 1;
            }
        }
        else if (insertAt == 'inplace') {
            if (vim.visualMode) {
                return;
            }
        }
        else if (insertAt == 'lastEdit') {
            head = getLastEditPos(cm) || head;
        }
        cm.setOption('disableInput', false);
        if (actionArgs && actionArgs.replace) {
            cm.toggleOverwrite(true);
            cm.setOption('keyMap', 'vim-replace');
            CodeMirror.signal(cm, "vim-mode-change", { mode: "replace" });
        }
        else {
            cm.toggleOverwrite(false);
            cm.setOption('keyMap', 'vim-insert');
            CodeMirror.signal(cm, "vim-mode-change", { mode: "insert" });
        }
        if (!vimGlobalState.macroModeState.isPlaying) {
            cm.on('change', onChange);
            if (vim.insertEnd)
                vim.insertEnd.clear();
            vim.insertEnd = cm.setBookmark(head, { insertLeft: true });
            CodeMirror.on(cm.getInputField(), 'keydown', onKeyEventTargetKeyDown);
        }
        if (vim.visualMode) {
            exitVisualMode(cm);
        }
        selectForInsert(cm, head, height);
    },
    toggleVisualMode: function (cm, actionArgs, vim) {
        var repeat = actionArgs.repeat;
        var anchor = cm.getCursor();
        var head;
        if (!vim.visualMode) {
            vim.visualMode = true;
            vim.visualLine = !!actionArgs.linewise;
            vim.visualBlock = !!actionArgs.blockwise;
            head = clipCursorToContent(cm, new Pos(anchor.line, anchor.ch + repeat - 1));
            var newPosition = updateSelectionForSurrogateCharacters(cm, anchor, head);
            vim.sel = {
                anchor: newPosition.start,
                head: newPosition.end
            };
            CodeMirror.signal(cm, "vim-mode-change", { mode: "visual", subMode: vim.visualLine ? "linewise" : vim.visualBlock ? "blockwise" : "" });
            updateCmSelection(cm);
            updateMark(cm, vim, '<', cursorMin(anchor, head));
            updateMark(cm, vim, '>', cursorMax(anchor, head));
        }
        else if (vim.visualLine ^ actionArgs.linewise ||
            vim.visualBlock ^ actionArgs.blockwise) {
            vim.visualLine = !!actionArgs.linewise;
            vim.visualBlock = !!actionArgs.blockwise;
            CodeMirror.signal(cm, "vim-mode-change", { mode: "visual", subMode: vim.visualLine ? "linewise" : vim.visualBlock ? "blockwise" : "" });
            updateCmSelection(cm);
        }
        else {
            exitVisualMode(cm);
        }
    },
    reselectLastSelection: function (cm, _actionArgs, vim) {
        var lastSelection = vim.lastSelection;
        if (vim.visualMode) {
            updateLastSelection(cm, vim);
        }
        if (lastSelection) {
            var anchor = lastSelection.anchorMark.find();
            var head = lastSelection.headMark.find();
            if (!anchor || !head) {
                return;
            }
            vim.sel = {
                anchor: anchor,
                head: head
            };
            vim.visualMode = true;
            vim.visualLine = lastSelection.visualLine;
            vim.visualBlock = lastSelection.visualBlock;
            updateCmSelection(cm);
            updateMark(cm, vim, '<', cursorMin(anchor, head));
            updateMark(cm, vim, '>', cursorMax(anchor, head));
            CodeMirror.signal(cm, 'vim-mode-change', {
                mode: 'visual',
                subMode: vim.visualLine ? 'linewise' :
                    vim.visualBlock ? 'blockwise' : ''
            });
        }
    },
    joinLines: function (cm, actionArgs, vim) {
        var curStart, curEnd;
        if (vim.visualMode) {
            curStart = cm.getCursor('anchor');
            curEnd = cm.getCursor('head');
            if (cursorIsBefore(curEnd, curStart)) {
                var tmp = curEnd;
                curEnd = curStart;
                curStart = tmp;
            }
            curEnd.ch = lineLength(cm, curEnd.line) - 1;
        }
        else {
            var repeat = Math.max(actionArgs.repeat, 2);
            curStart = cm.getCursor();
            curEnd = clipCursorToContent(cm, new Pos(curStart.line + repeat - 1, Infinity));
        }
        var finalCh = 0;
        for (var i = curStart.line; i < curEnd.line; i++) {
            finalCh = lineLength(cm, curStart.line);
            var text = '';
            var nextStartCh = 0;
            if (!actionArgs.keepSpaces) {
                var nextLine = cm.getLine(curStart.line + 1);
                nextStartCh = nextLine.search(/\S/);
                if (nextStartCh == -1) {
                    nextStartCh = nextLine.length;
                }
                else {
                    text = " ";
                }
            }
            cm.replaceRange(text, new Pos(curStart.line, finalCh), new Pos(curStart.line + 1, nextStartCh));
        }
        var curFinalPos = clipCursorToContent(cm, new Pos(curStart.line, finalCh));
        if (vim.visualMode) {
            exitVisualMode(cm, false);
        }
        cm.setCursor(curFinalPos);
    },
    newLineAndEnterInsertMode: function (cm, actionArgs, vim) {
        vim.insertMode = true;
        var insertAt = copyCursor(cm.getCursor());
        if (insertAt.line === cm.firstLine() && !actionArgs.after) {
            cm.replaceRange('\n', new Pos(cm.firstLine(), 0));
            cm.setCursor(cm.firstLine(), 0);
        }
        else {
            insertAt.line = (actionArgs.after) ? insertAt.line :
                insertAt.line - 1;
            insertAt.ch = lineLength(cm, insertAt.line);
            cm.setCursor(insertAt);
            var newlineFn = CodeMirror.commands.newlineAndIndentContinueComment ||
                CodeMirror.commands.newlineAndIndent;
            newlineFn(cm);
        }
        this.enterInsertMode(cm, { repeat: actionArgs.repeat }, vim);
    },
    paste: function (cm, actionArgs, vim) {
        var _this = this;
        var register = vimGlobalState.registerController.getRegister(actionArgs.registerName);
        var fallback = function () {
            var text = register.toString();
            _this.continuePaste(cm, actionArgs, vim, text, register);
        };
        if (actionArgs.registerName === '+' &&
            typeof navigator !== 'undefined' &&
            typeof navigator.clipboard !== 'undefined' &&
            typeof navigator.clipboard.readText === 'function') {
            navigator.clipboard.readText().then(function (value) {
                _this.continuePaste(cm, actionArgs, vim, value, register);
            }, function () { fallback(); });
        }
        else {
            fallback();
        }
    },
    continuePaste: function (cm, actionArgs, vim, text, register) {
        var cur = copyCursor(cm.getCursor());
        if (!text) {
            return;
        }
        if (actionArgs.matchIndent) {
            var tabSize = cm.getOption("tabSize");
            var whitespaceLength = function (str) {
                var tabs = (str.split("\t").length - 1);
                var spaces = (str.split(" ").length - 1);
                return tabs * tabSize + spaces * 1;
            };
            var currentLine = cm.getLine(cm.getCursor().line);
            var indent = whitespaceLength(currentLine.match(/^\s*/)[0]);
            var chompedText = text.replace(/\n$/, '');
            var wasChomped = text !== chompedText;
            var firstIndent = whitespaceLength(text.match(/^\s*/)[0]);
            var text = chompedText.replace(/^\s*/gm, function (wspace) {
                var newIndent = indent + (whitespaceLength(wspace) - firstIndent);
                if (newIndent < 0) {
                    return "";
                }
                else if (cm.getOption("indentWithTabs")) {
                    var quotient = Math.floor(newIndent / tabSize);
                    return Array(quotient + 1).join('\t');
                }
                else {
                    return Array(newIndent + 1).join(' ');
                }
            });
            text += wasChomped ? "\n" : "";
        }
        if (actionArgs.repeat > 1) {
            var text = Array(actionArgs.repeat + 1).join(text);
        }
        var linewise = register.linewise;
        var blockwise = register.blockwise;
        if (blockwise) {
            text = text.split('\n');
            if (linewise) {
                text.pop();
            }
            for (var i = 0; i < text.length; i++) {
                text[i] = (text[i] == '') ? ' ' : text[i];
            }
            cur.ch += actionArgs.after ? 1 : 0;
            cur.ch = Math.min(lineLength(cm, cur.line), cur.ch);
        }
        else if (linewise) {
            if (vim.visualMode) {
                text = vim.visualLine ? text.slice(0, -1) : '\n' + text.slice(0, text.length - 1) + '\n';
            }
            else if (actionArgs.after) {
                text = '\n' + text.slice(0, text.length - 1);
                cur.ch = lineLength(cm, cur.line);
            }
            else {
                cur.ch = 0;
            }
        }
        else {
            cur.ch += actionArgs.after ? 1 : 0;
        }
        var curPosFinal;
        if (vim.visualMode) {
            vim.lastPastedText = text;
            var lastSelectionCurEnd;
            var selectedArea = getSelectedAreaRange(cm, vim);
            var selectionStart = selectedArea[0];
            var selectionEnd = selectedArea[1];
            var selectedText = cm.getSelection();
            var selections = cm.listSelections();
            var emptyStrings = new Array(selections.length).join('1').split('1');
            if (vim.lastSelection) {
                lastSelectionCurEnd = vim.lastSelection.headMark.find();
            }
            vimGlobalState.registerController.unnamedRegister.setText(selectedText);
            if (blockwise) {
                cm.replaceSelections(emptyStrings);
                selectionEnd = new Pos(selectionStart.line + text.length - 1, selectionStart.ch);
                cm.setCursor(selectionStart);
                selectBlock(cm, selectionEnd);
                cm.replaceSelections(text);
                curPosFinal = selectionStart;
            }
            else if (vim.visualBlock) {
                cm.replaceSelections(emptyStrings);
                cm.setCursor(selectionStart);
                cm.replaceRange(text, selectionStart, selectionStart);
                curPosFinal = selectionStart;
            }
            else {
                cm.replaceRange(text, selectionStart, selectionEnd);
                curPosFinal = cm.posFromIndex(cm.indexFromPos(selectionStart) + text.length - 1);
            }
            if (lastSelectionCurEnd) {
                vim.lastSelection.headMark = cm.setBookmark(lastSelectionCurEnd);
            }
            if (linewise) {
                curPosFinal.ch = 0;
            }
        }
        else {
            if (blockwise) {
                cm.setCursor(cur);
                for (var i = 0; i < text.length; i++) {
                    var line = cur.line + i;
                    if (line > cm.lastLine()) {
                        cm.replaceRange('\n', new Pos(line, 0));
                    }
                    var lastCh = lineLength(cm, line);
                    if (lastCh < cur.ch) {
                        extendLineToColumn(cm, line, cur.ch);
                    }
                }
                cm.setCursor(cur);
                selectBlock(cm, new Pos(cur.line + text.length - 1, cur.ch));
                cm.replaceSelections(text);
                curPosFinal = cur;
            }
            else {
                cm.replaceRange(text, cur);
                if (linewise) {
                    var line = actionArgs.after ? cur.line + 1 : cur.line;
                    curPosFinal = new Pos(line, findFirstNonWhiteSpaceCharacter(cm.getLine(line)));
                }
                else {
                    curPosFinal = copyCursor(cur);
                    if (!/\n/.test(text)) {
                        curPosFinal.ch += text.length - (actionArgs.after ? 1 : 0);
                    }
                }
            }
        }
        if (vim.visualMode) {
            exitVisualMode(cm, false);
        }
        cm.setCursor(curPosFinal);
    },
    undo: function (cm, actionArgs) {
        cm.operation(function () {
            repeatFn(cm, CodeMirror.commands.undo, actionArgs.repeat)();
            cm.setCursor(clipCursorToContent(cm, cm.getCursor('start')));
        });
    },
    redo: function (cm, actionArgs) {
        repeatFn(cm, CodeMirror.commands.redo, actionArgs.repeat)();
    },
    setRegister: function (_cm, actionArgs, vim) {
        vim.inputState.registerName = actionArgs.selectedCharacter;
    },
    insertRegister: function (cm, actionArgs, vim) {
        var registerName = actionArgs.selectedCharacter;
        var register = vimGlobalState.registerController.getRegister(registerName);
        var text = register && register.toString();
        if (text) {
            cm.replaceSelection(text);
        }
    },
    oneNormalCommand: function (cm, actionArgs, vim) {
        exitInsertMode(cm, true);
        vim.insertModeReturn = true;
        CodeMirror.on(cm, 'vim-command-done', function handler() {
            if (vim.visualMode)
                return;
            if (vim.insertModeReturn) {
                vim.insertModeReturn = false;
                if (!vim.insertMode) {
                    actions.enterInsertMode(cm, {}, vim);
                }
            }
            CodeMirror.off(cm, 'vim-command-done', handler);
        });
    },
    setMark: function (cm, actionArgs, vim) {
        var markName = actionArgs.selectedCharacter;
        updateMark(cm, vim, markName, cm.getCursor());
    },
    replace: function (cm, actionArgs, vim) {
        var replaceWith = actionArgs.selectedCharacter;
        var curStart = cm.getCursor();
        var replaceTo;
        var curEnd;
        var selections = cm.listSelections();
        if (vim.visualMode) {
            curStart = cm.getCursor('start');
            curEnd = cm.getCursor('end');
        }
        else {
            var line = cm.getLine(curStart.line);
            replaceTo = curStart.ch + actionArgs.repeat;
            if (replaceTo > line.length) {
                replaceTo = line.length;
            }
            curEnd = new Pos(curStart.line, replaceTo);
        }
        var newPositions = updateSelectionForSurrogateCharacters(cm, curStart, curEnd);
        curStart = newPositions.start;
        curEnd = newPositions.end;
        if (replaceWith == '\n') {
            if (!vim.visualMode)
                cm.replaceRange('', curStart, curEnd);
            (CodeMirror.commands.newlineAndIndentContinueComment || CodeMirror.commands.newlineAndIndent)(cm);
        }
        else {
            var replaceWithStr = cm.getRange(curStart, curEnd);
            replaceWithStr = replaceWithStr.replace(/[\uD800-\uDBFF][\uDC00-\uDFFF]/g, replaceWith);
            replaceWithStr = replaceWithStr.replace(/[^\n]/g, replaceWith);
            if (vim.visualBlock) {
                var spaces = new Array(cm.getOption("tabSize") + 1).join(' ');
                replaceWithStr = cm.getSelection();
                replaceWithStr = replaceWithStr.replace(/[\uD800-\uDBFF][\uDC00-\uDFFF]/g, replaceWith);
                replaceWithStr = replaceWithStr.replace(/\t/g, spaces).replace(/[^\n]/g, replaceWith).split('\n');
                cm.replaceSelections(replaceWithStr);
            }
            else {
                cm.replaceRange(replaceWithStr, curStart, curEnd);
            }
            if (vim.visualMode) {
                curStart = cursorIsBefore(selections[0].anchor, selections[0].head) ?
                    selections[0].anchor : selections[0].head;
                cm.setCursor(curStart);
                exitVisualMode(cm, false);
            }
            else {
                cm.setCursor(offsetCursor(curEnd, 0, -1));
            }
        }
    },
    incrementNumberToken: function (cm, actionArgs) {
        var cur = cm.getCursor();
        var lineStr = cm.getLine(cur.line);
        var re = /(-?)(?:(0x)([\da-f]+)|(0b|0|)(\d+))/gi;
        var match;
        var start;
        var end;
        var numberStr;
        while ((match = re.exec(lineStr)) !== null) {
            start = match.index;
            end = start + match[0].length;
            if (cur.ch < end)
                break;
        }
        if (!actionArgs.backtrack && (end <= cur.ch))
            return;
        if (match) {
            var baseStr = match[2] || match[4];
            var digits = match[3] || match[5];
            var increment = actionArgs.increase ? 1 : -1;
            var base = { '0b': 2, '0': 8, '': 10, '0x': 16 }[baseStr.toLowerCase()];
            var number = parseInt(match[1] + digits, base) + (increment * actionArgs.repeat);
            numberStr = number.toString(base);
            var zeroPadding = baseStr ? new Array(digits.length - numberStr.length + 1 + match[1].length).join('0') : '';
            if (numberStr.charAt(0) === '-') {
                numberStr = '-' + baseStr + zeroPadding + numberStr.substr(1);
            }
            else {
                numberStr = baseStr + zeroPadding + numberStr;
            }
            var from = new Pos(cur.line, start);
            var to = new Pos(cur.line, end);
            cm.replaceRange(numberStr, from, to);
        }
        else {
            return;
        }
        cm.setCursor(new Pos(cur.line, start + numberStr.length - 1));
    },
    repeatLastEdit: function (cm, actionArgs, vim) {
        var lastEditInputState = vim.lastEditInputState;
        if (!lastEditInputState) {
            return;
        }
        var repeat = actionArgs.repeat;
        if (repeat && actionArgs.repeatIsExplicit) {
            vim.lastEditInputState.repeatOverride = repeat;
        }
        else {
            repeat = vim.lastEditInputState.repeatOverride || repeat;
        }
        repeatLastEdit(cm, vim, repeat, false /** repeatForInsert */);
    },
    indent: function (cm, actionArgs) {
        cm.indentLine(cm.getCursor().line, actionArgs.indentRight);
    },
    exitInsertMode: exitInsertMode
};
function defineAction(name, fn) {
    actions[name] = fn;
}
function clipCursorToContent(cm, cur, oldCur) {
    var vim = cm.state.vim;
    var includeLineBreak = vim.insertMode || vim.visualMode;
    var line = Math.min(Math.max(cm.firstLine(), cur.line), cm.lastLine());
    var text = cm.getLine(line);
    var maxCh = text.length - 1 + Number(!!includeLineBreak);
    var ch = Math.min(Math.max(0, cur.ch), maxCh);
    var charCode = text.charCodeAt(ch);
    if (0xDC00 <= charCode && charCode <= 0xDFFF) {
        var direction = 1;
        if (oldCur && oldCur.line == line && oldCur.ch > ch) {
            direction = -1;
        }
        ch += direction;
        if (ch > maxCh)
            ch -= 2;
    }
    return new Pos(line, ch);
}
function copyArgs(args) {
    var ret = {};
    for (var prop in args) {
        if (args.hasOwnProperty(prop)) {
            ret[prop] = args[prop];
        }
    }
    return ret;
}
function offsetCursor(cur, offsetLine, offsetCh) {
    if (typeof offsetLine === 'object') {
        offsetCh = offsetLine.ch;
        offsetLine = offsetLine.line;
    }
    return new Pos(cur.line + offsetLine, cur.ch + offsetCh);
}
function commandMatches(keys, keyMap, context, inputState) {
    if (inputState.operator)
        context = "operatorPending";
    var match, partial = [], full = [];
    var startIndex = noremap ? keyMap.length - defaultKeymapLength : 0;
    for (var i = startIndex; i < keyMap.length; i++) {
        var command = keyMap[i];
        if (context == 'insert' && command.context != 'insert' ||
            (command.context && command.context != context) ||
            inputState.operator && command.type == 'action' ||
            !(match = commandMatch(keys, command.keys))) {
            continue;
        }
        if (match == 'partial') {
            partial.push(command);
        }
        if (match == 'full') {
            full.push(command);
        }
    }
    return {
        partial: partial.length && partial,
        full: full.length && full
    };
}
function commandMatch(pressed, mapped) {
    var isLastCharacter = mapped.slice(-11) == '<character>';
    var isLastRegister = mapped.slice(-10) == '<register>';
    if (isLastCharacter || isLastRegister) {
        var prefixLen = mapped.length - (isLastCharacter ? 11 : 10);
        var pressedPrefix = pressed.slice(0, prefixLen);
        var mappedPrefix = mapped.slice(0, prefixLen);
        return pressedPrefix == mappedPrefix && pressed.length > prefixLen ? 'full' :
            mappedPrefix.indexOf(pressedPrefix) == 0 ? 'partial' : false;
    }
    else {
        return pressed == mapped ? 'full' :
            mapped.indexOf(pressed) == 0 ? 'partial' : false;
    }
}
function lastChar(keys) {
    var match = /^.*(<[^>]+>)$/.exec(keys);
    var selectedCharacter = match ? match[1] : keys.slice(-1);
    if (selectedCharacter.length > 1) {
        switch (selectedCharacter) {
            case '<CR>':
                selectedCharacter = '\n';
                break;
            case '<Space>':
                selectedCharacter = ' ';
                break;
            default:
                selectedCharacter = '';
                break;
        }
    }
    return selectedCharacter;
}
function repeatFn(cm, fn, repeat) {
    return function () {
        for (var i = 0; i < repeat; i++) {
            fn(cm);
        }
    };
}
function copyCursor(cur) {
    return new Pos(cur.line, cur.ch);
}
function cursorEqual(cur1, cur2) {
    return cur1.ch == cur2.ch && cur1.line == cur2.line;
}
function cursorIsBefore(cur1, cur2) {
    if (cur1.line < cur2.line) {
        return true;
    }
    if (cur1.line == cur2.line && cur1.ch < cur2.ch) {
        return true;
    }
    return false;
}
function cursorMin(cur1, cur2) {
    if (arguments.length > 2) {
        cur2 = cursorMin.apply(undefined, Array.prototype.slice.call(arguments, 1));
    }
    return cursorIsBefore(cur1, cur2) ? cur1 : cur2;
}
function cursorMax(cur1, cur2) {
    if (arguments.length > 2) {
        cur2 = cursorMax.apply(undefined, Array.prototype.slice.call(arguments, 1));
    }
    return cursorIsBefore(cur1, cur2) ? cur2 : cur1;
}
function cursorIsBetween(cur1, cur2, cur3) {
    var cur1before2 = cursorIsBefore(cur1, cur2);
    var cur2before3 = cursorIsBefore(cur2, cur3);
    return cur1before2 && cur2before3;
}
function lineLength(cm, lineNum) {
    return cm.getLine(lineNum).length;
}
function trim(s) {
    if (s.trim) {
        return s.trim();
    }
    return s.replace(/^\s+|\s+$/g, '');
}
function escapeRegex(s) {
    return s.replace(/([.?*+$\[\]\/\\(){}|\-])/g, '\\$1');
}
function extendLineToColumn(cm, lineNum, column) {
    var endCh = lineLength(cm, lineNum);
    var spaces = new Array(column - endCh + 1).join(' ');
    cm.setCursor(new Pos(lineNum, endCh));
    cm.replaceRange(spaces, cm.getCursor());
}
function selectBlock(cm, selectionEnd) {
    var selections = [], ranges = cm.listSelections();
    var head = copyCursor(cm.clipPos(selectionEnd));
    var isClipped = !cursorEqual(selectionEnd, head);
    var curHead = cm.getCursor('head');
    var primIndex = getIndex(ranges, curHead);
    var wasClipped = cursorEqual(ranges[primIndex].head, ranges[primIndex].anchor);
    var max = ranges.length - 1;
    var index = max - primIndex > primIndex ? max : 0;
    var base = ranges[index].anchor;
    var firstLine = Math.min(base.line, head.line);
    var lastLine = Math.max(base.line, head.line);
    var baseCh = base.ch, headCh = head.ch;
    var dir = ranges[index].head.ch - baseCh;
    var newDir = headCh - baseCh;
    if (dir > 0 && newDir <= 0) {
        baseCh++;
        if (!isClipped) {
            headCh--;
        }
    }
    else if (dir < 0 && newDir >= 0) {
        baseCh--;
        if (!wasClipped) {
            headCh++;
        }
    }
    else if (dir < 0 && newDir == -1) {
        baseCh--;
        headCh++;
    }
    for (var line = firstLine; line <= lastLine; line++) {
        var range = { anchor: new Pos(line, baseCh), head: new Pos(line, headCh) };
        selections.push(range);
    }
    cm.setSelections(selections);
    selectionEnd.ch = headCh;
    base.ch = baseCh;
    return base;
}
function selectForInsert(cm, head, height) {
    var sel = [];
    for (var i = 0; i < height; i++) {
        var lineHead = offsetCursor(head, i, 0);
        sel.push({ anchor: lineHead, head: lineHead });
    }
    cm.setSelections(sel, 0);
}
function getIndex(ranges, cursor, end) {
    for (var i = 0; i < ranges.length; i++) {
        var atAnchor = end != 'head' && cursorEqual(ranges[i].anchor, cursor);
        var atHead = end != 'anchor' && cursorEqual(ranges[i].head, cursor);
        if (atAnchor || atHead) {
            return i;
        }
    }
    return -1;
}
function getSelectedAreaRange(cm, vim) {
    var lastSelection = vim.lastSelection;
    var getCurrentSelectedAreaRange = function () {
        var selections = cm.listSelections();
        var start = selections[0];
        var end = selections[selections.length - 1];
        var selectionStart = cursorIsBefore(start.anchor, start.head) ? start.anchor : start.head;
        var selectionEnd = cursorIsBefore(end.anchor, end.head) ? end.head : end.anchor;
        return [selectionStart, selectionEnd];
    };
    var getLastSelectedAreaRange = function () {
        var selectionStart = cm.getCursor();
        var selectionEnd = cm.getCursor();
        var block = lastSelection.visualBlock;
        if (block) {
            var width = block.width;
            var height = block.height;
            selectionEnd = new Pos(selectionStart.line + height, selectionStart.ch + width);
            var selections = [];
            for (var i = selectionStart.line; i < selectionEnd.line; i++) {
                var anchor = new Pos(i, selectionStart.ch);
                var head = new Pos(i, selectionEnd.ch);
                var range = { anchor: anchor, head: head };
                selections.push(range);
            }
            cm.setSelections(selections);
        }
        else {
            var start = lastSelection.anchorMark.find();
            var end = lastSelection.headMark.find();
            var line = end.line - start.line;
            var ch = end.ch - start.ch;
            selectionEnd = { line: selectionEnd.line + line, ch: line ? selectionEnd.ch : ch + selectionEnd.ch };
            if (lastSelection.visualLine) {
                selectionStart = new Pos(selectionStart.line, 0);
                selectionEnd = new Pos(selectionEnd.line, lineLength(cm, selectionEnd.line));
            }
            cm.setSelection(selectionStart, selectionEnd);
        }
        return [selectionStart, selectionEnd];
    };
    if (!vim.visualMode) {
        return getLastSelectedAreaRange();
    }
    else {
        return getCurrentSelectedAreaRange();
    }
}
function updateLastSelection(cm, vim) {
    var anchor = vim.sel.anchor;
    var head = vim.sel.head;
    if (vim.lastPastedText) {
        head = cm.posFromIndex(cm.indexFromPos(anchor) + vim.lastPastedText.length);
        vim.lastPastedText = null;
    }
    vim.lastSelection = { 'anchorMark': cm.setBookmark(anchor),
        'headMark': cm.setBookmark(head),
        'anchor': copyCursor(anchor),
        'head': copyCursor(head),
        'visualMode': vim.visualMode,
        'visualLine': vim.visualLine,
        'visualBlock': vim.visualBlock };
}
function expandSelection(cm, start, end, move) {
    var sel = cm.state.vim.sel;
    var head = move ? start : sel.head;
    var anchor = move ? start : sel.anchor;
    var tmp;
    if (cursorIsBefore(end, start)) {
        tmp = end;
        end = start;
        start = tmp;
    }
    if (cursorIsBefore(head, anchor)) {
        head = cursorMin(start, head);
        anchor = cursorMax(anchor, end);
    }
    else {
        anchor = cursorMin(start, anchor);
        head = cursorMax(head, end);
        head = offsetCursor(head, 0, -1);
        if (head.ch == -1 && head.line != cm.firstLine()) {
            head = new Pos(head.line - 1, lineLength(cm, head.line - 1));
        }
    }
    return [anchor, head];
}
function updateCmSelection(cm, sel, mode) {
    var vim = cm.state.vim;
    sel = sel || vim.sel;
    var mode = mode ||
        vim.visualLine ? 'line' : vim.visualBlock ? 'block' : 'char';
    var cmSel = makeCmSelection(cm, sel, mode);
    cm.setSelections(cmSel.ranges, cmSel.primary);
}
function makeCmSelection(cm, sel, mode, exclusive) {
    var head = copyCursor(sel.head);
    var anchor = copyCursor(sel.anchor);
    if (mode == 'char') {
        var headOffset = !exclusive && !cursorIsBefore(sel.head, sel.anchor) ? 1 : 0;
        var anchorOffset = cursorIsBefore(sel.head, sel.anchor) ? 1 : 0;
        head = offsetCursor(sel.head, 0, headOffset);
        anchor = offsetCursor(sel.anchor, 0, anchorOffset);
        return {
            ranges: [{ anchor: anchor, head: head }],
            primary: 0
        };
    }
    else if (mode == 'line') {
        if (!cursorIsBefore(sel.head, sel.anchor)) {
            anchor.ch = 0;
            var lastLine = cm.lastLine();
            if (head.line > lastLine) {
                head.line = lastLine;
            }
            head.ch = lineLength(cm, head.line);
        }
        else {
            head.ch = 0;
            anchor.ch = lineLength(cm, anchor.line);
        }
        return {
            ranges: [{ anchor: anchor, head: head }],
            primary: 0
        };
    }
    else if (mode == 'block') {
        var top = Math.min(anchor.line, head.line), fromCh = anchor.ch, bottom = Math.max(anchor.line, head.line), toCh = head.ch;
        if (fromCh < toCh) {
            toCh += 1;
        }
        else {
            fromCh += 1;
        }
        ;
        var height = bottom - top + 1;
        var primary = head.line == top ? 0 : height - 1;
        var ranges = [];
        for (var i = 0; i < height; i++) {
            ranges.push({
                anchor: new Pos(top + i, fromCh),
                head: new Pos(top + i, toCh)
            });
        }
        return {
            ranges: ranges,
            primary: primary
        };
    }
}
function getHead(cm) {
    var cur = cm.getCursor('head');
    if (cm.getSelection().length == 1) {
        cur = cursorMin(cur, cm.getCursor('anchor'));
    }
    return cur;
}
function exitVisualMode(cm, moveHead) {
    var vim = cm.state.vim;
    if (moveHead !== false) {
        cm.setCursor(clipCursorToContent(cm, vim.sel.head));
    }
    updateLastSelection(cm, vim);
    vim.visualMode = false;
    vim.visualLine = false;
    vim.visualBlock = false;
    if (!vim.insertMode)
        CodeMirror.signal(cm, "vim-mode-change", { mode: "normal" });
}
function clipToLine(cm, curStart, curEnd) {
    var selection = cm.getRange(curStart, curEnd);
    if (/\n\s*$/.test(selection)) {
        var lines = selection.split('\n');
        lines.pop();
        var line;
        for (var line = lines.pop(); lines.length > 0 && line && isWhiteSpaceString(line); line = lines.pop()) {
            curEnd.line--;
            curEnd.ch = 0;
        }
        if (line) {
            curEnd.line--;
            curEnd.ch = lineLength(cm, curEnd.line);
        }
        else {
            curEnd.ch = 0;
        }
    }
}
function expandSelectionToLine(_cm, curStart, curEnd) {
    curStart.ch = 0;
    curEnd.ch = 0;
    curEnd.line++;
}
function findFirstNonWhiteSpaceCharacter(text) {
    if (!text) {
        return 0;
    }
    var firstNonWS = text.search(/\S/);
    return firstNonWS == -1 ? text.length : firstNonWS;
}
function expandWordUnderCursor(cm, _a, cursor) {
    var inclusive = _a.inclusive, innerWord = _a.innerWord, bigWord = _a.bigWord, noSymbol = _a.noSymbol, multiline = _a.multiline;
    var cur = cursor || getHead(cm);
    var line = cm.getLine(cur.line);
    var endLine = line;
    var startLineNumber = cur.line;
    var endLineNumber = startLineNumber;
    var idx = cur.ch;
    var wordOnNextLine;
    var test = noSymbol ? wordCharTest[0] : bigWordCharTest[0];
    if (innerWord && /\s/.test(line.charAt(idx))) {
        test = function (ch) { return /\s/.test(ch); };
    }
    else {
        while (!test(line.charAt(idx))) {
            idx++;
            if (idx >= line.length) {
                if (!multiline)
                    return null;
                idx--;
                wordOnNextLine = findWord(cm, cur, true, bigWord, true);
                break;
            }
        }
        if (bigWord) {
            test = bigWordCharTest[0];
        }
        else {
            test = wordCharTest[0];
            if (!test(line.charAt(idx))) {
                test = wordCharTest[1];
            }
        }
    }
    var end = idx, start = idx;
    while (test(line.charAt(start)) && start >= 0) {
        start--;
    }
    start++;
    if (wordOnNextLine) {
        end = wordOnNextLine.to;
        endLineNumber = wordOnNextLine.line;
        endLine = cm.getLine(endLineNumber);
        if (!endLine && end == 0)
            end++;
    }
    else {
        while (test(line.charAt(end)) && end < line.length) {
            end++;
        }
    }
    if (inclusive) {
        var wordEnd = end;
        var startsWithSpace = cur.ch <= start && /\s/.test(line.charAt(cur.ch));
        if (!startsWithSpace) {
            while (/\s/.test(endLine.charAt(end)) && end < endLine.length) {
                end++;
            }
        }
        if (wordEnd == end || startsWithSpace) {
            var wordStart = start;
            while (/\s/.test(line.charAt(start - 1)) && start > 0) {
                start--;
            }
            if (!start && !startsWithSpace) {
                start = wordStart;
            }
        }
    }
    return { start: new Pos(startLineNumber, start), end: new Pos(endLineNumber, end) };
}
function expandTagUnderCursor(cm, head, inclusive) {
    var cur = head;
    if (!CodeMirror.findMatchingTag || !CodeMirror.findEnclosingTag) {
        return { start: cur, end: cur };
    }
    var tags = CodeMirror.findMatchingTag(cm, head) || CodeMirror.findEnclosingTag(cm, head);
    if (!tags || !tags.open || !tags.close) {
        return { start: cur, end: cur };
    }
    if (inclusive) {
        return { start: tags.open.from, end: tags.close.to };
    }
    return { start: tags.open.to, end: tags.close.from };
}
function recordJumpPosition(cm, oldCur, newCur) {
    if (!cursorEqual(oldCur, newCur)) {
        vimGlobalState.jumpList.add(cm, oldCur, newCur);
    }
}
function recordLastCharacterSearch(increment, args) {
    vimGlobalState.lastCharacterSearch.increment = increment;
    vimGlobalState.lastCharacterSearch.forward = args.forward;
    vimGlobalState.lastCharacterSearch.selectedCharacter = args.selectedCharacter;
}
var symbolToMode = {
    '(': 'bracket', ')': 'bracket', '{': 'bracket', '}': 'bracket',
    '[': 'section', ']': 'section',
    '*': 'comment', '/': 'comment',
    'm': 'method', 'M': 'method',
    '#': 'preprocess'
};
var findSymbolModes = {
    bracket: {
        isComplete: function (state) {
            if (state.nextCh === state.symb) {
                state.depth++;
                if (state.depth >= 1)
                    return true;
            }
            else if (state.nextCh === state.reverseSymb) {
                state.depth--;
            }
            return false;
        }
    },
    section: {
        init: function (state) {
            state.curMoveThrough = true;
            state.symb = (state.forward ? ']' : '[') === state.symb ? '{' : '}';
        },
        isComplete: function (state) {
            return state.index === 0 && state.nextCh === state.symb;
        }
    },
    comment: {
        isComplete: function (state) {
            var found = state.lastCh === '*' && state.nextCh === '/';
            state.lastCh = state.nextCh;
            return found;
        }
    },
    method: {
        init: function (state) {
            state.symb = (state.symb === 'm' ? '{' : '}');
            state.reverseSymb = state.symb === '{' ? '}' : '{';
        },
        isComplete: function (state) {
            if (state.nextCh === state.symb)
                return true;
            return false;
        }
    },
    preprocess: {
        init: function (state) {
            state.index = 0;
        },
        isComplete: function (state) {
            if (state.nextCh === '#') {
                var token = state.lineText.match(/^#(\w+)/)[1];
                if (token === 'endif') {
                    if (state.forward && state.depth === 0) {
                        return true;
                    }
                    state.depth++;
                }
                else if (token === 'if') {
                    if (!state.forward && state.depth === 0) {
                        return true;
                    }
                    state.depth--;
                }
                if (token === 'else' && state.depth === 0)
                    return true;
            }
            return false;
        }
    }
};
function findSymbol(cm, repeat, forward, symb) {
    var cur = copyCursor(cm.getCursor());
    var increment = forward ? 1 : -1;
    var endLine = forward ? cm.lineCount() : -1;
    var curCh = cur.ch;
    var line = cur.line;
    var lineText = cm.getLine(line);
    var state = {
        lineText: lineText,
        nextCh: lineText.charAt(curCh),
        lastCh: null,
        index: curCh,
        symb: symb,
        reverseSymb: (forward ? { ')': '(', '}': '{' } : { '(': ')', '{': '}' })[symb],
        forward: forward,
        depth: 0,
        curMoveThrough: false
    };
    var mode = symbolToMode[symb];
    if (!mode)
        return cur;
    var init = findSymbolModes[mode].init;
    var isComplete = findSymbolModes[mode].isComplete;
    if (init) {
        init(state);
    }
    while (line !== endLine && repeat) {
        state.index += increment;
        state.nextCh = state.lineText.charAt(state.index);
        if (!state.nextCh) {
            line += increment;
            state.lineText = cm.getLine(line) || '';
            if (increment > 0) {
                state.index = 0;
            }
            else {
                var lineLen = state.lineText.length;
                state.index = (lineLen > 0) ? (lineLen - 1) : 0;
            }
            state.nextCh = state.lineText.charAt(state.index);
        }
        if (isComplete(state)) {
            cur.line = line;
            cur.ch = state.index;
            repeat--;
        }
    }
    if (state.nextCh || state.curMoveThrough) {
        return new Pos(line, state.index);
    }
    return cur;
}
function findWord(cm, cur, forward, bigWord, emptyLineIsWord) {
    var lineNum = cur.line;
    var pos = cur.ch;
    var line = cm.getLine(lineNum);
    var dir = forward ? 1 : -1;
    var charTests = bigWord ? bigWordCharTest : wordCharTest;
    if (emptyLineIsWord && line == '') {
        lineNum += dir;
        line = cm.getLine(lineNum);
        if (!isLine(cm, lineNum)) {
            return null;
        }
        pos = (forward) ? 0 : line.length;
    }
    while (true) {
        if (emptyLineIsWord && line == '') {
            return { from: 0, to: 0, line: lineNum };
        }
        var stop = (dir > 0) ? line.length : -1;
        var wordStart = stop, wordEnd = stop;
        while (pos != stop) {
            var foundWord = false;
            for (var i = 0; i < charTests.length && !foundWord; ++i) {
                if (charTests[i](line.charAt(pos))) {
                    wordStart = pos;
                    while (pos != stop && charTests[i](line.charAt(pos))) {
                        pos += dir;
                    }
                    wordEnd = pos;
                    foundWord = wordStart != wordEnd;
                    if (wordStart == cur.ch && lineNum == cur.line &&
                        wordEnd == wordStart + dir) {
                        continue;
                    }
                    else {
                        return {
                            from: Math.min(wordStart, wordEnd + 1),
                            to: Math.max(wordStart, wordEnd),
                            line: lineNum
                        };
                    }
                }
            }
            if (!foundWord) {
                pos += dir;
            }
        }
        lineNum += dir;
        if (!isLine(cm, lineNum)) {
            return null;
        }
        line = cm.getLine(lineNum);
        pos = (dir > 0) ? 0 : line.length;
    }
}
function moveToWord(cm, cur, repeat, forward, wordEnd, bigWord) {
    var curStart = copyCursor(cur);
    var words = [];
    if (forward && !wordEnd || !forward && wordEnd) {
        repeat++;
    }
    var emptyLineIsWord = !(forward && wordEnd);
    for (var i = 0; i < repeat; i++) {
        var word = findWord(cm, cur, forward, bigWord, emptyLineIsWord);
        if (!word) {
            var eodCh = lineLength(cm, cm.lastLine());
            words.push(forward
                ? { line: cm.lastLine(), from: eodCh, to: eodCh }
                : { line: 0, from: 0, to: 0 });
            break;
        }
        words.push(word);
        cur = new Pos(word.line, forward ? (word.to - 1) : word.from);
    }
    var shortCircuit = words.length != repeat;
    var firstWord = words[0];
    var lastWord = words.pop();
    if (forward && !wordEnd) {
        if (!shortCircuit && (firstWord.from != curStart.ch || firstWord.line != curStart.line)) {
            lastWord = words.pop();
        }
        return new Pos(lastWord.line, lastWord.from);
    }
    else if (forward && wordEnd) {
        return new Pos(lastWord.line, lastWord.to - 1);
    }
    else if (!forward && wordEnd) {
        if (!shortCircuit && (firstWord.to != curStart.ch || firstWord.line != curStart.line)) {
            lastWord = words.pop();
        }
        return new Pos(lastWord.line, lastWord.to);
    }
    else {
        return new Pos(lastWord.line, lastWord.from);
    }
}
function moveToEol(cm, head, motionArgs, vim, keepHPos) {
    var cur = head;
    var retval = new Pos(cur.line + motionArgs.repeat - 1, Infinity);
    var end = cm.clipPos(retval);
    end.ch--;
    if (!keepHPos) {
        vim.lastHPos = Infinity;
        vim.lastHSPos = cm.charCoords(end, 'div').left;
    }
    return retval;
}
function moveToCharacter(cm, repeat, forward, character, head) {
    var cur = head || cm.getCursor();
    var start = cur.ch;
    var idx;
    for (var i = 0; i < repeat; i++) {
        var line = cm.getLine(cur.line);
        idx = charIdxInLine(start, line, character, forward, true);
        if (idx == -1) {
            return null;
        }
        start = idx;
    }
    return new Pos(cm.getCursor().line, idx);
}
function moveToColumn(cm, repeat) {
    var line = cm.getCursor().line;
    return clipCursorToContent(cm, new Pos(line, repeat - 1));
}
function updateMark(cm, vim, markName, pos) {
    if (!inArray(markName, validMarks) && !latinCharRegex.test(markName)) {
        return;
    }
    if (vim.marks[markName]) {
        vim.marks[markName].clear();
    }
    vim.marks[markName] = cm.setBookmark(pos);
}
function charIdxInLine(start, line, character, forward, includeChar) {
    var idx;
    if (forward) {
        idx = line.indexOf(character, start + 1);
        if (idx != -1 && !includeChar) {
            idx -= 1;
        }
    }
    else {
        idx = line.lastIndexOf(character, start - 1);
        if (idx != -1 && !includeChar) {
            idx += 1;
        }
    }
    return idx;
}
function findParagraph(cm, head, repeat, dir, inclusive) {
    var line = head.line;
    var min = cm.firstLine();
    var max = cm.lastLine();
    var start, end, i = line;
    function isEmpty(i) { return !/\S/.test(cm.getLine(i)); } // ace_patch
    function isBoundary(i, dir, any) {
        if (any) {
            return isEmpty(i) != isEmpty(i + dir);
        }
        return !isEmpty(i) && isEmpty(i + dir);
    }
    function skipFold(i) {
        dir = dir > 0 ? 1 : -1;
        var foldLine = cm.ace.session.getFoldLine(i);
        if (foldLine) {
            if (i + dir > foldLine.start.row && i + dir < foldLine.end.row)
                dir = (dir > 0 ? foldLine.end.row : foldLine.start.row) - i;
        }
    }
    if (dir) {
        while (min <= i && i <= max && repeat > 0) {
            skipFold(i);
            if (isBoundary(i, dir)) {
                repeat--;
            }
            i += dir;
        }
        return new Pos(i, 0);
    }
    var vim = cm.state.vim;
    if (vim.visualLine && isBoundary(line, 1, true)) {
        var anchor = vim.sel.anchor;
        if (isBoundary(anchor.line, -1, true)) {
            if (!inclusive || anchor.line != line) {
                line += 1;
            }
        }
    }
    var startState = isEmpty(line);
    for (i = line; i <= max && repeat; i++) {
        if (isBoundary(i, 1, true)) {
            if (!inclusive || isEmpty(i) != startState) {
                repeat--;
            }
        }
    }
    end = new Pos(i, 0);
    if (i > max && !startState) {
        startState = true;
    }
    else {
        inclusive = false;
    }
    for (i = line; i > min; i--) {
        if (!inclusive || isEmpty(i) == startState || i == line) {
            if (isBoundary(i, -1, true)) {
                break;
            }
        }
    }
    start = new Pos(i, 0);
    return { start: start, end: end };
}
function getSentence(cm, cur, repeat, dir, inclusive /*includes whitespace*/) {
    function nextChar(curr) {
        if (curr.pos + curr.dir < 0 || curr.pos + curr.dir >= curr.line.length) {
            curr.line = null;
        }
        else {
            curr.pos += curr.dir;
        }
    }
    function forward(cm, ln, pos, dir) {
        var line = cm.getLine(ln);
        var curr = {
            line: line,
            ln: ln,
            pos: pos,
            dir: dir,
        };
        if (curr.line === "") {
            return { ln: curr.ln, pos: curr.pos };
        }
        var lastSentencePos = curr.pos;
        nextChar(curr);
        while (curr.line !== null) {
            lastSentencePos = curr.pos;
            if (isEndOfSentenceSymbol(curr.line[curr.pos])) {
                if (!inclusive) {
                    return { ln: curr.ln, pos: curr.pos + 1 };
                }
                else {
                    nextChar(curr);
                    while (curr.line !== null) {
                        if (isWhiteSpaceString(curr.line[curr.pos])) {
                            lastSentencePos = curr.pos;
                            nextChar(curr);
                        }
                        else {
                            break;
                        }
                    }
                    return { ln: curr.ln, pos: lastSentencePos + 1 };
                }
            }
            nextChar(curr);
        }
        return { ln: curr.ln, pos: lastSentencePos + 1 };
    }
    function reverse(cm, ln, pos, dir) {
        var line = cm.getLine(ln);
        var curr = {
            line: line,
            ln: ln,
            pos: pos,
            dir: dir,
        };
        if (curr.line === "") {
            return { ln: curr.ln, pos: curr.pos };
        }
        var lastSentencePos = curr.pos;
        nextChar(curr);
        while (curr.line !== null) {
            if (!isWhiteSpaceString(curr.line[curr.pos]) && !isEndOfSentenceSymbol(curr.line[curr.pos])) {
                lastSentencePos = curr.pos;
            }
            else if (isEndOfSentenceSymbol(curr.line[curr.pos])) {
                if (!inclusive) {
                    return { ln: curr.ln, pos: lastSentencePos };
                }
                else {
                    if (isWhiteSpaceString(curr.line[curr.pos + 1])) {
                        return { ln: curr.ln, pos: curr.pos + 1 };
                    }
                    else {
                        return { ln: curr.ln, pos: lastSentencePos };
                    }
                }
            }
            nextChar(curr);
        }
        curr.line = line;
        if (inclusive && isWhiteSpaceString(curr.line[curr.pos])) {
            return { ln: curr.ln, pos: curr.pos };
        }
        else {
            return { ln: curr.ln, pos: lastSentencePos };
        }
    }
    var curr_index = {
        ln: cur.line,
        pos: cur.ch,
    };
    while (repeat > 0) {
        if (dir < 0) {
            curr_index = reverse(cm, curr_index.ln, curr_index.pos, dir);
        }
        else {
            curr_index = forward(cm, curr_index.ln, curr_index.pos, dir);
        }
        repeat--;
    }
    return new Pos(curr_index.ln, curr_index.pos);
}
function findSentence(cm, cur, repeat, dir) {
    function nextChar(cm, idx) {
        if (idx.pos + idx.dir < 0 || idx.pos + idx.dir >= idx.line.length) {
            idx.ln += idx.dir;
            if (!isLine(cm, idx.ln)) {
                idx.line = null;
                idx.ln = null;
                idx.pos = null;
                return;
            }
            idx.line = cm.getLine(idx.ln);
            idx.pos = (idx.dir > 0) ? 0 : idx.line.length - 1;
        }
        else {
            idx.pos += idx.dir;
        }
    }
    function forward(cm, ln, pos, dir) {
        var line = cm.getLine(ln);
        var stop = (line === "");
        var curr = {
            line: line,
            ln: ln,
            pos: pos,
            dir: dir,
        };
        var last_valid = {
            ln: curr.ln,
            pos: curr.pos,
        };
        var skip_empty_lines = (curr.line === "");
        nextChar(cm, curr);
        while (curr.line !== null) {
            last_valid.ln = curr.ln;
            last_valid.pos = curr.pos;
            if (curr.line === "" && !skip_empty_lines) {
                return { ln: curr.ln, pos: curr.pos, };
            }
            else if (stop && curr.line !== "" && !isWhiteSpaceString(curr.line[curr.pos])) {
                return { ln: curr.ln, pos: curr.pos, };
            }
            else if (isEndOfSentenceSymbol(curr.line[curr.pos])
                && !stop
                && (curr.pos === curr.line.length - 1
                    || isWhiteSpaceString(curr.line[curr.pos + 1]))) {
                stop = true;
            }
            nextChar(cm, curr);
        }
        var line = cm.getLine(last_valid.ln);
        last_valid.pos = 0;
        for (var i = line.length - 1; i >= 0; --i) {
            if (!isWhiteSpaceString(line[i])) {
                last_valid.pos = i;
                break;
            }
        }
        return last_valid;
    }
    function reverse(cm, ln, pos, dir) {
        var line = cm.getLine(ln);
        var curr = {
            line: line,
            ln: ln,
            pos: pos,
            dir: dir,
        };
        var last_valid = {
            ln: curr.ln,
            pos: null,
        };
        var skip_empty_lines = (curr.line === "");
        nextChar(cm, curr);
        while (curr.line !== null) {
            if (curr.line === "" && !skip_empty_lines) {
                if (last_valid.pos !== null) {
                    return last_valid;
                }
                else {
                    return { ln: curr.ln, pos: curr.pos };
                }
            }
            else if (isEndOfSentenceSymbol(curr.line[curr.pos])
                && last_valid.pos !== null
                && !(curr.ln === last_valid.ln && curr.pos + 1 === last_valid.pos)) {
                return last_valid;
            }
            else if (curr.line !== "" && !isWhiteSpaceString(curr.line[curr.pos])) {
                skip_empty_lines = false;
                last_valid = { ln: curr.ln, pos: curr.pos };
            }
            nextChar(cm, curr);
        }
        var line = cm.getLine(last_valid.ln);
        last_valid.pos = 0;
        for (var i = 0; i < line.length; ++i) {
            if (!isWhiteSpaceString(line[i])) {
                last_valid.pos = i;
                break;
            }
        }
        return last_valid;
    }
    var curr_index = {
        ln: cur.line,
        pos: cur.ch,
    };
    while (repeat > 0) {
        if (dir < 0) {
            curr_index = reverse(cm, curr_index.ln, curr_index.pos, dir);
        }
        else {
            curr_index = forward(cm, curr_index.ln, curr_index.pos, dir);
        }
        repeat--;
    }
    return new Pos(curr_index.ln, curr_index.pos);
}
function selectCompanionObject(cm, head, symb, inclusive) {
    var cur = head, start, end;
    var bracketRegexp = ({
        '(': /[()]/, ')': /[()]/,
        '[': /[[\]]/, ']': /[[\]]/,
        '{': /[{}]/, '}': /[{}]/,
        '<': /[<>]/, '>': /[<>]/
    })[symb];
    var openSym = ({
        '(': '(', ')': '(',
        '[': '[', ']': '[',
        '{': '{', '}': '{',
        '<': '<', '>': '<'
    })[symb];
    var curChar = cm.getLine(cur.line).charAt(cur.ch);
    var offset = curChar === openSym ? 1 : 0;
    start = cm.scanForBracket(new Pos(cur.line, cur.ch + offset), -1, undefined, { 'bracketRegex': bracketRegexp });
    end = cm.scanForBracket(new Pos(cur.line, cur.ch + offset), 1, undefined, { 'bracketRegex': bracketRegexp });
    if (!start || !end)
        return null;
    start = start.pos;
    end = end.pos;
    if ((start.line == end.line && start.ch > end.ch)
        || (start.line > end.line)) {
        var tmp = start;
        start = end;
        end = tmp;
    }
    if (inclusive) {
        end.ch += 1;
    }
    else {
        start.ch += 1;
    }
    return { start: start, end: end };
}
function findBeginningAndEnd(cm, head, symb, inclusive) {
    var cur = copyCursor(head);
    var line = cm.getLine(cur.line);
    var chars = line.split('');
    var start, end, i, len;
    var firstIndex = chars.indexOf(symb);
    if (cur.ch < firstIndex) {
        cur.ch = firstIndex;
    }
    else if (firstIndex < cur.ch && chars[cur.ch] == symb) {
        var stringAfter = /string/.test(cm.getTokenTypeAt(offsetCursor(head, 0, 1)));
        var stringBefore = /string/.test(cm.getTokenTypeAt(head));
        var isStringStart = stringAfter && !stringBefore;
        if (!isStringStart) {
            end = cur.ch; // assign end to the current cursor
            --cur.ch; // make sure to look backwards
        }
    }
    if (chars[cur.ch] == symb && !end) {
        start = cur.ch + 1; // assign start to ahead of the cursor
    }
    else {
        for (i = cur.ch; i > -1 && !start; i--) {
            if (chars[i] == symb) {
                start = i + 1;
            }
        }
    }
    if (start && !end) {
        for (i = start, len = chars.length; i < len && !end; i++) {
            if (chars[i] == symb) {
                end = i;
            }
        }
    }
    if (!start || !end) {
        return { start: cur, end: cur };
    }
    if (inclusive) {
        --start;
        ++end;
    }
    return {
        start: new Pos(cur.line, start),
        end: new Pos(cur.line, end)
    };
}
defineOption('pcre', true, 'boolean');
function SearchState() { }
SearchState.prototype = {
    getQuery: function () {
        return vimGlobalState.query;
    },
    setQuery: function (query) {
        vimGlobalState.query = query;
    },
    getOverlay: function () {
        return this.searchOverlay;
    },
    setOverlay: function (overlay) {
        this.searchOverlay = overlay;
    },
    isReversed: function () {
        return vimGlobalState.isReversed;
    },
    setReversed: function (reversed) {
        vimGlobalState.isReversed = reversed;
    },
    getScrollbarAnnotate: function () {
        return this.annotate;
    },
    setScrollbarAnnotate: function (annotate) {
        this.annotate = annotate;
    }
};
function getSearchState(cm) {
    var vim = cm.state.vim;
    return vim.searchState_ || (vim.searchState_ = new SearchState());
}
function splitBySlash(argString) {
    return splitBySeparator(argString, '/');
}
function findUnescapedSlashes(argString) {
    return findUnescapedSeparators(argString, '/');
}
function splitBySeparator(argString, separator) {
    var slashes = findUnescapedSeparators(argString, separator) || [];
    if (!slashes.length)
        return [];
    var tokens = [];
    if (slashes[0] !== 0)
        return;
    for (var i = 0; i < slashes.length; i++) {
        if (typeof slashes[i] == 'number')
            tokens.push(argString.substring(slashes[i] + 1, slashes[i + 1]));
    }
    return tokens;
}
function findUnescapedSeparators(str, separator) {
    if (!separator)
        separator = '/';
    var escapeNextChar = false;
    var slashes = [];
    for (var i = 0; i < str.length; i++) {
        var c = str.charAt(i);
        if (!escapeNextChar && c == separator) {
            slashes.push(i);
        }
        escapeNextChar = !escapeNextChar && (c == '\\');
    }
    return slashes;
}
function translateRegex(str) {
    var specials = '|(){';
    var unescape = '}';
    var escapeNextChar = false;
    var out = [];
    for (var i = -1; i < str.length; i++) {
        var c = str.charAt(i) || '';
        var n = str.charAt(i + 1) || '';
        var specialComesNext = (n && specials.indexOf(n) != -1);
        if (escapeNextChar) {
            if (c !== '\\' || !specialComesNext) {
                out.push(c);
            }
            escapeNextChar = false;
        }
        else {
            if (c === '\\') {
                escapeNextChar = true;
                if (n && unescape.indexOf(n) != -1) {
                    specialComesNext = true;
                }
                if (!specialComesNext || n === '\\') {
                    out.push(c);
                }
            }
            else {
                out.push(c);
                if (specialComesNext && n !== '\\') {
                    out.push('\\');
                }
            }
        }
    }
    return out.join('');
}
var charUnescapes = { '\\n': '\n', '\\r': '\r', '\\t': '\t' };
function translateRegexReplace(str) {
    var escapeNextChar = false;
    var out = [];
    for (var i = -1; i < str.length; i++) {
        var c = str.charAt(i) || '';
        var n = str.charAt(i + 1) || '';
        if (charUnescapes[c + n]) {
            out.push(charUnescapes[c + n]);
            i++;
        }
        else if (escapeNextChar) {
            out.push(c);
            escapeNextChar = false;
        }
        else {
            if (c === '\\') {
                escapeNextChar = true;
                if ((isNumber(n) || n === '$')) {
                    out.push('$');
                }
                else if (n !== '/' && n !== '\\') {
                    out.push('\\');
                }
            }
            else {
                if (c === '$') {
                    out.push('$');
                }
                out.push(c);
                if (n === '/') {
                    out.push('\\');
                }
            }
        }
    }
    return out.join('');
}
var unescapes = { '\\/': '/', '\\\\': '\\', '\\n': '\n', '\\r': '\r', '\\t': '\t', '\\&': '&' };
function unescapeRegexReplace(str) {
    var stream = new CodeMirror.StringStream(str);
    var output = [];
    while (!stream.eol()) {
        while (stream.peek() && stream.peek() != '\\') {
            output.push(stream.next());
        }
        var matched = false;
        for (var matcher in unescapes) {
            if (stream.match(matcher, true)) {
                matched = true;
                output.push(unescapes[matcher]);
                break;
            }
        }
        if (!matched) {
            output.push(stream.next());
        }
    }
    return output.join('');
}
function parseQuery(query, ignoreCase, smartCase) {
    var lastSearchRegister = vimGlobalState.registerController.getRegister('/');
    lastSearchRegister.setText(query);
    if (query instanceof RegExp) {
        return query;
    }
    var slashes = findUnescapedSlashes(query);
    var regexPart;
    var forceIgnoreCase;
    if (!slashes.length) {
        regexPart = query;
    }
    else {
        regexPart = query.substring(0, slashes[0]);
        var flagsPart = query.substring(slashes[0]);
        forceIgnoreCase = (flagsPart.indexOf('i') != -1);
    }
    if (!regexPart) {
        return null;
    }
    if (!getOption('pcre')) {
        regexPart = translateRegex(regexPart);
    }
    if (smartCase) {
        ignoreCase = (/^[^A-Z]*$/).test(regexPart);
    }
    var regexp = new RegExp(regexPart, (ignoreCase || forceIgnoreCase) ? 'im' : 'm');
    return regexp;
}
function dom(n) {
    if (typeof n === 'string')
        n = document.createElement(n);
    for (var a, i = 1; i < arguments.length; i++) {
        if (!(a = arguments[i]))
            continue;
        if (typeof a !== 'object')
            a = document.createTextNode(a);
        if (a.nodeType)
            n.appendChild(a);
        else
            for (var key in a) {
                if (!Object.prototype.hasOwnProperty.call(a, key))
                    continue;
                if (key[0] === '$')
                    n.style[key.slice(1)] = a[key];
                else
                    n.setAttribute(key, a[key]);
            }
    }
    return n;
}
function showConfirm(cm, template) {
    var pre = dom('div', { $color: 'red', $whiteSpace: 'pre', class: 'cm-vim-message' }, template);
    if (cm.openNotification) {
        cm.openNotification(pre, { bottom: true, duration: 5000 });
    }
    else {
        alert(pre.innerText);
    }
}
function makePrompt(prefix, desc) {
    return dom('div', { $display: 'flex' }, dom('span', { $fontFamily: 'monospace', $whiteSpace: 'pre', $flex: 1 }, prefix, dom('input', { type: 'text', autocorrect: 'off',
        autocapitalize: 'off', spellcheck: 'false', $width: '100%' })), desc && dom('span', { $color: '#888' }, desc));
}
function showPrompt(cm, options) {
    if (keyToKeyStack.length) {
        if (!options.value)
            options.value = '';
        virtualPrompt = options;
        return;
    }
    var template = makePrompt(options.prefix, options.desc);
    if (cm.openDialog) {
        cm.openDialog(template, options.onClose, {
            onKeyDown: options.onKeyDown, onKeyUp: options.onKeyUp,
            bottom: true, selectValueOnOpen: false, value: options.value
        });
    }
    else {
        var shortText = '';
        if (typeof options.prefix != "string" && options.prefix)
            shortText += options.prefix.textContent;
        if (options.desc)
            shortText += " " + options.desc;
        options.onClose(prompt(shortText, ''));
    }
}
function regexEqual(r1, r2) {
    if (r1 instanceof RegExp && r2 instanceof RegExp) {
        var props = ['global', 'multiline', 'ignoreCase', 'source'];
        for (var i = 0; i < props.length; i++) {
            var prop = props[i];
            if (r1[prop] !== r2[prop]) {
                return false;
            }
        }
        return true;
    }
    return false;
}
function updateSearchQuery(cm, rawQuery, ignoreCase, smartCase) {
    if (!rawQuery) {
        return;
    }
    var state = getSearchState(cm);
    var query = parseQuery(rawQuery, !!ignoreCase, !!smartCase);
    if (!query) {
        return;
    }
    highlightSearchMatches(cm, query);
    if (regexEqual(query, state.getQuery())) {
        return query;
    }
    state.setQuery(query);
    return query;
}
function searchOverlay(query) {
    if (query.source.charAt(0) == '^') {
        var matchSol = true;
    }
    return {
        token: function (stream) {
            if (matchSol && !stream.sol()) {
                stream.skipToEnd();
                return;
            }
            var match = stream.match(query, false);
            if (match) {
                if (match[0].length == 0) {
                    stream.next();
                    return 'searching';
                }
                if (!stream.sol()) {
                    stream.backUp(1);
                    if (!query.exec(stream.next() + match[0])) {
                        stream.next();
                        return null;
                    }
                }
                stream.match(query);
                return 'searching';
            }
            while (!stream.eol()) {
                stream.next();
                if (stream.match(query, false))
                    break;
            }
        },
        query: query
    };
}
var highlightTimeout = 0;
function highlightSearchMatches(cm, query) {
    clearTimeout(highlightTimeout);
    var searchState = getSearchState(cm);
    searchState.highlightTimeout = highlightTimeout;
    highlightTimeout = setTimeout(function () {
        if (!cm.state.vim)
            return;
        var searchState = getSearchState(cm);
        searchState.highlightTimeout = null;
        var overlay = searchState.getOverlay();
        if (!overlay || query != overlay.query) {
            if (overlay) {
                cm.removeOverlay(overlay);
            }
            overlay = searchOverlay(query);
            cm.addOverlay(overlay);
            if (cm.showMatchesOnScrollbar) {
                if (searchState.getScrollbarAnnotate()) {
                    searchState.getScrollbarAnnotate().clear();
                }
                searchState.setScrollbarAnnotate(cm.showMatchesOnScrollbar(query));
            }
            searchState.setOverlay(overlay);
        }
    }, 50);
}
function findNext(cm, prev, query, repeat) {
    if (repeat === undefined) {
        repeat = 1;
    }
    return cm.operation(function () {
        var pos = cm.getCursor();
        var cursor = cm.getSearchCursor(query, pos);
        for (var i = 0; i < repeat; i++) {
            var found = cursor.find(prev);
            if (i == 0 && found && cursorEqual(cursor.from(), pos)) {
                var lastEndPos = prev ? cursor.from() : cursor.to();
                found = cursor.find(prev);
                if (found && !found[0] && cursorEqual(cursor.from(), lastEndPos)) {
                    if (cm.getLine(lastEndPos.line).length == lastEndPos.ch)
                        found = cursor.find(prev);
                }
            }
            if (!found) {
                cursor = cm.getSearchCursor(query, (prev) ? new Pos(cm.lastLine()) : new Pos(cm.firstLine(), 0));
                if (!cursor.find(prev)) {
                    return;
                }
            }
        }
        return cursor.from();
    });
}
function findNextFromAndToInclusive(cm, prev, query, repeat, vim) {
    if (repeat === undefined) {
        repeat = 1;
    }
    return cm.operation(function () {
        var pos = cm.getCursor();
        var cursor = cm.getSearchCursor(query, pos);
        var found = cursor.find(!prev);
        if (!vim.visualMode && found && cursorEqual(cursor.from(), pos)) {
            cursor.find(!prev);
        }
        for (var i = 0; i < repeat; i++) {
            found = cursor.find(prev);
            if (!found) {
                cursor = cm.getSearchCursor(query, (prev) ? new Pos(cm.lastLine()) : new Pos(cm.firstLine(), 0));
                if (!cursor.find(prev)) {
                    return;
                }
            }
        }
        return [cursor.from(), cursor.to()];
    });
}
function clearSearchHighlight(cm) {
    var state = getSearchState(cm);
    if (state.highlightTimeout) {
        clearTimeout(state.highlightTimeout);
        state.highlightTimeout = null;
    }
    cm.removeOverlay(getSearchState(cm).getOverlay());
    state.setOverlay(null);
    if (state.getScrollbarAnnotate()) {
        state.getScrollbarAnnotate().clear();
        state.setScrollbarAnnotate(null);
    }
}
function isInRange(pos, start, end) {
    if (typeof pos != 'number') {
        pos = pos.line;
    }
    if (start instanceof Array) {
        return inArray(pos, start);
    }
    else {
        if (typeof end == 'number') {
            return (pos >= start && pos <= end);
        }
        else {
            return pos == start;
        }
    }
}
function getUserVisibleLines(cm) {
    var renderer = cm.ace.renderer;
    return {
        top: renderer.getFirstFullyVisibleRow(),
        bottom: renderer.getLastFullyVisibleRow()
    };
}
function getMarkPos(cm, vim, markName) {
    if (markName == '\'' || markName == '`') {
        return vimGlobalState.jumpList.find(cm, -1) || new Pos(0, 0);
    }
    else if (markName == '.') {
        return getLastEditPos(cm);
    }
    var mark = vim.marks[markName];
    return mark && mark.find();
}
function getLastEditPos(cm) {
    if (cm.getLastEditEnd) {
        return cm.getLastEditEnd();
    }
    var done = cm.doc.history.done;
    for (var i = done.length; i--;) {
        if (done[i].changes) {
            return copyCursor(done[i].changes[0].to);
        }
    }
}
var ExCommandDispatcher = function () {
    this.buildCommandMap_();
};
ExCommandDispatcher.prototype = {
    processCommand: function (cm, input, opt_params) {
        var that = this;
        cm.operation(function () {
            cm.curOp.isVimOp = true;
            that._processCommand(cm, input, opt_params);
        });
    },
    _processCommand: function (cm, input, opt_params) {
        var vim = cm.state.vim;
        var commandHistoryRegister = vimGlobalState.registerController.getRegister(':');
        var previousCommand = commandHistoryRegister.toString();
        var inputStream = new CodeMirror.StringStream(input);
        commandHistoryRegister.setText(input);
        var params = opt_params || {};
        params.input = input;
        try {
            this.parseInput_(cm, inputStream, params);
        }
        catch (e) {
            showConfirm(cm, e.toString());
            throw e;
        }
        if (vim.visualMode) {
            exitVisualMode(cm);
        }
        var command;
        var commandName;
        if (!params.commandName) {
            if (params.line !== undefined) {
                commandName = 'move';
            }
        }
        else {
            command = this.matchCommand_(params.commandName);
            if (command) {
                commandName = command.name;
                if (command.excludeFromCommandHistory) {
                    commandHistoryRegister.setText(previousCommand);
                }
                this.parseCommandArgs_(inputStream, params, command);
                if (command.type == 'exToKey') {
                    doKeyToKey(cm, command.toKeys, command);
                    return;
                }
                else if (command.type == 'exToEx') {
                    this.processCommand(cm, command.toInput);
                    return;
                }
            }
        }
        if (!commandName) {
            showConfirm(cm, 'Not an editor command ":' + input + '"');
            return;
        }
        try {
            exCommands[commandName](cm, params);
            if ((!command || !command.possiblyAsync) && params.callback) {
                params.callback();
            }
        }
        catch (e) {
            showConfirm(cm, e.toString());
            throw e;
        }
    },
    parseInput_: function (cm, inputStream, result) {
        inputStream.eatWhile(':');
        if (inputStream.eat('%')) {
            result.line = cm.firstLine();
            result.lineEnd = cm.lastLine();
        }
        else {
            result.line = this.parseLineSpec_(cm, inputStream);
            if (result.line !== undefined && inputStream.eat(',')) {
                result.lineEnd = this.parseLineSpec_(cm, inputStream);
            }
        }
        if (result.line == undefined) {
            if (cm.state.vim.visualMode) {
                var pos = getMarkPos(cm, cm.state.vim, '<');
                result.selectionLine = pos && pos.line;
                pos = getMarkPos(cm, cm.state.vim, '>');
                result.selectionLineEnd = pos && pos.line;
            }
            else {
                result.selectionLine = cm.getCursor().line;
            }
        }
        else {
            result.selectionLine = result.line;
            result.selectionLineEnd = result.lineEnd;
        }
        var commandMatch = inputStream.match(/^(\w+|!!|@@|[!#&*<=>@~])/);
        if (commandMatch) {
            result.commandName = commandMatch[1];
        }
        else {
            result.commandName = inputStream.match(/.*/)[0];
        }
        return result;
    },
    parseLineSpec_: function (cm, inputStream) {
        var numberMatch = inputStream.match(/^(\d+)/);
        if (numberMatch) {
            return parseInt(numberMatch[1], 10) - 1;
        }
        switch (inputStream.next()) {
            case '.':
                return this.parseLineSpecOffset_(inputStream, cm.getCursor().line);
            case '$':
                return this.parseLineSpecOffset_(inputStream, cm.lastLine());
            case '\'':
                var markName = inputStream.next();
                var markPos = getMarkPos(cm, cm.state.vim, markName);
                if (!markPos)
                    throw new Error('Mark not set');
                return this.parseLineSpecOffset_(inputStream, markPos.line);
            case '-':
            case '+':
                inputStream.backUp(1);
                return this.parseLineSpecOffset_(inputStream, cm.getCursor().line);
            default:
                inputStream.backUp(1);
                return undefined;
        }
    },
    parseLineSpecOffset_: function (inputStream, line) {
        var offsetMatch = inputStream.match(/^([+-])?(\d+)/);
        if (offsetMatch) {
            var offset = parseInt(offsetMatch[2], 10);
            if (offsetMatch[1] == "-") {
                line -= offset;
            }
            else {
                line += offset;
            }
        }
        return line;
    },
    parseCommandArgs_: function (inputStream, params, command) {
        if (inputStream.eol()) {
            return;
        }
        params.argString = inputStream.match(/.*/)[0];
        var delim = command.argDelimiter || /\s+/;
        var args = trim(params.argString).split(delim);
        if (args.length && args[0]) {
            params.args = args;
        }
    },
    matchCommand_: function (commandName) {
        for (var i = commandName.length; i > 0; i--) {
            var prefix = commandName.substring(0, i);
            if (this.commandMap_[prefix]) {
                var command = this.commandMap_[prefix];
                if (command.name.indexOf(commandName) === 0) {
                    return command;
                }
            }
        }
        return null;
    },
    buildCommandMap_: function () {
        this.commandMap_ = {};
        for (var i = 0; i < defaultExCommandMap.length; i++) {
            var command = defaultExCommandMap[i];
            var key = command.shortName || command.name;
            this.commandMap_[key] = command;
        }
    },
    map: function (lhs, rhs, ctx, noremap) {
        if (lhs != ':' && lhs.charAt(0) == ':') {
            if (ctx) {
                throw Error('Mode not supported for ex mappings');
            }
            var commandName = lhs.substring(1);
            if (rhs != ':' && rhs.charAt(0) == ':') {
                this.commandMap_[commandName] = {
                    name: commandName,
                    type: 'exToEx',
                    toInput: rhs.substring(1),
                    user: true
                };
            }
            else {
                this.commandMap_[commandName] = {
                    name: commandName,
                    type: 'exToKey',
                    toKeys: rhs,
                    user: true
                };
            }
        }
        else {
            var mapping = {
                keys: lhs,
                type: 'keyToKey',
                toKeys: rhs,
                noremap: !!noremap
            };
            if (ctx) {
                mapping.context = ctx;
            }
            defaultKeymap.unshift(mapping);
        }
    },
    unmap: function (lhs, ctx) {
        if (lhs != ':' && lhs.charAt(0) == ':') {
            if (ctx) {
                throw Error('Mode not supported for ex mappings');
            }
            var commandName = lhs.substring(1);
            if (this.commandMap_[commandName] && this.commandMap_[commandName].user) {
                delete this.commandMap_[commandName];
                return true;
            }
        }
        else {
            var keys = lhs;
            for (var i = 0; i < defaultKeymap.length; i++) {
                if (keys == defaultKeymap[i].keys
                    && defaultKeymap[i].context === ctx) {
                    defaultKeymap.splice(i, 1);
                    return true;
                }
            }
        }
    }
};
var exCommands = {
    colorscheme: function (cm, params) {
        if (!params.args || params.args.length < 1) {
            showConfirm(cm, cm.getOption('theme'));
            return;
        }
        cm.setOption('theme', params.args[0]);
    },
    map: function (cm, params, ctx, defaultOnly) {
        var mapArgs = params.args;
        if (!mapArgs || mapArgs.length < 2) {
            if (cm) {
                showConfirm(cm, 'Invalid mapping: ' + params.input);
            }
            return;
        }
        exCommandDispatcher.map(mapArgs[0], mapArgs[1], ctx, defaultOnly);
    },
    imap: function (cm, params) { this.map(cm, params, 'insert'); },
    nmap: function (cm, params) { this.map(cm, params, 'normal'); },
    vmap: function (cm, params) { this.map(cm, params, 'visual'); },
    omap: function (cm, params) { this.map(cm, params, 'operatorPending'); },
    noremap: function (cm, params) { this.map(cm, params, undefined, true); },
    inoremap: function (cm, params) { this.map(cm, params, 'insert', true); },
    nnoremap: function (cm, params) { this.map(cm, params, 'normal', true); },
    vnoremap: function (cm, params) { this.map(cm, params, 'visual', true); },
    onoremap: function (cm, params) { this.map(cm, params, 'operatorPending', true); },
    unmap: function (cm, params, ctx) {
        var mapArgs = params.args;
        if (!mapArgs || mapArgs.length < 1 || !exCommandDispatcher.unmap(mapArgs[0], ctx)) {
            if (cm) {
                showConfirm(cm, 'No such mapping: ' + params.input);
            }
        }
    },
    mapclear: function (cm, params) { vimApi.mapclear(); },
    imapclear: function (cm, params) { vimApi.mapclear('insert'); },
    nmapclear: function (cm, params) { vimApi.mapclear('normal'); },
    vmapclear: function (cm, params) { vimApi.mapclear('visual'); },
    omapclear: function (cm, params) { vimApi.mapclear('operatorPending'); },
    move: function (cm, params) {
        commandDispatcher.processCommand(cm, cm.state.vim, {
            type: 'motion',
            motion: 'moveToLineOrEdgeOfDocument',
            motionArgs: { forward: false, explicitRepeat: true,
                linewise: true },
            repeatOverride: params.line + 1
        });
    },
    set: function (cm, params) {
        var setArgs = params.args;
        var setCfg = params.setCfg || {};
        if (!setArgs || setArgs.length < 1) {
            if (cm) {
                showConfirm(cm, 'Invalid mapping: ' + params.input);
            }
            return;
        }
        var expr = setArgs[0].split('=');
        var optionName = expr[0];
        var value = expr[1];
        var forceGet = false;
        var forceToggle = false;
        if (optionName.charAt(optionName.length - 1) == '?') {
            if (value) {
                throw Error('Trailing characters: ' + params.argString);
            }
            optionName = optionName.substring(0, optionName.length - 1);
            forceGet = true;
        }
        else if (optionName.charAt(optionName.length - 1) == '!') {
            optionName = optionName.substring(0, optionName.length - 1);
            forceToggle = true;
        }
        if (value === undefined && optionName.substring(0, 2) == 'no') {
            optionName = optionName.substring(2);
            value = false;
        }
        var optionIsBoolean = options[optionName] && options[optionName].type == 'boolean';
        if (optionIsBoolean) {
            if (forceToggle) {
                value = !getOption(optionName, cm, setCfg);
            }
            else if (value == undefined) {
                value = true;
            }
        }
        if (!optionIsBoolean && value === undefined || forceGet) {
            var oldValue = getOption(optionName, cm, setCfg);
            if (oldValue instanceof Error) {
                showConfirm(cm, oldValue.message);
            }
            else if (oldValue === true || oldValue === false) {
                showConfirm(cm, ' ' + (oldValue ? '' : 'no') + optionName);
            }
            else {
                showConfirm(cm, '  ' + optionName + '=' + oldValue);
            }
        }
        else {
            var setOptionReturn = setOption(optionName, value, cm, setCfg);
            if (setOptionReturn instanceof Error) {
                showConfirm(cm, setOptionReturn.message);
            }
        }
    },
    setlocal: function (cm, params) {
        params.setCfg = { scope: 'local' };
        this.set(cm, params);
    },
    setglobal: function (cm, params) {
        params.setCfg = { scope: 'global' };
        this.set(cm, params);
    },
    registers: function (cm, params) {
        var regArgs = params.args;
        var registers = vimGlobalState.registerController.registers;
        var regInfo = '----------Registers----------\n\n';
        if (!regArgs) {
            for (var registerName in registers) {
                var text = registers[registerName].toString();
                if (text.length) {
                    regInfo += '"' + registerName + '    ' + text + '\n';
                }
            }
        }
        else {
            var registerName;
            regArgs = regArgs.join('');
            for (var i = 0; i < regArgs.length; i++) {
                registerName = regArgs.charAt(i);
                if (!vimGlobalState.registerController.isValidRegister(registerName)) {
                    continue;
                }
                var register = registers[registerName] || new Register();
                regInfo += '"' + registerName + '    ' + register.toString() + '\n';
            }
        }
        showConfirm(cm, regInfo);
    },
    sort: function (cm, params) {
        var reverse, ignoreCase, unique, number, pattern;
        function parseArgs() {
            if (params.argString) {
                var args = new CodeMirror.StringStream(params.argString);
                if (args.eat('!')) {
                    reverse = true;
                }
                if (args.eol()) {
                    return;
                }
                if (!args.eatSpace()) {
                    return 'Invalid arguments';
                }
                var opts = args.match(/([dinuox]+)?\s*(\/.+\/)?\s*/);
                if (!opts && !args.eol()) {
                    return 'Invalid arguments';
                }
                if (opts[1]) {
                    ignoreCase = opts[1].indexOf('i') != -1;
                    unique = opts[1].indexOf('u') != -1;
                    var decimal = opts[1].indexOf('d') != -1 || opts[1].indexOf('n') != -1 && 1;
                    var hex = opts[1].indexOf('x') != -1 && 1;
                    var octal = opts[1].indexOf('o') != -1 && 1;
                    if (decimal + hex + octal > 1) {
                        return 'Invalid arguments';
                    }
                    number = decimal && 'decimal' || hex && 'hex' || octal && 'octal';
                }
                if (opts[2]) {
                    pattern = new RegExp(opts[2].substr(1, opts[2].length - 2), ignoreCase ? 'i' : '');
                }
            }
        }
        var err = parseArgs();
        if (err) {
            showConfirm(cm, err + ': ' + params.argString);
            return;
        }
        var lineStart = params.line || cm.firstLine();
        var lineEnd = params.lineEnd || params.line || cm.lastLine();
        if (lineStart == lineEnd) {
            return;
        }
        var curStart = new Pos(lineStart, 0);
        var curEnd = new Pos(lineEnd, lineLength(cm, lineEnd));
        var text = cm.getRange(curStart, curEnd).split('\n');
        var numberRegex = pattern ? pattern :
            (number == 'decimal') ? /(-?)([\d]+)/ :
                (number == 'hex') ? /(-?)(?:0x)?([0-9a-f]+)/i :
                    (number == 'octal') ? /([0-7]+)/ : null;
        var radix = (number == 'decimal') ? 10 : (number == 'hex') ? 16 : (number == 'octal') ? 8 : null;
        var numPart = [], textPart = [];
        if (number || pattern) {
            for (var i = 0; i < text.length; i++) {
                var matchPart = pattern ? text[i].match(pattern) : null;
                if (matchPart && matchPart[0] != '') {
                    numPart.push(matchPart);
                }
                else if (!pattern && numberRegex.exec(text[i])) {
                    numPart.push(text[i]);
                }
                else {
                    textPart.push(text[i]);
                }
            }
        }
        else {
            textPart = text;
        }
        function compareFn(a, b) {
            if (reverse) {
                var tmp;
                tmp = a;
                a = b;
                b = tmp;
            }
            if (ignoreCase) {
                a = a.toLowerCase();
                b = b.toLowerCase();
            }
            var anum = number && numberRegex.exec(a);
            var bnum = number && numberRegex.exec(b);
            if (!anum) {
                return a < b ? -1 : 1;
            }
            anum = parseInt((anum[1] + anum[2]).toLowerCase(), radix);
            bnum = parseInt((bnum[1] + bnum[2]).toLowerCase(), radix);
            return anum - bnum;
        }
        function comparePatternFn(a, b) {
            if (reverse) {
                var tmp;
                tmp = a;
                a = b;
                b = tmp;
            }
            if (ignoreCase) {
                a[0] = a[0].toLowerCase();
                b[0] = b[0].toLowerCase();
            }
            return (a[0] < b[0]) ? -1 : 1;
        }
        numPart.sort(pattern ? comparePatternFn : compareFn);
        if (pattern) {
            for (var i = 0; i < numPart.length; i++) {
                numPart[i] = numPart[i].input;
            }
        }
        else if (!number) {
            textPart.sort(compareFn);
        }
        text = (!reverse) ? textPart.concat(numPart) : numPart.concat(textPart);
        if (unique) { // Remove duplicate lines
            var textOld = text;
            var lastLine;
            text = [];
            for (var i = 0; i < textOld.length; i++) {
                if (textOld[i] != lastLine) {
                    text.push(textOld[i]);
                }
                lastLine = textOld[i];
            }
        }
        cm.replaceRange(text.join('\n'), curStart, curEnd);
    },
    vglobal: function (cm, params) {
        this.global(cm, params);
    },
    normal: function (cm, params) {
        var argString = params.argString;
        if (argString && argString[0] == '!') {
            argString = argString.slice(1);
            noremap = true;
        }
        argString = argString.trimStart();
        if (!argString) {
            showConfirm(cm, 'Argument is required.');
            return;
        }
        var line = params.line;
        if (typeof line == 'number') {
            var lineEnd = isNaN(params.lineEnd) ? line : params.lineEnd;
            for (var i = line; i <= lineEnd; i++) {
                cm.setCursor(i, 0);
                doKeyToKey(cm, params.argString.trimStart());
                if (cm.state.vim.insertMode) {
                    exitInsertMode(cm, true);
                }
            }
        }
        else {
            doKeyToKey(cm, params.argString.trimStart());
            if (cm.state.vim.insertMode) {
                exitInsertMode(cm, true);
            }
        }
    },
    global: function (cm, params) {
        var argString = params.argString;
        if (!argString) {
            showConfirm(cm, 'Regular Expression missing from global');
            return;
        }
        var inverted = params.commandName[0] === 'v';
        if (argString[0] === '!' && params.commandName[0] === 'g') {
            inverted = true;
            argString = argString.slice(1);
        }
        var lineStart = (params.line !== undefined) ? params.line : cm.firstLine();
        var lineEnd = params.lineEnd || params.line || cm.lastLine();
        var tokens = splitBySlash(argString);
        var regexPart = argString, cmd;
        if (tokens.length) {
            regexPart = tokens[0];
            cmd = tokens.slice(1, tokens.length).join('/');
        }
        if (regexPart) {
            try {
                updateSearchQuery(cm, regexPart, true /** ignoreCase */, true /** smartCase */);
            }
            catch (e) {
                showConfirm(cm, 'Invalid regex: ' + regexPart);
                return;
            }
        }
        var query = getSearchState(cm).getQuery();
        var matchedLines = [];
        for (var i = lineStart; i <= lineEnd; i++) {
            var line = cm.getLine(i);
            var matched = query.test(line);
            if (matched !== inverted) {
                matchedLines.push(cmd ? cm.getLineHandle(i) : line);
            }
        }
        if (!cmd) {
            showConfirm(cm, matchedLines.join('\n'));
            return;
        }
        var index = 0;
        var nextCommand = function () {
            if (index < matchedLines.length) {
                var lineHandle = matchedLines[index++];
                var lineNum = cm.getLineNumber(lineHandle);
                if (lineNum == null) {
                    nextCommand();
                    return;
                }
                var command = (lineNum + 1) + cmd;
                exCommandDispatcher.processCommand(cm, command, {
                    callback: nextCommand
                });
            }
            else if (cm.releaseLineHandles) {
                cm.releaseLineHandles();
            }
        };
        nextCommand();
    },
    substitute: function (cm, params) {
        if (!cm.getSearchCursor) {
            throw new Error('Search feature not available. Requires searchcursor.js or ' +
                'any other getSearchCursor implementation.');
        }
        var argString = params.argString;
        var tokens = argString ? splitBySeparator(argString, argString[0]) : [];
        var regexPart, replacePart = '', trailing, flagsPart, count;
        var confirm = false; // Whether to confirm each replace.
        var global = false; // True to replace all instances on a line, false to replace only 1.
        if (tokens.length) {
            regexPart = tokens[0];
            if (getOption('pcre') && regexPart !== '') {
                regexPart = new RegExp(regexPart).source; //normalize not escaped characters
            }
            replacePart = tokens[1];
            if (replacePart !== undefined) {
                if (getOption('pcre')) {
                    replacePart = unescapeRegexReplace(replacePart.replace(/([^\\])&/g, "$1$$&"));
                }
                else {
                    replacePart = translateRegexReplace(replacePart);
                }
                vimGlobalState.lastSubstituteReplacePart = replacePart;
            }
            trailing = tokens[2] ? tokens[2].split(' ') : [];
        }
        else {
            if (argString && argString.length) {
                showConfirm(cm, 'Substitutions should be of the form ' +
                    ':s/pattern/replace/');
                return;
            }
        }
        if (trailing) {
            flagsPart = trailing[0];
            count = parseInt(trailing[1]);
            if (flagsPart) {
                if (flagsPart.indexOf('c') != -1) {
                    confirm = true;
                }
                if (flagsPart.indexOf('g') != -1) {
                    global = true;
                }
                if (getOption('pcre')) {
                    regexPart = regexPart + '/' + flagsPart;
                }
                else {
                    regexPart = regexPart.replace(/\//g, "\\/") + '/' + flagsPart;
                }
            }
        }
        if (regexPart) {
            try {
                updateSearchQuery(cm, regexPart, true /** ignoreCase */, true /** smartCase */);
            }
            catch (e) {
                showConfirm(cm, 'Invalid regex: ' + regexPart);
                return;
            }
        }
        replacePart = replacePart || vimGlobalState.lastSubstituteReplacePart;
        if (replacePart === undefined) {
            showConfirm(cm, 'No previous substitute regular expression');
            return;
        }
        var state = getSearchState(cm);
        var query = state.getQuery();
        var lineStart = (params.line !== undefined) ? params.line : cm.getCursor().line;
        var lineEnd = params.lineEnd || lineStart;
        if (lineStart == cm.firstLine() && lineEnd == cm.lastLine()) {
            lineEnd = Infinity;
        }
        if (count) {
            lineStart = lineEnd;
            lineEnd = lineStart + count - 1;
        }
        var startPos = clipCursorToContent(cm, new Pos(lineStart, 0));
        var cursor = cm.getSearchCursor(query, startPos);
        doReplace(cm, confirm, global, lineStart, lineEnd, cursor, query, replacePart, params.callback);
    },
    startinsert: function (cm, params) {
        doKeyToKey(cm, params.argString == '!' ? 'A' : 'i', {});
    },
    redo: CodeMirror.commands.redo,
    undo: CodeMirror.commands.undo,
    write: function (cm) {
        if (CodeMirror.commands.save) {
            CodeMirror.commands.save(cm);
        }
        else if (cm.save) {
            cm.save();
        }
    },
    nohlsearch: function (cm) {
        clearSearchHighlight(cm);
    },
    yank: function (cm) {
        var cur = copyCursor(cm.getCursor());
        var line = cur.line;
        var lineText = cm.getLine(line);
        vimGlobalState.registerController.pushText('0', 'yank', lineText, true, true);
    },
    delete: function (cm, params) {
        var line = params.selectionLine;
        var lineEnd = isNaN(params.selectionLineEnd) ? line : params.selectionLineEnd;
        operators.delete(cm, { linewise: true }, [
            { anchor: new Pos(line, 0),
                head: new Pos(lineEnd + 1, 0) }
        ]);
    },
    join: function (cm, params) {
        var line = params.selectionLine;
        var lineEnd = isNaN(params.selectionLineEnd) ? line : params.selectionLineEnd;
        cm.setCursor(new Pos(line, 0));
        actions.joinLines(cm, { repeat: lineEnd - line }, cm.state.vim);
    },
    delmarks: function (cm, params) {
        if (!params.argString || !trim(params.argString)) {
            showConfirm(cm, 'Argument required');
            return;
        }
        var state = cm.state.vim;
        var stream = new CodeMirror.StringStream(trim(params.argString));
        while (!stream.eol()) {
            stream.eatSpace();
            var count = stream.pos;
            if (!stream.match(/[a-zA-Z]/, false)) {
                showConfirm(cm, 'Invalid argument: ' + params.argString.substring(count));
                return;
            }
            var sym = stream.next();
            if (stream.match('-', true)) {
                if (!stream.match(/[a-zA-Z]/, false)) {
                    showConfirm(cm, 'Invalid argument: ' + params.argString.substring(count));
                    return;
                }
                var startMark = sym;
                var finishMark = stream.next();
                if (isLowerCase(startMark) && isLowerCase(finishMark) ||
                    isUpperCase(startMark) && isUpperCase(finishMark)) {
                    var start = startMark.charCodeAt(0);
                    var finish = finishMark.charCodeAt(0);
                    if (start >= finish) {
                        showConfirm(cm, 'Invalid argument: ' + params.argString.substring(count));
                        return;
                    }
                    for (var j = 0; j <= finish - start; j++) {
                        var mark = String.fromCharCode(start + j);
                        delete state.marks[mark];
                    }
                }
                else {
                    showConfirm(cm, 'Invalid argument: ' + startMark + '-');
                    return;
                }
            }
            else {
                delete state.marks[sym];
            }
        }
    }
};
var exCommandDispatcher = new ExCommandDispatcher();
function doReplace(cm, confirm, global, lineStart, lineEnd, searchCursor, query, replaceWith, callback) {
    cm.state.vim.exMode = true;
    var done = false;
    var lastPos, modifiedLineNumber, joined;
    function replaceAll() {
        cm.operation(function () {
            while (!done) {
                replace();
                next();
            }
            stop();
        });
    }
    function replace() {
        var text = cm.getRange(searchCursor.from(), searchCursor.to());
        var newText = text.replace(query, replaceWith);
        var unmodifiedLineNumber = searchCursor.to().line;
        searchCursor.replace(newText);
        modifiedLineNumber = searchCursor.to().line;
        lineEnd += modifiedLineNumber - unmodifiedLineNumber;
        joined = modifiedLineNumber < unmodifiedLineNumber;
    }
    function findNextValidMatch() {
        var lastMatchTo = lastPos && copyCursor(searchCursor.to());
        var match = searchCursor.findNext();
        if (match && !match[0] && lastMatchTo && cursorEqual(searchCursor.from(), lastMatchTo)) {
            match = searchCursor.findNext();
        }
        return match;
    }
    function next() {
        while (findNextValidMatch() &&
            isInRange(searchCursor.from(), lineStart, lineEnd)) {
            if (!global && searchCursor.from().line == modifiedLineNumber && !joined) {
                continue;
            }
            cm.scrollIntoView(searchCursor.from(), 30);
            cm.setSelection(searchCursor.from(), searchCursor.to());
            lastPos = searchCursor.from();
            done = false;
            return;
        }
        done = true;
    }
    function stop(close) {
        if (close) {
            close();
        }
        cm.focus();
        if (lastPos) {
            cm.setCursor(lastPos);
            var vim = cm.state.vim;
            vim.exMode = false;
            vim.lastHPos = vim.lastHSPos = lastPos.ch;
        }
        if (callback) {
            callback();
        }
    }
    function onPromptKeyDown(e, _value, close) {
        CodeMirror.e_stop(e);
        var keyName = vimKeyFromEvent(e);
        switch (keyName) {
            case 'y':
                replace();
                next();
                break;
            case 'n':
                next();
                break;
            case 'a':
                var savedCallback = callback;
                callback = undefined;
                cm.operation(replaceAll);
                callback = savedCallback;
                break;
            case 'l':
                replace();
            case 'q':
            case '<Esc>':
            case '<C-c>':
            case '<C-[>':
                stop(close);
                break;
        }
        if (done) {
            stop(close);
        }
        return true;
    }
    next();
    if (done) {
        showConfirm(cm, 'No matches for ' + query.source);
        return;
    }
    if (!confirm) {
        replaceAll();
        if (callback) {
            callback();
        }
        return;
    }
    showPrompt(cm, {
        prefix: dom('span', 'replace with ', dom('strong', replaceWith), ' (y/n/a/q/l)'),
        onKeyDown: onPromptKeyDown
    });
}
function exitInsertMode(cm, keepCursor) {
    var vim = cm.state.vim;
    var macroModeState = vimGlobalState.macroModeState;
    var insertModeChangeRegister = vimGlobalState.registerController.getRegister('.');
    var isPlaying = macroModeState.isPlaying;
    var lastChange = macroModeState.lastInsertModeChanges;
    if (!isPlaying) {
        cm.off('change', onChange);
        if (vim.insertEnd)
            vim.insertEnd.clear();
        vim.insertEnd = null;
        CodeMirror.off(cm.getInputField(), 'keydown', onKeyEventTargetKeyDown);
    }
    if (!isPlaying && vim.insertModeRepeat > 1) {
        repeatLastEdit(cm, vim, vim.insertModeRepeat - 1, true /** repeatForInsert */);
        vim.lastEditInputState.repeatOverride = vim.insertModeRepeat;
    }
    delete vim.insertModeRepeat;
    vim.insertMode = false;
    if (!keepCursor) {
        cm.setCursor(cm.getCursor().line, cm.getCursor().ch - 1);
    }
    cm.setOption('keyMap', 'vim');
    cm.setOption('disableInput', true);
    cm.toggleOverwrite(false); // exit replace mode if we were in it.
    insertModeChangeRegister.setText(lastChange.changes.join(''));
    CodeMirror.signal(cm, "vim-mode-change", { mode: "normal" });
    if (macroModeState.isRecording) {
        logInsertModeChange(macroModeState);
    }
}
function _mapCommand(command) {
    defaultKeymap.unshift(command);
}
function mapCommand(keys, type, name, args, extra) {
    var command = { keys: keys, type: type };
    command[type] = name;
    command[type + "Args"] = args;
    for (var key in extra)
        command[key] = extra[key];
    _mapCommand(command);
}
defineOption('insertModeEscKeysTimeout', 200, 'number');
function executeMacroRegister(cm, vim, macroModeState, registerName) {
    var register = vimGlobalState.registerController.getRegister(registerName);
    if (registerName == ':') {
        if (register.keyBuffer[0]) {
            exCommandDispatcher.processCommand(cm, register.keyBuffer[0]);
        }
        macroModeState.isPlaying = false;
        return;
    }
    var keyBuffer = register.keyBuffer;
    var imc = 0;
    macroModeState.isPlaying = true;
    macroModeState.replaySearchQueries = register.searchQueries.slice(0);
    for (var i = 0; i < keyBuffer.length; i++) {
        var text = keyBuffer[i];
        var match, key;
        while (text) {
            match = (/<\w+-.+?>|<\w+>|./).exec(text);
            key = match[0];
            text = text.substring(match.index + key.length);
            vimApi.handleKey(cm, key, 'macro');
            if (vim.insertMode) {
                var changes = register.insertModeChanges[imc++].changes;
                vimGlobalState.macroModeState.lastInsertModeChanges.changes =
                    changes;
                repeatInsertModeChanges(cm, changes, 1);
                exitInsertMode(cm);
            }
        }
    }
    macroModeState.isPlaying = false;
}
function logKey(macroModeState, key) {
    if (macroModeState.isPlaying) {
        return;
    }
    var registerName = macroModeState.latestRegister;
    var register = vimGlobalState.registerController.getRegister(registerName);
    if (register) {
        register.pushText(key);
    }
}
function logInsertModeChange(macroModeState) {
    if (macroModeState.isPlaying) {
        return;
    }
    var registerName = macroModeState.latestRegister;
    var register = vimGlobalState.registerController.getRegister(registerName);
    if (register && register.pushInsertModeChanges) {
        register.pushInsertModeChanges(macroModeState.lastInsertModeChanges);
    }
}
function logSearchQuery(macroModeState, query) {
    if (macroModeState.isPlaying) {
        return;
    }
    var registerName = macroModeState.latestRegister;
    var register = vimGlobalState.registerController.getRegister(registerName);
    if (register && register.pushSearchQuery) {
        register.pushSearchQuery(query);
    }
}
function onChange(cm, changeObj) {
    var macroModeState = vimGlobalState.macroModeState;
    var lastChange = macroModeState.lastInsertModeChanges;
    if (!macroModeState.isPlaying) {
        var vim = cm.state.vim;
        while (changeObj) {
            lastChange.expectCursorActivityForChange = true;
            if (lastChange.ignoreCount > 1) {
                lastChange.ignoreCount--;
            }
            else if (changeObj.origin == '+input' || changeObj.origin == 'paste'
                || changeObj.origin === undefined /* only in testing */) {
                var selectionCount = cm.listSelections().length;
                if (selectionCount > 1)
                    lastChange.ignoreCount = selectionCount;
                var text = changeObj.text.join('\n');
                if (lastChange.maybeReset) {
                    lastChange.changes = [];
                    lastChange.maybeReset = false;
                }
                if (text) {
                    if (cm.state.overwrite && !/\n/.test(text)) {
                        lastChange.changes.push([text]);
                    }
                    else {
                        if (text.length > 1) {
                            var insertEnd = vim && vim.insertEnd && vim.insertEnd.find();
                            var cursor = cm.getCursor();
                            if (insertEnd && insertEnd.line == cursor.line) {
                                var offset = insertEnd.ch - cursor.ch;
                                if (offset > 0 && offset < text.length) {
                                    lastChange.changes.push([text, offset]);
                                    text = '';
                                }
                            }
                        }
                        if (text)
                            lastChange.changes.push(text);
                    }
                }
            }
            changeObj = changeObj.next;
        }
    }
}
function onCursorActivity(cm) {
    var vim = cm.state.vim;
    if (vim.insertMode) {
        var macroModeState = vimGlobalState.macroModeState;
        if (macroModeState.isPlaying) {
            return;
        }
        var lastChange = macroModeState.lastInsertModeChanges;
        if (lastChange.expectCursorActivityForChange) {
            lastChange.expectCursorActivityForChange = false;
        }
        else {
            lastChange.maybeReset = true;
            if (vim.insertEnd)
                vim.insertEnd.clear();
            vim.insertEnd = cm.setBookmark(cm.getCursor(), { insertLeft: true });
        }
    }
    else if (!cm.curOp.isVimOp) {
        handleExternalSelection(cm, vim);
    }
}
function handleExternalSelection(cm, vim, keepHPos) {
    var anchor = cm.getCursor('anchor');
    var head = cm.getCursor('head');
    if (vim.visualMode && !cm.somethingSelected()) {
        exitVisualMode(cm, false);
    }
    else if (!vim.visualMode && !vim.insertMode && cm.somethingSelected()) {
        vim.visualMode = true;
        vim.visualLine = false;
        CodeMirror.signal(cm, "vim-mode-change", { mode: "visual" });
    }
    if (vim.visualMode) {
        var headOffset = !cursorIsBefore(head, anchor) ? -1 : 0;
        var anchorOffset = cursorIsBefore(head, anchor) ? -1 : 0;
        head = offsetCursor(head, 0, headOffset);
        anchor = offsetCursor(anchor, 0, anchorOffset);
        vim.sel = {
            anchor: anchor,
            head: head
        };
        updateMark(cm, vim, '<', cursorMin(head, anchor));
        updateMark(cm, vim, '>', cursorMax(head, anchor));
    }
    else if (!vim.insertMode && !keepHPos) {
        vim.lastHPos = cm.getCursor().ch;
    }
}
function InsertModeKey(keyName, e) {
    this.keyName = keyName;
    this.key = e.key;
    this.ctrlKey = e.ctrlKey;
    this.altKey = e.altKey;
    this.metaKey = e.metaKey;
    this.shiftKey = e.shiftKey;
}
function onKeyEventTargetKeyDown(e) {
    var macroModeState = vimGlobalState.macroModeState;
    var lastChange = macroModeState.lastInsertModeChanges;
    var keyName = CodeMirror.keyName ? CodeMirror.keyName(e) : e.key;
    if (!keyName) {
        return;
    }
    if (keyName.indexOf('Delete') != -1 || keyName.indexOf('Backspace') != -1) {
        if (lastChange.maybeReset) {
            lastChange.changes = [];
            lastChange.maybeReset = false;
        }
        lastChange.changes.push(new InsertModeKey(keyName, e));
    }
}
function repeatLastEdit(cm, vim, repeat, repeatForInsert) {
    var macroModeState = vimGlobalState.macroModeState;
    macroModeState.isPlaying = true;
    var isAction = !!vim.lastEditActionCommand;
    var cachedInputState = vim.inputState;
    function repeatCommand() {
        if (isAction) {
            commandDispatcher.processAction(cm, vim, vim.lastEditActionCommand);
        }
        else {
            commandDispatcher.evalInput(cm, vim);
        }
    }
    function repeatInsert(repeat) {
        if (macroModeState.lastInsertModeChanges.changes.length > 0) {
            repeat = !vim.lastEditActionCommand ? 1 : repeat;
            var changeObject = macroModeState.lastInsertModeChanges;
            repeatInsertModeChanges(cm, changeObject.changes, repeat);
        }
    }
    vim.inputState = vim.lastEditInputState;
    if (isAction && vim.lastEditActionCommand.interlaceInsertRepeat) {
        for (var i = 0; i < repeat; i++) {
            repeatCommand();
            repeatInsert(1);
        }
    }
    else {
        if (!repeatForInsert) {
            repeatCommand();
        }
        repeatInsert(repeat);
    }
    vim.inputState = cachedInputState;
    if (vim.insertMode && !repeatForInsert) {
        exitInsertMode(cm);
    }
    macroModeState.isPlaying = false;
}
function sendCmKey(cm, key) {
    CodeMirror.lookupKey(key, 'vim-insert', function keyHandler(binding) {
        if (typeof binding == 'string') {
            CodeMirror.commands[binding](cm);
        }
        else {
            binding(cm);
        }
        return true;
    });
}
function repeatInsertModeChanges(cm, changes, repeat) {
    var head = cm.getCursor('head');
    var visualBlock = vimGlobalState.macroModeState.lastInsertModeChanges.visualBlock;
    if (visualBlock) {
        selectForInsert(cm, head, visualBlock + 1);
        repeat = cm.listSelections().length;
        cm.setCursor(head);
    }
    for (var i = 0; i < repeat; i++) {
        if (visualBlock) {
            cm.setCursor(offsetCursor(head, i, 0));
        }
        for (var j = 0; j < changes.length; j++) {
            var change = changes[j];
            if (change instanceof InsertModeKey) {
                sendCmKey(cm, change.keyName, change);
            }
            else if (typeof change == "string") {
                cm.replaceSelection(change);
            }
            else {
                var start = cm.getCursor();
                var end = offsetCursor(start, 0, change[0].length - (change[1] || 0));
                cm.replaceRange(change[0], start, change[1] ? start : end);
                cm.setCursor(end);
            }
        }
    }
    if (visualBlock) {
        cm.setCursor(offsetCursor(head, 0, 1));
    }
}
CodeMirror.Vim = vimApi;
var specialKeyAce = { 'return': 'CR', backspace: 'BS', 'delete': 'Del', esc: 'Esc',
    left: 'Left', right: 'Right', up: 'Up', down: 'Down', space: 'Space', insert: 'Ins',
    home: 'Home', end: 'End', pageup: 'PageUp', pagedown: 'PageDown', enter: 'CR'
};
function lookupKey(hashId, key, e, vim) {
    if (key.length > 1 && key[0] == "n") {
        key = key.replace("numpad", "");
    }
    key = specialKeyAce[key] || key;
    var name = '';
    if (e.ctrlKey) {
        name += 'C-';
    }
    if (e.altKey) {
        name += 'A-';
    }
    if ((name || key.length > 1) && e.shiftKey) {
        name += 'S-';
    }
    if (vim && !vim.expectLiteralNext && key.length == 1) {
        if (langmap.keymap && key in langmap.keymap) {
            if (langmap.remapCtrl !== false || !name)
                key = langmap.keymap[key];
        }
        else if (key.charCodeAt(0) > 255) {
            var code = e.code && e.code.slice(-1) || "";
            if (!e.shiftKey)
                code = code.toLowerCase();
            if (code)
                key = code;
        }
    }
    name += key;
    if (name.length > 1) {
        name = '<' + name + '>';
    }
    return name;
}
var handleKey = vimApi.handleKey.bind(vimApi);
vimApi.handleKey = function (cm, key, origin) {
    return cm.operation(function () {
        return handleKey(cm, key, origin);
    }, true);
};
function cloneVimState(state) {
    var n = new state.constructor();
    Object.keys(state).forEach(function (key) {
        if (key == "insertEnd")
            return;
        var o = state[key];
        if (Array.isArray(o))
            o = o.slice();
        else if (o && typeof o == "object" && o.constructor != Object)
            o = cloneVimState(o);
        n[key] = o;
    });
    if (state.sel) {
        n.sel = {
            head: state.sel.head && copyCursor(state.sel.head),
            anchor: state.sel.anchor && copyCursor(state.sel.anchor)
        };
    }
    return n;
}
function multiSelectHandleKey(cm, key, origin) {
    var isHandled = false;
    var vim = vimApi.maybeInitVimState_(cm);
    var visualBlock = vim.visualBlock || vim.wasInVisualBlock;
    var wasMultiselect = cm.ace.inMultiSelectMode;
    if (vim.wasInVisualBlock && !wasMultiselect) {
        vim.wasInVisualBlock = false;
    }
    else if (wasMultiselect && vim.visualBlock) {
        vim.wasInVisualBlock = true;
    }
    if (key == '<Esc>' && !vim.insertMode && !vim.visualMode && wasMultiselect) {
        cm.ace.exitMultiSelectMode();
    }
    else if (visualBlock || !wasMultiselect || cm.ace.inVirtualSelectionMode) {
        isHandled = vimApi.handleKey(cm, key, origin);
    }
    else {
        var old = cloneVimState(vim);
        var changeQueueList = vim.inputState.changeQueueList || [];
        cm.operation(function () {
            cm.curOp.isVimOp = true;
            var index = 0;
            cm.ace.forEachSelection(function () {
                var sel = cm.ace.selection;
                cm.state.vim.lastHPos = sel.$desiredColumn == null ? sel.lead.column : sel.$desiredColumn;
                cm.state.vim.inputState.changeQueue = changeQueueList[index];
                var head = cm.getCursor("head");
                var anchor = cm.getCursor("anchor");
                var headOffset = !cursorIsBefore(head, anchor) ? -1 : 0;
                var anchorOffset = cursorIsBefore(head, anchor) ? -1 : 0;
                head = offsetCursor(head, 0, headOffset);
                anchor = offsetCursor(anchor, 0, anchorOffset);
                cm.state.vim.sel.head = head;
                cm.state.vim.sel.anchor = anchor;
                isHandled = handleKey(cm, key, origin);
                sel.$desiredColumn = cm.state.vim.lastHPos == -1 ? null : cm.state.vim.lastHPos;
                if (cm.ace.inVirtualSelectionMode) {
                    changeQueueList[index] = cm.state.vim.inputState.changeQueue;
                }
                if (cm.virtualSelectionMode()) {
                    cm.state.vim = cloneVimState(old);
                }
                index++;
            });
            if (cm.curOp.cursorActivity && !isHandled)
                cm.curOp.cursorActivity = false;
            vim.status = cm.state.vim.status;
            cm.state.vim = vim;
            vim.inputState.changeQueueList = changeQueueList;
            vim.inputState.changeQueue = null;
        }, true);
    }
    if (isHandled && !vim.visualMode && !vim.insert && vim.visualMode != cm.somethingSelected()) {
        handleExternalSelection(cm, vim, true);
    }
    return isHandled;
}
resetVimGlobalState();
exports.CodeMirror = CodeMirror;
var getVim = vimApi.maybeInitVimState_;
exports.handler = {
    $id: "ace/keyboard/vim",
    drawCursor: function (element, pixelPos, config, sel, session) {
        var vim = this.state.vim || {};
        var w = config.characterWidth;
        var h = config.lineHeight;
        var top = pixelPos.top;
        var left = pixelPos.left;
        if (!vim.insertMode) {
            var isbackwards = !sel.cursor
                ? session.selection.isBackwards() || session.selection.isEmpty()
                : Range.comparePoints(sel.cursor, sel.start) <= 0;
            if (!isbackwards && left > w)
                left -= w;
        }
        if (!vim.insertMode && vim.status) {
            h = h / 2;
            top += h;
        }
        domLib.translate(element, left, top);
        domLib.setStyle(element.style, "width", w + "px");
        domLib.setStyle(element.style, "height", h + "px");
    },
    $getDirectionForHighlight: function (editor) {
        var cm = editor.state.cm;
        var vim = getVim(cm);
        if (!vim.insertMode) {
            return editor.session.selection.isBackwards() || editor.session.selection.isEmpty();
        }
    },
    handleKeyboard: function (data, hashId, key, keyCode, e) {
        var editor = data.editor;
        var cm = editor.state.cm;
        var vim = getVim(cm);
        if (keyCode == -1)
            return;
        if (!vim.insertMode) {
            if (hashId == -1) {
                if (key.charCodeAt(0) > 0xFF) {
                    if (data.inputKey) {
                        key = data.inputKey;
                        if (key && data.inputHash == 4)
                            key = key.toUpperCase();
                    }
                }
                data.inputChar = key;
            }
            else if (hashId == 4 || hashId == 0) {
                if (data.inputKey == key && data.inputHash == hashId && data.inputChar) {
                    key = data.inputChar;
                    hashId = -1;
                }
                else {
                    data.inputChar = null;
                    data.inputKey = key;
                    data.inputHash = hashId;
                }
            }
            else {
                data.inputChar = data.inputKey = null;
            }
        }
        if (cm.state.overwrite && vim.insertMode && key == "backspace" && hashId == 0) {
            return { command: "gotoleft" };
        }
        if (key == "c" && hashId == 1) { // key == "ctrl-c"
            if (!useragent.isMac && editor.getCopyText()) {
                editor.once("copy", function () {
                    if (vim.insertMode)
                        editor.selection.clearSelection();
                    else
                        cm.operation(function () { exitVisualMode(cm); });
                });
                return { command: "null", passEvent: true };
            }
        }
        if (key == "esc" && !vim.insertMode && !vim.visualMode && !cm.ace.inMultiSelectMode) {
            var searchState = getSearchState(cm);
            var overlay = searchState.getOverlay();
            if (overlay)
                cm.removeOverlay(overlay);
        }
        if (hashId == -1 || hashId & 1 || hashId === 0 && key.length > 1) {
            var insertMode = vim.insertMode;
            var name = lookupKey(hashId, key, e || {}, vim);
            if (vim.status == null)
                vim.status = "";
            var isHandled = multiSelectHandleKey(cm, name, 'user');
            vim = getVim(cm); // may be changed by multiSelectHandleKey
            if (isHandled && vim.status != null)
                vim.status += name;
            else if (vim.status == null)
                vim.status = "";
            cm._signal("changeStatus");
            if (!isHandled && (hashId != -1 || insertMode))
                return;
            return { command: "null", passEvent: !isHandled };
        }
    },
    attach: function (editor) {
        if (!editor.state)
            editor.state = {};
        var cm = new CodeMirror(editor);
        editor.state.cm = cm;
        editor.$vimModeHandler = this;
        enterVimMode(cm);
        getVim(cm).status = null;
        cm.on('vim-command-done', function () {
            if (cm.virtualSelectionMode())
                return;
            getVim(cm).status = null;
            cm.ace._signal("changeStatus");
            cm.ace.session.markUndoGroup();
        });
        cm.on("changeStatus", function () {
            cm.ace.renderer.updateCursor();
            cm.ace._signal("changeStatus");
        });
        cm.on("vim-mode-change", function () {
            if (cm.virtualSelectionMode())
                return;
            updateInputMode();
            cm._signal("changeStatus");
        });
        function updateInputMode() {
            var isIntsert = getVim(cm).insertMode;
            cm.ace.renderer.setStyle("normal-mode", !isIntsert);
            editor.textInput.setCommandMode(!isIntsert);
            editor.renderer.$keepTextAreaAtCursor = isIntsert;
            editor.renderer.$blockCursor = !isIntsert;
        }
        updateInputMode();
        editor.renderer.$cursorLayer.drawCursor = this.drawCursor.bind(cm);
    },
    detach: function (editor) {
        var cm = editor.state.cm;
        leaveVimMode(cm);
        cm.destroy();
        editor.state.cm = null;
        editor.$vimModeHandler = null;
        editor.renderer.$cursorLayer.drawCursor = null;
        editor.renderer.setStyle("normal-mode", false);
        editor.textInput.setCommandMode(false);
        editor.renderer.$keepTextAreaAtCursor = true;
    },
    getStatusText: function (editor) {
        var cm = editor.state.cm;
        var vim = getVim(cm);
        if (vim.insertMode)
            return "INSERT";
        var status = "";
        if (vim.visualMode) {
            status += "VISUAL";
            if (vim.visualLine)
                status += " LINE";
            if (vim.visualBlock)
                status += " BLOCK";
        }
        if (vim.status)
            status += (status ? " " : "") + vim.status;
        return status;
    }
};
vimApi.defineOption({
    name: "wrap",
    set: function (value, cm) {
        if (cm) {
            cm.ace.setOption("wrap", value);
        }
    },
    type: "boolean"
}, false);
vimApi.defineEx('write', 'w', function () {
    console.log(':write is not implemented');
});
defaultKeymap.push({ keys: 'zc', type: 'action', action: 'fold', actionArgs: { open: false } }, { keys: 'zC', type: 'action', action: 'fold', actionArgs: { open: false, all: true } }, { keys: 'zo', type: 'action', action: 'fold', actionArgs: { open: true } }, { keys: 'zO', type: 'action', action: 'fold', actionArgs: { open: true, all: true } }, { keys: 'za', type: 'action', action: 'fold', actionArgs: { toggle: true } }, { keys: 'zA', type: 'action', action: 'fold', actionArgs: { toggle: true, all: true } }, { keys: 'zf', type: 'action', action: 'fold', actionArgs: { open: true, all: true } }, { keys: 'zd', type: 'action', action: 'fold', actionArgs: { open: true, all: true } }, { keys: '<C-A-k>', type: 'action', action: 'aceCommand', actionArgs: { name: "addCursorAbove" } }, { keys: '<C-A-j>', type: 'action', action: 'aceCommand', actionArgs: { name: "addCursorBelow" } }, { keys: '<C-A-S-k>', type: 'action', action: 'aceCommand', actionArgs: { name: "addCursorAboveSkipCurrent" } }, { keys: '<C-A-S-j>', type: 'action', action: 'aceCommand', actionArgs: { name: "addCursorBelowSkipCurrent" } }, { keys: '<C-A-h>', type: 'action', action: 'aceCommand', actionArgs: { name: "selectMoreBefore" } }, { keys: '<C-A-l>', type: 'action', action: 'aceCommand', actionArgs: { name: "selectMoreAfter" } }, { keys: '<C-A-S-h>', type: 'action', action: 'aceCommand', actionArgs: { name: "selectNextBefore" } }, { keys: '<C-A-S-l>', type: 'action', action: 'aceCommand', actionArgs: { name: "selectNextAfter" } });
defaultKeymap.push({
    keys: 'gq',
    type: 'operator',
    operator: 'hardWrap'
});
vimApi.defineOperator("hardWrap", function (cm, operatorArgs, ranges, oldAnchor, newHead) {
    var anchor = ranges[0].anchor.line;
    var head = ranges[0].head.line;
    if (operatorArgs.linewise)
        head--;
    hardWrap(cm.ace, { startRow: anchor, endRow: head });
    return Pos(head, 0);
});
defineOption('textwidth', undefined, 'number', ['tw'], function (width, cm) {
    if (cm === undefined) {
        return;
    }
    if (width === undefined) {
        var value = cm.ace.getOption('printMarginColumn');
        return value;
    }
    else {
        var column = Math.round(width);
        if (column > 1) {
            cm.ace.setOption('printMarginColumn', column);
        }
    }
});
actions.aceCommand = function (cm, actionArgs, vim) {
    cm.vimCmd = actionArgs;
    if (cm.ace.inVirtualSelectionMode)
        cm.ace.on("beforeEndOperation", delayedExecAceCommand);
    else
        delayedExecAceCommand(null, cm.ace);
};
function delayedExecAceCommand(op, ace) {
    ace.off("beforeEndOperation", delayedExecAceCommand);
    var cmd = ace.state.cm.vimCmd;
    if (cmd) {
        ace.execCommand(cmd.exec ? cmd : cmd.name, cmd.args);
    }
    ace.curOp = ace.prevOp;
}
actions.fold = function (cm, actionArgs, vim) {
    cm.ace.execCommand(['toggleFoldWidget', 'toggleFoldWidget', 'foldOther', 'unfoldall'
    ][(actionArgs.all ? 2 : 0) + (actionArgs.open ? 1 : 0)]);
};
defaultKeymapLength = defaultKeymap.length; // ace_patch
exports.handler.defaultKeymap = defaultKeymap;
exports.handler.actions = actions;
exports.Vim = vimApi;

});                (function() {
                    ace.require(["ace/keyboard/vim"], function(m) {
                        if ( true && module) {
                            module.exports = m;
                        }
                    });
                })();
            

/***/ }

}]);
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYWNlLWtleWJpbmRpbmctdmltLWY4M2ZmMTNhMDAwNWY5MWViNTk3LmpzIiwibWFwcGluZ3MiOiI7Ozs7Ozs7OztBQUFBLHVJQUF1STtBQUN2STtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQSxDQUFDO0FBQ0Q7O0FBRUEsQ0FBQzs7QUFFRCxtVkFBbVY7QUFDblY7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsYUFBYTtBQUNiO0FBQ0E7QUFDQSxvQkFBb0Isc0JBQXNCO0FBQzFDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtB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QTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsZ0JBQWdCO0FBQU07QUFDdEI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhO0FBQ2I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw2RUFBNkUsbUNBQW1DO0FBQ2hIO0FBQ0Esc0JBQXNCO0FBQ3RCO0FBQ0E7QUFDQSxzQkFBc0I7QUFDdEI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtB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O0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSwyQ0FBMkM7QUFDM0M7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw0REFBNEQ7QUFDNUQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLENBQUM7QUFDRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsQ0FBQztBQUNEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGNBQWM7QUFDZDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDhDQUE4QztBQUM5QztBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7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QUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esb0JBQW9CO0FBQ3BCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxDQUFDO0FBQ0Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw2Q0FBNkMsU0FBUztBQUN0RDtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3QjtBQUN4Qiw0QkFBNEIsaUJBQWlCO0FBQzdDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0I7QUFDeEIsNEJBQTRCLGtCQUFrQjtBQUM5QztBQUNBO0FBQ0EsS0FBSztBQUNMLGFBQWE7QUFDYjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsQ0FBQztBQUNEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EseUJBQXlCO0FBQ3pCLDhCQUE4QjtBQUM5Qiw2QkFBNkI7QUFDN0I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0Esd0JBQXdCLFFBQVE7QUFDaEM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsMENBQTBDLHdDQUF3QztBQUNsRjtBQUNBLDRCQUE0QixxQkFBcUI7QUFDakQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3Qix5QkFBeUI7QUFDakQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHlCQUF5QjtBQUN6QjtBQUNBO0FBQ0EsaUJBQWlCO0FBQ2pCLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsMENBQTBDO0FBQzFDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDhCQUE4QjtBQUM5QixhQUFhO0FBQ2I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHFCQUFxQjtBQUNyQjtBQUNBO0FBQ0E7QUFDQSx1REFBdUQsZ0JBQWdCO0FBQ3ZFO0FBQ0E7QUFDQSx1REFBdUQsaUJBQWlCO0FBQ3hFO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxpQ0FBaUM7QUFDakMsMEVBQTBFO0FBQzFFO0FBQ0E7QUFDQSxpQ0FBaUM7QUFDakMsZ0RBQWdEO0FBQ2hEO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEVBQTRFO0FBQzVFO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxRUFBcUU7QUFDckU7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxpQkFBaUI7QUFDakI7QUFDQTtBQUNBO0FBQ0Esd0NBQXdDLG1CQUFtQjtBQUMzRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsaUJBQWlCO0FBQ2pCO0FBQ0E7QUFDQTtBQUNBLDBDQUEwQztBQUMxQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDJEQUEyRCw2QkFBNkI7QUFDeEY7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsdURBQXVELDZCQUE2QjtBQUNwRjtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBLDJDQUEyQyw0RUFBNEU7QUFDdkg7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSx3QkFBd0IsdUJBQXVCO0FBQy9DO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxtQ0FBbUM7QUFDbkM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxlQUFlLHNCQUFzQjtBQUNyQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1REFBdUQsZ0JBQWdCLE9BQU87QUFDOUUsMEVBQTBFLGtCQUFrQjtBQUM1RjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQSw4QkFBOEI7QUFDOUIsY0FBYyxLQUFLLEtBQUssS0FBSztBQUM3QjtBQUNBO0FBQ0EsMkJBQTJCO0FBQzNCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSwwQkFBMEI7QUFDMUI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsMEJBQTBCO0FBQzFCO0FBQ0Esb0JBQW9CO0FBQ3BCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQixXQUFXO0FBQy9CO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esc0NBQXNDLGlCQUFpQjtBQUN2RCxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw0Q0FBNEMsUUFBUTtBQUNwRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9DQUFvQyxZQUFZO0FBQ2hEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDRDQUE0QyxtQkFBbUI7QUFDL0Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw0QkFBNEIsWUFBWTtBQUN4QztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esb0NBQW9DLGNBQWM7QUFDbEQsZ0NBQWdDLFlBQVk7QUFDNUM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxtQ0FBbUMsb0JBQW9CO0FBQ3ZEO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3Qix1QkFBdUI7QUFDL0M7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsZ0NBQWdDLG1CQUFtQjtBQUNuRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsZ0VBQWdFO0FBQ2hFLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1REFBdUQsaUJBQWlCO0FBQ3hFO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsdURBQXVELGdCQUFnQjtBQUN2RTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsdURBQXVELGlCQUFpQjtBQUN4RTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHVEQUF1RCxnQkFBZ0I7QUFDdkU7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG1EQUFtRCxrQkFBa0I7QUFDckU7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1REFBdUQsMkZBQTJGO0FBQ2xKO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1REFBdUQsMkZBQTJGO0FBQ2xKO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhO0FBQ2I7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esb0NBQW9DLGlCQUFpQjtBQUNyRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsbUNBQW1DLDJCQUEyQjtBQUM5RCxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhLGdCQUFnQixhQUFhO0FBQzFDO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhO0FBQ2I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCLGlCQUFpQjtBQUM3QztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsZ0NBQWdDLGlCQUFpQjtBQUNqRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNULEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esa0RBQWtEO0FBQ2xEO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVCxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHlCQUF5QixtQ0FBbUM7QUFDNUQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDZCQUE2QixtQkFBbUI7QUFDaEQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esd0JBQXdCLFlBQVk7QUFDcEM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx5Q0FBeUM7QUFDekM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLCtCQUErQixrQkFBa0I7QUFDakQsc0JBQXNCO0FBQ3RCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQixZQUFZO0FBQ2hDO0FBQ0EsbUJBQW1CLGtDQUFrQztBQUNyRDtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQixtQkFBbUI7QUFDdkM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsOENBQThDLHVCQUF1QjtBQUNyRTtBQUNBO0FBQ0EsOEJBQThCO0FBQzlCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDZCQUE2QjtBQUM3QjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDBCQUEwQjtBQUMxQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1QkFBdUIsNEJBQTRCO0FBQ25EO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx1QkFBdUIsNEJBQTRCO0FBQ25EO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3QixZQUFZO0FBQ3BDO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxtREFBbUQsZ0JBQWdCO0FBQ25FO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EscUNBQXFDLHNEQUFzRDtBQUMzRjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsK0JBQStCO0FBQy9CO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0E7QUFDQSxpQkFBaUI7QUFDakI7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBLGFBQWE7QUFDYjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxzQ0FBc0MsZ0JBQWdCO0FBQ3REO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSx3RUFBd0UsTUFBTTtBQUM5RSxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsaURBQWlELE1BQU07QUFDdkQsaURBQWlELE1BQU0sTUFBTTtBQUM3RCxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGtDQUFrQyxZQUFZLEtBQUssSUFBSSxJQUFJLFlBQVksS0FBSyxHQUFHO0FBQy9FO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHFCQUFxQjtBQUNyQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCLG9DQUFvQztBQUNoRTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxvQkFBb0IsWUFBWTtBQUNoQztBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQjtBQUNwQixvQkFBb0IseUJBQXlCO0FBQzdDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQixZQUFZO0FBQ2hDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsMEJBQTBCLG9DQUFvQztBQUM5RDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG1CQUFtQixvQkFBb0I7QUFDdkM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxtQkFBbUIsU0FBUztBQUM1QjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHFCQUFxQjtBQUNyQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDZCQUE2QjtBQUM3QjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw2QkFBNkI7QUFDN0I7QUFDQTtBQUNBO0FBQ0E7QUFDQSxpQkFBaUI7QUFDakI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNkJBQTZCO0FBQzdCO0FBQ0E7QUFDQTtBQUNBLGlDQUFpQztBQUNqQztBQUNBO0FBQ0EsaUNBQWlDO0FBQ2pDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EscUJBQXFCO0FBQ3JCO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHlCQUF5QjtBQUN6QjtBQUNBO0FBQ0EseUJBQXlCO0FBQ3pCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxzQ0FBc0MsUUFBUTtBQUM5QztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSw2QkFBNkI7QUFDN0I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsK0JBQStCO0FBQy9CO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0IsaUJBQWlCO0FBQ3pDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFVBQVUsT0FBTyxNQUFNLE9BQU87QUFDOUI7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0EsVUFBVSxLQUFLLEtBQUssS0FBSztBQUN6QjtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsbUZBQW1GLCtCQUErQjtBQUNsSCxnRkFBZ0YsK0JBQStCO0FBQy9HO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsYUFBYTtBQUNiO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDBCQUEwQjtBQUMxQixzQkFBc0I7QUFDdEI7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCO0FBQzVCO0FBQ0E7QUFDQSx5QkFBeUIsa0JBQWtCO0FBQzNDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDRDQUE0QyxpQkFBaUI7QUFDN0Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsaUJBQWlCO0FBQ2pCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxvQkFBb0Isb0JBQW9CO0FBQ3hDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esb0JBQW9CLGdCQUFnQjtBQUNwQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0I7QUFDeEIscUJBQXFCO0FBQ3JCO0FBQ0E7QUFDQSxxQkFBcUIsZ0JBQWdCO0FBQ3JDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxzQkFBc0I7QUFDdEI7QUFDQTtBQUNBO0FBQ0EscUJBQXFCLGdCQUFnQjtBQUNyQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxrQkFBa0I7QUFDbEI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHVCQUF1QixzQkFBc0I7QUFDN0M7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSwyQkFBMkIsNERBQTREO0FBQ3ZGO0FBQ0EsbUNBQW1DLDhCQUE4QjtBQUNqRTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0Isa0JBQWtCLGdCQUFnQix3REFBd0QseUJBQXlCO0FBQzNJLG9FQUFvRSwwQkFBMEIsZ0JBQWdCO0FBQzlHO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0Esd0JBQXdCLGtCQUFrQjtBQUMxQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0IsWUFBWTtBQUNwQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3QixZQUFZO0FBQ3BDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDhCQUE4QixJQUFJO0FBQ2xDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1QsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQSx5Q0FBeUMsT0FBTztBQUNoRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBLHdCQUF3QixnQ0FBZ0M7QUFDeEQ7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDRCQUE0QiwwQkFBMEI7QUFDdEQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMLGtDQUFrQyxpQ0FBaUM7QUFDbkUsa0NBQWtDLGlDQUFpQztBQUNuRSxrQ0FBa0MsaUNBQWlDO0FBQ25FLGtDQUFrQywwQ0FBMEM7QUFDNUUscUNBQXFDLHdDQUF3QztBQUM3RSxzQ0FBc0MsdUNBQXVDO0FBQzdFLHNDQUFzQyx1Q0FBdUM7QUFDN0Usc0NBQXNDLHVDQUF1QztBQUM3RSxzQ0FBc0MsZ0RBQWdEO0FBQ3RGO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMLHNDQUFzQyxvQkFBb0I7QUFDMUQsdUNBQXVDLDRCQUE0QjtBQUNuRSx1Q0FBdUMsNEJBQTRCO0FBQ25FLHVDQUF1Qyw0QkFBNEI7QUFDbkUsdUNBQXVDLHFDQUFxQztBQUM1RTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDBCQUEwQjtBQUMxQixnQ0FBZ0M7QUFDaEM7QUFDQSxTQUFTO0FBQ1QsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQSwwQkFBMEI7QUFDMUI7QUFDQSxLQUFLO0FBQ0w7QUFDQSwwQkFBMEI7QUFDMUI7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCLG9CQUFvQjtBQUNoRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCLGlCQUFpQjtBQUM3QztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNEJBQTRCLG9CQUFvQjtBQUNoRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHNCQUFzQjtBQUN0QjtBQUNBO0FBQ0E7QUFDQSw0QkFBNEIsb0JBQW9CO0FBQ2hEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLCtCQUErQixjQUFjO0FBQzdDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGdDQUFnQyxjQUFjO0FBQzlDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsaUJBQWlCO0FBQ2pCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNkJBQTZCO0FBQzdCLDRCQUE0QjtBQUM1QjtBQUNBO0FBQ0E7QUFDQSwwREFBMEQ7QUFDMUQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0EsOERBQThEO0FBQzlELEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBLCtCQUErQixnQkFBZ0I7QUFDL0MsY0FBYztBQUNkO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSxnQ0FBZ0Msd0JBQXdCO0FBQ3hELEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxvQ0FBb0MscUJBQXFCO0FBQ3pEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSwrQkFBK0I7QUFDL0I7QUFDQSwrQ0FBK0MsZ0JBQWdCO0FBQy9EO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxvQkFBb0I7QUFDcEI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG9CQUFvQixzQkFBc0I7QUFDMUM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsNkRBQTZELGtCQUFrQjtBQUMvRTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxtREFBbUQsZ0JBQWdCO0FBQ25FO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3QkFBd0IsWUFBWTtBQUNwQztBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxvQkFBb0IsWUFBWTtBQUNoQztBQUNBO0FBQ0E7QUFDQSx3QkFBd0Isb0JBQW9CO0FBQzVDO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxzQkFBc0I7QUFDdEI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhO0FBQ2I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckI7QUFDQSx5Q0FBeUM7QUFDekM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLG1EQUFtRCxxQkFBcUI7QUFDeEUsaUJBQWlCO0FBQ2pCLHlCQUF5QjtBQUN6QjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHFEQUFxRDtBQUNyRDtBQUNBO0FBQ0E7QUFDQSw4QkFBOEI7QUFDOUI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckI7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0EsQ0FBQztBQUNEO0FBQ0E7QUFDQSxDQUFDO0FBQ0QscUJBQXFCLDBEQUEwRCxlQUFlLElBQUksMERBQTBELDBCQUEwQixJQUFJLDBEQUEwRCxjQUFjLElBQUksMERBQTBELHlCQUF5QixJQUFJLDBEQUEwRCxnQkFBZ0IsSUFBSSwwREFBMEQsMkJBQTJCLElBQUksMERBQTBELHlCQUF5QixJQUFJLDBEQUEwRCx5QkFBeUIsSUFBSSxxRUFBcUUsMEJBQTBCLElBQUkscUVBQXFFLDBCQUEwQixJQUFJLHVFQUF1RSxxQ0FBcUMsSUFBSSx1RUFBdUUscUNBQXFDLElBQUkscUVBQXFFLDRCQUE0QixJQUFJLHFFQUFxRSwyQkFBMkIsSUFBSSx1RUFBdUUsNEJBQTRCLElBQUksdUVBQXVFLDJCQUEyQjtBQUMxK0M7QUFDQTtBQUNBO0FBQ0E7QUFDQSxDQUFDO0FBQ0Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHVCQUF1QixnQ0FBZ0M7QUFDdkQ7QUFDQSxDQUFDO0FBQ0Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLENBQUM7QUFDRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDRDQUE0QztBQUM1QztBQUNBO0FBQ0E7O0FBRUEsQ0FBQyxrQkFBa0I7QUFDbkI7QUFDQSw0QkFBNEIsS0FBdUQ7QUFDbkY7QUFDQTtBQUNBLHFCQUFxQjtBQUNyQixpQkFBaUI7QUFDakIsWSIsInNvdXJjZXMiOlsid2VicGFjazovL3VpLy4vbm9kZV9tb2R1bGVzLy5wbnBtL2FjZS1idWlsZHNAMS40My42L25vZGVfbW9kdWxlcy9hY2UtYnVpbGRzL3NyYy1ub2NvbmZsaWN0L2tleWJpbmRpbmctdmltLmpzIl0sInNvdXJjZXNDb250ZW50IjpbImFjZS5kZWZpbmUoXCJhY2UvZXh0L2hhcmR3cmFwXCIsW1wicmVxdWlyZVwiLFwiZXhwb3J0c1wiLFwibW9kdWxlXCIsXCJhY2UvcmFuZ2VcIixcImFjZS9lZGl0b3JcIixcImFjZS9jb25maWdcIl0sIGZ1bmN0aW9uKHJlcXVpcmUsIGV4cG9ydHMsIG1vZHVsZSl7LyoqXG4gKiAjIyBUZXh0IGhhcmQgd3JhcHBpbmcgZXh0ZW5zaW9uIGZvciBhdXRvbWF0aWMgbGluZSBicmVha2luZyBhbmQgdGV4dCBmb3JtYXR0aW5nLlxuICpcbiAqIFByb3ZpZGVzIGludGVsbGlnZW50IGxpbmUgd3JhcHBpbmcgZnVuY3Rpb25hbGl0eSB0aGF0IGJyZWFrcyBsb25nIGxpbmVzIGF0IGNvbmZpZ3VyYWJsZSBjb2x1bW4gbGltaXRzIHdoaWxlXG4gKiBwcmVzZXJ2aW5nIGluZGVudGF0aW9uIGFuZCBvcHRpb25hbGx5IG1lcmdpbmcgc2hvcnQgYWRqYWNlbnQgbGluZXMuIFN1cHBvcnRzIGJvdGggYXV0b21hdGljIHdyYXBwaW5nIGR1cmluZyB0ZXh0XG4gKiBpbnB1dCBhbmQgbWFudWFsIGZvcm1hdHRpbmcgb2Ygc2VsZWN0ZWQgdGV4dCByYW5nZXMuXG4gKlxuICogKipFbmFibGU6KiogYGVkaXRvci5zZXRPcHRpb24oXCJoYXJkV3JhcFwiLCB0cnVlKWBcbiAqIG9yIGNvbmZpZ3VyZSBpdCBkdXJpbmcgZWRpdG9yIGluaXRpYWxpemF0aW9uIGluIHRoZSBvcHRpb25zIG9iamVjdC5cbiAqIEBtb2R1bGVcbiAqL1xuXCJ1c2Ugc3RyaWN0XCI7XG52YXIgUmFuZ2UgPSByZXF1aXJlKFwiLi4vcmFuZ2VcIikuUmFuZ2U7XG5mdW5jdGlvbiBoYXJkV3JhcChlZGl0b3IsIG9wdGlvbnMpIHtcbiAgICB2YXIgbWF4ID0gb3B0aW9ucy5jb2x1bW4gfHwgZWRpdG9yLmdldE9wdGlvbihcInByaW50TWFyZ2luQ29sdW1uXCIpO1xuICAgIHZhciBhbGxvd01lcmdlID0gb3B0aW9ucy5hbGxvd01lcmdlICE9IGZhbHNlO1xuICAgIHZhciByb3cgPSBNYXRoLm1pbihvcHRpb25zLnN0YXJ0Um93LCBvcHRpb25zLmVuZFJvdyk7XG4gICAgdmFyIGVuZFJvdyA9IE1hdGgubWF4KG9wdGlvbnMuc3RhcnRSb3csIG9wdGlvbnMuZW5kUm93KTtcbiAgICB2YXIgc2Vzc2lvbiA9IGVkaXRvci5zZXNzaW9uO1xuICAgIHdoaWxlIChyb3cgPD0gZW5kUm93KSB7XG4gICAgICAgIHZhciBsaW5lID0gc2Vzc2lvbi5nZXRMaW5lKHJvdyk7XG4gICAgICAgIGlmIChsaW5lLmxlbmd0aCA+IG1heCkge1xuICAgICAgICAgICAgdmFyIHNwYWNlID0gZmluZFNwYWNlKGxpbmUsIG1heCwgNSk7XG4gICAgICAgICAgICBpZiAoc3BhY2UpIHtcbiAgICAgICAgICAgICAgICB2YXIgaW5kZW50YXRpb24gPSAvXlxccyovLmV4ZWMobGluZSlbMF07XG4gICAgICAgICAgICAgICAgc2Vzc2lvbi5yZXBsYWNlKG5ldyBSYW5nZShyb3csIHNwYWNlLnN0YXJ0LCByb3csIHNwYWNlLmVuZCksIFwiXFxuXCIgKyBpbmRlbnRhdGlvbik7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbmRSb3crKztcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChhbGxvd01lcmdlICYmIC9cXFMvLnRlc3QobGluZSkgJiYgcm93ICE9IGVuZFJvdykge1xuICAgICAgICAgICAgdmFyIG5leHRMaW5lID0gc2Vzc2lvbi5nZXRMaW5lKHJvdyArIDEpO1xuICAgICAgICAgICAgaWYgKG5leHRMaW5lICYmIC9cXFMvLnRlc3QobmV4dExpbmUpKSB7XG4gICAgICAgICAgICAgICAgdmFyIHRyaW1tZWRMaW5lID0gbGluZS5yZXBsYWNlKC9cXHMrJC8sIFwiXCIpO1xuICAgICAgICAgICAgICAgIHZhciB0cmltbWVkTmV4dExpbmUgPSBuZXh0TGluZS5yZXBsYWNlKC9eXFxzKy8sIFwiXCIpO1xuICAgICAgICAgICAgICAgIHZhciBtZXJnZWRMaW5lID0gdHJpbW1lZExpbmUgKyBcIiBcIiArIHRyaW1tZWROZXh0TGluZTtcbiAgICAgICAgICAgICAgICB2YXIgc3BhY2UgPSBmaW5kU3BhY2UobWVyZ2VkTGluZSwgbWF4LCA1KTtcbiAgICAgICAgICAgICAgICBpZiAoc3BhY2UgJiYgc3BhY2Uuc3RhcnQgPiB0cmltbWVkTGluZS5sZW5ndGggfHwgbWVyZ2VkTGluZS5sZW5ndGggPCBtYXgpIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyIHJlcGxhY2VSYW5nZSA9IG5ldyBSYW5nZShyb3csIHRyaW1tZWRMaW5lLmxlbmd0aCwgcm93ICsgMSwgbmV4dExpbmUubGVuZ3RoIC0gdHJpbW1lZE5leHRMaW5lLmxlbmd0aCk7XG4gICAgICAgICAgICAgICAgICAgIHNlc3Npb24ucmVwbGFjZShyZXBsYWNlUmFuZ2UsIFwiIFwiKTtcbiAgICAgICAgICAgICAgICAgICAgcm93LS07XG4gICAgICAgICAgICAgICAgICAgIGVuZFJvdy0tO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmICh0cmltbWVkTGluZS5sZW5ndGggPCBsaW5lLmxlbmd0aCkge1xuICAgICAgICAgICAgICAgICAgICBzZXNzaW9uLnJlbW92ZShuZXcgUmFuZ2Uocm93LCB0cmltbWVkTGluZS5sZW5ndGgsIHJvdywgbGluZS5sZW5ndGgpKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcm93Kys7XG4gICAgfVxuICAgIGZ1bmN0aW9uIGZpbmRTcGFjZShsaW5lLCBtYXgsIG1pbikge1xuICAgICAgICBpZiAobGluZS5sZW5ndGggPCBtYXgpXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIHZhciBiZWZvcmUgPSBsaW5lLnNsaWNlKDAsIG1heCk7XG4gICAgICAgIHZhciBhZnRlciA9IGxpbmUuc2xpY2UobWF4KTtcbiAgICAgICAgdmFyIHNwYWNlQWZ0ZXIgPSAvXig/OihcXHMrKXwoXFxTKykoXFxzKykpLy5leGVjKGFmdGVyKTtcbiAgICAgICAgdmFyIHNwYWNlQmVmb3JlID0gLyg/OihcXHMrKXwoXFxzKykoXFxTKykpJC8uZXhlYyhiZWZvcmUpO1xuICAgICAgICB2YXIgc3RhcnQgPSAwO1xuICAgICAgICB2YXIgZW5kID0gMDtcbiAgICAgICAgaWYgKHNwYWNlQmVmb3JlICYmICFzcGFjZUJlZm9yZVsyXSkge1xuICAgICAgICAgICAgc3RhcnQgPSBtYXggLSBzcGFjZUJlZm9yZVsxXS5sZW5ndGg7XG4gICAgICAgICAgICBlbmQgPSBtYXg7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHNwYWNlQWZ0ZXIgJiYgIXNwYWNlQWZ0ZXJbMl0pIHtcbiAgICAgICAgICAgIGlmICghc3RhcnQpXG4gICAgICAgICAgICAgICAgc3RhcnQgPSBtYXg7XG4gICAgICAgICAgICBlbmQgPSBtYXggKyBzcGFjZUFmdGVyWzFdLmxlbmd0aDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoc3RhcnQpIHtcbiAgICAgICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICAgICAgc3RhcnQ6IHN0YXJ0LFxuICAgICAgICAgICAgICAgIGVuZDogZW5kXG4gICAgICAgICAgICB9O1xuICAgICAgICB9XG4gICAgICAgIGlmIChzcGFjZUJlZm9yZSAmJiBzcGFjZUJlZm9yZVsyXSAmJiBzcGFjZUJlZm9yZS5pbmRleCA+IG1pbikge1xuICAgICAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgICAgICBzdGFydDogc3BhY2VCZWZvcmUuaW5kZXgsXG4gICAgICAgICAgICAgICAgZW5kOiBzcGFjZUJlZm9yZS5pbmRleCArIHNwYWNlQmVmb3JlWzJdLmxlbmd0aFxuICAgICAgICAgICAgfTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoc3BhY2VBZnRlciAmJiBzcGFjZUFmdGVyWzJdKSB7XG4gICAgICAgICAgICBzdGFydCA9IG1heCArIHNwYWNlQWZ0ZXJbMl0ubGVuZ3RoO1xuICAgICAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgICAgICBzdGFydDogc3RhcnQsXG4gICAgICAgICAgICAgICAgZW5kOiBzdGFydCArIHNwYWNlQWZ0ZXJbM10ubGVuZ3RoXG4gICAgICAgICAgICB9O1xuICAgICAgICB9XG4gICAgfVxufVxuZnVuY3Rpb24gd3JhcEFmdGVySW5wdXQoZSkge1xuICAgIGlmIChlLmNvbW1hbmQubmFtZSA9PSBcImluc2VydHN0cmluZ1wiICYmIC9cXFMvLnRlc3QoZS5hcmdzKSkge1xuICAgICAgICB2YXIgZWRpdG9yID0gZS5lZGl0b3I7XG4gICAgICAgIHZhciBjdXJzb3IgPSBlZGl0b3Iuc2VsZWN0aW9uLmN1cnNvcjtcbiAgICAgICAgaWYgKGN1cnNvci5jb2x1bW4gPD0gZWRpdG9yLnJlbmRlcmVyLiRwcmludE1hcmdpbkNvbHVtbilcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgdmFyIGxhc3REZWx0YSA9IGVkaXRvci5zZXNzaW9uLiR1bmRvTWFuYWdlci4kbGFzdERlbHRhO1xuICAgICAgICBoYXJkV3JhcChlZGl0b3IsIHtcbiAgICAgICAgICAgIHN0YXJ0Um93OiBjdXJzb3Iucm93LCBlbmRSb3c6IGN1cnNvci5yb3csXG4gICAgICAgICAgICBhbGxvd01lcmdlOiBmYWxzZVxuICAgICAgICB9KTtcbiAgICAgICAgaWYgKGxhc3REZWx0YSAhPSBlZGl0b3Iuc2Vzc2lvbi4kdW5kb01hbmFnZXIuJGxhc3REZWx0YSlcbiAgICAgICAgICAgIGVkaXRvci5zZXNzaW9uLm1hcmtVbmRvR3JvdXAoKTtcbiAgICB9XG59XG52YXIgRWRpdG9yID0gcmVxdWlyZShcIi4uL2VkaXRvclwiKS5FZGl0b3I7XG5yZXF1aXJlKFwiLi4vY29uZmlnXCIpLmRlZmluZU9wdGlvbnMoRWRpdG9yLnByb3RvdHlwZSwgXCJlZGl0b3JcIiwge1xuICAgIGhhcmRXcmFwOiB7XG4gICAgICAgIHNldDogZnVuY3Rpb24gKHZhbCkge1xuICAgICAgICAgICAgaWYgKHZhbCkge1xuICAgICAgICAgICAgICAgIHRoaXMuY29tbWFuZHMub24oXCJhZnRlckV4ZWNcIiwgd3JhcEFmdGVySW5wdXQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhpcy5jb21tYW5kcy5vZmYoXCJhZnRlckV4ZWNcIiwgd3JhcEFmdGVySW5wdXQpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9LFxuICAgICAgICB2YWx1ZTogZmFsc2VcbiAgICB9XG59KTtcbmV4cG9ydHMuaGFyZFdyYXAgPSBoYXJkV3JhcDtcblxufSk7XG5cbmFjZS5kZWZpbmUoXCJhY2Uva2V5Ym9hcmQvdmltXCIsW1wicmVxdWlyZVwiLFwiZXhwb3J0c1wiLFwibW9kdWxlXCIsXCJhY2UvcmFuZ2VcIixcImFjZS9saWIvZXZlbnRfZW1pdHRlclwiLFwiYWNlL2xpYi9kb21cIixcImFjZS9saWIvb29wXCIsXCJhY2UvbGliL2tleXNcIixcImFjZS9saWIvZXZlbnRcIixcImFjZS9zZWFyY2hcIixcImFjZS9saWIvdXNlcmFnZW50XCIsXCJhY2Uvc2VhcmNoX2hpZ2hsaWdodFwiLFwiYWNlL2NvbW1hbmRzL211bHRpX3NlbGVjdF9jb21tYW5kc1wiLFwiYWNlL21vZGUvdGV4dFwiLFwiYWNlL2V4dC9oYXJkd3JhcFwiLFwiYWNlL211bHRpX3NlbGVjdFwiXSwgZnVuY3Rpb24ocmVxdWlyZSwgZXhwb3J0cywgbW9kdWxlKXsvLyBDb2RlTWlycm9yLCBjb3B5cmlnaHQgKGMpIGJ5IE1hcmlqbiBIYXZlcmJla2UgYW5kIG90aGVyc1xuJ3VzZSBzdHJpY3QnO1xuZnVuY3Rpb24gbG9nKCkge1xuICAgIHZhciBkID0gXCJcIjtcbiAgICBmdW5jdGlvbiBmb3JtYXQocCkge1xuICAgICAgICBpZiAodHlwZW9mIHAgIT0gXCJvYmplY3RcIilcbiAgICAgICAgICAgIHJldHVybiBwICsgXCJcIjtcbiAgICAgICAgaWYgKFwibGluZVwiIGluIHApIHtcbiAgICAgICAgICAgIHJldHVybiBwLmxpbmUgKyBcIjpcIiArIHAuY2g7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKFwiYW5jaG9yXCIgaW4gcCkge1xuICAgICAgICAgICAgcmV0dXJuIGZvcm1hdChwLmFuY2hvcikgKyBcIi0+XCIgKyBmb3JtYXQocC5oZWFkKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoQXJyYXkuaXNBcnJheShwKSlcbiAgICAgICAgICAgIHJldHVybiBcIltcIiArIHAubWFwKGZ1bmN0aW9uICh4KSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZvcm1hdCh4KTtcbiAgICAgICAgICAgIH0pICsgXCJdXCI7XG4gICAgICAgIHJldHVybiBKU09OLnN0cmluZ2lmeShwKTtcbiAgICB9XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIHAgPSBhcmd1bWVudHNbaV07XG4gICAgICAgIHZhciBmID0gZm9ybWF0KHApO1xuICAgICAgICBkICs9IGYgKyBcIiAgXCI7XG4gICAgfVxuICAgIGNvbnNvbGUubG9nKGQpO1xufVxudmFyIFJhbmdlID0gcmVxdWlyZShcIi4uL3JhbmdlXCIpLlJhbmdlO1xudmFyIEV2ZW50RW1pdHRlciA9IHJlcXVpcmUoXCIuLi9saWIvZXZlbnRfZW1pdHRlclwiKS5FdmVudEVtaXR0ZXI7XG52YXIgZG9tTGliID0gcmVxdWlyZShcIi4uL2xpYi9kb21cIik7XG52YXIgb29wID0gcmVxdWlyZShcIi4uL2xpYi9vb3BcIik7XG52YXIgS0VZUyA9IHJlcXVpcmUoXCIuLi9saWIva2V5c1wiKTtcbnZhciBldmVudCA9IHJlcXVpcmUoXCIuLi9saWIvZXZlbnRcIik7XG52YXIgU2VhcmNoID0gcmVxdWlyZShcIi4uL3NlYXJjaFwiKS5TZWFyY2g7XG52YXIgdXNlcmFnZW50ID0gcmVxdWlyZShcIi4uL2xpYi91c2VyYWdlbnRcIik7XG52YXIgU2VhcmNoSGlnaGxpZ2h0ID0gcmVxdWlyZShcIi4uL3NlYXJjaF9oaWdobGlnaHRcIikuU2VhcmNoSGlnaGxpZ2h0O1xudmFyIG11bHRpU2VsZWN0Q29tbWFuZHMgPSByZXF1aXJlKFwiLi4vY29tbWFuZHMvbXVsdGlfc2VsZWN0X2NvbW1hbmRzXCIpO1xudmFyIFRleHRNb2RlVG9rZW5SZSA9IHJlcXVpcmUoXCIuLi9tb2RlL3RleHRcIikuTW9kZS5wcm90b3R5cGUudG9rZW5SZTtcbnZhciBoYXJkV3JhcCA9IHJlcXVpcmUoXCIuLi9leHQvaGFyZHdyYXBcIikuaGFyZFdyYXA7XG5yZXF1aXJlKFwiLi4vbXVsdGlfc2VsZWN0XCIpO1xudmFyIENvZGVNaXJyb3IgPSBmdW5jdGlvbiAoYWNlKSB7XG4gICAgdGhpcy5hY2UgPSBhY2U7XG4gICAgdGhpcy5zdGF0ZSA9IHt9O1xuICAgIHRoaXMubWFya3MgPSB7fTtcbiAgICB0aGlzLm9wdGlvbnMgPSB7fTtcbiAgICB0aGlzLiR1aWQgPSAwO1xuICAgIHRoaXMub25DaGFuZ2UgPSB0aGlzLm9uQ2hhbmdlLmJpbmQodGhpcyk7XG4gICAgdGhpcy5vblNlbGVjdGlvbkNoYW5nZSA9IHRoaXMub25TZWxlY3Rpb25DaGFuZ2UuYmluZCh0aGlzKTtcbiAgICB0aGlzLm9uQmVmb3JlRW5kT3BlcmF0aW9uID0gdGhpcy5vbkJlZm9yZUVuZE9wZXJhdGlvbi5iaW5kKHRoaXMpO1xuICAgIHRoaXMuYWNlLm9uKCdjaGFuZ2UnLCB0aGlzLm9uQ2hhbmdlKTtcbiAgICB0aGlzLmFjZS5vbignY2hhbmdlU2VsZWN0aW9uJywgdGhpcy5vblNlbGVjdGlvbkNoYW5nZSk7XG4gICAgdGhpcy5hY2Uub24oJ2JlZm9yZUVuZE9wZXJhdGlvbicsIHRoaXMub25CZWZvcmVFbmRPcGVyYXRpb24pO1xufTtcbkNvZGVNaXJyb3IuUG9zID0gZnVuY3Rpb24gKGxpbmUsIGNoKSB7XG4gICAgaWYgKCEodGhpcyBpbnN0YW5jZW9mIFBvcykpXG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxpbmUsIGNoKTtcbiAgICB0aGlzLmxpbmUgPSBsaW5lO1xuICAgIHRoaXMuY2ggPSBjaDtcbn07XG5Db2RlTWlycm9yLmRlZmluZU9wdGlvbiA9IGZ1bmN0aW9uIChuYW1lLCB2YWwsIHNldHRlcikgeyB9O1xuQ29kZU1pcnJvci5jb21tYW5kcyA9IHtcbiAgICByZWRvOiBmdW5jdGlvbiAoY20pIHsgY20uYWNlLnJlZG8oKTsgfSxcbiAgICB1bmRvOiBmdW5jdGlvbiAoY20pIHsgY20uYWNlLnVuZG8oKTsgfSxcbiAgICBuZXdsaW5lQW5kSW5kZW50OiBmdW5jdGlvbiAoY20pIHsgY20uYWNlLmluc2VydChcIlxcblwiKTsgfSxcbiAgICBnb0xpbmVMZWZ0OiBmdW5jdGlvbiAoY20pIHsgY20uYWNlLnNlbGVjdGlvbi5tb3ZlQ3Vyc29yTGluZVN0YXJ0KCk7IH0sXG4gICAgZ29MaW5lUmlnaHQ6IGZ1bmN0aW9uIChjbSkgeyBjbS5hY2Uuc2VsZWN0aW9uLm1vdmVDdXJzb3JMaW5lRW5kKCk7IH1cbn07XG5Db2RlTWlycm9yLmtleU1hcCA9IHt9O1xuQ29kZU1pcnJvci5hZGRDbGFzcyA9IENvZGVNaXJyb3Iucm1DbGFzcyA9IGZ1bmN0aW9uICgpIHsgfTtcbkNvZGVNaXJyb3IuZV9zdG9wID0gQ29kZU1pcnJvci5lX3ByZXZlbnREZWZhdWx0ID0gZXZlbnQuc3RvcEV2ZW50O1xuQ29kZU1pcnJvci5rZXlOYW1lID0gZnVuY3Rpb24gKGUpIHtcbiAgICB2YXIga2V5ID0gKEtFWVNbZS5rZXlDb2RlXSB8fCBlLmtleSB8fCBcIlwiKTtcbiAgICBpZiAoa2V5Lmxlbmd0aCA9PSAxKVxuICAgICAgICBrZXkgPSBrZXkudG9VcHBlckNhc2UoKTtcbiAgICBrZXkgPSBldmVudC5nZXRNb2RpZmllclN0cmluZyhlKS5yZXBsYWNlKC8oXnwtKVxcdy9nLCBmdW5jdGlvbiAobSkge1xuICAgICAgICByZXR1cm4gbS50b1VwcGVyQ2FzZSgpO1xuICAgIH0pICsga2V5O1xuICAgIHJldHVybiBrZXk7XG59O1xuQ29kZU1pcnJvci5rZXlNYXBbJ2RlZmF1bHQnXSA9IGZ1bmN0aW9uIChrZXkpIHtcbiAgICByZXR1cm4gZnVuY3Rpb24gKGNtKSB7XG4gICAgICAgIHZhciBjbWQgPSBjbS5hY2UuY29tbWFuZHMuY29tbWFuZEtleUJpbmRpbmdba2V5LnRvTG93ZXJDYXNlKCldO1xuICAgICAgICByZXR1cm4gY21kICYmIGNtLmFjZS5leGVjQ29tbWFuZChjbWQpICE9PSBmYWxzZTtcbiAgICB9O1xufTtcbkNvZGVNaXJyb3IubG9va3VwS2V5ID0gZnVuY3Rpb24gbG9va3VwS2V5KGtleSwgbWFwLCBoYW5kbGUpIHtcbiAgICBpZiAoIW1hcClcbiAgICAgICAgbWFwID0gXCJkZWZhdWx0XCI7XG4gICAgaWYgKHR5cGVvZiBtYXAgPT0gXCJzdHJpbmdcIilcbiAgICAgICAgbWFwID0gQ29kZU1pcnJvci5rZXlNYXBbbWFwXSB8fCBDb2RlTWlycm9yLmtleU1hcFsnZGVmYXVsdCddO1xuICAgIHZhciBmb3VuZCA9IHR5cGVvZiBtYXAgPT0gXCJmdW5jdGlvblwiID8gbWFwKGtleSkgOiBtYXBba2V5XTtcbiAgICBpZiAoZm91bmQgPT09IGZhbHNlKVxuICAgICAgICByZXR1cm4gXCJub3RoaW5nXCI7XG4gICAgaWYgKGZvdW5kID09PSBcIi4uLlwiKVxuICAgICAgICByZXR1cm4gXCJtdWx0aVwiO1xuICAgIGlmIChmb3VuZCAhPSBudWxsICYmIGhhbmRsZShmb3VuZCkpXG4gICAgICAgIHJldHVybiBcImhhbmRsZWRcIjtcbiAgICBpZiAobWFwLmZhbGx0aHJvdWdoKSB7XG4gICAgICAgIGlmICghQXJyYXkuaXNBcnJheShtYXAuZmFsbHRocm91Z2gpKVxuICAgICAgICAgICAgcmV0dXJuIGxvb2t1cEtleShrZXksIG1hcC5mYWxsdGhyb3VnaCwgaGFuZGxlKTtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBtYXAuZmFsbHRocm91Z2gubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHZhciByZXN1bHQgPSBsb29rdXBLZXkoa2V5LCBtYXAuZmFsbHRocm91Z2hbaV0sIGhhbmRsZSk7XG4gICAgICAgICAgICBpZiAocmVzdWx0KVxuICAgICAgICAgICAgICAgIHJldHVybiByZXN1bHQ7XG4gICAgICAgIH1cbiAgICB9XG59O1xuQ29kZU1pcnJvci5maW5kTWF0Y2hpbmdUYWcgPSBmdW5jdGlvbiAoY20sIGhlYWQpIHtcbiAgICByZXR1cm4gY20uZmluZE1hdGNoaW5nVGFnKGhlYWQpO1xufTtcbkNvZGVNaXJyb3IuZmluZEVuY2xvc2luZ1RhZyA9IGZ1bmN0aW9uIChjbSwgaGVhZCkge1xufTtcbkNvZGVNaXJyb3Iuc2lnbmFsID0gZnVuY3Rpb24gKG8sIG5hbWUsIGUpIHsgcmV0dXJuIG8uX3NpZ25hbChuYW1lLCBlKTsgfTtcbkNvZGVNaXJyb3Iub24gPSBldmVudC5hZGRMaXN0ZW5lcjtcbkNvZGVNaXJyb3Iub2ZmID0gZXZlbnQucmVtb3ZlTGlzdGVuZXI7XG5Db2RlTWlycm9yLmlzV29yZENoYXIgPSBmdW5jdGlvbiAoY2gpIHtcbiAgICBpZiAoY2ggPCBcIlxceDdmXCIpXG4gICAgICAgIHJldHVybiAvXlxcdyQvLnRlc3QoY2gpO1xuICAgIFRleHRNb2RlVG9rZW5SZS5sYXN0SW5kZXggPSAwO1xuICAgIHJldHVybiBUZXh0TW9kZVRva2VuUmUudGVzdChjaCk7XG59O1xuKGZ1bmN0aW9uICgpIHtcbiAgICBvb3AuaW1wbGVtZW50KENvZGVNaXJyb3IucHJvdG90eXBlLCBFdmVudEVtaXR0ZXIpO1xuICAgIHRoaXMuZGVzdHJveSA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdGhpcy5hY2Uub2ZmKCdjaGFuZ2UnLCB0aGlzLm9uQ2hhbmdlKTtcbiAgICAgICAgdGhpcy5hY2Uub2ZmKCdjaGFuZ2VTZWxlY3Rpb24nLCB0aGlzLm9uU2VsZWN0aW9uQ2hhbmdlKTtcbiAgICAgICAgdGhpcy5hY2Uub2ZmKCdiZWZvcmVFbmRPcGVyYXRpb24nLCB0aGlzLm9uQmVmb3JlRW5kT3BlcmF0aW9uKTtcbiAgICAgICAgdGhpcy5yZW1vdmVPdmVybGF5KCk7XG4gICAgfTtcbiAgICB0aGlzLnZpcnR1YWxTZWxlY3Rpb25Nb2RlID0gZnVuY3Rpb24gKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5hY2UuaW5WaXJ0dWFsU2VsZWN0aW9uTW9kZSAmJiB0aGlzLmFjZS5zZWxlY3Rpb24uaW5kZXg7XG4gICAgfTtcbiAgICB0aGlzLm9uQ2hhbmdlID0gZnVuY3Rpb24gKGRlbHRhKSB7XG4gICAgICAgIGlmICh0aGlzLiRsaW5lSGFuZGxlQ2hhbmdlcykge1xuICAgICAgICAgICAgdGhpcy4kbGluZUhhbmRsZUNoYW5nZXMucHVzaChkZWx0YSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGNoYW5nZSA9IHsgdGV4dDogZGVsdGEuYWN0aW9uWzBdID09ICdpJyA/IGRlbHRhLmxpbmVzIDogW10gfTtcbiAgICAgICAgdmFyIGN1ck9wID0gdGhpcy5jdXJPcCA9IHRoaXMuY3VyT3AgfHwge307XG4gICAgICAgIGlmICghY3VyT3AuY2hhbmdlSGFuZGxlcnMpXG4gICAgICAgICAgICBjdXJPcC5jaGFuZ2VIYW5kbGVycyA9IHRoaXMuX2V2ZW50UmVnaXN0cnlbXCJjaGFuZ2VcIl0gJiYgdGhpcy5fZXZlbnRSZWdpc3RyeVtcImNoYW5nZVwiXS5zbGljZSgpO1xuICAgICAgICBpZiAoIWN1ck9wLmxhc3RDaGFuZ2UpIHtcbiAgICAgICAgICAgIGN1ck9wLmxhc3RDaGFuZ2UgPSBjdXJPcC5jaGFuZ2UgPSBjaGFuZ2U7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBjdXJPcC5sYXN0Q2hhbmdlLm5leHQgPSBjdXJPcC5sYXN0Q2hhbmdlID0gY2hhbmdlO1xuICAgICAgICB9XG4gICAgICAgIHRoaXMuJHVwZGF0ZU1hcmtlcnMoZGVsdGEpO1xuICAgIH07XG4gICAgdGhpcy5vblNlbGVjdGlvbkNoYW5nZSA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdmFyIGN1ck9wID0gdGhpcy5jdXJPcCA9IHRoaXMuY3VyT3AgfHwge307XG4gICAgICAgIGlmICghY3VyT3AuY3Vyc29yQWN0aXZpdHlIYW5kbGVycylcbiAgICAgICAgICAgIGN1ck9wLmN1cnNvckFjdGl2aXR5SGFuZGxlcnMgPSB0aGlzLl9ldmVudFJlZ2lzdHJ5W1wiY3Vyc29yQWN0aXZpdHlcIl0gJiYgdGhpcy5fZXZlbnRSZWdpc3RyeVtcImN1cnNvckFjdGl2aXR5XCJdLnNsaWNlKCk7XG4gICAgICAgIHRoaXMuY3VyT3AuY3Vyc29yQWN0aXZpdHkgPSB0cnVlO1xuICAgICAgICBpZiAodGhpcy5hY2UuaW5NdWx0aVNlbGVjdE1vZGUpIHtcbiAgICAgICAgICAgIHRoaXMuYWNlLmtleUJpbmRpbmcucmVtb3ZlS2V5Ym9hcmRIYW5kbGVyKG11bHRpU2VsZWN0Q29tbWFuZHMua2V5Ym9hcmRIYW5kbGVyKTtcbiAgICAgICAgfVxuICAgIH07XG4gICAgdGhpcy5vcGVyYXRpb24gPSBmdW5jdGlvbiAoZm4sIGZvcmNlKSB7XG4gICAgICAgIGlmICghZm9yY2UgJiYgdGhpcy5jdXJPcCB8fCBmb3JjZSAmJiB0aGlzLmN1ck9wICYmIHRoaXMuY3VyT3AuZm9yY2UpIHtcbiAgICAgICAgICAgIHJldHVybiBmbigpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChmb3JjZSB8fCAhdGhpcy5hY2UuY3VyT3ApIHtcbiAgICAgICAgICAgIGlmICh0aGlzLmN1ck9wKVxuICAgICAgICAgICAgICAgIHRoaXMub25CZWZvcmVFbmRPcGVyYXRpb24oKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIXRoaXMuYWNlLmN1ck9wKSB7XG4gICAgICAgICAgICB2YXIgcHJldk9wID0gdGhpcy5hY2UucHJldk9wO1xuICAgICAgICAgICAgdGhpcy5hY2Uuc3RhcnRPcGVyYXRpb24oe1xuICAgICAgICAgICAgICAgIGNvbW1hbmQ6IHsgbmFtZTogXCJ2aW1cIiwgc2Nyb2xsSW50b1ZpZXc6IFwiY3Vyc29yXCIgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGN1ck9wID0gdGhpcy5jdXJPcCA9IHRoaXMuY3VyT3AgfHwge307XG4gICAgICAgIHRoaXMuY3VyT3AuZm9yY2UgPSBmb3JjZTtcbiAgICAgICAgdmFyIHJlc3VsdCA9IGZuKCk7XG4gICAgICAgIGlmICh0aGlzLmFjZS5jdXJPcCAmJiB0aGlzLmFjZS5jdXJPcC5jb21tYW5kLm5hbWUgPT0gXCJ2aW1cIikge1xuICAgICAgICAgICAgaWYgKHRoaXMuc3RhdGUuZGlhbG9nKVxuICAgICAgICAgICAgICAgIHRoaXMuYWNlLmN1ck9wLmNvbW1hbmQuc2Nyb2xsSW50b1ZpZXcgPSB0aGlzLmFjZS5jdXJPcC52aW1EaWFsb2dTY3JvbGw7XG4gICAgICAgICAgICB0aGlzLmFjZS5lbmRPcGVyYXRpb24oKTtcbiAgICAgICAgICAgIGlmICghY3VyT3AuY3Vyc29yQWN0aXZpdHkgJiYgIWN1ck9wLmxhc3RDaGFuZ2UgJiYgcHJldk9wKVxuICAgICAgICAgICAgICAgIHRoaXMuYWNlLnByZXZPcCA9IHByZXZPcDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZm9yY2UgfHwgIXRoaXMuYWNlLmN1ck9wKSB7XG4gICAgICAgICAgICBpZiAodGhpcy5jdXJPcClcbiAgICAgICAgICAgICAgICB0aGlzLm9uQmVmb3JlRW5kT3BlcmF0aW9uKCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHJlc3VsdDtcbiAgICB9O1xuICAgIHRoaXMub25CZWZvcmVFbmRPcGVyYXRpb24gPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHZhciBvcCA9IHRoaXMuY3VyT3A7XG4gICAgICAgIGlmIChvcCkge1xuICAgICAgICAgICAgaWYgKG9wLmNoYW5nZSkge1xuICAgICAgICAgICAgICAgIHRoaXMuc2lnbmFsKFwiY2hhbmdlXCIsIG9wLmNoYW5nZSwgb3ApO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG9wICYmIG9wLmN1cnNvckFjdGl2aXR5KSB7XG4gICAgICAgICAgICAgICAgdGhpcy5zaWduYWwoXCJjdXJzb3JBY3Rpdml0eVwiLCBudWxsLCBvcCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB0aGlzLmN1ck9wID0gbnVsbDtcbiAgICAgICAgfVxuICAgIH07XG4gICAgdGhpcy5zaWduYWwgPSBmdW5jdGlvbiAoZXZlbnROYW1lLCBlLCBoYW5kbGVycykge1xuICAgICAgICB2YXIgbGlzdGVuZXJzID0gaGFuZGxlcnMgPyBoYW5kbGVyc1tldmVudE5hbWUgKyBcIkhhbmRsZXJzXCJdXG4gICAgICAgICAgICA6ICh0aGlzLl9ldmVudFJlZ2lzdHJ5IHx8IHt9KVtldmVudE5hbWVdO1xuICAgICAgICBpZiAoIWxpc3RlbmVycylcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgbGlzdGVuZXJzID0gbGlzdGVuZXJzLnNsaWNlKCk7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbGlzdGVuZXJzLmxlbmd0aDsgaSsrKVxuICAgICAgICAgICAgbGlzdGVuZXJzW2ldKHRoaXMsIGUpO1xuICAgIH07XG4gICAgdGhpcy5maXJzdExpbmUgPSBmdW5jdGlvbiAoKSB7IHJldHVybiAwOyB9O1xuICAgIHRoaXMubGFzdExpbmUgPSBmdW5jdGlvbiAoKSB7IHJldHVybiB0aGlzLmFjZS5zZXNzaW9uLmdldExlbmd0aCgpIC0gMTsgfTtcbiAgICB0aGlzLmxpbmVDb3VudCA9IGZ1bmN0aW9uICgpIHsgcmV0dXJuIHRoaXMuYWNlLnNlc3Npb24uZ2V0TGVuZ3RoKCk7IH07XG4gICAgdGhpcy5zZXRDdXJzb3IgPSBmdW5jdGlvbiAobGluZSwgY2gpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBsaW5lID09PSAnb2JqZWN0Jykge1xuICAgICAgICAgICAgY2ggPSBsaW5lLmNoO1xuICAgICAgICAgICAgbGluZSA9IGxpbmUubGluZTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgc2hvdWxkU2Nyb2xsID0gIXRoaXMuY3VyT3AgJiYgIXRoaXMuYWNlLmluVmlydHVhbFNlbGVjdGlvbk1vZGU7XG4gICAgICAgIGlmICghdGhpcy5hY2UuaW5WaXJ0dWFsU2VsZWN0aW9uTW9kZSlcbiAgICAgICAgICAgIHRoaXMuYWNlLmV4aXRNdWx0aVNlbGVjdE1vZGUoKTtcbiAgICAgICAgdGhpcy5hY2Uuc2Vzc2lvbi51bmZvbGQoeyByb3c6IGxpbmUsIGNvbHVtbjogY2ggfSk7XG4gICAgICAgIHRoaXMuYWNlLnNlbGVjdGlvbi5tb3ZlVG8obGluZSwgY2gpO1xuICAgICAgICBpZiAoc2hvdWxkU2Nyb2xsKSB7XG4gICAgICAgICAgICB0aGlzLmFjZS5yZW5kZXJlci5zY3JvbGxDdXJzb3JJbnRvVmlldygpO1xuICAgICAgICAgICAgdGhpcy5hY2UuZW5kT3BlcmF0aW9uKCk7XG4gICAgICAgIH1cbiAgICB9O1xuICAgIHRoaXMuZ2V0Q3Vyc29yID0gZnVuY3Rpb24gKHApIHtcbiAgICAgICAgdmFyIHNlbCA9IHRoaXMuYWNlLnNlbGVjdGlvbjtcbiAgICAgICAgdmFyIHBvcyA9IHAgPT0gJ2FuY2hvcicgPyAoc2VsLmlzRW1wdHkoKSA/IHNlbC5sZWFkIDogc2VsLmFuY2hvcikgOlxuICAgICAgICAgICAgcCA9PSAnaGVhZCcgfHwgIXAgPyBzZWwubGVhZCA6IHNlbC5nZXRSYW5nZSgpW3BdO1xuICAgICAgICByZXR1cm4gdG9DbVBvcyhwb3MpO1xuICAgIH07XG4gICAgdGhpcy5saXN0U2VsZWN0aW9ucyA9IGZ1bmN0aW9uIChwKSB7XG4gICAgICAgIHZhciByYW5nZXMgPSB0aGlzLmFjZS5tdWx0aVNlbGVjdC5yYW5nZUxpc3QucmFuZ2VzO1xuICAgICAgICBpZiAoIXJhbmdlcy5sZW5ndGggfHwgdGhpcy5hY2UuaW5WaXJ0dWFsU2VsZWN0aW9uTW9kZSlcbiAgICAgICAgICAgIHJldHVybiBbeyBhbmNob3I6IHRoaXMuZ2V0Q3Vyc29yKCdhbmNob3InKSwgaGVhZDogdGhpcy5nZXRDdXJzb3IoJ2hlYWQnKSB9XTtcbiAgICAgICAgcmV0dXJuIHJhbmdlcy5tYXAoZnVuY3Rpb24gKHIpIHtcbiAgICAgICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICAgICAgYW5jaG9yOiB0aGlzLmNsaXBQb3ModG9DbVBvcyhyLmN1cnNvciA9PSByLmVuZCA/IHIuc3RhcnQgOiByLmVuZCkpLFxuICAgICAgICAgICAgICAgIGhlYWQ6IHRoaXMuY2xpcFBvcyh0b0NtUG9zKHIuY3Vyc29yKSlcbiAgICAgICAgICAgIH07XG4gICAgICAgIH0sIHRoaXMpO1xuICAgIH07XG4gICAgdGhpcy5zZXRTZWxlY3Rpb25zID0gZnVuY3Rpb24gKHAsIHByaW1JbmRleCkge1xuICAgICAgICB2YXIgc2VsID0gdGhpcy5hY2UubXVsdGlTZWxlY3Q7XG4gICAgICAgIHZhciByYW5nZXMgPSBwLm1hcChmdW5jdGlvbiAoeCkge1xuICAgICAgICAgICAgdmFyIGFuY2hvciA9IHRvQWNlUG9zKHguYW5jaG9yKTtcbiAgICAgICAgICAgIHZhciBoZWFkID0gdG9BY2VQb3MoeC5oZWFkKTtcbiAgICAgICAgICAgIHZhciByID0gUmFuZ2UuY29tcGFyZVBvaW50cyhhbmNob3IsIGhlYWQpIDwgMFxuICAgICAgICAgICAgICAgID8gbmV3IFJhbmdlLmZyb21Qb2ludHMoYW5jaG9yLCBoZWFkKVxuICAgICAgICAgICAgICAgIDogbmV3IFJhbmdlLmZyb21Qb2ludHMoaGVhZCwgYW5jaG9yKTtcbiAgICAgICAgICAgIHIuY3Vyc29yID0gUmFuZ2UuY29tcGFyZVBvaW50cyhyLnN0YXJ0LCBoZWFkKSA/IHIuZW5kIDogci5zdGFydDtcbiAgICAgICAgICAgIHJldHVybiByO1xuICAgICAgICB9KTtcbiAgICAgICAgaWYgKHRoaXMuYWNlLmluVmlydHVhbFNlbGVjdGlvbk1vZGUpIHtcbiAgICAgICAgICAgIHRoaXMuYWNlLnNlbGVjdGlvbi5mcm9tT3JpZW50ZWRSYW5nZShyYW5nZXNbMF0pO1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIGlmICghcHJpbUluZGV4KSB7XG4gICAgICAgICAgICByYW5nZXMgPSByYW5nZXMucmV2ZXJzZSgpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKHJhbmdlc1twcmltSW5kZXhdKSB7XG4gICAgICAgICAgICByYW5nZXMucHVzaChyYW5nZXMuc3BsaWNlKHByaW1JbmRleCwgMSlbMF0pO1xuICAgICAgICB9XG4gICAgICAgIHNlbC50b1NpbmdsZVJhbmdlKHJhbmdlc1swXS5jbG9uZSgpKTtcbiAgICAgICAgdmFyIHNlc3Npb24gPSB0aGlzLmFjZS5zZXNzaW9uO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJhbmdlcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIHJhbmdlID0gc2Vzc2lvbi4kY2xpcFJhbmdlVG9Eb2N1bWVudChyYW5nZXNbaV0pOyAvLyB0b2RvIHdoeSBhY2UgZG9lc24ndCBkbyB0aGlzP1xuICAgICAgICAgICAgc2VsLmFkZFJhbmdlKHJhbmdlKTtcbiAgICAgICAgfVxuICAgIH07XG4gICAgdGhpcy5zZXRTZWxlY3Rpb24gPSBmdW5jdGlvbiAoYSwgaCwgb3B0aW9ucykge1xuICAgICAgICB2YXIgc2VsID0gdGhpcy5hY2Uuc2VsZWN0aW9uO1xuICAgICAgICBzZWwubW92ZVRvKGEubGluZSwgYS5jaCk7XG4gICAgICAgIHNlbC5zZWxlY3RUbyhoLmxpbmUsIGguY2gpO1xuICAgICAgICBpZiAob3B0aW9ucyAmJiBvcHRpb25zLm9yaWdpbiA9PSAnKm1vdXNlJykge1xuICAgICAgICAgICAgdGhpcy5vbkJlZm9yZUVuZE9wZXJhdGlvbigpO1xuICAgICAgICB9XG4gICAgfTtcbiAgICB0aGlzLnNvbWV0aGluZ1NlbGVjdGVkID0gZnVuY3Rpb24gKHApIHtcbiAgICAgICAgcmV0dXJuICF0aGlzLmFjZS5zZWxlY3Rpb24uaXNFbXB0eSgpO1xuICAgIH07XG4gICAgdGhpcy5jbGlwUG9zID0gZnVuY3Rpb24gKHApIHtcbiAgICAgICAgdmFyIHBvcyA9IHRoaXMuYWNlLnNlc3Npb24uJGNsaXBQb3NpdGlvblRvRG9jdW1lbnQocC5saW5lLCBwLmNoKTtcbiAgICAgICAgcmV0dXJuIHRvQ21Qb3MocG9zKTtcbiAgICB9O1xuICAgIHRoaXMuZm9sZENvZGUgPSBmdW5jdGlvbiAocG9zKSB7XG4gICAgICAgIHRoaXMuYWNlLnNlc3Npb24uJHRvZ2dsZUZvbGRXaWRnZXQocG9zLmxpbmUsIHt9KTtcbiAgICB9O1xuICAgIHRoaXMubWFya1RleHQgPSBmdW5jdGlvbiAoY3Vyc29yKSB7XG4gICAgICAgIHJldHVybiB7IGNsZWFyOiBmdW5jdGlvbiAoKSB7IH0sIGZpbmQ6IGZ1bmN0aW9uICgpIHsgfSB9O1xuICAgIH07XG4gICAgdGhpcy4kdXBkYXRlTWFya2VycyA9IGZ1bmN0aW9uIChkZWx0YSkge1xuICAgICAgICB2YXIgaXNJbnNlcnQgPSBkZWx0YS5hY3Rpb24gPT0gXCJpbnNlcnRcIjtcbiAgICAgICAgdmFyIHN0YXJ0ID0gZGVsdGEuc3RhcnQ7XG4gICAgICAgIHZhciBlbmQgPSBkZWx0YS5lbmQ7XG4gICAgICAgIHZhciByb3dTaGlmdCA9IChlbmQucm93IC0gc3RhcnQucm93KSAqIChpc0luc2VydCA/IDEgOiAtMSk7XG4gICAgICAgIHZhciBjb2xTaGlmdCA9IChlbmQuY29sdW1uIC0gc3RhcnQuY29sdW1uKSAqIChpc0luc2VydCA/IDEgOiAtMSk7XG4gICAgICAgIGlmIChpc0luc2VydClcbiAgICAgICAgICAgIGVuZCA9IHN0YXJ0O1xuICAgICAgICBmb3IgKHZhciBpIGluIHRoaXMubWFya3MpIHtcbiAgICAgICAgICAgIHZhciBwb2ludCA9IHRoaXMubWFya3NbaV07XG4gICAgICAgICAgICB2YXIgY21wID0gUmFuZ2UuY29tcGFyZVBvaW50cyhwb2ludCwgc3RhcnQpO1xuICAgICAgICAgICAgaWYgKGNtcCA8IDApIHtcbiAgICAgICAgICAgICAgICBjb250aW51ZTsgLy8gZGVsdGEgc3RhcnRzIGFmdGVyIHRoZSByYW5nZVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGNtcCA9PT0gMCkge1xuICAgICAgICAgICAgICAgIGlmIChpc0luc2VydCkge1xuICAgICAgICAgICAgICAgICAgICBpZiAoIXBvaW50LiRpbnNlcnRSaWdodCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgY21wID0gMTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChwb2ludC5iaWFzID09IDEpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNtcCA9IDE7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBwb2ludC5iaWFzID0gLTE7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZhciBjbXAyID0gaXNJbnNlcnQgPyBjbXAgOiBSYW5nZS5jb21wYXJlUG9pbnRzKHBvaW50LCBlbmQpO1xuICAgICAgICAgICAgaWYgKGNtcDIgPiAwKSB7XG4gICAgICAgICAgICAgICAgcG9pbnQucm93ICs9IHJvd1NoaWZ0O1xuICAgICAgICAgICAgICAgIHBvaW50LmNvbHVtbiArPSBwb2ludC5yb3cgPT0gZW5kLnJvdyA/IGNvbFNoaWZ0IDogMDtcbiAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmICghaXNJbnNlcnQgJiYgY21wMiA8PSAwKSB7XG4gICAgICAgICAgICAgICAgcG9pbnQucm93ID0gc3RhcnQucm93O1xuICAgICAgICAgICAgICAgIHBvaW50LmNvbHVtbiA9IHN0YXJ0LmNvbHVtbjtcbiAgICAgICAgICAgICAgICBpZiAoY21wMiA9PT0gMClcbiAgICAgICAgICAgICAgICAgICAgcG9pbnQuYmlhcyA9IDE7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9O1xuICAgIHZhciBNYXJrZXIgPSBmdW5jdGlvbiAoY20sIGlkLCByb3csIGNvbHVtbikge1xuICAgICAgICB0aGlzLmNtID0gY207XG4gICAgICAgIHRoaXMuaWQgPSBpZDtcbiAgICAgICAgdGhpcy5yb3cgPSByb3c7XG4gICAgICAgIHRoaXMuY29sdW1uID0gY29sdW1uO1xuICAgICAgICBjbS5tYXJrc1t0aGlzLmlkXSA9IHRoaXM7XG4gICAgfTtcbiAgICBNYXJrZXIucHJvdG90eXBlLmNsZWFyID0gZnVuY3Rpb24gKCkgeyBkZWxldGUgdGhpcy5jbS5tYXJrc1t0aGlzLmlkXTsgfTtcbiAgICBNYXJrZXIucHJvdG90eXBlLmZpbmQgPSBmdW5jdGlvbiAoKSB7IHJldHVybiB0b0NtUG9zKHRoaXMpOyB9O1xuICAgIHRoaXMuc2V0Qm9va21hcmsgPSBmdW5jdGlvbiAoY3Vyc29yLCBvcHRpb25zKSB7XG4gICAgICAgIHZhciBibSA9IG5ldyBNYXJrZXIodGhpcywgdGhpcy4kdWlkKyssIGN1cnNvci5saW5lLCBjdXJzb3IuY2gpO1xuICAgICAgICBpZiAoIW9wdGlvbnMgfHwgIW9wdGlvbnMuaW5zZXJ0TGVmdClcbiAgICAgICAgICAgIGJtLiRpbnNlcnRSaWdodCA9IHRydWU7XG4gICAgICAgIHRoaXMubWFya3NbYm0uaWRdID0gYm07XG4gICAgICAgIHJldHVybiBibTtcbiAgICB9O1xuICAgIHRoaXMubW92ZUggPSBmdW5jdGlvbiAoaW5jcmVtZW50LCB1bml0KSB7XG4gICAgICAgIGlmICh1bml0ID09ICdjaGFyJykge1xuICAgICAgICAgICAgdmFyIHNlbCA9IHRoaXMuYWNlLnNlbGVjdGlvbjtcbiAgICAgICAgICAgIHNlbC5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICAgICAgc2VsLm1vdmVDdXJzb3JCeSgwLCBpbmNyZW1lbnQpO1xuICAgICAgICB9XG4gICAgfTtcbiAgICB0aGlzLmZpbmRQb3NWID0gZnVuY3Rpb24gKHN0YXJ0LCBhbW91bnQsIHVuaXQsIGdvYWxDb2x1bW4pIHtcbiAgICAgICAgaWYgKHVuaXQgPT0gJ3BhZ2UnKSB7XG4gICAgICAgICAgICB2YXIgcmVuZGVyZXIgPSB0aGlzLmFjZS5yZW5kZXJlcjtcbiAgICAgICAgICAgIHZhciBjb25maWcgPSByZW5kZXJlci5sYXllckNvbmZpZztcbiAgICAgICAgICAgIGFtb3VudCA9IGFtb3VudCAqIE1hdGguZmxvb3IoY29uZmlnLmhlaWdodCAvIGNvbmZpZy5saW5lSGVpZ2h0KTtcbiAgICAgICAgICAgIHVuaXQgPSAnbGluZSc7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHVuaXQgPT0gJ2xpbmUnKSB7XG4gICAgICAgICAgICB2YXIgc2NyZWVuUG9zID0gdGhpcy5hY2Uuc2Vzc2lvbi5kb2N1bWVudFRvU2NyZWVuUG9zaXRpb24oc3RhcnQubGluZSwgc3RhcnQuY2gpO1xuICAgICAgICAgICAgaWYgKGdvYWxDb2x1bW4gIT0gbnVsbClcbiAgICAgICAgICAgICAgICBzY3JlZW5Qb3MuY29sdW1uID0gZ29hbENvbHVtbjtcbiAgICAgICAgICAgIHNjcmVlblBvcy5yb3cgKz0gYW1vdW50O1xuICAgICAgICAgICAgc2NyZWVuUG9zLnJvdyA9IE1hdGgubWluKE1hdGgubWF4KDAsIHNjcmVlblBvcy5yb3cpLCB0aGlzLmFjZS5zZXNzaW9uLmdldFNjcmVlbkxlbmd0aCgpIC0gMSk7XG4gICAgICAgICAgICB2YXIgcG9zID0gdGhpcy5hY2Uuc2Vzc2lvbi5zY3JlZW5Ub0RvY3VtZW50UG9zaXRpb24oc2NyZWVuUG9zLnJvdywgc2NyZWVuUG9zLmNvbHVtbik7XG4gICAgICAgICAgICByZXR1cm4gdG9DbVBvcyhwb3MpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgZGVidWdnZXI7XG4gICAgICAgIH1cbiAgICB9O1xuICAgIHRoaXMuY2hhckNvb3JkcyA9IGZ1bmN0aW9uIChwb3MsIG1vZGUpIHtcbiAgICAgICAgaWYgKG1vZGUgPT0gJ2RpdicgfHwgIW1vZGUpIHtcbiAgICAgICAgICAgIHZhciBzYyA9IHRoaXMuYWNlLnNlc3Npb24uZG9jdW1lbnRUb1NjcmVlblBvc2l0aW9uKHBvcy5saW5lLCBwb3MuY2gpO1xuICAgICAgICAgICAgcmV0dXJuIHsgbGVmdDogc2MuY29sdW1uLCB0b3A6IHNjLnJvdyB9O1xuICAgICAgICB9XG4gICAgICAgIGlmIChtb2RlID09ICdsb2NhbCcpIHtcbiAgICAgICAgICAgIHZhciByZW5kZXJlciA9IHRoaXMuYWNlLnJlbmRlcmVyO1xuICAgICAgICAgICAgdmFyIHNjID0gdGhpcy5hY2Uuc2Vzc2lvbi5kb2N1bWVudFRvU2NyZWVuUG9zaXRpb24ocG9zLmxpbmUsIHBvcy5jaCk7XG4gICAgICAgICAgICB2YXIgbGggPSByZW5kZXJlci5sYXllckNvbmZpZy5saW5lSGVpZ2h0O1xuICAgICAgICAgICAgdmFyIGN3ID0gcmVuZGVyZXIubGF5ZXJDb25maWcuY2hhcmFjdGVyV2lkdGg7XG4gICAgICAgICAgICB2YXIgdG9wID0gbGggKiBzYy5yb3c7XG4gICAgICAgICAgICByZXR1cm4geyBsZWZ0OiBzYy5jb2x1bW4gKiBjdywgdG9wOiB0b3AsIGJvdHRvbTogdG9wICsgbGggfTtcbiAgICAgICAgfVxuICAgIH07XG4gICAgdGhpcy5jb29yZHNDaGFyID0gZnVuY3Rpb24gKHBvcywgbW9kZSkge1xuICAgICAgICB2YXIgcmVuZGVyZXIgPSB0aGlzLmFjZS5yZW5kZXJlcjtcbiAgICAgICAgaWYgKG1vZGUgPT0gJ2xvY2FsJykge1xuICAgICAgICAgICAgdmFyIHJvdyA9IE1hdGgubWF4KDAsIE1hdGguZmxvb3IocG9zLnRvcCAvIHJlbmRlcmVyLmxpbmVIZWlnaHQpKTtcbiAgICAgICAgICAgIHZhciBjb2wgPSBNYXRoLm1heCgwLCBNYXRoLmZsb29yKHBvcy5sZWZ0IC8gcmVuZGVyZXIuY2hhcmFjdGVyV2lkdGgpKTtcbiAgICAgICAgICAgIHZhciBjaCA9IHJlbmRlcmVyLnNlc3Npb24uc2NyZWVuVG9Eb2N1bWVudFBvc2l0aW9uKHJvdywgY29sKTtcbiAgICAgICAgICAgIHJldHVybiB0b0NtUG9zKGNoKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChtb2RlID09ICdkaXYnKSB7XG4gICAgICAgICAgICB0aHJvdyBcIm5vdCBpbXBsZW1lbnRlZFwiO1xuICAgICAgICB9XG4gICAgfTtcbiAgICB0aGlzLmdldFNlYXJjaEN1cnNvciA9IGZ1bmN0aW9uIChxdWVyeSwgcG9zLCBjYXNlRm9sZCkge1xuICAgICAgICB2YXIgY2FzZVNlbnNpdGl2ZSA9IGZhbHNlO1xuICAgICAgICB2YXIgaXNSZWdleHAgPSBmYWxzZTtcbiAgICAgICAgaWYgKHF1ZXJ5IGluc3RhbmNlb2YgUmVnRXhwICYmICFxdWVyeS5nbG9iYWwpIHtcbiAgICAgICAgICAgIGNhc2VTZW5zaXRpdmUgPSAhcXVlcnkuaWdub3JlQ2FzZTtcbiAgICAgICAgICAgIHF1ZXJ5ID0gcXVlcnkuc291cmNlO1xuICAgICAgICAgICAgaXNSZWdleHAgPSB0cnVlO1xuICAgICAgICB9XG4gICAgICAgIGlmIChxdWVyeSA9PSBcIlxcXFxuXCIpIHtcbiAgICAgICAgICAgIHF1ZXJ5ID0gXCJcXG5cIjtcbiAgICAgICAgICAgIGlzUmVnZXhwID0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIHNlYXJjaCA9IG5ldyBTZWFyY2goKTtcbiAgICAgICAgaWYgKHBvcy5jaCA9PSB1bmRlZmluZWQpXG4gICAgICAgICAgICBwb3MuY2ggPSBOdW1iZXIuTUFYX1ZBTFVFO1xuICAgICAgICB2YXIgYWNlUG9zID0geyByb3c6IHBvcy5saW5lLCBjb2x1bW46IHBvcy5jaCB9O1xuICAgICAgICB2YXIgY20gPSB0aGlzO1xuICAgICAgICB2YXIgbGFzdCA9IG51bGw7XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICBmaW5kTmV4dDogZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpcy5maW5kKGZhbHNlKTsgfSxcbiAgICAgICAgICAgIGZpbmRQcmV2aW91czogZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpcy5maW5kKHRydWUpOyB9LFxuICAgICAgICAgICAgZmluZDogZnVuY3Rpb24gKGJhY2spIHtcbiAgICAgICAgICAgICAgICBzZWFyY2guc2V0T3B0aW9ucyh7XG4gICAgICAgICAgICAgICAgICAgIG5lZWRsZTogcXVlcnksXG4gICAgICAgICAgICAgICAgICAgIGNhc2VTZW5zaXRpdmU6IGNhc2VTZW5zaXRpdmUsXG4gICAgICAgICAgICAgICAgICAgIHdyYXA6IGZhbHNlLFxuICAgICAgICAgICAgICAgICAgICBiYWNrd2FyZHM6IGJhY2ssXG4gICAgICAgICAgICAgICAgICAgIHJlZ0V4cDogaXNSZWdleHAsXG4gICAgICAgICAgICAgICAgICAgIHN0YXJ0OiBsYXN0IHx8IGFjZVBvc1xuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgIHZhciByYW5nZSA9IHNlYXJjaC5maW5kKGNtLmFjZS5zZXNzaW9uKTtcbiAgICAgICAgICAgICAgICBsYXN0ID0gcmFuZ2U7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGxhc3QgJiYgWyFsYXN0LmlzRW1wdHkoKV07XG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgZnJvbTogZnVuY3Rpb24gKCkgeyByZXR1cm4gbGFzdCAmJiB0b0NtUG9zKGxhc3Quc3RhcnQpOyB9LFxuICAgICAgICAgICAgdG86IGZ1bmN0aW9uICgpIHsgcmV0dXJuIGxhc3QgJiYgdG9DbVBvcyhsYXN0LmVuZCk7IH0sXG4gICAgICAgICAgICByZXBsYWNlOiBmdW5jdGlvbiAodGV4dCkge1xuICAgICAgICAgICAgICAgIGlmIChsYXN0KSB7XG4gICAgICAgICAgICAgICAgICAgIGxhc3QuZW5kID0gY20uYWNlLnNlc3Npb24uZG9jLnJlcGxhY2UobGFzdCwgdGV4dCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgIH07XG4gICAgdGhpcy5zY3JvbGxUbyA9IGZ1bmN0aW9uICh4LCB5KSB7XG4gICAgICAgIHZhciByZW5kZXJlciA9IHRoaXMuYWNlLnJlbmRlcmVyO1xuICAgICAgICB2YXIgY29uZmlnID0gcmVuZGVyZXIubGF5ZXJDb25maWc7XG4gICAgICAgIHZhciBtYXhIZWlnaHQgPSBjb25maWcubWF4SGVpZ2h0O1xuICAgICAgICBtYXhIZWlnaHQgLT0gKHJlbmRlcmVyLiRzaXplLnNjcm9sbGVySGVpZ2h0IC0gcmVuZGVyZXIubGluZUhlaWdodCkgKiByZW5kZXJlci4kc2Nyb2xsUGFzdEVuZDtcbiAgICAgICAgaWYgKHkgIT0gbnVsbClcbiAgICAgICAgICAgIHRoaXMuYWNlLnNlc3Npb24uc2V0U2Nyb2xsVG9wKE1hdGgubWF4KDAsIE1hdGgubWluKHksIG1heEhlaWdodCkpKTtcbiAgICAgICAgaWYgKHggIT0gbnVsbClcbiAgICAgICAgICAgIHRoaXMuYWNlLnNlc3Npb24uc2V0U2Nyb2xsTGVmdChNYXRoLm1heCgwLCBNYXRoLm1pbih4LCBjb25maWcud2lkdGgpKSk7XG4gICAgfTtcbiAgICB0aGlzLnNjcm9sbEluZm8gPSBmdW5jdGlvbiAoKSB7IHJldHVybiAwOyB9O1xuICAgIHRoaXMuc2Nyb2xsSW50b1ZpZXcgPSBmdW5jdGlvbiAocG9zLCBtYXJnaW4pIHtcbiAgICAgICAgaWYgKHBvcykge1xuICAgICAgICAgICAgdmFyIHJlbmRlcmVyID0gdGhpcy5hY2UucmVuZGVyZXI7XG4gICAgICAgICAgICB2YXIgdmlld01hcmdpbiA9IHsgXCJ0b3BcIjogMCwgXCJib3R0b21cIjogbWFyZ2luIH07XG4gICAgICAgICAgICByZW5kZXJlci5zY3JvbGxDdXJzb3JJbnRvVmlldyh0b0FjZVBvcyhwb3MpLCAocmVuZGVyZXIubGluZUhlaWdodCAqIDIpIC8gcmVuZGVyZXIuJHNpemUuc2Nyb2xsZXJIZWlnaHQsIHZpZXdNYXJnaW4pO1xuICAgICAgICB9XG4gICAgfTtcbiAgICB0aGlzLmdldExpbmUgPSBmdW5jdGlvbiAocm93KSB7IHJldHVybiB0aGlzLmFjZS5zZXNzaW9uLmdldExpbmUocm93KTsgfTtcbiAgICB0aGlzLmdldFJhbmdlID0gZnVuY3Rpb24gKHMsIGUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYWNlLnNlc3Npb24uZ2V0VGV4dFJhbmdlKG5ldyBSYW5nZShzLmxpbmUsIHMuY2gsIGUubGluZSwgZS5jaCkpO1xuICAgIH07XG4gICAgdGhpcy5yZXBsYWNlUmFuZ2UgPSBmdW5jdGlvbiAodGV4dCwgcywgZSkge1xuICAgICAgICBpZiAoIWUpXG4gICAgICAgICAgICBlID0gcztcbiAgICAgICAgdmFyIHJhbmdlID0gbmV3IFJhbmdlKHMubGluZSwgcy5jaCwgZS5saW5lLCBlLmNoKTtcbiAgICAgICAgdGhpcy5hY2Uuc2Vzc2lvbi4kY2xpcFJhbmdlVG9Eb2N1bWVudChyYW5nZSk7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5zZXNzaW9uLnJlcGxhY2UocmFuZ2UsIHRleHQpO1xuICAgIH07XG4gICAgdGhpcy5yZXBsYWNlU2VsZWN0aW9uID1cbiAgICAgICAgdGhpcy5yZXBsYWNlU2VsZWN0aW9ucyA9IGZ1bmN0aW9uIChwKSB7XG4gICAgICAgICAgICB2YXIgc3RyaW5ncyA9IEFycmF5LmlzQXJyYXkocCkgJiYgcDtcbiAgICAgICAgICAgIHZhciBzZWwgPSB0aGlzLmFjZS5zZWxlY3Rpb247XG4gICAgICAgICAgICBpZiAodGhpcy5hY2UuaW5WaXJ0dWFsU2VsZWN0aW9uTW9kZSkge1xuICAgICAgICAgICAgICAgIHRoaXMuYWNlLnNlc3Npb24ucmVwbGFjZShzZWwuZ2V0UmFuZ2UoKSwgc3RyaW5ncyA/IHBbMF0gfHwgXCJcIiA6IHApO1xuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHNlbC5pblZpcnR1YWxTZWxlY3Rpb25Nb2RlID0gdHJ1ZTtcbiAgICAgICAgICAgIHZhciByYW5nZXMgPSBzZWwucmFuZ2VMaXN0LnJhbmdlcztcbiAgICAgICAgICAgIGlmICghcmFuZ2VzLmxlbmd0aClcbiAgICAgICAgICAgICAgICByYW5nZXMgPSBbdGhpcy5hY2UubXVsdGlTZWxlY3QuZ2V0UmFuZ2UoKV07XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gcmFuZ2VzLmxlbmd0aDsgaS0tOylcbiAgICAgICAgICAgICAgICB0aGlzLmFjZS5zZXNzaW9uLnJlcGxhY2UocmFuZ2VzW2ldLCBzdHJpbmdzID8gcFtpXSB8fCBcIlwiIDogcCk7XG4gICAgICAgICAgICBzZWwuaW5WaXJ0dWFsU2VsZWN0aW9uTW9kZSA9IGZhbHNlO1xuICAgICAgICB9O1xuICAgIHRoaXMuZ2V0U2VsZWN0aW9uID0gZnVuY3Rpb24gKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5hY2UuZ2V0U2VsZWN0ZWRUZXh0KCk7XG4gICAgfTtcbiAgICB0aGlzLmdldFNlbGVjdGlvbnMgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmxpc3RTZWxlY3Rpb25zKCkubWFwKGZ1bmN0aW9uICh4KSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy5nZXRSYW5nZSh4LmFuY2hvciwgeC5oZWFkKTtcbiAgICAgICAgfSwgdGhpcyk7XG4gICAgfTtcbiAgICB0aGlzLmdldElucHV0RmllbGQgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS50ZXh0SW5wdXQuZ2V0RWxlbWVudCgpO1xuICAgIH07XG4gICAgdGhpcy5nZXRXcmFwcGVyRWxlbWVudCA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYWNlLmNvbnRhaW5lcjtcbiAgICB9O1xuICAgIHZhciBvcHRNYXAgPSB7XG4gICAgICAgIGluZGVudFdpdGhUYWJzOiBcInVzZVNvZnRUYWJzXCIsXG4gICAgICAgIGluZGVudFVuaXQ6IFwidGFiU2l6ZVwiLFxuICAgICAgICB0YWJTaXplOiBcInRhYlNpemVcIixcbiAgICAgICAgZmlyc3RMaW5lTnVtYmVyOiBcImZpcnN0TGluZU51bWJlclwiLFxuICAgICAgICByZWFkT25seTogXCJyZWFkT25seVwiXG4gICAgfTtcbiAgICB0aGlzLnNldE9wdGlvbiA9IGZ1bmN0aW9uIChuYW1lLCB2YWwpIHtcbiAgICAgICAgdGhpcy5zdGF0ZVtuYW1lXSA9IHZhbDtcbiAgICAgICAgc3dpdGNoIChuYW1lKSB7XG4gICAgICAgICAgICBjYXNlICdpbmRlbnRXaXRoVGFicyc6XG4gICAgICAgICAgICAgICAgbmFtZSA9IG9wdE1hcFtuYW1lXTtcbiAgICAgICAgICAgICAgICB2YWwgPSAhdmFsO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAna2V5TWFwJzpcbiAgICAgICAgICAgICAgICB0aGlzLnN0YXRlLiRrZXlNYXAgPSB2YWw7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICAgICAgICBuYW1lID0gb3B0TWFwW25hbWVdO1xuICAgICAgICB9XG4gICAgICAgIGlmIChuYW1lKVxuICAgICAgICAgICAgdGhpcy5hY2Uuc2V0T3B0aW9uKG5hbWUsIHZhbCk7XG4gICAgfTtcbiAgICB0aGlzLmdldE9wdGlvbiA9IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgICAgIHZhciB2YWw7XG4gICAgICAgIHZhciBhY2VPcHQgPSBvcHRNYXBbbmFtZV07XG4gICAgICAgIGlmIChhY2VPcHQpXG4gICAgICAgICAgICB2YWwgPSB0aGlzLmFjZS5nZXRPcHRpb24oYWNlT3B0KTtcbiAgICAgICAgc3dpdGNoIChuYW1lKSB7XG4gICAgICAgICAgICBjYXNlICdpbmRlbnRXaXRoVGFicyc6XG4gICAgICAgICAgICAgICAgbmFtZSA9IG9wdE1hcFtuYW1lXTtcbiAgICAgICAgICAgICAgICByZXR1cm4gIXZhbDtcbiAgICAgICAgICAgIGNhc2UgJ2tleU1hcCc6XG4gICAgICAgICAgICAgICAgcmV0dXJuIHRoaXMuc3RhdGUuJGtleU1hcCB8fCAndmltJztcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gYWNlT3B0ID8gdmFsIDogdGhpcy5zdGF0ZVtuYW1lXTtcbiAgICB9O1xuICAgIHRoaXMudG9nZ2xlT3ZlcndyaXRlID0gZnVuY3Rpb24gKG9uKSB7XG4gICAgICAgIHRoaXMuc3RhdGUub3ZlcndyaXRlID0gb247XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5zZXRPdmVyd3JpdGUob24pO1xuICAgIH07XG4gICAgdGhpcy5hZGRPdmVybGF5ID0gZnVuY3Rpb24gKG8pIHtcbiAgICAgICAgaWYgKCF0aGlzLiRzZWFyY2hIaWdobGlnaHQgfHwgIXRoaXMuJHNlYXJjaEhpZ2hsaWdodC5zZXNzaW9uKSB7XG4gICAgICAgICAgICB2YXIgaGlnaGxpZ2h0ID0gbmV3IFNlYXJjaEhpZ2hsaWdodChudWxsLCBcImFjZV9oaWdobGlnaHQtbWFya2VyXCIsIFwidGV4dFwiKTtcbiAgICAgICAgICAgIHZhciBtYXJrZXIgPSB0aGlzLmFjZS5zZXNzaW9uLmFkZER5bmFtaWNNYXJrZXIoaGlnaGxpZ2h0KTtcbiAgICAgICAgICAgIGhpZ2hsaWdodC5pZCA9IG1hcmtlci5pZDtcbiAgICAgICAgICAgIGhpZ2hsaWdodC5zZXNzaW9uID0gdGhpcy5hY2Uuc2Vzc2lvbjtcbiAgICAgICAgICAgIGhpZ2hsaWdodC5kZXN0cm95ID0gZnVuY3Rpb24gKG8pIHtcbiAgICAgICAgICAgICAgICBoaWdobGlnaHQuc2Vzc2lvbi5vZmYoXCJjaGFuZ2VcIiwgaGlnaGxpZ2h0LnVwZGF0ZU9uQ2hhbmdlKTtcbiAgICAgICAgICAgICAgICBoaWdobGlnaHQuc2Vzc2lvbi5vZmYoXCJjaGFuZ2VFZGl0b3JcIiwgaGlnaGxpZ2h0LmRlc3Ryb3kpO1xuICAgICAgICAgICAgICAgIGhpZ2hsaWdodC5zZXNzaW9uLnJlbW92ZU1hcmtlcihoaWdobGlnaHQuaWQpO1xuICAgICAgICAgICAgICAgIGhpZ2hsaWdodC5zZXNzaW9uID0gbnVsbDtcbiAgICAgICAgICAgIH07XG4gICAgICAgICAgICBoaWdobGlnaHQudXBkYXRlT25DaGFuZ2UgPSBmdW5jdGlvbiAoZGVsdGEpIHtcbiAgICAgICAgICAgICAgICB2YXIgcm93ID0gZGVsdGEuc3RhcnQucm93O1xuICAgICAgICAgICAgICAgIGlmIChyb3cgPT0gZGVsdGEuZW5kLnJvdylcbiAgICAgICAgICAgICAgICAgICAgaGlnaGxpZ2h0LmNhY2hlW3Jvd10gPSB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgZWxzZVxuICAgICAgICAgICAgICAgICAgICBoaWdobGlnaHQuY2FjaGUuc3BsaWNlKHJvdywgaGlnaGxpZ2h0LmNhY2hlLmxlbmd0aCk7XG4gICAgICAgICAgICB9O1xuICAgICAgICAgICAgaGlnaGxpZ2h0LnNlc3Npb24ub24oXCJjaGFuZ2VFZGl0b3JcIiwgaGlnaGxpZ2h0LmRlc3Ryb3kpO1xuICAgICAgICAgICAgaGlnaGxpZ2h0LnNlc3Npb24ub24oXCJjaGFuZ2VcIiwgaGlnaGxpZ2h0LnVwZGF0ZU9uQ2hhbmdlKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgcmUgPSBuZXcgUmVnRXhwKG8ucXVlcnkuc291cmNlLCBcImdtaVwiKTtcbiAgICAgICAgdGhpcy4kc2VhcmNoSGlnaGxpZ2h0ID0gby5oaWdobGlnaHQgPSBoaWdobGlnaHQ7XG4gICAgICAgIHRoaXMuJHNlYXJjaEhpZ2hsaWdodC5zZXRSZWdleHAocmUpO1xuICAgICAgICB0aGlzLmFjZS5yZW5kZXJlci51cGRhdGVCYWNrTWFya2VycygpO1xuICAgIH07XG4gICAgdGhpcy5yZW1vdmVPdmVybGF5ID0gZnVuY3Rpb24gKG8pIHtcbiAgICAgICAgaWYgKHRoaXMuJHNlYXJjaEhpZ2hsaWdodCAmJiB0aGlzLiRzZWFyY2hIaWdobGlnaHQuc2Vzc2lvbikge1xuICAgICAgICAgICAgdGhpcy4kc2VhcmNoSGlnaGxpZ2h0LmRlc3Ryb3koKTtcbiAgICAgICAgfVxuICAgIH07XG4gICAgdGhpcy5nZXRTY3JvbGxJbmZvID0gZnVuY3Rpb24gKCkge1xuICAgICAgICB2YXIgcmVuZGVyZXIgPSB0aGlzLmFjZS5yZW5kZXJlcjtcbiAgICAgICAgdmFyIGNvbmZpZyA9IHJlbmRlcmVyLmxheWVyQ29uZmlnO1xuICAgICAgICByZXR1cm4ge1xuICAgICAgICAgICAgbGVmdDogcmVuZGVyZXIuc2Nyb2xsTGVmdCxcbiAgICAgICAgICAgIHRvcDogcmVuZGVyZXIuc2Nyb2xsVG9wLFxuICAgICAgICAgICAgaGVpZ2h0OiBjb25maWcubWF4SGVpZ2h0LFxuICAgICAgICAgICAgd2lkdGg6IGNvbmZpZy53aWR0aCxcbiAgICAgICAgICAgIGNsaWVudEhlaWdodDogY29uZmlnLmhlaWdodCxcbiAgICAgICAgICAgIGNsaWVudFdpZHRoOiBjb25maWcud2lkdGhcbiAgICAgICAgfTtcbiAgICB9O1xuICAgIHRoaXMuZ2V0VmFsdWUgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5nZXRWYWx1ZSgpO1xuICAgIH07XG4gICAgdGhpcy5zZXRWYWx1ZSA9IGZ1bmN0aW9uICh2KSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5zZXRWYWx1ZSh2LCAtMSk7XG4gICAgfTtcbiAgICB0aGlzLmdldFRva2VuVHlwZUF0ID0gZnVuY3Rpb24gKHBvcykge1xuICAgICAgICB2YXIgdG9rZW4gPSB0aGlzLmFjZS5zZXNzaW9uLmdldFRva2VuQXQocG9zLmxpbmUsIHBvcy5jaCk7XG4gICAgICAgIHJldHVybiB0b2tlbiAmJiAvY29tbWVudHxzdHJpbmcvLnRlc3QodG9rZW4udHlwZSkgPyBcInN0cmluZ1wiIDogXCJcIjtcbiAgICB9O1xuICAgIHRoaXMuZmluZE1hdGNoaW5nQnJhY2tldCA9IGZ1bmN0aW9uIChwb3MpIHtcbiAgICAgICAgdmFyIG0gPSB0aGlzLmFjZS5zZXNzaW9uLmZpbmRNYXRjaGluZ0JyYWNrZXQodG9BY2VQb3MocG9zKSk7XG4gICAgICAgIHJldHVybiB7IHRvOiBtICYmIHRvQ21Qb3MobSkgfTtcbiAgICB9O1xuICAgIHRoaXMuZmluZE1hdGNoaW5nVGFnID0gZnVuY3Rpb24gKHBvcykge1xuICAgICAgICB2YXIgbSA9IHRoaXMuYWNlLnNlc3Npb24uZ2V0TWF0Y2hpbmdUYWdzKHRvQWNlUG9zKHBvcykpO1xuICAgICAgICBpZiAoIW0pXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICBvcGVuOiB7XG4gICAgICAgICAgICAgICAgZnJvbTogdG9DbVBvcyhtLm9wZW5UYWcuc3RhcnQpLFxuICAgICAgICAgICAgICAgIHRvOiB0b0NtUG9zKG0ub3BlblRhZy5lbmQpXG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgY2xvc2U6IHtcbiAgICAgICAgICAgICAgICBmcm9tOiB0b0NtUG9zKG0uY2xvc2VUYWcuc3RhcnQpLFxuICAgICAgICAgICAgICAgIHRvOiB0b0NtUG9zKG0uY2xvc2VUYWcuZW5kKVxuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgIH07XG4gICAgdGhpcy5pbmRlbnRMaW5lID0gZnVuY3Rpb24gKGxpbmUsIG1ldGhvZCkge1xuICAgICAgICBpZiAobWV0aG9kID09PSB0cnVlKVxuICAgICAgICAgICAgdGhpcy5hY2Uuc2Vzc2lvbi5pbmRlbnRSb3dzKGxpbmUsIGxpbmUsIFwiXFx0XCIpO1xuICAgICAgICBlbHNlIGlmIChtZXRob2QgPT09IGZhbHNlKVxuICAgICAgICAgICAgdGhpcy5hY2Uuc2Vzc2lvbi5vdXRkZW50Um93cyhuZXcgUmFuZ2UobGluZSwgMCwgbGluZSwgMCkpO1xuICAgIH07XG4gICAgdGhpcy5pbmRleEZyb21Qb3MgPSBmdW5jdGlvbiAocG9zKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5zZXNzaW9uLmRvYy5wb3NpdGlvblRvSW5kZXgodG9BY2VQb3MocG9zKSk7XG4gICAgfTtcbiAgICB0aGlzLnBvc0Zyb21JbmRleCA9IGZ1bmN0aW9uIChpbmRleCkge1xuICAgICAgICByZXR1cm4gdG9DbVBvcyh0aGlzLmFjZS5zZXNzaW9uLmRvYy5pbmRleFRvUG9zaXRpb24oaW5kZXgpKTtcbiAgICB9O1xuICAgIHRoaXMuZm9jdXMgPSBmdW5jdGlvbiAoaW5kZXgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYWNlLnRleHRJbnB1dC5mb2N1cygpO1xuICAgIH07XG4gICAgdGhpcy5ibHVyID0gZnVuY3Rpb24gKGluZGV4KSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5ibHVyKCk7XG4gICAgfTtcbiAgICB0aGlzLmRlZmF1bHRUZXh0SGVpZ2h0ID0gZnVuY3Rpb24gKGluZGV4KSB7XG4gICAgICAgIHJldHVybiB0aGlzLmFjZS5yZW5kZXJlci5sYXllckNvbmZpZy5saW5lSGVpZ2h0O1xuICAgIH07XG4gICAgdGhpcy5zY2FuRm9yQnJhY2tldCA9IGZ1bmN0aW9uIChwb3MsIGRpciwgXywgb3B0aW9ucykge1xuICAgICAgICB2YXIgcmUgPSBvcHRpb25zLmJyYWNrZXRSZWdleC5zb3VyY2U7XG4gICAgICAgIHZhciB0b2tlblJlID0gL3BhcmVufHRleHR8b3BlcmF0b3J8dGFnLztcbiAgICAgICAgaWYgKGRpciA9PSAxKSB7XG4gICAgICAgICAgICB2YXIgbSA9IHRoaXMuYWNlLnNlc3Npb24uJGZpbmRDbG9zaW5nQnJhY2tldChyZS5zbGljZSgxLCAyKSwgdG9BY2VQb3MocG9zKSwgdG9rZW5SZSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YXIgbSA9IHRoaXMuYWNlLnNlc3Npb24uJGZpbmRPcGVuaW5nQnJhY2tldChyZS5zbGljZSgtMiwgLTEpLCB7IHJvdzogcG9zLmxpbmUsIGNvbHVtbjogcG9zLmNoICsgMSB9LCB0b2tlblJlKTtcbiAgICAgICAgICAgIGlmICghbSAmJiBvcHRpb25zLmJyYWNrZXRSZWdleCAmJiBvcHRpb25zLmJyYWNrZXRSZWdleC50ZXN0KHRoaXMuZ2V0TGluZShwb3MubGluZSlbcG9zLmNoIC0gMV0pKSB7XG4gICAgICAgICAgICAgICAgbSA9IHsgcm93OiBwb3MubGluZSwgY29sdW1uOiBwb3MuY2ggLSAxIH07XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG0gJiYgeyBwb3M6IHRvQ21Qb3MobSkgfTtcbiAgICB9O1xuICAgIHRoaXMucmVmcmVzaCA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuYWNlLnJlc2l6ZSh0cnVlKTtcbiAgICB9O1xuICAgIHRoaXMuZ2V0TW9kZSA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHsgbmFtZTogdGhpcy5nZXRPcHRpb24oXCJtb2RlXCIpIH07XG4gICAgfTtcbiAgICB0aGlzLmV4ZWNDb21tYW5kID0gZnVuY3Rpb24gKG5hbWUpIHtcbiAgICAgICAgaWYgKENvZGVNaXJyb3IuY29tbWFuZHMuaGFzT3duUHJvcGVydHkobmFtZSkpXG4gICAgICAgICAgICByZXR1cm4gQ29kZU1pcnJvci5jb21tYW5kc1tuYW1lXSh0aGlzKTtcbiAgICAgICAgaWYgKG5hbWUgPT0gXCJpbmRlbnRBdXRvXCIpXG4gICAgICAgICAgICByZXR1cm4gdGhpcy5hY2UuZXhlY0NvbW1hbmQoXCJhdXRvaW5kZW50XCIpO1xuICAgICAgICBjb25zb2xlLmxvZyhuYW1lICsgXCIgaXMgbm90IGltcGxlbWVudGVkXCIpO1xuICAgIH07XG4gICAgdGhpcy5nZXRMaW5lTnVtYmVyID0gZnVuY3Rpb24gKGhhbmRsZSkge1xuICAgICAgICB2YXIgZGVsdGFzID0gdGhpcy4kbGluZUhhbmRsZUNoYW5nZXM7XG4gICAgICAgIGlmICghZGVsdGFzKVxuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgIHZhciByb3cgPSBoYW5kbGUucm93O1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGRlbHRhcy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIGRlbHRhID0gZGVsdGFzW2ldO1xuICAgICAgICAgICAgaWYgKGRlbHRhLnN0YXJ0LnJvdyAhPSBkZWx0YS5lbmQucm93KSB7XG4gICAgICAgICAgICAgICAgaWYgKGRlbHRhLmFjdGlvblswXSA9PSBcImlcIikge1xuICAgICAgICAgICAgICAgICAgICBpZiAoZGVsdGEuc3RhcnQucm93IDwgcm93KVxuICAgICAgICAgICAgICAgICAgICAgICAgcm93ICs9IGRlbHRhLmVuZC5yb3cgLSBkZWx0YS5zdGFydC5yb3c7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBpZiAoZGVsdGEuc3RhcnQucm93IDwgcm93KSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAocm93IDwgZGVsdGEuZW5kLnJvdyB8fCByb3cgPT0gZGVsdGEuZW5kLnJvdyAmJiBkZWx0YS5zdGFydC5jb2x1bW4gPiAwKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByb3cgLT0gZGVsdGEuZW5kLnJvdyAtIGRlbHRhLnN0YXJ0LnJvdztcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcm93O1xuICAgIH07XG4gICAgdGhpcy5nZXRMaW5lSGFuZGxlID0gZnVuY3Rpb24gKHJvdykge1xuICAgICAgICBpZiAoIXRoaXMuJGxpbmVIYW5kbGVDaGFuZ2VzKVxuICAgICAgICAgICAgdGhpcy4kbGluZUhhbmRsZUNoYW5nZXMgPSBbXTtcbiAgICAgICAgcmV0dXJuIHsgdGV4dDogdGhpcy5hY2Uuc2Vzc2lvbi5nZXRMaW5lKHJvdyksIHJvdzogcm93IH07XG4gICAgfTtcbiAgICB0aGlzLnJlbGVhc2VMaW5lSGFuZGxlcyA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdGhpcy4kbGluZUhhbmRsZUNoYW5nZXMgPSB1bmRlZmluZWQ7XG4gICAgfTtcbiAgICB0aGlzLmdldExhc3RFZGl0RW5kID0gZnVuY3Rpb24gKCkge1xuICAgICAgICB2YXIgdW5kb01hbmFnZXIgPSB0aGlzLmFjZS5zZXNzaW9uLiR1bmRvTWFuYWdlcjtcbiAgICAgICAgaWYgKHVuZG9NYW5hZ2VyICYmIHVuZG9NYW5hZ2VyLiRsYXN0RGVsdGEpXG4gICAgICAgICAgICByZXR1cm4gdG9DbVBvcyh1bmRvTWFuYWdlci4kbGFzdERlbHRhLmVuZCk7XG4gICAgfTtcbn0pLmNhbGwoQ29kZU1pcnJvci5wcm90b3R5cGUpO1xuZnVuY3Rpb24gdG9BY2VQb3MoY21Qb3MpIHtcbiAgICByZXR1cm4geyByb3c6IGNtUG9zLmxpbmUsIGNvbHVtbjogY21Qb3MuY2ggfTtcbn1cbmZ1bmN0aW9uIHRvQ21Qb3MoYWNlUG9zKSB7XG4gICAgcmV0dXJuIG5ldyBQb3MoYWNlUG9zLnJvdywgYWNlUG9zLmNvbHVtbik7XG59XG52YXIgU3RyaW5nU3RyZWFtID0gQ29kZU1pcnJvci5TdHJpbmdTdHJlYW0gPSBmdW5jdGlvbiAoc3RyaW5nLCB0YWJTaXplKSB7XG4gICAgdGhpcy5wb3MgPSB0aGlzLnN0YXJ0ID0gMDtcbiAgICB0aGlzLnN0cmluZyA9IHN0cmluZztcbiAgICB0aGlzLnRhYlNpemUgPSB0YWJTaXplIHx8IDg7XG4gICAgdGhpcy5sYXN0Q29sdW1uUG9zID0gdGhpcy5sYXN0Q29sdW1uVmFsdWUgPSAwO1xuICAgIHRoaXMubGluZVN0YXJ0ID0gMDtcbn07XG5TdHJpbmdTdHJlYW0ucHJvdG90eXBlID0ge1xuICAgIGVvbDogZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpcy5wb3MgPj0gdGhpcy5zdHJpbmcubGVuZ3RoOyB9LFxuICAgIHNvbDogZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpcy5wb3MgPT0gdGhpcy5saW5lU3RhcnQ7IH0sXG4gICAgcGVlazogZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpcy5zdHJpbmcuY2hhckF0KHRoaXMucG9zKSB8fCB1bmRlZmluZWQ7IH0sXG4gICAgbmV4dDogZnVuY3Rpb24gKCkge1xuICAgICAgICBpZiAodGhpcy5wb3MgPCB0aGlzLnN0cmluZy5sZW5ndGgpXG4gICAgICAgICAgICByZXR1cm4gdGhpcy5zdHJpbmcuY2hhckF0KHRoaXMucG9zKyspO1xuICAgIH0sXG4gICAgZWF0OiBmdW5jdGlvbiAobWF0Y2gpIHtcbiAgICAgICAgdmFyIGNoID0gdGhpcy5zdHJpbmcuY2hhckF0KHRoaXMucG9zKTtcbiAgICAgICAgaWYgKHR5cGVvZiBtYXRjaCA9PSBcInN0cmluZ1wiKVxuICAgICAgICAgICAgdmFyIG9rID0gY2ggPT0gbWF0Y2g7XG4gICAgICAgIGVsc2VcbiAgICAgICAgICAgIHZhciBvayA9IGNoICYmIChtYXRjaC50ZXN0ID8gbWF0Y2gudGVzdChjaCkgOiBtYXRjaChjaCkpO1xuICAgICAgICBpZiAob2spIHtcbiAgICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgICAgICByZXR1cm4gY2g7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIGVhdFdoaWxlOiBmdW5jdGlvbiAobWF0Y2gpIHtcbiAgICAgICAgdmFyIHN0YXJ0ID0gdGhpcy5wb3M7XG4gICAgICAgIHdoaWxlICh0aGlzLmVhdChtYXRjaCkpIHsgfVxuICAgICAgICByZXR1cm4gdGhpcy5wb3MgPiBzdGFydDtcbiAgICB9LFxuICAgIGVhdFNwYWNlOiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHZhciBzdGFydCA9IHRoaXMucG9zO1xuICAgICAgICB3aGlsZSAoL1tcXHNcXHUwMGEwXS8udGVzdCh0aGlzLnN0cmluZy5jaGFyQXQodGhpcy5wb3MpKSlcbiAgICAgICAgICAgICsrdGhpcy5wb3M7XG4gICAgICAgIHJldHVybiB0aGlzLnBvcyA+IHN0YXJ0O1xuICAgIH0sXG4gICAgc2tpcFRvRW5kOiBmdW5jdGlvbiAoKSB7IHRoaXMucG9zID0gdGhpcy5zdHJpbmcubGVuZ3RoOyB9LFxuICAgIHNraXBUbzogZnVuY3Rpb24gKGNoKSB7XG4gICAgICAgIHZhciBmb3VuZCA9IHRoaXMuc3RyaW5nLmluZGV4T2YoY2gsIHRoaXMucG9zKTtcbiAgICAgICAgaWYgKGZvdW5kID4gLTEpIHtcbiAgICAgICAgICAgIHRoaXMucG9zID0gZm91bmQ7XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgYmFja1VwOiBmdW5jdGlvbiAobikgeyB0aGlzLnBvcyAtPSBuOyB9LFxuICAgIGNvbHVtbjogZnVuY3Rpb24gKCkge1xuICAgICAgICB0aHJvdyBcIm5vdCBpbXBsZW1lbnRlZFwiO1xuICAgIH0sXG4gICAgaW5kZW50YXRpb246IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdGhyb3cgXCJub3QgaW1wbGVtZW50ZWRcIjtcbiAgICB9LFxuICAgIG1hdGNoOiBmdW5jdGlvbiAocGF0dGVybiwgY29uc3VtZSwgY2FzZUluc2Vuc2l0aXZlKSB7XG4gICAgICAgIGlmICh0eXBlb2YgcGF0dGVybiA9PSBcInN0cmluZ1wiKSB7XG4gICAgICAgICAgICB2YXIgY2FzZWQgPSBmdW5jdGlvbiAoc3RyKSB7IHJldHVybiBjYXNlSW5zZW5zaXRpdmUgPyBzdHIudG9Mb3dlckNhc2UoKSA6IHN0cjsgfTtcbiAgICAgICAgICAgIHZhciBzdWJzdHIgPSB0aGlzLnN0cmluZy5zdWJzdHIodGhpcy5wb3MsIHBhdHRlcm4ubGVuZ3RoKTtcbiAgICAgICAgICAgIGlmIChjYXNlZChzdWJzdHIpID09IGNhc2VkKHBhdHRlcm4pKSB7XG4gICAgICAgICAgICAgICAgaWYgKGNvbnN1bWUgIT09IGZhbHNlKVxuICAgICAgICAgICAgICAgICAgICB0aGlzLnBvcyArPSBwYXR0ZXJuLmxlbmd0aDtcbiAgICAgICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhciBtYXRjaCA9IHRoaXMuc3RyaW5nLnNsaWNlKHRoaXMucG9zKS5tYXRjaChwYXR0ZXJuKTtcbiAgICAgICAgICAgIGlmIChtYXRjaCAmJiBtYXRjaC5pbmRleCA+IDApXG4gICAgICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgICAgICBpZiAobWF0Y2ggJiYgY29uc3VtZSAhPT0gZmFsc2UpXG4gICAgICAgICAgICAgICAgdGhpcy5wb3MgKz0gbWF0Y2hbMF0ubGVuZ3RoO1xuICAgICAgICAgICAgcmV0dXJuIG1hdGNoO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBjdXJyZW50OiBmdW5jdGlvbiAoKSB7IHJldHVybiB0aGlzLnN0cmluZy5zbGljZSh0aGlzLnN0YXJ0LCB0aGlzLnBvcyk7IH0sXG4gICAgaGlkZUZpcnN0Q2hhcnM6IGZ1bmN0aW9uIChuLCBpbm5lcikge1xuICAgICAgICB0aGlzLmxpbmVTdGFydCArPSBuO1xuICAgICAgICB0cnkge1xuICAgICAgICAgICAgcmV0dXJuIGlubmVyKCk7XG4gICAgICAgIH1cbiAgICAgICAgZmluYWxseSB7XG4gICAgICAgICAgICB0aGlzLmxpbmVTdGFydCAtPSBuO1xuICAgICAgICB9XG4gICAgfVxufTtcbkNvZGVNaXJyb3IuZGVmaW5lRXh0ZW5zaW9uID0gZnVuY3Rpb24gKG5hbWUsIGZuKSB7XG4gICAgQ29kZU1pcnJvci5wcm90b3R5cGVbbmFtZV0gPSBmbjtcbn07XG5kb21MaWIuaW1wb3J0Q3NzU3RyaW5nKFwiLm5vcm1hbC1tb2RlIC5hY2VfY3Vyc29ye1xcbiAgICBib3JkZXI6IG5vbmU7XFxuICAgIGJhY2tncm91bmQtY29sb3I6IHJnYmEoMjU1LDAsMCwwLjUpO1xcbn1cXG4ubm9ybWFsLW1vZGUgLmFjZV9oaWRkZW4tY3Vyc29ycyAuYWNlX2N1cnNvcntcXG4gIGJhY2tncm91bmQtY29sb3I6IHRyYW5zcGFyZW50O1xcbiAgYm9yZGVyOiAxcHggc29saWQgcmVkO1xcbiAgb3BhY2l0eTogMC43XFxufVxcbi5hY2VfZGlhbG9nIHtcXG4gIHBvc2l0aW9uOiBhYnNvbHV0ZTtcXG4gIGxlZnQ6IDA7IHJpZ2h0OiAwO1xcbiAgYmFja2dyb3VuZDogaW5oZXJpdDtcXG4gIHotaW5kZXg6IDE1O1xcbiAgcGFkZGluZzogLjFlbSAuOGVtO1xcbiAgb3ZlcmZsb3c6IGhpZGRlbjtcXG4gIGNvbG9yOiBpbmhlcml0O1xcbn1cXG4uYWNlX2RpYWxvZy10b3Age1xcbiAgYm9yZGVyLWJvdHRvbTogMXB4IHNvbGlkICM0NDQ7XFxuICB0b3A6IDA7XFxufVxcbi5hY2VfZGlhbG9nLWJvdHRvbSB7XFxuICBib3JkZXItdG9wOiAxcHggc29saWQgIzQ0NDtcXG4gIGJvdHRvbTogMDtcXG59XFxuLmFjZV9kaWFsb2cgaW5wdXQge1xcbiAgYm9yZGVyOiBub25lO1xcbiAgb3V0bGluZTogbm9uZTtcXG4gIGJhY2tncm91bmQ6IHRyYW5zcGFyZW50O1xcbiAgd2lkdGg6IDIwZW07XFxuICBjb2xvcjogaW5oZXJpdDtcXG4gIGZvbnQtZmFtaWx5OiBtb25vc3BhY2U7XFxufVwiLCBcInZpbU1vZGVcIiwgZmFsc2UpO1xuKGZ1bmN0aW9uICgpIHtcbiAgICBmdW5jdGlvbiBkaWFsb2dEaXYoY20sIHRlbXBsYXRlLCBib3R0b20pIHtcbiAgICAgICAgdmFyIHdyYXAgPSBjbS5hY2UuY29udGFpbmVyO1xuICAgICAgICB2YXIgZGlhbG9nO1xuICAgICAgICBkaWFsb2cgPSB3cmFwLmFwcGVuZENoaWxkKGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoXCJkaXZcIikpO1xuICAgICAgICBpZiAoYm90dG9tKVxuICAgICAgICAgICAgZGlhbG9nLmNsYXNzTmFtZSA9IFwiYWNlX2RpYWxvZyBhY2VfZGlhbG9nLWJvdHRvbVwiO1xuICAgICAgICBlbHNlXG4gICAgICAgICAgICBkaWFsb2cuY2xhc3NOYW1lID0gXCJhY2VfZGlhbG9nIGFjZV9kaWFsb2ctdG9wXCI7XG4gICAgICAgIGlmICh0eXBlb2YgdGVtcGxhdGUgPT0gXCJzdHJpbmdcIikge1xuICAgICAgICAgICAgZGlhbG9nLmlubmVySFRNTCA9IHRlbXBsYXRlO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgeyAvLyBBc3N1bWluZyBpdCdzIGEgZGV0YWNoZWQgRE9NIGVsZW1lbnQuXG4gICAgICAgICAgICBkaWFsb2cuYXBwZW5kQ2hpbGQodGVtcGxhdGUpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBkaWFsb2c7XG4gICAgfVxuICAgIGZ1bmN0aW9uIGNsb3NlTm90aWZpY2F0aW9uKGNtLCBuZXdWYWwpIHtcbiAgICAgICAgaWYgKGNtLnN0YXRlLmN1cnJlbnROb3RpZmljYXRpb25DbG9zZSlcbiAgICAgICAgICAgIGNtLnN0YXRlLmN1cnJlbnROb3RpZmljYXRpb25DbG9zZSgpO1xuICAgICAgICBjbS5zdGF0ZS5jdXJyZW50Tm90aWZpY2F0aW9uQ2xvc2UgPSBuZXdWYWw7XG4gICAgfVxuICAgIENvZGVNaXJyb3IuZGVmaW5lRXh0ZW5zaW9uKFwib3BlbkRpYWxvZ1wiLCBmdW5jdGlvbiAodGVtcGxhdGUsIGNhbGxiYWNrLCBvcHRpb25zKSB7XG4gICAgICAgIGlmICh0aGlzLnZpcnR1YWxTZWxlY3Rpb25Nb2RlKCkpXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIGlmICghb3B0aW9ucylcbiAgICAgICAgICAgIG9wdGlvbnMgPSB7fTtcbiAgICAgICAgY2xvc2VOb3RpZmljYXRpb24odGhpcywgbnVsbCk7XG4gICAgICAgIHZhciBkaWFsb2cgPSBkaWFsb2dEaXYodGhpcywgdGVtcGxhdGUsIG9wdGlvbnMuYm90dG9tKTtcbiAgICAgICAgdmFyIGNsb3NlZCA9IGZhbHNlLCBtZSA9IHRoaXM7XG4gICAgICAgIHRoaXMuc3RhdGUuZGlhbG9nID0gZGlhbG9nO1xuICAgICAgICBmdW5jdGlvbiBjbG9zZShuZXdWYWwpIHtcbiAgICAgICAgICAgIGlmICh0eXBlb2YgbmV3VmFsID09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgICAgICAgaW5wLnZhbHVlID0gbmV3VmFsO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGNsb3NlZClcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIGlmIChuZXdWYWwgJiYgbmV3VmFsLnR5cGUgPT0gXCJibHVyXCIpIHtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGRvY3VtZW50LmFjdGl2ZUVsZW1lbnQgPT09IGlucClcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKG1lLnN0YXRlLmRpYWxvZyA9PSBkaWFsb2cpIHtcbiAgICAgICAgICAgICAgICAgICAgbWUuc3RhdGUuZGlhbG9nID0gbnVsbDtcbiAgICAgICAgICAgICAgICAgICAgbWUuZm9jdXMoKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgY2xvc2VkID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICBkaWFsb2cucmVtb3ZlKCk7XG4gICAgICAgICAgICAgICAgaWYgKG9wdGlvbnMub25DbG9zZSlcbiAgICAgICAgICAgICAgICAgICAgb3B0aW9ucy5vbkNsb3NlKGRpYWxvZyk7XG4gICAgICAgICAgICAgICAgdmFyIGNtID0gbWU7XG4gICAgICAgICAgICAgICAgaWYgKGNtLnN0YXRlLnZpbSkge1xuICAgICAgICAgICAgICAgICAgICBjbS5zdGF0ZS52aW0uc3RhdHVzID0gbnVsbDtcbiAgICAgICAgICAgICAgICAgICAgY20uYWNlLl9zaWduYWwoXCJjaGFuZ2VTdGF0dXNcIik7XG4gICAgICAgICAgICAgICAgICAgIGNtLmFjZS5yZW5kZXJlci4kbG9vcC5zY2hlZHVsZShjbS5hY2UucmVuZGVyZXIuQ0hBTkdFX0NVUlNPUik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHZhciBpbnAgPSBkaWFsb2cuZ2V0RWxlbWVudHNCeVRhZ05hbWUoXCJpbnB1dFwiKVswXSwgYnV0dG9uO1xuICAgICAgICBpZiAoaW5wKSB7XG4gICAgICAgICAgICBpZiAob3B0aW9ucy52YWx1ZSkge1xuICAgICAgICAgICAgICAgIGlucC52YWx1ZSA9IG9wdGlvbnMudmFsdWU7XG4gICAgICAgICAgICAgICAgaWYgKG9wdGlvbnMuc2VsZWN0VmFsdWVPbk9wZW4gIT09IGZhbHNlKVxuICAgICAgICAgICAgICAgICAgICBpbnAuc2VsZWN0KCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAob3B0aW9ucy5vbklucHV0KVxuICAgICAgICAgICAgICAgIENvZGVNaXJyb3Iub24oaW5wLCBcImlucHV0XCIsIGZ1bmN0aW9uIChlKSB7IG9wdGlvbnMub25JbnB1dChlLCBpbnAudmFsdWUsIGNsb3NlKTsgfSk7XG4gICAgICAgICAgICBpZiAob3B0aW9ucy5vbktleVVwKVxuICAgICAgICAgICAgICAgIENvZGVNaXJyb3Iub24oaW5wLCBcImtleXVwXCIsIGZ1bmN0aW9uIChlKSB7IG9wdGlvbnMub25LZXlVcChlLCBpbnAudmFsdWUsIGNsb3NlKTsgfSk7XG4gICAgICAgICAgICBDb2RlTWlycm9yLm9uKGlucCwgXCJrZXlkb3duXCIsIGZ1bmN0aW9uIChlKSB7XG4gICAgICAgICAgICAgICAgaWYgKG9wdGlvbnMgJiYgb3B0aW9ucy5vbktleURvd24gJiYgb3B0aW9ucy5vbktleURvd24oZSwgaW5wLnZhbHVlLCBjbG9zZSkpIHtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoZS5rZXlDb2RlID09IDEzKVxuICAgICAgICAgICAgICAgICAgICBjYWxsYmFjayhpbnAudmFsdWUpO1xuICAgICAgICAgICAgICAgIGlmIChlLmtleUNvZGUgPT0gMjcgfHwgKG9wdGlvbnMuY2xvc2VPbkVudGVyICE9PSBmYWxzZSAmJiBlLmtleUNvZGUgPT0gMTMpKSB7XG4gICAgICAgICAgICAgICAgICAgIENvZGVNaXJyb3IuZV9zdG9wKGUpO1xuICAgICAgICAgICAgICAgICAgICBjbG9zZSgpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgaWYgKG9wdGlvbnMuY2xvc2VPbkJsdXIgIT09IGZhbHNlKVxuICAgICAgICAgICAgICAgIENvZGVNaXJyb3Iub24oaW5wLCBcImJsdXJcIiwgY2xvc2UpO1xuICAgICAgICAgICAgaW5wLmZvY3VzKCk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoYnV0dG9uID0gZGlhbG9nLmdldEVsZW1lbnRzQnlUYWdOYW1lKFwiYnV0dG9uXCIpWzBdKSB7XG4gICAgICAgICAgICBDb2RlTWlycm9yLm9uKGJ1dHRvbiwgXCJjbGlja1wiLCBmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICAgICAgY2xvc2UoKTtcbiAgICAgICAgICAgICAgICBtZS5mb2N1cygpO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICBpZiAob3B0aW9ucy5jbG9zZU9uQmx1ciAhPT0gZmFsc2UpXG4gICAgICAgICAgICAgICAgQ29kZU1pcnJvci5vbihidXR0b24sIFwiYmx1clwiLCBjbG9zZSk7XG4gICAgICAgICAgICBidXR0b24uZm9jdXMoKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gY2xvc2U7XG4gICAgfSk7XG4gICAgQ29kZU1pcnJvci5kZWZpbmVFeHRlbnNpb24oXCJvcGVuTm90aWZpY2F0aW9uXCIsIGZ1bmN0aW9uICh0ZW1wbGF0ZSwgb3B0aW9ucykge1xuICAgICAgICBpZiAodGhpcy52aXJ0dWFsU2VsZWN0aW9uTW9kZSgpKVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICBjbG9zZU5vdGlmaWNhdGlvbih0aGlzLCBjbG9zZSk7XG4gICAgICAgIHZhciBkaWFsb2cgPSBkaWFsb2dEaXYodGhpcywgdGVtcGxhdGUsIG9wdGlvbnMgJiYgb3B0aW9ucy5ib3R0b20pO1xuICAgICAgICB2YXIgY2xvc2VkID0gZmFsc2UsIGRvbmVUaW1lcjtcbiAgICAgICAgdmFyIGR1cmF0aW9uID0gb3B0aW9ucyAmJiB0eXBlb2Ygb3B0aW9ucy5kdXJhdGlvbiAhPT0gXCJ1bmRlZmluZWRcIiA/IG9wdGlvbnMuZHVyYXRpb24gOiA1MDAwO1xuICAgICAgICBmdW5jdGlvbiBjbG9zZSgpIHtcbiAgICAgICAgICAgIGlmIChjbG9zZWQpXG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgY2xvc2VkID0gdHJ1ZTtcbiAgICAgICAgICAgIGNsZWFyVGltZW91dChkb25lVGltZXIpO1xuICAgICAgICAgICAgZGlhbG9nLnJlbW92ZSgpO1xuICAgICAgICB9XG4gICAgICAgIENvZGVNaXJyb3Iub24oZGlhbG9nLCAnY2xpY2snLCBmdW5jdGlvbiAoZSkge1xuICAgICAgICAgICAgQ29kZU1pcnJvci5lX3ByZXZlbnREZWZhdWx0KGUpO1xuICAgICAgICAgICAgY2xvc2UoKTtcbiAgICAgICAgfSk7XG4gICAgICAgIGlmIChkdXJhdGlvbilcbiAgICAgICAgICAgIGRvbmVUaW1lciA9IHNldFRpbWVvdXQoY2xvc2UsIGR1cmF0aW9uKTtcbiAgICAgICAgcmV0dXJuIGNsb3NlO1xuICAgIH0pO1xufSkoKTtcbnZhciBQb3MgPSBDb2RlTWlycm9yLlBvcztcbmZ1bmN0aW9uIHVwZGF0ZVNlbGVjdGlvbkZvclN1cnJvZ2F0ZUNoYXJhY3RlcnMoY20sIGN1clN0YXJ0LCBjdXJFbmQpIHtcbiAgICBpZiAoY3VyU3RhcnQubGluZSA9PT0gY3VyRW5kLmxpbmUgJiYgY3VyU3RhcnQuY2ggPj0gY3VyRW5kLmNoIC0gMSkge1xuICAgICAgICB2YXIgdGV4dCA9IGNtLmdldExpbmUoY3VyU3RhcnQubGluZSk7XG4gICAgICAgIHZhciBjaGFyQ29kZSA9IHRleHQuY2hhckNvZGVBdChjdXJTdGFydC5jaCk7XG4gICAgICAgIGlmICgweEQ4MDAgPD0gY2hhckNvZGUgJiYgY2hhckNvZGUgPD0gMHhEOEZGKSB7XG4gICAgICAgICAgICBjdXJFbmQuY2ggKz0gMTtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4geyBzdGFydDogY3VyU3RhcnQsIGVuZDogY3VyRW5kIH07XG59XG52YXIgZGVmYXVsdEtleW1hcCA9IFtcbiAgICB7IGtleXM6ICc8TGVmdD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdoJyB9LFxuICAgIHsga2V5czogJzxSaWdodD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdsJyB9LFxuICAgIHsga2V5czogJzxVcD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdrJyB9LFxuICAgIHsga2V5czogJzxEb3duPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJ2onIH0sXG4gICAgeyBrZXlzOiAnZzxVcD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdnaycgfSxcbiAgICB7IGtleXM6ICdnPERvd24+JywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnZ2onIH0sXG4gICAgeyBrZXlzOiAnPFNwYWNlPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJ2wnIH0sXG4gICAgeyBrZXlzOiAnPEJTPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJ2gnIH0sXG4gICAgeyBrZXlzOiAnPERlbD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICd4JyB9LFxuICAgIHsga2V5czogJzxDLVNwYWNlPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJ1cnIH0sXG4gICAgeyBrZXlzOiAnPEMtQlM+JywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnQicgfSxcbiAgICB7IGtleXM6ICc8Uy1TcGFjZT4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICd3JyB9LFxuICAgIHsga2V5czogJzxTLUJTPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJ2InIH0sXG4gICAgeyBrZXlzOiAnPEMtbj4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdqJyB9LFxuICAgIHsga2V5czogJzxDLXA+JywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnaycgfSxcbiAgICB7IGtleXM6ICc8Qy1bPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJzxFc2M+JyB9LFxuICAgIHsga2V5czogJzxDLWM+JywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnPEVzYz4nIH0sXG4gICAgeyBrZXlzOiAnPEMtWz4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICc8RXNjPicsIGNvbnRleHQ6ICdpbnNlcnQnIH0sXG4gICAgeyBrZXlzOiAnPEMtYz4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICc8RXNjPicsIGNvbnRleHQ6ICdpbnNlcnQnIH0sXG4gICAgeyBrZXlzOiAnPEMtRXNjPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJzxFc2M+JyB9LCAvLyBpcGFkIGtleWJvYXJkIHNlbmRzIEMtRXNjIGluc3RlYWQgb2YgQy1bXG4gICAgeyBrZXlzOiAnPEMtRXNjPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJzxFc2M+JywgY29udGV4dDogJ2luc2VydCcgfSxcbiAgICB7IGtleXM6ICdzJywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnY2wnLCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ3MnLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdjJywgY29udGV4dDogJ3Zpc3VhbCcgfSxcbiAgICB7IGtleXM6ICdTJywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnY2MnLCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ1MnLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdWZE8nLCBjb250ZXh0OiAndmlzdWFsJyB9LFxuICAgIHsga2V5czogJzxIb21lPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJzAnIH0sXG4gICAgeyBrZXlzOiAnPEVuZD4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICckJyB9LFxuICAgIHsga2V5czogJzxQYWdlVXA+JywgdHlwZTogJ2tleVRvS2V5JywgdG9LZXlzOiAnPEMtYj4nIH0sXG4gICAgeyBrZXlzOiAnPFBhZ2VEb3duPicsIHR5cGU6ICdrZXlUb0tleScsIHRvS2V5czogJzxDLWY+JyB9LFxuICAgIHsga2V5czogJzxDUj4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdqXicsIGNvbnRleHQ6ICdub3JtYWwnIH0sXG4gICAgeyBrZXlzOiAnPElucz4nLCB0eXBlOiAna2V5VG9LZXknLCB0b0tleXM6ICdpJywgY29udGV4dDogJ25vcm1hbCcgfSxcbiAgICB7IGtleXM6ICc8SW5zPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICd0b2dnbGVPdmVyd3JpdGUnLCBjb250ZXh0OiAnaW5zZXJ0JyB9LFxuICAgIHsga2V5czogJ0gnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRvVG9wTGluZScsIG1vdGlvbkFyZ3M6IHsgbGluZXdpc2U6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ00nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRvTWlkZGxlTGluZScsIG1vdGlvbkFyZ3M6IHsgbGluZXdpc2U6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ0wnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRvQm90dG9tTGluZScsIG1vdGlvbkFyZ3M6IHsgbGluZXdpc2U6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2gnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5Q2hhcmFjdGVycycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJ2wnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5Q2hhcmFjdGVycycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnaicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlMaW5lcycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgbGluZXdpc2U6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2snLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5TGluZXMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCBsaW5ld2lzZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnZ2onLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5RGlzcGxheUxpbmVzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdnaycsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlEaXNwbGF5TGluZXMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICd3JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVdvcmRzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCB3b3JkRW5kOiBmYWxzZSB9IH0sXG4gICAgeyBrZXlzOiAnVycsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlXb3JkcycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgd29yZEVuZDogZmFsc2UsIGJpZ1dvcmQ6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2UnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5V29yZHMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IHRydWUsIHdvcmRFbmQ6IHRydWUsIGluY2x1c2l2ZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnRScsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlXb3JkcycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgd29yZEVuZDogdHJ1ZSwgYmlnV29yZDogdHJ1ZSwgaW5jbHVzaXZlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdiJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVdvcmRzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgd29yZEVuZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJ0InLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5V29yZHMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCB3b3JkRW5kOiBmYWxzZSwgYmlnV29yZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnZ2UnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5V29yZHMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCB3b3JkRW5kOiB0cnVlLCBpbmNsdXNpdmU6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2dFJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVdvcmRzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgd29yZEVuZDogdHJ1ZSwgYmlnV29yZDogdHJ1ZSwgaW5jbHVzaXZlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICd7JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVBhcmFncmFwaCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ30nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5UGFyYWdyYXBoJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICcoJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVNlbnRlbmNlJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSB9IH0sXG4gICAgeyBrZXlzOiAnKScsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlTZW50ZW5jZScsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMtZj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5UGFnZScsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMtYj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZUJ5UGFnZScsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJzxDLWQ+JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVNjcm9sbCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgZXhwbGljaXRSZXBlYXQ6IHRydWUgfSB9LFxuICAgIHsga2V5czogJzxDLXU+JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeVNjcm9sbCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UsIGV4cGxpY2l0UmVwZWF0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdnZycsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9MaW5lT3JFZGdlT2ZEb2N1bWVudCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UsIGV4cGxpY2l0UmVwZWF0OiB0cnVlLCBsaW5ld2lzZTogdHJ1ZSwgdG9KdW1wbGlzdDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnRycsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9MaW5lT3JFZGdlT2ZEb2N1bWVudCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgZXhwbGljaXRSZXBlYXQ6IHRydWUsIGxpbmV3aXNlOiB0cnVlLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6IFwiZyRcIiwgdHlwZTogXCJtb3Rpb25cIiwgbW90aW9uOiBcIm1vdmVUb0VuZE9mRGlzcGxheUxpbmVcIiB9LFxuICAgIHsga2V5czogXCJnXlwiLCB0eXBlOiBcIm1vdGlvblwiLCBtb3Rpb246IFwibW92ZVRvU3RhcnRPZkRpc3BsYXlMaW5lXCIgfSxcbiAgICB7IGtleXM6IFwiZzBcIiwgdHlwZTogXCJtb3Rpb25cIiwgbW90aW9uOiBcIm1vdmVUb1N0YXJ0T2ZEaXNwbGF5TGluZVwiIH0sXG4gICAgeyBrZXlzOiAnMCcsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9TdGFydE9mTGluZScgfSxcbiAgICB7IGtleXM6ICdeJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVUb0ZpcnN0Tm9uV2hpdGVTcGFjZUNoYXJhY3RlcicgfSxcbiAgICB7IGtleXM6ICcrJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeUxpbmVzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCB0b0ZpcnN0Q2hhcjogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnLScsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlQnlMaW5lcycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UsIHRvRmlyc3RDaGFyOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdfJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVCeUxpbmVzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCB0b0ZpcnN0Q2hhcjogdHJ1ZSwgcmVwZWF0T2Zmc2V0OiAtMSB9IH0sXG4gICAgeyBrZXlzOiAnJCcsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9Fb2wnLCBtb3Rpb25BcmdzOiB7IGluY2x1c2l2ZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnJScsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9NYXRjaGVkU3ltYm9sJywgbW90aW9uQXJnczogeyBpbmNsdXNpdmU6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2Y8Y2hhcmFjdGVyPicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9DaGFyYWN0ZXInLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IHRydWUsIGluY2x1c2l2ZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnRjxjaGFyYWN0ZXI+JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVUb0NoYXJhY3RlcicsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJ3Q8Y2hhcmFjdGVyPicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVGlsbENoYXJhY3RlcicsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgaW5jbHVzaXZlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdUPGNoYXJhY3Rlcj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRpbGxDaGFyYWN0ZXInLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICc7JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ3JlcGVhdExhc3RDaGFyYWN0ZXJTZWFyY2gnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IHRydWUgfSB9LFxuICAgIHsga2V5czogJywnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAncmVwZWF0TGFzdENoYXJhY3RlclNlYXJjaCcsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJ1xcJzxyZWdpc3Rlcj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnZ29Ub01hcmsnLCBtb3Rpb25BcmdzOiB7IHRvSnVtcGxpc3Q6IHRydWUsIGxpbmV3aXNlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdgPHJlZ2lzdGVyPicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdnb1RvTWFyaycsIG1vdGlvbkFyZ3M6IHsgdG9KdW1wbGlzdDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnXWAnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnanVtcFRvTWFyaycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnW2AnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnanVtcFRvTWFyaycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UgfSB9LFxuICAgIHsga2V5czogJ11cXCcnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnanVtcFRvTWFyaycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgbGluZXdpc2U6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ1tcXCcnLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnanVtcFRvTWFyaycsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogZmFsc2UsIGxpbmV3aXNlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICddcCcsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdwYXN0ZScsIGlzRWRpdDogdHJ1ZSwgYWN0aW9uQXJnczogeyBhZnRlcjogdHJ1ZSwgaXNFZGl0OiB0cnVlLCBtYXRjaEluZGVudDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnW3AnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAncGFzdGUnLCBpc0VkaXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgYWZ0ZXI6IGZhbHNlLCBpc0VkaXQ6IHRydWUsIG1hdGNoSW5kZW50OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICddPGNoYXJhY3Rlcj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRvU3ltYm9sJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdbPGNoYXJhY3Rlcj4nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnbW92ZVRvU3ltYm9sJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgdG9KdW1wbGlzdDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnfCcsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9Db2x1bW4nIH0sXG4gICAgeyBrZXlzOiAnbycsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdtb3ZlVG9PdGhlckhpZ2hsaWdodGVkRW5kJywgY29udGV4dDogJ3Zpc3VhbCcgfSxcbiAgICB7IGtleXM6ICdPJywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ21vdmVUb090aGVySGlnaGxpZ2h0ZWRFbmQnLCBtb3Rpb25BcmdzOiB7IHNhbWVMaW5lOiB0cnVlIH0sIGNvbnRleHQ6ICd2aXN1YWwnIH0sXG4gICAgeyBrZXlzOiAnZCcsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnZGVsZXRlJyB9LFxuICAgIHsga2V5czogJ3knLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ3lhbmsnIH0sXG4gICAgeyBrZXlzOiAnYycsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnY2hhbmdlJyB9LFxuICAgIHsga2V5czogJz0nLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ2luZGVudEF1dG8nIH0sXG4gICAgeyBrZXlzOiAnPicsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnaW5kZW50Jywgb3BlcmF0b3JBcmdzOiB7IGluZGVudFJpZ2h0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICc8JywgdHlwZTogJ29wZXJhdG9yJywgb3BlcmF0b3I6ICdpbmRlbnQnLCBvcGVyYXRvckFyZ3M6IHsgaW5kZW50UmlnaHQ6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICdnficsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnY2hhbmdlQ2FzZScgfSxcbiAgICB7IGtleXM6ICdndScsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnY2hhbmdlQ2FzZScsIG9wZXJhdG9yQXJnczogeyB0b0xvd2VyOiB0cnVlIH0sIGlzRWRpdDogdHJ1ZSB9LFxuICAgIHsga2V5czogJ2dVJywgdHlwZTogJ29wZXJhdG9yJywgb3BlcmF0b3I6ICdjaGFuZ2VDYXNlJywgb3BlcmF0b3JBcmdzOiB7IHRvTG93ZXI6IGZhbHNlIH0sIGlzRWRpdDogdHJ1ZSB9LFxuICAgIHsga2V5czogJ24nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnZmluZE5leHQnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ04nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnZmluZE5leHQnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdnbicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICdmaW5kQW5kU2VsZWN0TmV4dEluY2x1c2l2ZScsIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnZ04nLCB0eXBlOiAnbW90aW9uJywgbW90aW9uOiAnZmluZEFuZFNlbGVjdE5leHRJbmNsdXNpdmUnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICdncScsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnaGFyZFdyYXAnIH0sXG4gICAgeyBrZXlzOiAnZ3cnLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ2hhcmRXcmFwJywgb3BlcmF0b3JBcmdzOiB7IGtlZXBDdXJzb3I6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ3gnLCB0eXBlOiAnb3BlcmF0b3JNb3Rpb24nLCBvcGVyYXRvcjogJ2RlbGV0ZScsIG1vdGlvbjogJ21vdmVCeUNoYXJhY3RlcnMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IHRydWUgfSwgb3BlcmF0b3JNb3Rpb25BcmdzOiB7IHZpc3VhbExpbmU6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICdYJywgdHlwZTogJ29wZXJhdG9yTW90aW9uJywgb3BlcmF0b3I6ICdkZWxldGUnLCBtb3Rpb246ICdtb3ZlQnlDaGFyYWN0ZXJzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSB9LCBvcGVyYXRvck1vdGlvbkFyZ3M6IHsgdmlzdWFsTGluZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnRCcsIHR5cGU6ICdvcGVyYXRvck1vdGlvbicsIG9wZXJhdG9yOiAnZGVsZXRlJywgbW90aW9uOiAnbW92ZVRvRW9sJywgbW90aW9uQXJnczogeyBpbmNsdXNpdmU6IHRydWUgfSwgY29udGV4dDogJ25vcm1hbCcgfSxcbiAgICB7IGtleXM6ICdEJywgdHlwZTogJ29wZXJhdG9yJywgb3BlcmF0b3I6ICdkZWxldGUnLCBvcGVyYXRvckFyZ3M6IHsgbGluZXdpc2U6IHRydWUgfSwgY29udGV4dDogJ3Zpc3VhbCcgfSxcbiAgICB7IGtleXM6ICdZJywgdHlwZTogJ29wZXJhdG9yTW90aW9uJywgb3BlcmF0b3I6ICd5YW5rJywgbW90aW9uOiAnZXhwYW5kVG9MaW5lJywgbW90aW9uQXJnczogeyBsaW5ld2lzZTogdHJ1ZSB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ1knLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ3lhbmsnLCBvcGVyYXRvckFyZ3M6IHsgbGluZXdpc2U6IHRydWUgfSwgY29udGV4dDogJ3Zpc3VhbCcgfSxcbiAgICB7IGtleXM6ICdDJywgdHlwZTogJ29wZXJhdG9yTW90aW9uJywgb3BlcmF0b3I6ICdjaGFuZ2UnLCBtb3Rpb246ICdtb3ZlVG9Fb2wnLCBtb3Rpb25BcmdzOiB7IGluY2x1c2l2ZTogdHJ1ZSB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ0MnLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ2NoYW5nZScsIG9wZXJhdG9yQXJnczogeyBsaW5ld2lzZTogdHJ1ZSB9LCBjb250ZXh0OiAndmlzdWFsJyB9LFxuICAgIHsga2V5czogJ34nLCB0eXBlOiAnb3BlcmF0b3JNb3Rpb24nLCBvcGVyYXRvcjogJ2NoYW5nZUNhc2UnLCBtb3Rpb246ICdtb3ZlQnlDaGFyYWN0ZXJzJywgbW90aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlIH0sIG9wZXJhdG9yQXJnczogeyBzaG91bGRNb3ZlQ3Vyc29yOiB0cnVlIH0sIGNvbnRleHQ6ICdub3JtYWwnIH0sXG4gICAgeyBrZXlzOiAnficsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnY2hhbmdlQ2FzZScsIGNvbnRleHQ6ICd2aXN1YWwnIH0sXG4gICAgeyBrZXlzOiAnPEMtdT4nLCB0eXBlOiAnb3BlcmF0b3JNb3Rpb24nLCBvcGVyYXRvcjogJ2RlbGV0ZScsIG1vdGlvbjogJ21vdmVUb1N0YXJ0T2ZMaW5lJywgY29udGV4dDogJ2luc2VydCcgfSxcbiAgICB7IGtleXM6ICc8Qy13PicsIHR5cGU6ICdvcGVyYXRvck1vdGlvbicsIG9wZXJhdG9yOiAnZGVsZXRlJywgbW90aW9uOiAnbW92ZUJ5V29yZHMnLCBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCB3b3JkRW5kOiBmYWxzZSB9LCBjb250ZXh0OiAnaW5zZXJ0JyB9LFxuICAgIHsga2V5czogJzxDLXc+JywgdHlwZTogJ2lkbGUnLCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJzxDLWk+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2p1bXBMaXN0V2FsaycsIGFjdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMtbz4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnanVtcExpc3RXYWxrJywgYWN0aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMtZT4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsJywgYWN0aW9uQXJnczogeyBmb3J3YXJkOiB0cnVlLCBsaW5ld2lzZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMteT4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsJywgYWN0aW9uQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgbGluZXdpc2U6IHRydWUgfSB9LFxuICAgIHsga2V5czogJ2EnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGluc2VydEF0OiAnY2hhckFmdGVyJyB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ0EnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGluc2VydEF0OiAnZW9sJyB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ0EnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGluc2VydEF0OiAnZW5kT2ZTZWxlY3RlZEFyZWEnIH0sIGNvbnRleHQ6ICd2aXN1YWwnIH0sXG4gICAgeyBrZXlzOiAnaScsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdlbnRlckluc2VydE1vZGUnLCBpc0VkaXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgaW5zZXJ0QXQ6ICdpbnBsYWNlJyB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ2dpJywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2VudGVySW5zZXJ0TW9kZScsIGlzRWRpdDogdHJ1ZSwgYWN0aW9uQXJnczogeyBpbnNlcnRBdDogJ2xhc3RFZGl0JyB9LCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ0knLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGluc2VydEF0OiAnZmlyc3ROb25CbGFuaycgfSwgY29udGV4dDogJ25vcm1hbCcgfSxcbiAgICB7IGtleXM6ICdnSScsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdlbnRlckluc2VydE1vZGUnLCBpc0VkaXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgaW5zZXJ0QXQ6ICdib2wnIH0sIGNvbnRleHQ6ICdub3JtYWwnIH0sXG4gICAgeyBrZXlzOiAnSScsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdlbnRlckluc2VydE1vZGUnLCBpc0VkaXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgaW5zZXJ0QXQ6ICdzdGFydE9mU2VsZWN0ZWRBcmVhJyB9LCBjb250ZXh0OiAndmlzdWFsJyB9LFxuICAgIHsga2V5czogJ28nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnbmV3TGluZUFuZEVudGVySW5zZXJ0TW9kZScsIGlzRWRpdDogdHJ1ZSwgaW50ZXJsYWNlSW5zZXJ0UmVwZWF0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGFmdGVyOiB0cnVlIH0sIGNvbnRleHQ6ICdub3JtYWwnIH0sXG4gICAgeyBrZXlzOiAnTycsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICduZXdMaW5lQW5kRW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBpbnRlcmxhY2VJbnNlcnRSZXBlYXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgYWZ0ZXI6IGZhbHNlIH0sIGNvbnRleHQ6ICdub3JtYWwnIH0sXG4gICAgeyBrZXlzOiAndicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICd0b2dnbGVWaXN1YWxNb2RlJyB9LFxuICAgIHsga2V5czogJ1YnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAndG9nZ2xlVmlzdWFsTW9kZScsIGFjdGlvbkFyZ3M6IHsgbGluZXdpc2U6IHRydWUgfSB9LFxuICAgIHsga2V5czogJzxDLXY+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ3RvZ2dsZVZpc3VhbE1vZGUnLCBhY3Rpb25BcmdzOiB7IGJsb2Nrd2lzZTogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMtcT4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAndG9nZ2xlVmlzdWFsTW9kZScsIGFjdGlvbkFyZ3M6IHsgYmxvY2t3aXNlOiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdndicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdyZXNlbGVjdExhc3RTZWxlY3Rpb24nIH0sXG4gICAgeyBrZXlzOiAnSicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdqb2luTGluZXMnLCBpc0VkaXQ6IHRydWUgfSxcbiAgICB7IGtleXM6ICdnSicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdqb2luTGluZXMnLCBhY3Rpb25BcmdzOiB7IGtlZXBTcGFjZXM6IHRydWUgfSwgaXNFZGl0OiB0cnVlIH0sXG4gICAgeyBrZXlzOiAncCcsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdwYXN0ZScsIGlzRWRpdDogdHJ1ZSwgYWN0aW9uQXJnczogeyBhZnRlcjogdHJ1ZSwgaXNFZGl0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdQJywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ3Bhc3RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IGFmdGVyOiBmYWxzZSwgaXNFZGl0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdyPGNoYXJhY3Rlcj4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAncmVwbGFjZScsIGlzRWRpdDogdHJ1ZSB9LFxuICAgIHsga2V5czogJ0A8cmVnaXN0ZXI+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ3JlcGxheU1hY3JvJyB9LFxuICAgIHsga2V5czogJ3E8cmVnaXN0ZXI+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2VudGVyTWFjcm9SZWNvcmRNb2RlJyB9LFxuICAgIHsga2V5czogJ1InLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZW50ZXJJbnNlcnRNb2RlJywgaXNFZGl0OiB0cnVlLCBhY3Rpb25BcmdzOiB7IHJlcGxhY2U6IHRydWUgfSwgY29udGV4dDogJ25vcm1hbCcgfSxcbiAgICB7IGtleXM6ICdSJywgdHlwZTogJ29wZXJhdG9yJywgb3BlcmF0b3I6ICdjaGFuZ2UnLCBvcGVyYXRvckFyZ3M6IHsgbGluZXdpc2U6IHRydWUsIGZ1bGxMaW5lOiB0cnVlIH0sIGNvbnRleHQ6ICd2aXN1YWwnLCBleGl0VmlzdWFsQmxvY2s6IHRydWUgfSxcbiAgICB7IGtleXM6ICd1JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ3VuZG8nLCBjb250ZXh0OiAnbm9ybWFsJyB9LFxuICAgIHsga2V5czogJ3UnLCB0eXBlOiAnb3BlcmF0b3InLCBvcGVyYXRvcjogJ2NoYW5nZUNhc2UnLCBvcGVyYXRvckFyZ3M6IHsgdG9Mb3dlcjogdHJ1ZSB9LCBjb250ZXh0OiAndmlzdWFsJywgaXNFZGl0OiB0cnVlIH0sXG4gICAgeyBrZXlzOiAnVScsIHR5cGU6ICdvcGVyYXRvcicsIG9wZXJhdG9yOiAnY2hhbmdlQ2FzZScsIG9wZXJhdG9yQXJnczogeyB0b0xvd2VyOiBmYWxzZSB9LCBjb250ZXh0OiAndmlzdWFsJywgaXNFZGl0OiB0cnVlIH0sXG4gICAgeyBrZXlzOiAnPEMtcj4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAncmVkbycgfSxcbiAgICB7IGtleXM6ICdtPHJlZ2lzdGVyPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdzZXRNYXJrJyB9LFxuICAgIHsga2V5czogJ1wiPHJlZ2lzdGVyPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdzZXRSZWdpc3RlcicgfSxcbiAgICB7IGtleXM6ICc8Qy1yPjxyZWdpc3Rlcj4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnaW5zZXJ0UmVnaXN0ZXInLCBjb250ZXh0OiAnaW5zZXJ0JywgaXNFZGl0OiB0cnVlIH0sXG4gICAgeyBrZXlzOiAnPEMtbz4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnb25lTm9ybWFsQ29tbWFuZCcsIGNvbnRleHQ6ICdpbnNlcnQnIH0sXG4gICAgeyBrZXlzOiAnenonLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAnY2VudGVyJyB9IH0sXG4gICAgeyBrZXlzOiAnei4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAnY2VudGVyJyB9LCBtb3Rpb246ICdtb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXInIH0sXG4gICAgeyBrZXlzOiAnenQnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAndG9wJyB9IH0sXG4gICAgeyBrZXlzOiAnejxDUj4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAndG9wJyB9LCBtb3Rpb246ICdtb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXInIH0sXG4gICAgeyBrZXlzOiAnemInLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAnYm90dG9tJyB9IH0sXG4gICAgeyBrZXlzOiAnei0nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnc2Nyb2xsVG9DdXJzb3InLCBhY3Rpb25BcmdzOiB7IHBvc2l0aW9uOiAnYm90dG9tJyB9LCBtb3Rpb246ICdtb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXInIH0sXG4gICAgeyBrZXlzOiAnLicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdyZXBlYXRMYXN0RWRpdCcgfSxcbiAgICB7IGtleXM6ICc8Qy1hPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdpbmNyZW1lbnROdW1iZXJUb2tlbicsIGlzRWRpdDogdHJ1ZSwgYWN0aW9uQXJnczogeyBpbmNyZWFzZTogdHJ1ZSwgYmFja3RyYWNrOiBmYWxzZSB9IH0sXG4gICAgeyBrZXlzOiAnPEMteD4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnaW5jcmVtZW50TnVtYmVyVG9rZW4nLCBpc0VkaXQ6IHRydWUsIGFjdGlvbkFyZ3M6IHsgaW5jcmVhc2U6IGZhbHNlLCBiYWNrdHJhY2s6IGZhbHNlIH0gfSxcbiAgICB7IGtleXM6ICc8Qy10PicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdpbmRlbnQnLCBhY3Rpb25BcmdzOiB7IGluZGVudFJpZ2h0OiB0cnVlIH0sIGNvbnRleHQ6ICdpbnNlcnQnIH0sXG4gICAgeyBrZXlzOiAnPEMtZD4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnaW5kZW50JywgYWN0aW9uQXJnczogeyBpbmRlbnRSaWdodDogZmFsc2UgfSwgY29udGV4dDogJ2luc2VydCcgfSxcbiAgICB7IGtleXM6ICdhPHJlZ2lzdGVyPicsIHR5cGU6ICdtb3Rpb24nLCBtb3Rpb246ICd0ZXh0T2JqZWN0TWFuaXB1bGF0aW9uJyB9LFxuICAgIHsga2V5czogJ2k8cmVnaXN0ZXI+JywgdHlwZTogJ21vdGlvbicsIG1vdGlvbjogJ3RleHRPYmplY3RNYW5pcHVsYXRpb24nLCBtb3Rpb25BcmdzOiB7IHRleHRPYmplY3RJbm5lcjogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnLycsIHR5cGU6ICdzZWFyY2gnLCBzZWFyY2hBcmdzOiB7IGZvcndhcmQ6IHRydWUsIHF1ZXJ5U3JjOiAncHJvbXB0JywgdG9KdW1wbGlzdDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnPycsIHR5cGU6ICdzZWFyY2gnLCBzZWFyY2hBcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCBxdWVyeVNyYzogJ3Byb21wdCcsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJyonLCB0eXBlOiAnc2VhcmNoJywgc2VhcmNoQXJnczogeyBmb3J3YXJkOiB0cnVlLCBxdWVyeVNyYzogJ3dvcmRVbmRlckN1cnNvcicsIHdob2xlV29yZE9ubHk6IHRydWUsIHRvSnVtcGxpc3Q6IHRydWUgfSB9LFxuICAgIHsga2V5czogJyMnLCB0eXBlOiAnc2VhcmNoJywgc2VhcmNoQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgcXVlcnlTcmM6ICd3b3JkVW5kZXJDdXJzb3InLCB3aG9sZVdvcmRPbmx5OiB0cnVlLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICdnKicsIHR5cGU6ICdzZWFyY2gnLCBzZWFyY2hBcmdzOiB7IGZvcndhcmQ6IHRydWUsIHF1ZXJ5U3JjOiAnd29yZFVuZGVyQ3Vyc29yJywgdG9KdW1wbGlzdDogdHJ1ZSB9IH0sXG4gICAgeyBrZXlzOiAnZyMnLCB0eXBlOiAnc2VhcmNoJywgc2VhcmNoQXJnczogeyBmb3J3YXJkOiBmYWxzZSwgcXVlcnlTcmM6ICd3b3JkVW5kZXJDdXJzb3InLCB0b0p1bXBsaXN0OiB0cnVlIH0gfSxcbiAgICB7IGtleXM6ICc6JywgdHlwZTogJ2V4JyB9XG5dO1xudmFyIGRlZmF1bHRLZXltYXBMZW5ndGggPSBkZWZhdWx0S2V5bWFwLmxlbmd0aDtcbnZhciBkZWZhdWx0RXhDb21tYW5kTWFwID0gW1xuICAgIHsgbmFtZTogJ2NvbG9yc2NoZW1lJywgc2hvcnROYW1lOiAnY29sbycgfSxcbiAgICB7IG5hbWU6ICdtYXAnIH0sXG4gICAgeyBuYW1lOiAnaW1hcCcsIHNob3J0TmFtZTogJ2ltJyB9LFxuICAgIHsgbmFtZTogJ25tYXAnLCBzaG9ydE5hbWU6ICdubScgfSxcbiAgICB7IG5hbWU6ICd2bWFwJywgc2hvcnROYW1lOiAndm0nIH0sXG4gICAgeyBuYW1lOiAnb21hcCcsIHNob3J0TmFtZTogJ29tJyB9LFxuICAgIHsgbmFtZTogJ25vcmVtYXAnLCBzaG9ydE5hbWU6ICdubycgfSxcbiAgICB7IG5hbWU6ICdubm9yZW1hcCcsIHNob3J0TmFtZTogJ25uJyB9LFxuICAgIHsgbmFtZTogJ3Zub3JlbWFwJywgc2hvcnROYW1lOiAndm4nIH0sXG4gICAgeyBuYW1lOiAnaW5vcmVtYXAnLCBzaG9ydE5hbWU6ICdpbm8nIH0sXG4gICAgeyBuYW1lOiAnb25vcmVtYXAnLCBzaG9ydE5hbWU6ICdvbm8nIH0sXG4gICAgeyBuYW1lOiAndW5tYXAnIH0sXG4gICAgeyBuYW1lOiAnbWFwY2xlYXInLCBzaG9ydE5hbWU6ICdtYXBjJyB9LFxuICAgIHsgbmFtZTogJ25tYXBjbGVhcicsIHNob3J0TmFtZTogJ25tYXBjJyB9LFxuICAgIHsgbmFtZTogJ3ZtYXBjbGVhcicsIHNob3J0TmFtZTogJ3ZtYXBjJyB9LFxuICAgIHsgbmFtZTogJ2ltYXBjbGVhcicsIHNob3J0TmFtZTogJ2ltYXBjJyB9LFxuICAgIHsgbmFtZTogJ29tYXBjbGVhcicsIHNob3J0TmFtZTogJ29tYXBjJyB9LFxuICAgIHsgbmFtZTogJ3dyaXRlJywgc2hvcnROYW1lOiAndycgfSxcbiAgICB7IG5hbWU6ICd1bmRvJywgc2hvcnROYW1lOiAndScgfSxcbiAgICB7IG5hbWU6ICdyZWRvJywgc2hvcnROYW1lOiAncmVkJyB9LFxuICAgIHsgbmFtZTogJ3NldCcsIHNob3J0TmFtZTogJ3NlJyB9LFxuICAgIHsgbmFtZTogJ3NldGxvY2FsJywgc2hvcnROYW1lOiAnc2V0bCcgfSxcbiAgICB7IG5hbWU6ICdzZXRnbG9iYWwnLCBzaG9ydE5hbWU6ICdzZXRnJyB9LFxuICAgIHsgbmFtZTogJ3NvcnQnLCBzaG9ydE5hbWU6ICdzb3InIH0sXG4gICAgeyBuYW1lOiAnc3Vic3RpdHV0ZScsIHNob3J0TmFtZTogJ3MnLCBwb3NzaWJseUFzeW5jOiB0cnVlIH0sXG4gICAgeyBuYW1lOiAnc3RhcnRpbnNlcnQnLCBzaG9ydE5hbWU6ICdzdGFydCcgfSxcbiAgICB7IG5hbWU6ICdub2hsc2VhcmNoJywgc2hvcnROYW1lOiAnbm9oJyB9LFxuICAgIHsgbmFtZTogJ3lhbmsnLCBzaG9ydE5hbWU6ICd5JyB9LFxuICAgIHsgbmFtZTogJ2RlbG1hcmtzJywgc2hvcnROYW1lOiAnZGVsbScgfSxcbiAgICB7IG5hbWU6ICdyZWdpc3RlcnMnLCBzaG9ydE5hbWU6ICdyZWcnLCBleGNsdWRlRnJvbUNvbW1hbmRIaXN0b3J5OiB0cnVlIH0sXG4gICAgeyBuYW1lOiAndmdsb2JhbCcsIHNob3J0TmFtZTogJ3YnIH0sXG4gICAgeyBuYW1lOiAnZGVsZXRlJywgc2hvcnROYW1lOiAnZCcgfSxcbiAgICB7IG5hbWU6ICdqb2luJywgc2hvcnROYW1lOiAnaicgfSxcbiAgICB7IG5hbWU6ICdub3JtYWwnLCBzaG9ydE5hbWU6ICdub3JtJyB9LFxuICAgIHsgbmFtZTogJ2dsb2JhbCcsIHNob3J0TmFtZTogJ2cnIH1cbl07XG52YXIgbGFuZ21hcCA9IHBhcnNlTGFuZ21hcCgnJyk7XG5mdW5jdGlvbiBlbnRlclZpbU1vZGUoY20pIHtcbiAgICBjbS5zZXRPcHRpb24oJ2Rpc2FibGVJbnB1dCcsIHRydWUpO1xuICAgIGNtLnNldE9wdGlvbignc2hvd0N1cnNvcldoZW5TZWxlY3RpbmcnLCBmYWxzZSk7XG4gICAgQ29kZU1pcnJvci5zaWduYWwoY20sIFwidmltLW1vZGUtY2hhbmdlXCIsIHsgbW9kZTogXCJub3JtYWxcIiB9KTtcbiAgICBjbS5vbignY3Vyc29yQWN0aXZpdHknLCBvbkN1cnNvckFjdGl2aXR5KTtcbiAgICBtYXliZUluaXRWaW1TdGF0ZShjbSk7XG4gICAgQ29kZU1pcnJvci5vbihjbS5nZXRJbnB1dEZpZWxkKCksICdwYXN0ZScsIGdldE9uUGFzdGVGbihjbSkpO1xufVxuZnVuY3Rpb24gbGVhdmVWaW1Nb2RlKGNtKSB7XG4gICAgY20uc2V0T3B0aW9uKCdkaXNhYmxlSW5wdXQnLCBmYWxzZSk7XG4gICAgY20ub2ZmKCdjdXJzb3JBY3Rpdml0eScsIG9uQ3Vyc29yQWN0aXZpdHkpO1xuICAgIENvZGVNaXJyb3Iub2ZmKGNtLmdldElucHV0RmllbGQoKSwgJ3Bhc3RlJywgZ2V0T25QYXN0ZUZuKGNtKSk7XG4gICAgY20uc3RhdGUudmltID0gbnVsbDtcbiAgICBpZiAoaGlnaGxpZ2h0VGltZW91dClcbiAgICAgICAgY2xlYXJUaW1lb3V0KGhpZ2hsaWdodFRpbWVvdXQpO1xufVxuZnVuY3Rpb24gZ2V0T25QYXN0ZUZuKGNtKSB7XG4gICAgdmFyIHZpbSA9IGNtLnN0YXRlLnZpbTtcbiAgICBpZiAoIXZpbS5vblBhc3RlRm4pIHtcbiAgICAgICAgdmltLm9uUGFzdGVGbiA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgIGlmICghdmltLmluc2VydE1vZGUpIHtcbiAgICAgICAgICAgICAgICBjbS5zZXRDdXJzb3Iob2Zmc2V0Q3Vyc29yKGNtLmdldEN1cnNvcigpLCAwLCAxKSk7XG4gICAgICAgICAgICAgICAgYWN0aW9ucy5lbnRlckluc2VydE1vZGUoY20sIHt9LCB2aW0pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgIH1cbiAgICByZXR1cm4gdmltLm9uUGFzdGVGbjtcbn1cbnZhciBudW1iZXJSZWdleCA9IC9bXFxkXS87XG52YXIgd29yZENoYXJUZXN0ID0gW0NvZGVNaXJyb3IuaXNXb3JkQ2hhciwgZnVuY3Rpb24gKGNoKSB7XG4gICAgICAgIHJldHVybiBjaCAmJiAhQ29kZU1pcnJvci5pc1dvcmRDaGFyKGNoKSAmJiAhL1xccy8udGVzdChjaCk7XG4gICAgfV0sIGJpZ1dvcmRDaGFyVGVzdCA9IFtmdW5jdGlvbiAoY2gpIHtcbiAgICAgICAgcmV0dXJuIC9cXFMvLnRlc3QoY2gpO1xuICAgIH1dO1xudmFyIHZhbGlkTWFya3MgPSBbJzwnLCAnPiddO1xudmFyIHZhbGlkUmVnaXN0ZXJzID0gWyctJywgJ1wiJywgJy4nLCAnOicsICdfJywgJy8nLCAnKyddO1xudmFyIGxhdGluQ2hhclJlZ2V4ID0gL15cXHckLztcbnZhciB1cHBlckNhc2VDaGFycztcbnRyeSB7XG4gICAgdXBwZXJDYXNlQ2hhcnMgPSBuZXcgUmVnRXhwKFwiXltcXFxccHtMdX1dJFwiLCBcInVcIik7XG59XG5jYXRjaCAoXykge1xuICAgIHVwcGVyQ2FzZUNoYXJzID0gL15bQS1aXSQvO1xufVxuZnVuY3Rpb24gaXNMaW5lKGNtLCBsaW5lKSB7XG4gICAgcmV0dXJuIGxpbmUgPj0gY20uZmlyc3RMaW5lKCkgJiYgbGluZSA8PSBjbS5sYXN0TGluZSgpO1xufVxuZnVuY3Rpb24gaXNMb3dlckNhc2Uoaykge1xuICAgIHJldHVybiAoL15bYS16XSQvKS50ZXN0KGspO1xufVxuZnVuY3Rpb24gaXNNYXRjaGFibGVTeW1ib2woaykge1xuICAgIHJldHVybiAnKClbXXt9Jy5pbmRleE9mKGspICE9IC0xO1xufVxuZnVuY3Rpb24gaXNOdW1iZXIoaykge1xuICAgIHJldHVybiBudW1iZXJSZWdleC50ZXN0KGspO1xufVxuZnVuY3Rpb24gaXNVcHBlckNhc2Uoaykge1xuICAgIHJldHVybiB1cHBlckNhc2VDaGFycy50ZXN0KGspO1xufVxuZnVuY3Rpb24gaXNXaGl0ZVNwYWNlU3RyaW5nKGspIHtcbiAgICByZXR1cm4gKC9eXFxzKiQvKS50ZXN0KGspO1xufVxuZnVuY3Rpb24gaXNFbmRPZlNlbnRlbmNlU3ltYm9sKGspIHtcbiAgICByZXR1cm4gJy4/IScuaW5kZXhPZihrKSAhPSAtMTtcbn1cbmZ1bmN0aW9uIGluQXJyYXkodmFsLCBhcnIpIHtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFyci5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAoYXJyW2ldID09IHZhbCkge1xuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxudmFyIG9wdGlvbnMgPSB7fTtcbmZ1bmN0aW9uIGRlZmluZU9wdGlvbihuYW1lLCBkZWZhdWx0VmFsdWUsIHR5cGUsIGFsaWFzZXMsIGNhbGxiYWNrKSB7XG4gICAgaWYgKGRlZmF1bHRWYWx1ZSA9PT0gdW5kZWZpbmVkICYmICFjYWxsYmFjaykge1xuICAgICAgICB0aHJvdyBFcnJvcignZGVmYXVsdFZhbHVlIGlzIHJlcXVpcmVkIHVubGVzcyBjYWxsYmFjayBpcyBwcm92aWRlZCcpO1xuICAgIH1cbiAgICBpZiAoIXR5cGUpIHtcbiAgICAgICAgdHlwZSA9ICdzdHJpbmcnO1xuICAgIH1cbiAgICBvcHRpb25zW25hbWVdID0ge1xuICAgICAgICB0eXBlOiB0eXBlLFxuICAgICAgICBkZWZhdWx0VmFsdWU6IGRlZmF1bHRWYWx1ZSxcbiAgICAgICAgY2FsbGJhY2s6IGNhbGxiYWNrXG4gICAgfTtcbiAgICBpZiAoYWxpYXNlcykge1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFsaWFzZXMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIG9wdGlvbnNbYWxpYXNlc1tpXV0gPSBvcHRpb25zW25hbWVdO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChkZWZhdWx0VmFsdWUpIHtcbiAgICAgICAgc2V0T3B0aW9uKG5hbWUsIGRlZmF1bHRWYWx1ZSk7XG4gICAgfVxufVxuZnVuY3Rpb24gc2V0T3B0aW9uKG5hbWUsIHZhbHVlLCBjbSwgY2ZnKSB7XG4gICAgdmFyIG9wdGlvbiA9IG9wdGlvbnNbbmFtZV07XG4gICAgY2ZnID0gY2ZnIHx8IHt9O1xuICAgIHZhciBzY29wZSA9IGNmZy5zY29wZTtcbiAgICBpZiAoIW9wdGlvbikge1xuICAgICAgICByZXR1cm4gbmV3IEVycm9yKCdVbmtub3duIG9wdGlvbjogJyArIG5hbWUpO1xuICAgIH1cbiAgICBpZiAob3B0aW9uLnR5cGUgPT0gJ2Jvb2xlYW4nKSB7XG4gICAgICAgIGlmICh2YWx1ZSAmJiB2YWx1ZSAhPT0gdHJ1ZSkge1xuICAgICAgICAgICAgcmV0dXJuIG5ldyBFcnJvcignSW52YWxpZCBhcmd1bWVudDogJyArIG5hbWUgKyAnPScgKyB2YWx1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAodmFsdWUgIT09IGZhbHNlKSB7XG4gICAgICAgICAgICB2YWx1ZSA9IHRydWU7XG4gICAgICAgIH1cbiAgICB9XG4gICAgaWYgKG9wdGlvbi5jYWxsYmFjaykge1xuICAgICAgICBpZiAoc2NvcGUgIT09ICdsb2NhbCcpIHtcbiAgICAgICAgICAgIG9wdGlvbi5jYWxsYmFjayh2YWx1ZSwgdW5kZWZpbmVkKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoc2NvcGUgIT09ICdnbG9iYWwnICYmIGNtKSB7XG4gICAgICAgICAgICBvcHRpb24uY2FsbGJhY2sodmFsdWUsIGNtKTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgaWYgKHNjb3BlICE9PSAnbG9jYWwnKSB7XG4gICAgICAgICAgICBvcHRpb24udmFsdWUgPSBvcHRpb24udHlwZSA9PSAnYm9vbGVhbicgPyAhIXZhbHVlIDogdmFsdWU7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHNjb3BlICE9PSAnZ2xvYmFsJyAmJiBjbSkge1xuICAgICAgICAgICAgY20uc3RhdGUudmltLm9wdGlvbnNbbmFtZV0gPSB7IHZhbHVlOiB2YWx1ZSB9O1xuICAgICAgICB9XG4gICAgfVxufVxuZnVuY3Rpb24gZ2V0T3B0aW9uKG5hbWUsIGNtLCBjZmcpIHtcbiAgICB2YXIgb3B0aW9uID0gb3B0aW9uc1tuYW1lXTtcbiAgICBjZmcgPSBjZmcgfHwge307XG4gICAgdmFyIHNjb3BlID0gY2ZnLnNjb3BlO1xuICAgIGlmICghb3B0aW9uKSB7XG4gICAgICAgIHJldHVybiBuZXcgRXJyb3IoJ1Vua25vd24gb3B0aW9uOiAnICsgbmFtZSk7XG4gICAgfVxuICAgIGlmIChvcHRpb24uY2FsbGJhY2spIHtcbiAgICAgICAgdmFyIGxvY2FsID0gY20gJiYgb3B0aW9uLmNhbGxiYWNrKHVuZGVmaW5lZCwgY20pO1xuICAgICAgICBpZiAoc2NvcGUgIT09ICdnbG9iYWwnICYmIGxvY2FsICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgIHJldHVybiBsb2NhbDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoc2NvcGUgIT09ICdsb2NhbCcpIHtcbiAgICAgICAgICAgIHJldHVybiBvcHRpb24uY2FsbGJhY2soKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICB2YXIgbG9jYWwgPSAoc2NvcGUgIT09ICdnbG9iYWwnKSAmJiAoY20gJiYgY20uc3RhdGUudmltLm9wdGlvbnNbbmFtZV0pO1xuICAgICAgICByZXR1cm4gKGxvY2FsIHx8IChzY29wZSAhPT0gJ2xvY2FsJykgJiYgb3B0aW9uIHx8IHt9KS52YWx1ZTtcbiAgICB9XG59XG5kZWZpbmVPcHRpb24oJ2ZpbGV0eXBlJywgdW5kZWZpbmVkLCAnc3RyaW5nJywgWydmdCddLCBmdW5jdGlvbiAobmFtZSwgY20pIHtcbiAgICBpZiAoY20gPT09IHVuZGVmaW5lZCkge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGlmIChuYW1lID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgdmFyIG1vZGUgPSBjbS5nZXRPcHRpb24oJ21vZGUnKTtcbiAgICAgICAgcmV0dXJuIG1vZGUgPT0gJ251bGwnID8gJycgOiBtb2RlO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgdmFyIG1vZGUgPSBuYW1lID09ICcnID8gJ251bGwnIDogbmFtZTtcbiAgICAgICAgY20uc2V0T3B0aW9uKCdtb2RlJywgbW9kZSk7XG4gICAgfVxufSk7XG5kZWZpbmVPcHRpb24oJ3RleHR3aWR0aCcsIDgwLCAnbnVtYmVyJywgWyd0dyddLCBmdW5jdGlvbiAod2lkdGgsIGNtKSB7XG4gICAgaWYgKGNtID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICBpZiAod2lkdGggPT09IHVuZGVmaW5lZCkge1xuICAgICAgICB2YXIgdmFsdWUgPSBjbS5nZXRPcHRpb24oJ3RleHR3aWR0aCcpO1xuICAgICAgICByZXR1cm4gdmFsdWU7XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICB2YXIgY29sdW1uID0gTWF0aC5yb3VuZCh3aWR0aCk7XG4gICAgICAgIGlmIChjb2x1bW4gPiAxKSB7XG4gICAgICAgICAgICBjbS5zZXRPcHRpb24oJ3RleHR3aWR0aCcsIGNvbHVtbik7XG4gICAgICAgIH1cbiAgICB9XG59KTtcbnZhciBjcmVhdGVDaXJjdWxhckp1bXBMaXN0ID0gZnVuY3Rpb24gKCkge1xuICAgIHZhciBzaXplID0gMTAwO1xuICAgIHZhciBwb2ludGVyID0gLTE7XG4gICAgdmFyIGhlYWQgPSAwO1xuICAgIHZhciB0YWlsID0gMDtcbiAgICB2YXIgYnVmZmVyID0gbmV3IEFycmF5KHNpemUpO1xuICAgIGZ1bmN0aW9uIGFkZChjbSwgb2xkQ3VyLCBuZXdDdXIpIHtcbiAgICAgICAgdmFyIGN1cnJlbnQgPSBwb2ludGVyICUgc2l6ZTtcbiAgICAgICAgdmFyIGN1ck1hcmsgPSBidWZmZXJbY3VycmVudF07XG4gICAgICAgIGZ1bmN0aW9uIHVzZU5leHRTbG90KGN1cnNvcikge1xuICAgICAgICAgICAgdmFyIG5leHQgPSArK3BvaW50ZXIgJSBzaXplO1xuICAgICAgICAgICAgdmFyIHRyYXNoTWFyayA9IGJ1ZmZlcltuZXh0XTtcbiAgICAgICAgICAgIGlmICh0cmFzaE1hcmspIHtcbiAgICAgICAgICAgICAgICB0cmFzaE1hcmsuY2xlYXIoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGJ1ZmZlcltuZXh0XSA9IGNtLnNldEJvb2ttYXJrKGN1cnNvcik7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGN1ck1hcmspIHtcbiAgICAgICAgICAgIHZhciBtYXJrUG9zID0gY3VyTWFyay5maW5kKCk7XG4gICAgICAgICAgICBpZiAobWFya1BvcyAmJiAhY3Vyc29yRXF1YWwobWFya1Bvcywgb2xkQ3VyKSkge1xuICAgICAgICAgICAgICAgIHVzZU5leHRTbG90KG9sZEN1cik7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB1c2VOZXh0U2xvdChvbGRDdXIpO1xuICAgICAgICB9XG4gICAgICAgIHVzZU5leHRTbG90KG5ld0N1cik7XG4gICAgICAgIGhlYWQgPSBwb2ludGVyO1xuICAgICAgICB0YWlsID0gcG9pbnRlciAtIHNpemUgKyAxO1xuICAgICAgICBpZiAodGFpbCA8IDApIHtcbiAgICAgICAgICAgIHRhaWwgPSAwO1xuICAgICAgICB9XG4gICAgfVxuICAgIGZ1bmN0aW9uIG1vdmUoY20sIG9mZnNldCkge1xuICAgICAgICBwb2ludGVyICs9IG9mZnNldDtcbiAgICAgICAgaWYgKHBvaW50ZXIgPiBoZWFkKSB7XG4gICAgICAgICAgICBwb2ludGVyID0gaGVhZDtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChwb2ludGVyIDwgdGFpbCkge1xuICAgICAgICAgICAgcG9pbnRlciA9IHRhaWw7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIG1hcmsgPSBidWZmZXJbKHNpemUgKyBwb2ludGVyKSAlIHNpemVdO1xuICAgICAgICBpZiAobWFyayAmJiAhbWFyay5maW5kKCkpIHtcbiAgICAgICAgICAgIHZhciBpbmMgPSBvZmZzZXQgPiAwID8gMSA6IC0xO1xuICAgICAgICAgICAgdmFyIG5ld0N1cjtcbiAgICAgICAgICAgIHZhciBvbGRDdXIgPSBjbS5nZXRDdXJzb3IoKTtcbiAgICAgICAgICAgIGRvIHtcbiAgICAgICAgICAgICAgICBwb2ludGVyICs9IGluYztcbiAgICAgICAgICAgICAgICBtYXJrID0gYnVmZmVyWyhzaXplICsgcG9pbnRlcikgJSBzaXplXTtcbiAgICAgICAgICAgICAgICBpZiAobWFyayAmJlxuICAgICAgICAgICAgICAgICAgICAobmV3Q3VyID0gbWFyay5maW5kKCkpICYmXG4gICAgICAgICAgICAgICAgICAgICFjdXJzb3JFcXVhbChvbGRDdXIsIG5ld0N1cikpIHtcbiAgICAgICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfSB3aGlsZSAocG9pbnRlciA8IGhlYWQgJiYgcG9pbnRlciA+IHRhaWwpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBtYXJrO1xuICAgIH1cbiAgICBmdW5jdGlvbiBmaW5kKGNtLCBvZmZzZXQpIHtcbiAgICAgICAgdmFyIG9sZFBvaW50ZXIgPSBwb2ludGVyO1xuICAgICAgICB2YXIgbWFyayA9IG1vdmUoY20sIG9mZnNldCk7XG4gICAgICAgIHBvaW50ZXIgPSBvbGRQb2ludGVyO1xuICAgICAgICByZXR1cm4gbWFyayAmJiBtYXJrLmZpbmQoKTtcbiAgICB9XG4gICAgcmV0dXJuIHtcbiAgICAgICAgY2FjaGVkQ3Vyc29yOiB1bmRlZmluZWQsIC8vdXNlZCBmb3IgIyBhbmQgKiBqdW1wc1xuICAgICAgICBhZGQ6IGFkZCxcbiAgICAgICAgZmluZDogZmluZCxcbiAgICAgICAgbW92ZTogbW92ZVxuICAgIH07XG59O1xudmFyIGNyZWF0ZUluc2VydE1vZGVDaGFuZ2VzID0gZnVuY3Rpb24gKGMpIHtcbiAgICBpZiAoYykge1xuICAgICAgICByZXR1cm4ge1xuICAgICAgICAgICAgY2hhbmdlczogYy5jaGFuZ2VzLFxuICAgICAgICAgICAgZXhwZWN0Q3Vyc29yQWN0aXZpdHlGb3JDaGFuZ2U6IGMuZXhwZWN0Q3Vyc29yQWN0aXZpdHlGb3JDaGFuZ2VcbiAgICAgICAgfTtcbiAgICB9XG4gICAgcmV0dXJuIHtcbiAgICAgICAgY2hhbmdlczogW10sXG4gICAgICAgIGV4cGVjdEN1cnNvckFjdGl2aXR5Rm9yQ2hhbmdlOiBmYWxzZVxuICAgIH07XG59O1xuZnVuY3Rpb24gTWFjcm9Nb2RlU3RhdGUoKSB7XG4gICAgdGhpcy5sYXRlc3RSZWdpc3RlciA9IHVuZGVmaW5lZDtcbiAgICB0aGlzLmlzUGxheWluZyA9IGZhbHNlO1xuICAgIHRoaXMuaXNSZWNvcmRpbmcgPSBmYWxzZTtcbiAgICB0aGlzLnJlcGxheVNlYXJjaFF1ZXJpZXMgPSBbXTtcbiAgICB0aGlzLm9uUmVjb3JkaW5nRG9uZSA9IHVuZGVmaW5lZDtcbiAgICB0aGlzLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcyA9IGNyZWF0ZUluc2VydE1vZGVDaGFuZ2VzKCk7XG59XG5NYWNyb01vZGVTdGF0ZS5wcm90b3R5cGUgPSB7XG4gICAgZXhpdE1hY3JvUmVjb3JkTW9kZTogZnVuY3Rpb24gKCkge1xuICAgICAgICB2YXIgbWFjcm9Nb2RlU3RhdGUgPSB2aW1HbG9iYWxTdGF0ZS5tYWNyb01vZGVTdGF0ZTtcbiAgICAgICAgaWYgKG1hY3JvTW9kZVN0YXRlLm9uUmVjb3JkaW5nRG9uZSkge1xuICAgICAgICAgICAgbWFjcm9Nb2RlU3RhdGUub25SZWNvcmRpbmdEb25lKCk7IC8vIGNsb3NlIGRpYWxvZ1xuICAgICAgICB9XG4gICAgICAgIG1hY3JvTW9kZVN0YXRlLm9uUmVjb3JkaW5nRG9uZSA9IHVuZGVmaW5lZDtcbiAgICAgICAgbWFjcm9Nb2RlU3RhdGUuaXNSZWNvcmRpbmcgPSBmYWxzZTtcbiAgICB9LFxuICAgIGVudGVyTWFjcm9SZWNvcmRNb2RlOiBmdW5jdGlvbiAoY20sIHJlZ2lzdGVyTmFtZSkge1xuICAgICAgICB2YXIgcmVnaXN0ZXIgPSB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIuZ2V0UmVnaXN0ZXIocmVnaXN0ZXJOYW1lKTtcbiAgICAgICAgaWYgKHJlZ2lzdGVyKSB7XG4gICAgICAgICAgICByZWdpc3Rlci5jbGVhcigpO1xuICAgICAgICAgICAgdGhpcy5sYXRlc3RSZWdpc3RlciA9IHJlZ2lzdGVyTmFtZTtcbiAgICAgICAgICAgIGlmIChjbS5vcGVuRGlhbG9nKSB7XG4gICAgICAgICAgICAgICAgdmFyIHRlbXBsYXRlID0gZG9tKCdzcGFuJywgeyBjbGFzczogJ2NtLXZpbS1tZXNzYWdlJyB9LCAncmVjb3JkaW5nIEAnICsgcmVnaXN0ZXJOYW1lKTtcbiAgICAgICAgICAgICAgICB0aGlzLm9uUmVjb3JkaW5nRG9uZSA9IGNtLm9wZW5EaWFsb2codGVtcGxhdGUsIG51bGwsIHsgYm90dG9tOiB0cnVlIH0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdGhpcy5pc1JlY29yZGluZyA9IHRydWU7XG4gICAgICAgIH1cbiAgICB9XG59O1xuZnVuY3Rpb24gbWF5YmVJbml0VmltU3RhdGUoY20pIHtcbiAgICBpZiAoIWNtLnN0YXRlLnZpbSkge1xuICAgICAgICBjbS5zdGF0ZS52aW0gPSB7XG4gICAgICAgICAgICBpbnB1dFN0YXRlOiBuZXcgSW5wdXRTdGF0ZSgpLFxuICAgICAgICAgICAgbGFzdEVkaXRJbnB1dFN0YXRlOiB1bmRlZmluZWQsXG4gICAgICAgICAgICBsYXN0RWRpdEFjdGlvbkNvbW1hbmQ6IHVuZGVmaW5lZCxcbiAgICAgICAgICAgIGxhc3RIUG9zOiAtMSxcbiAgICAgICAgICAgIGxhc3RIU1BvczogLTEsXG4gICAgICAgICAgICBsYXN0TW90aW9uOiBudWxsLFxuICAgICAgICAgICAgbWFya3M6IHt9LFxuICAgICAgICAgICAgaW5zZXJ0TW9kZTogZmFsc2UsXG4gICAgICAgICAgICBpbnNlcnRNb2RlUmV0dXJuOiBmYWxzZSxcbiAgICAgICAgICAgIGluc2VydE1vZGVSZXBlYXQ6IHVuZGVmaW5lZCxcbiAgICAgICAgICAgIHZpc3VhbE1vZGU6IGZhbHNlLFxuICAgICAgICAgICAgdmlzdWFsTGluZTogZmFsc2UsXG4gICAgICAgICAgICB2aXN1YWxCbG9jazogZmFsc2UsXG4gICAgICAgICAgICBsYXN0U2VsZWN0aW9uOiBudWxsLFxuICAgICAgICAgICAgbGFzdFBhc3RlZFRleHQ6IG51bGwsXG4gICAgICAgICAgICBzZWw6IHt9LFxuICAgICAgICAgICAgb3B0aW9uczoge30sXG4gICAgICAgICAgICBleHBlY3RMaXRlcmFsTmV4dDogZmFsc2VcbiAgICAgICAgfTtcbiAgICB9XG4gICAgcmV0dXJuIGNtLnN0YXRlLnZpbTtcbn1cbnZhciB2aW1HbG9iYWxTdGF0ZTtcbmZ1bmN0aW9uIHJlc2V0VmltR2xvYmFsU3RhdGUoKSB7XG4gICAgdmltR2xvYmFsU3RhdGUgPSB7XG4gICAgICAgIHNlYXJjaFF1ZXJ5OiBudWxsLFxuICAgICAgICBzZWFyY2hJc1JldmVyc2VkOiBmYWxzZSxcbiAgICAgICAgbGFzdFN1YnN0aXR1dGVSZXBsYWNlUGFydDogdW5kZWZpbmVkLFxuICAgICAgICBqdW1wTGlzdDogY3JlYXRlQ2lyY3VsYXJKdW1wTGlzdCgpLFxuICAgICAgICBtYWNyb01vZGVTdGF0ZTogbmV3IE1hY3JvTW9kZVN0YXRlLFxuICAgICAgICBsYXN0Q2hhcmFjdGVyU2VhcmNoOiB7IGluY3JlbWVudDogMCwgZm9yd2FyZDogdHJ1ZSwgc2VsZWN0ZWRDaGFyYWN0ZXI6ICcnIH0sXG4gICAgICAgIHJlZ2lzdGVyQ29udHJvbGxlcjogbmV3IFJlZ2lzdGVyQ29udHJvbGxlcih7fSksXG4gICAgICAgIHNlYXJjaEhpc3RvcnlDb250cm9sbGVyOiBuZXcgSGlzdG9yeUNvbnRyb2xsZXIoKSxcbiAgICAgICAgZXhDb21tYW5kSGlzdG9yeUNvbnRyb2xsZXI6IG5ldyBIaXN0b3J5Q29udHJvbGxlcigpXG4gICAgfTtcbiAgICBmb3IgKHZhciBvcHRpb25OYW1lIGluIG9wdGlvbnMpIHtcbiAgICAgICAgdmFyIG9wdGlvbiA9IG9wdGlvbnNbb3B0aW9uTmFtZV07XG4gICAgICAgIG9wdGlvbi52YWx1ZSA9IG9wdGlvbi5kZWZhdWx0VmFsdWU7XG4gICAgfVxufVxudmFyIGxhc3RJbnNlcnRNb2RlS2V5VGltZXI7XG52YXIgdmltQXBpID0ge1xuICAgIGVudGVyVmltTW9kZTogZW50ZXJWaW1Nb2RlLFxuICAgIGxlYXZlVmltTW9kZTogbGVhdmVWaW1Nb2RlLFxuICAgIGJ1aWxkS2V5TWFwOiBmdW5jdGlvbiAoKSB7XG4gICAgfSxcbiAgICBnZXRSZWdpc3RlckNvbnRyb2xsZXI6IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlcjtcbiAgICB9LFxuICAgIHJlc2V0VmltR2xvYmFsU3RhdGVfOiByZXNldFZpbUdsb2JhbFN0YXRlLFxuICAgIGdldFZpbUdsb2JhbFN0YXRlXzogZnVuY3Rpb24gKCkge1xuICAgICAgICByZXR1cm4gdmltR2xvYmFsU3RhdGU7XG4gICAgfSxcbiAgICBtYXliZUluaXRWaW1TdGF0ZV86IG1heWJlSW5pdFZpbVN0YXRlLFxuICAgIHN1cHByZXNzRXJyb3JMb2dnaW5nOiBmYWxzZSxcbiAgICBJbnNlcnRNb2RlS2V5OiBJbnNlcnRNb2RlS2V5LFxuICAgIG1hcDogZnVuY3Rpb24gKGxocywgcmhzLCBjdHgpIHtcbiAgICAgICAgZXhDb21tYW5kRGlzcGF0Y2hlci5tYXAobGhzLCByaHMsIGN0eCk7XG4gICAgfSxcbiAgICB1bm1hcDogZnVuY3Rpb24gKGxocywgY3R4KSB7XG4gICAgICAgIHJldHVybiBleENvbW1hbmREaXNwYXRjaGVyLnVubWFwKGxocywgY3R4KTtcbiAgICB9LFxuICAgIG5vcmVtYXA6IGZ1bmN0aW9uIChsaHMsIHJocywgY3R4KSB7XG4gICAgICAgIGV4Q29tbWFuZERpc3BhdGNoZXIubWFwKGxocywgcmhzLCBjdHgsIHRydWUpO1xuICAgIH0sXG4gICAgbWFwY2xlYXI6IGZ1bmN0aW9uIChjdHgpIHtcbiAgICAgICAgdmFyIGFjdHVhbExlbmd0aCA9IGRlZmF1bHRLZXltYXAubGVuZ3RoLCBvcmlnTGVuZ3RoID0gZGVmYXVsdEtleW1hcExlbmd0aDtcbiAgICAgICAgdmFyIHVzZXJLZXltYXAgPSBkZWZhdWx0S2V5bWFwLnNsaWNlKDAsIGFjdHVhbExlbmd0aCAtIG9yaWdMZW5ndGgpO1xuICAgICAgICBkZWZhdWx0S2V5bWFwID0gZGVmYXVsdEtleW1hcC5zbGljZShhY3R1YWxMZW5ndGggLSBvcmlnTGVuZ3RoKTtcbiAgICAgICAgaWYgKGN0eCkge1xuICAgICAgICAgICAgZm9yICh2YXIgaSA9IHVzZXJLZXltYXAubGVuZ3RoIC0gMTsgaSA+PSAwOyBpLS0pIHtcbiAgICAgICAgICAgICAgICB2YXIgbWFwcGluZyA9IHVzZXJLZXltYXBbaV07XG4gICAgICAgICAgICAgICAgaWYgKGN0eCAhPT0gbWFwcGluZy5jb250ZXh0KSB7XG4gICAgICAgICAgICAgICAgICAgIGlmIChtYXBwaW5nLmNvbnRleHQpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMuX21hcENvbW1hbmQobWFwcGluZyk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICB2YXIgY29udGV4dHMgPSBbJ25vcm1hbCcsICdpbnNlcnQnLCAndmlzdWFsJ107XG4gICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHZhciBqIGluIGNvbnRleHRzKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRzW2pdICE9PSBjdHgpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFyIG5ld01hcHBpbmcgPSB7fTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZm9yICh2YXIga2V5IGluIG1hcHBpbmcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIG5ld01hcHBpbmdba2V5XSA9IG1hcHBpbmdba2V5XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBuZXdNYXBwaW5nLmNvbnRleHQgPSBjb250ZXh0c1tqXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5fbWFwQ29tbWFuZChuZXdNYXBwaW5nKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIGxhbmdtYXA6IHVwZGF0ZUxhbmdtYXAsXG4gICAgdmltS2V5RnJvbUV2ZW50OiB2aW1LZXlGcm9tRXZlbnQsXG4gICAgc2V0T3B0aW9uOiBzZXRPcHRpb24sXG4gICAgZ2V0T3B0aW9uOiBnZXRPcHRpb24sXG4gICAgZGVmaW5lT3B0aW9uOiBkZWZpbmVPcHRpb24sXG4gICAgZGVmaW5lRXg6IGZ1bmN0aW9uIChuYW1lLCBwcmVmaXgsIGZ1bmMpIHtcbiAgICAgICAgaWYgKCFwcmVmaXgpIHtcbiAgICAgICAgICAgIHByZWZpeCA9IG5hbWU7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAobmFtZS5pbmRleE9mKHByZWZpeCkgIT09IDApIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignKFZpbS5kZWZpbmVFeCkgXCInICsgcHJlZml4ICsgJ1wiIGlzIG5vdCBhIHByZWZpeCBvZiBcIicgKyBuYW1lICsgJ1wiLCBjb21tYW5kIG5vdCByZWdpc3RlcmVkJyk7XG4gICAgICAgIH1cbiAgICAgICAgZXhDb21tYW5kc1tuYW1lXSA9IGZ1bmM7XG4gICAgICAgIGV4Q29tbWFuZERpc3BhdGNoZXIuY29tbWFuZE1hcF9bcHJlZml4XSA9IHsgbmFtZTogbmFtZSwgc2hvcnROYW1lOiBwcmVmaXgsIHR5cGU6ICdhcGknIH07XG4gICAgfSxcbiAgICBoYW5kbGVLZXk6IGZ1bmN0aW9uIChjbSwga2V5LCBvcmlnaW4pIHtcbiAgICAgICAgdmFyIGNvbW1hbmQgPSB0aGlzLmZpbmRLZXkoY20sIGtleSwgb3JpZ2luKTtcbiAgICAgICAgaWYgKHR5cGVvZiBjb21tYW5kID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICByZXR1cm4gY29tbWFuZCgpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBtdWx0aVNlbGVjdEhhbmRsZUtleTogbXVsdGlTZWxlY3RIYW5kbGVLZXksXG4gICAgZmluZEtleTogZnVuY3Rpb24gKGNtLCBrZXksIG9yaWdpbikge1xuICAgICAgICB2YXIgdmltID0gbWF5YmVJbml0VmltU3RhdGUoY20pO1xuICAgICAgICBmdW5jdGlvbiBoYW5kbGVNYWNyb1JlY29yZGluZygpIHtcbiAgICAgICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICAgICAgaWYgKG1hY3JvTW9kZVN0YXRlLmlzUmVjb3JkaW5nKSB7XG4gICAgICAgICAgICAgICAgaWYgKGtleSA9PSAncScpIHtcbiAgICAgICAgICAgICAgICAgICAgbWFjcm9Nb2RlU3RhdGUuZXhpdE1hY3JvUmVjb3JkTW9kZSgpO1xuICAgICAgICAgICAgICAgICAgICBjbGVhcklucHV0U3RhdGUoY20pO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKG9yaWdpbiAhPSAnbWFwcGluZycpIHtcbiAgICAgICAgICAgICAgICAgICAgbG9nS2V5KG1hY3JvTW9kZVN0YXRlLCBrZXkpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBmdW5jdGlvbiBoYW5kbGVFc2MoKSB7XG4gICAgICAgICAgICBpZiAoa2V5ID09ICc8RXNjPicpIHtcbiAgICAgICAgICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgICAgICAgICAgZXhpdFZpc3VhbE1vZGUoY20pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmICh2aW0uaW5zZXJ0TW9kZSkge1xuICAgICAgICAgICAgICAgICAgICBleGl0SW5zZXJ0TW9kZShjbSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZnVuY3Rpb24gaGFuZGxlS2V5SW5zZXJ0TW9kZSgpIHtcbiAgICAgICAgICAgIGlmIChoYW5kbGVFc2MoKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmltLmlucHV0U3RhdGUua2V5QnVmZmVyLnB1c2goa2V5KTtcbiAgICAgICAgICAgIHZhciBrZXlzID0gdmltLmlucHV0U3RhdGUua2V5QnVmZmVyLmpvaW4oXCJcIik7XG4gICAgICAgICAgICB2YXIga2V5c0FyZUNoYXJzID0ga2V5Lmxlbmd0aCA9PSAxO1xuICAgICAgICAgICAgdmFyIG1hdGNoID0gY29tbWFuZERpc3BhdGNoZXIubWF0Y2hDb21tYW5kKGtleXMsIGRlZmF1bHRLZXltYXAsIHZpbS5pbnB1dFN0YXRlLCAnaW5zZXJ0Jyk7XG4gICAgICAgICAgICB2YXIgY2hhbmdlUXVldWUgPSB2aW0uaW5wdXRTdGF0ZS5jaGFuZ2VRdWV1ZTtcbiAgICAgICAgICAgIGlmIChtYXRjaC50eXBlID09ICdub25lJykge1xuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAobWF0Y2gudHlwZSA9PSAncGFydGlhbCcpIHtcbiAgICAgICAgICAgICAgICBpZiAobWF0Y2guZXhwZWN0TGl0ZXJhbE5leHQpXG4gICAgICAgICAgICAgICAgICAgIHZpbS5leHBlY3RMaXRlcmFsTmV4dCA9IHRydWU7XG4gICAgICAgICAgICAgICAgaWYgKGxhc3RJbnNlcnRNb2RlS2V5VGltZXIpIHtcbiAgICAgICAgICAgICAgICAgICAgd2luZG93LmNsZWFyVGltZW91dChsYXN0SW5zZXJ0TW9kZUtleVRpbWVyKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgbGFzdEluc2VydE1vZGVLZXlUaW1lciA9IGtleXNBcmVDaGFycyAmJiB3aW5kb3cuc2V0VGltZW91dChmdW5jdGlvbiAoKSB7IGlmICh2aW0uaW5zZXJ0TW9kZSAmJiB2aW0uaW5wdXRTdGF0ZS5rZXlCdWZmZXIubGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgfSB9LCBnZXRPcHRpb24oJ2luc2VydE1vZGVFc2NLZXlzVGltZW91dCcpKTtcbiAgICAgICAgICAgICAgICBpZiAoa2V5c0FyZUNoYXJzKSB7XG4gICAgICAgICAgICAgICAgICAgIHZhciBzZWxlY3Rpb25zID0gY20ubGlzdFNlbGVjdGlvbnMoKTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKCFjaGFuZ2VRdWV1ZSB8fCBjaGFuZ2VRdWV1ZS5yZW1vdmVkLmxlbmd0aCAhPSBzZWxlY3Rpb25zLmxlbmd0aClcbiAgICAgICAgICAgICAgICAgICAgICAgIGNoYW5nZVF1ZXVlID0gdmltLmlucHV0U3RhdGUuY2hhbmdlUXVldWUgPSBuZXcgQ2hhbmdlUXVldWU7XG4gICAgICAgICAgICAgICAgICAgIGNoYW5nZVF1ZXVlLmluc2VydGVkICs9IGtleTtcbiAgICAgICAgICAgICAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBzZWxlY3Rpb25zLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICB2YXIgZnJvbSA9IGN1cnNvck1pbihzZWxlY3Rpb25zW2ldLmFuY2hvciwgc2VsZWN0aW9uc1tpXS5oZWFkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHZhciB0byA9IGN1cnNvck1heChzZWxlY3Rpb25zW2ldLmFuY2hvciwgc2VsZWN0aW9uc1tpXS5oZWFkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHZhciB0ZXh0ID0gY20uZ2V0UmFuZ2UoZnJvbSwgY20uc3RhdGUub3ZlcndyaXRlID8gb2Zmc2V0Q3Vyc29yKHRvLCAwLCAxKSA6IHRvKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNoYW5nZVF1ZXVlLnJlbW92ZWRbaV0gPSAoY2hhbmdlUXVldWUucmVtb3ZlZFtpXSB8fCBcIlwiKSArIHRleHQ7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuICFrZXlzQXJlQ2hhcnM7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2aW0uZXhwZWN0TGl0ZXJhbE5leHQgPSBmYWxzZTtcbiAgICAgICAgICAgIGlmIChsYXN0SW5zZXJ0TW9kZUtleVRpbWVyKSB7XG4gICAgICAgICAgICAgICAgd2luZG93LmNsZWFyVGltZW91dChsYXN0SW5zZXJ0TW9kZUtleVRpbWVyKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChtYXRjaC5jb21tYW5kICYmIGNoYW5nZVF1ZXVlKSB7XG4gICAgICAgICAgICAgICAgdmFyIHNlbGVjdGlvbnMgPSBjbS5saXN0U2VsZWN0aW9ucygpO1xuICAgICAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgc2VsZWN0aW9ucy5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgICAgICB2YXIgaGVyZSA9IHNlbGVjdGlvbnNbaV0uaGVhZDtcbiAgICAgICAgICAgICAgICAgICAgY20ucmVwbGFjZVJhbmdlKGNoYW5nZVF1ZXVlLnJlbW92ZWRbaV0gfHwgXCJcIiwgb2Zmc2V0Q3Vyc29yKGhlcmUsIDAsIC1jaGFuZ2VRdWV1ZS5pbnNlcnRlZC5sZW5ndGgpLCBoZXJlLCAnK2lucHV0Jyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcy5jaGFuZ2VzLnBvcCgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFtYXRjaC5jb21tYW5kKVxuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICByZXR1cm4gbWF0Y2guY29tbWFuZDtcbiAgICAgICAgfVxuICAgICAgICBmdW5jdGlvbiBoYW5kbGVLZXlOb25JbnNlcnRNb2RlKCkge1xuICAgICAgICAgICAgaWYgKGhhbmRsZU1hY3JvUmVjb3JkaW5nKCkgfHwgaGFuZGxlRXNjKCkpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZpbS5pbnB1dFN0YXRlLmtleUJ1ZmZlci5wdXNoKGtleSk7XG4gICAgICAgICAgICB2YXIga2V5cyA9IHZpbS5pbnB1dFN0YXRlLmtleUJ1ZmZlci5qb2luKFwiXCIpO1xuICAgICAgICAgICAgaWYgKC9eWzEtOV1cXGQqJC8udGVzdChrZXlzKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIGtleXNNYXRjaGVyID0gL14oXFxkKikoLiopJC8uZXhlYyhrZXlzKTtcbiAgICAgICAgICAgIGlmICgha2V5c01hdGNoZXIpIHtcbiAgICAgICAgICAgICAgICBjbGVhcklucHV0U3RhdGUoY20pO1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZhciBjb250ZXh0ID0gdmltLnZpc3VhbE1vZGUgPyAndmlzdWFsJyA6XG4gICAgICAgICAgICAgICAgJ25vcm1hbCc7XG4gICAgICAgICAgICB2YXIgbWFpbktleSA9IGtleXNNYXRjaGVyWzJdIHx8IGtleXNNYXRjaGVyWzFdO1xuICAgICAgICAgICAgaWYgKHZpbS5pbnB1dFN0YXRlLm9wZXJhdG9yU2hvcnRjdXQgJiYgdmltLmlucHV0U3RhdGUub3BlcmF0b3JTaG9ydGN1dC5zbGljZSgtMSkgPT0gbWFpbktleSkge1xuICAgICAgICAgICAgICAgIG1haW5LZXkgPSB2aW0uaW5wdXRTdGF0ZS5vcGVyYXRvclNob3J0Y3V0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIG1hdGNoID0gY29tbWFuZERpc3BhdGNoZXIubWF0Y2hDb21tYW5kKG1haW5LZXksIGRlZmF1bHRLZXltYXAsIHZpbS5pbnB1dFN0YXRlLCBjb250ZXh0KTtcbiAgICAgICAgICAgIGlmIChtYXRjaC50eXBlID09ICdub25lJykge1xuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAobWF0Y2gudHlwZSA9PSAncGFydGlhbCcpIHtcbiAgICAgICAgICAgICAgICBpZiAobWF0Y2guZXhwZWN0TGl0ZXJhbE5leHQpXG4gICAgICAgICAgICAgICAgICAgIHZpbS5leHBlY3RMaXRlcmFsTmV4dCA9IHRydWU7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChtYXRjaC50eXBlID09ICdjbGVhcicpIHtcbiAgICAgICAgICAgICAgICBjbGVhcklucHV0U3RhdGUoY20pO1xuICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmltLmV4cGVjdExpdGVyYWxOZXh0ID0gZmFsc2U7XG4gICAgICAgICAgICB2aW0uaW5wdXRTdGF0ZS5rZXlCdWZmZXIubGVuZ3RoID0gMDtcbiAgICAgICAgICAgIGtleXNNYXRjaGVyID0gL14oXFxkKikoLiopJC8uZXhlYyhrZXlzKTtcbiAgICAgICAgICAgIGlmIChrZXlzTWF0Y2hlclsxXSAmJiBrZXlzTWF0Y2hlclsxXSAhPSAnMCcpIHtcbiAgICAgICAgICAgICAgICB2aW0uaW5wdXRTdGF0ZS5wdXNoUmVwZWF0RGlnaXQoa2V5c01hdGNoZXJbMV0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIG1hdGNoLmNvbW1hbmQ7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGNvbW1hbmQ7XG4gICAgICAgIGlmICh2aW0uaW5zZXJ0TW9kZSkge1xuICAgICAgICAgICAgY29tbWFuZCA9IGhhbmRsZUtleUluc2VydE1vZGUoKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGNvbW1hbmQgPSBoYW5kbGVLZXlOb25JbnNlcnRNb2RlKCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGNvbW1hbmQgPT09IGZhbHNlKSB7XG4gICAgICAgICAgICByZXR1cm4gIXZpbS5pbnNlcnRNb2RlICYmIGtleS5sZW5ndGggPT09IDEgPyBmdW5jdGlvbiAoKSB7IHJldHVybiB0cnVlOyB9IDogdW5kZWZpbmVkO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKGNvbW1hbmQgPT09IHRydWUpIHtcbiAgICAgICAgICAgIHJldHVybiBmdW5jdGlvbiAoKSB7IHJldHVybiB0cnVlOyB9O1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgICAgICBpZiAoKGNvbW1hbmQub3BlcmF0b3IgfHwgY29tbWFuZC5pc0VkaXQpICYmIGNtLmdldE9wdGlvbigncmVhZE9ubHknKSlcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuOyAvLyBhY2VfcGF0Y2hcbiAgICAgICAgICAgICAgICByZXR1cm4gY20ub3BlcmF0aW9uKGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgICAgICAgICAgY20uY3VyT3AuaXNWaW1PcCA9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29tbWFuZC50eXBlID09ICdrZXlUb0tleScpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBkb0tleVRvS2V5KGNtLCBjb21tYW5kLnRvS2V5cywgY29tbWFuZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb21tYW5kRGlzcGF0Y2hlci5wcm9jZXNzQ29tbWFuZChjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBjYXRjaCAoZSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgY20uc3RhdGUudmltID0gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgbWF5YmVJbml0VmltU3RhdGUoY20pO1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCF2aW1BcGkuc3VwcHJlc3NFcnJvckxvZ2dpbmcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb25zb2xlWydsb2cnXShlKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHRocm93IGU7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICB9O1xuICAgICAgICB9XG4gICAgfSxcbiAgICBoYW5kbGVFeDogZnVuY3Rpb24gKGNtLCBpbnB1dCkge1xuICAgICAgICBleENvbW1hbmREaXNwYXRjaGVyLnByb2Nlc3NDb21tYW5kKGNtLCBpbnB1dCk7XG4gICAgfSxcbiAgICBkZWZpbmVNb3Rpb246IGRlZmluZU1vdGlvbixcbiAgICBkZWZpbmVBY3Rpb246IGRlZmluZUFjdGlvbixcbiAgICBkZWZpbmVPcGVyYXRvcjogZGVmaW5lT3BlcmF0b3IsXG4gICAgbWFwQ29tbWFuZDogbWFwQ29tbWFuZCxcbiAgICBfbWFwQ29tbWFuZDogX21hcENvbW1hbmQsXG4gICAgZGVmaW5lUmVnaXN0ZXI6IGRlZmluZVJlZ2lzdGVyLFxuICAgIGV4aXRWaXN1YWxNb2RlOiBleGl0VmlzdWFsTW9kZSxcbiAgICBleGl0SW5zZXJ0TW9kZTogZXhpdEluc2VydE1vZGVcbn07XG52YXIga2V5VG9LZXlTdGFjayA9IFtdO1xudmFyIG5vcmVtYXAgPSBmYWxzZTtcbnZhciB2aXJ0dWFsUHJvbXB0O1xuZnVuY3Rpb24gc2VuZEtleVRvUHJvbXB0KGtleSkge1xuICAgIGlmIChrZXlbMF0gPT0gXCI8XCIpIHtcbiAgICAgICAgdmFyIGxvd2VyS2V5ID0ga2V5LnRvTG93ZXJDYXNlKCkuc2xpY2UoMSwgLTEpO1xuICAgICAgICB2YXIgcGFydHMgPSBsb3dlcktleS5zcGxpdCgnLScpO1xuICAgICAgICBsb3dlcktleSA9IHBhcnRzLnBvcCgpIHx8ICcnO1xuICAgICAgICBpZiAobG93ZXJLZXkgPT0gJ2x0JylcbiAgICAgICAgICAgIGtleSA9ICc8JztcbiAgICAgICAgZWxzZSBpZiAobG93ZXJLZXkgPT0gJ3NwYWNlJylcbiAgICAgICAgICAgIGtleSA9ICcgJztcbiAgICAgICAgZWxzZSBpZiAobG93ZXJLZXkgPT0gJ2NyJylcbiAgICAgICAgICAgIGtleSA9ICdcXG4nO1xuICAgICAgICBlbHNlIGlmICh2aW1Ub0NtS2V5TWFwW2xvd2VyS2V5XSkge1xuICAgICAgICAgICAgdmFyIHZhbHVlID0gdmlydHVhbFByb21wdC52YWx1ZTtcbiAgICAgICAgICAgIHZhciBldmVudCA9IHtcbiAgICAgICAgICAgICAgICBrZXk6IHZpbVRvQ21LZXlNYXBbbG93ZXJLZXldLFxuICAgICAgICAgICAgICAgIHRhcmdldDoge1xuICAgICAgICAgICAgICAgICAgICB2YWx1ZTogdmFsdWUsXG4gICAgICAgICAgICAgICAgICAgIHNlbGVjdGlvbkVuZDogdmFsdWUubGVuZ3RoLFxuICAgICAgICAgICAgICAgICAgICBzZWxlY3Rpb25TdGFydDogdmFsdWUubGVuZ3RoXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfTtcbiAgICAgICAgICAgIGlmICh2aXJ0dWFsUHJvbXB0Lm9uS2V5RG93bikge1xuICAgICAgICAgICAgICAgIHZpcnR1YWxQcm9tcHQub25LZXlEb3duKGV2ZW50LCB2aXJ0dWFsUHJvbXB0LnZhbHVlLCBjbG9zZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAodmlydHVhbFByb21wdCAmJiB2aXJ0dWFsUHJvbXB0Lm9uS2V5VXApIHtcbiAgICAgICAgICAgICAgICB2aXJ0dWFsUHJvbXB0Lm9uS2V5VXAoZXZlbnQsIHZpcnR1YWxQcm9tcHQudmFsdWUsIGNsb3NlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgIH1cbiAgICBpZiAoa2V5ID09ICdcXG4nKSB7XG4gICAgICAgIHZhciBwcm9tcHQgPSB2aXJ0dWFsUHJvbXB0O1xuICAgICAgICB2aXJ0dWFsUHJvbXB0ID0gbnVsbDtcbiAgICAgICAgcHJvbXB0Lm9uQ2xvc2UgJiYgcHJvbXB0Lm9uQ2xvc2UocHJvbXB0LnZhbHVlKTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIHZpcnR1YWxQcm9tcHQudmFsdWUgPSAodmlydHVhbFByb21wdC52YWx1ZSB8fCAnJykgKyBrZXk7XG4gICAgfVxuICAgIGZ1bmN0aW9uIGNsb3NlKHZhbHVlKSB7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsdWUgPT0gJ3N0cmluZycpIHtcbiAgICAgICAgICAgIHZpcnR1YWxQcm9tcHQudmFsdWUgPSB2YWx1ZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZpcnR1YWxQcm9tcHQgPSBudWxsO1xuICAgICAgICB9XG4gICAgfVxufVxuZnVuY3Rpb24gZG9LZXlUb0tleShjbSwga2V5cywgZnJvbUtleSkge1xuICAgIHZhciBub3JlbWFwQmVmb3JlID0gbm9yZW1hcDtcbiAgICBpZiAoZnJvbUtleSkge1xuICAgICAgICBpZiAoa2V5VG9LZXlTdGFjay5pbmRleE9mKGZyb21LZXkpICE9IC0xKVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICBrZXlUb0tleVN0YWNrLnB1c2goZnJvbUtleSk7XG4gICAgICAgIG5vcmVtYXAgPSBmcm9tS2V5Lm5vcmVtYXAgIT0gZmFsc2U7XG4gICAgfVxuICAgIHRyeSB7XG4gICAgICAgIHZhciB2aW0gPSBtYXliZUluaXRWaW1TdGF0ZShjbSk7XG4gICAgICAgIHZhciBrZXlSZSA9IC88KD86W0NTTUFdLSkqXFx3Kz58Li9naTtcbiAgICAgICAgdmFyIG1hdGNoO1xuICAgICAgICB3aGlsZSAoKG1hdGNoID0ga2V5UmUuZXhlYyhrZXlzKSkpIHtcbiAgICAgICAgICAgIHZhciBrZXkgPSBtYXRjaFswXTtcbiAgICAgICAgICAgIHZhciB3YXNJbnNlcnQgPSB2aW0uaW5zZXJ0TW9kZTtcbiAgICAgICAgICAgIGlmICh2aXJ0dWFsUHJvbXB0KSB7XG4gICAgICAgICAgICAgICAgc2VuZEtleVRvUHJvbXB0KGtleSk7XG4gICAgICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2YXIgcmVzdWx0ID0gdmltQXBpLmhhbmRsZUtleShjbSwga2V5LCAnbWFwcGluZycpO1xuICAgICAgICAgICAgaWYgKCFyZXN1bHQgJiYgd2FzSW5zZXJ0ICYmIHZpbS5pbnNlcnRNb2RlKSB7XG4gICAgICAgICAgICAgICAgaWYgKGtleVswXSA9PSBcIjxcIikge1xuICAgICAgICAgICAgICAgICAgICB2YXIgbG93ZXJLZXkgPSBrZXkudG9Mb3dlckNhc2UoKS5zbGljZSgxLCAtMSk7XG4gICAgICAgICAgICAgICAgICAgIHZhciBwYXJ0cyA9IGxvd2VyS2V5LnNwbGl0KCctJyk7XG4gICAgICAgICAgICAgICAgICAgIGxvd2VyS2V5ID0gcGFydHMucG9wKCkgfHwgJyc7XG4gICAgICAgICAgICAgICAgICAgIGlmIChsb3dlcktleSA9PSAnbHQnKVxuICAgICAgICAgICAgICAgICAgICAgICAga2V5ID0gJzwnO1xuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChsb3dlcktleSA9PSAnc3BhY2UnKVxuICAgICAgICAgICAgICAgICAgICAgICAga2V5ID0gJyAnO1xuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChsb3dlcktleSA9PSAnY3InKVxuICAgICAgICAgICAgICAgICAgICAgICAga2V5ID0gJ1xcbic7XG4gICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHZpbVRvQ21LZXlNYXAuaGFzT3duUHJvcGVydHkobG93ZXJLZXkpKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBrZXkgPSB2aW1Ub0NtS2V5TWFwW2xvd2VyS2V5XTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNlbmRDbUtleShjbSwga2V5KTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAga2V5ID0ga2V5WzBdO1xuICAgICAgICAgICAgICAgICAgICAgICAga2V5UmUubGFzdEluZGV4ID0gbWF0Y2guaW5kZXggKyAxO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNtLnJlcGxhY2VTZWxlY3Rpb24oa2V5KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cbiAgICBmaW5hbGx5IHtcbiAgICAgICAga2V5VG9LZXlTdGFjay5wb3AoKTtcbiAgICAgICAgbm9yZW1hcCA9IGtleVRvS2V5U3RhY2subGVuZ3RoID8gbm9yZW1hcEJlZm9yZSA6IGZhbHNlO1xuICAgICAgICBpZiAoIWtleVRvS2V5U3RhY2subGVuZ3RoICYmIHZpcnR1YWxQcm9tcHQpIHtcbiAgICAgICAgICAgIHZhciBwcm9tcHRPcHRpb25zID0gdmlydHVhbFByb21wdDtcbiAgICAgICAgICAgIHZpcnR1YWxQcm9tcHQgPSBudWxsO1xuICAgICAgICAgICAgc2hvd1Byb21wdChjbSwgcHJvbXB0T3B0aW9ucyk7XG4gICAgICAgIH1cbiAgICB9XG59XG52YXIgc3BlY2lhbEtleSA9IHtcbiAgICBSZXR1cm46ICdDUicsIEJhY2tzcGFjZTogJ0JTJywgJ0RlbGV0ZSc6ICdEZWwnLCBFc2NhcGU6ICdFc2MnLCBJbnNlcnQ6ICdJbnMnLFxuICAgIEFycm93TGVmdDogJ0xlZnQnLCBBcnJvd1JpZ2h0OiAnUmlnaHQnLCBBcnJvd1VwOiAnVXAnLCBBcnJvd0Rvd246ICdEb3duJyxcbiAgICBFbnRlcjogJ0NSJywgJyAnOiAnU3BhY2UnXG59O1xudmFyIGlnbm9yZWRLZXlzID0geyBTaGlmdDogMSwgQWx0OiAxLCBDb21tYW5kOiAxLCBDb250cm9sOiAxLFxuICAgIENhcHNMb2NrOiAxLCBBbHRHcmFwaDogMSwgRGVhZDogMSwgVW5pZGVudGlmaWVkOiAxIH07XG52YXIgdmltVG9DbUtleU1hcCA9IHt9O1xuJ0xlZnR8UmlnaHR8VXB8RG93bnxFbmR8SG9tZScuc3BsaXQoJ3wnKS5jb25jYXQoT2JqZWN0LmtleXMoc3BlY2lhbEtleSkpLmZvckVhY2goZnVuY3Rpb24gKHgpIHtcbiAgICB2aW1Ub0NtS2V5TWFwWyhzcGVjaWFsS2V5W3hdIHx8ICcnKS50b0xvd2VyQ2FzZSgpXVxuICAgICAgICA9IHZpbVRvQ21LZXlNYXBbeC50b0xvd2VyQ2FzZSgpXSA9IHg7XG59KTtcbmZ1bmN0aW9uIHZpbUtleUZyb21FdmVudChlLCB2aW0pIHtcbiAgICB2YXIga2V5ID0gZS5rZXk7XG4gICAgaWYgKGlnbm9yZWRLZXlzW2tleV0pXG4gICAgICAgIHJldHVybjtcbiAgICBpZiAoa2V5Lmxlbmd0aCA+IDEgJiYga2V5WzBdID09IFwiblwiKSB7XG4gICAgICAgIGtleSA9IGtleS5yZXBsYWNlKFwiTnVtcGFkXCIsIFwiXCIpO1xuICAgIH1cbiAgICBrZXkgPSBzcGVjaWFsS2V5W2tleV0gfHwga2V5O1xuICAgIHZhciBuYW1lID0gJyc7XG4gICAgaWYgKGUuY3RybEtleSkge1xuICAgICAgICBuYW1lICs9ICdDLSc7XG4gICAgfVxuICAgIGlmIChlLmFsdEtleSkge1xuICAgICAgICBuYW1lICs9ICdBLSc7XG4gICAgfVxuICAgIGlmIChlLm1ldGFLZXkpIHtcbiAgICAgICAgbmFtZSArPSAnTS0nO1xuICAgIH1cbiAgICBpZiAoQ29kZU1pcnJvci5pc01hYyAmJiBlLmFsdEtleSAmJiAhZS5tZXRhS2V5ICYmICFlLmN0cmxLZXkpIHtcbiAgICAgICAgbmFtZSA9IG5hbWUuc2xpY2UoMik7XG4gICAgfVxuICAgIGlmICgobmFtZSB8fCBrZXkubGVuZ3RoID4gMSkgJiYgZS5zaGlmdEtleSkge1xuICAgICAgICBuYW1lICs9ICdTLSc7XG4gICAgfVxuICAgIGlmICh2aW0gJiYgIXZpbS5leHBlY3RMaXRlcmFsTmV4dCAmJiBrZXkubGVuZ3RoID09IDEpIHtcbiAgICAgICAgaWYgKGxhbmdtYXAua2V5bWFwICYmIGtleSBpbiBsYW5nbWFwLmtleW1hcCkge1xuICAgICAgICAgICAgaWYgKGxhbmdtYXAucmVtYXBDdHJsICE9IGZhbHNlIHx8ICFuYW1lKVxuICAgICAgICAgICAgICAgIGtleSA9IGxhbmdtYXAua2V5bWFwW2tleV07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoa2V5LmNoYXJDb2RlQXQoMCkgPiAyNTUpIHtcbiAgICAgICAgICAgIHZhciBjb2RlID0gZS5jb2RlICYmIGUuY29kZS5zbGljZSgtMSkgfHwgXCJcIjtcbiAgICAgICAgICAgIGlmICghZS5zaGlmdEtleSlcbiAgICAgICAgICAgICAgICBjb2RlID0gY29kZS50b0xvd2VyQ2FzZSgpO1xuICAgICAgICAgICAgaWYgKGNvZGUpXG4gICAgICAgICAgICAgICAga2V5ID0gY29kZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBuYW1lICs9IGtleTtcbiAgICBpZiAobmFtZS5sZW5ndGggPiAxKSB7XG4gICAgICAgIG5hbWUgPSAnPCcgKyBuYW1lICsgJz4nO1xuICAgIH1cbiAgICByZXR1cm4gbmFtZTtcbn1cbjtcbmZ1bmN0aW9uIHVwZGF0ZUxhbmdtYXAobGFuZ21hcFN0cmluZywgcmVtYXBDdHJsKSB7XG4gICAgaWYgKGxhbmdtYXAuc3RyaW5nICE9PSBsYW5nbWFwU3RyaW5nKSB7XG4gICAgICAgIGxhbmdtYXAgPSBwYXJzZUxhbmdtYXAobGFuZ21hcFN0cmluZyk7XG4gICAgfVxuICAgIGxhbmdtYXAucmVtYXBDdHJsID0gcmVtYXBDdHJsO1xufVxuZnVuY3Rpb24gcGFyc2VMYW5nbWFwKGxhbmdtYXBTdHJpbmcpIHtcbiAgICB2YXIga2V5bWFwID0ge307XG4gICAgaWYgKCFsYW5nbWFwU3RyaW5nKVxuICAgICAgICByZXR1cm4geyBrZXltYXA6IGtleW1hcCwgc3RyaW5nOiAnJyB9O1xuICAgIGZ1bmN0aW9uIGdldEVzY2FwZWQobGlzdCkge1xuICAgICAgICByZXR1cm4gbGlzdC5zcGxpdCgvXFxcXD8oLikvKS5maWx0ZXIoQm9vbGVhbik7XG4gICAgfVxuICAgIGxhbmdtYXBTdHJpbmcuc3BsaXQoLygoPzpbXlxcXFwsXXxcXFxcLikrKSwvKS5tYXAoZnVuY3Rpb24gKHBhcnQpIHtcbiAgICAgICAgaWYgKCFwYXJ0KVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB2YXIgc2VtaWNvbG9uID0gcGFydC5zcGxpdCgvKCg/OlteXFxcXDtdfFxcXFwuKSspOy8pO1xuICAgICAgICBpZiAoc2VtaWNvbG9uLmxlbmd0aCA9PSAzKSB7XG4gICAgICAgICAgICB2YXIgZnJvbSA9IGdldEVzY2FwZWQoc2VtaWNvbG9uWzFdKTtcbiAgICAgICAgICAgIHZhciB0byA9IGdldEVzY2FwZWQoc2VtaWNvbG9uWzJdKTtcbiAgICAgICAgICAgIGlmIChmcm9tLmxlbmd0aCAhPT0gdG8ubGVuZ3RoKVxuICAgICAgICAgICAgICAgIHJldHVybjsgLy8gc2tpcCBvdmVyIG1hbGZvcm1lZCBwYXJ0XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGZyb20ubGVuZ3RoOyArK2kpXG4gICAgICAgICAgICAgICAga2V5bWFwW2Zyb21baV1dID0gdG9baV07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoc2VtaWNvbG9uLmxlbmd0aCA9PSAxKSB7XG4gICAgICAgICAgICB2YXIgcGFpcnMgPSBnZXRFc2NhcGVkKHBhcnQpO1xuICAgICAgICAgICAgaWYgKHBhaXJzLmxlbmd0aCAlIDIgIT09IDApXG4gICAgICAgICAgICAgICAgcmV0dXJuOyAvLyBza2lwIG92ZXIgbWFsZm9ybWVkIHBhcnRcbiAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcGFpcnMubGVuZ3RoOyBpICs9IDIpXG4gICAgICAgICAgICAgICAga2V5bWFwW3BhaXJzW2ldXSA9IHBhaXJzW2kgKyAxXTtcbiAgICAgICAgfVxuICAgIH0pO1xuICAgIHJldHVybiB7IGtleW1hcDoga2V5bWFwLCBzdHJpbmc6IGxhbmdtYXBTdHJpbmcgfTtcbn1cbmRlZmluZU9wdGlvbignbGFuZ21hcCcsIHVuZGVmaW5lZCwgJ3N0cmluZycsIFsnbG1hcCddLCBmdW5jdGlvbiAobmFtZSwgY20pIHtcbiAgICBpZiAobmFtZSA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIHJldHVybiBsYW5nbWFwLnN0cmluZztcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIHVwZGF0ZUxhbmdtYXAobmFtZSk7XG4gICAgfVxufSk7XG5mdW5jdGlvbiBJbnB1dFN0YXRlKCkge1xuICAgIHRoaXMucHJlZml4UmVwZWF0ID0gW107XG4gICAgdGhpcy5tb3Rpb25SZXBlYXQgPSBbXTtcbiAgICB0aGlzLm9wZXJhdG9yID0gbnVsbDtcbiAgICB0aGlzLm9wZXJhdG9yQXJncyA9IG51bGw7XG4gICAgdGhpcy5tb3Rpb24gPSBudWxsO1xuICAgIHRoaXMubW90aW9uQXJncyA9IG51bGw7XG4gICAgdGhpcy5rZXlCdWZmZXIgPSBbXTsgLy8gRm9yIG1hdGNoaW5nIG11bHRpLWtleSBjb21tYW5kcy5cbiAgICB0aGlzLnJlZ2lzdGVyTmFtZSA9IG51bGw7IC8vIERlZmF1bHRzIHRvIHRoZSB1bm5hbWVkIHJlZ2lzdGVyLlxuICAgIHRoaXMuY2hhbmdlUXVldWUgPSBudWxsOyAvLyBGb3IgcmVzdG9yaW5nIHRleHQgdXNlZCBieSBpbnNlcnQgbW9kZSBrZXliaW5kaW5nc1xufVxuSW5wdXRTdGF0ZS5wcm90b3R5cGUucHVzaFJlcGVhdERpZ2l0ID0gZnVuY3Rpb24gKG4pIHtcbiAgICBpZiAoIXRoaXMub3BlcmF0b3IpIHtcbiAgICAgICAgdGhpcy5wcmVmaXhSZXBlYXQgPSB0aGlzLnByZWZpeFJlcGVhdC5jb25jYXQobik7XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICB0aGlzLm1vdGlvblJlcGVhdCA9IHRoaXMubW90aW9uUmVwZWF0LmNvbmNhdChuKTtcbiAgICB9XG59O1xuSW5wdXRTdGF0ZS5wcm90b3R5cGUuZ2V0UmVwZWF0ID0gZnVuY3Rpb24gKCkge1xuICAgIHZhciByZXBlYXQgPSAwO1xuICAgIGlmICh0aGlzLnByZWZpeFJlcGVhdC5sZW5ndGggPiAwIHx8IHRoaXMubW90aW9uUmVwZWF0Lmxlbmd0aCA+IDApIHtcbiAgICAgICAgcmVwZWF0ID0gMTtcbiAgICAgICAgaWYgKHRoaXMucHJlZml4UmVwZWF0Lmxlbmd0aCA+IDApIHtcbiAgICAgICAgICAgIHJlcGVhdCAqPSBwYXJzZUludCh0aGlzLnByZWZpeFJlcGVhdC5qb2luKCcnKSwgMTApO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0aGlzLm1vdGlvblJlcGVhdC5sZW5ndGggPiAwKSB7XG4gICAgICAgICAgICByZXBlYXQgKj0gcGFyc2VJbnQodGhpcy5tb3Rpb25SZXBlYXQuam9pbignJyksIDEwKTtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmVwZWF0O1xufTtcbmZ1bmN0aW9uIGNsZWFySW5wdXRTdGF0ZShjbSwgcmVhc29uKSB7XG4gICAgY20uc3RhdGUudmltLmlucHV0U3RhdGUgPSBuZXcgSW5wdXRTdGF0ZSgpO1xuICAgIGNtLnN0YXRlLnZpbS5leHBlY3RMaXRlcmFsTmV4dCA9IGZhbHNlO1xuICAgIENvZGVNaXJyb3Iuc2lnbmFsKGNtLCAndmltLWNvbW1hbmQtZG9uZScsIHJlYXNvbik7XG59XG5mdW5jdGlvbiBDaGFuZ2VRdWV1ZSgpIHtcbiAgICB0aGlzLnJlbW92ZWQgPSBbXTtcbiAgICB0aGlzLmluc2VydGVkID0gXCJcIjtcbn1cbmZ1bmN0aW9uIFJlZ2lzdGVyKHRleHQsIGxpbmV3aXNlLCBibG9ja3dpc2UpIHtcbiAgICB0aGlzLmNsZWFyKCk7XG4gICAgdGhpcy5rZXlCdWZmZXIgPSBbdGV4dCB8fCAnJ107XG4gICAgdGhpcy5pbnNlcnRNb2RlQ2hhbmdlcyA9IFtdO1xuICAgIHRoaXMuc2VhcmNoUXVlcmllcyA9IFtdO1xuICAgIHRoaXMubGluZXdpc2UgPSAhIWxpbmV3aXNlO1xuICAgIHRoaXMuYmxvY2t3aXNlID0gISFibG9ja3dpc2U7XG59XG5SZWdpc3Rlci5wcm90b3R5cGUgPSB7XG4gICAgc2V0VGV4dDogZnVuY3Rpb24gKHRleHQsIGxpbmV3aXNlLCBibG9ja3dpc2UpIHtcbiAgICAgICAgdGhpcy5rZXlCdWZmZXIgPSBbdGV4dCB8fCAnJ107XG4gICAgICAgIHRoaXMubGluZXdpc2UgPSAhIWxpbmV3aXNlO1xuICAgICAgICB0aGlzLmJsb2Nrd2lzZSA9ICEhYmxvY2t3aXNlO1xuICAgIH0sXG4gICAgcHVzaFRleHQ6IGZ1bmN0aW9uICh0ZXh0LCBsaW5ld2lzZSkge1xuICAgICAgICBpZiAobGluZXdpc2UpIHtcbiAgICAgICAgICAgIGlmICghdGhpcy5saW5ld2lzZSkge1xuICAgICAgICAgICAgICAgIHRoaXMua2V5QnVmZmVyLnB1c2goJ1xcbicpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdGhpcy5saW5ld2lzZSA9IHRydWU7XG4gICAgICAgIH1cbiAgICAgICAgdGhpcy5rZXlCdWZmZXIucHVzaCh0ZXh0KTtcbiAgICB9LFxuICAgIHB1c2hJbnNlcnRNb2RlQ2hhbmdlczogZnVuY3Rpb24gKGNoYW5nZXMpIHtcbiAgICAgICAgdGhpcy5pbnNlcnRNb2RlQ2hhbmdlcy5wdXNoKGNyZWF0ZUluc2VydE1vZGVDaGFuZ2VzKGNoYW5nZXMpKTtcbiAgICB9LFxuICAgIHB1c2hTZWFyY2hRdWVyeTogZnVuY3Rpb24gKHF1ZXJ5KSB7XG4gICAgICAgIHRoaXMuc2VhcmNoUXVlcmllcy5wdXNoKHF1ZXJ5KTtcbiAgICB9LFxuICAgIGNsZWFyOiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHRoaXMua2V5QnVmZmVyID0gW107XG4gICAgICAgIHRoaXMuaW5zZXJ0TW9kZUNoYW5nZXMgPSBbXTtcbiAgICAgICAgdGhpcy5zZWFyY2hRdWVyaWVzID0gW107XG4gICAgICAgIHRoaXMubGluZXdpc2UgPSBmYWxzZTtcbiAgICB9LFxuICAgIHRvU3RyaW5nOiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLmtleUJ1ZmZlci5qb2luKCcnKTtcbiAgICB9XG59O1xuZnVuY3Rpb24gZGVmaW5lUmVnaXN0ZXIobmFtZSwgcmVnaXN0ZXIpIHtcbiAgICB2YXIgcmVnaXN0ZXJzID0gdmltR2xvYmFsU3RhdGUucmVnaXN0ZXJDb250cm9sbGVyLnJlZ2lzdGVycztcbiAgICBpZiAoIW5hbWUgfHwgbmFtZS5sZW5ndGggIT0gMSkge1xuICAgICAgICB0aHJvdyBFcnJvcignUmVnaXN0ZXIgbmFtZSBtdXN0IGJlIDEgY2hhcmFjdGVyJyk7XG4gICAgfVxuICAgIHJlZ2lzdGVyc1tuYW1lXSA9IHJlZ2lzdGVyO1xuICAgIHZhbGlkUmVnaXN0ZXJzLnB1c2gobmFtZSk7XG59XG5mdW5jdGlvbiBSZWdpc3RlckNvbnRyb2xsZXIocmVnaXN0ZXJzKSB7XG4gICAgdGhpcy5yZWdpc3RlcnMgPSByZWdpc3RlcnM7XG4gICAgdGhpcy51bm5hbWVkUmVnaXN0ZXIgPSByZWdpc3RlcnNbJ1wiJ10gPSBuZXcgUmVnaXN0ZXIoKTtcbiAgICByZWdpc3RlcnNbJy4nXSA9IG5ldyBSZWdpc3RlcigpO1xuICAgIHJlZ2lzdGVyc1snOiddID0gbmV3IFJlZ2lzdGVyKCk7XG4gICAgcmVnaXN0ZXJzWycvJ10gPSBuZXcgUmVnaXN0ZXIoKTtcbiAgICByZWdpc3RlcnNbJysnXSA9IG5ldyBSZWdpc3RlcigpO1xufVxuUmVnaXN0ZXJDb250cm9sbGVyLnByb3RvdHlwZSA9IHtcbiAgICBwdXNoVGV4dDogZnVuY3Rpb24gKHJlZ2lzdGVyTmFtZSwgb3BlcmF0b3IsIHRleHQsIGxpbmV3aXNlLCBibG9ja3dpc2UpIHtcbiAgICAgICAgaWYgKHJlZ2lzdGVyTmFtZSA9PT0gJ18nKVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICBpZiAobGluZXdpc2UgJiYgdGV4dC5jaGFyQXQodGV4dC5sZW5ndGggLSAxKSAhPT0gJ1xcbicpIHtcbiAgICAgICAgICAgIHRleHQgKz0gJ1xcbic7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIHJlZ2lzdGVyID0gdGhpcy5pc1ZhbGlkUmVnaXN0ZXIocmVnaXN0ZXJOYW1lKSA/XG4gICAgICAgICAgICB0aGlzLmdldFJlZ2lzdGVyKHJlZ2lzdGVyTmFtZSkgOiBudWxsO1xuICAgICAgICBpZiAoIXJlZ2lzdGVyKSB7XG4gICAgICAgICAgICBzd2l0Y2ggKG9wZXJhdG9yKSB7XG4gICAgICAgICAgICAgICAgY2FzZSAneWFuayc6XG4gICAgICAgICAgICAgICAgICAgIHRoaXMucmVnaXN0ZXJzWycwJ10gPSBuZXcgUmVnaXN0ZXIodGV4dCwgbGluZXdpc2UsIGJsb2Nrd2lzZSk7XG4gICAgICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgICAgIGNhc2UgJ2RlbGV0ZSc6XG4gICAgICAgICAgICAgICAgY2FzZSAnY2hhbmdlJzpcbiAgICAgICAgICAgICAgICAgICAgaWYgKHRleHQuaW5kZXhPZignXFxuJykgPT0gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRoaXMucmVnaXN0ZXJzWyctJ10gPSBuZXcgUmVnaXN0ZXIodGV4dCwgbGluZXdpc2UpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgdGhpcy5zaGlmdE51bWVyaWNSZWdpc3RlcnNfKCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB0aGlzLnJlZ2lzdGVyc1snMSddID0gbmV3IFJlZ2lzdGVyKHRleHQsIGxpbmV3aXNlKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHRoaXMudW5uYW1lZFJlZ2lzdGVyLnNldFRleHQodGV4dCwgbGluZXdpc2UsIGJsb2Nrd2lzZSk7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGFwcGVuZCA9IGlzVXBwZXJDYXNlKHJlZ2lzdGVyTmFtZSk7XG4gICAgICAgIGlmIChhcHBlbmQpIHtcbiAgICAgICAgICAgIHJlZ2lzdGVyLnB1c2hUZXh0KHRleHQsIGxpbmV3aXNlKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJlZ2lzdGVyLnNldFRleHQodGV4dCwgbGluZXdpc2UsIGJsb2Nrd2lzZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHJlZ2lzdGVyTmFtZSA9PT0gJysnICYmIHR5cGVvZiBuYXZpZ2F0b3IgIT09ICd1bmRlZmluZWQnICYmXG4gICAgICAgICAgICB0eXBlb2YgbmF2aWdhdG9yLmNsaXBib2FyZCAhPT0gJ3VuZGVmaW5lZCcgJiZcbiAgICAgICAgICAgIHR5cGVvZiBuYXZpZ2F0b3IuY2xpcGJvYXJkLnJlYWRUZXh0ID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICBuYXZpZ2F0b3IuY2xpcGJvYXJkLndyaXRlVGV4dCh0ZXh0KTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLnVubmFtZWRSZWdpc3Rlci5zZXRUZXh0KHJlZ2lzdGVyLnRvU3RyaW5nKCksIGxpbmV3aXNlKTtcbiAgICB9LFxuICAgIGdldFJlZ2lzdGVyOiBmdW5jdGlvbiAobmFtZSkge1xuICAgICAgICBpZiAoIXRoaXMuaXNWYWxpZFJlZ2lzdGVyKG5hbWUpKSB7XG4gICAgICAgICAgICByZXR1cm4gdGhpcy51bm5hbWVkUmVnaXN0ZXI7XG4gICAgICAgIH1cbiAgICAgICAgbmFtZSA9IG5hbWUudG9Mb3dlckNhc2UoKTtcbiAgICAgICAgaWYgKCF0aGlzLnJlZ2lzdGVyc1tuYW1lXSkge1xuICAgICAgICAgICAgdGhpcy5yZWdpc3RlcnNbbmFtZV0gPSBuZXcgUmVnaXN0ZXIoKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdGhpcy5yZWdpc3RlcnNbbmFtZV07XG4gICAgfSxcbiAgICBpc1ZhbGlkUmVnaXN0ZXI6IGZ1bmN0aW9uIChuYW1lKSB7XG4gICAgICAgIHJldHVybiBuYW1lICYmIChpbkFycmF5KG5hbWUsIHZhbGlkUmVnaXN0ZXJzKSB8fCBsYXRpbkNoYXJSZWdleC50ZXN0KG5hbWUpKTtcbiAgICB9LFxuICAgIHNoaWZ0TnVtZXJpY1JlZ2lzdGVyc186IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgZm9yICh2YXIgaSA9IDk7IGkgPj0gMjsgaS0tKSB7XG4gICAgICAgICAgICB0aGlzLnJlZ2lzdGVyc1tpXSA9IHRoaXMuZ2V0UmVnaXN0ZXIoJycgKyAoaSAtIDEpKTtcbiAgICAgICAgfVxuICAgIH1cbn07XG5mdW5jdGlvbiBIaXN0b3J5Q29udHJvbGxlcigpIHtcbiAgICB0aGlzLmhpc3RvcnlCdWZmZXIgPSBbXTtcbiAgICB0aGlzLml0ZXJhdG9yID0gMDtcbiAgICB0aGlzLmluaXRpYWxQcmVmaXggPSBudWxsO1xufVxuSGlzdG9yeUNvbnRyb2xsZXIucHJvdG90eXBlID0ge1xuICAgIG5leHRNYXRjaDogZnVuY3Rpb24gKGlucHV0LCB1cCkge1xuICAgICAgICB2YXIgaGlzdG9yeUJ1ZmZlciA9IHRoaXMuaGlzdG9yeUJ1ZmZlcjtcbiAgICAgICAgdmFyIGRpciA9IHVwID8gLTEgOiAxO1xuICAgICAgICBpZiAodGhpcy5pbml0aWFsUHJlZml4ID09PSBudWxsKVxuICAgICAgICAgICAgdGhpcy5pbml0aWFsUHJlZml4ID0gaW5wdXQ7XG4gICAgICAgIGZvciAodmFyIGkgPSB0aGlzLml0ZXJhdG9yICsgZGlyOyB1cCA/IGkgPj0gMCA6IGkgPCBoaXN0b3J5QnVmZmVyLmxlbmd0aDsgaSArPSBkaXIpIHtcbiAgICAgICAgICAgIHZhciBlbGVtZW50ID0gaGlzdG9yeUJ1ZmZlcltpXTtcbiAgICAgICAgICAgIGZvciAodmFyIGogPSAwOyBqIDw9IGVsZW1lbnQubGVuZ3RoOyBqKyspIHtcbiAgICAgICAgICAgICAgICBpZiAodGhpcy5pbml0aWFsUHJlZml4ID09IGVsZW1lbnQuc3Vic3RyaW5nKDAsIGopKSB7XG4gICAgICAgICAgICAgICAgICAgIHRoaXMuaXRlcmF0b3IgPSBpO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gZWxlbWVudDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGkgPj0gaGlzdG9yeUJ1ZmZlci5sZW5ndGgpIHtcbiAgICAgICAgICAgIHRoaXMuaXRlcmF0b3IgPSBoaXN0b3J5QnVmZmVyLmxlbmd0aDtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmluaXRpYWxQcmVmaXg7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGkgPCAwKVxuICAgICAgICAgICAgcmV0dXJuIGlucHV0O1xuICAgIH0sXG4gICAgcHVzaElucHV0OiBmdW5jdGlvbiAoaW5wdXQpIHtcbiAgICAgICAgdmFyIGluZGV4ID0gdGhpcy5oaXN0b3J5QnVmZmVyLmluZGV4T2YoaW5wdXQpO1xuICAgICAgICBpZiAoaW5kZXggPiAtMSlcbiAgICAgICAgICAgIHRoaXMuaGlzdG9yeUJ1ZmZlci5zcGxpY2UoaW5kZXgsIDEpO1xuICAgICAgICBpZiAoaW5wdXQubGVuZ3RoKVxuICAgICAgICAgICAgdGhpcy5oaXN0b3J5QnVmZmVyLnB1c2goaW5wdXQpO1xuICAgIH0sXG4gICAgcmVzZXQ6IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdGhpcy5pbml0aWFsUHJlZml4ID0gbnVsbDtcbiAgICAgICAgdGhpcy5pdGVyYXRvciA9IHRoaXMuaGlzdG9yeUJ1ZmZlci5sZW5ndGg7XG4gICAgfVxufTtcbnZhciBjb21tYW5kRGlzcGF0Y2hlciA9IHtcbiAgICBtYXRjaENvbW1hbmQ6IGZ1bmN0aW9uIChrZXlzLCBrZXlNYXAsIGlucHV0U3RhdGUsIGNvbnRleHQpIHtcbiAgICAgICAgdmFyIG1hdGNoZXMgPSBjb21tYW5kTWF0Y2hlcyhrZXlzLCBrZXlNYXAsIGNvbnRleHQsIGlucHV0U3RhdGUpO1xuICAgICAgICBpZiAoIW1hdGNoZXMuZnVsbCAmJiAhbWF0Y2hlcy5wYXJ0aWFsKSB7XG4gICAgICAgICAgICByZXR1cm4geyB0eXBlOiAnbm9uZScgfTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmICghbWF0Y2hlcy5mdWxsICYmIG1hdGNoZXMucGFydGlhbCkge1xuICAgICAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgICAgICB0eXBlOiAncGFydGlhbCcsXG4gICAgICAgICAgICAgICAgZXhwZWN0TGl0ZXJhbE5leHQ6IG1hdGNoZXMucGFydGlhbC5sZW5ndGggPT0gMSAmJiBtYXRjaGVzLnBhcnRpYWxbMF0ua2V5cy5zbGljZSgtMTEpID09ICc8Y2hhcmFjdGVyPicgLy8gbGFuZ21hcCBsaXRlcmFsIGxvZ2ljXG4gICAgICAgICAgICB9O1xuICAgICAgICB9XG4gICAgICAgIHZhciBiZXN0TWF0Y2g7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbWF0Y2hlcy5mdWxsLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgbWF0Y2ggPSBtYXRjaGVzLmZ1bGxbaV07XG4gICAgICAgICAgICBpZiAoIWJlc3RNYXRjaCkge1xuICAgICAgICAgICAgICAgIGJlc3RNYXRjaCA9IG1hdGNoO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChiZXN0TWF0Y2gua2V5cy5zbGljZSgtMTEpID09ICc8Y2hhcmFjdGVyPicgfHwgYmVzdE1hdGNoLmtleXMuc2xpY2UoLTEwKSA9PSAnPHJlZ2lzdGVyPicpIHtcbiAgICAgICAgICAgIHZhciBjaGFyYWN0ZXIgPSBsYXN0Q2hhcihrZXlzKTtcbiAgICAgICAgICAgIGlmICghY2hhcmFjdGVyIHx8IGNoYXJhY3Rlci5sZW5ndGggPiAxKVxuICAgICAgICAgICAgICAgIHJldHVybiB7IHR5cGU6ICdjbGVhcicgfTtcbiAgICAgICAgICAgIGlucHV0U3RhdGUuc2VsZWN0ZWRDaGFyYWN0ZXIgPSBjaGFyYWN0ZXI7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHsgdHlwZTogJ2Z1bGwnLCBjb21tYW5kOiBiZXN0TWF0Y2ggfTtcbiAgICB9LFxuICAgIHByb2Nlc3NDb21tYW5kOiBmdW5jdGlvbiAoY20sIHZpbSwgY29tbWFuZCkge1xuICAgICAgICB2aW0uaW5wdXRTdGF0ZS5yZXBlYXRPdmVycmlkZSA9IGNvbW1hbmQucmVwZWF0T3ZlcnJpZGU7XG4gICAgICAgIHN3aXRjaCAoY29tbWFuZC50eXBlKSB7XG4gICAgICAgICAgICBjYXNlICdtb3Rpb24nOlxuICAgICAgICAgICAgICAgIHRoaXMucHJvY2Vzc01vdGlvbihjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ29wZXJhdG9yJzpcbiAgICAgICAgICAgICAgICB0aGlzLnByb2Nlc3NPcGVyYXRvcihjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ29wZXJhdG9yTW90aW9uJzpcbiAgICAgICAgICAgICAgICB0aGlzLnByb2Nlc3NPcGVyYXRvck1vdGlvbihjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2FjdGlvbic6XG4gICAgICAgICAgICAgICAgdGhpcy5wcm9jZXNzQWN0aW9uKGNtLCB2aW0sIGNvbW1hbmQpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnc2VhcmNoJzpcbiAgICAgICAgICAgICAgICB0aGlzLnByb2Nlc3NTZWFyY2goY20sIHZpbSwgY29tbWFuZCk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdleCc6XG4gICAgICAgICAgICBjYXNlICdrZXlUb0V4JzpcbiAgICAgICAgICAgICAgICB0aGlzLnByb2Nlc3NFeChjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHByb2Nlc3NNb3Rpb246IGZ1bmN0aW9uIChjbSwgdmltLCBjb21tYW5kKSB7XG4gICAgICAgIHZpbS5pbnB1dFN0YXRlLm1vdGlvbiA9IGNvbW1hbmQubW90aW9uO1xuICAgICAgICB2aW0uaW5wdXRTdGF0ZS5tb3Rpb25BcmdzID0gY29weUFyZ3MoY29tbWFuZC5tb3Rpb25BcmdzKTtcbiAgICAgICAgdGhpcy5ldmFsSW5wdXQoY20sIHZpbSk7XG4gICAgfSxcbiAgICBwcm9jZXNzT3BlcmF0b3I6IGZ1bmN0aW9uIChjbSwgdmltLCBjb21tYW5kKSB7XG4gICAgICAgIHZhciBpbnB1dFN0YXRlID0gdmltLmlucHV0U3RhdGU7XG4gICAgICAgIGlmIChpbnB1dFN0YXRlLm9wZXJhdG9yKSB7XG4gICAgICAgICAgICBpZiAoaW5wdXRTdGF0ZS5vcGVyYXRvciA9PSBjb21tYW5kLm9wZXJhdG9yKSB7XG4gICAgICAgICAgICAgICAgaW5wdXRTdGF0ZS5tb3Rpb24gPSAnZXhwYW5kVG9MaW5lJztcbiAgICAgICAgICAgICAgICBpbnB1dFN0YXRlLm1vdGlvbkFyZ3MgPSB7IGxpbmV3aXNlOiB0cnVlIH07XG4gICAgICAgICAgICAgICAgdGhpcy5ldmFsSW5wdXQoY20sIHZpbSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgY2xlYXJJbnB1dFN0YXRlKGNtKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpbnB1dFN0YXRlLm9wZXJhdG9yID0gY29tbWFuZC5vcGVyYXRvcjtcbiAgICAgICAgaW5wdXRTdGF0ZS5vcGVyYXRvckFyZ3MgPSBjb3B5QXJncyhjb21tYW5kLm9wZXJhdG9yQXJncyk7XG4gICAgICAgIGlmIChjb21tYW5kLmtleXMubGVuZ3RoID4gMSkge1xuICAgICAgICAgICAgaW5wdXRTdGF0ZS5vcGVyYXRvclNob3J0Y3V0ID0gY29tbWFuZC5rZXlzO1xuICAgICAgICB9XG4gICAgICAgIGlmIChjb21tYW5kLmV4aXRWaXN1YWxCbG9jaykge1xuICAgICAgICAgICAgdmltLnZpc3VhbEJsb2NrID0gZmFsc2U7XG4gICAgICAgICAgICB1cGRhdGVDbVNlbGVjdGlvbihjbSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICB0aGlzLmV2YWxJbnB1dChjbSwgdmltKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgcHJvY2Vzc09wZXJhdG9yTW90aW9uOiBmdW5jdGlvbiAoY20sIHZpbSwgY29tbWFuZCkge1xuICAgICAgICB2YXIgdmlzdWFsTW9kZSA9IHZpbS52aXN1YWxNb2RlO1xuICAgICAgICB2YXIgb3BlcmF0b3JNb3Rpb25BcmdzID0gY29weUFyZ3MoY29tbWFuZC5vcGVyYXRvck1vdGlvbkFyZ3MpO1xuICAgICAgICBpZiAob3BlcmF0b3JNb3Rpb25BcmdzKSB7XG4gICAgICAgICAgICBpZiAodmlzdWFsTW9kZSAmJiBvcGVyYXRvck1vdGlvbkFyZ3MudmlzdWFsTGluZSkge1xuICAgICAgICAgICAgICAgIHZpbS52aXN1YWxMaW5lID0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICB0aGlzLnByb2Nlc3NPcGVyYXRvcihjbSwgdmltLCBjb21tYW5kKTtcbiAgICAgICAgaWYgKCF2aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICB0aGlzLnByb2Nlc3NNb3Rpb24oY20sIHZpbSwgY29tbWFuZCk7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHByb2Nlc3NBY3Rpb246IGZ1bmN0aW9uIChjbSwgdmltLCBjb21tYW5kKSB7XG4gICAgICAgIHZhciBpbnB1dFN0YXRlID0gdmltLmlucHV0U3RhdGU7XG4gICAgICAgIHZhciByZXBlYXQgPSBpbnB1dFN0YXRlLmdldFJlcGVhdCgpO1xuICAgICAgICB2YXIgcmVwZWF0SXNFeHBsaWNpdCA9ICEhcmVwZWF0O1xuICAgICAgICB2YXIgYWN0aW9uQXJncyA9IGNvcHlBcmdzKGNvbW1hbmQuYWN0aW9uQXJncykgfHwge307XG4gICAgICAgIGlmIChpbnB1dFN0YXRlLnNlbGVjdGVkQ2hhcmFjdGVyKSB7XG4gICAgICAgICAgICBhY3Rpb25BcmdzLnNlbGVjdGVkQ2hhcmFjdGVyID0gaW5wdXRTdGF0ZS5zZWxlY3RlZENoYXJhY3RlcjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoY29tbWFuZC5vcGVyYXRvcikge1xuICAgICAgICAgICAgdGhpcy5wcm9jZXNzT3BlcmF0b3IoY20sIHZpbSwgY29tbWFuZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGNvbW1hbmQubW90aW9uKSB7XG4gICAgICAgICAgICB0aGlzLnByb2Nlc3NNb3Rpb24oY20sIHZpbSwgY29tbWFuZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGNvbW1hbmQubW90aW9uIHx8IGNvbW1hbmQub3BlcmF0b3IpIHtcbiAgICAgICAgICAgIHRoaXMuZXZhbElucHV0KGNtLCB2aW0pO1xuICAgICAgICB9XG4gICAgICAgIGFjdGlvbkFyZ3MucmVwZWF0ID0gcmVwZWF0IHx8IDE7XG4gICAgICAgIGFjdGlvbkFyZ3MucmVwZWF0SXNFeHBsaWNpdCA9IHJlcGVhdElzRXhwbGljaXQ7XG4gICAgICAgIGFjdGlvbkFyZ3MucmVnaXN0ZXJOYW1lID0gaW5wdXRTdGF0ZS5yZWdpc3Rlck5hbWU7XG4gICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgIHZpbS5sYXN0TW90aW9uID0gbnVsbDtcbiAgICAgICAgaWYgKGNvbW1hbmQuaXNFZGl0KSB7XG4gICAgICAgICAgICB0aGlzLnJlY29yZExhc3RFZGl0KHZpbSwgaW5wdXRTdGF0ZSwgY29tbWFuZCk7XG4gICAgICAgIH1cbiAgICAgICAgYWN0aW9uc1tjb21tYW5kLmFjdGlvbl0oY20sIGFjdGlvbkFyZ3MsIHZpbSk7XG4gICAgfSxcbiAgICBwcm9jZXNzU2VhcmNoOiBmdW5jdGlvbiAoY20sIHZpbSwgY29tbWFuZCkge1xuICAgICAgICBpZiAoIWNtLmdldFNlYXJjaEN1cnNvcikge1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIHZhciBmb3J3YXJkID0gY29tbWFuZC5zZWFyY2hBcmdzLmZvcndhcmQ7XG4gICAgICAgIHZhciB3aG9sZVdvcmRPbmx5ID0gY29tbWFuZC5zZWFyY2hBcmdzLndob2xlV29yZE9ubHk7XG4gICAgICAgIGdldFNlYXJjaFN0YXRlKGNtKS5zZXRSZXZlcnNlZCghZm9yd2FyZCk7XG4gICAgICAgIHZhciBwcm9tcHRQcmVmaXggPSAoZm9yd2FyZCkgPyAnLycgOiAnPyc7XG4gICAgICAgIHZhciBvcmlnaW5hbFF1ZXJ5ID0gZ2V0U2VhcmNoU3RhdGUoY20pLmdldFF1ZXJ5KCk7XG4gICAgICAgIHZhciBvcmlnaW5hbFNjcm9sbFBvcyA9IGNtLmdldFNjcm9sbEluZm8oKTtcbiAgICAgICAgZnVuY3Rpb24gaGFuZGxlUXVlcnkocXVlcnksIGlnbm9yZUNhc2UsIHNtYXJ0Q2FzZSkge1xuICAgICAgICAgICAgdmltR2xvYmFsU3RhdGUuc2VhcmNoSGlzdG9yeUNvbnRyb2xsZXIucHVzaElucHV0KHF1ZXJ5KTtcbiAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLnNlYXJjaEhpc3RvcnlDb250cm9sbGVyLnJlc2V0KCk7XG4gICAgICAgICAgICB0cnkge1xuICAgICAgICAgICAgICAgIHVwZGF0ZVNlYXJjaFF1ZXJ5KGNtLCBxdWVyeSwgaWdub3JlQ2FzZSwgc21hcnRDYXNlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNhdGNoIChlKSB7XG4gICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdJbnZhbGlkIHJlZ2V4OiAnICsgcXVlcnkpO1xuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY29tbWFuZERpc3BhdGNoZXIucHJvY2Vzc01vdGlvbihjbSwgdmltLCB7XG4gICAgICAgICAgICAgICAgdHlwZTogJ21vdGlvbicsXG4gICAgICAgICAgICAgICAgbW90aW9uOiAnZmluZE5leHQnLFxuICAgICAgICAgICAgICAgIG1vdGlvbkFyZ3M6IHsgZm9yd2FyZDogdHJ1ZSwgdG9KdW1wbGlzdDogY29tbWFuZC5zZWFyY2hBcmdzLnRvSnVtcGxpc3QgfVxuICAgICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICAgICAgZnVuY3Rpb24gb25Qcm9tcHRDbG9zZShxdWVyeSkge1xuICAgICAgICAgICAgaGFuZGxlUXVlcnkocXVlcnksIHRydWUgLyoqIGlnbm9yZUNhc2UgKi8sIHRydWUgLyoqIHNtYXJ0Q2FzZSAqLyk7XG4gICAgICAgICAgICB2YXIgbWFjcm9Nb2RlU3RhdGUgPSB2aW1HbG9iYWxTdGF0ZS5tYWNyb01vZGVTdGF0ZTtcbiAgICAgICAgICAgIGlmIChtYWNyb01vZGVTdGF0ZS5pc1JlY29yZGluZykge1xuICAgICAgICAgICAgICAgIGxvZ1NlYXJjaFF1ZXJ5KG1hY3JvTW9kZVN0YXRlLCBxdWVyeSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZnVuY3Rpb24gb25Qcm9tcHRLZXlVcChlLCBxdWVyeSwgY2xvc2UpIHtcbiAgICAgICAgICAgIHZhciBrZXlOYW1lID0gdmltS2V5RnJvbUV2ZW50KGUpLCB1cCwgb2Zmc2V0O1xuICAgICAgICAgICAgaWYgKGtleU5hbWUgPT0gJzxVcD4nIHx8IGtleU5hbWUgPT0gJzxEb3duPicpIHtcbiAgICAgICAgICAgICAgICB1cCA9IGtleU5hbWUgPT0gJzxVcD4nID8gdHJ1ZSA6IGZhbHNlO1xuICAgICAgICAgICAgICAgIG9mZnNldCA9IGUudGFyZ2V0ID8gZS50YXJnZXQuc2VsZWN0aW9uRW5kIDogMDtcbiAgICAgICAgICAgICAgICBxdWVyeSA9IHZpbUdsb2JhbFN0YXRlLnNlYXJjaEhpc3RvcnlDb250cm9sbGVyLm5leHRNYXRjaChxdWVyeSwgdXApIHx8ICcnO1xuICAgICAgICAgICAgICAgIGNsb3NlKHF1ZXJ5KTtcbiAgICAgICAgICAgICAgICBpZiAob2Zmc2V0ICYmIGUudGFyZ2V0KVxuICAgICAgICAgICAgICAgICAgICBlLnRhcmdldC5zZWxlY3Rpb25FbmQgPSBlLnRhcmdldC5zZWxlY3Rpb25TdGFydCA9IE1hdGgubWluKG9mZnNldCwgZS50YXJnZXQudmFsdWUubGVuZ3RoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGtleU5hbWUgJiYga2V5TmFtZSAhPSAnPExlZnQ+JyAmJiBrZXlOYW1lICE9ICc8UmlnaHQ+Jykge1xuICAgICAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLnNlYXJjaEhpc3RvcnlDb250cm9sbGVyLnJlc2V0KCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2YXIgcGFyc2VkUXVlcnk7XG4gICAgICAgICAgICB0cnkge1xuICAgICAgICAgICAgICAgIHBhcnNlZFF1ZXJ5ID0gdXBkYXRlU2VhcmNoUXVlcnkoY20sIHF1ZXJ5LCB0cnVlIC8qKiBpZ25vcmVDYXNlICovLCB0cnVlIC8qKiBzbWFydENhc2UgKi8pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY2F0Y2ggKGUpIHtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChwYXJzZWRRdWVyeSkge1xuICAgICAgICAgICAgICAgIGNtLnNjcm9sbEludG9WaWV3KGZpbmROZXh0KGNtLCAhZm9yd2FyZCwgcGFyc2VkUXVlcnkpLCAzMCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBjbGVhclNlYXJjaEhpZ2hsaWdodChjbSk7XG4gICAgICAgICAgICAgICAgY20uc2Nyb2xsVG8ob3JpZ2luYWxTY3JvbGxQb3MubGVmdCwgb3JpZ2luYWxTY3JvbGxQb3MudG9wKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBmdW5jdGlvbiBvblByb21wdEtleURvd24oZSwgcXVlcnksIGNsb3NlKSB7XG4gICAgICAgICAgICB2YXIga2V5TmFtZSA9IHZpbUtleUZyb21FdmVudChlKTtcbiAgICAgICAgICAgIGlmIChrZXlOYW1lID09ICc8RXNjPicgfHwga2V5TmFtZSA9PSAnPEMtYz4nIHx8IGtleU5hbWUgPT0gJzxDLVs+JyB8fFxuICAgICAgICAgICAgICAgIChrZXlOYW1lID09ICc8QlM+JyAmJiBxdWVyeSA9PSAnJykpIHtcbiAgICAgICAgICAgICAgICB2aW1HbG9iYWxTdGF0ZS5zZWFyY2hIaXN0b3J5Q29udHJvbGxlci5wdXNoSW5wdXQocXVlcnkpO1xuICAgICAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLnNlYXJjaEhpc3RvcnlDb250cm9sbGVyLnJlc2V0KCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlU2VhcmNoUXVlcnkoY20sIG9yaWdpbmFsUXVlcnkpO1xuICAgICAgICAgICAgICAgIGNsZWFyU2VhcmNoSGlnaGxpZ2h0KGNtKTtcbiAgICAgICAgICAgICAgICBjbS5zY3JvbGxUbyhvcmlnaW5hbFNjcm9sbFBvcy5sZWZ0LCBvcmlnaW5hbFNjcm9sbFBvcy50b3ApO1xuICAgICAgICAgICAgICAgIENvZGVNaXJyb3IuZV9zdG9wKGUpO1xuICAgICAgICAgICAgICAgIGNsZWFySW5wdXRTdGF0ZShjbSk7XG4gICAgICAgICAgICAgICAgY2xvc2UoKTtcbiAgICAgICAgICAgICAgICBjbS5mb2N1cygpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoa2V5TmFtZSA9PSAnPFVwPicgfHwga2V5TmFtZSA9PSAnPERvd24+Jykge1xuICAgICAgICAgICAgICAgIENvZGVNaXJyb3IuZV9zdG9wKGUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoa2V5TmFtZSA9PSAnPEMtdT4nKSB7XG4gICAgICAgICAgICAgICAgQ29kZU1pcnJvci5lX3N0b3AoZSk7XG4gICAgICAgICAgICAgICAgY2xvc2UoJycpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHN3aXRjaCAoY29tbWFuZC5zZWFyY2hBcmdzLnF1ZXJ5U3JjKSB7XG4gICAgICAgICAgICBjYXNlICdwcm9tcHQnOlxuICAgICAgICAgICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICAgICAgICAgIGlmIChtYWNyb01vZGVTdGF0ZS5pc1BsYXlpbmcpIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyIHF1ZXJ5ID0gbWFjcm9Nb2RlU3RhdGUucmVwbGF5U2VhcmNoUXVlcmllcy5zaGlmdCgpO1xuICAgICAgICAgICAgICAgICAgICBoYW5kbGVRdWVyeShxdWVyeSwgdHJ1ZSAvKiogaWdub3JlQ2FzZSAqLywgZmFsc2UgLyoqIHNtYXJ0Q2FzZSAqLyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBzaG93UHJvbXB0KGNtLCB7XG4gICAgICAgICAgICAgICAgICAgICAgICBvbkNsb3NlOiBvblByb21wdENsb3NlLFxuICAgICAgICAgICAgICAgICAgICAgICAgcHJlZml4OiBwcm9tcHRQcmVmaXgsXG4gICAgICAgICAgICAgICAgICAgICAgICBkZXNjOiAnKEphdmFTY3JpcHQgcmVnZXhwKScsXG4gICAgICAgICAgICAgICAgICAgICAgICBvbktleVVwOiBvblByb21wdEtleVVwLFxuICAgICAgICAgICAgICAgICAgICAgICAgb25LZXlEb3duOiBvblByb21wdEtleURvd25cbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgY2FzZSAnd29yZFVuZGVyQ3Vyc29yJzpcbiAgICAgICAgICAgICAgICB2YXIgd29yZCA9IGV4cGFuZFdvcmRVbmRlckN1cnNvcihjbSwgeyBub1N5bWJvbDogdHJ1ZSB9KTtcbiAgICAgICAgICAgICAgICB2YXIgaXNLZXl3b3JkID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICBpZiAoIXdvcmQpIHtcbiAgICAgICAgICAgICAgICAgICAgd29yZCA9IGV4cGFuZFdvcmRVbmRlckN1cnNvcihjbSwgeyBub1N5bWJvbDogZmFsc2UgfSk7XG4gICAgICAgICAgICAgICAgICAgIGlzS2V5d29yZCA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoIXdvcmQpIHtcbiAgICAgICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdObyB3b3JkIHVuZGVyIGN1cnNvcicpO1xuICAgICAgICAgICAgICAgICAgICBjbGVhcklucHV0U3RhdGUoY20pO1xuICAgICAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHZhciBxdWVyeSA9IGNtLmdldExpbmUod29yZC5zdGFydC5saW5lKS5zdWJzdHJpbmcod29yZC5zdGFydC5jaCwgd29yZC5lbmQuY2gpO1xuICAgICAgICAgICAgICAgIGlmIChpc0tleXdvcmQgJiYgd2hvbGVXb3JkT25seSkge1xuICAgICAgICAgICAgICAgICAgICBxdWVyeSA9ICdcXFxcYicgKyBxdWVyeSArICdcXFxcYic7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBxdWVyeSA9IGVzY2FwZVJlZ2V4KHF1ZXJ5KTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmltR2xvYmFsU3RhdGUuanVtcExpc3QuY2FjaGVkQ3Vyc29yID0gY20uZ2V0Q3Vyc29yKCk7XG4gICAgICAgICAgICAgICAgY20uc2V0Q3Vyc29yKHdvcmQuc3RhcnQpO1xuICAgICAgICAgICAgICAgIGhhbmRsZVF1ZXJ5KHF1ZXJ5LCB0cnVlIC8qKiBpZ25vcmVDYXNlICovLCBmYWxzZSAvKiogc21hcnRDYXNlICovKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuICAgIH0sXG4gICAgcHJvY2Vzc0V4OiBmdW5jdGlvbiAoY20sIHZpbSwgY29tbWFuZCkge1xuICAgICAgICBmdW5jdGlvbiBvblByb21wdENsb3NlKGlucHV0KSB7XG4gICAgICAgICAgICB2aW1HbG9iYWxTdGF0ZS5leENvbW1hbmRIaXN0b3J5Q29udHJvbGxlci5wdXNoSW5wdXQoaW5wdXQpO1xuICAgICAgICAgICAgdmltR2xvYmFsU3RhdGUuZXhDb21tYW5kSGlzdG9yeUNvbnRyb2xsZXIucmVzZXQoKTtcbiAgICAgICAgICAgIGV4Q29tbWFuZERpc3BhdGNoZXIucHJvY2Vzc0NvbW1hbmQoY20sIGlucHV0KTtcbiAgICAgICAgICAgIGlmIChjbS5zdGF0ZS52aW0pXG4gICAgICAgICAgICAgICAgY2xlYXJJbnB1dFN0YXRlKGNtKTtcbiAgICAgICAgfVxuICAgICAgICBmdW5jdGlvbiBvblByb21wdEtleURvd24oZSwgaW5wdXQsIGNsb3NlKSB7XG4gICAgICAgICAgICB2YXIga2V5TmFtZSA9IHZpbUtleUZyb21FdmVudChlKSwgdXAsIG9mZnNldDtcbiAgICAgICAgICAgIGlmIChrZXlOYW1lID09ICc8RXNjPicgfHwga2V5TmFtZSA9PSAnPEMtYz4nIHx8IGtleU5hbWUgPT0gJzxDLVs+JyB8fFxuICAgICAgICAgICAgICAgIChrZXlOYW1lID09ICc8QlM+JyAmJiBpbnB1dCA9PSAnJykpIHtcbiAgICAgICAgICAgICAgICB2aW1HbG9iYWxTdGF0ZS5leENvbW1hbmRIaXN0b3J5Q29udHJvbGxlci5wdXNoSW5wdXQoaW5wdXQpO1xuICAgICAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLmV4Q29tbWFuZEhpc3RvcnlDb250cm9sbGVyLnJlc2V0KCk7XG4gICAgICAgICAgICAgICAgQ29kZU1pcnJvci5lX3N0b3AoZSk7XG4gICAgICAgICAgICAgICAgY2xlYXJJbnB1dFN0YXRlKGNtKTtcbiAgICAgICAgICAgICAgICBjbG9zZSgpO1xuICAgICAgICAgICAgICAgIGNtLmZvY3VzKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAoa2V5TmFtZSA9PSAnPFVwPicgfHwga2V5TmFtZSA9PSAnPERvd24+Jykge1xuICAgICAgICAgICAgICAgIENvZGVNaXJyb3IuZV9zdG9wKGUpO1xuICAgICAgICAgICAgICAgIHVwID0ga2V5TmFtZSA9PSAnPFVwPicgPyB0cnVlIDogZmFsc2U7XG4gICAgICAgICAgICAgICAgb2Zmc2V0ID0gZS50YXJnZXQgPyBlLnRhcmdldC5zZWxlY3Rpb25FbmQgOiAwO1xuICAgICAgICAgICAgICAgIGlucHV0ID0gdmltR2xvYmFsU3RhdGUuZXhDb21tYW5kSGlzdG9yeUNvbnRyb2xsZXIubmV4dE1hdGNoKGlucHV0LCB1cCkgfHwgJyc7XG4gICAgICAgICAgICAgICAgY2xvc2UoaW5wdXQpO1xuICAgICAgICAgICAgICAgIGlmIChvZmZzZXQgJiYgZS50YXJnZXQpXG4gICAgICAgICAgICAgICAgICAgIGUudGFyZ2V0LnNlbGVjdGlvbkVuZCA9IGUudGFyZ2V0LnNlbGVjdGlvblN0YXJ0ID0gTWF0aC5taW4ob2Zmc2V0LCBlLnRhcmdldC52YWx1ZS5sZW5ndGgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoa2V5TmFtZSA9PSAnPEMtdT4nKSB7XG4gICAgICAgICAgICAgICAgQ29kZU1pcnJvci5lX3N0b3AoZSk7XG4gICAgICAgICAgICAgICAgY2xvc2UoJycpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoa2V5TmFtZSAmJiBrZXlOYW1lICE9ICc8TGVmdD4nICYmIGtleU5hbWUgIT0gJzxSaWdodD4nKSB7XG4gICAgICAgICAgICAgICAgdmltR2xvYmFsU3RhdGUuZXhDb21tYW5kSGlzdG9yeUNvbnRyb2xsZXIucmVzZXQoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAoY29tbWFuZC50eXBlID09ICdrZXlUb0V4Jykge1xuICAgICAgICAgICAgZXhDb21tYW5kRGlzcGF0Y2hlci5wcm9jZXNzQ29tbWFuZChjbSwgY29tbWFuZC5leEFyZ3MuaW5wdXQpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICAgICAgc2hvd1Byb21wdChjbSwgeyBvbkNsb3NlOiBvblByb21wdENsb3NlLCBwcmVmaXg6ICc6JywgdmFsdWU6ICdcXCc8LFxcJz4nLFxuICAgICAgICAgICAgICAgICAgICBvbktleURvd246IG9uUHJvbXB0S2V5RG93biwgc2VsZWN0VmFsdWVPbk9wZW46IGZhbHNlIH0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgc2hvd1Byb21wdChjbSwgeyBvbkNsb3NlOiBvblByb21wdENsb3NlLCBwcmVmaXg6ICc6JyxcbiAgICAgICAgICAgICAgICAgICAgb25LZXlEb3duOiBvblByb21wdEtleURvd24gfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIGV2YWxJbnB1dDogZnVuY3Rpb24gKGNtLCB2aW0pIHtcbiAgICAgICAgdmFyIGlucHV0U3RhdGUgPSB2aW0uaW5wdXRTdGF0ZTtcbiAgICAgICAgdmFyIG1vdGlvbiA9IGlucHV0U3RhdGUubW90aW9uO1xuICAgICAgICB2YXIgbW90aW9uQXJncyA9IGlucHV0U3RhdGUubW90aW9uQXJncyB8fCB7fTtcbiAgICAgICAgdmFyIG9wZXJhdG9yID0gaW5wdXRTdGF0ZS5vcGVyYXRvcjtcbiAgICAgICAgdmFyIG9wZXJhdG9yQXJncyA9IGlucHV0U3RhdGUub3BlcmF0b3JBcmdzIHx8IHt9O1xuICAgICAgICB2YXIgcmVnaXN0ZXJOYW1lID0gaW5wdXRTdGF0ZS5yZWdpc3Rlck5hbWU7XG4gICAgICAgIHZhciBzZWwgPSB2aW0uc2VsO1xuICAgICAgICB2YXIgb3JpZ0hlYWQgPSBjb3B5Q3Vyc29yKHZpbS52aXN1YWxNb2RlID8gY2xpcEN1cnNvclRvQ29udGVudChjbSwgc2VsLmhlYWQpIDogY20uZ2V0Q3Vyc29yKCdoZWFkJykpO1xuICAgICAgICB2YXIgb3JpZ0FuY2hvciA9IGNvcHlDdXJzb3IodmltLnZpc3VhbE1vZGUgPyBjbGlwQ3Vyc29yVG9Db250ZW50KGNtLCBzZWwuYW5jaG9yKSA6IGNtLmdldEN1cnNvcignYW5jaG9yJykpO1xuICAgICAgICB2YXIgb2xkSGVhZCA9IGNvcHlDdXJzb3Iob3JpZ0hlYWQpO1xuICAgICAgICB2YXIgb2xkQW5jaG9yID0gY29weUN1cnNvcihvcmlnQW5jaG9yKTtcbiAgICAgICAgdmFyIG5ld0hlYWQsIG5ld0FuY2hvcjtcbiAgICAgICAgdmFyIHJlcGVhdDtcbiAgICAgICAgaWYgKG9wZXJhdG9yKSB7XG4gICAgICAgICAgICB0aGlzLnJlY29yZExhc3RFZGl0KHZpbSwgaW5wdXRTdGF0ZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGlucHV0U3RhdGUucmVwZWF0T3ZlcnJpZGUgIT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgcmVwZWF0ID0gaW5wdXRTdGF0ZS5yZXBlYXRPdmVycmlkZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJlcGVhdCA9IGlucHV0U3RhdGUuZ2V0UmVwZWF0KCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHJlcGVhdCA+IDAgJiYgbW90aW9uQXJncy5leHBsaWNpdFJlcGVhdCkge1xuICAgICAgICAgICAgbW90aW9uQXJncy5yZXBlYXRJc0V4cGxpY2l0ID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChtb3Rpb25BcmdzLm5vUmVwZWF0IHx8XG4gICAgICAgICAgICAoIW1vdGlvbkFyZ3MuZXhwbGljaXRSZXBlYXQgJiYgcmVwZWF0ID09PSAwKSkge1xuICAgICAgICAgICAgcmVwZWF0ID0gMTtcbiAgICAgICAgICAgIG1vdGlvbkFyZ3MucmVwZWF0SXNFeHBsaWNpdCA9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIGlmIChpbnB1dFN0YXRlLnNlbGVjdGVkQ2hhcmFjdGVyKSB7XG4gICAgICAgICAgICBtb3Rpb25BcmdzLnNlbGVjdGVkQ2hhcmFjdGVyID0gb3BlcmF0b3JBcmdzLnNlbGVjdGVkQ2hhcmFjdGVyID1cbiAgICAgICAgICAgICAgICBpbnB1dFN0YXRlLnNlbGVjdGVkQ2hhcmFjdGVyO1xuICAgICAgICB9XG4gICAgICAgIG1vdGlvbkFyZ3MucmVwZWF0ID0gcmVwZWF0O1xuICAgICAgICBjbGVhcklucHV0U3RhdGUoY20pO1xuICAgICAgICBpZiAobW90aW9uKSB7XG4gICAgICAgICAgICB2YXIgbW90aW9uUmVzdWx0ID0gbW90aW9uc1ttb3Rpb25dKGNtLCBvcmlnSGVhZCwgbW90aW9uQXJncywgdmltLCBpbnB1dFN0YXRlKTtcbiAgICAgICAgICAgIHZpbS5sYXN0TW90aW9uID0gbW90aW9uc1ttb3Rpb25dO1xuICAgICAgICAgICAgaWYgKCFtb3Rpb25SZXN1bHQpIHtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZiAobW90aW9uQXJncy50b0p1bXBsaXN0KSB7XG4gICAgICAgICAgICAgICAgaWYgKCFvcGVyYXRvciAmJiBjbS5hY2UuY3VyT3AgIT0gbnVsbClcbiAgICAgICAgICAgICAgICAgICAgY20uYWNlLmN1ck9wLmNvbW1hbmQuc2Nyb2xsSW50b1ZpZXcgPSBcImNlbnRlci1hbmltYXRlXCI7IC8vIGFjZV9wYXRjaFxuICAgICAgICAgICAgICAgIHZhciBqdW1wTGlzdCA9IHZpbUdsb2JhbFN0YXRlLmp1bXBMaXN0O1xuICAgICAgICAgICAgICAgIHZhciBjYWNoZWRDdXJzb3IgPSBqdW1wTGlzdC5jYWNoZWRDdXJzb3I7XG4gICAgICAgICAgICAgICAgaWYgKGNhY2hlZEN1cnNvcikge1xuICAgICAgICAgICAgICAgICAgICByZWNvcmRKdW1wUG9zaXRpb24oY20sIGNhY2hlZEN1cnNvciwgbW90aW9uUmVzdWx0KTtcbiAgICAgICAgICAgICAgICAgICAgZGVsZXRlIGp1bXBMaXN0LmNhY2hlZEN1cnNvcjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIHJlY29yZEp1bXBQb3NpdGlvbihjbSwgb3JpZ0hlYWQsIG1vdGlvblJlc3VsdCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKG1vdGlvblJlc3VsdCBpbnN0YW5jZW9mIEFycmF5KSB7XG4gICAgICAgICAgICAgICAgbmV3QW5jaG9yID0gbW90aW9uUmVzdWx0WzBdO1xuICAgICAgICAgICAgICAgIG5ld0hlYWQgPSBtb3Rpb25SZXN1bHRbMV07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBuZXdIZWFkID0gbW90aW9uUmVzdWx0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFuZXdIZWFkKSB7XG4gICAgICAgICAgICAgICAgbmV3SGVhZCA9IGNvcHlDdXJzb3Iob3JpZ0hlYWQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICAgICAgaWYgKCEodmltLnZpc3VhbEJsb2NrICYmIG5ld0hlYWQuY2ggPT09IEluZmluaXR5KSkge1xuICAgICAgICAgICAgICAgICAgICBuZXdIZWFkID0gY2xpcEN1cnNvclRvQ29udGVudChjbSwgbmV3SGVhZCwgb2xkSGVhZCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChuZXdBbmNob3IpIHtcbiAgICAgICAgICAgICAgICAgICAgbmV3QW5jaG9yID0gY2xpcEN1cnNvclRvQ29udGVudChjbSwgbmV3QW5jaG9yKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgbmV3QW5jaG9yID0gbmV3QW5jaG9yIHx8IG9sZEFuY2hvcjtcbiAgICAgICAgICAgICAgICBzZWwuYW5jaG9yID0gbmV3QW5jaG9yO1xuICAgICAgICAgICAgICAgIHNlbC5oZWFkID0gbmV3SGVhZDtcbiAgICAgICAgICAgICAgICB1cGRhdGVDbVNlbGVjdGlvbihjbSk7XG4gICAgICAgICAgICAgICAgdXBkYXRlTWFyayhjbSwgdmltLCAnPCcsIGN1cnNvcklzQmVmb3JlKG5ld0FuY2hvciwgbmV3SGVhZCkgPyBuZXdBbmNob3JcbiAgICAgICAgICAgICAgICAgICAgOiBuZXdIZWFkKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVNYXJrKGNtLCB2aW0sICc+JywgY3Vyc29ySXNCZWZvcmUobmV3QW5jaG9yLCBuZXdIZWFkKSA/IG5ld0hlYWRcbiAgICAgICAgICAgICAgICAgICAgOiBuZXdBbmNob3IpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoIW9wZXJhdG9yKSB7XG4gICAgICAgICAgICAgICAgaWYgKGNtLmFjZS5jdXJPcClcbiAgICAgICAgICAgICAgICAgICAgY20uYWNlLmN1ck9wLnZpbURpYWxvZ1Njcm9sbCA9IFwiY2VudGVyLWFuaW1hdGVcIjsgLy8gYWNlX3BhdGNoXG4gICAgICAgICAgICAgICAgbmV3SGVhZCA9IGNsaXBDdXJzb3JUb0NvbnRlbnQoY20sIG5ld0hlYWQsIG9sZEhlYWQpO1xuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihuZXdIZWFkLmxpbmUsIG5ld0hlYWQuY2gpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChvcGVyYXRvcikge1xuICAgICAgICAgICAgaWYgKG9wZXJhdG9yQXJncy5sYXN0U2VsKSB7XG4gICAgICAgICAgICAgICAgbmV3QW5jaG9yID0gb2xkQW5jaG9yO1xuICAgICAgICAgICAgICAgIHZhciBsYXN0U2VsID0gb3BlcmF0b3JBcmdzLmxhc3RTZWw7XG4gICAgICAgICAgICAgICAgdmFyIGxpbmVPZmZzZXQgPSBNYXRoLmFicyhsYXN0U2VsLmhlYWQubGluZSAtIGxhc3RTZWwuYW5jaG9yLmxpbmUpO1xuICAgICAgICAgICAgICAgIHZhciBjaE9mZnNldCA9IE1hdGguYWJzKGxhc3RTZWwuaGVhZC5jaCAtIGxhc3RTZWwuYW5jaG9yLmNoKTtcbiAgICAgICAgICAgICAgICBpZiAobGFzdFNlbC52aXN1YWxMaW5lKSB7XG4gICAgICAgICAgICAgICAgICAgIG5ld0hlYWQgPSBuZXcgUG9zKG9sZEFuY2hvci5saW5lICsgbGluZU9mZnNldCwgb2xkQW5jaG9yLmNoKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAobGFzdFNlbC52aXN1YWxCbG9jaykge1xuICAgICAgICAgICAgICAgICAgICBuZXdIZWFkID0gbmV3IFBvcyhvbGRBbmNob3IubGluZSArIGxpbmVPZmZzZXQsIG9sZEFuY2hvci5jaCArIGNoT2Zmc2V0KTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAobGFzdFNlbC5oZWFkLmxpbmUgPT0gbGFzdFNlbC5hbmNob3IubGluZSkge1xuICAgICAgICAgICAgICAgICAgICBuZXdIZWFkID0gbmV3IFBvcyhvbGRBbmNob3IubGluZSwgb2xkQW5jaG9yLmNoICsgY2hPZmZzZXQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgbmV3SGVhZCA9IG5ldyBQb3Mob2xkQW5jaG9yLmxpbmUgKyBsaW5lT2Zmc2V0LCBvbGRBbmNob3IuY2gpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB2aW0udmlzdWFsTW9kZSA9IHRydWU7XG4gICAgICAgICAgICAgICAgdmltLnZpc3VhbExpbmUgPSBsYXN0U2VsLnZpc3VhbExpbmU7XG4gICAgICAgICAgICAgICAgdmltLnZpc3VhbEJsb2NrID0gbGFzdFNlbC52aXN1YWxCbG9jaztcbiAgICAgICAgICAgICAgICBzZWwgPSB2aW0uc2VsID0ge1xuICAgICAgICAgICAgICAgICAgICBhbmNob3I6IG5ld0FuY2hvcixcbiAgICAgICAgICAgICAgICAgICAgaGVhZDogbmV3SGVhZFxuICAgICAgICAgICAgICAgIH07XG4gICAgICAgICAgICAgICAgdXBkYXRlQ21TZWxlY3Rpb24oY20pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgICAgICBvcGVyYXRvckFyZ3MubGFzdFNlbCA9IHtcbiAgICAgICAgICAgICAgICAgICAgYW5jaG9yOiBjb3B5Q3Vyc29yKHNlbC5hbmNob3IpLFxuICAgICAgICAgICAgICAgICAgICBoZWFkOiBjb3B5Q3Vyc29yKHNlbC5oZWFkKSxcbiAgICAgICAgICAgICAgICAgICAgdmlzdWFsQmxvY2s6IHZpbS52aXN1YWxCbG9jayxcbiAgICAgICAgICAgICAgICAgICAgdmlzdWFsTGluZTogdmltLnZpc3VhbExpbmVcbiAgICAgICAgICAgICAgICB9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIGN1clN0YXJ0LCBjdXJFbmQsIGxpbmV3aXNlLCBtb2RlO1xuICAgICAgICAgICAgdmFyIGNtU2VsO1xuICAgICAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICAgICAgY3VyU3RhcnQgPSBjdXJzb3JNaW4oc2VsLmhlYWQsIHNlbC5hbmNob3IpO1xuICAgICAgICAgICAgICAgIGN1ckVuZCA9IGN1cnNvck1heChzZWwuaGVhZCwgc2VsLmFuY2hvcik7XG4gICAgICAgICAgICAgICAgbGluZXdpc2UgPSB2aW0udmlzdWFsTGluZSB8fCBvcGVyYXRvckFyZ3MubGluZXdpc2U7XG4gICAgICAgICAgICAgICAgbW9kZSA9IHZpbS52aXN1YWxCbG9jayA/ICdibG9jaycgOlxuICAgICAgICAgICAgICAgICAgICBsaW5ld2lzZSA/ICdsaW5lJyA6XG4gICAgICAgICAgICAgICAgICAgICAgICAnY2hhcic7XG4gICAgICAgICAgICAgICAgdmFyIG5ld1Bvc2l0aW9ucyA9IHVwZGF0ZVNlbGVjdGlvbkZvclN1cnJvZ2F0ZUNoYXJhY3RlcnMoY20sIGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgICAgICAgICAgICAgIGNtU2VsID0gbWFrZUNtU2VsZWN0aW9uKGNtLCB7XG4gICAgICAgICAgICAgICAgICAgIGFuY2hvcjogbmV3UG9zaXRpb25zLnN0YXJ0LFxuICAgICAgICAgICAgICAgICAgICBoZWFkOiBuZXdQb3NpdGlvbnMuZW5kXG4gICAgICAgICAgICAgICAgfSwgbW9kZSk7XG4gICAgICAgICAgICAgICAgaWYgKGxpbmV3aXNlKSB7XG4gICAgICAgICAgICAgICAgICAgIHZhciByYW5nZXMgPSBjbVNlbC5yYW5nZXM7XG4gICAgICAgICAgICAgICAgICAgIGlmIChtb2RlID09ICdibG9jaycpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcmFuZ2VzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmFuZ2VzW2ldLmhlYWQuY2ggPSBsaW5lTGVuZ3RoKGNtLCByYW5nZXNbaV0uaGVhZC5saW5lKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChtb2RlID09ICdsaW5lJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmFuZ2VzWzBdLmhlYWQgPSBuZXcgUG9zKHJhbmdlc1swXS5oZWFkLmxpbmUgKyAxLCAwKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGN1clN0YXJ0ID0gY29weUN1cnNvcihuZXdBbmNob3IgfHwgb2xkQW5jaG9yKTtcbiAgICAgICAgICAgICAgICBjdXJFbmQgPSBjb3B5Q3Vyc29yKG5ld0hlYWQgfHwgb2xkSGVhZCk7XG4gICAgICAgICAgICAgICAgaWYgKGN1cnNvcklzQmVmb3JlKGN1ckVuZCwgY3VyU3RhcnQpKSB7XG4gICAgICAgICAgICAgICAgICAgIHZhciB0bXAgPSBjdXJTdGFydDtcbiAgICAgICAgICAgICAgICAgICAgY3VyU3RhcnQgPSBjdXJFbmQ7XG4gICAgICAgICAgICAgICAgICAgIGN1ckVuZCA9IHRtcDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgbGluZXdpc2UgPSBtb3Rpb25BcmdzLmxpbmV3aXNlIHx8IG9wZXJhdG9yQXJncy5saW5ld2lzZTtcbiAgICAgICAgICAgICAgICBpZiAobGluZXdpc2UpIHtcbiAgICAgICAgICAgICAgICAgICAgZXhwYW5kU2VsZWN0aW9uVG9MaW5lKGNtLCBjdXJTdGFydCwgY3VyRW5kKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAobW90aW9uQXJncy5mb3J3YXJkKSB7XG4gICAgICAgICAgICAgICAgICAgIGNsaXBUb0xpbmUoY20sIGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBtb2RlID0gJ2NoYXInO1xuICAgICAgICAgICAgICAgIHZhciBleGNsdXNpdmUgPSAhbW90aW9uQXJncy5pbmNsdXNpdmUgfHwgbGluZXdpc2U7XG4gICAgICAgICAgICAgICAgdmFyIG5ld1Bvc2l0aW9ucyA9IHVwZGF0ZVNlbGVjdGlvbkZvclN1cnJvZ2F0ZUNoYXJhY3RlcnMoY20sIGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgICAgICAgICAgICAgIGNtU2VsID0gbWFrZUNtU2VsZWN0aW9uKGNtLCB7XG4gICAgICAgICAgICAgICAgICAgIGFuY2hvcjogbmV3UG9zaXRpb25zLnN0YXJ0LFxuICAgICAgICAgICAgICAgICAgICBoZWFkOiBuZXdQb3NpdGlvbnMuZW5kXG4gICAgICAgICAgICAgICAgfSwgbW9kZSwgZXhjbHVzaXZlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNtLnNldFNlbGVjdGlvbnMoY21TZWwucmFuZ2VzLCBjbVNlbC5wcmltYXJ5KTtcbiAgICAgICAgICAgIHZpbS5sYXN0TW90aW9uID0gbnVsbDtcbiAgICAgICAgICAgIG9wZXJhdG9yQXJncy5yZXBlYXQgPSByZXBlYXQ7IC8vIEZvciBpbmRlbnQgaW4gdmlzdWFsIG1vZGUuXG4gICAgICAgICAgICBvcGVyYXRvckFyZ3MucmVnaXN0ZXJOYW1lID0gcmVnaXN0ZXJOYW1lO1xuICAgICAgICAgICAgb3BlcmF0b3JBcmdzLmxpbmV3aXNlID0gbGluZXdpc2U7XG4gICAgICAgICAgICB2YXIgb3BlcmF0b3JNb3ZlVG8gPSBvcGVyYXRvcnNbb3BlcmF0b3JdKGNtLCBvcGVyYXRvckFyZ3MsIGNtU2VsLnJhbmdlcywgb2xkQW5jaG9yLCBuZXdIZWFkKTtcbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgICAgIGV4aXRWaXN1YWxNb2RlKGNtLCBvcGVyYXRvck1vdmVUbyAhPSBudWxsKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChvcGVyYXRvck1vdmVUbykge1xuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihvcGVyYXRvck1vdmVUbyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHJlY29yZExhc3RFZGl0OiBmdW5jdGlvbiAodmltLCBpbnB1dFN0YXRlLCBhY3Rpb25Db21tYW5kKSB7XG4gICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICBpZiAobWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmltLmxhc3RFZGl0SW5wdXRTdGF0ZSA9IGlucHV0U3RhdGU7XG4gICAgICAgIHZpbS5sYXN0RWRpdEFjdGlvbkNvbW1hbmQgPSBhY3Rpb25Db21tYW5kO1xuICAgICAgICBtYWNyb01vZGVTdGF0ZS5sYXN0SW5zZXJ0TW9kZUNoYW5nZXMuY2hhbmdlcyA9IFtdO1xuICAgICAgICBtYWNyb01vZGVTdGF0ZS5sYXN0SW5zZXJ0TW9kZUNoYW5nZXMuZXhwZWN0Q3Vyc29yQWN0aXZpdHlGb3JDaGFuZ2UgPSBmYWxzZTtcbiAgICAgICAgbWFjcm9Nb2RlU3RhdGUubGFzdEluc2VydE1vZGVDaGFuZ2VzLnZpc3VhbEJsb2NrID0gdmltLnZpc3VhbEJsb2NrID8gdmltLnNlbC5oZWFkLmxpbmUgLSB2aW0uc2VsLmFuY2hvci5saW5lIDogMDtcbiAgICB9XG59O1xudmFyIG1vdGlvbnMgPSB7XG4gICAgbW92ZVRvVG9wTGluZTogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgbGluZSA9IGdldFVzZXJWaXNpYmxlTGluZXMoY20pLnRvcCArIG1vdGlvbkFyZ3MucmVwZWF0IC0gMTtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MobGluZSwgZmluZEZpcnN0Tm9uV2hpdGVTcGFjZUNoYXJhY3RlcihjbS5nZXRMaW5lKGxpbmUpKSk7XG4gICAgfSxcbiAgICBtb3ZlVG9NaWRkbGVMaW5lOiBmdW5jdGlvbiAoY20pIHtcbiAgICAgICAgdmFyIHJhbmdlID0gZ2V0VXNlclZpc2libGVMaW5lcyhjbSk7XG4gICAgICAgIHZhciBsaW5lID0gTWF0aC5mbG9vcigocmFuZ2UudG9wICsgcmFuZ2UuYm90dG9tKSAqIDAuNSk7XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxpbmUsIGZpbmRGaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20uZ2V0TGluZShsaW5lKSkpO1xuICAgIH0sXG4gICAgbW92ZVRvQm90dG9tTGluZTogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgbGluZSA9IGdldFVzZXJWaXNpYmxlTGluZXMoY20pLmJvdHRvbSAtIG1vdGlvbkFyZ3MucmVwZWF0ICsgMTtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MobGluZSwgZmluZEZpcnN0Tm9uV2hpdGVTcGFjZUNoYXJhY3RlcihjbS5nZXRMaW5lKGxpbmUpKSk7XG4gICAgfSxcbiAgICBleHBhbmRUb0xpbmU6IGZ1bmN0aW9uIChfY20sIGhlYWQsIG1vdGlvbkFyZ3MpIHtcbiAgICAgICAgdmFyIGN1ciA9IGhlYWQ7XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGN1ci5saW5lICsgbW90aW9uQXJncy5yZXBlYXQgLSAxLCBJbmZpbml0eSk7XG4gICAgfSxcbiAgICBmaW5kTmV4dDogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgc3RhdGUgPSBnZXRTZWFyY2hTdGF0ZShjbSk7XG4gICAgICAgIHZhciBxdWVyeSA9IHN0YXRlLmdldFF1ZXJ5KCk7XG4gICAgICAgIGlmICghcXVlcnkpIHtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgcHJldiA9ICFtb3Rpb25BcmdzLmZvcndhcmQ7XG4gICAgICAgIHByZXYgPSAoc3RhdGUuaXNSZXZlcnNlZCgpKSA/ICFwcmV2IDogcHJldjtcbiAgICAgICAgaGlnaGxpZ2h0U2VhcmNoTWF0Y2hlcyhjbSwgcXVlcnkpO1xuICAgICAgICByZXR1cm4gZmluZE5leHQoY20sIHByZXYgLyoqIHByZXYgKi8sIHF1ZXJ5LCBtb3Rpb25BcmdzLnJlcGVhdCk7XG4gICAgfSxcbiAgICBmaW5kQW5kU2VsZWN0TmV4dEluY2x1c2l2ZTogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncywgdmltLCBwcmV2SW5wdXRTdGF0ZSkge1xuICAgICAgICB2YXIgc3RhdGUgPSBnZXRTZWFyY2hTdGF0ZShjbSk7XG4gICAgICAgIHZhciBxdWVyeSA9IHN0YXRlLmdldFF1ZXJ5KCk7XG4gICAgICAgIGlmICghcXVlcnkpIHtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgcHJldiA9ICFtb3Rpb25BcmdzLmZvcndhcmQ7XG4gICAgICAgIHByZXYgPSAoc3RhdGUuaXNSZXZlcnNlZCgpKSA/ICFwcmV2IDogcHJldjtcbiAgICAgICAgdmFyIG5leHQgPSBmaW5kTmV4dEZyb21BbmRUb0luY2x1c2l2ZShjbSwgcHJldiwgcXVlcnksIG1vdGlvbkFyZ3MucmVwZWF0LCB2aW0pO1xuICAgICAgICBpZiAoIW5leHQpIHtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBpZiAocHJldklucHV0U3RhdGUub3BlcmF0b3IpIHtcbiAgICAgICAgICAgIHJldHVybiBuZXh0O1xuICAgICAgICB9XG4gICAgICAgIHZhciBmcm9tID0gbmV4dFswXTtcbiAgICAgICAgdmFyIHRvID0gbmV3IFBvcyhuZXh0WzFdLmxpbmUsIG5leHRbMV0uY2ggLSAxKTtcbiAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICBpZiAodmltLnZpc3VhbExpbmUgfHwgdmltLnZpc3VhbEJsb2NrKSB7XG4gICAgICAgICAgICAgICAgdmltLnZpc3VhbExpbmUgPSBmYWxzZTtcbiAgICAgICAgICAgICAgICB2aW0udmlzdWFsQmxvY2sgPSBmYWxzZTtcbiAgICAgICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcInZpc3VhbFwiLCBzdWJNb2RlOiBcIlwiIH0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIGFuY2hvciA9IHZpbS5zZWwuYW5jaG9yO1xuICAgICAgICAgICAgaWYgKGFuY2hvcikge1xuICAgICAgICAgICAgICAgIGlmIChzdGF0ZS5pc1JldmVyc2VkKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgaWYgKG1vdGlvbkFyZ3MuZm9yd2FyZCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIFthbmNob3IsIGZyb21dO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBbYW5jaG9yLCB0b107XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBpZiAobW90aW9uQXJncy5mb3J3YXJkKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gW2FuY2hvciwgdG9dO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBbYW5jaG9yLCBmcm9tXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2aW0udmlzdWFsTW9kZSA9IHRydWU7XG4gICAgICAgICAgICB2aW0udmlzdWFsTGluZSA9IGZhbHNlO1xuICAgICAgICAgICAgdmltLnZpc3VhbEJsb2NrID0gZmFsc2U7XG4gICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcInZpc3VhbFwiLCBzdWJNb2RlOiBcIlwiIH0pO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBwcmV2ID8gW3RvLCBmcm9tXSA6IFtmcm9tLCB0b107XG4gICAgfSxcbiAgICBnb1RvTWFyazogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciBwb3MgPSBnZXRNYXJrUG9zKGNtLCB2aW0sIG1vdGlvbkFyZ3Muc2VsZWN0ZWRDaGFyYWN0ZXIpO1xuICAgICAgICBpZiAocG9zKSB7XG4gICAgICAgICAgICByZXR1cm4gbW90aW9uQXJncy5saW5ld2lzZSA/IHsgbGluZTogcG9zLmxpbmUsIGNoOiBmaW5kRmlyc3ROb25XaGl0ZVNwYWNlQ2hhcmFjdGVyKGNtLmdldExpbmUocG9zLmxpbmUpKSB9IDogcG9zO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH0sXG4gICAgbW92ZVRvT3RoZXJIaWdobGlnaHRlZEVuZDogZnVuY3Rpb24gKGNtLCBfaGVhZCwgbW90aW9uQXJncywgdmltKSB7XG4gICAgICAgIGlmICh2aW0udmlzdWFsQmxvY2sgJiYgbW90aW9uQXJncy5zYW1lTGluZSkge1xuICAgICAgICAgICAgdmFyIHNlbCA9IHZpbS5zZWw7XG4gICAgICAgICAgICByZXR1cm4gW1xuICAgICAgICAgICAgICAgIGNsaXBDdXJzb3JUb0NvbnRlbnQoY20sIG5ldyBQb3Moc2VsLmFuY2hvci5saW5lLCBzZWwuaGVhZC5jaCkpLFxuICAgICAgICAgICAgICAgIGNsaXBDdXJzb3JUb0NvbnRlbnQoY20sIG5ldyBQb3Moc2VsLmhlYWQubGluZSwgc2VsLmFuY2hvci5jaCkpXG4gICAgICAgICAgICBdO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIChbdmltLnNlbC5oZWFkLCB2aW0uc2VsLmFuY2hvcl0pO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBqdW1wVG9NYXJrOiBmdW5jdGlvbiAoY20sIGhlYWQsIG1vdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2YXIgYmVzdCA9IGhlYWQ7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgbW90aW9uQXJncy5yZXBlYXQ7IGkrKykge1xuICAgICAgICAgICAgdmFyIGN1cnNvciA9IGJlc3Q7XG4gICAgICAgICAgICBmb3IgKHZhciBrZXkgaW4gdmltLm1hcmtzKSB7XG4gICAgICAgICAgICAgICAgaWYgKCFpc0xvd2VyQ2FzZShrZXkpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB2YXIgbWFyayA9IHZpbS5tYXJrc1trZXldLmZpbmQoKTtcbiAgICAgICAgICAgICAgICB2YXIgaXNXcm9uZ0RpcmVjdGlvbiA9IChtb3Rpb25BcmdzLmZvcndhcmQpID9cbiAgICAgICAgICAgICAgICAgICAgY3Vyc29ySXNCZWZvcmUobWFyaywgY3Vyc29yKSA6IGN1cnNvcklzQmVmb3JlKGN1cnNvciwgbWFyayk7XG4gICAgICAgICAgICAgICAgaWYgKGlzV3JvbmdEaXJlY3Rpb24pIHtcbiAgICAgICAgICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChtb3Rpb25BcmdzLmxpbmV3aXNlICYmIChtYXJrLmxpbmUgPT0gY3Vyc29yLmxpbmUpKSB7XG4gICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB2YXIgZXF1YWwgPSBjdXJzb3JFcXVhbChjdXJzb3IsIGJlc3QpO1xuICAgICAgICAgICAgICAgIHZhciBiZXR3ZWVuID0gKG1vdGlvbkFyZ3MuZm9yd2FyZCkgP1xuICAgICAgICAgICAgICAgICAgICBjdXJzb3JJc0JldHdlZW4oY3Vyc29yLCBtYXJrLCBiZXN0KSA6XG4gICAgICAgICAgICAgICAgICAgIGN1cnNvcklzQmV0d2VlbihiZXN0LCBtYXJrLCBjdXJzb3IpO1xuICAgICAgICAgICAgICAgIGlmIChlcXVhbCB8fCBiZXR3ZWVuKSB7XG4gICAgICAgICAgICAgICAgICAgIGJlc3QgPSBtYXJrO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAobW90aW9uQXJncy5saW5ld2lzZSkge1xuICAgICAgICAgICAgYmVzdCA9IG5ldyBQb3MoYmVzdC5saW5lLCBmaW5kRmlyc3ROb25XaGl0ZVNwYWNlQ2hhcmFjdGVyKGNtLmdldExpbmUoYmVzdC5saW5lKSkpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBiZXN0O1xuICAgIH0sXG4gICAgbW92ZUJ5Q2hhcmFjdGVyczogZnVuY3Rpb24gKF9jbSwgaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgY3VyID0gaGVhZDtcbiAgICAgICAgdmFyIHJlcGVhdCA9IG1vdGlvbkFyZ3MucmVwZWF0O1xuICAgICAgICB2YXIgY2ggPSBtb3Rpb25BcmdzLmZvcndhcmQgPyBjdXIuY2ggKyByZXBlYXQgOiBjdXIuY2ggLSByZXBlYXQ7XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGN1ci5saW5lLCBjaCk7XG4gICAgfSxcbiAgICBtb3ZlQnlMaW5lczogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgdmFyIGN1ciA9IGhlYWQ7XG4gICAgICAgIHZhciBlbmRDaCA9IGN1ci5jaDtcbiAgICAgICAgc3dpdGNoICh2aW0ubGFzdE1vdGlvbikge1xuICAgICAgICAgICAgY2FzZSB0aGlzLm1vdmVCeUxpbmVzOlxuICAgICAgICAgICAgY2FzZSB0aGlzLm1vdmVCeURpc3BsYXlMaW5lczpcbiAgICAgICAgICAgIGNhc2UgdGhpcy5tb3ZlQnlTY3JvbGw6XG4gICAgICAgICAgICBjYXNlIHRoaXMubW92ZVRvQ29sdW1uOlxuICAgICAgICAgICAgY2FzZSB0aGlzLm1vdmVUb0VvbDpcbiAgICAgICAgICAgICAgICBlbmRDaCA9IHZpbS5sYXN0SFBvcztcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICAgICAgdmltLmxhc3RIUG9zID0gZW5kQ2g7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIHJlcGVhdCA9IG1vdGlvbkFyZ3MucmVwZWF0ICsgKG1vdGlvbkFyZ3MucmVwZWF0T2Zmc2V0IHx8IDApO1xuICAgICAgICB2YXIgbGluZSA9IG1vdGlvbkFyZ3MuZm9yd2FyZCA/IGN1ci5saW5lICsgcmVwZWF0IDogY3VyLmxpbmUgLSByZXBlYXQ7XG4gICAgICAgIHZhciBmaXJzdCA9IGNtLmZpcnN0TGluZSgpO1xuICAgICAgICB2YXIgbGFzdCA9IGNtLmxhc3RMaW5lKCk7XG4gICAgICAgIGlmIChsaW5lIDwgZmlyc3QgJiYgY3VyLmxpbmUgPT0gZmlyc3QpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLm1vdmVUb1N0YXJ0T2ZMaW5lKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKGxpbmUgPiBsYXN0ICYmIGN1ci5saW5lID09IGxhc3QpIHtcbiAgICAgICAgICAgIHJldHVybiBtb3ZlVG9Fb2woY20sIGhlYWQsIG1vdGlvbkFyZ3MsIHZpbSwgdHJ1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGZvbGQgPSBjbS5hY2Uuc2Vzc2lvbi5nZXRGb2xkTGluZShsaW5lKTtcbiAgICAgICAgaWYgKGZvbGQpIHtcbiAgICAgICAgICAgIGlmIChtb3Rpb25BcmdzLmZvcndhcmQpIHtcbiAgICAgICAgICAgICAgICBpZiAobGluZSA+IGZvbGQuc3RhcnQucm93KVxuICAgICAgICAgICAgICAgICAgICBsaW5lID0gZm9sZC5lbmQucm93ICsgMTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGxpbmUgPSBmb2xkLnN0YXJ0LnJvdztcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAobW90aW9uQXJncy50b0ZpcnN0Q2hhcikge1xuICAgICAgICAgICAgZW5kQ2ggPSBmaW5kRmlyc3ROb25XaGl0ZVNwYWNlQ2hhcmFjdGVyKGNtLmdldExpbmUobGluZSkpO1xuICAgICAgICAgICAgdmltLmxhc3RIUG9zID0gZW5kQ2g7XG4gICAgICAgIH1cbiAgICAgICAgdmltLmxhc3RIU1BvcyA9IGNtLmNoYXJDb29yZHMobmV3IFBvcyhsaW5lLCBlbmRDaCksICdkaXYnKS5sZWZ0O1xuICAgICAgICByZXR1cm4gbmV3IFBvcyhsaW5lLCBlbmRDaCk7XG4gICAgfSxcbiAgICBtb3ZlQnlEaXNwbGF5TGluZXM6IGZ1bmN0aW9uIChjbSwgaGVhZCwgbW90aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciBjdXIgPSBoZWFkO1xuICAgICAgICBzd2l0Y2ggKHZpbS5sYXN0TW90aW9uKSB7XG4gICAgICAgICAgICBjYXNlIHRoaXMubW92ZUJ5RGlzcGxheUxpbmVzOlxuICAgICAgICAgICAgY2FzZSB0aGlzLm1vdmVCeVNjcm9sbDpcbiAgICAgICAgICAgIGNhc2UgdGhpcy5tb3ZlQnlMaW5lczpcbiAgICAgICAgICAgIGNhc2UgdGhpcy5tb3ZlVG9Db2x1bW46XG4gICAgICAgICAgICBjYXNlIHRoaXMubW92ZVRvRW9sOlxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICAgICAgICB2aW0ubGFzdEhTUG9zID0gY20uY2hhckNvb3JkcyhjdXIsICdkaXYnKS5sZWZ0O1xuICAgICAgICB9XG4gICAgICAgIHZhciByZXBlYXQgPSBtb3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgdmFyIHJlcyA9IGNtLmZpbmRQb3NWKGN1ciwgKG1vdGlvbkFyZ3MuZm9yd2FyZCA/IHJlcGVhdCA6IC1yZXBlYXQpLCAnbGluZScsIHZpbS5sYXN0SFNQb3MpO1xuICAgICAgICBpZiAocmVzLmhpdFNpZGUpIHtcbiAgICAgICAgICAgIGlmIChtb3Rpb25BcmdzLmZvcndhcmQpIHtcbiAgICAgICAgICAgICAgICB2YXIgbGFzdENoYXJDb29yZHMgPSBjbS5jaGFyQ29vcmRzKHJlcywgJ2RpdicpO1xuICAgICAgICAgICAgICAgIHZhciBnb2FsQ29vcmRzID0geyB0b3A6IGxhc3RDaGFyQ29vcmRzLnRvcCArIDgsIGxlZnQ6IHZpbS5sYXN0SFNQb3MgfTtcbiAgICAgICAgICAgICAgICB2YXIgcmVzID0gY20uY29vcmRzQ2hhcihnb2FsQ29vcmRzLCAnZGl2Jyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB2YXIgcmVzQ29vcmRzID0gY20uY2hhckNvb3JkcyhuZXcgUG9zKGNtLmZpcnN0TGluZSgpLCAwKSwgJ2RpdicpO1xuICAgICAgICAgICAgICAgIHJlc0Nvb3Jkcy5sZWZ0ID0gdmltLmxhc3RIU1BvcztcbiAgICAgICAgICAgICAgICByZXMgPSBjbS5jb29yZHNDaGFyKHJlc0Nvb3JkcywgJ2RpdicpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHZpbS5sYXN0SFBvcyA9IHJlcy5jaDtcbiAgICAgICAgcmV0dXJuIHJlcztcbiAgICB9LFxuICAgIG1vdmVCeVBhZ2U6IGZ1bmN0aW9uIChjbSwgaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgY3VyU3RhcnQgPSBoZWFkO1xuICAgICAgICB2YXIgcmVwZWF0ID0gbW90aW9uQXJncy5yZXBlYXQ7XG4gICAgICAgIHJldHVybiBjbS5maW5kUG9zVihjdXJTdGFydCwgKG1vdGlvbkFyZ3MuZm9yd2FyZCA/IHJlcGVhdCA6IC1yZXBlYXQpLCAncGFnZScpO1xuICAgIH0sXG4gICAgbW92ZUJ5UGFyYWdyYXBoOiBmdW5jdGlvbiAoY20sIGhlYWQsIG1vdGlvbkFyZ3MpIHtcbiAgICAgICAgdmFyIGRpciA9IG1vdGlvbkFyZ3MuZm9yd2FyZCA/IDEgOiAtMTtcbiAgICAgICAgcmV0dXJuIGZpbmRQYXJhZ3JhcGgoY20sIGhlYWQsIG1vdGlvbkFyZ3MucmVwZWF0LCBkaXIpO1xuICAgIH0sXG4gICAgbW92ZUJ5U2VudGVuY2U6IGZ1bmN0aW9uIChjbSwgaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgZGlyID0gbW90aW9uQXJncy5mb3J3YXJkID8gMSA6IC0xO1xuICAgICAgICByZXR1cm4gZmluZFNlbnRlbmNlKGNtLCBoZWFkLCBtb3Rpb25BcmdzLnJlcGVhdCwgZGlyKTtcbiAgICB9LFxuICAgIG1vdmVCeVNjcm9sbDogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgdmFyIHNjcm9sbGJveCA9IGNtLmdldFNjcm9sbEluZm8oKTtcbiAgICAgICAgdmFyIGN1ckVuZCA9IG51bGw7XG4gICAgICAgIHZhciByZXBlYXQgPSBtb3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgaWYgKCFyZXBlYXQpIHtcbiAgICAgICAgICAgIHJlcGVhdCA9IHNjcm9sbGJveC5jbGllbnRIZWlnaHQgLyAoMiAqIGNtLmRlZmF1bHRUZXh0SGVpZ2h0KCkpO1xuICAgICAgICB9XG4gICAgICAgIHZhciBvcmlnID0gY20uY2hhckNvb3JkcyhoZWFkLCAnbG9jYWwnKTtcbiAgICAgICAgbW90aW9uQXJncy5yZXBlYXQgPSByZXBlYXQ7XG4gICAgICAgIGN1ckVuZCA9IG1vdGlvbnMubW92ZUJ5RGlzcGxheUxpbmVzKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pO1xuICAgICAgICBpZiAoIWN1ckVuZCkge1xuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGRlc3QgPSBjbS5jaGFyQ29vcmRzKGN1ckVuZCwgJ2xvY2FsJyk7XG4gICAgICAgIGNtLnNjcm9sbFRvKG51bGwsIHNjcm9sbGJveC50b3AgKyBkZXN0LnRvcCAtIG9yaWcudG9wKTtcbiAgICAgICAgcmV0dXJuIGN1ckVuZDtcbiAgICB9LFxuICAgIG1vdmVCeVdvcmRzOiBmdW5jdGlvbiAoY20sIGhlYWQsIG1vdGlvbkFyZ3MpIHtcbiAgICAgICAgcmV0dXJuIG1vdmVUb1dvcmQoY20sIGhlYWQsIG1vdGlvbkFyZ3MucmVwZWF0LCAhIW1vdGlvbkFyZ3MuZm9yd2FyZCwgISFtb3Rpb25BcmdzLndvcmRFbmQsICEhbW90aW9uQXJncy5iaWdXb3JkKTtcbiAgICB9LFxuICAgIG1vdmVUaWxsQ2hhcmFjdGVyOiBmdW5jdGlvbiAoY20sIGhlYWQsIG1vdGlvbkFyZ3MpIHtcbiAgICAgICAgdmFyIHJlcGVhdCA9IG1vdGlvbkFyZ3MucmVwZWF0O1xuICAgICAgICB2YXIgY3VyRW5kID0gbW92ZVRvQ2hhcmFjdGVyKGNtLCByZXBlYXQsIG1vdGlvbkFyZ3MuZm9yd2FyZCwgbW90aW9uQXJncy5zZWxlY3RlZENoYXJhY3RlciwgaGVhZCk7XG4gICAgICAgIHZhciBpbmNyZW1lbnQgPSBtb3Rpb25BcmdzLmZvcndhcmQgPyAtMSA6IDE7XG4gICAgICAgIHJlY29yZExhc3RDaGFyYWN0ZXJTZWFyY2goaW5jcmVtZW50LCBtb3Rpb25BcmdzKTtcbiAgICAgICAgaWYgKCFjdXJFbmQpXG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgY3VyRW5kLmNoICs9IGluY3JlbWVudDtcbiAgICAgICAgcmV0dXJuIGN1ckVuZDtcbiAgICB9LFxuICAgIG1vdmVUb0NoYXJhY3RlcjogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzKSB7XG4gICAgICAgIHZhciByZXBlYXQgPSBtb3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgcmVjb3JkTGFzdENoYXJhY3RlclNlYXJjaCgwLCBtb3Rpb25BcmdzKTtcbiAgICAgICAgcmV0dXJuIG1vdmVUb0NoYXJhY3RlcihjbSwgcmVwZWF0LCBtb3Rpb25BcmdzLmZvcndhcmQsIG1vdGlvbkFyZ3Muc2VsZWN0ZWRDaGFyYWN0ZXIsIGhlYWQpIHx8IGhlYWQ7XG4gICAgfSxcbiAgICBtb3ZlVG9TeW1ib2w6IGZ1bmN0aW9uIChjbSwgaGVhZCwgbW90aW9uQXJncykge1xuICAgICAgICB2YXIgcmVwZWF0ID0gbW90aW9uQXJncy5yZXBlYXQ7XG4gICAgICAgIHJldHVybiBmaW5kU3ltYm9sKGNtLCByZXBlYXQsIG1vdGlvbkFyZ3MuZm9yd2FyZCwgbW90aW9uQXJncy5zZWxlY3RlZENoYXJhY3RlcikgfHwgaGVhZDtcbiAgICB9LFxuICAgIG1vdmVUb0NvbHVtbjogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgdmFyIHJlcGVhdCA9IG1vdGlvbkFyZ3MucmVwZWF0O1xuICAgICAgICB2aW0ubGFzdEhQb3MgPSByZXBlYXQgLSAxO1xuICAgICAgICB2aW0ubGFzdEhTUG9zID0gY20uY2hhckNvb3JkcyhoZWFkLCAnZGl2JykubGVmdDtcbiAgICAgICAgcmV0dXJuIG1vdmVUb0NvbHVtbihjbSwgcmVwZWF0KTtcbiAgICB9LFxuICAgIG1vdmVUb0VvbDogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgcmV0dXJuIG1vdmVUb0VvbChjbSwgaGVhZCwgbW90aW9uQXJncywgdmltLCBmYWxzZSk7XG4gICAgfSxcbiAgICBtb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXI6IGZ1bmN0aW9uIChjbSwgaGVhZCkge1xuICAgICAgICB2YXIgY3Vyc29yID0gaGVhZDtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MoY3Vyc29yLmxpbmUsIGZpbmRGaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20uZ2V0TGluZShjdXJzb3IubGluZSkpKTtcbiAgICB9LFxuICAgIG1vdmVUb01hdGNoZWRTeW1ib2w6IGZ1bmN0aW9uIChjbSwgaGVhZCkge1xuICAgICAgICB2YXIgY3Vyc29yID0gaGVhZDtcbiAgICAgICAgdmFyIGxpbmUgPSBjdXJzb3IubGluZTtcbiAgICAgICAgdmFyIGNoID0gY3Vyc29yLmNoO1xuICAgICAgICB2YXIgbGluZVRleHQgPSBjbS5nZXRMaW5lKGxpbmUpO1xuICAgICAgICB2YXIgc3ltYm9sO1xuICAgICAgICBmb3IgKDsgY2ggPCBsaW5lVGV4dC5sZW5ndGg7IGNoKyspIHtcbiAgICAgICAgICAgIHN5bWJvbCA9IGxpbmVUZXh0LmNoYXJBdChjaCk7XG4gICAgICAgICAgICBpZiAoc3ltYm9sICYmIGlzTWF0Y2hhYmxlU3ltYm9sKHN5bWJvbCkpIHtcbiAgICAgICAgICAgICAgICB2YXIgc3R5bGUgPSBjbS5nZXRUb2tlblR5cGVBdChuZXcgUG9zKGxpbmUsIGNoICsgMSkpO1xuICAgICAgICAgICAgICAgIGlmIChzdHlsZSAhPT0gXCJzdHJpbmdcIiAmJiBzdHlsZSAhPT0gXCJjb21tZW50XCIpIHtcbiAgICAgICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChjaCA8IGxpbmVUZXh0Lmxlbmd0aCkge1xuICAgICAgICAgICAgdmFyIHJlID0gL1s8Pl0vLnRlc3QobGluZVRleHRbY2hdKSA/IC9bKCl7fVtcXF08Pl0vIDogL1soKXt9W1xcXV0vOyAvL2FjZV9wYXRjaD9cbiAgICAgICAgICAgIHZhciBtYXRjaGVkID0gY20uZmluZE1hdGNoaW5nQnJhY2tldChuZXcgUG9zKGxpbmUsIGNoICsgMSksIHsgYnJhY2tldFJlZ2V4OiByZSB9KTtcbiAgICAgICAgICAgIHJldHVybiBtYXRjaGVkLnRvO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgcmV0dXJuIGN1cnNvcjtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgbW92ZVRvU3RhcnRPZkxpbmU6IGZ1bmN0aW9uIChfY20sIGhlYWQpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MoaGVhZC5saW5lLCAwKTtcbiAgICB9LFxuICAgIG1vdmVUb0xpbmVPckVkZ2VPZkRvY3VtZW50OiBmdW5jdGlvbiAoY20sIF9oZWFkLCBtb3Rpb25BcmdzKSB7XG4gICAgICAgIHZhciBsaW5lTnVtID0gbW90aW9uQXJncy5mb3J3YXJkID8gY20ubGFzdExpbmUoKSA6IGNtLmZpcnN0TGluZSgpO1xuICAgICAgICBpZiAobW90aW9uQXJncy5yZXBlYXRJc0V4cGxpY2l0KSB7XG4gICAgICAgICAgICBsaW5lTnVtID0gbW90aW9uQXJncy5yZXBlYXQgLSBjbS5nZXRPcHRpb24oJ2ZpcnN0TGluZU51bWJlcicpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxpbmVOdW0sIGZpbmRGaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20uZ2V0TGluZShsaW5lTnVtKSkpO1xuICAgIH0sXG4gICAgbW92ZVRvU3RhcnRPZkRpc3BsYXlMaW5lOiBmdW5jdGlvbiAoY20pIHtcbiAgICAgICAgY20uZXhlY0NvbW1hbmQoXCJnb0xpbmVMZWZ0XCIpO1xuICAgICAgICByZXR1cm4gY20uZ2V0Q3Vyc29yKCk7XG4gICAgfSxcbiAgICBtb3ZlVG9FbmRPZkRpc3BsYXlMaW5lOiBmdW5jdGlvbiAoY20pIHtcbiAgICAgICAgY20uZXhlY0NvbW1hbmQoXCJnb0xpbmVSaWdodFwiKTtcbiAgICAgICAgdmFyIGhlYWQgPSBjbS5nZXRDdXJzb3IoKTtcbiAgICAgICAgaWYgKGhlYWQuc3RpY2t5ID09IFwiYmVmb3JlXCIpXG4gICAgICAgICAgICBoZWFkLmNoLS07XG4gICAgICAgIHJldHVybiBoZWFkO1xuICAgIH0sXG4gICAgdGV4dE9iamVjdE1hbmlwdWxhdGlvbjogZnVuY3Rpb24gKGNtLCBoZWFkLCBtb3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgdmFyIG1pcnJvcmVkUGFpcnMgPSB7ICcoJzogJyknLCAnKSc6ICcoJyxcbiAgICAgICAgICAgICd7JzogJ30nLCAnfSc6ICd7JyxcbiAgICAgICAgICAgICdbJzogJ10nLCAnXSc6ICdbJyxcbiAgICAgICAgICAgICc8JzogJz4nLCAnPic6ICc8JyB9O1xuICAgICAgICB2YXIgc2VsZlBhaXJlZCA9IHsgJ1xcJyc6IHRydWUsICdcIic6IHRydWUsICdgJzogdHJ1ZSB9O1xuICAgICAgICB2YXIgY2hhcmFjdGVyID0gbW90aW9uQXJncy5zZWxlY3RlZENoYXJhY3RlcjtcbiAgICAgICAgaWYgKGNoYXJhY3RlciA9PSAnYicpIHtcbiAgICAgICAgICAgIGNoYXJhY3RlciA9ICcoJztcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChjaGFyYWN0ZXIgPT0gJ0InKSB7XG4gICAgICAgICAgICBjaGFyYWN0ZXIgPSAneyc7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGluY2x1c2l2ZSA9ICFtb3Rpb25BcmdzLnRleHRPYmplY3RJbm5lcjtcbiAgICAgICAgdmFyIHRtcCwgbW92ZTtcbiAgICAgICAgaWYgKG1pcnJvcmVkUGFpcnNbY2hhcmFjdGVyXSkge1xuICAgICAgICAgICAgbW92ZSA9IHRydWU7XG4gICAgICAgICAgICB0bXAgPSBzZWxlY3RDb21wYW5pb25PYmplY3QoY20sIGhlYWQsIGNoYXJhY3RlciwgaW5jbHVzaXZlKTtcbiAgICAgICAgICAgIGlmICghdG1wKSB7XG4gICAgICAgICAgICAgICAgdmFyIHNjID0gY20uZ2V0U2VhcmNoQ3Vyc29yKG5ldyBSZWdFeHAoXCJcXFxcXCIgKyBjaGFyYWN0ZXIsIFwiZ1wiKSwgaGVhZCk7XG4gICAgICAgICAgICAgICAgaWYgKHNjLmZpbmQoKSkge1xuICAgICAgICAgICAgICAgICAgICB0bXAgPSBzZWxlY3RDb21wYW5pb25PYmplY3QoY20sIHNjLmZyb20oKSwgY2hhcmFjdGVyLCBpbmNsdXNpdmUpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChzZWxmUGFpcmVkW2NoYXJhY3Rlcl0pIHtcbiAgICAgICAgICAgIG1vdmUgPSB0cnVlO1xuICAgICAgICAgICAgdG1wID0gZmluZEJlZ2lubmluZ0FuZEVuZChjbSwgaGVhZCwgY2hhcmFjdGVyLCBpbmNsdXNpdmUpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKGNoYXJhY3RlciA9PT0gJ1cnIHx8IGNoYXJhY3RlciA9PT0gJ3cnKSB7XG4gICAgICAgICAgICB2YXIgcmVwZWF0ID0gbW90aW9uQXJncy5yZXBlYXQgfHwgMTtcbiAgICAgICAgICAgIHdoaWxlIChyZXBlYXQtLSA+IDApIHtcbiAgICAgICAgICAgICAgICB2YXIgcmVwZWF0ZWQgPSBleHBhbmRXb3JkVW5kZXJDdXJzb3IoY20sIHtcbiAgICAgICAgICAgICAgICAgICAgaW5jbHVzaXZlOiBpbmNsdXNpdmUsXG4gICAgICAgICAgICAgICAgICAgIGlubmVyV29yZDogIWluY2x1c2l2ZSxcbiAgICAgICAgICAgICAgICAgICAgYmlnV29yZDogY2hhcmFjdGVyID09PSAnVycsXG4gICAgICAgICAgICAgICAgICAgIG5vU3ltYm9sOiBjaGFyYWN0ZXIgPT09ICdXJyxcbiAgICAgICAgICAgICAgICAgICAgbXVsdGlsaW5lOiB0cnVlXG4gICAgICAgICAgICAgICAgfSwgdG1wICYmIHRtcC5lbmQpO1xuICAgICAgICAgICAgICAgIGlmIChyZXBlYXRlZCkge1xuICAgICAgICAgICAgICAgICAgICBpZiAoIXRtcClcbiAgICAgICAgICAgICAgICAgICAgICAgIHRtcCA9IHJlcGVhdGVkO1xuICAgICAgICAgICAgICAgICAgICB0bXAuZW5kID0gcmVwZWF0ZWQuZW5kO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChjaGFyYWN0ZXIgPT09ICdwJykge1xuICAgICAgICAgICAgdG1wID0gZmluZFBhcmFncmFwaChjbSwgaGVhZCwgbW90aW9uQXJncy5yZXBlYXQsIDAsIGluY2x1c2l2ZSk7XG4gICAgICAgICAgICBtb3Rpb25BcmdzLmxpbmV3aXNlID0gdHJ1ZTtcbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgICAgIGlmICghdmltLnZpc3VhbExpbmUpIHtcbiAgICAgICAgICAgICAgICAgICAgdmltLnZpc3VhbExpbmUgPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHZhciBvcGVyYXRvckFyZ3MgPSB2aW0uaW5wdXRTdGF0ZS5vcGVyYXRvckFyZ3M7XG4gICAgICAgICAgICAgICAgaWYgKG9wZXJhdG9yQXJncykge1xuICAgICAgICAgICAgICAgICAgICBvcGVyYXRvckFyZ3MubGluZXdpc2UgPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB0bXAuZW5kLmxpbmUtLTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChjaGFyYWN0ZXIgPT09ICd0Jykge1xuICAgICAgICAgICAgdG1wID0gZXhwYW5kVGFnVW5kZXJDdXJzb3IoY20sIGhlYWQsIGluY2x1c2l2ZSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoY2hhcmFjdGVyID09PSAncycpIHtcbiAgICAgICAgICAgIHZhciBjb250ZW50ID0gY20uZ2V0TGluZShoZWFkLmxpbmUpO1xuICAgICAgICAgICAgaWYgKGhlYWQuY2ggPiAwICYmIGlzRW5kT2ZTZW50ZW5jZVN5bWJvbChjb250ZW50W2hlYWQuY2hdKSkge1xuICAgICAgICAgICAgICAgIGhlYWQuY2ggLT0gMTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZhciBlbmQgPSBnZXRTZW50ZW5jZShjbSwgaGVhZCwgbW90aW9uQXJncy5yZXBlYXQsIDEsIGluY2x1c2l2ZSk7XG4gICAgICAgICAgICB2YXIgc3RhcnQgPSBnZXRTZW50ZW5jZShjbSwgaGVhZCwgbW90aW9uQXJncy5yZXBlYXQsIC0xLCBpbmNsdXNpdmUpO1xuICAgICAgICAgICAgaWYgKGlzV2hpdGVTcGFjZVN0cmluZyhjbS5nZXRMaW5lKHN0YXJ0LmxpbmUpW3N0YXJ0LmNoXSlcbiAgICAgICAgICAgICAgICAmJiBpc1doaXRlU3BhY2VTdHJpbmcoY20uZ2V0TGluZShlbmQubGluZSlbZW5kLmNoIC0gMV0pKSB7XG4gICAgICAgICAgICAgICAgc3RhcnQgPSB7IGxpbmU6IHN0YXJ0LmxpbmUsIGNoOiBzdGFydC5jaCArIDEgfTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHRtcCA9IHsgc3RhcnQ6IHN0YXJ0LCBlbmQ6IGVuZCB9O1xuICAgICAgICB9XG4gICAgICAgIGlmICghdG1wKSB7XG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWNtLnN0YXRlLnZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICByZXR1cm4gW3RtcC5zdGFydCwgdG1wLmVuZF07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICByZXR1cm4gZXhwYW5kU2VsZWN0aW9uKGNtLCB0bXAuc3RhcnQsIHRtcC5lbmQsIG1vdmUpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICByZXBlYXRMYXN0Q2hhcmFjdGVyU2VhcmNoOiBmdW5jdGlvbiAoY20sIGhlYWQsIG1vdGlvbkFyZ3MpIHtcbiAgICAgICAgdmFyIGxhc3RTZWFyY2ggPSB2aW1HbG9iYWxTdGF0ZS5sYXN0Q2hhcmFjdGVyU2VhcmNoO1xuICAgICAgICB2YXIgcmVwZWF0ID0gbW90aW9uQXJncy5yZXBlYXQ7XG4gICAgICAgIHZhciBmb3J3YXJkID0gbW90aW9uQXJncy5mb3J3YXJkID09PSBsYXN0U2VhcmNoLmZvcndhcmQ7XG4gICAgICAgIHZhciBpbmNyZW1lbnQgPSAobGFzdFNlYXJjaC5pbmNyZW1lbnQgPyAxIDogMCkgKiAoZm9yd2FyZCA/IC0xIDogMSk7XG4gICAgICAgIGNtLm1vdmVIKC1pbmNyZW1lbnQsICdjaGFyJyk7XG4gICAgICAgIG1vdGlvbkFyZ3MuaW5jbHVzaXZlID0gZm9yd2FyZCA/IHRydWUgOiBmYWxzZTtcbiAgICAgICAgdmFyIGN1ckVuZCA9IG1vdmVUb0NoYXJhY3RlcihjbSwgcmVwZWF0LCBmb3J3YXJkLCBsYXN0U2VhcmNoLnNlbGVjdGVkQ2hhcmFjdGVyKTtcbiAgICAgICAgaWYgKCFjdXJFbmQpIHtcbiAgICAgICAgICAgIGNtLm1vdmVIKGluY3JlbWVudCwgJ2NoYXInKTtcbiAgICAgICAgICAgIHJldHVybiBoZWFkO1xuICAgICAgICB9XG4gICAgICAgIGN1ckVuZC5jaCArPSBpbmNyZW1lbnQ7XG4gICAgICAgIHJldHVybiBjdXJFbmQ7XG4gICAgfVxufTtcbmZ1bmN0aW9uIGRlZmluZU1vdGlvbihuYW1lLCBmbikge1xuICAgIG1vdGlvbnNbbmFtZV0gPSBmbjtcbn1cbmZ1bmN0aW9uIGZpbGxBcnJheSh2YWwsIHRpbWVzKSB7XG4gICAgdmFyIGFyciA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdGltZXM7IGkrKykge1xuICAgICAgICBhcnIucHVzaCh2YWwpO1xuICAgIH1cbiAgICByZXR1cm4gYXJyO1xufVxudmFyIG9wZXJhdG9ycyA9IHtcbiAgICBjaGFuZ2U6IGZ1bmN0aW9uIChjbSwgYXJncywgcmFuZ2VzKSB7XG4gICAgICAgIHZhciBmaW5hbEhlYWQsIHRleHQ7XG4gICAgICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgICAgIHZhciBhbmNob3IgPSByYW5nZXNbMF0uYW5jaG9yLCBoZWFkID0gcmFuZ2VzWzBdLmhlYWQ7XG4gICAgICAgIGlmICghdmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIHRleHQgPSBjbS5nZXRSYW5nZShhbmNob3IsIGhlYWQpO1xuICAgICAgICAgICAgdmFyIGxhc3RTdGF0ZSA9IHZpbS5sYXN0RWRpdElucHV0U3RhdGUgfHwge307XG4gICAgICAgICAgICBpZiAobGFzdFN0YXRlLm1vdGlvbiA9PSBcIm1vdmVCeVdvcmRzXCIgJiYgIWlzV2hpdGVTcGFjZVN0cmluZyh0ZXh0KSkge1xuICAgICAgICAgICAgICAgIHZhciBtYXRjaCA9ICgvXFxzKyQvKS5leGVjKHRleHQpO1xuICAgICAgICAgICAgICAgIGlmIChtYXRjaCAmJiBsYXN0U3RhdGUubW90aW9uQXJncyAmJiBsYXN0U3RhdGUubW90aW9uQXJncy5mb3J3YXJkKSB7XG4gICAgICAgICAgICAgICAgICAgIGhlYWQgPSBvZmZzZXRDdXJzb3IoaGVhZCwgMCwgLW1hdGNoWzBdLmxlbmd0aCk7XG4gICAgICAgICAgICAgICAgICAgIHRleHQgPSB0ZXh0LnNsaWNlKDAsIC1tYXRjaFswXS5sZW5ndGgpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChhcmdzLmxpbmV3aXNlKSB7XG4gICAgICAgICAgICAgICAgYW5jaG9yID0gbmV3IFBvcyhhbmNob3IubGluZSwgZmluZEZpcnN0Tm9uV2hpdGVTcGFjZUNoYXJhY3RlcihjbS5nZXRMaW5lKGFuY2hvci5saW5lKSkpO1xuICAgICAgICAgICAgICAgIGlmIChoZWFkLmxpbmUgPiBhbmNob3IubGluZSkge1xuICAgICAgICAgICAgICAgICAgICBoZWFkID0gbmV3IFBvcyhoZWFkLmxpbmUgLSAxLCBOdW1iZXIuTUFYX1ZBTFVFKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoJycsIGFuY2hvciwgaGVhZCk7XG4gICAgICAgICAgICBmaW5hbEhlYWQgPSBhbmNob3I7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoYXJncy5mdWxsTGluZSkge1xuICAgICAgICAgICAgaGVhZC5jaCA9IE51bWJlci5NQVhfVkFMVUU7XG4gICAgICAgICAgICBoZWFkLmxpbmUtLTtcbiAgICAgICAgICAgIGNtLnNldFNlbGVjdGlvbihhbmNob3IsIGhlYWQpO1xuICAgICAgICAgICAgdGV4dCA9IGNtLmdldFNlbGVjdGlvbigpO1xuICAgICAgICAgICAgY20ucmVwbGFjZVNlbGVjdGlvbihcIlwiKTtcbiAgICAgICAgICAgIGZpbmFsSGVhZCA9IGFuY2hvcjtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRleHQgPSBjbS5nZXRTZWxlY3Rpb24oKTtcbiAgICAgICAgICAgIHZhciByZXBsYWNlbWVudCA9IGZpbGxBcnJheSgnJywgcmFuZ2VzLmxlbmd0aCk7XG4gICAgICAgICAgICBjbS5yZXBsYWNlU2VsZWN0aW9ucyhyZXBsYWNlbWVudCk7XG4gICAgICAgICAgICBmaW5hbEhlYWQgPSBjdXJzb3JNaW4ocmFuZ2VzWzBdLmhlYWQsIHJhbmdlc1swXS5hbmNob3IpO1xuICAgICAgICB9XG4gICAgICAgIHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5wdXNoVGV4dChhcmdzLnJlZ2lzdGVyTmFtZSwgJ2NoYW5nZScsIHRleHQsIGFyZ3MubGluZXdpc2UsIHJhbmdlcy5sZW5ndGggPiAxKTtcbiAgICAgICAgYWN0aW9ucy5lbnRlckluc2VydE1vZGUoY20sIHsgaGVhZDogZmluYWxIZWFkIH0sIGNtLnN0YXRlLnZpbSk7XG4gICAgfSxcbiAgICAnZGVsZXRlJzogZnVuY3Rpb24gKGNtLCBhcmdzLCByYW5nZXMpIHtcbiAgICAgICAgdmFyIGZpbmFsSGVhZCwgdGV4dDtcbiAgICAgICAgdmFyIHZpbSA9IGNtLnN0YXRlLnZpbTtcbiAgICAgICAgaWYgKCF2aW0udmlzdWFsQmxvY2spIHtcbiAgICAgICAgICAgIHZhciBhbmNob3IgPSByYW5nZXNbMF0uYW5jaG9yLCBoZWFkID0gcmFuZ2VzWzBdLmhlYWQ7XG4gICAgICAgICAgICBpZiAoYXJncy5saW5ld2lzZSAmJlxuICAgICAgICAgICAgICAgIGhlYWQubGluZSAhPSBjbS5maXJzdExpbmUoKSAmJlxuICAgICAgICAgICAgICAgIGFuY2hvci5saW5lID09IGNtLmxhc3RMaW5lKCkgJiZcbiAgICAgICAgICAgICAgICBhbmNob3IubGluZSA9PSBoZWFkLmxpbmUgLSAxKSB7XG4gICAgICAgICAgICAgICAgaWYgKGFuY2hvci5saW5lID09IGNtLmZpcnN0TGluZSgpKSB7XG4gICAgICAgICAgICAgICAgICAgIGFuY2hvci5jaCA9IDA7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBhbmNob3IgPSBuZXcgUG9zKGFuY2hvci5saW5lIC0gMSwgbGluZUxlbmd0aChjbSwgYW5jaG9yLmxpbmUgLSAxKSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdGV4dCA9IGNtLmdldFJhbmdlKGFuY2hvciwgaGVhZCk7XG4gICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoJycsIGFuY2hvciwgaGVhZCk7XG4gICAgICAgICAgICBmaW5hbEhlYWQgPSBhbmNob3I7XG4gICAgICAgICAgICBpZiAoYXJncy5saW5ld2lzZSkge1xuICAgICAgICAgICAgICAgIGZpbmFsSGVhZCA9IG1vdGlvbnMubW92ZVRvRmlyc3ROb25XaGl0ZVNwYWNlQ2hhcmFjdGVyKGNtLCBhbmNob3IpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGV4dCA9IGNtLmdldFNlbGVjdGlvbigpO1xuICAgICAgICAgICAgdmFyIHJlcGxhY2VtZW50ID0gZmlsbEFycmF5KCcnLCByYW5nZXMubGVuZ3RoKTtcbiAgICAgICAgICAgIGNtLnJlcGxhY2VTZWxlY3Rpb25zKHJlcGxhY2VtZW50KTtcbiAgICAgICAgICAgIGZpbmFsSGVhZCA9IGN1cnNvck1pbihyYW5nZXNbMF0uaGVhZCwgcmFuZ2VzWzBdLmFuY2hvcik7XG4gICAgICAgIH1cbiAgICAgICAgdmltR2xvYmFsU3RhdGUucmVnaXN0ZXJDb250cm9sbGVyLnB1c2hUZXh0KGFyZ3MucmVnaXN0ZXJOYW1lLCAnZGVsZXRlJywgdGV4dCwgYXJncy5saW5ld2lzZSwgdmltLnZpc3VhbEJsb2NrKTtcbiAgICAgICAgcmV0dXJuIGNsaXBDdXJzb3JUb0NvbnRlbnQoY20sIGZpbmFsSGVhZCk7XG4gICAgfSxcbiAgICBpbmRlbnQ6IGZ1bmN0aW9uIChjbSwgYXJncywgcmFuZ2VzKSB7XG4gICAgICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgICAgIHZhciByZXBlYXQgPSAodmltLnZpc3VhbE1vZGUpID8gYXJncy5yZXBlYXQgOiAxO1xuICAgICAgICBpZiAodmltLnZpc3VhbEJsb2NrKSB7XG4gICAgICAgICAgICB2YXIgdGFiU2l6ZSA9IGNtLmdldE9wdGlvbigndGFiU2l6ZScpO1xuICAgICAgICAgICAgdmFyIGluZGVudCA9IGNtLmdldE9wdGlvbignaW5kZW50V2l0aFRhYnMnKSA/ICdcXHQnIDogJyAnLnJlcGVhdCh0YWJTaXplKTtcbiAgICAgICAgICAgIHZhciBjdXJzb3I7XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gcmFuZ2VzLmxlbmd0aCAtIDE7IGkgPj0gMDsgaS0tKSB7XG4gICAgICAgICAgICAgICAgY3Vyc29yID0gY3Vyc29yTWluKHJhbmdlc1tpXS5hbmNob3IsIHJhbmdlc1tpXS5oZWFkKTtcbiAgICAgICAgICAgICAgICBpZiAoYXJncy5pbmRlbnRSaWdodCkge1xuICAgICAgICAgICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoaW5kZW50LnJlcGVhdChyZXBlYXQpLCBjdXJzb3IsIGN1cnNvcik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICB2YXIgdGV4dCA9IGNtLmdldExpbmUoY3Vyc29yLmxpbmUpO1xuICAgICAgICAgICAgICAgICAgICB2YXIgZW5kID0gMDtcbiAgICAgICAgICAgICAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCByZXBlYXQ7IGorKykge1xuICAgICAgICAgICAgICAgICAgICAgICAgdmFyIGNoID0gdGV4dFtjdXJzb3IuY2ggKyBlbmRdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNoID09ICdcXHQnKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZW5kKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjaCA9PSAnICcpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbmQrKztcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHZhciBrID0gMTsgayA8IGluZGVudC5sZW5ndGg7IGsrKykge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjaCA9IHRleHRbY3Vyc29yLmNoICsgZW5kXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNoICE9PSAnICcpXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZW5kKys7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgY20ucmVwbGFjZVJhbmdlKCcnLCBjdXJzb3IsIG9mZnNldEN1cnNvcihjdXJzb3IsIDAsIGVuZCkpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiBjdXJzb3I7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoY20uaW5kZW50TW9yZSkge1xuICAgICAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCByZXBlYXQ7IGorKykge1xuICAgICAgICAgICAgICAgIGlmIChhcmdzLmluZGVudFJpZ2h0KVxuICAgICAgICAgICAgICAgICAgICBjbS5pbmRlbnRNb3JlKCk7XG4gICAgICAgICAgICAgICAgZWxzZVxuICAgICAgICAgICAgICAgICAgICBjbS5pbmRlbnRMZXNzKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YXIgc3RhcnRMaW5lID0gcmFuZ2VzWzBdLmFuY2hvci5saW5lO1xuICAgICAgICAgICAgdmFyIGVuZExpbmUgPSB2aW0udmlzdWFsQmxvY2sgP1xuICAgICAgICAgICAgICAgIHJhbmdlc1tyYW5nZXMubGVuZ3RoIC0gMV0uYW5jaG9yLmxpbmUgOlxuICAgICAgICAgICAgICAgIHJhbmdlc1swXS5oZWFkLmxpbmU7XG4gICAgICAgICAgICBpZiAoYXJncy5saW5ld2lzZSkge1xuICAgICAgICAgICAgICAgIGVuZExpbmUtLTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGZvciAodmFyIGkgPSBzdGFydExpbmU7IGkgPD0gZW5kTGluZTsgaSsrKSB7XG4gICAgICAgICAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCByZXBlYXQ7IGorKykge1xuICAgICAgICAgICAgICAgICAgICBjbS5pbmRlbnRMaW5lKGksIGFyZ3MuaW5kZW50UmlnaHQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbW90aW9ucy5tb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20sIHJhbmdlc1swXS5hbmNob3IpO1xuICAgIH0sXG4gICAgaW5kZW50QXV0bzogZnVuY3Rpb24gKGNtLCBfYXJncywgcmFuZ2VzKSB7XG4gICAgICAgIGNtLmV4ZWNDb21tYW5kKFwiaW5kZW50QXV0b1wiKTtcbiAgICAgICAgcmV0dXJuIG1vdGlvbnMubW92ZVRvRmlyc3ROb25XaGl0ZVNwYWNlQ2hhcmFjdGVyKGNtLCByYW5nZXNbMF0uYW5jaG9yKTtcbiAgICB9LFxuICAgIGhhcmRXcmFwOiBmdW5jdGlvbiAoY20sIG9wZXJhdG9yQXJncywgcmFuZ2VzLCBvbGRBbmNob3IsIG5ld0hlYWQpIHtcbiAgICAgICAgaWYgKCFjbS5oYXJkV3JhcClcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgdmFyIGZyb20gPSByYW5nZXNbMF0uYW5jaG9yLmxpbmU7XG4gICAgICAgIHZhciB0byA9IHJhbmdlc1swXS5oZWFkLmxpbmU7XG4gICAgICAgIGlmIChvcGVyYXRvckFyZ3MubGluZXdpc2UpXG4gICAgICAgICAgICB0by0tO1xuICAgICAgICB2YXIgZW5kUm93ID0gY20uaGFyZFdyYXAoeyBmcm9tOiBmcm9tLCB0bzogdG8gfSk7XG4gICAgICAgIGlmIChlbmRSb3cgPiBmcm9tICYmIG9wZXJhdG9yQXJncy5saW5ld2lzZSlcbiAgICAgICAgICAgIGVuZFJvdy0tO1xuICAgICAgICByZXR1cm4gb3BlcmF0b3JBcmdzLmtlZXBDdXJzb3IgPyBvbGRBbmNob3IgOiBuZXcgUG9zKGVuZFJvdywgMCk7XG4gICAgfSxcbiAgICBjaGFuZ2VDYXNlOiBmdW5jdGlvbiAoY20sIGFyZ3MsIHJhbmdlcywgb2xkQW5jaG9yLCBuZXdIZWFkKSB7XG4gICAgICAgIHZhciBzZWxlY3Rpb25zID0gY20uZ2V0U2VsZWN0aW9ucygpO1xuICAgICAgICB2YXIgc3dhcHBlZCA9IFtdO1xuICAgICAgICB2YXIgdG9Mb3dlciA9IGFyZ3MudG9Mb3dlcjtcbiAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCBzZWxlY3Rpb25zLmxlbmd0aDsgaisrKSB7XG4gICAgICAgICAgICB2YXIgdG9Td2FwID0gc2VsZWN0aW9uc1tqXTtcbiAgICAgICAgICAgIHZhciB0ZXh0ID0gJyc7XG4gICAgICAgICAgICBpZiAodG9Mb3dlciA9PT0gdHJ1ZSkge1xuICAgICAgICAgICAgICAgIHRleHQgPSB0b1N3YXAudG9Mb3dlckNhc2UoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKHRvTG93ZXIgPT09IGZhbHNlKSB7XG4gICAgICAgICAgICAgICAgdGV4dCA9IHRvU3dhcC50b1VwcGVyQ2FzZSgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0b1N3YXAubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyIGNoYXJhY3RlciA9IHRvU3dhcC5jaGFyQXQoaSk7XG4gICAgICAgICAgICAgICAgICAgIHRleHQgKz0gaXNVcHBlckNhc2UoY2hhcmFjdGVyKSA/IGNoYXJhY3Rlci50b0xvd2VyQ2FzZSgpIDpcbiAgICAgICAgICAgICAgICAgICAgICAgIGNoYXJhY3Rlci50b1VwcGVyQ2FzZSgpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHN3YXBwZWQucHVzaCh0ZXh0KTtcbiAgICAgICAgfVxuICAgICAgICBjbS5yZXBsYWNlU2VsZWN0aW9ucyhzd2FwcGVkKTtcbiAgICAgICAgaWYgKGFyZ3Muc2hvdWxkTW92ZUN1cnNvcikge1xuICAgICAgICAgICAgcmV0dXJuIG5ld0hlYWQ7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoIWNtLnN0YXRlLnZpbS52aXN1YWxNb2RlICYmIGFyZ3MubGluZXdpc2UgJiYgcmFuZ2VzWzBdLmFuY2hvci5saW5lICsgMSA9PSByYW5nZXNbMF0uaGVhZC5saW5lKSB7XG4gICAgICAgICAgICByZXR1cm4gbW90aW9ucy5tb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20sIG9sZEFuY2hvcik7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoYXJncy5saW5ld2lzZSkge1xuICAgICAgICAgICAgcmV0dXJuIG9sZEFuY2hvcjtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBjdXJzb3JNaW4ocmFuZ2VzWzBdLmFuY2hvciwgcmFuZ2VzWzBdLmhlYWQpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICB5YW5rOiBmdW5jdGlvbiAoY20sIGFyZ3MsIHJhbmdlcywgb2xkQW5jaG9yKSB7XG4gICAgICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgICAgIHZhciB0ZXh0ID0gY20uZ2V0U2VsZWN0aW9uKCk7XG4gICAgICAgIHZhciBlbmRQb3MgPSB2aW0udmlzdWFsTW9kZVxuICAgICAgICAgICAgPyBjdXJzb3JNaW4odmltLnNlbC5hbmNob3IsIHZpbS5zZWwuaGVhZCwgcmFuZ2VzWzBdLmhlYWQsIHJhbmdlc1swXS5hbmNob3IpXG4gICAgICAgICAgICA6IG9sZEFuY2hvcjtcbiAgICAgICAgdmltR2xvYmFsU3RhdGUucmVnaXN0ZXJDb250cm9sbGVyLnB1c2hUZXh0KGFyZ3MucmVnaXN0ZXJOYW1lLCAneWFuaycsIHRleHQsIGFyZ3MubGluZXdpc2UsIHZpbS52aXN1YWxCbG9jayk7XG4gICAgICAgIHJldHVybiBlbmRQb3M7XG4gICAgfVxufTtcbmZ1bmN0aW9uIGRlZmluZU9wZXJhdG9yKG5hbWUsIGZuKSB7XG4gICAgb3BlcmF0b3JzW25hbWVdID0gZm47XG59XG52YXIgYWN0aW9ucyA9IHtcbiAgICBqdW1wTGlzdFdhbGs6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIHZhciByZXBlYXQgPSBhY3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgdmFyIGZvcndhcmQgPSBhY3Rpb25BcmdzLmZvcndhcmQ7XG4gICAgICAgIHZhciBqdW1wTGlzdCA9IHZpbUdsb2JhbFN0YXRlLmp1bXBMaXN0O1xuICAgICAgICB2YXIgbWFyayA9IGp1bXBMaXN0Lm1vdmUoY20sIGZvcndhcmQgPyByZXBlYXQgOiAtcmVwZWF0KTtcbiAgICAgICAgdmFyIG1hcmtQb3MgPSBtYXJrID8gbWFyay5maW5kKCkgOiB1bmRlZmluZWQ7XG4gICAgICAgIG1hcmtQb3MgPSBtYXJrUG9zID8gbWFya1BvcyA6IGNtLmdldEN1cnNvcigpO1xuICAgICAgICBjbS5zZXRDdXJzb3IobWFya1Bvcyk7XG4gICAgICAgIGNtLmFjZS5jdXJPcC5jb21tYW5kLnNjcm9sbEludG9WaWV3ID0gXCJjZW50ZXItYW5pbWF0ZVwiOyAvLyBhY2VfcGF0Y2hcbiAgICB9LFxuICAgIHNjcm9sbDogZnVuY3Rpb24gKGNtLCBhY3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmFyIHJlcGVhdCA9IGFjdGlvbkFyZ3MucmVwZWF0IHx8IDE7XG4gICAgICAgIHZhciBsaW5lSGVpZ2h0ID0gY20uZGVmYXVsdFRleHRIZWlnaHQoKTtcbiAgICAgICAgdmFyIHRvcCA9IGNtLmdldFNjcm9sbEluZm8oKS50b3A7XG4gICAgICAgIHZhciBkZWx0YSA9IGxpbmVIZWlnaHQgKiByZXBlYXQ7XG4gICAgICAgIHZhciBuZXdQb3MgPSBhY3Rpb25BcmdzLmZvcndhcmQgPyB0b3AgKyBkZWx0YSA6IHRvcCAtIGRlbHRhO1xuICAgICAgICB2YXIgY3Vyc29yID0gY29weUN1cnNvcihjbS5nZXRDdXJzb3IoKSk7XG4gICAgICAgIHZhciBjdXJzb3JDb29yZHMgPSBjbS5jaGFyQ29vcmRzKGN1cnNvciwgJ2xvY2FsJyk7XG4gICAgICAgIGlmIChhY3Rpb25BcmdzLmZvcndhcmQpIHtcbiAgICAgICAgICAgIGlmIChuZXdQb3MgPiBjdXJzb3JDb29yZHMudG9wKSB7XG4gICAgICAgICAgICAgICAgY3Vyc29yLmxpbmUgKz0gKG5ld1BvcyAtIGN1cnNvckNvb3Jkcy50b3ApIC8gbGluZUhlaWdodDtcbiAgICAgICAgICAgICAgICBjdXJzb3IubGluZSA9IE1hdGguY2VpbChjdXJzb3IubGluZSk7XG4gICAgICAgICAgICAgICAgY20uc2V0Q3Vyc29yKGN1cnNvcik7XG4gICAgICAgICAgICAgICAgY3Vyc29yQ29vcmRzID0gY20uY2hhckNvb3JkcyhjdXJzb3IsICdsb2NhbCcpO1xuICAgICAgICAgICAgICAgIGNtLnNjcm9sbFRvKG51bGwsIGN1cnNvckNvb3Jkcy50b3ApO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgY20uc2Nyb2xsVG8obnVsbCwgbmV3UG9zKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhciBuZXdCb3R0b20gPSBuZXdQb3MgKyBjbS5nZXRTY3JvbGxJbmZvKCkuY2xpZW50SGVpZ2h0O1xuICAgICAgICAgICAgaWYgKG5ld0JvdHRvbSA8IGN1cnNvckNvb3Jkcy5ib3R0b20pIHtcbiAgICAgICAgICAgICAgICBjdXJzb3IubGluZSAtPSAoY3Vyc29yQ29vcmRzLmJvdHRvbSAtIG5ld0JvdHRvbSkgLyBsaW5lSGVpZ2h0O1xuICAgICAgICAgICAgICAgIGN1cnNvci5saW5lID0gTWF0aC5mbG9vcihjdXJzb3IubGluZSk7XG4gICAgICAgICAgICAgICAgY20uc2V0Q3Vyc29yKGN1cnNvcik7XG4gICAgICAgICAgICAgICAgY3Vyc29yQ29vcmRzID0gY20uY2hhckNvb3JkcyhjdXJzb3IsICdsb2NhbCcpO1xuICAgICAgICAgICAgICAgIGNtLnNjcm9sbFRvKG51bGwsIGN1cnNvckNvb3Jkcy5ib3R0b20gLSBjbS5nZXRTY3JvbGxJbmZvKCkuY2xpZW50SGVpZ2h0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGNtLnNjcm9sbFRvKG51bGwsIG5ld1Bvcyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHNjcm9sbFRvQ3Vyc29yOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MpIHtcbiAgICAgICAgdmFyIGxpbmVOdW0gPSBjbS5nZXRDdXJzb3IoKS5saW5lO1xuICAgICAgICB2YXIgY2hhckNvb3JkcyA9IGNtLmNoYXJDb29yZHMobmV3IFBvcyhsaW5lTnVtLCAwKSwgJ2xvY2FsJyk7XG4gICAgICAgIHZhciBoZWlnaHQgPSBjbS5nZXRTY3JvbGxJbmZvKCkuY2xpZW50SGVpZ2h0O1xuICAgICAgICB2YXIgeSA9IGNoYXJDb29yZHMudG9wO1xuICAgICAgICBzd2l0Y2ggKGFjdGlvbkFyZ3MucG9zaXRpb24pIHtcbiAgICAgICAgICAgIGNhc2UgJ2NlbnRlcic6XG4gICAgICAgICAgICAgICAgeSA9IGNoYXJDb29yZHMuYm90dG9tIC0gaGVpZ2h0IC8gMjtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGNhc2UgJ2JvdHRvbSc6XG4gICAgICAgICAgICAgICAgdmFyIGxpbmVMYXN0Q2hhclBvcyA9IG5ldyBQb3MobGluZU51bSwgY20uZ2V0TGluZShsaW5lTnVtKS5sZW5ndGggLSAxKTtcbiAgICAgICAgICAgICAgICB2YXIgbGluZUxhc3RDaGFyQ29vcmRzID0gY20uY2hhckNvb3JkcyhsaW5lTGFzdENoYXJQb3MsICdsb2NhbCcpO1xuICAgICAgICAgICAgICAgIHZhciBsaW5lSGVpZ2h0ID0gbGluZUxhc3RDaGFyQ29vcmRzLmJvdHRvbSAtIHk7XG4gICAgICAgICAgICAgICAgeSA9IHkgLSBoZWlnaHQgKyBsaW5lSGVpZ2h0O1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICB9XG4gICAgICAgIGNtLnNjcm9sbFRvKG51bGwsIHkpO1xuICAgIH0sXG4gICAgcmVwbGF5TWFjcm86IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciByZWdpc3Rlck5hbWUgPSBhY3Rpb25BcmdzLnNlbGVjdGVkQ2hhcmFjdGVyO1xuICAgICAgICB2YXIgcmVwZWF0ID0gYWN0aW9uQXJncy5yZXBlYXQ7XG4gICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICBpZiAocmVnaXN0ZXJOYW1lID09ICdAJykge1xuICAgICAgICAgICAgcmVnaXN0ZXJOYW1lID0gbWFjcm9Nb2RlU3RhdGUubGF0ZXN0UmVnaXN0ZXI7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBtYWNyb01vZGVTdGF0ZS5sYXRlc3RSZWdpc3RlciA9IHJlZ2lzdGVyTmFtZTtcbiAgICAgICAgfVxuICAgICAgICB3aGlsZSAocmVwZWF0LS0pIHtcbiAgICAgICAgICAgIGV4ZWN1dGVNYWNyb1JlZ2lzdGVyKGNtLCB2aW0sIG1hY3JvTW9kZVN0YXRlLCByZWdpc3Rlck5hbWUpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBlbnRlck1hY3JvUmVjb3JkTW9kZTogZnVuY3Rpb24gKGNtLCBhY3Rpb25BcmdzKSB7XG4gICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICB2YXIgcmVnaXN0ZXJOYW1lID0gYWN0aW9uQXJncy5zZWxlY3RlZENoYXJhY3RlcjtcbiAgICAgICAgaWYgKHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5pc1ZhbGlkUmVnaXN0ZXIocmVnaXN0ZXJOYW1lKSkge1xuICAgICAgICAgICAgbWFjcm9Nb2RlU3RhdGUuZW50ZXJNYWNyb1JlY29yZE1vZGUoY20sIHJlZ2lzdGVyTmFtZSk7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHRvZ2dsZU92ZXJ3cml0ZTogZnVuY3Rpb24gKGNtKSB7XG4gICAgICAgIGlmICghY20uc3RhdGUub3ZlcndyaXRlKSB7XG4gICAgICAgICAgICBjbS50b2dnbGVPdmVyd3JpdGUodHJ1ZSk7XG4gICAgICAgICAgICBjbS5zZXRPcHRpb24oJ2tleU1hcCcsICd2aW0tcmVwbGFjZScpO1xuICAgICAgICAgICAgQ29kZU1pcnJvci5zaWduYWwoY20sIFwidmltLW1vZGUtY2hhbmdlXCIsIHsgbW9kZTogXCJyZXBsYWNlXCIgfSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBjbS50b2dnbGVPdmVyd3JpdGUoZmFsc2UpO1xuICAgICAgICAgICAgY20uc2V0T3B0aW9uKCdrZXlNYXAnLCAndmltLWluc2VydCcpO1xuICAgICAgICAgICAgQ29kZU1pcnJvci5zaWduYWwoY20sIFwidmltLW1vZGUtY2hhbmdlXCIsIHsgbW9kZTogXCJpbnNlcnRcIiB9KTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgZW50ZXJJbnNlcnRNb2RlOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICBpZiAoY20uZ2V0T3B0aW9uKCdyZWFkT25seScpKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmltLmluc2VydE1vZGUgPSB0cnVlO1xuICAgICAgICB2aW0uaW5zZXJ0TW9kZVJlcGVhdCA9IGFjdGlvbkFyZ3MgJiYgYWN0aW9uQXJncy5yZXBlYXQgfHwgMTtcbiAgICAgICAgdmFyIGluc2VydEF0ID0gKGFjdGlvbkFyZ3MpID8gYWN0aW9uQXJncy5pbnNlcnRBdCA6IG51bGw7XG4gICAgICAgIHZhciBzZWwgPSB2aW0uc2VsO1xuICAgICAgICB2YXIgaGVhZCA9IGFjdGlvbkFyZ3MuaGVhZCB8fCBjbS5nZXRDdXJzb3IoJ2hlYWQnKTtcbiAgICAgICAgdmFyIGhlaWdodCA9IGNtLmxpc3RTZWxlY3Rpb25zKCkubGVuZ3RoO1xuICAgICAgICBpZiAoaW5zZXJ0QXQgPT0gJ2VvbCcpIHtcbiAgICAgICAgICAgIGhlYWQgPSBuZXcgUG9zKGhlYWQubGluZSwgbGluZUxlbmd0aChjbSwgaGVhZC5saW5lKSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoaW5zZXJ0QXQgPT0gJ2JvbCcpIHtcbiAgICAgICAgICAgIGhlYWQgPSBuZXcgUG9zKGhlYWQubGluZSwgMCk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoaW5zZXJ0QXQgPT0gJ2NoYXJBZnRlcicpIHtcbiAgICAgICAgICAgIHZhciBuZXdQb3NpdGlvbiA9IHVwZGF0ZVNlbGVjdGlvbkZvclN1cnJvZ2F0ZUNoYXJhY3RlcnMoY20sIGhlYWQsIG9mZnNldEN1cnNvcihoZWFkLCAwLCAxKSk7XG4gICAgICAgICAgICBoZWFkID0gbmV3UG9zaXRpb24uZW5kO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKGluc2VydEF0ID09ICdmaXJzdE5vbkJsYW5rJykge1xuICAgICAgICAgICAgdmFyIG5ld1Bvc2l0aW9uID0gdXBkYXRlU2VsZWN0aW9uRm9yU3Vycm9nYXRlQ2hhcmFjdGVycyhjbSwgaGVhZCwgbW90aW9ucy5tb3ZlVG9GaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20sIGhlYWQpKTtcbiAgICAgICAgICAgIGhlYWQgPSBuZXdQb3NpdGlvbi5lbmQ7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoaW5zZXJ0QXQgPT0gJ3N0YXJ0T2ZTZWxlY3RlZEFyZWEnKSB7XG4gICAgICAgICAgICBpZiAoIXZpbS52aXN1YWxNb2RlKVxuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIGlmICghdmltLnZpc3VhbEJsb2NrKSB7XG4gICAgICAgICAgICAgICAgaWYgKHNlbC5oZWFkLmxpbmUgPCBzZWwuYW5jaG9yLmxpbmUpIHtcbiAgICAgICAgICAgICAgICAgICAgaGVhZCA9IHNlbC5oZWFkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgaGVhZCA9IG5ldyBQb3Moc2VsLmFuY2hvci5saW5lLCAwKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBoZWFkID0gbmV3IFBvcyhNYXRoLm1pbihzZWwuaGVhZC5saW5lLCBzZWwuYW5jaG9yLmxpbmUpLCBNYXRoLm1pbihzZWwuaGVhZC5jaCwgc2VsLmFuY2hvci5jaCkpO1xuICAgICAgICAgICAgICAgIGhlaWdodCA9IE1hdGguYWJzKHNlbC5oZWFkLmxpbmUgLSBzZWwuYW5jaG9yLmxpbmUpICsgMTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChpbnNlcnRBdCA9PSAnZW5kT2ZTZWxlY3RlZEFyZWEnKSB7XG4gICAgICAgICAgICBpZiAoIXZpbS52aXN1YWxNb2RlKVxuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIGlmICghdmltLnZpc3VhbEJsb2NrKSB7XG4gICAgICAgICAgICAgICAgaWYgKHNlbC5oZWFkLmxpbmUgPj0gc2VsLmFuY2hvci5saW5lKSB7XG4gICAgICAgICAgICAgICAgICAgIGhlYWQgPSBvZmZzZXRDdXJzb3Ioc2VsLmhlYWQsIDAsIDEpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgaGVhZCA9IG5ldyBQb3Moc2VsLmFuY2hvci5saW5lLCAwKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBoZWFkID0gbmV3IFBvcyhNYXRoLm1pbihzZWwuaGVhZC5saW5lLCBzZWwuYW5jaG9yLmxpbmUpLCBNYXRoLm1heChzZWwuaGVhZC5jaCwgc2VsLmFuY2hvci5jaCkgKyAxKTtcbiAgICAgICAgICAgICAgICBoZWlnaHQgPSBNYXRoLmFicyhzZWwuaGVhZC5saW5lIC0gc2VsLmFuY2hvci5saW5lKSArIDE7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoaW5zZXJ0QXQgPT0gJ2lucGxhY2UnKSB7XG4gICAgICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoaW5zZXJ0QXQgPT0gJ2xhc3RFZGl0Jykge1xuICAgICAgICAgICAgaGVhZCA9IGdldExhc3RFZGl0UG9zKGNtKSB8fCBoZWFkO1xuICAgICAgICB9XG4gICAgICAgIGNtLnNldE9wdGlvbignZGlzYWJsZUlucHV0JywgZmFsc2UpO1xuICAgICAgICBpZiAoYWN0aW9uQXJncyAmJiBhY3Rpb25BcmdzLnJlcGxhY2UpIHtcbiAgICAgICAgICAgIGNtLnRvZ2dsZU92ZXJ3cml0ZSh0cnVlKTtcbiAgICAgICAgICAgIGNtLnNldE9wdGlvbigna2V5TWFwJywgJ3ZpbS1yZXBsYWNlJyk7XG4gICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcInJlcGxhY2VcIiB9KTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGNtLnRvZ2dsZU92ZXJ3cml0ZShmYWxzZSk7XG4gICAgICAgICAgICBjbS5zZXRPcHRpb24oJ2tleU1hcCcsICd2aW0taW5zZXJ0Jyk7XG4gICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcImluc2VydFwiIH0pO1xuICAgICAgICB9XG4gICAgICAgIGlmICghdmltR2xvYmFsU3RhdGUubWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgICAgICBjbS5vbignY2hhbmdlJywgb25DaGFuZ2UpO1xuICAgICAgICAgICAgaWYgKHZpbS5pbnNlcnRFbmQpXG4gICAgICAgICAgICAgICAgdmltLmluc2VydEVuZC5jbGVhcigpO1xuICAgICAgICAgICAgdmltLmluc2VydEVuZCA9IGNtLnNldEJvb2ttYXJrKGhlYWQsIHsgaW5zZXJ0TGVmdDogdHJ1ZSB9KTtcbiAgICAgICAgICAgIENvZGVNaXJyb3Iub24oY20uZ2V0SW5wdXRGaWVsZCgpLCAna2V5ZG93bicsIG9uS2V5RXZlbnRUYXJnZXRLZXlEb3duKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIGV4aXRWaXN1YWxNb2RlKGNtKTtcbiAgICAgICAgfVxuICAgICAgICBzZWxlY3RGb3JJbnNlcnQoY20sIGhlYWQsIGhlaWdodCk7XG4gICAgfSxcbiAgICB0b2dnbGVWaXN1YWxNb2RlOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2YXIgcmVwZWF0ID0gYWN0aW9uQXJncy5yZXBlYXQ7XG4gICAgICAgIHZhciBhbmNob3IgPSBjbS5nZXRDdXJzb3IoKTtcbiAgICAgICAgdmFyIGhlYWQ7XG4gICAgICAgIGlmICghdmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIHZpbS52aXN1YWxNb2RlID0gdHJ1ZTtcbiAgICAgICAgICAgIHZpbS52aXN1YWxMaW5lID0gISFhY3Rpb25BcmdzLmxpbmV3aXNlO1xuICAgICAgICAgICAgdmltLnZpc3VhbEJsb2NrID0gISFhY3Rpb25BcmdzLmJsb2Nrd2lzZTtcbiAgICAgICAgICAgIGhlYWQgPSBjbGlwQ3Vyc29yVG9Db250ZW50KGNtLCBuZXcgUG9zKGFuY2hvci5saW5lLCBhbmNob3IuY2ggKyByZXBlYXQgLSAxKSk7XG4gICAgICAgICAgICB2YXIgbmV3UG9zaXRpb24gPSB1cGRhdGVTZWxlY3Rpb25Gb3JTdXJyb2dhdGVDaGFyYWN0ZXJzKGNtLCBhbmNob3IsIGhlYWQpO1xuICAgICAgICAgICAgdmltLnNlbCA9IHtcbiAgICAgICAgICAgICAgICBhbmNob3I6IG5ld1Bvc2l0aW9uLnN0YXJ0LFxuICAgICAgICAgICAgICAgIGhlYWQ6IG5ld1Bvc2l0aW9uLmVuZFxuICAgICAgICAgICAgfTtcbiAgICAgICAgICAgIENvZGVNaXJyb3Iuc2lnbmFsKGNtLCBcInZpbS1tb2RlLWNoYW5nZVwiLCB7IG1vZGU6IFwidmlzdWFsXCIsIHN1Yk1vZGU6IHZpbS52aXN1YWxMaW5lID8gXCJsaW5ld2lzZVwiIDogdmltLnZpc3VhbEJsb2NrID8gXCJibG9ja3dpc2VcIiA6IFwiXCIgfSk7XG4gICAgICAgICAgICB1cGRhdGVDbVNlbGVjdGlvbihjbSk7XG4gICAgICAgICAgICB1cGRhdGVNYXJrKGNtLCB2aW0sICc8JywgY3Vyc29yTWluKGFuY2hvciwgaGVhZCkpO1xuICAgICAgICAgICAgdXBkYXRlTWFyayhjbSwgdmltLCAnPicsIGN1cnNvck1heChhbmNob3IsIGhlYWQpKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmICh2aW0udmlzdWFsTGluZSBeIGFjdGlvbkFyZ3MubGluZXdpc2UgfHxcbiAgICAgICAgICAgIHZpbS52aXN1YWxCbG9jayBeIGFjdGlvbkFyZ3MuYmxvY2t3aXNlKSB7XG4gICAgICAgICAgICB2aW0udmlzdWFsTGluZSA9ICEhYWN0aW9uQXJncy5saW5ld2lzZTtcbiAgICAgICAgICAgIHZpbS52aXN1YWxCbG9jayA9ICEhYWN0aW9uQXJncy5ibG9ja3dpc2U7XG4gICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcInZpc3VhbFwiLCBzdWJNb2RlOiB2aW0udmlzdWFsTGluZSA/IFwibGluZXdpc2VcIiA6IHZpbS52aXN1YWxCbG9jayA/IFwiYmxvY2t3aXNlXCIgOiBcIlwiIH0pO1xuICAgICAgICAgICAgdXBkYXRlQ21TZWxlY3Rpb24oY20pO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgZXhpdFZpc3VhbE1vZGUoY20pO1xuICAgICAgICB9XG4gICAgfSxcbiAgICByZXNlbGVjdExhc3RTZWxlY3Rpb246IGZ1bmN0aW9uIChjbSwgX2FjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2YXIgbGFzdFNlbGVjdGlvbiA9IHZpbS5sYXN0U2VsZWN0aW9uO1xuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIHVwZGF0ZUxhc3RTZWxlY3Rpb24oY20sIHZpbSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGxhc3RTZWxlY3Rpb24pIHtcbiAgICAgICAgICAgIHZhciBhbmNob3IgPSBsYXN0U2VsZWN0aW9uLmFuY2hvck1hcmsuZmluZCgpO1xuICAgICAgICAgICAgdmFyIGhlYWQgPSBsYXN0U2VsZWN0aW9uLmhlYWRNYXJrLmZpbmQoKTtcbiAgICAgICAgICAgIGlmICghYW5jaG9yIHx8ICFoZWFkKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmltLnNlbCA9IHtcbiAgICAgICAgICAgICAgICBhbmNob3I6IGFuY2hvcixcbiAgICAgICAgICAgICAgICBoZWFkOiBoZWFkXG4gICAgICAgICAgICB9O1xuICAgICAgICAgICAgdmltLnZpc3VhbE1vZGUgPSB0cnVlO1xuICAgICAgICAgICAgdmltLnZpc3VhbExpbmUgPSBsYXN0U2VsZWN0aW9uLnZpc3VhbExpbmU7XG4gICAgICAgICAgICB2aW0udmlzdWFsQmxvY2sgPSBsYXN0U2VsZWN0aW9uLnZpc3VhbEJsb2NrO1xuICAgICAgICAgICAgdXBkYXRlQ21TZWxlY3Rpb24oY20pO1xuICAgICAgICAgICAgdXBkYXRlTWFyayhjbSwgdmltLCAnPCcsIGN1cnNvck1pbihhbmNob3IsIGhlYWQpKTtcbiAgICAgICAgICAgIHVwZGF0ZU1hcmsoY20sIHZpbSwgJz4nLCBjdXJzb3JNYXgoYW5jaG9yLCBoZWFkKSk7XG4gICAgICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgJ3ZpbS1tb2RlLWNoYW5nZScsIHtcbiAgICAgICAgICAgICAgICBtb2RlOiAndmlzdWFsJyxcbiAgICAgICAgICAgICAgICBzdWJNb2RlOiB2aW0udmlzdWFsTGluZSA/ICdsaW5ld2lzZScgOlxuICAgICAgICAgICAgICAgICAgICB2aW0udmlzdWFsQmxvY2sgPyAnYmxvY2t3aXNlJyA6ICcnXG4gICAgICAgICAgICB9KTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgam9pbkxpbmVzOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2YXIgY3VyU3RhcnQsIGN1ckVuZDtcbiAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICBjdXJTdGFydCA9IGNtLmdldEN1cnNvcignYW5jaG9yJyk7XG4gICAgICAgICAgICBjdXJFbmQgPSBjbS5nZXRDdXJzb3IoJ2hlYWQnKTtcbiAgICAgICAgICAgIGlmIChjdXJzb3JJc0JlZm9yZShjdXJFbmQsIGN1clN0YXJ0KSkge1xuICAgICAgICAgICAgICAgIHZhciB0bXAgPSBjdXJFbmQ7XG4gICAgICAgICAgICAgICAgY3VyRW5kID0gY3VyU3RhcnQ7XG4gICAgICAgICAgICAgICAgY3VyU3RhcnQgPSB0bXA7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjdXJFbmQuY2ggPSBsaW5lTGVuZ3RoKGNtLCBjdXJFbmQubGluZSkgLSAxO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdmFyIHJlcGVhdCA9IE1hdGgubWF4KGFjdGlvbkFyZ3MucmVwZWF0LCAyKTtcbiAgICAgICAgICAgIGN1clN0YXJ0ID0gY20uZ2V0Q3Vyc29yKCk7XG4gICAgICAgICAgICBjdXJFbmQgPSBjbGlwQ3Vyc29yVG9Db250ZW50KGNtLCBuZXcgUG9zKGN1clN0YXJ0LmxpbmUgKyByZXBlYXQgLSAxLCBJbmZpbml0eSkpO1xuICAgICAgICB9XG4gICAgICAgIHZhciBmaW5hbENoID0gMDtcbiAgICAgICAgZm9yICh2YXIgaSA9IGN1clN0YXJ0LmxpbmU7IGkgPCBjdXJFbmQubGluZTsgaSsrKSB7XG4gICAgICAgICAgICBmaW5hbENoID0gbGluZUxlbmd0aChjbSwgY3VyU3RhcnQubGluZSk7XG4gICAgICAgICAgICB2YXIgdGV4dCA9ICcnO1xuICAgICAgICAgICAgdmFyIG5leHRTdGFydENoID0gMDtcbiAgICAgICAgICAgIGlmICghYWN0aW9uQXJncy5rZWVwU3BhY2VzKSB7XG4gICAgICAgICAgICAgICAgdmFyIG5leHRMaW5lID0gY20uZ2V0TGluZShjdXJTdGFydC5saW5lICsgMSk7XG4gICAgICAgICAgICAgICAgbmV4dFN0YXJ0Q2ggPSBuZXh0TGluZS5zZWFyY2goL1xcUy8pO1xuICAgICAgICAgICAgICAgIGlmIChuZXh0U3RhcnRDaCA9PSAtMSkge1xuICAgICAgICAgICAgICAgICAgICBuZXh0U3RhcnRDaCA9IG5leHRMaW5lLmxlbmd0aDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIHRleHQgPSBcIiBcIjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UodGV4dCwgbmV3IFBvcyhjdXJTdGFydC5saW5lLCBmaW5hbENoKSwgbmV3IFBvcyhjdXJTdGFydC5saW5lICsgMSwgbmV4dFN0YXJ0Q2gpKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgY3VyRmluYWxQb3MgPSBjbGlwQ3Vyc29yVG9Db250ZW50KGNtLCBuZXcgUG9zKGN1clN0YXJ0LmxpbmUsIGZpbmFsQ2gpKTtcbiAgICAgICAgaWYgKHZpbS52aXN1YWxNb2RlKSB7XG4gICAgICAgICAgICBleGl0VmlzdWFsTW9kZShjbSwgZmFsc2UpO1xuICAgICAgICB9XG4gICAgICAgIGNtLnNldEN1cnNvcihjdXJGaW5hbFBvcyk7XG4gICAgfSxcbiAgICBuZXdMaW5lQW5kRW50ZXJJbnNlcnRNb2RlOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2aW0uaW5zZXJ0TW9kZSA9IHRydWU7XG4gICAgICAgIHZhciBpbnNlcnRBdCA9IGNvcHlDdXJzb3IoY20uZ2V0Q3Vyc29yKCkpO1xuICAgICAgICBpZiAoaW5zZXJ0QXQubGluZSA9PT0gY20uZmlyc3RMaW5lKCkgJiYgIWFjdGlvbkFyZ3MuYWZ0ZXIpIHtcbiAgICAgICAgICAgIGNtLnJlcGxhY2VSYW5nZSgnXFxuJywgbmV3IFBvcyhjbS5maXJzdExpbmUoKSwgMCkpO1xuICAgICAgICAgICAgY20uc2V0Q3Vyc29yKGNtLmZpcnN0TGluZSgpLCAwKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGluc2VydEF0LmxpbmUgPSAoYWN0aW9uQXJncy5hZnRlcikgPyBpbnNlcnRBdC5saW5lIDpcbiAgICAgICAgICAgICAgICBpbnNlcnRBdC5saW5lIC0gMTtcbiAgICAgICAgICAgIGluc2VydEF0LmNoID0gbGluZUxlbmd0aChjbSwgaW5zZXJ0QXQubGluZSk7XG4gICAgICAgICAgICBjbS5zZXRDdXJzb3IoaW5zZXJ0QXQpO1xuICAgICAgICAgICAgdmFyIG5ld2xpbmVGbiA9IENvZGVNaXJyb3IuY29tbWFuZHMubmV3bGluZUFuZEluZGVudENvbnRpbnVlQ29tbWVudCB8fFxuICAgICAgICAgICAgICAgIENvZGVNaXJyb3IuY29tbWFuZHMubmV3bGluZUFuZEluZGVudDtcbiAgICAgICAgICAgIG5ld2xpbmVGbihjbSk7XG4gICAgICAgIH1cbiAgICAgICAgdGhpcy5lbnRlckluc2VydE1vZGUoY20sIHsgcmVwZWF0OiBhY3Rpb25BcmdzLnJlcGVhdCB9LCB2aW0pO1xuICAgIH0sXG4gICAgcGFzdGU6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciBfdGhpcyA9IHRoaXM7XG4gICAgICAgIHZhciByZWdpc3RlciA9IHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5nZXRSZWdpc3RlcihhY3Rpb25BcmdzLnJlZ2lzdGVyTmFtZSk7XG4gICAgICAgIHZhciBmYWxsYmFjayA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgIHZhciB0ZXh0ID0gcmVnaXN0ZXIudG9TdHJpbmcoKTtcbiAgICAgICAgICAgIF90aGlzLmNvbnRpbnVlUGFzdGUoY20sIGFjdGlvbkFyZ3MsIHZpbSwgdGV4dCwgcmVnaXN0ZXIpO1xuICAgICAgICB9O1xuICAgICAgICBpZiAoYWN0aW9uQXJncy5yZWdpc3Rlck5hbWUgPT09ICcrJyAmJlxuICAgICAgICAgICAgdHlwZW9mIG5hdmlnYXRvciAhPT0gJ3VuZGVmaW5lZCcgJiZcbiAgICAgICAgICAgIHR5cGVvZiBuYXZpZ2F0b3IuY2xpcGJvYXJkICE9PSAndW5kZWZpbmVkJyAmJlxuICAgICAgICAgICAgdHlwZW9mIG5hdmlnYXRvci5jbGlwYm9hcmQucmVhZFRleHQgPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgIG5hdmlnYXRvci5jbGlwYm9hcmQucmVhZFRleHQoKS50aGVuKGZ1bmN0aW9uICh2YWx1ZSkge1xuICAgICAgICAgICAgICAgIF90aGlzLmNvbnRpbnVlUGFzdGUoY20sIGFjdGlvbkFyZ3MsIHZpbSwgdmFsdWUsIHJlZ2lzdGVyKTtcbiAgICAgICAgICAgIH0sIGZ1bmN0aW9uICgpIHsgZmFsbGJhY2soKTsgfSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBmYWxsYmFjaygpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBjb250aW51ZVBhc3RlOiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSwgdGV4dCwgcmVnaXN0ZXIpIHtcbiAgICAgICAgdmFyIGN1ciA9IGNvcHlDdXJzb3IoY20uZ2V0Q3Vyc29yKCkpO1xuICAgICAgICBpZiAoIXRleHQpIHtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBpZiAoYWN0aW9uQXJncy5tYXRjaEluZGVudCkge1xuICAgICAgICAgICAgdmFyIHRhYlNpemUgPSBjbS5nZXRPcHRpb24oXCJ0YWJTaXplXCIpO1xuICAgICAgICAgICAgdmFyIHdoaXRlc3BhY2VMZW5ndGggPSBmdW5jdGlvbiAoc3RyKSB7XG4gICAgICAgICAgICAgICAgdmFyIHRhYnMgPSAoc3RyLnNwbGl0KFwiXFx0XCIpLmxlbmd0aCAtIDEpO1xuICAgICAgICAgICAgICAgIHZhciBzcGFjZXMgPSAoc3RyLnNwbGl0KFwiIFwiKS5sZW5ndGggLSAxKTtcbiAgICAgICAgICAgICAgICByZXR1cm4gdGFicyAqIHRhYlNpemUgKyBzcGFjZXMgKiAxO1xuICAgICAgICAgICAgfTtcbiAgICAgICAgICAgIHZhciBjdXJyZW50TGluZSA9IGNtLmdldExpbmUoY20uZ2V0Q3Vyc29yKCkubGluZSk7XG4gICAgICAgICAgICB2YXIgaW5kZW50ID0gd2hpdGVzcGFjZUxlbmd0aChjdXJyZW50TGluZS5tYXRjaCgvXlxccyovKVswXSk7XG4gICAgICAgICAgICB2YXIgY2hvbXBlZFRleHQgPSB0ZXh0LnJlcGxhY2UoL1xcbiQvLCAnJyk7XG4gICAgICAgICAgICB2YXIgd2FzQ2hvbXBlZCA9IHRleHQgIT09IGNob21wZWRUZXh0O1xuICAgICAgICAgICAgdmFyIGZpcnN0SW5kZW50ID0gd2hpdGVzcGFjZUxlbmd0aCh0ZXh0Lm1hdGNoKC9eXFxzKi8pWzBdKTtcbiAgICAgICAgICAgIHZhciB0ZXh0ID0gY2hvbXBlZFRleHQucmVwbGFjZSgvXlxccyovZ20sIGZ1bmN0aW9uICh3c3BhY2UpIHtcbiAgICAgICAgICAgICAgICB2YXIgbmV3SW5kZW50ID0gaW5kZW50ICsgKHdoaXRlc3BhY2VMZW5ndGgod3NwYWNlKSAtIGZpcnN0SW5kZW50KTtcbiAgICAgICAgICAgICAgICBpZiAobmV3SW5kZW50IDwgMCkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gXCJcIjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY20uZ2V0T3B0aW9uKFwiaW5kZW50V2l0aFRhYnNcIikpIHtcbiAgICAgICAgICAgICAgICAgICAgdmFyIHF1b3RpZW50ID0gTWF0aC5mbG9vcihuZXdJbmRlbnQgLyB0YWJTaXplKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIEFycmF5KHF1b3RpZW50ICsgMSkuam9pbignXFx0Jyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gQXJyYXkobmV3SW5kZW50ICsgMSkuam9pbignICcpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgdGV4dCArPSB3YXNDaG9tcGVkID8gXCJcXG5cIiA6IFwiXCI7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGFjdGlvbkFyZ3MucmVwZWF0ID4gMSkge1xuICAgICAgICAgICAgdmFyIHRleHQgPSBBcnJheShhY3Rpb25BcmdzLnJlcGVhdCArIDEpLmpvaW4odGV4dCk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGxpbmV3aXNlID0gcmVnaXN0ZXIubGluZXdpc2U7XG4gICAgICAgIHZhciBibG9ja3dpc2UgPSByZWdpc3Rlci5ibG9ja3dpc2U7XG4gICAgICAgIGlmIChibG9ja3dpc2UpIHtcbiAgICAgICAgICAgIHRleHQgPSB0ZXh0LnNwbGl0KCdcXG4nKTtcbiAgICAgICAgICAgIGlmIChsaW5ld2lzZSkge1xuICAgICAgICAgICAgICAgIHRleHQucG9wKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHRleHQubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICB0ZXh0W2ldID0gKHRleHRbaV0gPT0gJycpID8gJyAnIDogdGV4dFtpXTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGN1ci5jaCArPSBhY3Rpb25BcmdzLmFmdGVyID8gMSA6IDA7XG4gICAgICAgICAgICBjdXIuY2ggPSBNYXRoLm1pbihsaW5lTGVuZ3RoKGNtLCBjdXIubGluZSksIGN1ci5jaCk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAobGluZXdpc2UpIHtcbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgICAgIHRleHQgPSB2aW0udmlzdWFsTGluZSA/IHRleHQuc2xpY2UoMCwgLTEpIDogJ1xcbicgKyB0ZXh0LnNsaWNlKDAsIHRleHQubGVuZ3RoIC0gMSkgKyAnXFxuJztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGFjdGlvbkFyZ3MuYWZ0ZXIpIHtcbiAgICAgICAgICAgICAgICB0ZXh0ID0gJ1xcbicgKyB0ZXh0LnNsaWNlKDAsIHRleHQubGVuZ3RoIC0gMSk7XG4gICAgICAgICAgICAgICAgY3VyLmNoID0gbGluZUxlbmd0aChjbSwgY3VyLmxpbmUpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgY3VyLmNoID0gMDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGN1ci5jaCArPSBhY3Rpb25BcmdzLmFmdGVyID8gMSA6IDA7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGN1clBvc0ZpbmFsO1xuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIHZpbS5sYXN0UGFzdGVkVGV4dCA9IHRleHQ7XG4gICAgICAgICAgICB2YXIgbGFzdFNlbGVjdGlvbkN1ckVuZDtcbiAgICAgICAgICAgIHZhciBzZWxlY3RlZEFyZWEgPSBnZXRTZWxlY3RlZEFyZWFSYW5nZShjbSwgdmltKTtcbiAgICAgICAgICAgIHZhciBzZWxlY3Rpb25TdGFydCA9IHNlbGVjdGVkQXJlYVswXTtcbiAgICAgICAgICAgIHZhciBzZWxlY3Rpb25FbmQgPSBzZWxlY3RlZEFyZWFbMV07XG4gICAgICAgICAgICB2YXIgc2VsZWN0ZWRUZXh0ID0gY20uZ2V0U2VsZWN0aW9uKCk7XG4gICAgICAgICAgICB2YXIgc2VsZWN0aW9ucyA9IGNtLmxpc3RTZWxlY3Rpb25zKCk7XG4gICAgICAgICAgICB2YXIgZW1wdHlTdHJpbmdzID0gbmV3IEFycmF5KHNlbGVjdGlvbnMubGVuZ3RoKS5qb2luKCcxJykuc3BsaXQoJzEnKTtcbiAgICAgICAgICAgIGlmICh2aW0ubGFzdFNlbGVjdGlvbikge1xuICAgICAgICAgICAgICAgIGxhc3RTZWxlY3Rpb25DdXJFbmQgPSB2aW0ubGFzdFNlbGVjdGlvbi5oZWFkTWFyay5maW5kKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIudW5uYW1lZFJlZ2lzdGVyLnNldFRleHQoc2VsZWN0ZWRUZXh0KTtcbiAgICAgICAgICAgIGlmIChibG9ja3dpc2UpIHtcbiAgICAgICAgICAgICAgICBjbS5yZXBsYWNlU2VsZWN0aW9ucyhlbXB0eVN0cmluZ3MpO1xuICAgICAgICAgICAgICAgIHNlbGVjdGlvbkVuZCA9IG5ldyBQb3Moc2VsZWN0aW9uU3RhcnQubGluZSArIHRleHQubGVuZ3RoIC0gMSwgc2VsZWN0aW9uU3RhcnQuY2gpO1xuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihzZWxlY3Rpb25TdGFydCk7XG4gICAgICAgICAgICAgICAgc2VsZWN0QmxvY2soY20sIHNlbGVjdGlvbkVuZCk7XG4gICAgICAgICAgICAgICAgY20ucmVwbGFjZVNlbGVjdGlvbnModGV4dCk7XG4gICAgICAgICAgICAgICAgY3VyUG9zRmluYWwgPSBzZWxlY3Rpb25TdGFydDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKHZpbS52aXN1YWxCbG9jaykge1xuICAgICAgICAgICAgICAgIGNtLnJlcGxhY2VTZWxlY3Rpb25zKGVtcHR5U3RyaW5ncyk7XG4gICAgICAgICAgICAgICAgY20uc2V0Q3Vyc29yKHNlbGVjdGlvblN0YXJ0KTtcbiAgICAgICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UodGV4dCwgc2VsZWN0aW9uU3RhcnQsIHNlbGVjdGlvblN0YXJ0KTtcbiAgICAgICAgICAgICAgICBjdXJQb3NGaW5hbCA9IHNlbGVjdGlvblN0YXJ0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgY20ucmVwbGFjZVJhbmdlKHRleHQsIHNlbGVjdGlvblN0YXJ0LCBzZWxlY3Rpb25FbmQpO1xuICAgICAgICAgICAgICAgIGN1clBvc0ZpbmFsID0gY20ucG9zRnJvbUluZGV4KGNtLmluZGV4RnJvbVBvcyhzZWxlY3Rpb25TdGFydCkgKyB0ZXh0Lmxlbmd0aCAtIDEpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGxhc3RTZWxlY3Rpb25DdXJFbmQpIHtcbiAgICAgICAgICAgICAgICB2aW0ubGFzdFNlbGVjdGlvbi5oZWFkTWFyayA9IGNtLnNldEJvb2ttYXJrKGxhc3RTZWxlY3Rpb25DdXJFbmQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGxpbmV3aXNlKSB7XG4gICAgICAgICAgICAgICAgY3VyUG9zRmluYWwuY2ggPSAwO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgaWYgKGJsb2Nrd2lzZSkge1xuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihjdXIpO1xuICAgICAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdGV4dC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgICAgICB2YXIgbGluZSA9IGN1ci5saW5lICsgaTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGxpbmUgPiBjbS5sYXN0TGluZSgpKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoJ1xcbicsIG5ldyBQb3MobGluZSwgMCkpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHZhciBsYXN0Q2ggPSBsaW5lTGVuZ3RoKGNtLCBsaW5lKTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGxhc3RDaCA8IGN1ci5jaCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgZXh0ZW5kTGluZVRvQ29sdW1uKGNtLCBsaW5lLCBjdXIuY2gpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihjdXIpO1xuICAgICAgICAgICAgICAgIHNlbGVjdEJsb2NrKGNtLCBuZXcgUG9zKGN1ci5saW5lICsgdGV4dC5sZW5ndGggLSAxLCBjdXIuY2gpKTtcbiAgICAgICAgICAgICAgICBjbS5yZXBsYWNlU2VsZWN0aW9ucyh0ZXh0KTtcbiAgICAgICAgICAgICAgICBjdXJQb3NGaW5hbCA9IGN1cjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGNtLnJlcGxhY2VSYW5nZSh0ZXh0LCBjdXIpO1xuICAgICAgICAgICAgICAgIGlmIChsaW5ld2lzZSkge1xuICAgICAgICAgICAgICAgICAgICB2YXIgbGluZSA9IGFjdGlvbkFyZ3MuYWZ0ZXIgPyBjdXIubGluZSArIDEgOiBjdXIubGluZTtcbiAgICAgICAgICAgICAgICAgICAgY3VyUG9zRmluYWwgPSBuZXcgUG9zKGxpbmUsIGZpbmRGaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIoY20uZ2V0TGluZShsaW5lKSkpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgY3VyUG9zRmluYWwgPSBjb3B5Q3Vyc29yKGN1cik7XG4gICAgICAgICAgICAgICAgICAgIGlmICghL1xcbi8udGVzdCh0ZXh0KSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgY3VyUG9zRmluYWwuY2ggKz0gdGV4dC5sZW5ndGggLSAoYWN0aW9uQXJncy5hZnRlciA/IDEgOiAwKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIGV4aXRWaXN1YWxNb2RlKGNtLCBmYWxzZSk7XG4gICAgICAgIH1cbiAgICAgICAgY20uc2V0Q3Vyc29yKGN1clBvc0ZpbmFsKTtcbiAgICB9LFxuICAgIHVuZG86IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncykge1xuICAgICAgICBjbS5vcGVyYXRpb24oZnVuY3Rpb24gKCkge1xuICAgICAgICAgICAgcmVwZWF0Rm4oY20sIENvZGVNaXJyb3IuY29tbWFuZHMudW5kbywgYWN0aW9uQXJncy5yZXBlYXQpKCk7XG4gICAgICAgICAgICBjbS5zZXRDdXJzb3IoY2xpcEN1cnNvclRvQ29udGVudChjbSwgY20uZ2V0Q3Vyc29yKCdzdGFydCcpKSk7XG4gICAgICAgIH0pO1xuICAgIH0sXG4gICAgcmVkbzogZnVuY3Rpb24gKGNtLCBhY3Rpb25BcmdzKSB7XG4gICAgICAgIHJlcGVhdEZuKGNtLCBDb2RlTWlycm9yLmNvbW1hbmRzLnJlZG8sIGFjdGlvbkFyZ3MucmVwZWF0KSgpO1xuICAgIH0sXG4gICAgc2V0UmVnaXN0ZXI6IGZ1bmN0aW9uIChfY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgICAgICB2aW0uaW5wdXRTdGF0ZS5yZWdpc3Rlck5hbWUgPSBhY3Rpb25BcmdzLnNlbGVjdGVkQ2hhcmFjdGVyO1xuICAgIH0sXG4gICAgaW5zZXJ0UmVnaXN0ZXI6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciByZWdpc3Rlck5hbWUgPSBhY3Rpb25BcmdzLnNlbGVjdGVkQ2hhcmFjdGVyO1xuICAgICAgICB2YXIgcmVnaXN0ZXIgPSB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIuZ2V0UmVnaXN0ZXIocmVnaXN0ZXJOYW1lKTtcbiAgICAgICAgdmFyIHRleHQgPSByZWdpc3RlciAmJiByZWdpc3Rlci50b1N0cmluZygpO1xuICAgICAgICBpZiAodGV4dCkge1xuICAgICAgICAgICAgY20ucmVwbGFjZVNlbGVjdGlvbih0ZXh0KTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgb25lTm9ybWFsQ29tbWFuZDogZnVuY3Rpb24gKGNtLCBhY3Rpb25BcmdzLCB2aW0pIHtcbiAgICAgICAgZXhpdEluc2VydE1vZGUoY20sIHRydWUpO1xuICAgICAgICB2aW0uaW5zZXJ0TW9kZVJldHVybiA9IHRydWU7XG4gICAgICAgIENvZGVNaXJyb3Iub24oY20sICd2aW0tY29tbWFuZC1kb25lJywgZnVuY3Rpb24gaGFuZGxlcigpIHtcbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSlcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICBpZiAodmltLmluc2VydE1vZGVSZXR1cm4pIHtcbiAgICAgICAgICAgICAgICB2aW0uaW5zZXJ0TW9kZVJldHVybiA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIGlmICghdmltLmluc2VydE1vZGUpIHtcbiAgICAgICAgICAgICAgICAgICAgYWN0aW9ucy5lbnRlckluc2VydE1vZGUoY20sIHt9LCB2aW0pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIENvZGVNaXJyb3Iub2ZmKGNtLCAndmltLWNvbW1hbmQtZG9uZScsIGhhbmRsZXIpO1xuICAgICAgICB9KTtcbiAgICB9LFxuICAgIHNldE1hcms6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciBtYXJrTmFtZSA9IGFjdGlvbkFyZ3Muc2VsZWN0ZWRDaGFyYWN0ZXI7XG4gICAgICAgIHVwZGF0ZU1hcmsoY20sIHZpbSwgbWFya05hbWUsIGNtLmdldEN1cnNvcigpKTtcbiAgICB9LFxuICAgIHJlcGxhY2U6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciByZXBsYWNlV2l0aCA9IGFjdGlvbkFyZ3Muc2VsZWN0ZWRDaGFyYWN0ZXI7XG4gICAgICAgIHZhciBjdXJTdGFydCA9IGNtLmdldEN1cnNvcigpO1xuICAgICAgICB2YXIgcmVwbGFjZVRvO1xuICAgICAgICB2YXIgY3VyRW5kO1xuICAgICAgICB2YXIgc2VsZWN0aW9ucyA9IGNtLmxpc3RTZWxlY3Rpb25zKCk7XG4gICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgY3VyU3RhcnQgPSBjbS5nZXRDdXJzb3IoJ3N0YXJ0Jyk7XG4gICAgICAgICAgICBjdXJFbmQgPSBjbS5nZXRDdXJzb3IoJ2VuZCcpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGN1clN0YXJ0LmxpbmUpO1xuICAgICAgICAgICAgcmVwbGFjZVRvID0gY3VyU3RhcnQuY2ggKyBhY3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgICAgIGlmIChyZXBsYWNlVG8gPiBsaW5lLmxlbmd0aCkge1xuICAgICAgICAgICAgICAgIHJlcGxhY2VUbyA9IGxpbmUubGVuZ3RoO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY3VyRW5kID0gbmV3IFBvcyhjdXJTdGFydC5saW5lLCByZXBsYWNlVG8pO1xuICAgICAgICB9XG4gICAgICAgIHZhciBuZXdQb3NpdGlvbnMgPSB1cGRhdGVTZWxlY3Rpb25Gb3JTdXJyb2dhdGVDaGFyYWN0ZXJzKGNtLCBjdXJTdGFydCwgY3VyRW5kKTtcbiAgICAgICAgY3VyU3RhcnQgPSBuZXdQb3NpdGlvbnMuc3RhcnQ7XG4gICAgICAgIGN1ckVuZCA9IG5ld1Bvc2l0aW9ucy5lbmQ7XG4gICAgICAgIGlmIChyZXBsYWNlV2l0aCA9PSAnXFxuJykge1xuICAgICAgICAgICAgaWYgKCF2aW0udmlzdWFsTW9kZSlcbiAgICAgICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoJycsIGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgICAgICAgICAgKENvZGVNaXJyb3IuY29tbWFuZHMubmV3bGluZUFuZEluZGVudENvbnRpbnVlQ29tbWVudCB8fCBDb2RlTWlycm9yLmNvbW1hbmRzLm5ld2xpbmVBbmRJbmRlbnQpKGNtKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhciByZXBsYWNlV2l0aFN0ciA9IGNtLmdldFJhbmdlKGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgICAgICAgICAgcmVwbGFjZVdpdGhTdHIgPSByZXBsYWNlV2l0aFN0ci5yZXBsYWNlKC9bXFx1RDgwMC1cXHVEQkZGXVtcXHVEQzAwLVxcdURGRkZdL2csIHJlcGxhY2VXaXRoKTtcbiAgICAgICAgICAgIHJlcGxhY2VXaXRoU3RyID0gcmVwbGFjZVdpdGhTdHIucmVwbGFjZSgvW15cXG5dL2csIHJlcGxhY2VXaXRoKTtcbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsQmxvY2spIHtcbiAgICAgICAgICAgICAgICB2YXIgc3BhY2VzID0gbmV3IEFycmF5KGNtLmdldE9wdGlvbihcInRhYlNpemVcIikgKyAxKS5qb2luKCcgJyk7XG4gICAgICAgICAgICAgICAgcmVwbGFjZVdpdGhTdHIgPSBjbS5nZXRTZWxlY3Rpb24oKTtcbiAgICAgICAgICAgICAgICByZXBsYWNlV2l0aFN0ciA9IHJlcGxhY2VXaXRoU3RyLnJlcGxhY2UoL1tcXHVEODAwLVxcdURCRkZdW1xcdURDMDAtXFx1REZGRl0vZywgcmVwbGFjZVdpdGgpO1xuICAgICAgICAgICAgICAgIHJlcGxhY2VXaXRoU3RyID0gcmVwbGFjZVdpdGhTdHIucmVwbGFjZSgvXFx0L2csIHNwYWNlcykucmVwbGFjZSgvW15cXG5dL2csIHJlcGxhY2VXaXRoKS5zcGxpdCgnXFxuJyk7XG4gICAgICAgICAgICAgICAgY20ucmVwbGFjZVNlbGVjdGlvbnMocmVwbGFjZVdpdGhTdHIpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgY20ucmVwbGFjZVJhbmdlKHJlcGxhY2VXaXRoU3RyLCBjdXJTdGFydCwgY3VyRW5kKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmICh2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICAgICAgICAgIGN1clN0YXJ0ID0gY3Vyc29ySXNCZWZvcmUoc2VsZWN0aW9uc1swXS5hbmNob3IsIHNlbGVjdGlvbnNbMF0uaGVhZCkgP1xuICAgICAgICAgICAgICAgICAgICBzZWxlY3Rpb25zWzBdLmFuY2hvciA6IHNlbGVjdGlvbnNbMF0uaGVhZDtcbiAgICAgICAgICAgICAgICBjbS5zZXRDdXJzb3IoY3VyU3RhcnQpO1xuICAgICAgICAgICAgICAgIGV4aXRWaXN1YWxNb2RlKGNtLCBmYWxzZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBjbS5zZXRDdXJzb3Iob2Zmc2V0Q3Vyc29yKGN1ckVuZCwgMCwgLTEpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sXG4gICAgaW5jcmVtZW50TnVtYmVyVG9rZW46IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncykge1xuICAgICAgICB2YXIgY3VyID0gY20uZ2V0Q3Vyc29yKCk7XG4gICAgICAgIHZhciBsaW5lU3RyID0gY20uZ2V0TGluZShjdXIubGluZSk7XG4gICAgICAgIHZhciByZSA9IC8oLT8pKD86KDB4KShbXFxkYS1mXSspfCgwYnwwfCkoXFxkKykpL2dpO1xuICAgICAgICB2YXIgbWF0Y2g7XG4gICAgICAgIHZhciBzdGFydDtcbiAgICAgICAgdmFyIGVuZDtcbiAgICAgICAgdmFyIG51bWJlclN0cjtcbiAgICAgICAgd2hpbGUgKChtYXRjaCA9IHJlLmV4ZWMobGluZVN0cikpICE9PSBudWxsKSB7XG4gICAgICAgICAgICBzdGFydCA9IG1hdGNoLmluZGV4O1xuICAgICAgICAgICAgZW5kID0gc3RhcnQgKyBtYXRjaFswXS5sZW5ndGg7XG4gICAgICAgICAgICBpZiAoY3VyLmNoIDwgZW5kKVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICB9XG4gICAgICAgIGlmICghYWN0aW9uQXJncy5iYWNrdHJhY2sgJiYgKGVuZCA8PSBjdXIuY2gpKVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICBpZiAobWF0Y2gpIHtcbiAgICAgICAgICAgIHZhciBiYXNlU3RyID0gbWF0Y2hbMl0gfHwgbWF0Y2hbNF07XG4gICAgICAgICAgICB2YXIgZGlnaXRzID0gbWF0Y2hbM10gfHwgbWF0Y2hbNV07XG4gICAgICAgICAgICB2YXIgaW5jcmVtZW50ID0gYWN0aW9uQXJncy5pbmNyZWFzZSA/IDEgOiAtMTtcbiAgICAgICAgICAgIHZhciBiYXNlID0geyAnMGInOiAyLCAnMCc6IDgsICcnOiAxMCwgJzB4JzogMTYgfVtiYXNlU3RyLnRvTG93ZXJDYXNlKCldO1xuICAgICAgICAgICAgdmFyIG51bWJlciA9IHBhcnNlSW50KG1hdGNoWzFdICsgZGlnaXRzLCBiYXNlKSArIChpbmNyZW1lbnQgKiBhY3Rpb25BcmdzLnJlcGVhdCk7XG4gICAgICAgICAgICBudW1iZXJTdHIgPSBudW1iZXIudG9TdHJpbmcoYmFzZSk7XG4gICAgICAgICAgICB2YXIgemVyb1BhZGRpbmcgPSBiYXNlU3RyID8gbmV3IEFycmF5KGRpZ2l0cy5sZW5ndGggLSBudW1iZXJTdHIubGVuZ3RoICsgMSArIG1hdGNoWzFdLmxlbmd0aCkuam9pbignMCcpIDogJyc7XG4gICAgICAgICAgICBpZiAobnVtYmVyU3RyLmNoYXJBdCgwKSA9PT0gJy0nKSB7XG4gICAgICAgICAgICAgICAgbnVtYmVyU3RyID0gJy0nICsgYmFzZVN0ciArIHplcm9QYWRkaW5nICsgbnVtYmVyU3RyLnN1YnN0cigxKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIG51bWJlclN0ciA9IGJhc2VTdHIgKyB6ZXJvUGFkZGluZyArIG51bWJlclN0cjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZhciBmcm9tID0gbmV3IFBvcyhjdXIubGluZSwgc3RhcnQpO1xuICAgICAgICAgICAgdmFyIHRvID0gbmV3IFBvcyhjdXIubGluZSwgZW5kKTtcbiAgICAgICAgICAgIGNtLnJlcGxhY2VSYW5nZShudW1iZXJTdHIsIGZyb20sIHRvKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBjbS5zZXRDdXJzb3IobmV3IFBvcyhjdXIubGluZSwgc3RhcnQgKyBudW1iZXJTdHIubGVuZ3RoIC0gMSkpO1xuICAgIH0sXG4gICAgcmVwZWF0TGFzdEVkaXQ6IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgICAgIHZhciBsYXN0RWRpdElucHV0U3RhdGUgPSB2aW0ubGFzdEVkaXRJbnB1dFN0YXRlO1xuICAgICAgICBpZiAoIWxhc3RFZGl0SW5wdXRTdGF0ZSkge1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIHZhciByZXBlYXQgPSBhY3Rpb25BcmdzLnJlcGVhdDtcbiAgICAgICAgaWYgKHJlcGVhdCAmJiBhY3Rpb25BcmdzLnJlcGVhdElzRXhwbGljaXQpIHtcbiAgICAgICAgICAgIHZpbS5sYXN0RWRpdElucHV0U3RhdGUucmVwZWF0T3ZlcnJpZGUgPSByZXBlYXQ7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICByZXBlYXQgPSB2aW0ubGFzdEVkaXRJbnB1dFN0YXRlLnJlcGVhdE92ZXJyaWRlIHx8IHJlcGVhdDtcbiAgICAgICAgfVxuICAgICAgICByZXBlYXRMYXN0RWRpdChjbSwgdmltLCByZXBlYXQsIGZhbHNlIC8qKiByZXBlYXRGb3JJbnNlcnQgKi8pO1xuICAgIH0sXG4gICAgaW5kZW50OiBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MpIHtcbiAgICAgICAgY20uaW5kZW50TGluZShjbS5nZXRDdXJzb3IoKS5saW5lLCBhY3Rpb25BcmdzLmluZGVudFJpZ2h0KTtcbiAgICB9LFxuICAgIGV4aXRJbnNlcnRNb2RlOiBleGl0SW5zZXJ0TW9kZVxufTtcbmZ1bmN0aW9uIGRlZmluZUFjdGlvbihuYW1lLCBmbikge1xuICAgIGFjdGlvbnNbbmFtZV0gPSBmbjtcbn1cbmZ1bmN0aW9uIGNsaXBDdXJzb3JUb0NvbnRlbnQoY20sIGN1ciwgb2xkQ3VyKSB7XG4gICAgdmFyIHZpbSA9IGNtLnN0YXRlLnZpbTtcbiAgICB2YXIgaW5jbHVkZUxpbmVCcmVhayA9IHZpbS5pbnNlcnRNb2RlIHx8IHZpbS52aXN1YWxNb2RlO1xuICAgIHZhciBsaW5lID0gTWF0aC5taW4oTWF0aC5tYXgoY20uZmlyc3RMaW5lKCksIGN1ci5saW5lKSwgY20ubGFzdExpbmUoKSk7XG4gICAgdmFyIHRleHQgPSBjbS5nZXRMaW5lKGxpbmUpO1xuICAgIHZhciBtYXhDaCA9IHRleHQubGVuZ3RoIC0gMSArIE51bWJlcighIWluY2x1ZGVMaW5lQnJlYWspO1xuICAgIHZhciBjaCA9IE1hdGgubWluKE1hdGgubWF4KDAsIGN1ci5jaCksIG1heENoKTtcbiAgICB2YXIgY2hhckNvZGUgPSB0ZXh0LmNoYXJDb2RlQXQoY2gpO1xuICAgIGlmICgweERDMDAgPD0gY2hhckNvZGUgJiYgY2hhckNvZGUgPD0gMHhERkZGKSB7XG4gICAgICAgIHZhciBkaXJlY3Rpb24gPSAxO1xuICAgICAgICBpZiAob2xkQ3VyICYmIG9sZEN1ci5saW5lID09IGxpbmUgJiYgb2xkQ3VyLmNoID4gY2gpIHtcbiAgICAgICAgICAgIGRpcmVjdGlvbiA9IC0xO1xuICAgICAgICB9XG4gICAgICAgIGNoICs9IGRpcmVjdGlvbjtcbiAgICAgICAgaWYgKGNoID4gbWF4Q2gpXG4gICAgICAgICAgICBjaCAtPSAyO1xuICAgIH1cbiAgICByZXR1cm4gbmV3IFBvcyhsaW5lLCBjaCk7XG59XG5mdW5jdGlvbiBjb3B5QXJncyhhcmdzKSB7XG4gICAgdmFyIHJldCA9IHt9O1xuICAgIGZvciAodmFyIHByb3AgaW4gYXJncykge1xuICAgICAgICBpZiAoYXJncy5oYXNPd25Qcm9wZXJ0eShwcm9wKSkge1xuICAgICAgICAgICAgcmV0W3Byb3BdID0gYXJnc1twcm9wXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcmV0O1xufVxuZnVuY3Rpb24gb2Zmc2V0Q3Vyc29yKGN1ciwgb2Zmc2V0TGluZSwgb2Zmc2V0Q2gpIHtcbiAgICBpZiAodHlwZW9mIG9mZnNldExpbmUgPT09ICdvYmplY3QnKSB7XG4gICAgICAgIG9mZnNldENoID0gb2Zmc2V0TGluZS5jaDtcbiAgICAgICAgb2Zmc2V0TGluZSA9IG9mZnNldExpbmUubGluZTtcbiAgICB9XG4gICAgcmV0dXJuIG5ldyBQb3MoY3VyLmxpbmUgKyBvZmZzZXRMaW5lLCBjdXIuY2ggKyBvZmZzZXRDaCk7XG59XG5mdW5jdGlvbiBjb21tYW5kTWF0Y2hlcyhrZXlzLCBrZXlNYXAsIGNvbnRleHQsIGlucHV0U3RhdGUpIHtcbiAgICBpZiAoaW5wdXRTdGF0ZS5vcGVyYXRvcilcbiAgICAgICAgY29udGV4dCA9IFwib3BlcmF0b3JQZW5kaW5nXCI7XG4gICAgdmFyIG1hdGNoLCBwYXJ0aWFsID0gW10sIGZ1bGwgPSBbXTtcbiAgICB2YXIgc3RhcnRJbmRleCA9IG5vcmVtYXAgPyBrZXlNYXAubGVuZ3RoIC0gZGVmYXVsdEtleW1hcExlbmd0aCA6IDA7XG4gICAgZm9yICh2YXIgaSA9IHN0YXJ0SW5kZXg7IGkgPCBrZXlNYXAubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIGNvbW1hbmQgPSBrZXlNYXBbaV07XG4gICAgICAgIGlmIChjb250ZXh0ID09ICdpbnNlcnQnICYmIGNvbW1hbmQuY29udGV4dCAhPSAnaW5zZXJ0JyB8fFxuICAgICAgICAgICAgKGNvbW1hbmQuY29udGV4dCAmJiBjb21tYW5kLmNvbnRleHQgIT0gY29udGV4dCkgfHxcbiAgICAgICAgICAgIGlucHV0U3RhdGUub3BlcmF0b3IgJiYgY29tbWFuZC50eXBlID09ICdhY3Rpb24nIHx8XG4gICAgICAgICAgICAhKG1hdGNoID0gY29tbWFuZE1hdGNoKGtleXMsIGNvbW1hbmQua2V5cykpKSB7XG4gICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAobWF0Y2ggPT0gJ3BhcnRpYWwnKSB7XG4gICAgICAgICAgICBwYXJ0aWFsLnB1c2goY29tbWFuZCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG1hdGNoID09ICdmdWxsJykge1xuICAgICAgICAgICAgZnVsbC5wdXNoKGNvbW1hbmQpO1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiB7XG4gICAgICAgIHBhcnRpYWw6IHBhcnRpYWwubGVuZ3RoICYmIHBhcnRpYWwsXG4gICAgICAgIGZ1bGw6IGZ1bGwubGVuZ3RoICYmIGZ1bGxcbiAgICB9O1xufVxuZnVuY3Rpb24gY29tbWFuZE1hdGNoKHByZXNzZWQsIG1hcHBlZCkge1xuICAgIHZhciBpc0xhc3RDaGFyYWN0ZXIgPSBtYXBwZWQuc2xpY2UoLTExKSA9PSAnPGNoYXJhY3Rlcj4nO1xuICAgIHZhciBpc0xhc3RSZWdpc3RlciA9IG1hcHBlZC5zbGljZSgtMTApID09ICc8cmVnaXN0ZXI+JztcbiAgICBpZiAoaXNMYXN0Q2hhcmFjdGVyIHx8IGlzTGFzdFJlZ2lzdGVyKSB7XG4gICAgICAgIHZhciBwcmVmaXhMZW4gPSBtYXBwZWQubGVuZ3RoIC0gKGlzTGFzdENoYXJhY3RlciA/IDExIDogMTApO1xuICAgICAgICB2YXIgcHJlc3NlZFByZWZpeCA9IHByZXNzZWQuc2xpY2UoMCwgcHJlZml4TGVuKTtcbiAgICAgICAgdmFyIG1hcHBlZFByZWZpeCA9IG1hcHBlZC5zbGljZSgwLCBwcmVmaXhMZW4pO1xuICAgICAgICByZXR1cm4gcHJlc3NlZFByZWZpeCA9PSBtYXBwZWRQcmVmaXggJiYgcHJlc3NlZC5sZW5ndGggPiBwcmVmaXhMZW4gPyAnZnVsbCcgOlxuICAgICAgICAgICAgbWFwcGVkUHJlZml4LmluZGV4T2YocHJlc3NlZFByZWZpeCkgPT0gMCA/ICdwYXJ0aWFsJyA6IGZhbHNlO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgcmV0dXJuIHByZXNzZWQgPT0gbWFwcGVkID8gJ2Z1bGwnIDpcbiAgICAgICAgICAgIG1hcHBlZC5pbmRleE9mKHByZXNzZWQpID09IDAgPyAncGFydGlhbCcgOiBmYWxzZTtcbiAgICB9XG59XG5mdW5jdGlvbiBsYXN0Q2hhcihrZXlzKSB7XG4gICAgdmFyIG1hdGNoID0gL14uKig8W14+XSs+KSQvLmV4ZWMoa2V5cyk7XG4gICAgdmFyIHNlbGVjdGVkQ2hhcmFjdGVyID0gbWF0Y2ggPyBtYXRjaFsxXSA6IGtleXMuc2xpY2UoLTEpO1xuICAgIGlmIChzZWxlY3RlZENoYXJhY3Rlci5sZW5ndGggPiAxKSB7XG4gICAgICAgIHN3aXRjaCAoc2VsZWN0ZWRDaGFyYWN0ZXIpIHtcbiAgICAgICAgICAgIGNhc2UgJzxDUj4nOlxuICAgICAgICAgICAgICAgIHNlbGVjdGVkQ2hhcmFjdGVyID0gJ1xcbic7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICc8U3BhY2U+JzpcbiAgICAgICAgICAgICAgICBzZWxlY3RlZENoYXJhY3RlciA9ICcgJztcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICAgICAgc2VsZWN0ZWRDaGFyYWN0ZXIgPSAnJztcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gc2VsZWN0ZWRDaGFyYWN0ZXI7XG59XG5mdW5jdGlvbiByZXBlYXRGbihjbSwgZm4sIHJlcGVhdCkge1xuICAgIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcmVwZWF0OyBpKyspIHtcbiAgICAgICAgICAgIGZuKGNtKTtcbiAgICAgICAgfVxuICAgIH07XG59XG5mdW5jdGlvbiBjb3B5Q3Vyc29yKGN1cikge1xuICAgIHJldHVybiBuZXcgUG9zKGN1ci5saW5lLCBjdXIuY2gpO1xufVxuZnVuY3Rpb24gY3Vyc29yRXF1YWwoY3VyMSwgY3VyMikge1xuICAgIHJldHVybiBjdXIxLmNoID09IGN1cjIuY2ggJiYgY3VyMS5saW5lID09IGN1cjIubGluZTtcbn1cbmZ1bmN0aW9uIGN1cnNvcklzQmVmb3JlKGN1cjEsIGN1cjIpIHtcbiAgICBpZiAoY3VyMS5saW5lIDwgY3VyMi5saW5lKSB7XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICBpZiAoY3VyMS5saW5lID09IGN1cjIubGluZSAmJiBjdXIxLmNoIDwgY3VyMi5jaCkge1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufVxuZnVuY3Rpb24gY3Vyc29yTWluKGN1cjEsIGN1cjIpIHtcbiAgICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+IDIpIHtcbiAgICAgICAgY3VyMiA9IGN1cnNvck1pbi5hcHBseSh1bmRlZmluZWQsIEFycmF5LnByb3RvdHlwZS5zbGljZS5jYWxsKGFyZ3VtZW50cywgMSkpO1xuICAgIH1cbiAgICByZXR1cm4gY3Vyc29ySXNCZWZvcmUoY3VyMSwgY3VyMikgPyBjdXIxIDogY3VyMjtcbn1cbmZ1bmN0aW9uIGN1cnNvck1heChjdXIxLCBjdXIyKSB7XG4gICAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPiAyKSB7XG4gICAgICAgIGN1cjIgPSBjdXJzb3JNYXguYXBwbHkodW5kZWZpbmVkLCBBcnJheS5wcm90b3R5cGUuc2xpY2UuY2FsbChhcmd1bWVudHMsIDEpKTtcbiAgICB9XG4gICAgcmV0dXJuIGN1cnNvcklzQmVmb3JlKGN1cjEsIGN1cjIpID8gY3VyMiA6IGN1cjE7XG59XG5mdW5jdGlvbiBjdXJzb3JJc0JldHdlZW4oY3VyMSwgY3VyMiwgY3VyMykge1xuICAgIHZhciBjdXIxYmVmb3JlMiA9IGN1cnNvcklzQmVmb3JlKGN1cjEsIGN1cjIpO1xuICAgIHZhciBjdXIyYmVmb3JlMyA9IGN1cnNvcklzQmVmb3JlKGN1cjIsIGN1cjMpO1xuICAgIHJldHVybiBjdXIxYmVmb3JlMiAmJiBjdXIyYmVmb3JlMztcbn1cbmZ1bmN0aW9uIGxpbmVMZW5ndGgoY20sIGxpbmVOdW0pIHtcbiAgICByZXR1cm4gY20uZ2V0TGluZShsaW5lTnVtKS5sZW5ndGg7XG59XG5mdW5jdGlvbiB0cmltKHMpIHtcbiAgICBpZiAocy50cmltKSB7XG4gICAgICAgIHJldHVybiBzLnRyaW0oKTtcbiAgICB9XG4gICAgcmV0dXJuIHMucmVwbGFjZSgvXlxccyt8XFxzKyQvZywgJycpO1xufVxuZnVuY3Rpb24gZXNjYXBlUmVnZXgocykge1xuICAgIHJldHVybiBzLnJlcGxhY2UoLyhbLj8qKyRcXFtcXF1cXC9cXFxcKCl7fXxcXC1dKS9nLCAnXFxcXCQxJyk7XG59XG5mdW5jdGlvbiBleHRlbmRMaW5lVG9Db2x1bW4oY20sIGxpbmVOdW0sIGNvbHVtbikge1xuICAgIHZhciBlbmRDaCA9IGxpbmVMZW5ndGgoY20sIGxpbmVOdW0pO1xuICAgIHZhciBzcGFjZXMgPSBuZXcgQXJyYXkoY29sdW1uIC0gZW5kQ2ggKyAxKS5qb2luKCcgJyk7XG4gICAgY20uc2V0Q3Vyc29yKG5ldyBQb3MobGluZU51bSwgZW5kQ2gpKTtcbiAgICBjbS5yZXBsYWNlUmFuZ2Uoc3BhY2VzLCBjbS5nZXRDdXJzb3IoKSk7XG59XG5mdW5jdGlvbiBzZWxlY3RCbG9jayhjbSwgc2VsZWN0aW9uRW5kKSB7XG4gICAgdmFyIHNlbGVjdGlvbnMgPSBbXSwgcmFuZ2VzID0gY20ubGlzdFNlbGVjdGlvbnMoKTtcbiAgICB2YXIgaGVhZCA9IGNvcHlDdXJzb3IoY20uY2xpcFBvcyhzZWxlY3Rpb25FbmQpKTtcbiAgICB2YXIgaXNDbGlwcGVkID0gIWN1cnNvckVxdWFsKHNlbGVjdGlvbkVuZCwgaGVhZCk7XG4gICAgdmFyIGN1ckhlYWQgPSBjbS5nZXRDdXJzb3IoJ2hlYWQnKTtcbiAgICB2YXIgcHJpbUluZGV4ID0gZ2V0SW5kZXgocmFuZ2VzLCBjdXJIZWFkKTtcbiAgICB2YXIgd2FzQ2xpcHBlZCA9IGN1cnNvckVxdWFsKHJhbmdlc1twcmltSW5kZXhdLmhlYWQsIHJhbmdlc1twcmltSW5kZXhdLmFuY2hvcik7XG4gICAgdmFyIG1heCA9IHJhbmdlcy5sZW5ndGggLSAxO1xuICAgIHZhciBpbmRleCA9IG1heCAtIHByaW1JbmRleCA+IHByaW1JbmRleCA/IG1heCA6IDA7XG4gICAgdmFyIGJhc2UgPSByYW5nZXNbaW5kZXhdLmFuY2hvcjtcbiAgICB2YXIgZmlyc3RMaW5lID0gTWF0aC5taW4oYmFzZS5saW5lLCBoZWFkLmxpbmUpO1xuICAgIHZhciBsYXN0TGluZSA9IE1hdGgubWF4KGJhc2UubGluZSwgaGVhZC5saW5lKTtcbiAgICB2YXIgYmFzZUNoID0gYmFzZS5jaCwgaGVhZENoID0gaGVhZC5jaDtcbiAgICB2YXIgZGlyID0gcmFuZ2VzW2luZGV4XS5oZWFkLmNoIC0gYmFzZUNoO1xuICAgIHZhciBuZXdEaXIgPSBoZWFkQ2ggLSBiYXNlQ2g7XG4gICAgaWYgKGRpciA+IDAgJiYgbmV3RGlyIDw9IDApIHtcbiAgICAgICAgYmFzZUNoKys7XG4gICAgICAgIGlmICghaXNDbGlwcGVkKSB7XG4gICAgICAgICAgICBoZWFkQ2gtLTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBlbHNlIGlmIChkaXIgPCAwICYmIG5ld0RpciA+PSAwKSB7XG4gICAgICAgIGJhc2VDaC0tO1xuICAgICAgICBpZiAoIXdhc0NsaXBwZWQpIHtcbiAgICAgICAgICAgIGhlYWRDaCsrO1xuICAgICAgICB9XG4gICAgfVxuICAgIGVsc2UgaWYgKGRpciA8IDAgJiYgbmV3RGlyID09IC0xKSB7XG4gICAgICAgIGJhc2VDaC0tO1xuICAgICAgICBoZWFkQ2grKztcbiAgICB9XG4gICAgZm9yICh2YXIgbGluZSA9IGZpcnN0TGluZTsgbGluZSA8PSBsYXN0TGluZTsgbGluZSsrKSB7XG4gICAgICAgIHZhciByYW5nZSA9IHsgYW5jaG9yOiBuZXcgUG9zKGxpbmUsIGJhc2VDaCksIGhlYWQ6IG5ldyBQb3MobGluZSwgaGVhZENoKSB9O1xuICAgICAgICBzZWxlY3Rpb25zLnB1c2gocmFuZ2UpO1xuICAgIH1cbiAgICBjbS5zZXRTZWxlY3Rpb25zKHNlbGVjdGlvbnMpO1xuICAgIHNlbGVjdGlvbkVuZC5jaCA9IGhlYWRDaDtcbiAgICBiYXNlLmNoID0gYmFzZUNoO1xuICAgIHJldHVybiBiYXNlO1xufVxuZnVuY3Rpb24gc2VsZWN0Rm9ySW5zZXJ0KGNtLCBoZWFkLCBoZWlnaHQpIHtcbiAgICB2YXIgc2VsID0gW107XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBoZWlnaHQ7IGkrKykge1xuICAgICAgICB2YXIgbGluZUhlYWQgPSBvZmZzZXRDdXJzb3IoaGVhZCwgaSwgMCk7XG4gICAgICAgIHNlbC5wdXNoKHsgYW5jaG9yOiBsaW5lSGVhZCwgaGVhZDogbGluZUhlYWQgfSk7XG4gICAgfVxuICAgIGNtLnNldFNlbGVjdGlvbnMoc2VsLCAwKTtcbn1cbmZ1bmN0aW9uIGdldEluZGV4KHJhbmdlcywgY3Vyc29yLCBlbmQpIHtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJhbmdlcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgYXRBbmNob3IgPSBlbmQgIT0gJ2hlYWQnICYmIGN1cnNvckVxdWFsKHJhbmdlc1tpXS5hbmNob3IsIGN1cnNvcik7XG4gICAgICAgIHZhciBhdEhlYWQgPSBlbmQgIT0gJ2FuY2hvcicgJiYgY3Vyc29yRXF1YWwocmFuZ2VzW2ldLmhlYWQsIGN1cnNvcik7XG4gICAgICAgIGlmIChhdEFuY2hvciB8fCBhdEhlYWQpIHtcbiAgICAgICAgICAgIHJldHVybiBpO1xuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiAtMTtcbn1cbmZ1bmN0aW9uIGdldFNlbGVjdGVkQXJlYVJhbmdlKGNtLCB2aW0pIHtcbiAgICB2YXIgbGFzdFNlbGVjdGlvbiA9IHZpbS5sYXN0U2VsZWN0aW9uO1xuICAgIHZhciBnZXRDdXJyZW50U2VsZWN0ZWRBcmVhUmFuZ2UgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHZhciBzZWxlY3Rpb25zID0gY20ubGlzdFNlbGVjdGlvbnMoKTtcbiAgICAgICAgdmFyIHN0YXJ0ID0gc2VsZWN0aW9uc1swXTtcbiAgICAgICAgdmFyIGVuZCA9IHNlbGVjdGlvbnNbc2VsZWN0aW9ucy5sZW5ndGggLSAxXTtcbiAgICAgICAgdmFyIHNlbGVjdGlvblN0YXJ0ID0gY3Vyc29ySXNCZWZvcmUoc3RhcnQuYW5jaG9yLCBzdGFydC5oZWFkKSA/IHN0YXJ0LmFuY2hvciA6IHN0YXJ0LmhlYWQ7XG4gICAgICAgIHZhciBzZWxlY3Rpb25FbmQgPSBjdXJzb3JJc0JlZm9yZShlbmQuYW5jaG9yLCBlbmQuaGVhZCkgPyBlbmQuaGVhZCA6IGVuZC5hbmNob3I7XG4gICAgICAgIHJldHVybiBbc2VsZWN0aW9uU3RhcnQsIHNlbGVjdGlvbkVuZF07XG4gICAgfTtcbiAgICB2YXIgZ2V0TGFzdFNlbGVjdGVkQXJlYVJhbmdlID0gZnVuY3Rpb24gKCkge1xuICAgICAgICB2YXIgc2VsZWN0aW9uU3RhcnQgPSBjbS5nZXRDdXJzb3IoKTtcbiAgICAgICAgdmFyIHNlbGVjdGlvbkVuZCA9IGNtLmdldEN1cnNvcigpO1xuICAgICAgICB2YXIgYmxvY2sgPSBsYXN0U2VsZWN0aW9uLnZpc3VhbEJsb2NrO1xuICAgICAgICBpZiAoYmxvY2spIHtcbiAgICAgICAgICAgIHZhciB3aWR0aCA9IGJsb2NrLndpZHRoO1xuICAgICAgICAgICAgdmFyIGhlaWdodCA9IGJsb2NrLmhlaWdodDtcbiAgICAgICAgICAgIHNlbGVjdGlvbkVuZCA9IG5ldyBQb3Moc2VsZWN0aW9uU3RhcnQubGluZSArIGhlaWdodCwgc2VsZWN0aW9uU3RhcnQuY2ggKyB3aWR0aCk7XG4gICAgICAgICAgICB2YXIgc2VsZWN0aW9ucyA9IFtdO1xuICAgICAgICAgICAgZm9yICh2YXIgaSA9IHNlbGVjdGlvblN0YXJ0LmxpbmU7IGkgPCBzZWxlY3Rpb25FbmQubGluZTsgaSsrKSB7XG4gICAgICAgICAgICAgICAgdmFyIGFuY2hvciA9IG5ldyBQb3MoaSwgc2VsZWN0aW9uU3RhcnQuY2gpO1xuICAgICAgICAgICAgICAgIHZhciBoZWFkID0gbmV3IFBvcyhpLCBzZWxlY3Rpb25FbmQuY2gpO1xuICAgICAgICAgICAgICAgIHZhciByYW5nZSA9IHsgYW5jaG9yOiBhbmNob3IsIGhlYWQ6IGhlYWQgfTtcbiAgICAgICAgICAgICAgICBzZWxlY3Rpb25zLnB1c2gocmFuZ2UpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY20uc2V0U2VsZWN0aW9ucyhzZWxlY3Rpb25zKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhciBzdGFydCA9IGxhc3RTZWxlY3Rpb24uYW5jaG9yTWFyay5maW5kKCk7XG4gICAgICAgICAgICB2YXIgZW5kID0gbGFzdFNlbGVjdGlvbi5oZWFkTWFyay5maW5kKCk7XG4gICAgICAgICAgICB2YXIgbGluZSA9IGVuZC5saW5lIC0gc3RhcnQubGluZTtcbiAgICAgICAgICAgIHZhciBjaCA9IGVuZC5jaCAtIHN0YXJ0LmNoO1xuICAgICAgICAgICAgc2VsZWN0aW9uRW5kID0geyBsaW5lOiBzZWxlY3Rpb25FbmQubGluZSArIGxpbmUsIGNoOiBsaW5lID8gc2VsZWN0aW9uRW5kLmNoIDogY2ggKyBzZWxlY3Rpb25FbmQuY2ggfTtcbiAgICAgICAgICAgIGlmIChsYXN0U2VsZWN0aW9uLnZpc3VhbExpbmUpIHtcbiAgICAgICAgICAgICAgICBzZWxlY3Rpb25TdGFydCA9IG5ldyBQb3Moc2VsZWN0aW9uU3RhcnQubGluZSwgMCk7XG4gICAgICAgICAgICAgICAgc2VsZWN0aW9uRW5kID0gbmV3IFBvcyhzZWxlY3Rpb25FbmQubGluZSwgbGluZUxlbmd0aChjbSwgc2VsZWN0aW9uRW5kLmxpbmUpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNtLnNldFNlbGVjdGlvbihzZWxlY3Rpb25TdGFydCwgc2VsZWN0aW9uRW5kKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gW3NlbGVjdGlvblN0YXJ0LCBzZWxlY3Rpb25FbmRdO1xuICAgIH07XG4gICAgaWYgKCF2aW0udmlzdWFsTW9kZSkge1xuICAgICAgICByZXR1cm4gZ2V0TGFzdFNlbGVjdGVkQXJlYVJhbmdlKCk7XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICByZXR1cm4gZ2V0Q3VycmVudFNlbGVjdGVkQXJlYVJhbmdlKCk7XG4gICAgfVxufVxuZnVuY3Rpb24gdXBkYXRlTGFzdFNlbGVjdGlvbihjbSwgdmltKSB7XG4gICAgdmFyIGFuY2hvciA9IHZpbS5zZWwuYW5jaG9yO1xuICAgIHZhciBoZWFkID0gdmltLnNlbC5oZWFkO1xuICAgIGlmICh2aW0ubGFzdFBhc3RlZFRleHQpIHtcbiAgICAgICAgaGVhZCA9IGNtLnBvc0Zyb21JbmRleChjbS5pbmRleEZyb21Qb3MoYW5jaG9yKSArIHZpbS5sYXN0UGFzdGVkVGV4dC5sZW5ndGgpO1xuICAgICAgICB2aW0ubGFzdFBhc3RlZFRleHQgPSBudWxsO1xuICAgIH1cbiAgICB2aW0ubGFzdFNlbGVjdGlvbiA9IHsgJ2FuY2hvck1hcmsnOiBjbS5zZXRCb29rbWFyayhhbmNob3IpLFxuICAgICAgICAnaGVhZE1hcmsnOiBjbS5zZXRCb29rbWFyayhoZWFkKSxcbiAgICAgICAgJ2FuY2hvcic6IGNvcHlDdXJzb3IoYW5jaG9yKSxcbiAgICAgICAgJ2hlYWQnOiBjb3B5Q3Vyc29yKGhlYWQpLFxuICAgICAgICAndmlzdWFsTW9kZSc6IHZpbS52aXN1YWxNb2RlLFxuICAgICAgICAndmlzdWFsTGluZSc6IHZpbS52aXN1YWxMaW5lLFxuICAgICAgICAndmlzdWFsQmxvY2snOiB2aW0udmlzdWFsQmxvY2sgfTtcbn1cbmZ1bmN0aW9uIGV4cGFuZFNlbGVjdGlvbihjbSwgc3RhcnQsIGVuZCwgbW92ZSkge1xuICAgIHZhciBzZWwgPSBjbS5zdGF0ZS52aW0uc2VsO1xuICAgIHZhciBoZWFkID0gbW92ZSA/IHN0YXJ0IDogc2VsLmhlYWQ7XG4gICAgdmFyIGFuY2hvciA9IG1vdmUgPyBzdGFydCA6IHNlbC5hbmNob3I7XG4gICAgdmFyIHRtcDtcbiAgICBpZiAoY3Vyc29ySXNCZWZvcmUoZW5kLCBzdGFydCkpIHtcbiAgICAgICAgdG1wID0gZW5kO1xuICAgICAgICBlbmQgPSBzdGFydDtcbiAgICAgICAgc3RhcnQgPSB0bXA7XG4gICAgfVxuICAgIGlmIChjdXJzb3JJc0JlZm9yZShoZWFkLCBhbmNob3IpKSB7XG4gICAgICAgIGhlYWQgPSBjdXJzb3JNaW4oc3RhcnQsIGhlYWQpO1xuICAgICAgICBhbmNob3IgPSBjdXJzb3JNYXgoYW5jaG9yLCBlbmQpO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgYW5jaG9yID0gY3Vyc29yTWluKHN0YXJ0LCBhbmNob3IpO1xuICAgICAgICBoZWFkID0gY3Vyc29yTWF4KGhlYWQsIGVuZCk7XG4gICAgICAgIGhlYWQgPSBvZmZzZXRDdXJzb3IoaGVhZCwgMCwgLTEpO1xuICAgICAgICBpZiAoaGVhZC5jaCA9PSAtMSAmJiBoZWFkLmxpbmUgIT0gY20uZmlyc3RMaW5lKCkpIHtcbiAgICAgICAgICAgIGhlYWQgPSBuZXcgUG9zKGhlYWQubGluZSAtIDEsIGxpbmVMZW5ndGgoY20sIGhlYWQubGluZSAtIDEpKTtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gW2FuY2hvciwgaGVhZF07XG59XG5mdW5jdGlvbiB1cGRhdGVDbVNlbGVjdGlvbihjbSwgc2VsLCBtb2RlKSB7XG4gICAgdmFyIHZpbSA9IGNtLnN0YXRlLnZpbTtcbiAgICBzZWwgPSBzZWwgfHwgdmltLnNlbDtcbiAgICB2YXIgbW9kZSA9IG1vZGUgfHxcbiAgICAgICAgdmltLnZpc3VhbExpbmUgPyAnbGluZScgOiB2aW0udmlzdWFsQmxvY2sgPyAnYmxvY2snIDogJ2NoYXInO1xuICAgIHZhciBjbVNlbCA9IG1ha2VDbVNlbGVjdGlvbihjbSwgc2VsLCBtb2RlKTtcbiAgICBjbS5zZXRTZWxlY3Rpb25zKGNtU2VsLnJhbmdlcywgY21TZWwucHJpbWFyeSk7XG59XG5mdW5jdGlvbiBtYWtlQ21TZWxlY3Rpb24oY20sIHNlbCwgbW9kZSwgZXhjbHVzaXZlKSB7XG4gICAgdmFyIGhlYWQgPSBjb3B5Q3Vyc29yKHNlbC5oZWFkKTtcbiAgICB2YXIgYW5jaG9yID0gY29weUN1cnNvcihzZWwuYW5jaG9yKTtcbiAgICBpZiAobW9kZSA9PSAnY2hhcicpIHtcbiAgICAgICAgdmFyIGhlYWRPZmZzZXQgPSAhZXhjbHVzaXZlICYmICFjdXJzb3JJc0JlZm9yZShzZWwuaGVhZCwgc2VsLmFuY2hvcikgPyAxIDogMDtcbiAgICAgICAgdmFyIGFuY2hvck9mZnNldCA9IGN1cnNvcklzQmVmb3JlKHNlbC5oZWFkLCBzZWwuYW5jaG9yKSA/IDEgOiAwO1xuICAgICAgICBoZWFkID0gb2Zmc2V0Q3Vyc29yKHNlbC5oZWFkLCAwLCBoZWFkT2Zmc2V0KTtcbiAgICAgICAgYW5jaG9yID0gb2Zmc2V0Q3Vyc29yKHNlbC5hbmNob3IsIDAsIGFuY2hvck9mZnNldCk7XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICByYW5nZXM6IFt7IGFuY2hvcjogYW5jaG9yLCBoZWFkOiBoZWFkIH1dLFxuICAgICAgICAgICAgcHJpbWFyeTogMFxuICAgICAgICB9O1xuICAgIH1cbiAgICBlbHNlIGlmIChtb2RlID09ICdsaW5lJykge1xuICAgICAgICBpZiAoIWN1cnNvcklzQmVmb3JlKHNlbC5oZWFkLCBzZWwuYW5jaG9yKSkge1xuICAgICAgICAgICAgYW5jaG9yLmNoID0gMDtcbiAgICAgICAgICAgIHZhciBsYXN0TGluZSA9IGNtLmxhc3RMaW5lKCk7XG4gICAgICAgICAgICBpZiAoaGVhZC5saW5lID4gbGFzdExpbmUpIHtcbiAgICAgICAgICAgICAgICBoZWFkLmxpbmUgPSBsYXN0TGluZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGhlYWQuY2ggPSBsaW5lTGVuZ3RoKGNtLCBoZWFkLmxpbmUpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgaGVhZC5jaCA9IDA7XG4gICAgICAgICAgICBhbmNob3IuY2ggPSBsaW5lTGVuZ3RoKGNtLCBhbmNob3IubGluZSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgIHJhbmdlczogW3sgYW5jaG9yOiBhbmNob3IsIGhlYWQ6IGhlYWQgfV0sXG4gICAgICAgICAgICBwcmltYXJ5OiAwXG4gICAgICAgIH07XG4gICAgfVxuICAgIGVsc2UgaWYgKG1vZGUgPT0gJ2Jsb2NrJykge1xuICAgICAgICB2YXIgdG9wID0gTWF0aC5taW4oYW5jaG9yLmxpbmUsIGhlYWQubGluZSksIGZyb21DaCA9IGFuY2hvci5jaCwgYm90dG9tID0gTWF0aC5tYXgoYW5jaG9yLmxpbmUsIGhlYWQubGluZSksIHRvQ2ggPSBoZWFkLmNoO1xuICAgICAgICBpZiAoZnJvbUNoIDwgdG9DaCkge1xuICAgICAgICAgICAgdG9DaCArPSAxO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgZnJvbUNoICs9IDE7XG4gICAgICAgIH1cbiAgICAgICAgO1xuICAgICAgICB2YXIgaGVpZ2h0ID0gYm90dG9tIC0gdG9wICsgMTtcbiAgICAgICAgdmFyIHByaW1hcnkgPSBoZWFkLmxpbmUgPT0gdG9wID8gMCA6IGhlaWdodCAtIDE7XG4gICAgICAgIHZhciByYW5nZXMgPSBbXTtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBoZWlnaHQ7IGkrKykge1xuICAgICAgICAgICAgcmFuZ2VzLnB1c2goe1xuICAgICAgICAgICAgICAgIGFuY2hvcjogbmV3IFBvcyh0b3AgKyBpLCBmcm9tQ2gpLFxuICAgICAgICAgICAgICAgIGhlYWQ6IG5ldyBQb3ModG9wICsgaSwgdG9DaClcbiAgICAgICAgICAgIH0pO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICByYW5nZXM6IHJhbmdlcyxcbiAgICAgICAgICAgIHByaW1hcnk6IHByaW1hcnlcbiAgICAgICAgfTtcbiAgICB9XG59XG5mdW5jdGlvbiBnZXRIZWFkKGNtKSB7XG4gICAgdmFyIGN1ciA9IGNtLmdldEN1cnNvcignaGVhZCcpO1xuICAgIGlmIChjbS5nZXRTZWxlY3Rpb24oKS5sZW5ndGggPT0gMSkge1xuICAgICAgICBjdXIgPSBjdXJzb3JNaW4oY3VyLCBjbS5nZXRDdXJzb3IoJ2FuY2hvcicpKTtcbiAgICB9XG4gICAgcmV0dXJuIGN1cjtcbn1cbmZ1bmN0aW9uIGV4aXRWaXN1YWxNb2RlKGNtLCBtb3ZlSGVhZCkge1xuICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgaWYgKG1vdmVIZWFkICE9PSBmYWxzZSkge1xuICAgICAgICBjbS5zZXRDdXJzb3IoY2xpcEN1cnNvclRvQ29udGVudChjbSwgdmltLnNlbC5oZWFkKSk7XG4gICAgfVxuICAgIHVwZGF0ZUxhc3RTZWxlY3Rpb24oY20sIHZpbSk7XG4gICAgdmltLnZpc3VhbE1vZGUgPSBmYWxzZTtcbiAgICB2aW0udmlzdWFsTGluZSA9IGZhbHNlO1xuICAgIHZpbS52aXN1YWxCbG9jayA9IGZhbHNlO1xuICAgIGlmICghdmltLmluc2VydE1vZGUpXG4gICAgICAgIENvZGVNaXJyb3Iuc2lnbmFsKGNtLCBcInZpbS1tb2RlLWNoYW5nZVwiLCB7IG1vZGU6IFwibm9ybWFsXCIgfSk7XG59XG5mdW5jdGlvbiBjbGlwVG9MaW5lKGNtLCBjdXJTdGFydCwgY3VyRW5kKSB7XG4gICAgdmFyIHNlbGVjdGlvbiA9IGNtLmdldFJhbmdlKGN1clN0YXJ0LCBjdXJFbmQpO1xuICAgIGlmICgvXFxuXFxzKiQvLnRlc3Qoc2VsZWN0aW9uKSkge1xuICAgICAgICB2YXIgbGluZXMgPSBzZWxlY3Rpb24uc3BsaXQoJ1xcbicpO1xuICAgICAgICBsaW5lcy5wb3AoKTtcbiAgICAgICAgdmFyIGxpbmU7XG4gICAgICAgIGZvciAodmFyIGxpbmUgPSBsaW5lcy5wb3AoKTsgbGluZXMubGVuZ3RoID4gMCAmJiBsaW5lICYmIGlzV2hpdGVTcGFjZVN0cmluZyhsaW5lKTsgbGluZSA9IGxpbmVzLnBvcCgpKSB7XG4gICAgICAgICAgICBjdXJFbmQubGluZS0tO1xuICAgICAgICAgICAgY3VyRW5kLmNoID0gMDtcbiAgICAgICAgfVxuICAgICAgICBpZiAobGluZSkge1xuICAgICAgICAgICAgY3VyRW5kLmxpbmUtLTtcbiAgICAgICAgICAgIGN1ckVuZC5jaCA9IGxpbmVMZW5ndGgoY20sIGN1ckVuZC5saW5lKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGN1ckVuZC5jaCA9IDA7XG4gICAgICAgIH1cbiAgICB9XG59XG5mdW5jdGlvbiBleHBhbmRTZWxlY3Rpb25Ub0xpbmUoX2NtLCBjdXJTdGFydCwgY3VyRW5kKSB7XG4gICAgY3VyU3RhcnQuY2ggPSAwO1xuICAgIGN1ckVuZC5jaCA9IDA7XG4gICAgY3VyRW5kLmxpbmUrKztcbn1cbmZ1bmN0aW9uIGZpbmRGaXJzdE5vbldoaXRlU3BhY2VDaGFyYWN0ZXIodGV4dCkge1xuICAgIGlmICghdGV4dCkge1xuICAgICAgICByZXR1cm4gMDtcbiAgICB9XG4gICAgdmFyIGZpcnN0Tm9uV1MgPSB0ZXh0LnNlYXJjaCgvXFxTLyk7XG4gICAgcmV0dXJuIGZpcnN0Tm9uV1MgPT0gLTEgPyB0ZXh0Lmxlbmd0aCA6IGZpcnN0Tm9uV1M7XG59XG5mdW5jdGlvbiBleHBhbmRXb3JkVW5kZXJDdXJzb3IoY20sIF9hLCBjdXJzb3IpIHtcbiAgICB2YXIgaW5jbHVzaXZlID0gX2EuaW5jbHVzaXZlLCBpbm5lcldvcmQgPSBfYS5pbm5lcldvcmQsIGJpZ1dvcmQgPSBfYS5iaWdXb3JkLCBub1N5bWJvbCA9IF9hLm5vU3ltYm9sLCBtdWx0aWxpbmUgPSBfYS5tdWx0aWxpbmU7XG4gICAgdmFyIGN1ciA9IGN1cnNvciB8fCBnZXRIZWFkKGNtKTtcbiAgICB2YXIgbGluZSA9IGNtLmdldExpbmUoY3VyLmxpbmUpO1xuICAgIHZhciBlbmRMaW5lID0gbGluZTtcbiAgICB2YXIgc3RhcnRMaW5lTnVtYmVyID0gY3VyLmxpbmU7XG4gICAgdmFyIGVuZExpbmVOdW1iZXIgPSBzdGFydExpbmVOdW1iZXI7XG4gICAgdmFyIGlkeCA9IGN1ci5jaDtcbiAgICB2YXIgd29yZE9uTmV4dExpbmU7XG4gICAgdmFyIHRlc3QgPSBub1N5bWJvbCA/IHdvcmRDaGFyVGVzdFswXSA6IGJpZ1dvcmRDaGFyVGVzdFswXTtcbiAgICBpZiAoaW5uZXJXb3JkICYmIC9cXHMvLnRlc3QobGluZS5jaGFyQXQoaWR4KSkpIHtcbiAgICAgICAgdGVzdCA9IGZ1bmN0aW9uIChjaCkgeyByZXR1cm4gL1xccy8udGVzdChjaCk7IH07XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICB3aGlsZSAoIXRlc3QobGluZS5jaGFyQXQoaWR4KSkpIHtcbiAgICAgICAgICAgIGlkeCsrO1xuICAgICAgICAgICAgaWYgKGlkeCA+PSBsaW5lLmxlbmd0aCkge1xuICAgICAgICAgICAgICAgIGlmICghbXVsdGlsaW5lKVxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgICAgICAgICBpZHgtLTtcbiAgICAgICAgICAgICAgICB3b3JkT25OZXh0TGluZSA9IGZpbmRXb3JkKGNtLCBjdXIsIHRydWUsIGJpZ1dvcmQsIHRydWUpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChiaWdXb3JkKSB7XG4gICAgICAgICAgICB0ZXN0ID0gYmlnV29yZENoYXJUZXN0WzBdO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGVzdCA9IHdvcmRDaGFyVGVzdFswXTtcbiAgICAgICAgICAgIGlmICghdGVzdChsaW5lLmNoYXJBdChpZHgpKSkge1xuICAgICAgICAgICAgICAgIHRlc3QgPSB3b3JkQ2hhclRlc3RbMV07XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG4gICAgdmFyIGVuZCA9IGlkeCwgc3RhcnQgPSBpZHg7XG4gICAgd2hpbGUgKHRlc3QobGluZS5jaGFyQXQoc3RhcnQpKSAmJiBzdGFydCA+PSAwKSB7XG4gICAgICAgIHN0YXJ0LS07XG4gICAgfVxuICAgIHN0YXJ0Kys7XG4gICAgaWYgKHdvcmRPbk5leHRMaW5lKSB7XG4gICAgICAgIGVuZCA9IHdvcmRPbk5leHRMaW5lLnRvO1xuICAgICAgICBlbmRMaW5lTnVtYmVyID0gd29yZE9uTmV4dExpbmUubGluZTtcbiAgICAgICAgZW5kTGluZSA9IGNtLmdldExpbmUoZW5kTGluZU51bWJlcik7XG4gICAgICAgIGlmICghZW5kTGluZSAmJiBlbmQgPT0gMClcbiAgICAgICAgICAgIGVuZCsrO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgd2hpbGUgKHRlc3QobGluZS5jaGFyQXQoZW5kKSkgJiYgZW5kIDwgbGluZS5sZW5ndGgpIHtcbiAgICAgICAgICAgIGVuZCsrO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChpbmNsdXNpdmUpIHtcbiAgICAgICAgdmFyIHdvcmRFbmQgPSBlbmQ7XG4gICAgICAgIHZhciBzdGFydHNXaXRoU3BhY2UgPSBjdXIuY2ggPD0gc3RhcnQgJiYgL1xccy8udGVzdChsaW5lLmNoYXJBdChjdXIuY2gpKTtcbiAgICAgICAgaWYgKCFzdGFydHNXaXRoU3BhY2UpIHtcbiAgICAgICAgICAgIHdoaWxlICgvXFxzLy50ZXN0KGVuZExpbmUuY2hhckF0KGVuZCkpICYmIGVuZCA8IGVuZExpbmUubGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgZW5kKys7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHdvcmRFbmQgPT0gZW5kIHx8IHN0YXJ0c1dpdGhTcGFjZSkge1xuICAgICAgICAgICAgdmFyIHdvcmRTdGFydCA9IHN0YXJ0O1xuICAgICAgICAgICAgd2hpbGUgKC9cXHMvLnRlc3QobGluZS5jaGFyQXQoc3RhcnQgLSAxKSkgJiYgc3RhcnQgPiAwKSB7XG4gICAgICAgICAgICAgICAgc3RhcnQtLTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmICghc3RhcnQgJiYgIXN0YXJ0c1dpdGhTcGFjZSkge1xuICAgICAgICAgICAgICAgIHN0YXJ0ID0gd29yZFN0YXJ0O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiB7IHN0YXJ0OiBuZXcgUG9zKHN0YXJ0TGluZU51bWJlciwgc3RhcnQpLCBlbmQ6IG5ldyBQb3MoZW5kTGluZU51bWJlciwgZW5kKSB9O1xufVxuZnVuY3Rpb24gZXhwYW5kVGFnVW5kZXJDdXJzb3IoY20sIGhlYWQsIGluY2x1c2l2ZSkge1xuICAgIHZhciBjdXIgPSBoZWFkO1xuICAgIGlmICghQ29kZU1pcnJvci5maW5kTWF0Y2hpbmdUYWcgfHwgIUNvZGVNaXJyb3IuZmluZEVuY2xvc2luZ1RhZykge1xuICAgICAgICByZXR1cm4geyBzdGFydDogY3VyLCBlbmQ6IGN1ciB9O1xuICAgIH1cbiAgICB2YXIgdGFncyA9IENvZGVNaXJyb3IuZmluZE1hdGNoaW5nVGFnKGNtLCBoZWFkKSB8fCBDb2RlTWlycm9yLmZpbmRFbmNsb3NpbmdUYWcoY20sIGhlYWQpO1xuICAgIGlmICghdGFncyB8fCAhdGFncy5vcGVuIHx8ICF0YWdzLmNsb3NlKSB7XG4gICAgICAgIHJldHVybiB7IHN0YXJ0OiBjdXIsIGVuZDogY3VyIH07XG4gICAgfVxuICAgIGlmIChpbmNsdXNpdmUpIHtcbiAgICAgICAgcmV0dXJuIHsgc3RhcnQ6IHRhZ3Mub3Blbi5mcm9tLCBlbmQ6IHRhZ3MuY2xvc2UudG8gfTtcbiAgICB9XG4gICAgcmV0dXJuIHsgc3RhcnQ6IHRhZ3Mub3Blbi50bywgZW5kOiB0YWdzLmNsb3NlLmZyb20gfTtcbn1cbmZ1bmN0aW9uIHJlY29yZEp1bXBQb3NpdGlvbihjbSwgb2xkQ3VyLCBuZXdDdXIpIHtcbiAgICBpZiAoIWN1cnNvckVxdWFsKG9sZEN1ciwgbmV3Q3VyKSkge1xuICAgICAgICB2aW1HbG9iYWxTdGF0ZS5qdW1wTGlzdC5hZGQoY20sIG9sZEN1ciwgbmV3Q3VyKTtcbiAgICB9XG59XG5mdW5jdGlvbiByZWNvcmRMYXN0Q2hhcmFjdGVyU2VhcmNoKGluY3JlbWVudCwgYXJncykge1xuICAgIHZpbUdsb2JhbFN0YXRlLmxhc3RDaGFyYWN0ZXJTZWFyY2guaW5jcmVtZW50ID0gaW5jcmVtZW50O1xuICAgIHZpbUdsb2JhbFN0YXRlLmxhc3RDaGFyYWN0ZXJTZWFyY2guZm9yd2FyZCA9IGFyZ3MuZm9yd2FyZDtcbiAgICB2aW1HbG9iYWxTdGF0ZS5sYXN0Q2hhcmFjdGVyU2VhcmNoLnNlbGVjdGVkQ2hhcmFjdGVyID0gYXJncy5zZWxlY3RlZENoYXJhY3Rlcjtcbn1cbnZhciBzeW1ib2xUb01vZGUgPSB7XG4gICAgJygnOiAnYnJhY2tldCcsICcpJzogJ2JyYWNrZXQnLCAneyc6ICdicmFja2V0JywgJ30nOiAnYnJhY2tldCcsXG4gICAgJ1snOiAnc2VjdGlvbicsICddJzogJ3NlY3Rpb24nLFxuICAgICcqJzogJ2NvbW1lbnQnLCAnLyc6ICdjb21tZW50JyxcbiAgICAnbSc6ICdtZXRob2QnLCAnTSc6ICdtZXRob2QnLFxuICAgICcjJzogJ3ByZXByb2Nlc3MnXG59O1xudmFyIGZpbmRTeW1ib2xNb2RlcyA9IHtcbiAgICBicmFja2V0OiB7XG4gICAgICAgIGlzQ29tcGxldGU6IGZ1bmN0aW9uIChzdGF0ZSkge1xuICAgICAgICAgICAgaWYgKHN0YXRlLm5leHRDaCA9PT0gc3RhdGUuc3ltYikge1xuICAgICAgICAgICAgICAgIHN0YXRlLmRlcHRoKys7XG4gICAgICAgICAgICAgICAgaWYgKHN0YXRlLmRlcHRoID49IDEpXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoc3RhdGUubmV4dENoID09PSBzdGF0ZS5yZXZlcnNlU3ltYikge1xuICAgICAgICAgICAgICAgIHN0YXRlLmRlcHRoLS07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHNlY3Rpb246IHtcbiAgICAgICAgaW5pdDogZnVuY3Rpb24gKHN0YXRlKSB7XG4gICAgICAgICAgICBzdGF0ZS5jdXJNb3ZlVGhyb3VnaCA9IHRydWU7XG4gICAgICAgICAgICBzdGF0ZS5zeW1iID0gKHN0YXRlLmZvcndhcmQgPyAnXScgOiAnWycpID09PSBzdGF0ZS5zeW1iID8gJ3snIDogJ30nO1xuICAgICAgICB9LFxuICAgICAgICBpc0NvbXBsZXRlOiBmdW5jdGlvbiAoc3RhdGUpIHtcbiAgICAgICAgICAgIHJldHVybiBzdGF0ZS5pbmRleCA9PT0gMCAmJiBzdGF0ZS5uZXh0Q2ggPT09IHN0YXRlLnN5bWI7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIGNvbW1lbnQ6IHtcbiAgICAgICAgaXNDb21wbGV0ZTogZnVuY3Rpb24gKHN0YXRlKSB7XG4gICAgICAgICAgICB2YXIgZm91bmQgPSBzdGF0ZS5sYXN0Q2ggPT09ICcqJyAmJiBzdGF0ZS5uZXh0Q2ggPT09ICcvJztcbiAgICAgICAgICAgIHN0YXRlLmxhc3RDaCA9IHN0YXRlLm5leHRDaDtcbiAgICAgICAgICAgIHJldHVybiBmb3VuZDtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgbWV0aG9kOiB7XG4gICAgICAgIGluaXQ6IGZ1bmN0aW9uIChzdGF0ZSkge1xuICAgICAgICAgICAgc3RhdGUuc3ltYiA9IChzdGF0ZS5zeW1iID09PSAnbScgPyAneycgOiAnfScpO1xuICAgICAgICAgICAgc3RhdGUucmV2ZXJzZVN5bWIgPSBzdGF0ZS5zeW1iID09PSAneycgPyAnfScgOiAneyc7XG4gICAgICAgIH0sXG4gICAgICAgIGlzQ29tcGxldGU6IGZ1bmN0aW9uIChzdGF0ZSkge1xuICAgICAgICAgICAgaWYgKHN0YXRlLm5leHRDaCA9PT0gc3RhdGUuc3ltYilcbiAgICAgICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgcHJlcHJvY2Vzczoge1xuICAgICAgICBpbml0OiBmdW5jdGlvbiAoc3RhdGUpIHtcbiAgICAgICAgICAgIHN0YXRlLmluZGV4ID0gMDtcbiAgICAgICAgfSxcbiAgICAgICAgaXNDb21wbGV0ZTogZnVuY3Rpb24gKHN0YXRlKSB7XG4gICAgICAgICAgICBpZiAoc3RhdGUubmV4dENoID09PSAnIycpIHtcbiAgICAgICAgICAgICAgICB2YXIgdG9rZW4gPSBzdGF0ZS5saW5lVGV4dC5tYXRjaCgvXiMoXFx3KykvKVsxXTtcbiAgICAgICAgICAgICAgICBpZiAodG9rZW4gPT09ICdlbmRpZicpIHtcbiAgICAgICAgICAgICAgICAgICAgaWYgKHN0YXRlLmZvcndhcmQgJiYgc3RhdGUuZGVwdGggPT09IDApIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHN0YXRlLmRlcHRoKys7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKHRva2VuID09PSAnaWYnKSB7XG4gICAgICAgICAgICAgICAgICAgIGlmICghc3RhdGUuZm9yd2FyZCAmJiBzdGF0ZS5kZXB0aCA9PT0gMCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgc3RhdGUuZGVwdGgtLTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKHRva2VuID09PSAnZWxzZScgJiYgc3RhdGUuZGVwdGggPT09IDApXG4gICAgICAgICAgICAgICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICB9XG4gICAgfVxufTtcbmZ1bmN0aW9uIGZpbmRTeW1ib2woY20sIHJlcGVhdCwgZm9yd2FyZCwgc3ltYikge1xuICAgIHZhciBjdXIgPSBjb3B5Q3Vyc29yKGNtLmdldEN1cnNvcigpKTtcbiAgICB2YXIgaW5jcmVtZW50ID0gZm9yd2FyZCA/IDEgOiAtMTtcbiAgICB2YXIgZW5kTGluZSA9IGZvcndhcmQgPyBjbS5saW5lQ291bnQoKSA6IC0xO1xuICAgIHZhciBjdXJDaCA9IGN1ci5jaDtcbiAgICB2YXIgbGluZSA9IGN1ci5saW5lO1xuICAgIHZhciBsaW5lVGV4dCA9IGNtLmdldExpbmUobGluZSk7XG4gICAgdmFyIHN0YXRlID0ge1xuICAgICAgICBsaW5lVGV4dDogbGluZVRleHQsXG4gICAgICAgIG5leHRDaDogbGluZVRleHQuY2hhckF0KGN1ckNoKSxcbiAgICAgICAgbGFzdENoOiBudWxsLFxuICAgICAgICBpbmRleDogY3VyQ2gsXG4gICAgICAgIHN5bWI6IHN5bWIsXG4gICAgICAgIHJldmVyc2VTeW1iOiAoZm9yd2FyZCA/IHsgJyknOiAnKCcsICd9JzogJ3snIH0gOiB7ICcoJzogJyknLCAneyc6ICd9JyB9KVtzeW1iXSxcbiAgICAgICAgZm9yd2FyZDogZm9yd2FyZCxcbiAgICAgICAgZGVwdGg6IDAsXG4gICAgICAgIGN1ck1vdmVUaHJvdWdoOiBmYWxzZVxuICAgIH07XG4gICAgdmFyIG1vZGUgPSBzeW1ib2xUb01vZGVbc3ltYl07XG4gICAgaWYgKCFtb2RlKVxuICAgICAgICByZXR1cm4gY3VyO1xuICAgIHZhciBpbml0ID0gZmluZFN5bWJvbE1vZGVzW21vZGVdLmluaXQ7XG4gICAgdmFyIGlzQ29tcGxldGUgPSBmaW5kU3ltYm9sTW9kZXNbbW9kZV0uaXNDb21wbGV0ZTtcbiAgICBpZiAoaW5pdCkge1xuICAgICAgICBpbml0KHN0YXRlKTtcbiAgICB9XG4gICAgd2hpbGUgKGxpbmUgIT09IGVuZExpbmUgJiYgcmVwZWF0KSB7XG4gICAgICAgIHN0YXRlLmluZGV4ICs9IGluY3JlbWVudDtcbiAgICAgICAgc3RhdGUubmV4dENoID0gc3RhdGUubGluZVRleHQuY2hhckF0KHN0YXRlLmluZGV4KTtcbiAgICAgICAgaWYgKCFzdGF0ZS5uZXh0Q2gpIHtcbiAgICAgICAgICAgIGxpbmUgKz0gaW5jcmVtZW50O1xuICAgICAgICAgICAgc3RhdGUubGluZVRleHQgPSBjbS5nZXRMaW5lKGxpbmUpIHx8ICcnO1xuICAgICAgICAgICAgaWYgKGluY3JlbWVudCA+IDApIHtcbiAgICAgICAgICAgICAgICBzdGF0ZS5pbmRleCA9IDA7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB2YXIgbGluZUxlbiA9IHN0YXRlLmxpbmVUZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICBzdGF0ZS5pbmRleCA9IChsaW5lTGVuID4gMCkgPyAobGluZUxlbiAtIDEpIDogMDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHN0YXRlLm5leHRDaCA9IHN0YXRlLmxpbmVUZXh0LmNoYXJBdChzdGF0ZS5pbmRleCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGlzQ29tcGxldGUoc3RhdGUpKSB7XG4gICAgICAgICAgICBjdXIubGluZSA9IGxpbmU7XG4gICAgICAgICAgICBjdXIuY2ggPSBzdGF0ZS5pbmRleDtcbiAgICAgICAgICAgIHJlcGVhdC0tO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChzdGF0ZS5uZXh0Q2ggfHwgc3RhdGUuY3VyTW92ZVRocm91Z2gpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MobGluZSwgc3RhdGUuaW5kZXgpO1xuICAgIH1cbiAgICByZXR1cm4gY3VyO1xufVxuZnVuY3Rpb24gZmluZFdvcmQoY20sIGN1ciwgZm9yd2FyZCwgYmlnV29yZCwgZW1wdHlMaW5lSXNXb3JkKSB7XG4gICAgdmFyIGxpbmVOdW0gPSBjdXIubGluZTtcbiAgICB2YXIgcG9zID0gY3VyLmNoO1xuICAgIHZhciBsaW5lID0gY20uZ2V0TGluZShsaW5lTnVtKTtcbiAgICB2YXIgZGlyID0gZm9yd2FyZCA/IDEgOiAtMTtcbiAgICB2YXIgY2hhclRlc3RzID0gYmlnV29yZCA/IGJpZ1dvcmRDaGFyVGVzdCA6IHdvcmRDaGFyVGVzdDtcbiAgICBpZiAoZW1wdHlMaW5lSXNXb3JkICYmIGxpbmUgPT0gJycpIHtcbiAgICAgICAgbGluZU51bSArPSBkaXI7XG4gICAgICAgIGxpbmUgPSBjbS5nZXRMaW5lKGxpbmVOdW0pO1xuICAgICAgICBpZiAoIWlzTGluZShjbSwgbGluZU51bSkpIHtcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIHBvcyA9IChmb3J3YXJkKSA/IDAgOiBsaW5lLmxlbmd0aDtcbiAgICB9XG4gICAgd2hpbGUgKHRydWUpIHtcbiAgICAgICAgaWYgKGVtcHR5TGluZUlzV29yZCAmJiBsaW5lID09ICcnKSB7XG4gICAgICAgICAgICByZXR1cm4geyBmcm9tOiAwLCB0bzogMCwgbGluZTogbGluZU51bSB9O1xuICAgICAgICB9XG4gICAgICAgIHZhciBzdG9wID0gKGRpciA+IDApID8gbGluZS5sZW5ndGggOiAtMTtcbiAgICAgICAgdmFyIHdvcmRTdGFydCA9IHN0b3AsIHdvcmRFbmQgPSBzdG9wO1xuICAgICAgICB3aGlsZSAocG9zICE9IHN0b3ApIHtcbiAgICAgICAgICAgIHZhciBmb3VuZFdvcmQgPSBmYWxzZTtcbiAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgY2hhclRlc3RzLmxlbmd0aCAmJiAhZm91bmRXb3JkOyArK2kpIHtcbiAgICAgICAgICAgICAgICBpZiAoY2hhclRlc3RzW2ldKGxpbmUuY2hhckF0KHBvcykpKSB7XG4gICAgICAgICAgICAgICAgICAgIHdvcmRTdGFydCA9IHBvcztcbiAgICAgICAgICAgICAgICAgICAgd2hpbGUgKHBvcyAhPSBzdG9wICYmIGNoYXJUZXN0c1tpXShsaW5lLmNoYXJBdChwb3MpKSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgcG9zICs9IGRpcjtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB3b3JkRW5kID0gcG9zO1xuICAgICAgICAgICAgICAgICAgICBmb3VuZFdvcmQgPSB3b3JkU3RhcnQgIT0gd29yZEVuZDtcbiAgICAgICAgICAgICAgICAgICAgaWYgKHdvcmRTdGFydCA9PSBjdXIuY2ggJiYgbGluZU51bSA9PSBjdXIubGluZSAmJlxuICAgICAgICAgICAgICAgICAgICAgICAgd29yZEVuZCA9PSB3b3JkU3RhcnQgKyBkaXIpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBmcm9tOiBNYXRoLm1pbih3b3JkU3RhcnQsIHdvcmRFbmQgKyAxKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0bzogTWF0aC5tYXgod29yZFN0YXJ0LCB3b3JkRW5kKSxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBsaW5lOiBsaW5lTnVtXG4gICAgICAgICAgICAgICAgICAgICAgICB9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFmb3VuZFdvcmQpIHtcbiAgICAgICAgICAgICAgICBwb3MgKz0gZGlyO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGxpbmVOdW0gKz0gZGlyO1xuICAgICAgICBpZiAoIWlzTGluZShjbSwgbGluZU51bSkpIHtcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGxpbmUgPSBjbS5nZXRMaW5lKGxpbmVOdW0pO1xuICAgICAgICBwb3MgPSAoZGlyID4gMCkgPyAwIDogbGluZS5sZW5ndGg7XG4gICAgfVxufVxuZnVuY3Rpb24gbW92ZVRvV29yZChjbSwgY3VyLCByZXBlYXQsIGZvcndhcmQsIHdvcmRFbmQsIGJpZ1dvcmQpIHtcbiAgICB2YXIgY3VyU3RhcnQgPSBjb3B5Q3Vyc29yKGN1cik7XG4gICAgdmFyIHdvcmRzID0gW107XG4gICAgaWYgKGZvcndhcmQgJiYgIXdvcmRFbmQgfHwgIWZvcndhcmQgJiYgd29yZEVuZCkge1xuICAgICAgICByZXBlYXQrKztcbiAgICB9XG4gICAgdmFyIGVtcHR5TGluZUlzV29yZCA9ICEoZm9yd2FyZCAmJiB3b3JkRW5kKTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJlcGVhdDsgaSsrKSB7XG4gICAgICAgIHZhciB3b3JkID0gZmluZFdvcmQoY20sIGN1ciwgZm9yd2FyZCwgYmlnV29yZCwgZW1wdHlMaW5lSXNXb3JkKTtcbiAgICAgICAgaWYgKCF3b3JkKSB7XG4gICAgICAgICAgICB2YXIgZW9kQ2ggPSBsaW5lTGVuZ3RoKGNtLCBjbS5sYXN0TGluZSgpKTtcbiAgICAgICAgICAgIHdvcmRzLnB1c2goZm9yd2FyZFxuICAgICAgICAgICAgICAgID8geyBsaW5lOiBjbS5sYXN0TGluZSgpLCBmcm9tOiBlb2RDaCwgdG86IGVvZENoIH1cbiAgICAgICAgICAgICAgICA6IHsgbGluZTogMCwgZnJvbTogMCwgdG86IDAgfSk7XG4gICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuICAgICAgICB3b3Jkcy5wdXNoKHdvcmQpO1xuICAgICAgICBjdXIgPSBuZXcgUG9zKHdvcmQubGluZSwgZm9yd2FyZCA/ICh3b3JkLnRvIC0gMSkgOiB3b3JkLmZyb20pO1xuICAgIH1cbiAgICB2YXIgc2hvcnRDaXJjdWl0ID0gd29yZHMubGVuZ3RoICE9IHJlcGVhdDtcbiAgICB2YXIgZmlyc3RXb3JkID0gd29yZHNbMF07XG4gICAgdmFyIGxhc3RXb3JkID0gd29yZHMucG9wKCk7XG4gICAgaWYgKGZvcndhcmQgJiYgIXdvcmRFbmQpIHtcbiAgICAgICAgaWYgKCFzaG9ydENpcmN1aXQgJiYgKGZpcnN0V29yZC5mcm9tICE9IGN1clN0YXJ0LmNoIHx8IGZpcnN0V29yZC5saW5lICE9IGN1clN0YXJ0LmxpbmUpKSB7XG4gICAgICAgICAgICBsYXN0V29yZCA9IHdvcmRzLnBvcCgpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxhc3RXb3JkLmxpbmUsIGxhc3RXb3JkLmZyb20pO1xuICAgIH1cbiAgICBlbHNlIGlmIChmb3J3YXJkICYmIHdvcmRFbmQpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQb3MobGFzdFdvcmQubGluZSwgbGFzdFdvcmQudG8gLSAxKTtcbiAgICB9XG4gICAgZWxzZSBpZiAoIWZvcndhcmQgJiYgd29yZEVuZCkge1xuICAgICAgICBpZiAoIXNob3J0Q2lyY3VpdCAmJiAoZmlyc3RXb3JkLnRvICE9IGN1clN0YXJ0LmNoIHx8IGZpcnN0V29yZC5saW5lICE9IGN1clN0YXJ0LmxpbmUpKSB7XG4gICAgICAgICAgICBsYXN0V29yZCA9IHdvcmRzLnBvcCgpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxhc3RXb3JkLmxpbmUsIGxhc3RXb3JkLnRvKTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIHJldHVybiBuZXcgUG9zKGxhc3RXb3JkLmxpbmUsIGxhc3RXb3JkLmZyb20pO1xuICAgIH1cbn1cbmZ1bmN0aW9uIG1vdmVUb0VvbChjbSwgaGVhZCwgbW90aW9uQXJncywgdmltLCBrZWVwSFBvcykge1xuICAgIHZhciBjdXIgPSBoZWFkO1xuICAgIHZhciByZXR2YWwgPSBuZXcgUG9zKGN1ci5saW5lICsgbW90aW9uQXJncy5yZXBlYXQgLSAxLCBJbmZpbml0eSk7XG4gICAgdmFyIGVuZCA9IGNtLmNsaXBQb3MocmV0dmFsKTtcbiAgICBlbmQuY2gtLTtcbiAgICBpZiAoIWtlZXBIUG9zKSB7XG4gICAgICAgIHZpbS5sYXN0SFBvcyA9IEluZmluaXR5O1xuICAgICAgICB2aW0ubGFzdEhTUG9zID0gY20uY2hhckNvb3JkcyhlbmQsICdkaXYnKS5sZWZ0O1xuICAgIH1cbiAgICByZXR1cm4gcmV0dmFsO1xufVxuZnVuY3Rpb24gbW92ZVRvQ2hhcmFjdGVyKGNtLCByZXBlYXQsIGZvcndhcmQsIGNoYXJhY3RlciwgaGVhZCkge1xuICAgIHZhciBjdXIgPSBoZWFkIHx8IGNtLmdldEN1cnNvcigpO1xuICAgIHZhciBzdGFydCA9IGN1ci5jaDtcbiAgICB2YXIgaWR4O1xuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcmVwZWF0OyBpKyspIHtcbiAgICAgICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGN1ci5saW5lKTtcbiAgICAgICAgaWR4ID0gY2hhcklkeEluTGluZShzdGFydCwgbGluZSwgY2hhcmFjdGVyLCBmb3J3YXJkLCB0cnVlKTtcbiAgICAgICAgaWYgKGlkeCA9PSAtMSkge1xuICAgICAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICAgIH1cbiAgICAgICAgc3RhcnQgPSBpZHg7XG4gICAgfVxuICAgIHJldHVybiBuZXcgUG9zKGNtLmdldEN1cnNvcigpLmxpbmUsIGlkeCk7XG59XG5mdW5jdGlvbiBtb3ZlVG9Db2x1bW4oY20sIHJlcGVhdCkge1xuICAgIHZhciBsaW5lID0gY20uZ2V0Q3Vyc29yKCkubGluZTtcbiAgICByZXR1cm4gY2xpcEN1cnNvclRvQ29udGVudChjbSwgbmV3IFBvcyhsaW5lLCByZXBlYXQgLSAxKSk7XG59XG5mdW5jdGlvbiB1cGRhdGVNYXJrKGNtLCB2aW0sIG1hcmtOYW1lLCBwb3MpIHtcbiAgICBpZiAoIWluQXJyYXkobWFya05hbWUsIHZhbGlkTWFya3MpICYmICFsYXRpbkNoYXJSZWdleC50ZXN0KG1hcmtOYW1lKSkge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGlmICh2aW0ubWFya3NbbWFya05hbWVdKSB7XG4gICAgICAgIHZpbS5tYXJrc1ttYXJrTmFtZV0uY2xlYXIoKTtcbiAgICB9XG4gICAgdmltLm1hcmtzW21hcmtOYW1lXSA9IGNtLnNldEJvb2ttYXJrKHBvcyk7XG59XG5mdW5jdGlvbiBjaGFySWR4SW5MaW5lKHN0YXJ0LCBsaW5lLCBjaGFyYWN0ZXIsIGZvcndhcmQsIGluY2x1ZGVDaGFyKSB7XG4gICAgdmFyIGlkeDtcbiAgICBpZiAoZm9yd2FyZCkge1xuICAgICAgICBpZHggPSBsaW5lLmluZGV4T2YoY2hhcmFjdGVyLCBzdGFydCArIDEpO1xuICAgICAgICBpZiAoaWR4ICE9IC0xICYmICFpbmNsdWRlQ2hhcikge1xuICAgICAgICAgICAgaWR4IC09IDE7XG4gICAgICAgIH1cbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGlkeCA9IGxpbmUubGFzdEluZGV4T2YoY2hhcmFjdGVyLCBzdGFydCAtIDEpO1xuICAgICAgICBpZiAoaWR4ICE9IC0xICYmICFpbmNsdWRlQ2hhcikge1xuICAgICAgICAgICAgaWR4ICs9IDE7XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIGlkeDtcbn1cbmZ1bmN0aW9uIGZpbmRQYXJhZ3JhcGgoY20sIGhlYWQsIHJlcGVhdCwgZGlyLCBpbmNsdXNpdmUpIHtcbiAgICB2YXIgbGluZSA9IGhlYWQubGluZTtcbiAgICB2YXIgbWluID0gY20uZmlyc3RMaW5lKCk7XG4gICAgdmFyIG1heCA9IGNtLmxhc3RMaW5lKCk7XG4gICAgdmFyIHN0YXJ0LCBlbmQsIGkgPSBsaW5lO1xuICAgIGZ1bmN0aW9uIGlzRW1wdHkoaSkgeyByZXR1cm4gIS9cXFMvLnRlc3QoY20uZ2V0TGluZShpKSk7IH0gLy8gYWNlX3BhdGNoXG4gICAgZnVuY3Rpb24gaXNCb3VuZGFyeShpLCBkaXIsIGFueSkge1xuICAgICAgICBpZiAoYW55KSB7XG4gICAgICAgICAgICByZXR1cm4gaXNFbXB0eShpKSAhPSBpc0VtcHR5KGkgKyBkaXIpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiAhaXNFbXB0eShpKSAmJiBpc0VtcHR5KGkgKyBkaXIpO1xuICAgIH1cbiAgICBmdW5jdGlvbiBza2lwRm9sZChpKSB7XG4gICAgICAgIGRpciA9IGRpciA+IDAgPyAxIDogLTE7XG4gICAgICAgIHZhciBmb2xkTGluZSA9IGNtLmFjZS5zZXNzaW9uLmdldEZvbGRMaW5lKGkpO1xuICAgICAgICBpZiAoZm9sZExpbmUpIHtcbiAgICAgICAgICAgIGlmIChpICsgZGlyID4gZm9sZExpbmUuc3RhcnQucm93ICYmIGkgKyBkaXIgPCBmb2xkTGluZS5lbmQucm93KVxuICAgICAgICAgICAgICAgIGRpciA9IChkaXIgPiAwID8gZm9sZExpbmUuZW5kLnJvdyA6IGZvbGRMaW5lLnN0YXJ0LnJvdykgLSBpO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChkaXIpIHtcbiAgICAgICAgd2hpbGUgKG1pbiA8PSBpICYmIGkgPD0gbWF4ICYmIHJlcGVhdCA+IDApIHtcbiAgICAgICAgICAgIHNraXBGb2xkKGkpO1xuICAgICAgICAgICAgaWYgKGlzQm91bmRhcnkoaSwgZGlyKSkge1xuICAgICAgICAgICAgICAgIHJlcGVhdC0tO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaSArPSBkaXI7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG5ldyBQb3MoaSwgMCk7XG4gICAgfVxuICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgaWYgKHZpbS52aXN1YWxMaW5lICYmIGlzQm91bmRhcnkobGluZSwgMSwgdHJ1ZSkpIHtcbiAgICAgICAgdmFyIGFuY2hvciA9IHZpbS5zZWwuYW5jaG9yO1xuICAgICAgICBpZiAoaXNCb3VuZGFyeShhbmNob3IubGluZSwgLTEsIHRydWUpKSB7XG4gICAgICAgICAgICBpZiAoIWluY2x1c2l2ZSB8fCBhbmNob3IubGluZSAhPSBsaW5lKSB7XG4gICAgICAgICAgICAgICAgbGluZSArPSAxO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuICAgIHZhciBzdGFydFN0YXRlID0gaXNFbXB0eShsaW5lKTtcbiAgICBmb3IgKGkgPSBsaW5lOyBpIDw9IG1heCAmJiByZXBlYXQ7IGkrKykge1xuICAgICAgICBpZiAoaXNCb3VuZGFyeShpLCAxLCB0cnVlKSkge1xuICAgICAgICAgICAgaWYgKCFpbmNsdXNpdmUgfHwgaXNFbXB0eShpKSAhPSBzdGFydFN0YXRlKSB7XG4gICAgICAgICAgICAgICAgcmVwZWF0LS07XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG4gICAgZW5kID0gbmV3IFBvcyhpLCAwKTtcbiAgICBpZiAoaSA+IG1heCAmJiAhc3RhcnRTdGF0ZSkge1xuICAgICAgICBzdGFydFN0YXRlID0gdHJ1ZTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGluY2x1c2l2ZSA9IGZhbHNlO1xuICAgIH1cbiAgICBmb3IgKGkgPSBsaW5lOyBpID4gbWluOyBpLS0pIHtcbiAgICAgICAgaWYgKCFpbmNsdXNpdmUgfHwgaXNFbXB0eShpKSA9PSBzdGFydFN0YXRlIHx8IGkgPT0gbGluZSkge1xuICAgICAgICAgICAgaWYgKGlzQm91bmRhcnkoaSwgLTEsIHRydWUpKSB7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG4gICAgc3RhcnQgPSBuZXcgUG9zKGksIDApO1xuICAgIHJldHVybiB7IHN0YXJ0OiBzdGFydCwgZW5kOiBlbmQgfTtcbn1cbmZ1bmN0aW9uIGdldFNlbnRlbmNlKGNtLCBjdXIsIHJlcGVhdCwgZGlyLCBpbmNsdXNpdmUgLyppbmNsdWRlcyB3aGl0ZXNwYWNlKi8pIHtcbiAgICBmdW5jdGlvbiBuZXh0Q2hhcihjdXJyKSB7XG4gICAgICAgIGlmIChjdXJyLnBvcyArIGN1cnIuZGlyIDwgMCB8fCBjdXJyLnBvcyArIGN1cnIuZGlyID49IGN1cnIubGluZS5sZW5ndGgpIHtcbiAgICAgICAgICAgIGN1cnIubGluZSA9IG51bGw7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBjdXJyLnBvcyArPSBjdXJyLmRpcjtcbiAgICAgICAgfVxuICAgIH1cbiAgICBmdW5jdGlvbiBmb3J3YXJkKGNtLCBsbiwgcG9zLCBkaXIpIHtcbiAgICAgICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGxuKTtcbiAgICAgICAgdmFyIGN1cnIgPSB7XG4gICAgICAgICAgICBsaW5lOiBsaW5lLFxuICAgICAgICAgICAgbG46IGxuLFxuICAgICAgICAgICAgcG9zOiBwb3MsXG4gICAgICAgICAgICBkaXI6IGRpcixcbiAgICAgICAgfTtcbiAgICAgICAgaWYgKGN1cnIubGluZSA9PT0gXCJcIikge1xuICAgICAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MgfTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbGFzdFNlbnRlbmNlUG9zID0gY3Vyci5wb3M7XG4gICAgICAgIG5leHRDaGFyKGN1cnIpO1xuICAgICAgICB3aGlsZSAoY3Vyci5saW5lICE9PSBudWxsKSB7XG4gICAgICAgICAgICBsYXN0U2VudGVuY2VQb3MgPSBjdXJyLnBvcztcbiAgICAgICAgICAgIGlmIChpc0VuZE9mU2VudGVuY2VTeW1ib2woY3Vyci5saW5lW2N1cnIucG9zXSkpIHtcbiAgICAgICAgICAgICAgICBpZiAoIWluY2x1c2l2ZSkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4geyBsbjogY3Vyci5sbiwgcG9zOiBjdXJyLnBvcyArIDEgfTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIG5leHRDaGFyKGN1cnIpO1xuICAgICAgICAgICAgICAgICAgICB3aGlsZSAoY3Vyci5saW5lICE9PSBudWxsKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoaXNXaGl0ZVNwYWNlU3RyaW5nKGN1cnIubGluZVtjdXJyLnBvc10pKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgbGFzdFNlbnRlbmNlUG9zID0gY3Vyci5wb3M7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgbmV4dENoYXIoY3Vycik7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICByZXR1cm4geyBsbjogY3Vyci5sbiwgcG9zOiBsYXN0U2VudGVuY2VQb3MgKyAxIH07XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbmV4dENoYXIoY3Vycik7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogbGFzdFNlbnRlbmNlUG9zICsgMSB9O1xuICAgIH1cbiAgICBmdW5jdGlvbiByZXZlcnNlKGNtLCBsbiwgcG9zLCBkaXIpIHtcbiAgICAgICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGxuKTtcbiAgICAgICAgdmFyIGN1cnIgPSB7XG4gICAgICAgICAgICBsaW5lOiBsaW5lLFxuICAgICAgICAgICAgbG46IGxuLFxuICAgICAgICAgICAgcG9zOiBwb3MsXG4gICAgICAgICAgICBkaXI6IGRpcixcbiAgICAgICAgfTtcbiAgICAgICAgaWYgKGN1cnIubGluZSA9PT0gXCJcIikge1xuICAgICAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MgfTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbGFzdFNlbnRlbmNlUG9zID0gY3Vyci5wb3M7XG4gICAgICAgIG5leHRDaGFyKGN1cnIpO1xuICAgICAgICB3aGlsZSAoY3Vyci5saW5lICE9PSBudWxsKSB7XG4gICAgICAgICAgICBpZiAoIWlzV2hpdGVTcGFjZVN0cmluZyhjdXJyLmxpbmVbY3Vyci5wb3NdKSAmJiAhaXNFbmRPZlNlbnRlbmNlU3ltYm9sKGN1cnIubGluZVtjdXJyLnBvc10pKSB7XG4gICAgICAgICAgICAgICAgbGFzdFNlbnRlbmNlUG9zID0gY3Vyci5wb3M7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChpc0VuZE9mU2VudGVuY2VTeW1ib2woY3Vyci5saW5lW2N1cnIucG9zXSkpIHtcbiAgICAgICAgICAgICAgICBpZiAoIWluY2x1c2l2ZSkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4geyBsbjogY3Vyci5sbiwgcG9zOiBsYXN0U2VudGVuY2VQb3MgfTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIGlmIChpc1doaXRlU3BhY2VTdHJpbmcoY3Vyci5saW5lW2N1cnIucG9zICsgMV0pKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4geyBsbjogY3Vyci5sbiwgcG9zOiBjdXJyLnBvcyArIDEgfTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB7IGxuOiBjdXJyLmxuLCBwb3M6IGxhc3RTZW50ZW5jZVBvcyB9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgbmV4dENoYXIoY3Vycik7XG4gICAgICAgIH1cbiAgICAgICAgY3Vyci5saW5lID0gbGluZTtcbiAgICAgICAgaWYgKGluY2x1c2l2ZSAmJiBpc1doaXRlU3BhY2VTdHJpbmcoY3Vyci5saW5lW2N1cnIucG9zXSkpIHtcbiAgICAgICAgICAgIHJldHVybiB7IGxuOiBjdXJyLmxuLCBwb3M6IGN1cnIucG9zIH07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICByZXR1cm4geyBsbjogY3Vyci5sbiwgcG9zOiBsYXN0U2VudGVuY2VQb3MgfTtcbiAgICAgICAgfVxuICAgIH1cbiAgICB2YXIgY3Vycl9pbmRleCA9IHtcbiAgICAgICAgbG46IGN1ci5saW5lLFxuICAgICAgICBwb3M6IGN1ci5jaCxcbiAgICB9O1xuICAgIHdoaWxlIChyZXBlYXQgPiAwKSB7XG4gICAgICAgIGlmIChkaXIgPCAwKSB7XG4gICAgICAgICAgICBjdXJyX2luZGV4ID0gcmV2ZXJzZShjbSwgY3Vycl9pbmRleC5sbiwgY3Vycl9pbmRleC5wb3MsIGRpcik7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBjdXJyX2luZGV4ID0gZm9yd2FyZChjbSwgY3Vycl9pbmRleC5sbiwgY3Vycl9pbmRleC5wb3MsIGRpcik7XG4gICAgICAgIH1cbiAgICAgICAgcmVwZWF0LS07XG4gICAgfVxuICAgIHJldHVybiBuZXcgUG9zKGN1cnJfaW5kZXgubG4sIGN1cnJfaW5kZXgucG9zKTtcbn1cbmZ1bmN0aW9uIGZpbmRTZW50ZW5jZShjbSwgY3VyLCByZXBlYXQsIGRpcikge1xuICAgIGZ1bmN0aW9uIG5leHRDaGFyKGNtLCBpZHgpIHtcbiAgICAgICAgaWYgKGlkeC5wb3MgKyBpZHguZGlyIDwgMCB8fCBpZHgucG9zICsgaWR4LmRpciA+PSBpZHgubGluZS5sZW5ndGgpIHtcbiAgICAgICAgICAgIGlkeC5sbiArPSBpZHguZGlyO1xuICAgICAgICAgICAgaWYgKCFpc0xpbmUoY20sIGlkeC5sbikpIHtcbiAgICAgICAgICAgICAgICBpZHgubGluZSA9IG51bGw7XG4gICAgICAgICAgICAgICAgaWR4LmxuID0gbnVsbDtcbiAgICAgICAgICAgICAgICBpZHgucG9zID0gbnVsbDtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBpZHgubGluZSA9IGNtLmdldExpbmUoaWR4LmxuKTtcbiAgICAgICAgICAgIGlkeC5wb3MgPSAoaWR4LmRpciA+IDApID8gMCA6IGlkeC5saW5lLmxlbmd0aCAtIDE7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBpZHgucG9zICs9IGlkeC5kaXI7XG4gICAgICAgIH1cbiAgICB9XG4gICAgZnVuY3Rpb24gZm9yd2FyZChjbSwgbG4sIHBvcywgZGlyKSB7XG4gICAgICAgIHZhciBsaW5lID0gY20uZ2V0TGluZShsbik7XG4gICAgICAgIHZhciBzdG9wID0gKGxpbmUgPT09IFwiXCIpO1xuICAgICAgICB2YXIgY3VyciA9IHtcbiAgICAgICAgICAgIGxpbmU6IGxpbmUsXG4gICAgICAgICAgICBsbjogbG4sXG4gICAgICAgICAgICBwb3M6IHBvcyxcbiAgICAgICAgICAgIGRpcjogZGlyLFxuICAgICAgICB9O1xuICAgICAgICB2YXIgbGFzdF92YWxpZCA9IHtcbiAgICAgICAgICAgIGxuOiBjdXJyLmxuLFxuICAgICAgICAgICAgcG9zOiBjdXJyLnBvcyxcbiAgICAgICAgfTtcbiAgICAgICAgdmFyIHNraXBfZW1wdHlfbGluZXMgPSAoY3Vyci5saW5lID09PSBcIlwiKTtcbiAgICAgICAgbmV4dENoYXIoY20sIGN1cnIpO1xuICAgICAgICB3aGlsZSAoY3Vyci5saW5lICE9PSBudWxsKSB7XG4gICAgICAgICAgICBsYXN0X3ZhbGlkLmxuID0gY3Vyci5sbjtcbiAgICAgICAgICAgIGxhc3RfdmFsaWQucG9zID0gY3Vyci5wb3M7XG4gICAgICAgICAgICBpZiAoY3Vyci5saW5lID09PSBcIlwiICYmICFza2lwX2VtcHR5X2xpbmVzKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MsIH07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChzdG9wICYmIGN1cnIubGluZSAhPT0gXCJcIiAmJiAhaXNXaGl0ZVNwYWNlU3RyaW5nKGN1cnIubGluZVtjdXJyLnBvc10pKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MsIH07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChpc0VuZE9mU2VudGVuY2VTeW1ib2woY3Vyci5saW5lW2N1cnIucG9zXSlcbiAgICAgICAgICAgICAgICAmJiAhc3RvcFxuICAgICAgICAgICAgICAgICYmIChjdXJyLnBvcyA9PT0gY3Vyci5saW5lLmxlbmd0aCAtIDFcbiAgICAgICAgICAgICAgICAgICAgfHwgaXNXaGl0ZVNwYWNlU3RyaW5nKGN1cnIubGluZVtjdXJyLnBvcyArIDFdKSkpIHtcbiAgICAgICAgICAgICAgICBzdG9wID0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG5leHRDaGFyKGNtLCBjdXJyKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbGluZSA9IGNtLmdldExpbmUobGFzdF92YWxpZC5sbik7XG4gICAgICAgIGxhc3RfdmFsaWQucG9zID0gMDtcbiAgICAgICAgZm9yICh2YXIgaSA9IGxpbmUubGVuZ3RoIC0gMTsgaSA+PSAwOyAtLWkpIHtcbiAgICAgICAgICAgIGlmICghaXNXaGl0ZVNwYWNlU3RyaW5nKGxpbmVbaV0pKSB7XG4gICAgICAgICAgICAgICAgbGFzdF92YWxpZC5wb3MgPSBpO1xuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBsYXN0X3ZhbGlkO1xuICAgIH1cbiAgICBmdW5jdGlvbiByZXZlcnNlKGNtLCBsbiwgcG9zLCBkaXIpIHtcbiAgICAgICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGxuKTtcbiAgICAgICAgdmFyIGN1cnIgPSB7XG4gICAgICAgICAgICBsaW5lOiBsaW5lLFxuICAgICAgICAgICAgbG46IGxuLFxuICAgICAgICAgICAgcG9zOiBwb3MsXG4gICAgICAgICAgICBkaXI6IGRpcixcbiAgICAgICAgfTtcbiAgICAgICAgdmFyIGxhc3RfdmFsaWQgPSB7XG4gICAgICAgICAgICBsbjogY3Vyci5sbixcbiAgICAgICAgICAgIHBvczogbnVsbCxcbiAgICAgICAgfTtcbiAgICAgICAgdmFyIHNraXBfZW1wdHlfbGluZXMgPSAoY3Vyci5saW5lID09PSBcIlwiKTtcbiAgICAgICAgbmV4dENoYXIoY20sIGN1cnIpO1xuICAgICAgICB3aGlsZSAoY3Vyci5saW5lICE9PSBudWxsKSB7XG4gICAgICAgICAgICBpZiAoY3Vyci5saW5lID09PSBcIlwiICYmICFza2lwX2VtcHR5X2xpbmVzKSB7XG4gICAgICAgICAgICAgICAgaWYgKGxhc3RfdmFsaWQucG9zICE9PSBudWxsKSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiBsYXN0X3ZhbGlkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MgfTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChpc0VuZE9mU2VudGVuY2VTeW1ib2woY3Vyci5saW5lW2N1cnIucG9zXSlcbiAgICAgICAgICAgICAgICAmJiBsYXN0X3ZhbGlkLnBvcyAhPT0gbnVsbFxuICAgICAgICAgICAgICAgICYmICEoY3Vyci5sbiA9PT0gbGFzdF92YWxpZC5sbiAmJiBjdXJyLnBvcyArIDEgPT09IGxhc3RfdmFsaWQucG9zKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBsYXN0X3ZhbGlkO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5saW5lICE9PSBcIlwiICYmICFpc1doaXRlU3BhY2VTdHJpbmcoY3Vyci5saW5lW2N1cnIucG9zXSkpIHtcbiAgICAgICAgICAgICAgICBza2lwX2VtcHR5X2xpbmVzID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgbGFzdF92YWxpZCA9IHsgbG46IGN1cnIubG4sIHBvczogY3Vyci5wb3MgfTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG5leHRDaGFyKGNtLCBjdXJyKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbGluZSA9IGNtLmdldExpbmUobGFzdF92YWxpZC5sbik7XG4gICAgICAgIGxhc3RfdmFsaWQucG9zID0gMDtcbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBsaW5lLmxlbmd0aDsgKytpKSB7XG4gICAgICAgICAgICBpZiAoIWlzV2hpdGVTcGFjZVN0cmluZyhsaW5lW2ldKSkge1xuICAgICAgICAgICAgICAgIGxhc3RfdmFsaWQucG9zID0gaTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbGFzdF92YWxpZDtcbiAgICB9XG4gICAgdmFyIGN1cnJfaW5kZXggPSB7XG4gICAgICAgIGxuOiBjdXIubGluZSxcbiAgICAgICAgcG9zOiBjdXIuY2gsXG4gICAgfTtcbiAgICB3aGlsZSAocmVwZWF0ID4gMCkge1xuICAgICAgICBpZiAoZGlyIDwgMCkge1xuICAgICAgICAgICAgY3Vycl9pbmRleCA9IHJldmVyc2UoY20sIGN1cnJfaW5kZXgubG4sIGN1cnJfaW5kZXgucG9zLCBkaXIpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgY3Vycl9pbmRleCA9IGZvcndhcmQoY20sIGN1cnJfaW5kZXgubG4sIGN1cnJfaW5kZXgucG9zLCBkaXIpO1xuICAgICAgICB9XG4gICAgICAgIHJlcGVhdC0tO1xuICAgIH1cbiAgICByZXR1cm4gbmV3IFBvcyhjdXJyX2luZGV4LmxuLCBjdXJyX2luZGV4LnBvcyk7XG59XG5mdW5jdGlvbiBzZWxlY3RDb21wYW5pb25PYmplY3QoY20sIGhlYWQsIHN5bWIsIGluY2x1c2l2ZSkge1xuICAgIHZhciBjdXIgPSBoZWFkLCBzdGFydCwgZW5kO1xuICAgIHZhciBicmFja2V0UmVnZXhwID0gKHtcbiAgICAgICAgJygnOiAvWygpXS8sICcpJzogL1soKV0vLFxuICAgICAgICAnWyc6IC9bW1xcXV0vLCAnXSc6IC9bW1xcXV0vLFxuICAgICAgICAneyc6IC9be31dLywgJ30nOiAvW3t9XS8sXG4gICAgICAgICc8JzogL1s8Pl0vLCAnPic6IC9bPD5dL1xuICAgIH0pW3N5bWJdO1xuICAgIHZhciBvcGVuU3ltID0gKHtcbiAgICAgICAgJygnOiAnKCcsICcpJzogJygnLFxuICAgICAgICAnWyc6ICdbJywgJ10nOiAnWycsXG4gICAgICAgICd7JzogJ3snLCAnfSc6ICd7JyxcbiAgICAgICAgJzwnOiAnPCcsICc+JzogJzwnXG4gICAgfSlbc3ltYl07XG4gICAgdmFyIGN1ckNoYXIgPSBjbS5nZXRMaW5lKGN1ci5saW5lKS5jaGFyQXQoY3VyLmNoKTtcbiAgICB2YXIgb2Zmc2V0ID0gY3VyQ2hhciA9PT0gb3BlblN5bSA/IDEgOiAwO1xuICAgIHN0YXJ0ID0gY20uc2NhbkZvckJyYWNrZXQobmV3IFBvcyhjdXIubGluZSwgY3VyLmNoICsgb2Zmc2V0KSwgLTEsIHVuZGVmaW5lZCwgeyAnYnJhY2tldFJlZ2V4JzogYnJhY2tldFJlZ2V4cCB9KTtcbiAgICBlbmQgPSBjbS5zY2FuRm9yQnJhY2tldChuZXcgUG9zKGN1ci5saW5lLCBjdXIuY2ggKyBvZmZzZXQpLCAxLCB1bmRlZmluZWQsIHsgJ2JyYWNrZXRSZWdleCc6IGJyYWNrZXRSZWdleHAgfSk7XG4gICAgaWYgKCFzdGFydCB8fCAhZW5kKVxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICBzdGFydCA9IHN0YXJ0LnBvcztcbiAgICBlbmQgPSBlbmQucG9zO1xuICAgIGlmICgoc3RhcnQubGluZSA9PSBlbmQubGluZSAmJiBzdGFydC5jaCA+IGVuZC5jaClcbiAgICAgICAgfHwgKHN0YXJ0LmxpbmUgPiBlbmQubGluZSkpIHtcbiAgICAgICAgdmFyIHRtcCA9IHN0YXJ0O1xuICAgICAgICBzdGFydCA9IGVuZDtcbiAgICAgICAgZW5kID0gdG1wO1xuICAgIH1cbiAgICBpZiAoaW5jbHVzaXZlKSB7XG4gICAgICAgIGVuZC5jaCArPSAxO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgc3RhcnQuY2ggKz0gMTtcbiAgICB9XG4gICAgcmV0dXJuIHsgc3RhcnQ6IHN0YXJ0LCBlbmQ6IGVuZCB9O1xufVxuZnVuY3Rpb24gZmluZEJlZ2lubmluZ0FuZEVuZChjbSwgaGVhZCwgc3ltYiwgaW5jbHVzaXZlKSB7XG4gICAgdmFyIGN1ciA9IGNvcHlDdXJzb3IoaGVhZCk7XG4gICAgdmFyIGxpbmUgPSBjbS5nZXRMaW5lKGN1ci5saW5lKTtcbiAgICB2YXIgY2hhcnMgPSBsaW5lLnNwbGl0KCcnKTtcbiAgICB2YXIgc3RhcnQsIGVuZCwgaSwgbGVuO1xuICAgIHZhciBmaXJzdEluZGV4ID0gY2hhcnMuaW5kZXhPZihzeW1iKTtcbiAgICBpZiAoY3VyLmNoIDwgZmlyc3RJbmRleCkge1xuICAgICAgICBjdXIuY2ggPSBmaXJzdEluZGV4O1xuICAgIH1cbiAgICBlbHNlIGlmIChmaXJzdEluZGV4IDwgY3VyLmNoICYmIGNoYXJzW2N1ci5jaF0gPT0gc3ltYikge1xuICAgICAgICB2YXIgc3RyaW5nQWZ0ZXIgPSAvc3RyaW5nLy50ZXN0KGNtLmdldFRva2VuVHlwZUF0KG9mZnNldEN1cnNvcihoZWFkLCAwLCAxKSkpO1xuICAgICAgICB2YXIgc3RyaW5nQmVmb3JlID0gL3N0cmluZy8udGVzdChjbS5nZXRUb2tlblR5cGVBdChoZWFkKSk7XG4gICAgICAgIHZhciBpc1N0cmluZ1N0YXJ0ID0gc3RyaW5nQWZ0ZXIgJiYgIXN0cmluZ0JlZm9yZTtcbiAgICAgICAgaWYgKCFpc1N0cmluZ1N0YXJ0KSB7XG4gICAgICAgICAgICBlbmQgPSBjdXIuY2g7IC8vIGFzc2lnbiBlbmQgdG8gdGhlIGN1cnJlbnQgY3Vyc29yXG4gICAgICAgICAgICAtLWN1ci5jaDsgLy8gbWFrZSBzdXJlIHRvIGxvb2sgYmFja3dhcmRzXG4gICAgICAgIH1cbiAgICB9XG4gICAgaWYgKGNoYXJzW2N1ci5jaF0gPT0gc3ltYiAmJiAhZW5kKSB7XG4gICAgICAgIHN0YXJ0ID0gY3VyLmNoICsgMTsgLy8gYXNzaWduIHN0YXJ0IHRvIGFoZWFkIG9mIHRoZSBjdXJzb3JcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGZvciAoaSA9IGN1ci5jaDsgaSA+IC0xICYmICFzdGFydDsgaS0tKSB7XG4gICAgICAgICAgICBpZiAoY2hhcnNbaV0gPT0gc3ltYikge1xuICAgICAgICAgICAgICAgIHN0YXJ0ID0gaSArIDE7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG4gICAgaWYgKHN0YXJ0ICYmICFlbmQpIHtcbiAgICAgICAgZm9yIChpID0gc3RhcnQsIGxlbiA9IGNoYXJzLmxlbmd0aDsgaSA8IGxlbiAmJiAhZW5kOyBpKyspIHtcbiAgICAgICAgICAgIGlmIChjaGFyc1tpXSA9PSBzeW1iKSB7XG4gICAgICAgICAgICAgICAgZW5kID0gaTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH1cbiAgICBpZiAoIXN0YXJ0IHx8ICFlbmQpIHtcbiAgICAgICAgcmV0dXJuIHsgc3RhcnQ6IGN1ciwgZW5kOiBjdXIgfTtcbiAgICB9XG4gICAgaWYgKGluY2x1c2l2ZSkge1xuICAgICAgICAtLXN0YXJ0O1xuICAgICAgICArK2VuZDtcbiAgICB9XG4gICAgcmV0dXJuIHtcbiAgICAgICAgc3RhcnQ6IG5ldyBQb3MoY3VyLmxpbmUsIHN0YXJ0KSxcbiAgICAgICAgZW5kOiBuZXcgUG9zKGN1ci5saW5lLCBlbmQpXG4gICAgfTtcbn1cbmRlZmluZU9wdGlvbigncGNyZScsIHRydWUsICdib29sZWFuJyk7XG5mdW5jdGlvbiBTZWFyY2hTdGF0ZSgpIHsgfVxuU2VhcmNoU3RhdGUucHJvdG90eXBlID0ge1xuICAgIGdldFF1ZXJ5OiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB2aW1HbG9iYWxTdGF0ZS5xdWVyeTtcbiAgICB9LFxuICAgIHNldFF1ZXJ5OiBmdW5jdGlvbiAocXVlcnkpIHtcbiAgICAgICAgdmltR2xvYmFsU3RhdGUucXVlcnkgPSBxdWVyeTtcbiAgICB9LFxuICAgIGdldE92ZXJsYXk6IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuc2VhcmNoT3ZlcmxheTtcbiAgICB9LFxuICAgIHNldE92ZXJsYXk6IGZ1bmN0aW9uIChvdmVybGF5KSB7XG4gICAgICAgIHRoaXMuc2VhcmNoT3ZlcmxheSA9IG92ZXJsYXk7XG4gICAgfSxcbiAgICBpc1JldmVyc2VkOiBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB2aW1HbG9iYWxTdGF0ZS5pc1JldmVyc2VkO1xuICAgIH0sXG4gICAgc2V0UmV2ZXJzZWQ6IGZ1bmN0aW9uIChyZXZlcnNlZCkge1xuICAgICAgICB2aW1HbG9iYWxTdGF0ZS5pc1JldmVyc2VkID0gcmV2ZXJzZWQ7XG4gICAgfSxcbiAgICBnZXRTY3JvbGxiYXJBbm5vdGF0ZTogZnVuY3Rpb24gKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5hbm5vdGF0ZTtcbiAgICB9LFxuICAgIHNldFNjcm9sbGJhckFubm90YXRlOiBmdW5jdGlvbiAoYW5ub3RhdGUpIHtcbiAgICAgICAgdGhpcy5hbm5vdGF0ZSA9IGFubm90YXRlO1xuICAgIH1cbn07XG5mdW5jdGlvbiBnZXRTZWFyY2hTdGF0ZShjbSkge1xuICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgcmV0dXJuIHZpbS5zZWFyY2hTdGF0ZV8gfHwgKHZpbS5zZWFyY2hTdGF0ZV8gPSBuZXcgU2VhcmNoU3RhdGUoKSk7XG59XG5mdW5jdGlvbiBzcGxpdEJ5U2xhc2goYXJnU3RyaW5nKSB7XG4gICAgcmV0dXJuIHNwbGl0QnlTZXBhcmF0b3IoYXJnU3RyaW5nLCAnLycpO1xufVxuZnVuY3Rpb24gZmluZFVuZXNjYXBlZFNsYXNoZXMoYXJnU3RyaW5nKSB7XG4gICAgcmV0dXJuIGZpbmRVbmVzY2FwZWRTZXBhcmF0b3JzKGFyZ1N0cmluZywgJy8nKTtcbn1cbmZ1bmN0aW9uIHNwbGl0QnlTZXBhcmF0b3IoYXJnU3RyaW5nLCBzZXBhcmF0b3IpIHtcbiAgICB2YXIgc2xhc2hlcyA9IGZpbmRVbmVzY2FwZWRTZXBhcmF0b3JzKGFyZ1N0cmluZywgc2VwYXJhdG9yKSB8fCBbXTtcbiAgICBpZiAoIXNsYXNoZXMubGVuZ3RoKVxuICAgICAgICByZXR1cm4gW107XG4gICAgdmFyIHRva2VucyA9IFtdO1xuICAgIGlmIChzbGFzaGVzWzBdICE9PSAwKVxuICAgICAgICByZXR1cm47XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBzbGFzaGVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmICh0eXBlb2Ygc2xhc2hlc1tpXSA9PSAnbnVtYmVyJylcbiAgICAgICAgICAgIHRva2Vucy5wdXNoKGFyZ1N0cmluZy5zdWJzdHJpbmcoc2xhc2hlc1tpXSArIDEsIHNsYXNoZXNbaSArIDFdKSk7XG4gICAgfVxuICAgIHJldHVybiB0b2tlbnM7XG59XG5mdW5jdGlvbiBmaW5kVW5lc2NhcGVkU2VwYXJhdG9ycyhzdHIsIHNlcGFyYXRvcikge1xuICAgIGlmICghc2VwYXJhdG9yKVxuICAgICAgICBzZXBhcmF0b3IgPSAnLyc7XG4gICAgdmFyIGVzY2FwZU5leHRDaGFyID0gZmFsc2U7XG4gICAgdmFyIHNsYXNoZXMgPSBbXTtcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHN0ci5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgYyA9IHN0ci5jaGFyQXQoaSk7XG4gICAgICAgIGlmICghZXNjYXBlTmV4dENoYXIgJiYgYyA9PSBzZXBhcmF0b3IpIHtcbiAgICAgICAgICAgIHNsYXNoZXMucHVzaChpKTtcbiAgICAgICAgfVxuICAgICAgICBlc2NhcGVOZXh0Q2hhciA9ICFlc2NhcGVOZXh0Q2hhciAmJiAoYyA9PSAnXFxcXCcpO1xuICAgIH1cbiAgICByZXR1cm4gc2xhc2hlcztcbn1cbmZ1bmN0aW9uIHRyYW5zbGF0ZVJlZ2V4KHN0cikge1xuICAgIHZhciBzcGVjaWFscyA9ICd8KCl7JztcbiAgICB2YXIgdW5lc2NhcGUgPSAnfSc7XG4gICAgdmFyIGVzY2FwZU5leHRDaGFyID0gZmFsc2U7XG4gICAgdmFyIG91dCA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAtMTsgaSA8IHN0ci5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgYyA9IHN0ci5jaGFyQXQoaSkgfHwgJyc7XG4gICAgICAgIHZhciBuID0gc3RyLmNoYXJBdChpICsgMSkgfHwgJyc7XG4gICAgICAgIHZhciBzcGVjaWFsQ29tZXNOZXh0ID0gKG4gJiYgc3BlY2lhbHMuaW5kZXhPZihuKSAhPSAtMSk7XG4gICAgICAgIGlmIChlc2NhcGVOZXh0Q2hhcikge1xuICAgICAgICAgICAgaWYgKGMgIT09ICdcXFxcJyB8fCAhc3BlY2lhbENvbWVzTmV4dCkge1xuICAgICAgICAgICAgICAgIG91dC5wdXNoKGMpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZXNjYXBlTmV4dENoYXIgPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGlmIChjID09PSAnXFxcXCcpIHtcbiAgICAgICAgICAgICAgICBlc2NhcGVOZXh0Q2hhciA9IHRydWU7XG4gICAgICAgICAgICAgICAgaWYgKG4gJiYgdW5lc2NhcGUuaW5kZXhPZihuKSAhPSAtMSkge1xuICAgICAgICAgICAgICAgICAgICBzcGVjaWFsQ29tZXNOZXh0ID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKCFzcGVjaWFsQ29tZXNOZXh0IHx8IG4gPT09ICdcXFxcJykge1xuICAgICAgICAgICAgICAgICAgICBvdXQucHVzaChjKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBvdXQucHVzaChjKTtcbiAgICAgICAgICAgICAgICBpZiAoc3BlY2lhbENvbWVzTmV4dCAmJiBuICE9PSAnXFxcXCcpIHtcbiAgICAgICAgICAgICAgICAgICAgb3V0LnB1c2goJ1xcXFwnKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIG91dC5qb2luKCcnKTtcbn1cbnZhciBjaGFyVW5lc2NhcGVzID0geyAnXFxcXG4nOiAnXFxuJywgJ1xcXFxyJzogJ1xccicsICdcXFxcdCc6ICdcXHQnIH07XG5mdW5jdGlvbiB0cmFuc2xhdGVSZWdleFJlcGxhY2Uoc3RyKSB7XG4gICAgdmFyIGVzY2FwZU5leHRDaGFyID0gZmFsc2U7XG4gICAgdmFyIG91dCA9IFtdO1xuICAgIGZvciAodmFyIGkgPSAtMTsgaSA8IHN0ci5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgYyA9IHN0ci5jaGFyQXQoaSkgfHwgJyc7XG4gICAgICAgIHZhciBuID0gc3RyLmNoYXJBdChpICsgMSkgfHwgJyc7XG4gICAgICAgIGlmIChjaGFyVW5lc2NhcGVzW2MgKyBuXSkge1xuICAgICAgICAgICAgb3V0LnB1c2goY2hhclVuZXNjYXBlc1tjICsgbl0pO1xuICAgICAgICAgICAgaSsrO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKGVzY2FwZU5leHRDaGFyKSB7XG4gICAgICAgICAgICBvdXQucHVzaChjKTtcbiAgICAgICAgICAgIGVzY2FwZU5leHRDaGFyID0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBpZiAoYyA9PT0gJ1xcXFwnKSB7XG4gICAgICAgICAgICAgICAgZXNjYXBlTmV4dENoYXIgPSB0cnVlO1xuICAgICAgICAgICAgICAgIGlmICgoaXNOdW1iZXIobikgfHwgbiA9PT0gJyQnKSkge1xuICAgICAgICAgICAgICAgICAgICBvdXQucHVzaCgnJCcpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChuICE9PSAnLycgJiYgbiAhPT0gJ1xcXFwnKSB7XG4gICAgICAgICAgICAgICAgICAgIG91dC5wdXNoKCdcXFxcJyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGMgPT09ICckJykge1xuICAgICAgICAgICAgICAgICAgICBvdXQucHVzaCgnJCcpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBvdXQucHVzaChjKTtcbiAgICAgICAgICAgICAgICBpZiAobiA9PT0gJy8nKSB7XG4gICAgICAgICAgICAgICAgICAgIG91dC5wdXNoKCdcXFxcJyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuICAgIHJldHVybiBvdXQuam9pbignJyk7XG59XG52YXIgdW5lc2NhcGVzID0geyAnXFxcXC8nOiAnLycsICdcXFxcXFxcXCc6ICdcXFxcJywgJ1xcXFxuJzogJ1xcbicsICdcXFxccic6ICdcXHInLCAnXFxcXHQnOiAnXFx0JywgJ1xcXFwmJzogJyYnIH07XG5mdW5jdGlvbiB1bmVzY2FwZVJlZ2V4UmVwbGFjZShzdHIpIHtcbiAgICB2YXIgc3RyZWFtID0gbmV3IENvZGVNaXJyb3IuU3RyaW5nU3RyZWFtKHN0cik7XG4gICAgdmFyIG91dHB1dCA9IFtdO1xuICAgIHdoaWxlICghc3RyZWFtLmVvbCgpKSB7XG4gICAgICAgIHdoaWxlIChzdHJlYW0ucGVlaygpICYmIHN0cmVhbS5wZWVrKCkgIT0gJ1xcXFwnKSB7XG4gICAgICAgICAgICBvdXRwdXQucHVzaChzdHJlYW0ubmV4dCgpKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbWF0Y2hlZCA9IGZhbHNlO1xuICAgICAgICBmb3IgKHZhciBtYXRjaGVyIGluIHVuZXNjYXBlcykge1xuICAgICAgICAgICAgaWYgKHN0cmVhbS5tYXRjaChtYXRjaGVyLCB0cnVlKSkge1xuICAgICAgICAgICAgICAgIG1hdGNoZWQgPSB0cnVlO1xuICAgICAgICAgICAgICAgIG91dHB1dC5wdXNoKHVuZXNjYXBlc1ttYXRjaGVyXSk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKCFtYXRjaGVkKSB7XG4gICAgICAgICAgICBvdXRwdXQucHVzaChzdHJlYW0ubmV4dCgpKTtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gb3V0cHV0LmpvaW4oJycpO1xufVxuZnVuY3Rpb24gcGFyc2VRdWVyeShxdWVyeSwgaWdub3JlQ2FzZSwgc21hcnRDYXNlKSB7XG4gICAgdmFyIGxhc3RTZWFyY2hSZWdpc3RlciA9IHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5nZXRSZWdpc3RlcignLycpO1xuICAgIGxhc3RTZWFyY2hSZWdpc3Rlci5zZXRUZXh0KHF1ZXJ5KTtcbiAgICBpZiAocXVlcnkgaW5zdGFuY2VvZiBSZWdFeHApIHtcbiAgICAgICAgcmV0dXJuIHF1ZXJ5O1xuICAgIH1cbiAgICB2YXIgc2xhc2hlcyA9IGZpbmRVbmVzY2FwZWRTbGFzaGVzKHF1ZXJ5KTtcbiAgICB2YXIgcmVnZXhQYXJ0O1xuICAgIHZhciBmb3JjZUlnbm9yZUNhc2U7XG4gICAgaWYgKCFzbGFzaGVzLmxlbmd0aCkge1xuICAgICAgICByZWdleFBhcnQgPSBxdWVyeTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIHJlZ2V4UGFydCA9IHF1ZXJ5LnN1YnN0cmluZygwLCBzbGFzaGVzWzBdKTtcbiAgICAgICAgdmFyIGZsYWdzUGFydCA9IHF1ZXJ5LnN1YnN0cmluZyhzbGFzaGVzWzBdKTtcbiAgICAgICAgZm9yY2VJZ25vcmVDYXNlID0gKGZsYWdzUGFydC5pbmRleE9mKCdpJykgIT0gLTEpO1xuICAgIH1cbiAgICBpZiAoIXJlZ2V4UGFydCkge1xuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgaWYgKCFnZXRPcHRpb24oJ3BjcmUnKSkge1xuICAgICAgICByZWdleFBhcnQgPSB0cmFuc2xhdGVSZWdleChyZWdleFBhcnQpO1xuICAgIH1cbiAgICBpZiAoc21hcnRDYXNlKSB7XG4gICAgICAgIGlnbm9yZUNhc2UgPSAoL15bXkEtWl0qJC8pLnRlc3QocmVnZXhQYXJ0KTtcbiAgICB9XG4gICAgdmFyIHJlZ2V4cCA9IG5ldyBSZWdFeHAocmVnZXhQYXJ0LCAoaWdub3JlQ2FzZSB8fCBmb3JjZUlnbm9yZUNhc2UpID8gJ2ltJyA6ICdtJyk7XG4gICAgcmV0dXJuIHJlZ2V4cDtcbn1cbmZ1bmN0aW9uIGRvbShuKSB7XG4gICAgaWYgKHR5cGVvZiBuID09PSAnc3RyaW5nJylcbiAgICAgICAgbiA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQobik7XG4gICAgZm9yICh2YXIgYSwgaSA9IDE7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgaWYgKCEoYSA9IGFyZ3VtZW50c1tpXSkpXG4gICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgaWYgKHR5cGVvZiBhICE9PSAnb2JqZWN0JylcbiAgICAgICAgICAgIGEgPSBkb2N1bWVudC5jcmVhdGVUZXh0Tm9kZShhKTtcbiAgICAgICAgaWYgKGEubm9kZVR5cGUpXG4gICAgICAgICAgICBuLmFwcGVuZENoaWxkKGEpO1xuICAgICAgICBlbHNlXG4gICAgICAgICAgICBmb3IgKHZhciBrZXkgaW4gYSkge1xuICAgICAgICAgICAgICAgIGlmICghT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKGEsIGtleSkpXG4gICAgICAgICAgICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICAgICAgICAgIGlmIChrZXlbMF0gPT09ICckJylcbiAgICAgICAgICAgICAgICAgICAgbi5zdHlsZVtrZXkuc2xpY2UoMSldID0gYVtrZXldO1xuICAgICAgICAgICAgICAgIGVsc2VcbiAgICAgICAgICAgICAgICAgICAgbi5zZXRBdHRyaWJ1dGUoa2V5LCBhW2tleV0pO1xuICAgICAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gbjtcbn1cbmZ1bmN0aW9uIHNob3dDb25maXJtKGNtLCB0ZW1wbGF0ZSkge1xuICAgIHZhciBwcmUgPSBkb20oJ2RpdicsIHsgJGNvbG9yOiAncmVkJywgJHdoaXRlU3BhY2U6ICdwcmUnLCBjbGFzczogJ2NtLXZpbS1tZXNzYWdlJyB9LCB0ZW1wbGF0ZSk7XG4gICAgaWYgKGNtLm9wZW5Ob3RpZmljYXRpb24pIHtcbiAgICAgICAgY20ub3Blbk5vdGlmaWNhdGlvbihwcmUsIHsgYm90dG9tOiB0cnVlLCBkdXJhdGlvbjogNTAwMCB9KTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGFsZXJ0KHByZS5pbm5lclRleHQpO1xuICAgIH1cbn1cbmZ1bmN0aW9uIG1ha2VQcm9tcHQocHJlZml4LCBkZXNjKSB7XG4gICAgcmV0dXJuIGRvbSgnZGl2JywgeyAkZGlzcGxheTogJ2ZsZXgnIH0sIGRvbSgnc3BhbicsIHsgJGZvbnRGYW1pbHk6ICdtb25vc3BhY2UnLCAkd2hpdGVTcGFjZTogJ3ByZScsICRmbGV4OiAxIH0sIHByZWZpeCwgZG9tKCdpbnB1dCcsIHsgdHlwZTogJ3RleHQnLCBhdXRvY29ycmVjdDogJ29mZicsXG4gICAgICAgIGF1dG9jYXBpdGFsaXplOiAnb2ZmJywgc3BlbGxjaGVjazogJ2ZhbHNlJywgJHdpZHRoOiAnMTAwJScgfSkpLCBkZXNjICYmIGRvbSgnc3BhbicsIHsgJGNvbG9yOiAnIzg4OCcgfSwgZGVzYykpO1xufVxuZnVuY3Rpb24gc2hvd1Byb21wdChjbSwgb3B0aW9ucykge1xuICAgIGlmIChrZXlUb0tleVN0YWNrLmxlbmd0aCkge1xuICAgICAgICBpZiAoIW9wdGlvbnMudmFsdWUpXG4gICAgICAgICAgICBvcHRpb25zLnZhbHVlID0gJyc7XG4gICAgICAgIHZpcnR1YWxQcm9tcHQgPSBvcHRpb25zO1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciB0ZW1wbGF0ZSA9IG1ha2VQcm9tcHQob3B0aW9ucy5wcmVmaXgsIG9wdGlvbnMuZGVzYyk7XG4gICAgaWYgKGNtLm9wZW5EaWFsb2cpIHtcbiAgICAgICAgY20ub3BlbkRpYWxvZyh0ZW1wbGF0ZSwgb3B0aW9ucy5vbkNsb3NlLCB7XG4gICAgICAgICAgICBvbktleURvd246IG9wdGlvbnMub25LZXlEb3duLCBvbktleVVwOiBvcHRpb25zLm9uS2V5VXAsXG4gICAgICAgICAgICBib3R0b206IHRydWUsIHNlbGVjdFZhbHVlT25PcGVuOiBmYWxzZSwgdmFsdWU6IG9wdGlvbnMudmFsdWVcbiAgICAgICAgfSk7XG4gICAgfVxuICAgIGVsc2Uge1xuICAgICAgICB2YXIgc2hvcnRUZXh0ID0gJyc7XG4gICAgICAgIGlmICh0eXBlb2Ygb3B0aW9ucy5wcmVmaXggIT0gXCJzdHJpbmdcIiAmJiBvcHRpb25zLnByZWZpeClcbiAgICAgICAgICAgIHNob3J0VGV4dCArPSBvcHRpb25zLnByZWZpeC50ZXh0Q29udGVudDtcbiAgICAgICAgaWYgKG9wdGlvbnMuZGVzYylcbiAgICAgICAgICAgIHNob3J0VGV4dCArPSBcIiBcIiArIG9wdGlvbnMuZGVzYztcbiAgICAgICAgb3B0aW9ucy5vbkNsb3NlKHByb21wdChzaG9ydFRleHQsICcnKSk7XG4gICAgfVxufVxuZnVuY3Rpb24gcmVnZXhFcXVhbChyMSwgcjIpIHtcbiAgICBpZiAocjEgaW5zdGFuY2VvZiBSZWdFeHAgJiYgcjIgaW5zdGFuY2VvZiBSZWdFeHApIHtcbiAgICAgICAgdmFyIHByb3BzID0gWydnbG9iYWwnLCAnbXVsdGlsaW5lJywgJ2lnbm9yZUNhc2UnLCAnc291cmNlJ107XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcHJvcHMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgIHZhciBwcm9wID0gcHJvcHNbaV07XG4gICAgICAgICAgICBpZiAocjFbcHJvcF0gIT09IHIyW3Byb3BdKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59XG5mdW5jdGlvbiB1cGRhdGVTZWFyY2hRdWVyeShjbSwgcmF3UXVlcnksIGlnbm9yZUNhc2UsIHNtYXJ0Q2FzZSkge1xuICAgIGlmICghcmF3UXVlcnkpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICB2YXIgc3RhdGUgPSBnZXRTZWFyY2hTdGF0ZShjbSk7XG4gICAgdmFyIHF1ZXJ5ID0gcGFyc2VRdWVyeShyYXdRdWVyeSwgISFpZ25vcmVDYXNlLCAhIXNtYXJ0Q2FzZSk7XG4gICAgaWYgKCFxdWVyeSkge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGhpZ2hsaWdodFNlYXJjaE1hdGNoZXMoY20sIHF1ZXJ5KTtcbiAgICBpZiAocmVnZXhFcXVhbChxdWVyeSwgc3RhdGUuZ2V0UXVlcnkoKSkpIHtcbiAgICAgICAgcmV0dXJuIHF1ZXJ5O1xuICAgIH1cbiAgICBzdGF0ZS5zZXRRdWVyeShxdWVyeSk7XG4gICAgcmV0dXJuIHF1ZXJ5O1xufVxuZnVuY3Rpb24gc2VhcmNoT3ZlcmxheShxdWVyeSkge1xuICAgIGlmIChxdWVyeS5zb3VyY2UuY2hhckF0KDApID09ICdeJykge1xuICAgICAgICB2YXIgbWF0Y2hTb2wgPSB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4ge1xuICAgICAgICB0b2tlbjogZnVuY3Rpb24gKHN0cmVhbSkge1xuICAgICAgICAgICAgaWYgKG1hdGNoU29sICYmICFzdHJlYW0uc29sKCkpIHtcbiAgICAgICAgICAgICAgICBzdHJlYW0uc2tpcFRvRW5kKCk7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIG1hdGNoID0gc3RyZWFtLm1hdGNoKHF1ZXJ5LCBmYWxzZSk7XG4gICAgICAgICAgICBpZiAobWF0Y2gpIHtcbiAgICAgICAgICAgICAgICBpZiAobWF0Y2hbMF0ubGVuZ3RoID09IDApIHtcbiAgICAgICAgICAgICAgICAgICAgc3RyZWFtLm5leHQoKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuICdzZWFyY2hpbmcnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoIXN0cmVhbS5zb2woKSkge1xuICAgICAgICAgICAgICAgICAgICBzdHJlYW0uYmFja1VwKDEpO1xuICAgICAgICAgICAgICAgICAgICBpZiAoIXF1ZXJ5LmV4ZWMoc3RyZWFtLm5leHQoKSArIG1hdGNoWzBdKSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgc3RyZWFtLm5leHQoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHN0cmVhbS5tYXRjaChxdWVyeSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuICdzZWFyY2hpbmcnO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgd2hpbGUgKCFzdHJlYW0uZW9sKCkpIHtcbiAgICAgICAgICAgICAgICBzdHJlYW0ubmV4dCgpO1xuICAgICAgICAgICAgICAgIGlmIChzdHJlYW0ubWF0Y2gocXVlcnksIGZhbHNlKSlcbiAgICAgICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIHF1ZXJ5OiBxdWVyeVxuICAgIH07XG59XG52YXIgaGlnaGxpZ2h0VGltZW91dCA9IDA7XG5mdW5jdGlvbiBoaWdobGlnaHRTZWFyY2hNYXRjaGVzKGNtLCBxdWVyeSkge1xuICAgIGNsZWFyVGltZW91dChoaWdobGlnaHRUaW1lb3V0KTtcbiAgICB2YXIgc2VhcmNoU3RhdGUgPSBnZXRTZWFyY2hTdGF0ZShjbSk7XG4gICAgc2VhcmNoU3RhdGUuaGlnaGxpZ2h0VGltZW91dCA9IGhpZ2hsaWdodFRpbWVvdXQ7XG4gICAgaGlnaGxpZ2h0VGltZW91dCA9IHNldFRpbWVvdXQoZnVuY3Rpb24gKCkge1xuICAgICAgICBpZiAoIWNtLnN0YXRlLnZpbSlcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgdmFyIHNlYXJjaFN0YXRlID0gZ2V0U2VhcmNoU3RhdGUoY20pO1xuICAgICAgICBzZWFyY2hTdGF0ZS5oaWdobGlnaHRUaW1lb3V0ID0gbnVsbDtcbiAgICAgICAgdmFyIG92ZXJsYXkgPSBzZWFyY2hTdGF0ZS5nZXRPdmVybGF5KCk7XG4gICAgICAgIGlmICghb3ZlcmxheSB8fCBxdWVyeSAhPSBvdmVybGF5LnF1ZXJ5KSB7XG4gICAgICAgICAgICBpZiAob3ZlcmxheSkge1xuICAgICAgICAgICAgICAgIGNtLnJlbW92ZU92ZXJsYXkob3ZlcmxheSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBvdmVybGF5ID0gc2VhcmNoT3ZlcmxheShxdWVyeSk7XG4gICAgICAgICAgICBjbS5hZGRPdmVybGF5KG92ZXJsYXkpO1xuICAgICAgICAgICAgaWYgKGNtLnNob3dNYXRjaGVzT25TY3JvbGxiYXIpIHtcbiAgICAgICAgICAgICAgICBpZiAoc2VhcmNoU3RhdGUuZ2V0U2Nyb2xsYmFyQW5ub3RhdGUoKSkge1xuICAgICAgICAgICAgICAgICAgICBzZWFyY2hTdGF0ZS5nZXRTY3JvbGxiYXJBbm5vdGF0ZSgpLmNsZWFyKCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHNlYXJjaFN0YXRlLnNldFNjcm9sbGJhckFubm90YXRlKGNtLnNob3dNYXRjaGVzT25TY3JvbGxiYXIocXVlcnkpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHNlYXJjaFN0YXRlLnNldE92ZXJsYXkob3ZlcmxheSk7XG4gICAgICAgIH1cbiAgICB9LCA1MCk7XG59XG5mdW5jdGlvbiBmaW5kTmV4dChjbSwgcHJldiwgcXVlcnksIHJlcGVhdCkge1xuICAgIGlmIChyZXBlYXQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICByZXBlYXQgPSAxO1xuICAgIH1cbiAgICByZXR1cm4gY20ub3BlcmF0aW9uKGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdmFyIHBvcyA9IGNtLmdldEN1cnNvcigpO1xuICAgICAgICB2YXIgY3Vyc29yID0gY20uZ2V0U2VhcmNoQ3Vyc29yKHF1ZXJ5LCBwb3MpO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJlcGVhdDsgaSsrKSB7XG4gICAgICAgICAgICB2YXIgZm91bmQgPSBjdXJzb3IuZmluZChwcmV2KTtcbiAgICAgICAgICAgIGlmIChpID09IDAgJiYgZm91bmQgJiYgY3Vyc29yRXF1YWwoY3Vyc29yLmZyb20oKSwgcG9zKSkge1xuICAgICAgICAgICAgICAgIHZhciBsYXN0RW5kUG9zID0gcHJldiA/IGN1cnNvci5mcm9tKCkgOiBjdXJzb3IudG8oKTtcbiAgICAgICAgICAgICAgICBmb3VuZCA9IGN1cnNvci5maW5kKHByZXYpO1xuICAgICAgICAgICAgICAgIGlmIChmb3VuZCAmJiAhZm91bmRbMF0gJiYgY3Vyc29yRXF1YWwoY3Vyc29yLmZyb20oKSwgbGFzdEVuZFBvcykpIHtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGNtLmdldExpbmUobGFzdEVuZFBvcy5saW5lKS5sZW5ndGggPT0gbGFzdEVuZFBvcy5jaClcbiAgICAgICAgICAgICAgICAgICAgICAgIGZvdW5kID0gY3Vyc29yLmZpbmQocHJldik7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFmb3VuZCkge1xuICAgICAgICAgICAgICAgIGN1cnNvciA9IGNtLmdldFNlYXJjaEN1cnNvcihxdWVyeSwgKHByZXYpID8gbmV3IFBvcyhjbS5sYXN0TGluZSgpKSA6IG5ldyBQb3MoY20uZmlyc3RMaW5lKCksIDApKTtcbiAgICAgICAgICAgICAgICBpZiAoIWN1cnNvci5maW5kKHByZXYpKSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGN1cnNvci5mcm9tKCk7XG4gICAgfSk7XG59XG5mdW5jdGlvbiBmaW5kTmV4dEZyb21BbmRUb0luY2x1c2l2ZShjbSwgcHJldiwgcXVlcnksIHJlcGVhdCwgdmltKSB7XG4gICAgaWYgKHJlcGVhdCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIHJlcGVhdCA9IDE7XG4gICAgfVxuICAgIHJldHVybiBjbS5vcGVyYXRpb24oZnVuY3Rpb24gKCkge1xuICAgICAgICB2YXIgcG9zID0gY20uZ2V0Q3Vyc29yKCk7XG4gICAgICAgIHZhciBjdXJzb3IgPSBjbS5nZXRTZWFyY2hDdXJzb3IocXVlcnksIHBvcyk7XG4gICAgICAgIHZhciBmb3VuZCA9IGN1cnNvci5maW5kKCFwcmV2KTtcbiAgICAgICAgaWYgKCF2aW0udmlzdWFsTW9kZSAmJiBmb3VuZCAmJiBjdXJzb3JFcXVhbChjdXJzb3IuZnJvbSgpLCBwb3MpKSB7XG4gICAgICAgICAgICBjdXJzb3IuZmluZCghcHJldik7XG4gICAgICAgIH1cbiAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCByZXBlYXQ7IGkrKykge1xuICAgICAgICAgICAgZm91bmQgPSBjdXJzb3IuZmluZChwcmV2KTtcbiAgICAgICAgICAgIGlmICghZm91bmQpIHtcbiAgICAgICAgICAgICAgICBjdXJzb3IgPSBjbS5nZXRTZWFyY2hDdXJzb3IocXVlcnksIChwcmV2KSA/IG5ldyBQb3MoY20ubGFzdExpbmUoKSkgOiBuZXcgUG9zKGNtLmZpcnN0TGluZSgpLCAwKSk7XG4gICAgICAgICAgICAgICAgaWYgKCFjdXJzb3IuZmluZChwcmV2KSkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBbY3Vyc29yLmZyb20oKSwgY3Vyc29yLnRvKCldO1xuICAgIH0pO1xufVxuZnVuY3Rpb24gY2xlYXJTZWFyY2hIaWdobGlnaHQoY20pIHtcbiAgICB2YXIgc3RhdGUgPSBnZXRTZWFyY2hTdGF0ZShjbSk7XG4gICAgaWYgKHN0YXRlLmhpZ2hsaWdodFRpbWVvdXQpIHtcbiAgICAgICAgY2xlYXJUaW1lb3V0KHN0YXRlLmhpZ2hsaWdodFRpbWVvdXQpO1xuICAgICAgICBzdGF0ZS5oaWdobGlnaHRUaW1lb3V0ID0gbnVsbDtcbiAgICB9XG4gICAgY20ucmVtb3ZlT3ZlcmxheShnZXRTZWFyY2hTdGF0ZShjbSkuZ2V0T3ZlcmxheSgpKTtcbiAgICBzdGF0ZS5zZXRPdmVybGF5KG51bGwpO1xuICAgIGlmIChzdGF0ZS5nZXRTY3JvbGxiYXJBbm5vdGF0ZSgpKSB7XG4gICAgICAgIHN0YXRlLmdldFNjcm9sbGJhckFubm90YXRlKCkuY2xlYXIoKTtcbiAgICAgICAgc3RhdGUuc2V0U2Nyb2xsYmFyQW5ub3RhdGUobnVsbCk7XG4gICAgfVxufVxuZnVuY3Rpb24gaXNJblJhbmdlKHBvcywgc3RhcnQsIGVuZCkge1xuICAgIGlmICh0eXBlb2YgcG9zICE9ICdudW1iZXInKSB7XG4gICAgICAgIHBvcyA9IHBvcy5saW5lO1xuICAgIH1cbiAgICBpZiAoc3RhcnQgaW5zdGFuY2VvZiBBcnJheSkge1xuICAgICAgICByZXR1cm4gaW5BcnJheShwb3MsIHN0YXJ0KTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGlmICh0eXBlb2YgZW5kID09ICdudW1iZXInKSB7XG4gICAgICAgICAgICByZXR1cm4gKHBvcyA+PSBzdGFydCAmJiBwb3MgPD0gZW5kKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBwb3MgPT0gc3RhcnQ7XG4gICAgICAgIH1cbiAgICB9XG59XG5mdW5jdGlvbiBnZXRVc2VyVmlzaWJsZUxpbmVzKGNtKSB7XG4gICAgdmFyIHJlbmRlcmVyID0gY20uYWNlLnJlbmRlcmVyO1xuICAgIHJldHVybiB7XG4gICAgICAgIHRvcDogcmVuZGVyZXIuZ2V0Rmlyc3RGdWxseVZpc2libGVSb3coKSxcbiAgICAgICAgYm90dG9tOiByZW5kZXJlci5nZXRMYXN0RnVsbHlWaXNpYmxlUm93KClcbiAgICB9O1xufVxuZnVuY3Rpb24gZ2V0TWFya1BvcyhjbSwgdmltLCBtYXJrTmFtZSkge1xuICAgIGlmIChtYXJrTmFtZSA9PSAnXFwnJyB8fCBtYXJrTmFtZSA9PSAnYCcpIHtcbiAgICAgICAgcmV0dXJuIHZpbUdsb2JhbFN0YXRlLmp1bXBMaXN0LmZpbmQoY20sIC0xKSB8fCBuZXcgUG9zKDAsIDApO1xuICAgIH1cbiAgICBlbHNlIGlmIChtYXJrTmFtZSA9PSAnLicpIHtcbiAgICAgICAgcmV0dXJuIGdldExhc3RFZGl0UG9zKGNtKTtcbiAgICB9XG4gICAgdmFyIG1hcmsgPSB2aW0ubWFya3NbbWFya05hbWVdO1xuICAgIHJldHVybiBtYXJrICYmIG1hcmsuZmluZCgpO1xufVxuZnVuY3Rpb24gZ2V0TGFzdEVkaXRQb3MoY20pIHtcbiAgICBpZiAoY20uZ2V0TGFzdEVkaXRFbmQpIHtcbiAgICAgICAgcmV0dXJuIGNtLmdldExhc3RFZGl0RW5kKCk7XG4gICAgfVxuICAgIHZhciBkb25lID0gY20uZG9jLmhpc3RvcnkuZG9uZTtcbiAgICBmb3IgKHZhciBpID0gZG9uZS5sZW5ndGg7IGktLTspIHtcbiAgICAgICAgaWYgKGRvbmVbaV0uY2hhbmdlcykge1xuICAgICAgICAgICAgcmV0dXJuIGNvcHlDdXJzb3IoZG9uZVtpXS5jaGFuZ2VzWzBdLnRvKTtcbiAgICAgICAgfVxuICAgIH1cbn1cbnZhciBFeENvbW1hbmREaXNwYXRjaGVyID0gZnVuY3Rpb24gKCkge1xuICAgIHRoaXMuYnVpbGRDb21tYW5kTWFwXygpO1xufTtcbkV4Q29tbWFuZERpc3BhdGNoZXIucHJvdG90eXBlID0ge1xuICAgIHByb2Nlc3NDb21tYW5kOiBmdW5jdGlvbiAoY20sIGlucHV0LCBvcHRfcGFyYW1zKSB7XG4gICAgICAgIHZhciB0aGF0ID0gdGhpcztcbiAgICAgICAgY20ub3BlcmF0aW9uKGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgIGNtLmN1ck9wLmlzVmltT3AgPSB0cnVlO1xuICAgICAgICAgICAgdGhhdC5fcHJvY2Vzc0NvbW1hbmQoY20sIGlucHV0LCBvcHRfcGFyYW1zKTtcbiAgICAgICAgfSk7XG4gICAgfSxcbiAgICBfcHJvY2Vzc0NvbW1hbmQ6IGZ1bmN0aW9uIChjbSwgaW5wdXQsIG9wdF9wYXJhbXMpIHtcbiAgICAgICAgdmFyIHZpbSA9IGNtLnN0YXRlLnZpbTtcbiAgICAgICAgdmFyIGNvbW1hbmRIaXN0b3J5UmVnaXN0ZXIgPSB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIuZ2V0UmVnaXN0ZXIoJzonKTtcbiAgICAgICAgdmFyIHByZXZpb3VzQ29tbWFuZCA9IGNvbW1hbmRIaXN0b3J5UmVnaXN0ZXIudG9TdHJpbmcoKTtcbiAgICAgICAgdmFyIGlucHV0U3RyZWFtID0gbmV3IENvZGVNaXJyb3IuU3RyaW5nU3RyZWFtKGlucHV0KTtcbiAgICAgICAgY29tbWFuZEhpc3RvcnlSZWdpc3Rlci5zZXRUZXh0KGlucHV0KTtcbiAgICAgICAgdmFyIHBhcmFtcyA9IG9wdF9wYXJhbXMgfHwge307XG4gICAgICAgIHBhcmFtcy5pbnB1dCA9IGlucHV0O1xuICAgICAgICB0cnkge1xuICAgICAgICAgICAgdGhpcy5wYXJzZUlucHV0XyhjbSwgaW5wdXRTdHJlYW0sIHBhcmFtcyk7XG4gICAgICAgIH1cbiAgICAgICAgY2F0Y2ggKGUpIHtcbiAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCBlLnRvU3RyaW5nKCkpO1xuICAgICAgICAgICAgdGhyb3cgZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIGV4aXRWaXN1YWxNb2RlKGNtKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgY29tbWFuZDtcbiAgICAgICAgdmFyIGNvbW1hbmROYW1lO1xuICAgICAgICBpZiAoIXBhcmFtcy5jb21tYW5kTmFtZSkge1xuICAgICAgICAgICAgaWYgKHBhcmFtcy5saW5lICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgICAgICBjb21tYW5kTmFtZSA9ICdtb3ZlJztcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGNvbW1hbmQgPSB0aGlzLm1hdGNoQ29tbWFuZF8ocGFyYW1zLmNvbW1hbmROYW1lKTtcbiAgICAgICAgICAgIGlmIChjb21tYW5kKSB7XG4gICAgICAgICAgICAgICAgY29tbWFuZE5hbWUgPSBjb21tYW5kLm5hbWU7XG4gICAgICAgICAgICAgICAgaWYgKGNvbW1hbmQuZXhjbHVkZUZyb21Db21tYW5kSGlzdG9yeSkge1xuICAgICAgICAgICAgICAgICAgICBjb21tYW5kSGlzdG9yeVJlZ2lzdGVyLnNldFRleHQocHJldmlvdXNDb21tYW5kKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdGhpcy5wYXJzZUNvbW1hbmRBcmdzXyhpbnB1dFN0cmVhbSwgcGFyYW1zLCBjb21tYW5kKTtcbiAgICAgICAgICAgICAgICBpZiAoY29tbWFuZC50eXBlID09ICdleFRvS2V5Jykge1xuICAgICAgICAgICAgICAgICAgICBkb0tleVRvS2V5KGNtLCBjb21tYW5kLnRvS2V5cywgY29tbWFuZCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY29tbWFuZC50eXBlID09ICdleFRvRXgnKSB7XG4gICAgICAgICAgICAgICAgICAgIHRoaXMucHJvY2Vzc0NvbW1hbmQoY20sIGNvbW1hbmQudG9JbnB1dCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKCFjb21tYW5kTmFtZSkge1xuICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdOb3QgYW4gZWRpdG9yIGNvbW1hbmQgXCI6JyArIGlucHV0ICsgJ1wiJyk7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICAgIGV4Q29tbWFuZHNbY29tbWFuZE5hbWVdKGNtLCBwYXJhbXMpO1xuICAgICAgICAgICAgaWYgKCghY29tbWFuZCB8fCAhY29tbWFuZC5wb3NzaWJseUFzeW5jKSAmJiBwYXJhbXMuY2FsbGJhY2spIHtcbiAgICAgICAgICAgICAgICBwYXJhbXMuY2FsbGJhY2soKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBjYXRjaCAoZSkge1xuICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sIGUudG9TdHJpbmcoKSk7XG4gICAgICAgICAgICB0aHJvdyBlO1xuICAgICAgICB9XG4gICAgfSxcbiAgICBwYXJzZUlucHV0XzogZnVuY3Rpb24gKGNtLCBpbnB1dFN0cmVhbSwgcmVzdWx0KSB7XG4gICAgICAgIGlucHV0U3RyZWFtLmVhdFdoaWxlKCc6Jyk7XG4gICAgICAgIGlmIChpbnB1dFN0cmVhbS5lYXQoJyUnKSkge1xuICAgICAgICAgICAgcmVzdWx0LmxpbmUgPSBjbS5maXJzdExpbmUoKTtcbiAgICAgICAgICAgIHJlc3VsdC5saW5lRW5kID0gY20ubGFzdExpbmUoKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJlc3VsdC5saW5lID0gdGhpcy5wYXJzZUxpbmVTcGVjXyhjbSwgaW5wdXRTdHJlYW0pO1xuICAgICAgICAgICAgaWYgKHJlc3VsdC5saW5lICE9PSB1bmRlZmluZWQgJiYgaW5wdXRTdHJlYW0uZWF0KCcsJykpIHtcbiAgICAgICAgICAgICAgICByZXN1bHQubGluZUVuZCA9IHRoaXMucGFyc2VMaW5lU3BlY18oY20sIGlucHV0U3RyZWFtKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAocmVzdWx0LmxpbmUgPT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgICBpZiAoY20uc3RhdGUudmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgICAgICB2YXIgcG9zID0gZ2V0TWFya1BvcyhjbSwgY20uc3RhdGUudmltLCAnPCcpO1xuICAgICAgICAgICAgICAgIHJlc3VsdC5zZWxlY3Rpb25MaW5lID0gcG9zICYmIHBvcy5saW5lO1xuICAgICAgICAgICAgICAgIHBvcyA9IGdldE1hcmtQb3MoY20sIGNtLnN0YXRlLnZpbSwgJz4nKTtcbiAgICAgICAgICAgICAgICByZXN1bHQuc2VsZWN0aW9uTGluZUVuZCA9IHBvcyAmJiBwb3MubGluZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHJlc3VsdC5zZWxlY3Rpb25MaW5lID0gY20uZ2V0Q3Vyc29yKCkubGluZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHJlc3VsdC5zZWxlY3Rpb25MaW5lID0gcmVzdWx0LmxpbmU7XG4gICAgICAgICAgICByZXN1bHQuc2VsZWN0aW9uTGluZUVuZCA9IHJlc3VsdC5saW5lRW5kO1xuICAgICAgICB9XG4gICAgICAgIHZhciBjb21tYW5kTWF0Y2ggPSBpbnB1dFN0cmVhbS5tYXRjaCgvXihcXHcrfCEhfEBAfFshIyYqPD0+QH5dKS8pO1xuICAgICAgICBpZiAoY29tbWFuZE1hdGNoKSB7XG4gICAgICAgICAgICByZXN1bHQuY29tbWFuZE5hbWUgPSBjb21tYW5kTWF0Y2hbMV07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICByZXN1bHQuY29tbWFuZE5hbWUgPSBpbnB1dFN0cmVhbS5tYXRjaCgvLiovKVswXTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcmVzdWx0O1xuICAgIH0sXG4gICAgcGFyc2VMaW5lU3BlY186IGZ1bmN0aW9uIChjbSwgaW5wdXRTdHJlYW0pIHtcbiAgICAgICAgdmFyIG51bWJlck1hdGNoID0gaW5wdXRTdHJlYW0ubWF0Y2goL14oXFxkKykvKTtcbiAgICAgICAgaWYgKG51bWJlck1hdGNoKSB7XG4gICAgICAgICAgICByZXR1cm4gcGFyc2VJbnQobnVtYmVyTWF0Y2hbMV0sIDEwKSAtIDE7XG4gICAgICAgIH1cbiAgICAgICAgc3dpdGNoIChpbnB1dFN0cmVhbS5uZXh0KCkpIHtcbiAgICAgICAgICAgIGNhc2UgJy4nOlxuICAgICAgICAgICAgICAgIHJldHVybiB0aGlzLnBhcnNlTGluZVNwZWNPZmZzZXRfKGlucHV0U3RyZWFtLCBjbS5nZXRDdXJzb3IoKS5saW5lKTtcbiAgICAgICAgICAgIGNhc2UgJyQnOlxuICAgICAgICAgICAgICAgIHJldHVybiB0aGlzLnBhcnNlTGluZVNwZWNPZmZzZXRfKGlucHV0U3RyZWFtLCBjbS5sYXN0TGluZSgpKTtcbiAgICAgICAgICAgIGNhc2UgJ1xcJyc6XG4gICAgICAgICAgICAgICAgdmFyIG1hcmtOYW1lID0gaW5wdXRTdHJlYW0ubmV4dCgpO1xuICAgICAgICAgICAgICAgIHZhciBtYXJrUG9zID0gZ2V0TWFya1BvcyhjbSwgY20uc3RhdGUudmltLCBtYXJrTmFtZSk7XG4gICAgICAgICAgICAgICAgaWYgKCFtYXJrUG9zKVxuICAgICAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ01hcmsgbm90IHNldCcpO1xuICAgICAgICAgICAgICAgIHJldHVybiB0aGlzLnBhcnNlTGluZVNwZWNPZmZzZXRfKGlucHV0U3RyZWFtLCBtYXJrUG9zLmxpbmUpO1xuICAgICAgICAgICAgY2FzZSAnLSc6XG4gICAgICAgICAgICBjYXNlICcrJzpcbiAgICAgICAgICAgICAgICBpbnB1dFN0cmVhbS5iYWNrVXAoMSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHRoaXMucGFyc2VMaW5lU3BlY09mZnNldF8oaW5wdXRTdHJlYW0sIGNtLmdldEN1cnNvcigpLmxpbmUpO1xuICAgICAgICAgICAgZGVmYXVsdDpcbiAgICAgICAgICAgICAgICBpbnB1dFN0cmVhbS5iYWNrVXAoMSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgcGFyc2VMaW5lU3BlY09mZnNldF86IGZ1bmN0aW9uIChpbnB1dFN0cmVhbSwgbGluZSkge1xuICAgICAgICB2YXIgb2Zmc2V0TWF0Y2ggPSBpbnB1dFN0cmVhbS5tYXRjaCgvXihbKy1dKT8oXFxkKykvKTtcbiAgICAgICAgaWYgKG9mZnNldE1hdGNoKSB7XG4gICAgICAgICAgICB2YXIgb2Zmc2V0ID0gcGFyc2VJbnQob2Zmc2V0TWF0Y2hbMl0sIDEwKTtcbiAgICAgICAgICAgIGlmIChvZmZzZXRNYXRjaFsxXSA9PSBcIi1cIikge1xuICAgICAgICAgICAgICAgIGxpbmUgLT0gb2Zmc2V0O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgbGluZSArPSBvZmZzZXQ7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGxpbmU7XG4gICAgfSxcbiAgICBwYXJzZUNvbW1hbmRBcmdzXzogZnVuY3Rpb24gKGlucHV0U3RyZWFtLCBwYXJhbXMsIGNvbW1hbmQpIHtcbiAgICAgICAgaWYgKGlucHV0U3RyZWFtLmVvbCgpKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgcGFyYW1zLmFyZ1N0cmluZyA9IGlucHV0U3RyZWFtLm1hdGNoKC8uKi8pWzBdO1xuICAgICAgICB2YXIgZGVsaW0gPSBjb21tYW5kLmFyZ0RlbGltaXRlciB8fCAvXFxzKy87XG4gICAgICAgIHZhciBhcmdzID0gdHJpbShwYXJhbXMuYXJnU3RyaW5nKS5zcGxpdChkZWxpbSk7XG4gICAgICAgIGlmIChhcmdzLmxlbmd0aCAmJiBhcmdzWzBdKSB7XG4gICAgICAgICAgICBwYXJhbXMuYXJncyA9IGFyZ3M7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIG1hdGNoQ29tbWFuZF86IGZ1bmN0aW9uIChjb21tYW5kTmFtZSkge1xuICAgICAgICBmb3IgKHZhciBpID0gY29tbWFuZE5hbWUubGVuZ3RoOyBpID4gMDsgaS0tKSB7XG4gICAgICAgICAgICB2YXIgcHJlZml4ID0gY29tbWFuZE5hbWUuc3Vic3RyaW5nKDAsIGkpO1xuICAgICAgICAgICAgaWYgKHRoaXMuY29tbWFuZE1hcF9bcHJlZml4XSkge1xuICAgICAgICAgICAgICAgIHZhciBjb21tYW5kID0gdGhpcy5jb21tYW5kTWFwX1twcmVmaXhdO1xuICAgICAgICAgICAgICAgIGlmIChjb21tYW5kLm5hbWUuaW5kZXhPZihjb21tYW5kTmFtZSkgPT09IDApIHtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIGNvbW1hbmQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBudWxsO1xuICAgIH0sXG4gICAgYnVpbGRDb21tYW5kTWFwXzogZnVuY3Rpb24gKCkge1xuICAgICAgICB0aGlzLmNvbW1hbmRNYXBfID0ge307XG4gICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZGVmYXVsdEV4Q29tbWFuZE1hcC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgdmFyIGNvbW1hbmQgPSBkZWZhdWx0RXhDb21tYW5kTWFwW2ldO1xuICAgICAgICAgICAgdmFyIGtleSA9IGNvbW1hbmQuc2hvcnROYW1lIHx8IGNvbW1hbmQubmFtZTtcbiAgICAgICAgICAgIHRoaXMuY29tbWFuZE1hcF9ba2V5XSA9IGNvbW1hbmQ7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIG1hcDogZnVuY3Rpb24gKGxocywgcmhzLCBjdHgsIG5vcmVtYXApIHtcbiAgICAgICAgaWYgKGxocyAhPSAnOicgJiYgbGhzLmNoYXJBdCgwKSA9PSAnOicpIHtcbiAgICAgICAgICAgIGlmIChjdHgpIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBFcnJvcignTW9kZSBub3Qgc3VwcG9ydGVkIGZvciBleCBtYXBwaW5ncycpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIGNvbW1hbmROYW1lID0gbGhzLnN1YnN0cmluZygxKTtcbiAgICAgICAgICAgIGlmIChyaHMgIT0gJzonICYmIHJocy5jaGFyQXQoMCkgPT0gJzonKSB7XG4gICAgICAgICAgICAgICAgdGhpcy5jb21tYW5kTWFwX1tjb21tYW5kTmFtZV0gPSB7XG4gICAgICAgICAgICAgICAgICAgIG5hbWU6IGNvbW1hbmROYW1lLFxuICAgICAgICAgICAgICAgICAgICB0eXBlOiAnZXhUb0V4JyxcbiAgICAgICAgICAgICAgICAgICAgdG9JbnB1dDogcmhzLnN1YnN0cmluZygxKSxcbiAgICAgICAgICAgICAgICAgICAgdXNlcjogdHJ1ZVxuICAgICAgICAgICAgICAgIH07XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aGlzLmNvbW1hbmRNYXBfW2NvbW1hbmROYW1lXSA9IHtcbiAgICAgICAgICAgICAgICAgICAgbmFtZTogY29tbWFuZE5hbWUsXG4gICAgICAgICAgICAgICAgICAgIHR5cGU6ICdleFRvS2V5JyxcbiAgICAgICAgICAgICAgICAgICAgdG9LZXlzOiByaHMsXG4gICAgICAgICAgICAgICAgICAgIHVzZXI6IHRydWVcbiAgICAgICAgICAgICAgICB9O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdmFyIG1hcHBpbmcgPSB7XG4gICAgICAgICAgICAgICAga2V5czogbGhzLFxuICAgICAgICAgICAgICAgIHR5cGU6ICdrZXlUb0tleScsXG4gICAgICAgICAgICAgICAgdG9LZXlzOiByaHMsXG4gICAgICAgICAgICAgICAgbm9yZW1hcDogISFub3JlbWFwXG4gICAgICAgICAgICB9O1xuICAgICAgICAgICAgaWYgKGN0eCkge1xuICAgICAgICAgICAgICAgIG1hcHBpbmcuY29udGV4dCA9IGN0eDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGRlZmF1bHRLZXltYXAudW5zaGlmdChtYXBwaW5nKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgdW5tYXA6IGZ1bmN0aW9uIChsaHMsIGN0eCkge1xuICAgICAgICBpZiAobGhzICE9ICc6JyAmJiBsaHMuY2hhckF0KDApID09ICc6Jykge1xuICAgICAgICAgICAgaWYgKGN0eCkge1xuICAgICAgICAgICAgICAgIHRocm93IEVycm9yKCdNb2RlIG5vdCBzdXBwb3J0ZWQgZm9yIGV4IG1hcHBpbmdzJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2YXIgY29tbWFuZE5hbWUgPSBsaHMuc3Vic3RyaW5nKDEpO1xuICAgICAgICAgICAgaWYgKHRoaXMuY29tbWFuZE1hcF9bY29tbWFuZE5hbWVdICYmIHRoaXMuY29tbWFuZE1hcF9bY29tbWFuZE5hbWVdLnVzZXIpIHtcbiAgICAgICAgICAgICAgICBkZWxldGUgdGhpcy5jb21tYW5kTWFwX1tjb21tYW5kTmFtZV07XG4gICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YXIga2V5cyA9IGxocztcbiAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgZGVmYXVsdEtleW1hcC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGlmIChrZXlzID09IGRlZmF1bHRLZXltYXBbaV0ua2V5c1xuICAgICAgICAgICAgICAgICAgICAmJiBkZWZhdWx0S2V5bWFwW2ldLmNvbnRleHQgPT09IGN0eCkge1xuICAgICAgICAgICAgICAgICAgICBkZWZhdWx0S2V5bWFwLnNwbGljZShpLCAxKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxufTtcbnZhciBleENvbW1hbmRzID0ge1xuICAgIGNvbG9yc2NoZW1lOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICBpZiAoIXBhcmFtcy5hcmdzIHx8IHBhcmFtcy5hcmdzLmxlbmd0aCA8IDEpIHtcbiAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCBjbS5nZXRPcHRpb24oJ3RoZW1lJykpO1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIGNtLnNldE9wdGlvbigndGhlbWUnLCBwYXJhbXMuYXJnc1swXSk7XG4gICAgfSxcbiAgICBtYXA6IGZ1bmN0aW9uIChjbSwgcGFyYW1zLCBjdHgsIGRlZmF1bHRPbmx5KSB7XG4gICAgICAgIHZhciBtYXBBcmdzID0gcGFyYW1zLmFyZ3M7XG4gICAgICAgIGlmICghbWFwQXJncyB8fCBtYXBBcmdzLmxlbmd0aCA8IDIpIHtcbiAgICAgICAgICAgIGlmIChjbSkge1xuICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnSW52YWxpZCBtYXBwaW5nOiAnICsgcGFyYW1zLmlucHV0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBleENvbW1hbmREaXNwYXRjaGVyLm1hcChtYXBBcmdzWzBdLCBtYXBBcmdzWzFdLCBjdHgsIGRlZmF1bHRPbmx5KTtcbiAgICB9LFxuICAgIGltYXA6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7IHRoaXMubWFwKGNtLCBwYXJhbXMsICdpbnNlcnQnKTsgfSxcbiAgICBubWFwOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB0aGlzLm1hcChjbSwgcGFyYW1zLCAnbm9ybWFsJyk7IH0sXG4gICAgdm1hcDogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHsgdGhpcy5tYXAoY20sIHBhcmFtcywgJ3Zpc3VhbCcpOyB9LFxuICAgIG9tYXA6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7IHRoaXMubWFwKGNtLCBwYXJhbXMsICdvcGVyYXRvclBlbmRpbmcnKTsgfSxcbiAgICBub3JlbWFwOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB0aGlzLm1hcChjbSwgcGFyYW1zLCB1bmRlZmluZWQsIHRydWUpOyB9LFxuICAgIGlub3JlbWFwOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB0aGlzLm1hcChjbSwgcGFyYW1zLCAnaW5zZXJ0JywgdHJ1ZSk7IH0sXG4gICAgbm5vcmVtYXA6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7IHRoaXMubWFwKGNtLCBwYXJhbXMsICdub3JtYWwnLCB0cnVlKTsgfSxcbiAgICB2bm9yZW1hcDogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHsgdGhpcy5tYXAoY20sIHBhcmFtcywgJ3Zpc3VhbCcsIHRydWUpOyB9LFxuICAgIG9ub3JlbWFwOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB0aGlzLm1hcChjbSwgcGFyYW1zLCAnb3BlcmF0b3JQZW5kaW5nJywgdHJ1ZSk7IH0sXG4gICAgdW5tYXA6IGZ1bmN0aW9uIChjbSwgcGFyYW1zLCBjdHgpIHtcbiAgICAgICAgdmFyIG1hcEFyZ3MgPSBwYXJhbXMuYXJncztcbiAgICAgICAgaWYgKCFtYXBBcmdzIHx8IG1hcEFyZ3MubGVuZ3RoIDwgMSB8fCAhZXhDb21tYW5kRGlzcGF0Y2hlci51bm1hcChtYXBBcmdzWzBdLCBjdHgpKSB7XG4gICAgICAgICAgICBpZiAoY20pIHtcbiAgICAgICAgICAgICAgICBzaG93Q29uZmlybShjbSwgJ05vIHN1Y2ggbWFwcGluZzogJyArIHBhcmFtcy5pbnB1dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIG1hcGNsZWFyOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB2aW1BcGkubWFwY2xlYXIoKTsgfSxcbiAgICBpbWFwY2xlYXI6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7IHZpbUFwaS5tYXBjbGVhcignaW5zZXJ0Jyk7IH0sXG4gICAgbm1hcGNsZWFyOiBmdW5jdGlvbiAoY20sIHBhcmFtcykgeyB2aW1BcGkubWFwY2xlYXIoJ25vcm1hbCcpOyB9LFxuICAgIHZtYXBjbGVhcjogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHsgdmltQXBpLm1hcGNsZWFyKCd2aXN1YWwnKTsgfSxcbiAgICBvbWFwY2xlYXI6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7IHZpbUFwaS5tYXBjbGVhcignb3BlcmF0b3JQZW5kaW5nJyk7IH0sXG4gICAgbW92ZTogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHtcbiAgICAgICAgY29tbWFuZERpc3BhdGNoZXIucHJvY2Vzc0NvbW1hbmQoY20sIGNtLnN0YXRlLnZpbSwge1xuICAgICAgICAgICAgdHlwZTogJ21vdGlvbicsXG4gICAgICAgICAgICBtb3Rpb246ICdtb3ZlVG9MaW5lT3JFZGdlT2ZEb2N1bWVudCcsXG4gICAgICAgICAgICBtb3Rpb25BcmdzOiB7IGZvcndhcmQ6IGZhbHNlLCBleHBsaWNpdFJlcGVhdDogdHJ1ZSxcbiAgICAgICAgICAgICAgICBsaW5ld2lzZTogdHJ1ZSB9LFxuICAgICAgICAgICAgcmVwZWF0T3ZlcnJpZGU6IHBhcmFtcy5saW5lICsgMVxuICAgICAgICB9KTtcbiAgICB9LFxuICAgIHNldDogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHtcbiAgICAgICAgdmFyIHNldEFyZ3MgPSBwYXJhbXMuYXJncztcbiAgICAgICAgdmFyIHNldENmZyA9IHBhcmFtcy5zZXRDZmcgfHwge307XG4gICAgICAgIGlmICghc2V0QXJncyB8fCBzZXRBcmdzLmxlbmd0aCA8IDEpIHtcbiAgICAgICAgICAgIGlmIChjbSkge1xuICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnSW52YWxpZCBtYXBwaW5nOiAnICsgcGFyYW1zLmlucHV0KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgZXhwciA9IHNldEFyZ3NbMF0uc3BsaXQoJz0nKTtcbiAgICAgICAgdmFyIG9wdGlvbk5hbWUgPSBleHByWzBdO1xuICAgICAgICB2YXIgdmFsdWUgPSBleHByWzFdO1xuICAgICAgICB2YXIgZm9yY2VHZXQgPSBmYWxzZTtcbiAgICAgICAgdmFyIGZvcmNlVG9nZ2xlID0gZmFsc2U7XG4gICAgICAgIGlmIChvcHRpb25OYW1lLmNoYXJBdChvcHRpb25OYW1lLmxlbmd0aCAtIDEpID09ICc/Jykge1xuICAgICAgICAgICAgaWYgKHZhbHVlKSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgRXJyb3IoJ1RyYWlsaW5nIGNoYXJhY3RlcnM6ICcgKyBwYXJhbXMuYXJnU3RyaW5nKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG9wdGlvbk5hbWUgPSBvcHRpb25OYW1lLnN1YnN0cmluZygwLCBvcHRpb25OYW1lLmxlbmd0aCAtIDEpO1xuICAgICAgICAgICAgZm9yY2VHZXQgPSB0cnVlO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKG9wdGlvbk5hbWUuY2hhckF0KG9wdGlvbk5hbWUubGVuZ3RoIC0gMSkgPT0gJyEnKSB7XG4gICAgICAgICAgICBvcHRpb25OYW1lID0gb3B0aW9uTmFtZS5zdWJzdHJpbmcoMCwgb3B0aW9uTmFtZS5sZW5ndGggLSAxKTtcbiAgICAgICAgICAgIGZvcmNlVG9nZ2xlID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodmFsdWUgPT09IHVuZGVmaW5lZCAmJiBvcHRpb25OYW1lLnN1YnN0cmluZygwLCAyKSA9PSAnbm8nKSB7XG4gICAgICAgICAgICBvcHRpb25OYW1lID0gb3B0aW9uTmFtZS5zdWJzdHJpbmcoMik7XG4gICAgICAgICAgICB2YWx1ZSA9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIHZhciBvcHRpb25Jc0Jvb2xlYW4gPSBvcHRpb25zW29wdGlvbk5hbWVdICYmIG9wdGlvbnNbb3B0aW9uTmFtZV0udHlwZSA9PSAnYm9vbGVhbic7XG4gICAgICAgIGlmIChvcHRpb25Jc0Jvb2xlYW4pIHtcbiAgICAgICAgICAgIGlmIChmb3JjZVRvZ2dsZSkge1xuICAgICAgICAgICAgICAgIHZhbHVlID0gIWdldE9wdGlvbihvcHRpb25OYW1lLCBjbSwgc2V0Q2ZnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKHZhbHVlID09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgICAgIHZhbHVlID0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAoIW9wdGlvbklzQm9vbGVhbiAmJiB2YWx1ZSA9PT0gdW5kZWZpbmVkIHx8IGZvcmNlR2V0KSB7XG4gICAgICAgICAgICB2YXIgb2xkVmFsdWUgPSBnZXRPcHRpb24ob3B0aW9uTmFtZSwgY20sIHNldENmZyk7XG4gICAgICAgICAgICBpZiAob2xkVmFsdWUgaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCBvbGRWYWx1ZS5tZXNzYWdlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKG9sZFZhbHVlID09PSB0cnVlIHx8IG9sZFZhbHVlID09PSBmYWxzZSkge1xuICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnICcgKyAob2xkVmFsdWUgPyAnJyA6ICdubycpICsgb3B0aW9uTmFtZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBzaG93Q29uZmlybShjbSwgJyAgJyArIG9wdGlvbk5hbWUgKyAnPScgKyBvbGRWYWx1ZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YXIgc2V0T3B0aW9uUmV0dXJuID0gc2V0T3B0aW9uKG9wdGlvbk5hbWUsIHZhbHVlLCBjbSwgc2V0Q2ZnKTtcbiAgICAgICAgICAgIGlmIChzZXRPcHRpb25SZXR1cm4gaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCBzZXRPcHRpb25SZXR1cm4ubWVzc2FnZSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LFxuICAgIHNldGxvY2FsOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICBwYXJhbXMuc2V0Q2ZnID0geyBzY29wZTogJ2xvY2FsJyB9O1xuICAgICAgICB0aGlzLnNldChjbSwgcGFyYW1zKTtcbiAgICB9LFxuICAgIHNldGdsb2JhbDogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHtcbiAgICAgICAgcGFyYW1zLnNldENmZyA9IHsgc2NvcGU6ICdnbG9iYWwnIH07XG4gICAgICAgIHRoaXMuc2V0KGNtLCBwYXJhbXMpO1xuICAgIH0sXG4gICAgcmVnaXN0ZXJzOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICB2YXIgcmVnQXJncyA9IHBhcmFtcy5hcmdzO1xuICAgICAgICB2YXIgcmVnaXN0ZXJzID0gdmltR2xvYmFsU3RhdGUucmVnaXN0ZXJDb250cm9sbGVyLnJlZ2lzdGVycztcbiAgICAgICAgdmFyIHJlZ0luZm8gPSAnLS0tLS0tLS0tLVJlZ2lzdGVycy0tLS0tLS0tLS1cXG5cXG4nO1xuICAgICAgICBpZiAoIXJlZ0FyZ3MpIHtcbiAgICAgICAgICAgIGZvciAodmFyIHJlZ2lzdGVyTmFtZSBpbiByZWdpc3RlcnMpIHtcbiAgICAgICAgICAgICAgICB2YXIgdGV4dCA9IHJlZ2lzdGVyc1tyZWdpc3Rlck5hbWVdLnRvU3RyaW5nKCk7XG4gICAgICAgICAgICAgICAgaWYgKHRleHQubGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgICAgIHJlZ0luZm8gKz0gJ1wiJyArIHJlZ2lzdGVyTmFtZSArICcgICAgJyArIHRleHQgKyAnXFxuJztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB2YXIgcmVnaXN0ZXJOYW1lO1xuICAgICAgICAgICAgcmVnQXJncyA9IHJlZ0FyZ3Muam9pbignJyk7XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJlZ0FyZ3MubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgICAgICAgICByZWdpc3Rlck5hbWUgPSByZWdBcmdzLmNoYXJBdChpKTtcbiAgICAgICAgICAgICAgICBpZiAoIXZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5pc1ZhbGlkUmVnaXN0ZXIocmVnaXN0ZXJOYW1lKSkge1xuICAgICAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmFyIHJlZ2lzdGVyID0gcmVnaXN0ZXJzW3JlZ2lzdGVyTmFtZV0gfHwgbmV3IFJlZ2lzdGVyKCk7XG4gICAgICAgICAgICAgICAgcmVnSW5mbyArPSAnXCInICsgcmVnaXN0ZXJOYW1lICsgJyAgICAnICsgcmVnaXN0ZXIudG9TdHJpbmcoKSArICdcXG4nO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHNob3dDb25maXJtKGNtLCByZWdJbmZvKTtcbiAgICB9LFxuICAgIHNvcnQ6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7XG4gICAgICAgIHZhciByZXZlcnNlLCBpZ25vcmVDYXNlLCB1bmlxdWUsIG51bWJlciwgcGF0dGVybjtcbiAgICAgICAgZnVuY3Rpb24gcGFyc2VBcmdzKCkge1xuICAgICAgICAgICAgaWYgKHBhcmFtcy5hcmdTdHJpbmcpIHtcbiAgICAgICAgICAgICAgICB2YXIgYXJncyA9IG5ldyBDb2RlTWlycm9yLlN0cmluZ1N0cmVhbShwYXJhbXMuYXJnU3RyaW5nKTtcbiAgICAgICAgICAgICAgICBpZiAoYXJncy5lYXQoJyEnKSkge1xuICAgICAgICAgICAgICAgICAgICByZXZlcnNlID0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKGFyZ3MuZW9sKCkpIHtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoIWFyZ3MuZWF0U3BhY2UoKSkge1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gJ0ludmFsaWQgYXJndW1lbnRzJztcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmFyIG9wdHMgPSBhcmdzLm1hdGNoKC8oW2RpbnVveF0rKT9cXHMqKFxcLy4rXFwvKT9cXHMqLyk7XG4gICAgICAgICAgICAgICAgaWYgKCFvcHRzICYmICFhcmdzLmVvbCgpKSB7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybiAnSW52YWxpZCBhcmd1bWVudHMnO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAob3B0c1sxXSkge1xuICAgICAgICAgICAgICAgICAgICBpZ25vcmVDYXNlID0gb3B0c1sxXS5pbmRleE9mKCdpJykgIT0gLTE7XG4gICAgICAgICAgICAgICAgICAgIHVuaXF1ZSA9IG9wdHNbMV0uaW5kZXhPZigndScpICE9IC0xO1xuICAgICAgICAgICAgICAgICAgICB2YXIgZGVjaW1hbCA9IG9wdHNbMV0uaW5kZXhPZignZCcpICE9IC0xIHx8IG9wdHNbMV0uaW5kZXhPZignbicpICE9IC0xICYmIDE7XG4gICAgICAgICAgICAgICAgICAgIHZhciBoZXggPSBvcHRzWzFdLmluZGV4T2YoJ3gnKSAhPSAtMSAmJiAxO1xuICAgICAgICAgICAgICAgICAgICB2YXIgb2N0YWwgPSBvcHRzWzFdLmluZGV4T2YoJ28nKSAhPSAtMSAmJiAxO1xuICAgICAgICAgICAgICAgICAgICBpZiAoZGVjaW1hbCArIGhleCArIG9jdGFsID4gMSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuICdJbnZhbGlkIGFyZ3VtZW50cyc7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgbnVtYmVyID0gZGVjaW1hbCAmJiAnZGVjaW1hbCcgfHwgaGV4ICYmICdoZXgnIHx8IG9jdGFsICYmICdvY3RhbCc7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChvcHRzWzJdKSB7XG4gICAgICAgICAgICAgICAgICAgIHBhdHRlcm4gPSBuZXcgUmVnRXhwKG9wdHNbMl0uc3Vic3RyKDEsIG9wdHNbMl0ubGVuZ3RoIC0gMiksIGlnbm9yZUNhc2UgPyAnaScgOiAnJyk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHZhciBlcnIgPSBwYXJzZUFyZ3MoKTtcbiAgICAgICAgaWYgKGVycikge1xuICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sIGVyciArICc6ICcgKyBwYXJhbXMuYXJnU3RyaW5nKTtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgbGluZVN0YXJ0ID0gcGFyYW1zLmxpbmUgfHwgY20uZmlyc3RMaW5lKCk7XG4gICAgICAgIHZhciBsaW5lRW5kID0gcGFyYW1zLmxpbmVFbmQgfHwgcGFyYW1zLmxpbmUgfHwgY20ubGFzdExpbmUoKTtcbiAgICAgICAgaWYgKGxpbmVTdGFydCA9PSBsaW5lRW5kKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGN1clN0YXJ0ID0gbmV3IFBvcyhsaW5lU3RhcnQsIDApO1xuICAgICAgICB2YXIgY3VyRW5kID0gbmV3IFBvcyhsaW5lRW5kLCBsaW5lTGVuZ3RoKGNtLCBsaW5lRW5kKSk7XG4gICAgICAgIHZhciB0ZXh0ID0gY20uZ2V0UmFuZ2UoY3VyU3RhcnQsIGN1ckVuZCkuc3BsaXQoJ1xcbicpO1xuICAgICAgICB2YXIgbnVtYmVyUmVnZXggPSBwYXR0ZXJuID8gcGF0dGVybiA6XG4gICAgICAgICAgICAobnVtYmVyID09ICdkZWNpbWFsJykgPyAvKC0/KShbXFxkXSspLyA6XG4gICAgICAgICAgICAgICAgKG51bWJlciA9PSAnaGV4JykgPyAvKC0/KSg/OjB4KT8oWzAtOWEtZl0rKS9pIDpcbiAgICAgICAgICAgICAgICAgICAgKG51bWJlciA9PSAnb2N0YWwnKSA/IC8oWzAtN10rKS8gOiBudWxsO1xuICAgICAgICB2YXIgcmFkaXggPSAobnVtYmVyID09ICdkZWNpbWFsJykgPyAxMCA6IChudW1iZXIgPT0gJ2hleCcpID8gMTYgOiAobnVtYmVyID09ICdvY3RhbCcpID8gOCA6IG51bGw7XG4gICAgICAgIHZhciBudW1QYXJ0ID0gW10sIHRleHRQYXJ0ID0gW107XG4gICAgICAgIGlmIChudW1iZXIgfHwgcGF0dGVybikge1xuICAgICAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCB0ZXh0Lmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgdmFyIG1hdGNoUGFydCA9IHBhdHRlcm4gPyB0ZXh0W2ldLm1hdGNoKHBhdHRlcm4pIDogbnVsbDtcbiAgICAgICAgICAgICAgICBpZiAobWF0Y2hQYXJ0ICYmIG1hdGNoUGFydFswXSAhPSAnJykge1xuICAgICAgICAgICAgICAgICAgICBudW1QYXJ0LnB1c2gobWF0Y2hQYXJ0KTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoIXBhdHRlcm4gJiYgbnVtYmVyUmVnZXguZXhlYyh0ZXh0W2ldKSkge1xuICAgICAgICAgICAgICAgICAgICBudW1QYXJ0LnB1c2godGV4dFtpXSk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICB0ZXh0UGFydC5wdXNoKHRleHRbaV0pO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRleHRQYXJ0ID0gdGV4dDtcbiAgICAgICAgfVxuICAgICAgICBmdW5jdGlvbiBjb21wYXJlRm4oYSwgYikge1xuICAgICAgICAgICAgaWYgKHJldmVyc2UpIHtcbiAgICAgICAgICAgICAgICB2YXIgdG1wO1xuICAgICAgICAgICAgICAgIHRtcCA9IGE7XG4gICAgICAgICAgICAgICAgYSA9IGI7XG4gICAgICAgICAgICAgICAgYiA9IHRtcDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGlmIChpZ25vcmVDYXNlKSB7XG4gICAgICAgICAgICAgICAgYSA9IGEudG9Mb3dlckNhc2UoKTtcbiAgICAgICAgICAgICAgICBiID0gYi50b0xvd2VyQ2FzZSgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgdmFyIGFudW0gPSBudW1iZXIgJiYgbnVtYmVyUmVnZXguZXhlYyhhKTtcbiAgICAgICAgICAgIHZhciBibnVtID0gbnVtYmVyICYmIG51bWJlclJlZ2V4LmV4ZWMoYik7XG4gICAgICAgICAgICBpZiAoIWFudW0pIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gYSA8IGIgPyAtMSA6IDE7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBhbnVtID0gcGFyc2VJbnQoKGFudW1bMV0gKyBhbnVtWzJdKS50b0xvd2VyQ2FzZSgpLCByYWRpeCk7XG4gICAgICAgICAgICBibnVtID0gcGFyc2VJbnQoKGJudW1bMV0gKyBibnVtWzJdKS50b0xvd2VyQ2FzZSgpLCByYWRpeCk7XG4gICAgICAgICAgICByZXR1cm4gYW51bSAtIGJudW07XG4gICAgICAgIH1cbiAgICAgICAgZnVuY3Rpb24gY29tcGFyZVBhdHRlcm5GbihhLCBiKSB7XG4gICAgICAgICAgICBpZiAocmV2ZXJzZSkge1xuICAgICAgICAgICAgICAgIHZhciB0bXA7XG4gICAgICAgICAgICAgICAgdG1wID0gYTtcbiAgICAgICAgICAgICAgICBhID0gYjtcbiAgICAgICAgICAgICAgICBiID0gdG1wO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGlnbm9yZUNhc2UpIHtcbiAgICAgICAgICAgICAgICBhWzBdID0gYVswXS50b0xvd2VyQ2FzZSgpO1xuICAgICAgICAgICAgICAgIGJbMF0gPSBiWzBdLnRvTG93ZXJDYXNlKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gKGFbMF0gPCBiWzBdKSA/IC0xIDogMTtcbiAgICAgICAgfVxuICAgICAgICBudW1QYXJ0LnNvcnQocGF0dGVybiA/IGNvbXBhcmVQYXR0ZXJuRm4gOiBjb21wYXJlRm4pO1xuICAgICAgICBpZiAocGF0dGVybikge1xuICAgICAgICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBudW1QYXJ0Lmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICAgICAgbnVtUGFydFtpXSA9IG51bVBhcnRbaV0uaW5wdXQ7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoIW51bWJlcikge1xuICAgICAgICAgICAgdGV4dFBhcnQuc29ydChjb21wYXJlRm4pO1xuICAgICAgICB9XG4gICAgICAgIHRleHQgPSAoIXJldmVyc2UpID8gdGV4dFBhcnQuY29uY2F0KG51bVBhcnQpIDogbnVtUGFydC5jb25jYXQodGV4dFBhcnQpO1xuICAgICAgICBpZiAodW5pcXVlKSB7IC8vIFJlbW92ZSBkdXBsaWNhdGUgbGluZXNcbiAgICAgICAgICAgIHZhciB0ZXh0T2xkID0gdGV4dDtcbiAgICAgICAgICAgIHZhciBsYXN0TGluZTtcbiAgICAgICAgICAgIHRleHQgPSBbXTtcbiAgICAgICAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgdGV4dE9sZC5sZW5ndGg7IGkrKykge1xuICAgICAgICAgICAgICAgIGlmICh0ZXh0T2xkW2ldICE9IGxhc3RMaW5lKSB7XG4gICAgICAgICAgICAgICAgICAgIHRleHQucHVzaCh0ZXh0T2xkW2ldKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgbGFzdExpbmUgPSB0ZXh0T2xkW2ldO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGNtLnJlcGxhY2VSYW5nZSh0ZXh0LmpvaW4oJ1xcbicpLCBjdXJTdGFydCwgY3VyRW5kKTtcbiAgICB9LFxuICAgIHZnbG9iYWw6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7XG4gICAgICAgIHRoaXMuZ2xvYmFsKGNtLCBwYXJhbXMpO1xuICAgIH0sXG4gICAgbm9ybWFsOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICB2YXIgYXJnU3RyaW5nID0gcGFyYW1zLmFyZ1N0cmluZztcbiAgICAgICAgaWYgKGFyZ1N0cmluZyAmJiBhcmdTdHJpbmdbMF0gPT0gJyEnKSB7XG4gICAgICAgICAgICBhcmdTdHJpbmcgPSBhcmdTdHJpbmcuc2xpY2UoMSk7XG4gICAgICAgICAgICBub3JlbWFwID0gdHJ1ZTtcbiAgICAgICAgfVxuICAgICAgICBhcmdTdHJpbmcgPSBhcmdTdHJpbmcudHJpbVN0YXJ0KCk7XG4gICAgICAgIGlmICghYXJnU3RyaW5nKSB7XG4gICAgICAgICAgICBzaG93Q29uZmlybShjbSwgJ0FyZ3VtZW50IGlzIHJlcXVpcmVkLicpO1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIHZhciBsaW5lID0gcGFyYW1zLmxpbmU7XG4gICAgICAgIGlmICh0eXBlb2YgbGluZSA9PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgdmFyIGxpbmVFbmQgPSBpc05hTihwYXJhbXMubGluZUVuZCkgPyBsaW5lIDogcGFyYW1zLmxpbmVFbmQ7XG4gICAgICAgICAgICBmb3IgKHZhciBpID0gbGluZTsgaSA8PSBsaW5lRW5kOyBpKyspIHtcbiAgICAgICAgICAgICAgICBjbS5zZXRDdXJzb3IoaSwgMCk7XG4gICAgICAgICAgICAgICAgZG9LZXlUb0tleShjbSwgcGFyYW1zLmFyZ1N0cmluZy50cmltU3RhcnQoKSk7XG4gICAgICAgICAgICAgICAgaWYgKGNtLnN0YXRlLnZpbS5pbnNlcnRNb2RlKSB7XG4gICAgICAgICAgICAgICAgICAgIGV4aXRJbnNlcnRNb2RlKGNtLCB0cnVlKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBkb0tleVRvS2V5KGNtLCBwYXJhbXMuYXJnU3RyaW5nLnRyaW1TdGFydCgpKTtcbiAgICAgICAgICAgIGlmIChjbS5zdGF0ZS52aW0uaW5zZXJ0TW9kZSkge1xuICAgICAgICAgICAgICAgIGV4aXRJbnNlcnRNb2RlKGNtLCB0cnVlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sXG4gICAgZ2xvYmFsOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICB2YXIgYXJnU3RyaW5nID0gcGFyYW1zLmFyZ1N0cmluZztcbiAgICAgICAgaWYgKCFhcmdTdHJpbmcpIHtcbiAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnUmVndWxhciBFeHByZXNzaW9uIG1pc3NpbmcgZnJvbSBnbG9iYWwnKTtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgaW52ZXJ0ZWQgPSBwYXJhbXMuY29tbWFuZE5hbWVbMF0gPT09ICd2JztcbiAgICAgICAgaWYgKGFyZ1N0cmluZ1swXSA9PT0gJyEnICYmIHBhcmFtcy5jb21tYW5kTmFtZVswXSA9PT0gJ2cnKSB7XG4gICAgICAgICAgICBpbnZlcnRlZCA9IHRydWU7XG4gICAgICAgICAgICBhcmdTdHJpbmcgPSBhcmdTdHJpbmcuc2xpY2UoMSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGxpbmVTdGFydCA9IChwYXJhbXMubGluZSAhPT0gdW5kZWZpbmVkKSA/IHBhcmFtcy5saW5lIDogY20uZmlyc3RMaW5lKCk7XG4gICAgICAgIHZhciBsaW5lRW5kID0gcGFyYW1zLmxpbmVFbmQgfHwgcGFyYW1zLmxpbmUgfHwgY20ubGFzdExpbmUoKTtcbiAgICAgICAgdmFyIHRva2VucyA9IHNwbGl0QnlTbGFzaChhcmdTdHJpbmcpO1xuICAgICAgICB2YXIgcmVnZXhQYXJ0ID0gYXJnU3RyaW5nLCBjbWQ7XG4gICAgICAgIGlmICh0b2tlbnMubGVuZ3RoKSB7XG4gICAgICAgICAgICByZWdleFBhcnQgPSB0b2tlbnNbMF07XG4gICAgICAgICAgICBjbWQgPSB0b2tlbnMuc2xpY2UoMSwgdG9rZW5zLmxlbmd0aCkuam9pbignLycpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChyZWdleFBhcnQpIHtcbiAgICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICAgICAgdXBkYXRlU2VhcmNoUXVlcnkoY20sIHJlZ2V4UGFydCwgdHJ1ZSAvKiogaWdub3JlQ2FzZSAqLywgdHJ1ZSAvKiogc21hcnRDYXNlICovKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNhdGNoIChlKSB7XG4gICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdJbnZhbGlkIHJlZ2V4OiAnICsgcmVnZXhQYXJ0KTtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgdmFyIHF1ZXJ5ID0gZ2V0U2VhcmNoU3RhdGUoY20pLmdldFF1ZXJ5KCk7XG4gICAgICAgIHZhciBtYXRjaGVkTGluZXMgPSBbXTtcbiAgICAgICAgZm9yICh2YXIgaSA9IGxpbmVTdGFydDsgaSA8PSBsaW5lRW5kOyBpKyspIHtcbiAgICAgICAgICAgIHZhciBsaW5lID0gY20uZ2V0TGluZShpKTtcbiAgICAgICAgICAgIHZhciBtYXRjaGVkID0gcXVlcnkudGVzdChsaW5lKTtcbiAgICAgICAgICAgIGlmIChtYXRjaGVkICE9PSBpbnZlcnRlZCkge1xuICAgICAgICAgICAgICAgIG1hdGNoZWRMaW5lcy5wdXNoKGNtZCA/IGNtLmdldExpbmVIYW5kbGUoaSkgOiBsaW5lKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAoIWNtZCkge1xuICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sIG1hdGNoZWRMaW5lcy5qb2luKCdcXG4nKSk7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGluZGV4ID0gMDtcbiAgICAgICAgdmFyIG5leHRDb21tYW5kID0gZnVuY3Rpb24gKCkge1xuICAgICAgICAgICAgaWYgKGluZGV4IDwgbWF0Y2hlZExpbmVzLmxlbmd0aCkge1xuICAgICAgICAgICAgICAgIHZhciBsaW5lSGFuZGxlID0gbWF0Y2hlZExpbmVzW2luZGV4KytdO1xuICAgICAgICAgICAgICAgIHZhciBsaW5lTnVtID0gY20uZ2V0TGluZU51bWJlcihsaW5lSGFuZGxlKTtcbiAgICAgICAgICAgICAgICBpZiAobGluZU51bSA9PSBudWxsKSB7XG4gICAgICAgICAgICAgICAgICAgIG5leHRDb21tYW5kKCk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmFyIGNvbW1hbmQgPSAobGluZU51bSArIDEpICsgY21kO1xuICAgICAgICAgICAgICAgIGV4Q29tbWFuZERpc3BhdGNoZXIucHJvY2Vzc0NvbW1hbmQoY20sIGNvbW1hbmQsIHtcbiAgICAgICAgICAgICAgICAgICAgY2FsbGJhY2s6IG5leHRDb21tYW5kXG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmIChjbS5yZWxlYXNlTGluZUhhbmRsZXMpIHtcbiAgICAgICAgICAgICAgICBjbS5yZWxlYXNlTGluZUhhbmRsZXMoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICAgICAgbmV4dENvbW1hbmQoKTtcbiAgICB9LFxuICAgIHN1YnN0aXR1dGU6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7XG4gICAgICAgIGlmICghY20uZ2V0U2VhcmNoQ3Vyc29yKSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ1NlYXJjaCBmZWF0dXJlIG5vdCBhdmFpbGFibGUuIFJlcXVpcmVzIHNlYXJjaGN1cnNvci5qcyBvciAnICtcbiAgICAgICAgICAgICAgICAnYW55IG90aGVyIGdldFNlYXJjaEN1cnNvciBpbXBsZW1lbnRhdGlvbi4nKTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgYXJnU3RyaW5nID0gcGFyYW1zLmFyZ1N0cmluZztcbiAgICAgICAgdmFyIHRva2VucyA9IGFyZ1N0cmluZyA/IHNwbGl0QnlTZXBhcmF0b3IoYXJnU3RyaW5nLCBhcmdTdHJpbmdbMF0pIDogW107XG4gICAgICAgIHZhciByZWdleFBhcnQsIHJlcGxhY2VQYXJ0ID0gJycsIHRyYWlsaW5nLCBmbGFnc1BhcnQsIGNvdW50O1xuICAgICAgICB2YXIgY29uZmlybSA9IGZhbHNlOyAvLyBXaGV0aGVyIHRvIGNvbmZpcm0gZWFjaCByZXBsYWNlLlxuICAgICAgICB2YXIgZ2xvYmFsID0gZmFsc2U7IC8vIFRydWUgdG8gcmVwbGFjZSBhbGwgaW5zdGFuY2VzIG9uIGEgbGluZSwgZmFsc2UgdG8gcmVwbGFjZSBvbmx5IDEuXG4gICAgICAgIGlmICh0b2tlbnMubGVuZ3RoKSB7XG4gICAgICAgICAgICByZWdleFBhcnQgPSB0b2tlbnNbMF07XG4gICAgICAgICAgICBpZiAoZ2V0T3B0aW9uKCdwY3JlJykgJiYgcmVnZXhQYXJ0ICE9PSAnJykge1xuICAgICAgICAgICAgICAgIHJlZ2V4UGFydCA9IG5ldyBSZWdFeHAocmVnZXhQYXJ0KS5zb3VyY2U7IC8vbm9ybWFsaXplIG5vdCBlc2NhcGVkIGNoYXJhY3RlcnNcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJlcGxhY2VQYXJ0ID0gdG9rZW5zWzFdO1xuICAgICAgICAgICAgaWYgKHJlcGxhY2VQYXJ0ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgICAgICAgICBpZiAoZ2V0T3B0aW9uKCdwY3JlJykpIHtcbiAgICAgICAgICAgICAgICAgICAgcmVwbGFjZVBhcnQgPSB1bmVzY2FwZVJlZ2V4UmVwbGFjZShyZXBsYWNlUGFydC5yZXBsYWNlKC8oW15cXFxcXSkmL2csIFwiJDEkJCZcIikpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgcmVwbGFjZVBhcnQgPSB0cmFuc2xhdGVSZWdleFJlcGxhY2UocmVwbGFjZVBhcnQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB2aW1HbG9iYWxTdGF0ZS5sYXN0U3Vic3RpdHV0ZVJlcGxhY2VQYXJ0ID0gcmVwbGFjZVBhcnQ7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB0cmFpbGluZyA9IHRva2Vuc1syXSA/IHRva2Vuc1syXS5zcGxpdCgnICcpIDogW107XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBpZiAoYXJnU3RyaW5nICYmIGFyZ1N0cmluZy5sZW5ndGgpIHtcbiAgICAgICAgICAgICAgICBzaG93Q29uZmlybShjbSwgJ1N1YnN0aXR1dGlvbnMgc2hvdWxkIGJlIG9mIHRoZSBmb3JtICcgK1xuICAgICAgICAgICAgICAgICAgICAnOnMvcGF0dGVybi9yZXBsYWNlLycpO1xuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBpZiAodHJhaWxpbmcpIHtcbiAgICAgICAgICAgIGZsYWdzUGFydCA9IHRyYWlsaW5nWzBdO1xuICAgICAgICAgICAgY291bnQgPSBwYXJzZUludCh0cmFpbGluZ1sxXSk7XG4gICAgICAgICAgICBpZiAoZmxhZ3NQYXJ0KSB7XG4gICAgICAgICAgICAgICAgaWYgKGZsYWdzUGFydC5pbmRleE9mKCdjJykgIT0gLTEpIHtcbiAgICAgICAgICAgICAgICAgICAgY29uZmlybSA9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChmbGFnc1BhcnQuaW5kZXhPZignZycpICE9IC0xKSB7XG4gICAgICAgICAgICAgICAgICAgIGdsb2JhbCA9IHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChnZXRPcHRpb24oJ3BjcmUnKSkge1xuICAgICAgICAgICAgICAgICAgICByZWdleFBhcnQgPSByZWdleFBhcnQgKyAnLycgKyBmbGFnc1BhcnQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICByZWdleFBhcnQgPSByZWdleFBhcnQucmVwbGFjZSgvXFwvL2csIFwiXFxcXC9cIikgKyAnLycgKyBmbGFnc1BhcnQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChyZWdleFBhcnQpIHtcbiAgICAgICAgICAgIHRyeSB7XG4gICAgICAgICAgICAgICAgdXBkYXRlU2VhcmNoUXVlcnkoY20sIHJlZ2V4UGFydCwgdHJ1ZSAvKiogaWdub3JlQ2FzZSAqLywgdHJ1ZSAvKiogc21hcnRDYXNlICovKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNhdGNoIChlKSB7XG4gICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdJbnZhbGlkIHJlZ2V4OiAnICsgcmVnZXhQYXJ0KTtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgcmVwbGFjZVBhcnQgPSByZXBsYWNlUGFydCB8fCB2aW1HbG9iYWxTdGF0ZS5sYXN0U3Vic3RpdHV0ZVJlcGxhY2VQYXJ0O1xuICAgICAgICBpZiAocmVwbGFjZVBhcnQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdObyBwcmV2aW91cyBzdWJzdGl0dXRlIHJlZ3VsYXIgZXhwcmVzc2lvbicpO1xuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICB9XG4gICAgICAgIHZhciBzdGF0ZSA9IGdldFNlYXJjaFN0YXRlKGNtKTtcbiAgICAgICAgdmFyIHF1ZXJ5ID0gc3RhdGUuZ2V0UXVlcnkoKTtcbiAgICAgICAgdmFyIGxpbmVTdGFydCA9IChwYXJhbXMubGluZSAhPT0gdW5kZWZpbmVkKSA/IHBhcmFtcy5saW5lIDogY20uZ2V0Q3Vyc29yKCkubGluZTtcbiAgICAgICAgdmFyIGxpbmVFbmQgPSBwYXJhbXMubGluZUVuZCB8fCBsaW5lU3RhcnQ7XG4gICAgICAgIGlmIChsaW5lU3RhcnQgPT0gY20uZmlyc3RMaW5lKCkgJiYgbGluZUVuZCA9PSBjbS5sYXN0TGluZSgpKSB7XG4gICAgICAgICAgICBsaW5lRW5kID0gSW5maW5pdHk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGNvdW50KSB7XG4gICAgICAgICAgICBsaW5lU3RhcnQgPSBsaW5lRW5kO1xuICAgICAgICAgICAgbGluZUVuZCA9IGxpbmVTdGFydCArIGNvdW50IC0gMTtcbiAgICAgICAgfVxuICAgICAgICB2YXIgc3RhcnRQb3MgPSBjbGlwQ3Vyc29yVG9Db250ZW50KGNtLCBuZXcgUG9zKGxpbmVTdGFydCwgMCkpO1xuICAgICAgICB2YXIgY3Vyc29yID0gY20uZ2V0U2VhcmNoQ3Vyc29yKHF1ZXJ5LCBzdGFydFBvcyk7XG4gICAgICAgIGRvUmVwbGFjZShjbSwgY29uZmlybSwgZ2xvYmFsLCBsaW5lU3RhcnQsIGxpbmVFbmQsIGN1cnNvciwgcXVlcnksIHJlcGxhY2VQYXJ0LCBwYXJhbXMuY2FsbGJhY2spO1xuICAgIH0sXG4gICAgc3RhcnRpbnNlcnQ6IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7XG4gICAgICAgIGRvS2V5VG9LZXkoY20sIHBhcmFtcy5hcmdTdHJpbmcgPT0gJyEnID8gJ0EnIDogJ2knLCB7fSk7XG4gICAgfSxcbiAgICByZWRvOiBDb2RlTWlycm9yLmNvbW1hbmRzLnJlZG8sXG4gICAgdW5kbzogQ29kZU1pcnJvci5jb21tYW5kcy51bmRvLFxuICAgIHdyaXRlOiBmdW5jdGlvbiAoY20pIHtcbiAgICAgICAgaWYgKENvZGVNaXJyb3IuY29tbWFuZHMuc2F2ZSkge1xuICAgICAgICAgICAgQ29kZU1pcnJvci5jb21tYW5kcy5zYXZlKGNtKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChjbS5zYXZlKSB7XG4gICAgICAgICAgICBjbS5zYXZlKCk7XG4gICAgICAgIH1cbiAgICB9LFxuICAgIG5vaGxzZWFyY2g6IGZ1bmN0aW9uIChjbSkge1xuICAgICAgICBjbGVhclNlYXJjaEhpZ2hsaWdodChjbSk7XG4gICAgfSxcbiAgICB5YW5rOiBmdW5jdGlvbiAoY20pIHtcbiAgICAgICAgdmFyIGN1ciA9IGNvcHlDdXJzb3IoY20uZ2V0Q3Vyc29yKCkpO1xuICAgICAgICB2YXIgbGluZSA9IGN1ci5saW5lO1xuICAgICAgICB2YXIgbGluZVRleHQgPSBjbS5nZXRMaW5lKGxpbmUpO1xuICAgICAgICB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIucHVzaFRleHQoJzAnLCAneWFuaycsIGxpbmVUZXh0LCB0cnVlLCB0cnVlKTtcbiAgICB9LFxuICAgIGRlbGV0ZTogZnVuY3Rpb24gKGNtLCBwYXJhbXMpIHtcbiAgICAgICAgdmFyIGxpbmUgPSBwYXJhbXMuc2VsZWN0aW9uTGluZTtcbiAgICAgICAgdmFyIGxpbmVFbmQgPSBpc05hTihwYXJhbXMuc2VsZWN0aW9uTGluZUVuZCkgPyBsaW5lIDogcGFyYW1zLnNlbGVjdGlvbkxpbmVFbmQ7XG4gICAgICAgIG9wZXJhdG9ycy5kZWxldGUoY20sIHsgbGluZXdpc2U6IHRydWUgfSwgW1xuICAgICAgICAgICAgeyBhbmNob3I6IG5ldyBQb3MobGluZSwgMCksXG4gICAgICAgICAgICAgICAgaGVhZDogbmV3IFBvcyhsaW5lRW5kICsgMSwgMCkgfVxuICAgICAgICBdKTtcbiAgICB9LFxuICAgIGpvaW46IGZ1bmN0aW9uIChjbSwgcGFyYW1zKSB7XG4gICAgICAgIHZhciBsaW5lID0gcGFyYW1zLnNlbGVjdGlvbkxpbmU7XG4gICAgICAgIHZhciBsaW5lRW5kID0gaXNOYU4ocGFyYW1zLnNlbGVjdGlvbkxpbmVFbmQpID8gbGluZSA6IHBhcmFtcy5zZWxlY3Rpb25MaW5lRW5kO1xuICAgICAgICBjbS5zZXRDdXJzb3IobmV3IFBvcyhsaW5lLCAwKSk7XG4gICAgICAgIGFjdGlvbnMuam9pbkxpbmVzKGNtLCB7IHJlcGVhdDogbGluZUVuZCAtIGxpbmUgfSwgY20uc3RhdGUudmltKTtcbiAgICB9LFxuICAgIGRlbG1hcmtzOiBmdW5jdGlvbiAoY20sIHBhcmFtcykge1xuICAgICAgICBpZiAoIXBhcmFtcy5hcmdTdHJpbmcgfHwgIXRyaW0ocGFyYW1zLmFyZ1N0cmluZykpIHtcbiAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnQXJndW1lbnQgcmVxdWlyZWQnKTtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICB2YXIgc3RhdGUgPSBjbS5zdGF0ZS52aW07XG4gICAgICAgIHZhciBzdHJlYW0gPSBuZXcgQ29kZU1pcnJvci5TdHJpbmdTdHJlYW0odHJpbShwYXJhbXMuYXJnU3RyaW5nKSk7XG4gICAgICAgIHdoaWxlICghc3RyZWFtLmVvbCgpKSB7XG4gICAgICAgICAgICBzdHJlYW0uZWF0U3BhY2UoKTtcbiAgICAgICAgICAgIHZhciBjb3VudCA9IHN0cmVhbS5wb3M7XG4gICAgICAgICAgICBpZiAoIXN0cmVhbS5tYXRjaCgvW2EtekEtWl0vLCBmYWxzZSkpIHtcbiAgICAgICAgICAgICAgICBzaG93Q29uZmlybShjbSwgJ0ludmFsaWQgYXJndW1lbnQ6ICcgKyBwYXJhbXMuYXJnU3RyaW5nLnN1YnN0cmluZyhjb3VudCkpO1xuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHZhciBzeW0gPSBzdHJlYW0ubmV4dCgpO1xuICAgICAgICAgICAgaWYgKHN0cmVhbS5tYXRjaCgnLScsIHRydWUpKSB7XG4gICAgICAgICAgICAgICAgaWYgKCFzdHJlYW0ubWF0Y2goL1thLXpBLVpdLywgZmFsc2UpKSB7XG4gICAgICAgICAgICAgICAgICAgIHNob3dDb25maXJtKGNtLCAnSW52YWxpZCBhcmd1bWVudDogJyArIHBhcmFtcy5hcmdTdHJpbmcuc3Vic3RyaW5nKGNvdW50KSk7XG4gICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdmFyIHN0YXJ0TWFyayA9IHN5bTtcbiAgICAgICAgICAgICAgICB2YXIgZmluaXNoTWFyayA9IHN0cmVhbS5uZXh0KCk7XG4gICAgICAgICAgICAgICAgaWYgKGlzTG93ZXJDYXNlKHN0YXJ0TWFyaykgJiYgaXNMb3dlckNhc2UoZmluaXNoTWFyaykgfHxcbiAgICAgICAgICAgICAgICAgICAgaXNVcHBlckNhc2Uoc3RhcnRNYXJrKSAmJiBpc1VwcGVyQ2FzZShmaW5pc2hNYXJrKSkge1xuICAgICAgICAgICAgICAgICAgICB2YXIgc3RhcnQgPSBzdGFydE1hcmsuY2hhckNvZGVBdCgwKTtcbiAgICAgICAgICAgICAgICAgICAgdmFyIGZpbmlzaCA9IGZpbmlzaE1hcmsuY2hhckNvZGVBdCgwKTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKHN0YXJ0ID49IGZpbmlzaCkge1xuICAgICAgICAgICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdJbnZhbGlkIGFyZ3VtZW50OiAnICsgcGFyYW1zLmFyZ1N0cmluZy5zdWJzdHJpbmcoY291bnQpKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBmb3IgKHZhciBqID0gMDsgaiA8PSBmaW5pc2ggLSBzdGFydDsgaisrKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICB2YXIgbWFyayA9IFN0cmluZy5mcm9tQ2hhckNvZGUoc3RhcnQgKyBqKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGRlbGV0ZSBzdGF0ZS5tYXJrc1ttYXJrXTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgc2hvd0NvbmZpcm0oY20sICdJbnZhbGlkIGFyZ3VtZW50OiAnICsgc3RhcnRNYXJrICsgJy0nKTtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGRlbGV0ZSBzdGF0ZS5tYXJrc1tzeW1dO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxufTtcbnZhciBleENvbW1hbmREaXNwYXRjaGVyID0gbmV3IEV4Q29tbWFuZERpc3BhdGNoZXIoKTtcbmZ1bmN0aW9uIGRvUmVwbGFjZShjbSwgY29uZmlybSwgZ2xvYmFsLCBsaW5lU3RhcnQsIGxpbmVFbmQsIHNlYXJjaEN1cnNvciwgcXVlcnksIHJlcGxhY2VXaXRoLCBjYWxsYmFjaykge1xuICAgIGNtLnN0YXRlLnZpbS5leE1vZGUgPSB0cnVlO1xuICAgIHZhciBkb25lID0gZmFsc2U7XG4gICAgdmFyIGxhc3RQb3MsIG1vZGlmaWVkTGluZU51bWJlciwgam9pbmVkO1xuICAgIGZ1bmN0aW9uIHJlcGxhY2VBbGwoKSB7XG4gICAgICAgIGNtLm9wZXJhdGlvbihmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICB3aGlsZSAoIWRvbmUpIHtcbiAgICAgICAgICAgICAgICByZXBsYWNlKCk7XG4gICAgICAgICAgICAgICAgbmV4dCgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgc3RvcCgpO1xuICAgICAgICB9KTtcbiAgICB9XG4gICAgZnVuY3Rpb24gcmVwbGFjZSgpIHtcbiAgICAgICAgdmFyIHRleHQgPSBjbS5nZXRSYW5nZShzZWFyY2hDdXJzb3IuZnJvbSgpLCBzZWFyY2hDdXJzb3IudG8oKSk7XG4gICAgICAgIHZhciBuZXdUZXh0ID0gdGV4dC5yZXBsYWNlKHF1ZXJ5LCByZXBsYWNlV2l0aCk7XG4gICAgICAgIHZhciB1bm1vZGlmaWVkTGluZU51bWJlciA9IHNlYXJjaEN1cnNvci50bygpLmxpbmU7XG4gICAgICAgIHNlYXJjaEN1cnNvci5yZXBsYWNlKG5ld1RleHQpO1xuICAgICAgICBtb2RpZmllZExpbmVOdW1iZXIgPSBzZWFyY2hDdXJzb3IudG8oKS5saW5lO1xuICAgICAgICBsaW5lRW5kICs9IG1vZGlmaWVkTGluZU51bWJlciAtIHVubW9kaWZpZWRMaW5lTnVtYmVyO1xuICAgICAgICBqb2luZWQgPSBtb2RpZmllZExpbmVOdW1iZXIgPCB1bm1vZGlmaWVkTGluZU51bWJlcjtcbiAgICB9XG4gICAgZnVuY3Rpb24gZmluZE5leHRWYWxpZE1hdGNoKCkge1xuICAgICAgICB2YXIgbGFzdE1hdGNoVG8gPSBsYXN0UG9zICYmIGNvcHlDdXJzb3Ioc2VhcmNoQ3Vyc29yLnRvKCkpO1xuICAgICAgICB2YXIgbWF0Y2ggPSBzZWFyY2hDdXJzb3IuZmluZE5leHQoKTtcbiAgICAgICAgaWYgKG1hdGNoICYmICFtYXRjaFswXSAmJiBsYXN0TWF0Y2hUbyAmJiBjdXJzb3JFcXVhbChzZWFyY2hDdXJzb3IuZnJvbSgpLCBsYXN0TWF0Y2hUbykpIHtcbiAgICAgICAgICAgIG1hdGNoID0gc2VhcmNoQ3Vyc29yLmZpbmROZXh0KCk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG1hdGNoO1xuICAgIH1cbiAgICBmdW5jdGlvbiBuZXh0KCkge1xuICAgICAgICB3aGlsZSAoZmluZE5leHRWYWxpZE1hdGNoKCkgJiZcbiAgICAgICAgICAgIGlzSW5SYW5nZShzZWFyY2hDdXJzb3IuZnJvbSgpLCBsaW5lU3RhcnQsIGxpbmVFbmQpKSB7XG4gICAgICAgICAgICBpZiAoIWdsb2JhbCAmJiBzZWFyY2hDdXJzb3IuZnJvbSgpLmxpbmUgPT0gbW9kaWZpZWRMaW5lTnVtYmVyICYmICFqb2luZWQpIHtcbiAgICAgICAgICAgICAgICBjb250aW51ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNtLnNjcm9sbEludG9WaWV3KHNlYXJjaEN1cnNvci5mcm9tKCksIDMwKTtcbiAgICAgICAgICAgIGNtLnNldFNlbGVjdGlvbihzZWFyY2hDdXJzb3IuZnJvbSgpLCBzZWFyY2hDdXJzb3IudG8oKSk7XG4gICAgICAgICAgICBsYXN0UG9zID0gc2VhcmNoQ3Vyc29yLmZyb20oKTtcbiAgICAgICAgICAgIGRvbmUgPSBmYWxzZTtcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgfVxuICAgICAgICBkb25lID0gdHJ1ZTtcbiAgICB9XG4gICAgZnVuY3Rpb24gc3RvcChjbG9zZSkge1xuICAgICAgICBpZiAoY2xvc2UpIHtcbiAgICAgICAgICAgIGNsb3NlKCk7XG4gICAgICAgIH1cbiAgICAgICAgY20uZm9jdXMoKTtcbiAgICAgICAgaWYgKGxhc3RQb3MpIHtcbiAgICAgICAgICAgIGNtLnNldEN1cnNvcihsYXN0UG9zKTtcbiAgICAgICAgICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgICAgICAgICB2aW0uZXhNb2RlID0gZmFsc2U7XG4gICAgICAgICAgICB2aW0ubGFzdEhQb3MgPSB2aW0ubGFzdEhTUG9zID0gbGFzdFBvcy5jaDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoY2FsbGJhY2spIHtcbiAgICAgICAgICAgIGNhbGxiYWNrKCk7XG4gICAgICAgIH1cbiAgICB9XG4gICAgZnVuY3Rpb24gb25Qcm9tcHRLZXlEb3duKGUsIF92YWx1ZSwgY2xvc2UpIHtcbiAgICAgICAgQ29kZU1pcnJvci5lX3N0b3AoZSk7XG4gICAgICAgIHZhciBrZXlOYW1lID0gdmltS2V5RnJvbUV2ZW50KGUpO1xuICAgICAgICBzd2l0Y2ggKGtleU5hbWUpIHtcbiAgICAgICAgICAgIGNhc2UgJ3knOlxuICAgICAgICAgICAgICAgIHJlcGxhY2UoKTtcbiAgICAgICAgICAgICAgICBuZXh0KCk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICduJzpcbiAgICAgICAgICAgICAgICBuZXh0KCk7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdhJzpcbiAgICAgICAgICAgICAgICB2YXIgc2F2ZWRDYWxsYmFjayA9IGNhbGxiYWNrO1xuICAgICAgICAgICAgICAgIGNhbGxiYWNrID0gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgIGNtLm9wZXJhdGlvbihyZXBsYWNlQWxsKTtcbiAgICAgICAgICAgICAgICBjYWxsYmFjayA9IHNhdmVkQ2FsbGJhY2s7XG4gICAgICAgICAgICAgICAgYnJlYWs7XG4gICAgICAgICAgICBjYXNlICdsJzpcbiAgICAgICAgICAgICAgICByZXBsYWNlKCk7XG4gICAgICAgICAgICBjYXNlICdxJzpcbiAgICAgICAgICAgIGNhc2UgJzxFc2M+JzpcbiAgICAgICAgICAgIGNhc2UgJzxDLWM+JzpcbiAgICAgICAgICAgIGNhc2UgJzxDLVs+JzpcbiAgICAgICAgICAgICAgICBzdG9wKGNsb3NlKTtcbiAgICAgICAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuICAgICAgICBpZiAoZG9uZSkge1xuICAgICAgICAgICAgc3RvcChjbG9zZSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIG5leHQoKTtcbiAgICBpZiAoZG9uZSkge1xuICAgICAgICBzaG93Q29uZmlybShjbSwgJ05vIG1hdGNoZXMgZm9yICcgKyBxdWVyeS5zb3VyY2UpO1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIGlmICghY29uZmlybSkge1xuICAgICAgICByZXBsYWNlQWxsKCk7XG4gICAgICAgIGlmIChjYWxsYmFjaykge1xuICAgICAgICAgICAgY2FsbGJhY2soKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHNob3dQcm9tcHQoY20sIHtcbiAgICAgICAgcHJlZml4OiBkb20oJ3NwYW4nLCAncmVwbGFjZSB3aXRoICcsIGRvbSgnc3Ryb25nJywgcmVwbGFjZVdpdGgpLCAnICh5L24vYS9xL2wpJyksXG4gICAgICAgIG9uS2V5RG93bjogb25Qcm9tcHRLZXlEb3duXG4gICAgfSk7XG59XG5mdW5jdGlvbiBleGl0SW5zZXJ0TW9kZShjbSwga2VlcEN1cnNvcikge1xuICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgdmFyIG1hY3JvTW9kZVN0YXRlID0gdmltR2xvYmFsU3RhdGUubWFjcm9Nb2RlU3RhdGU7XG4gICAgdmFyIGluc2VydE1vZGVDaGFuZ2VSZWdpc3RlciA9IHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5nZXRSZWdpc3RlcignLicpO1xuICAgIHZhciBpc1BsYXlpbmcgPSBtYWNyb01vZGVTdGF0ZS5pc1BsYXlpbmc7XG4gICAgdmFyIGxhc3RDaGFuZ2UgPSBtYWNyb01vZGVTdGF0ZS5sYXN0SW5zZXJ0TW9kZUNoYW5nZXM7XG4gICAgaWYgKCFpc1BsYXlpbmcpIHtcbiAgICAgICAgY20ub2ZmKCdjaGFuZ2UnLCBvbkNoYW5nZSk7XG4gICAgICAgIGlmICh2aW0uaW5zZXJ0RW5kKVxuICAgICAgICAgICAgdmltLmluc2VydEVuZC5jbGVhcigpO1xuICAgICAgICB2aW0uaW5zZXJ0RW5kID0gbnVsbDtcbiAgICAgICAgQ29kZU1pcnJvci5vZmYoY20uZ2V0SW5wdXRGaWVsZCgpLCAna2V5ZG93bicsIG9uS2V5RXZlbnRUYXJnZXRLZXlEb3duKTtcbiAgICB9XG4gICAgaWYgKCFpc1BsYXlpbmcgJiYgdmltLmluc2VydE1vZGVSZXBlYXQgPiAxKSB7XG4gICAgICAgIHJlcGVhdExhc3RFZGl0KGNtLCB2aW0sIHZpbS5pbnNlcnRNb2RlUmVwZWF0IC0gMSwgdHJ1ZSAvKiogcmVwZWF0Rm9ySW5zZXJ0ICovKTtcbiAgICAgICAgdmltLmxhc3RFZGl0SW5wdXRTdGF0ZS5yZXBlYXRPdmVycmlkZSA9IHZpbS5pbnNlcnRNb2RlUmVwZWF0O1xuICAgIH1cbiAgICBkZWxldGUgdmltLmluc2VydE1vZGVSZXBlYXQ7XG4gICAgdmltLmluc2VydE1vZGUgPSBmYWxzZTtcbiAgICBpZiAoIWtlZXBDdXJzb3IpIHtcbiAgICAgICAgY20uc2V0Q3Vyc29yKGNtLmdldEN1cnNvcigpLmxpbmUsIGNtLmdldEN1cnNvcigpLmNoIC0gMSk7XG4gICAgfVxuICAgIGNtLnNldE9wdGlvbigna2V5TWFwJywgJ3ZpbScpO1xuICAgIGNtLnNldE9wdGlvbignZGlzYWJsZUlucHV0JywgdHJ1ZSk7XG4gICAgY20udG9nZ2xlT3ZlcndyaXRlKGZhbHNlKTsgLy8gZXhpdCByZXBsYWNlIG1vZGUgaWYgd2Ugd2VyZSBpbiBpdC5cbiAgICBpbnNlcnRNb2RlQ2hhbmdlUmVnaXN0ZXIuc2V0VGV4dChsYXN0Q2hhbmdlLmNoYW5nZXMuam9pbignJykpO1xuICAgIENvZGVNaXJyb3Iuc2lnbmFsKGNtLCBcInZpbS1tb2RlLWNoYW5nZVwiLCB7IG1vZGU6IFwibm9ybWFsXCIgfSk7XG4gICAgaWYgKG1hY3JvTW9kZVN0YXRlLmlzUmVjb3JkaW5nKSB7XG4gICAgICAgIGxvZ0luc2VydE1vZGVDaGFuZ2UobWFjcm9Nb2RlU3RhdGUpO1xuICAgIH1cbn1cbmZ1bmN0aW9uIF9tYXBDb21tYW5kKGNvbW1hbmQpIHtcbiAgICBkZWZhdWx0S2V5bWFwLnVuc2hpZnQoY29tbWFuZCk7XG59XG5mdW5jdGlvbiBtYXBDb21tYW5kKGtleXMsIHR5cGUsIG5hbWUsIGFyZ3MsIGV4dHJhKSB7XG4gICAgdmFyIGNvbW1hbmQgPSB7IGtleXM6IGtleXMsIHR5cGU6IHR5cGUgfTtcbiAgICBjb21tYW5kW3R5cGVdID0gbmFtZTtcbiAgICBjb21tYW5kW3R5cGUgKyBcIkFyZ3NcIl0gPSBhcmdzO1xuICAgIGZvciAodmFyIGtleSBpbiBleHRyYSlcbiAgICAgICAgY29tbWFuZFtrZXldID0gZXh0cmFba2V5XTtcbiAgICBfbWFwQ29tbWFuZChjb21tYW5kKTtcbn1cbmRlZmluZU9wdGlvbignaW5zZXJ0TW9kZUVzY0tleXNUaW1lb3V0JywgMjAwLCAnbnVtYmVyJyk7XG5mdW5jdGlvbiBleGVjdXRlTWFjcm9SZWdpc3RlcihjbSwgdmltLCBtYWNyb01vZGVTdGF0ZSwgcmVnaXN0ZXJOYW1lKSB7XG4gICAgdmFyIHJlZ2lzdGVyID0gdmltR2xvYmFsU3RhdGUucmVnaXN0ZXJDb250cm9sbGVyLmdldFJlZ2lzdGVyKHJlZ2lzdGVyTmFtZSk7XG4gICAgaWYgKHJlZ2lzdGVyTmFtZSA9PSAnOicpIHtcbiAgICAgICAgaWYgKHJlZ2lzdGVyLmtleUJ1ZmZlclswXSkge1xuICAgICAgICAgICAgZXhDb21tYW5kRGlzcGF0Y2hlci5wcm9jZXNzQ29tbWFuZChjbSwgcmVnaXN0ZXIua2V5QnVmZmVyWzBdKTtcbiAgICAgICAgfVxuICAgICAgICBtYWNyb01vZGVTdGF0ZS5pc1BsYXlpbmcgPSBmYWxzZTtcbiAgICAgICAgcmV0dXJuO1xuICAgIH1cbiAgICB2YXIga2V5QnVmZmVyID0gcmVnaXN0ZXIua2V5QnVmZmVyO1xuICAgIHZhciBpbWMgPSAwO1xuICAgIG1hY3JvTW9kZVN0YXRlLmlzUGxheWluZyA9IHRydWU7XG4gICAgbWFjcm9Nb2RlU3RhdGUucmVwbGF5U2VhcmNoUXVlcmllcyA9IHJlZ2lzdGVyLnNlYXJjaFF1ZXJpZXMuc2xpY2UoMCk7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBrZXlCdWZmZXIubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIHRleHQgPSBrZXlCdWZmZXJbaV07XG4gICAgICAgIHZhciBtYXRjaCwga2V5O1xuICAgICAgICB3aGlsZSAodGV4dCkge1xuICAgICAgICAgICAgbWF0Y2ggPSAoLzxcXHcrLS4rPz58PFxcdys+fC4vKS5leGVjKHRleHQpO1xuICAgICAgICAgICAga2V5ID0gbWF0Y2hbMF07XG4gICAgICAgICAgICB0ZXh0ID0gdGV4dC5zdWJzdHJpbmcobWF0Y2guaW5kZXggKyBrZXkubGVuZ3RoKTtcbiAgICAgICAgICAgIHZpbUFwaS5oYW5kbGVLZXkoY20sIGtleSwgJ21hY3JvJyk7XG4gICAgICAgICAgICBpZiAodmltLmluc2VydE1vZGUpIHtcbiAgICAgICAgICAgICAgICB2YXIgY2hhbmdlcyA9IHJlZ2lzdGVyLmluc2VydE1vZGVDaGFuZ2VzW2ltYysrXS5jaGFuZ2VzO1xuICAgICAgICAgICAgICAgIHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcy5jaGFuZ2VzID1cbiAgICAgICAgICAgICAgICAgICAgY2hhbmdlcztcbiAgICAgICAgICAgICAgICByZXBlYXRJbnNlcnRNb2RlQ2hhbmdlcyhjbSwgY2hhbmdlcywgMSk7XG4gICAgICAgICAgICAgICAgZXhpdEluc2VydE1vZGUoY20pO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuICAgIG1hY3JvTW9kZVN0YXRlLmlzUGxheWluZyA9IGZhbHNlO1xufVxuZnVuY3Rpb24gbG9nS2V5KG1hY3JvTW9kZVN0YXRlLCBrZXkpIHtcbiAgICBpZiAobWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdmFyIHJlZ2lzdGVyTmFtZSA9IG1hY3JvTW9kZVN0YXRlLmxhdGVzdFJlZ2lzdGVyO1xuICAgIHZhciByZWdpc3RlciA9IHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5nZXRSZWdpc3RlcihyZWdpc3Rlck5hbWUpO1xuICAgIGlmIChyZWdpc3Rlcikge1xuICAgICAgICByZWdpc3Rlci5wdXNoVGV4dChrZXkpO1xuICAgIH1cbn1cbmZ1bmN0aW9uIGxvZ0luc2VydE1vZGVDaGFuZ2UobWFjcm9Nb2RlU3RhdGUpIHtcbiAgICBpZiAobWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgdmFyIHJlZ2lzdGVyTmFtZSA9IG1hY3JvTW9kZVN0YXRlLmxhdGVzdFJlZ2lzdGVyO1xuICAgIHZhciByZWdpc3RlciA9IHZpbUdsb2JhbFN0YXRlLnJlZ2lzdGVyQ29udHJvbGxlci5nZXRSZWdpc3RlcihyZWdpc3Rlck5hbWUpO1xuICAgIGlmIChyZWdpc3RlciAmJiByZWdpc3Rlci5wdXNoSW5zZXJ0TW9kZUNoYW5nZXMpIHtcbiAgICAgICAgcmVnaXN0ZXIucHVzaEluc2VydE1vZGVDaGFuZ2VzKG1hY3JvTW9kZVN0YXRlLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcyk7XG4gICAgfVxufVxuZnVuY3Rpb24gbG9nU2VhcmNoUXVlcnkobWFjcm9Nb2RlU3RhdGUsIHF1ZXJ5KSB7XG4gICAgaWYgKG1hY3JvTW9kZVN0YXRlLmlzUGxheWluZykge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHZhciByZWdpc3Rlck5hbWUgPSBtYWNyb01vZGVTdGF0ZS5sYXRlc3RSZWdpc3RlcjtcbiAgICB2YXIgcmVnaXN0ZXIgPSB2aW1HbG9iYWxTdGF0ZS5yZWdpc3RlckNvbnRyb2xsZXIuZ2V0UmVnaXN0ZXIocmVnaXN0ZXJOYW1lKTtcbiAgICBpZiAocmVnaXN0ZXIgJiYgcmVnaXN0ZXIucHVzaFNlYXJjaFF1ZXJ5KSB7XG4gICAgICAgIHJlZ2lzdGVyLnB1c2hTZWFyY2hRdWVyeShxdWVyeSk7XG4gICAgfVxufVxuZnVuY3Rpb24gb25DaGFuZ2UoY20sIGNoYW5nZU9iaikge1xuICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgIHZhciBsYXN0Q2hhbmdlID0gbWFjcm9Nb2RlU3RhdGUubGFzdEluc2VydE1vZGVDaGFuZ2VzO1xuICAgIGlmICghbWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgICAgIHdoaWxlIChjaGFuZ2VPYmopIHtcbiAgICAgICAgICAgIGxhc3RDaGFuZ2UuZXhwZWN0Q3Vyc29yQWN0aXZpdHlGb3JDaGFuZ2UgPSB0cnVlO1xuICAgICAgICAgICAgaWYgKGxhc3RDaGFuZ2UuaWdub3JlQ291bnQgPiAxKSB7XG4gICAgICAgICAgICAgICAgbGFzdENoYW5nZS5pZ25vcmVDb3VudC0tO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY2hhbmdlT2JqLm9yaWdpbiA9PSAnK2lucHV0JyB8fCBjaGFuZ2VPYmoub3JpZ2luID09ICdwYXN0ZSdcbiAgICAgICAgICAgICAgICB8fCBjaGFuZ2VPYmoub3JpZ2luID09PSB1bmRlZmluZWQgLyogb25seSBpbiB0ZXN0aW5nICovKSB7XG4gICAgICAgICAgICAgICAgdmFyIHNlbGVjdGlvbkNvdW50ID0gY20ubGlzdFNlbGVjdGlvbnMoKS5sZW5ndGg7XG4gICAgICAgICAgICAgICAgaWYgKHNlbGVjdGlvbkNvdW50ID4gMSlcbiAgICAgICAgICAgICAgICAgICAgbGFzdENoYW5nZS5pZ25vcmVDb3VudCA9IHNlbGVjdGlvbkNvdW50O1xuICAgICAgICAgICAgICAgIHZhciB0ZXh0ID0gY2hhbmdlT2JqLnRleHQuam9pbignXFxuJyk7XG4gICAgICAgICAgICAgICAgaWYgKGxhc3RDaGFuZ2UubWF5YmVSZXNldCkge1xuICAgICAgICAgICAgICAgICAgICBsYXN0Q2hhbmdlLmNoYW5nZXMgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgbGFzdENoYW5nZS5tYXliZVJlc2V0ID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmICh0ZXh0KSB7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjbS5zdGF0ZS5vdmVyd3JpdGUgJiYgIS9cXG4vLnRlc3QodGV4dCkpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGxhc3RDaGFuZ2UuY2hhbmdlcy5wdXNoKFt0ZXh0XSk7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAodGV4dC5sZW5ndGggPiAxKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFyIGluc2VydEVuZCA9IHZpbSAmJiB2aW0uaW5zZXJ0RW5kICYmIHZpbS5pbnNlcnRFbmQuZmluZCgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHZhciBjdXJzb3IgPSBjbS5nZXRDdXJzb3IoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoaW5zZXJ0RW5kICYmIGluc2VydEVuZC5saW5lID09IGN1cnNvci5saW5lKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHZhciBvZmZzZXQgPSBpbnNlcnRFbmQuY2ggLSBjdXJzb3IuY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChvZmZzZXQgPiAwICYmIG9mZnNldCA8IHRleHQubGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBsYXN0Q2hhbmdlLmNoYW5nZXMucHVzaChbdGV4dCwgb2Zmc2V0XSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB0ZXh0ID0gJyc7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAodGV4dClcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBsYXN0Q2hhbmdlLmNoYW5nZXMucHVzaCh0ZXh0KTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNoYW5nZU9iaiA9IGNoYW5nZU9iai5uZXh0O1xuICAgICAgICB9XG4gICAgfVxufVxuZnVuY3Rpb24gb25DdXJzb3JBY3Rpdml0eShjbSkge1xuICAgIHZhciB2aW0gPSBjbS5zdGF0ZS52aW07XG4gICAgaWYgKHZpbS5pbnNlcnRNb2RlKSB7XG4gICAgICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgICAgICBpZiAobWFjcm9Nb2RlU3RhdGUuaXNQbGF5aW5nKSB7XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGxhc3RDaGFuZ2UgPSBtYWNyb01vZGVTdGF0ZS5sYXN0SW5zZXJ0TW9kZUNoYW5nZXM7XG4gICAgICAgIGlmIChsYXN0Q2hhbmdlLmV4cGVjdEN1cnNvckFjdGl2aXR5Rm9yQ2hhbmdlKSB7XG4gICAgICAgICAgICBsYXN0Q2hhbmdlLmV4cGVjdEN1cnNvckFjdGl2aXR5Rm9yQ2hhbmdlID0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBsYXN0Q2hhbmdlLm1heWJlUmVzZXQgPSB0cnVlO1xuICAgICAgICAgICAgaWYgKHZpbS5pbnNlcnRFbmQpXG4gICAgICAgICAgICAgICAgdmltLmluc2VydEVuZC5jbGVhcigpO1xuICAgICAgICAgICAgdmltLmluc2VydEVuZCA9IGNtLnNldEJvb2ttYXJrKGNtLmdldEN1cnNvcigpLCB7IGluc2VydExlZnQ6IHRydWUgfSk7XG4gICAgICAgIH1cbiAgICB9XG4gICAgZWxzZSBpZiAoIWNtLmN1ck9wLmlzVmltT3ApIHtcbiAgICAgICAgaGFuZGxlRXh0ZXJuYWxTZWxlY3Rpb24oY20sIHZpbSk7XG4gICAgfVxufVxuZnVuY3Rpb24gaGFuZGxlRXh0ZXJuYWxTZWxlY3Rpb24oY20sIHZpbSwga2VlcEhQb3MpIHtcbiAgICB2YXIgYW5jaG9yID0gY20uZ2V0Q3Vyc29yKCdhbmNob3InKTtcbiAgICB2YXIgaGVhZCA9IGNtLmdldEN1cnNvcignaGVhZCcpO1xuICAgIGlmICh2aW0udmlzdWFsTW9kZSAmJiAhY20uc29tZXRoaW5nU2VsZWN0ZWQoKSkge1xuICAgICAgICBleGl0VmlzdWFsTW9kZShjbSwgZmFsc2UpO1xuICAgIH1cbiAgICBlbHNlIGlmICghdmltLnZpc3VhbE1vZGUgJiYgIXZpbS5pbnNlcnRNb2RlICYmIGNtLnNvbWV0aGluZ1NlbGVjdGVkKCkpIHtcbiAgICAgICAgdmltLnZpc3VhbE1vZGUgPSB0cnVlO1xuICAgICAgICB2aW0udmlzdWFsTGluZSA9IGZhbHNlO1xuICAgICAgICBDb2RlTWlycm9yLnNpZ25hbChjbSwgXCJ2aW0tbW9kZS1jaGFuZ2VcIiwgeyBtb2RlOiBcInZpc3VhbFwiIH0pO1xuICAgIH1cbiAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgdmFyIGhlYWRPZmZzZXQgPSAhY3Vyc29ySXNCZWZvcmUoaGVhZCwgYW5jaG9yKSA/IC0xIDogMDtcbiAgICAgICAgdmFyIGFuY2hvck9mZnNldCA9IGN1cnNvcklzQmVmb3JlKGhlYWQsIGFuY2hvcikgPyAtMSA6IDA7XG4gICAgICAgIGhlYWQgPSBvZmZzZXRDdXJzb3IoaGVhZCwgMCwgaGVhZE9mZnNldCk7XG4gICAgICAgIGFuY2hvciA9IG9mZnNldEN1cnNvcihhbmNob3IsIDAsIGFuY2hvck9mZnNldCk7XG4gICAgICAgIHZpbS5zZWwgPSB7XG4gICAgICAgICAgICBhbmNob3I6IGFuY2hvcixcbiAgICAgICAgICAgIGhlYWQ6IGhlYWRcbiAgICAgICAgfTtcbiAgICAgICAgdXBkYXRlTWFyayhjbSwgdmltLCAnPCcsIGN1cnNvck1pbihoZWFkLCBhbmNob3IpKTtcbiAgICAgICAgdXBkYXRlTWFyayhjbSwgdmltLCAnPicsIGN1cnNvck1heChoZWFkLCBhbmNob3IpKTtcbiAgICB9XG4gICAgZWxzZSBpZiAoIXZpbS5pbnNlcnRNb2RlICYmICFrZWVwSFBvcykge1xuICAgICAgICB2aW0ubGFzdEhQb3MgPSBjbS5nZXRDdXJzb3IoKS5jaDtcbiAgICB9XG59XG5mdW5jdGlvbiBJbnNlcnRNb2RlS2V5KGtleU5hbWUsIGUpIHtcbiAgICB0aGlzLmtleU5hbWUgPSBrZXlOYW1lO1xuICAgIHRoaXMua2V5ID0gZS5rZXk7XG4gICAgdGhpcy5jdHJsS2V5ID0gZS5jdHJsS2V5O1xuICAgIHRoaXMuYWx0S2V5ID0gZS5hbHRLZXk7XG4gICAgdGhpcy5tZXRhS2V5ID0gZS5tZXRhS2V5O1xuICAgIHRoaXMuc2hpZnRLZXkgPSBlLnNoaWZ0S2V5O1xufVxuZnVuY3Rpb24gb25LZXlFdmVudFRhcmdldEtleURvd24oZSkge1xuICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgIHZhciBsYXN0Q2hhbmdlID0gbWFjcm9Nb2RlU3RhdGUubGFzdEluc2VydE1vZGVDaGFuZ2VzO1xuICAgIHZhciBrZXlOYW1lID0gQ29kZU1pcnJvci5rZXlOYW1lID8gQ29kZU1pcnJvci5rZXlOYW1lKGUpIDogZS5rZXk7XG4gICAgaWYgKCFrZXlOYW1lKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgaWYgKGtleU5hbWUuaW5kZXhPZignRGVsZXRlJykgIT0gLTEgfHwga2V5TmFtZS5pbmRleE9mKCdCYWNrc3BhY2UnKSAhPSAtMSkge1xuICAgICAgICBpZiAobGFzdENoYW5nZS5tYXliZVJlc2V0KSB7XG4gICAgICAgICAgICBsYXN0Q2hhbmdlLmNoYW5nZXMgPSBbXTtcbiAgICAgICAgICAgIGxhc3RDaGFuZ2UubWF5YmVSZXNldCA9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIGxhc3RDaGFuZ2UuY2hhbmdlcy5wdXNoKG5ldyBJbnNlcnRNb2RlS2V5KGtleU5hbWUsIGUpKTtcbiAgICB9XG59XG5mdW5jdGlvbiByZXBlYXRMYXN0RWRpdChjbSwgdmltLCByZXBlYXQsIHJlcGVhdEZvckluc2VydCkge1xuICAgIHZhciBtYWNyb01vZGVTdGF0ZSA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlO1xuICAgIG1hY3JvTW9kZVN0YXRlLmlzUGxheWluZyA9IHRydWU7XG4gICAgdmFyIGlzQWN0aW9uID0gISF2aW0ubGFzdEVkaXRBY3Rpb25Db21tYW5kO1xuICAgIHZhciBjYWNoZWRJbnB1dFN0YXRlID0gdmltLmlucHV0U3RhdGU7XG4gICAgZnVuY3Rpb24gcmVwZWF0Q29tbWFuZCgpIHtcbiAgICAgICAgaWYgKGlzQWN0aW9uKSB7XG4gICAgICAgICAgICBjb21tYW5kRGlzcGF0Y2hlci5wcm9jZXNzQWN0aW9uKGNtLCB2aW0sIHZpbS5sYXN0RWRpdEFjdGlvbkNvbW1hbmQpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgY29tbWFuZERpc3BhdGNoZXIuZXZhbElucHV0KGNtLCB2aW0pO1xuICAgICAgICB9XG4gICAgfVxuICAgIGZ1bmN0aW9uIHJlcGVhdEluc2VydChyZXBlYXQpIHtcbiAgICAgICAgaWYgKG1hY3JvTW9kZVN0YXRlLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcy5jaGFuZ2VzLmxlbmd0aCA+IDApIHtcbiAgICAgICAgICAgIHJlcGVhdCA9ICF2aW0ubGFzdEVkaXRBY3Rpb25Db21tYW5kID8gMSA6IHJlcGVhdDtcbiAgICAgICAgICAgIHZhciBjaGFuZ2VPYmplY3QgPSBtYWNyb01vZGVTdGF0ZS5sYXN0SW5zZXJ0TW9kZUNoYW5nZXM7XG4gICAgICAgICAgICByZXBlYXRJbnNlcnRNb2RlQ2hhbmdlcyhjbSwgY2hhbmdlT2JqZWN0LmNoYW5nZXMsIHJlcGVhdCk7XG4gICAgICAgIH1cbiAgICB9XG4gICAgdmltLmlucHV0U3RhdGUgPSB2aW0ubGFzdEVkaXRJbnB1dFN0YXRlO1xuICAgIGlmIChpc0FjdGlvbiAmJiB2aW0ubGFzdEVkaXRBY3Rpb25Db21tYW5kLmludGVybGFjZUluc2VydFJlcGVhdCkge1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJlcGVhdDsgaSsrKSB7XG4gICAgICAgICAgICByZXBlYXRDb21tYW5kKCk7XG4gICAgICAgICAgICByZXBlYXRJbnNlcnQoMSk7XG4gICAgICAgIH1cbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIGlmICghcmVwZWF0Rm9ySW5zZXJ0KSB7XG4gICAgICAgICAgICByZXBlYXRDb21tYW5kKCk7XG4gICAgICAgIH1cbiAgICAgICAgcmVwZWF0SW5zZXJ0KHJlcGVhdCk7XG4gICAgfVxuICAgIHZpbS5pbnB1dFN0YXRlID0gY2FjaGVkSW5wdXRTdGF0ZTtcbiAgICBpZiAodmltLmluc2VydE1vZGUgJiYgIXJlcGVhdEZvckluc2VydCkge1xuICAgICAgICBleGl0SW5zZXJ0TW9kZShjbSk7XG4gICAgfVxuICAgIG1hY3JvTW9kZVN0YXRlLmlzUGxheWluZyA9IGZhbHNlO1xufVxuZnVuY3Rpb24gc2VuZENtS2V5KGNtLCBrZXkpIHtcbiAgICBDb2RlTWlycm9yLmxvb2t1cEtleShrZXksICd2aW0taW5zZXJ0JywgZnVuY3Rpb24ga2V5SGFuZGxlcihiaW5kaW5nKSB7XG4gICAgICAgIGlmICh0eXBlb2YgYmluZGluZyA9PSAnc3RyaW5nJykge1xuICAgICAgICAgICAgQ29kZU1pcnJvci5jb21tYW5kc1tiaW5kaW5nXShjbSk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBiaW5kaW5nKGNtKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9KTtcbn1cbmZ1bmN0aW9uIHJlcGVhdEluc2VydE1vZGVDaGFuZ2VzKGNtLCBjaGFuZ2VzLCByZXBlYXQpIHtcbiAgICB2YXIgaGVhZCA9IGNtLmdldEN1cnNvcignaGVhZCcpO1xuICAgIHZhciB2aXN1YWxCbG9jayA9IHZpbUdsb2JhbFN0YXRlLm1hY3JvTW9kZVN0YXRlLmxhc3RJbnNlcnRNb2RlQ2hhbmdlcy52aXN1YWxCbG9jaztcbiAgICBpZiAodmlzdWFsQmxvY2spIHtcbiAgICAgICAgc2VsZWN0Rm9ySW5zZXJ0KGNtLCBoZWFkLCB2aXN1YWxCbG9jayArIDEpO1xuICAgICAgICByZXBlYXQgPSBjbS5saXN0U2VsZWN0aW9ucygpLmxlbmd0aDtcbiAgICAgICAgY20uc2V0Q3Vyc29yKGhlYWQpO1xuICAgIH1cbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IHJlcGVhdDsgaSsrKSB7XG4gICAgICAgIGlmICh2aXN1YWxCbG9jaykge1xuICAgICAgICAgICAgY20uc2V0Q3Vyc29yKG9mZnNldEN1cnNvcihoZWFkLCBpLCAwKSk7XG4gICAgICAgIH1cbiAgICAgICAgZm9yICh2YXIgaiA9IDA7IGogPCBjaGFuZ2VzLmxlbmd0aDsgaisrKSB7XG4gICAgICAgICAgICB2YXIgY2hhbmdlID0gY2hhbmdlc1tqXTtcbiAgICAgICAgICAgIGlmIChjaGFuZ2UgaW5zdGFuY2VvZiBJbnNlcnRNb2RlS2V5KSB7XG4gICAgICAgICAgICAgICAgc2VuZENtS2V5KGNtLCBjaGFuZ2Uua2V5TmFtZSwgY2hhbmdlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjaGFuZ2UgPT0gXCJzdHJpbmdcIikge1xuICAgICAgICAgICAgICAgIGNtLnJlcGxhY2VTZWxlY3Rpb24oY2hhbmdlKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHZhciBzdGFydCA9IGNtLmdldEN1cnNvcigpO1xuICAgICAgICAgICAgICAgIHZhciBlbmQgPSBvZmZzZXRDdXJzb3Ioc3RhcnQsIDAsIGNoYW5nZVswXS5sZW5ndGggLSAoY2hhbmdlWzFdIHx8IDApKTtcbiAgICAgICAgICAgICAgICBjbS5yZXBsYWNlUmFuZ2UoY2hhbmdlWzBdLCBzdGFydCwgY2hhbmdlWzFdID8gc3RhcnQgOiBlbmQpO1xuICAgICAgICAgICAgICAgIGNtLnNldEN1cnNvcihlbmQpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgfVxuICAgIGlmICh2aXN1YWxCbG9jaykge1xuICAgICAgICBjbS5zZXRDdXJzb3Iob2Zmc2V0Q3Vyc29yKGhlYWQsIDAsIDEpKTtcbiAgICB9XG59XG5Db2RlTWlycm9yLlZpbSA9IHZpbUFwaTtcbnZhciBzcGVjaWFsS2V5QWNlID0geyAncmV0dXJuJzogJ0NSJywgYmFja3NwYWNlOiAnQlMnLCAnZGVsZXRlJzogJ0RlbCcsIGVzYzogJ0VzYycsXG4gICAgbGVmdDogJ0xlZnQnLCByaWdodDogJ1JpZ2h0JywgdXA6ICdVcCcsIGRvd246ICdEb3duJywgc3BhY2U6ICdTcGFjZScsIGluc2VydDogJ0lucycsXG4gICAgaG9tZTogJ0hvbWUnLCBlbmQ6ICdFbmQnLCBwYWdldXA6ICdQYWdlVXAnLCBwYWdlZG93bjogJ1BhZ2VEb3duJywgZW50ZXI6ICdDUidcbn07XG5mdW5jdGlvbiBsb29rdXBLZXkoaGFzaElkLCBrZXksIGUsIHZpbSkge1xuICAgIGlmIChrZXkubGVuZ3RoID4gMSAmJiBrZXlbMF0gPT0gXCJuXCIpIHtcbiAgICAgICAga2V5ID0ga2V5LnJlcGxhY2UoXCJudW1wYWRcIiwgXCJcIik7XG4gICAgfVxuICAgIGtleSA9IHNwZWNpYWxLZXlBY2Vba2V5XSB8fCBrZXk7XG4gICAgdmFyIG5hbWUgPSAnJztcbiAgICBpZiAoZS5jdHJsS2V5KSB7XG4gICAgICAgIG5hbWUgKz0gJ0MtJztcbiAgICB9XG4gICAgaWYgKGUuYWx0S2V5KSB7XG4gICAgICAgIG5hbWUgKz0gJ0EtJztcbiAgICB9XG4gICAgaWYgKChuYW1lIHx8IGtleS5sZW5ndGggPiAxKSAmJiBlLnNoaWZ0S2V5KSB7XG4gICAgICAgIG5hbWUgKz0gJ1MtJztcbiAgICB9XG4gICAgaWYgKHZpbSAmJiAhdmltLmV4cGVjdExpdGVyYWxOZXh0ICYmIGtleS5sZW5ndGggPT0gMSkge1xuICAgICAgICBpZiAobGFuZ21hcC5rZXltYXAgJiYga2V5IGluIGxhbmdtYXAua2V5bWFwKSB7XG4gICAgICAgICAgICBpZiAobGFuZ21hcC5yZW1hcEN0cmwgIT09IGZhbHNlIHx8ICFuYW1lKVxuICAgICAgICAgICAgICAgIGtleSA9IGxhbmdtYXAua2V5bWFwW2tleV07XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoa2V5LmNoYXJDb2RlQXQoMCkgPiAyNTUpIHtcbiAgICAgICAgICAgIHZhciBjb2RlID0gZS5jb2RlICYmIGUuY29kZS5zbGljZSgtMSkgfHwgXCJcIjtcbiAgICAgICAgICAgIGlmICghZS5zaGlmdEtleSlcbiAgICAgICAgICAgICAgICBjb2RlID0gY29kZS50b0xvd2VyQ2FzZSgpO1xuICAgICAgICAgICAgaWYgKGNvZGUpXG4gICAgICAgICAgICAgICAga2V5ID0gY29kZTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBuYW1lICs9IGtleTtcbiAgICBpZiAobmFtZS5sZW5ndGggPiAxKSB7XG4gICAgICAgIG5hbWUgPSAnPCcgKyBuYW1lICsgJz4nO1xuICAgIH1cbiAgICByZXR1cm4gbmFtZTtcbn1cbnZhciBoYW5kbGVLZXkgPSB2aW1BcGkuaGFuZGxlS2V5LmJpbmQodmltQXBpKTtcbnZpbUFwaS5oYW5kbGVLZXkgPSBmdW5jdGlvbiAoY20sIGtleSwgb3JpZ2luKSB7XG4gICAgcmV0dXJuIGNtLm9wZXJhdGlvbihmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiBoYW5kbGVLZXkoY20sIGtleSwgb3JpZ2luKTtcbiAgICB9LCB0cnVlKTtcbn07XG5mdW5jdGlvbiBjbG9uZVZpbVN0YXRlKHN0YXRlKSB7XG4gICAgdmFyIG4gPSBuZXcgc3RhdGUuY29uc3RydWN0b3IoKTtcbiAgICBPYmplY3Qua2V5cyhzdGF0ZSkuZm9yRWFjaChmdW5jdGlvbiAoa2V5KSB7XG4gICAgICAgIGlmIChrZXkgPT0gXCJpbnNlcnRFbmRcIilcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgdmFyIG8gPSBzdGF0ZVtrZXldO1xuICAgICAgICBpZiAoQXJyYXkuaXNBcnJheShvKSlcbiAgICAgICAgICAgIG8gPSBvLnNsaWNlKCk7XG4gICAgICAgIGVsc2UgaWYgKG8gJiYgdHlwZW9mIG8gPT0gXCJvYmplY3RcIiAmJiBvLmNvbnN0cnVjdG9yICE9IE9iamVjdClcbiAgICAgICAgICAgIG8gPSBjbG9uZVZpbVN0YXRlKG8pO1xuICAgICAgICBuW2tleV0gPSBvO1xuICAgIH0pO1xuICAgIGlmIChzdGF0ZS5zZWwpIHtcbiAgICAgICAgbi5zZWwgPSB7XG4gICAgICAgICAgICBoZWFkOiBzdGF0ZS5zZWwuaGVhZCAmJiBjb3B5Q3Vyc29yKHN0YXRlLnNlbC5oZWFkKSxcbiAgICAgICAgICAgIGFuY2hvcjogc3RhdGUuc2VsLmFuY2hvciAmJiBjb3B5Q3Vyc29yKHN0YXRlLnNlbC5hbmNob3IpXG4gICAgICAgIH07XG4gICAgfVxuICAgIHJldHVybiBuO1xufVxuZnVuY3Rpb24gbXVsdGlTZWxlY3RIYW5kbGVLZXkoY20sIGtleSwgb3JpZ2luKSB7XG4gICAgdmFyIGlzSGFuZGxlZCA9IGZhbHNlO1xuICAgIHZhciB2aW0gPSB2aW1BcGkubWF5YmVJbml0VmltU3RhdGVfKGNtKTtcbiAgICB2YXIgdmlzdWFsQmxvY2sgPSB2aW0udmlzdWFsQmxvY2sgfHwgdmltLndhc0luVmlzdWFsQmxvY2s7XG4gICAgdmFyIHdhc011bHRpc2VsZWN0ID0gY20uYWNlLmluTXVsdGlTZWxlY3RNb2RlO1xuICAgIGlmICh2aW0ud2FzSW5WaXN1YWxCbG9jayAmJiAhd2FzTXVsdGlzZWxlY3QpIHtcbiAgICAgICAgdmltLndhc0luVmlzdWFsQmxvY2sgPSBmYWxzZTtcbiAgICB9XG4gICAgZWxzZSBpZiAod2FzTXVsdGlzZWxlY3QgJiYgdmltLnZpc3VhbEJsb2NrKSB7XG4gICAgICAgIHZpbS53YXNJblZpc3VhbEJsb2NrID0gdHJ1ZTtcbiAgICB9XG4gICAgaWYgKGtleSA9PSAnPEVzYz4nICYmICF2aW0uaW5zZXJ0TW9kZSAmJiAhdmltLnZpc3VhbE1vZGUgJiYgd2FzTXVsdGlzZWxlY3QpIHtcbiAgICAgICAgY20uYWNlLmV4aXRNdWx0aVNlbGVjdE1vZGUoKTtcbiAgICB9XG4gICAgZWxzZSBpZiAodmlzdWFsQmxvY2sgfHwgIXdhc011bHRpc2VsZWN0IHx8IGNtLmFjZS5pblZpcnR1YWxTZWxlY3Rpb25Nb2RlKSB7XG4gICAgICAgIGlzSGFuZGxlZCA9IHZpbUFwaS5oYW5kbGVLZXkoY20sIGtleSwgb3JpZ2luKTtcbiAgICB9XG4gICAgZWxzZSB7XG4gICAgICAgIHZhciBvbGQgPSBjbG9uZVZpbVN0YXRlKHZpbSk7XG4gICAgICAgIHZhciBjaGFuZ2VRdWV1ZUxpc3QgPSB2aW0uaW5wdXRTdGF0ZS5jaGFuZ2VRdWV1ZUxpc3QgfHwgW107XG4gICAgICAgIGNtLm9wZXJhdGlvbihmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICBjbS5jdXJPcC5pc1ZpbU9wID0gdHJ1ZTtcbiAgICAgICAgICAgIHZhciBpbmRleCA9IDA7XG4gICAgICAgICAgICBjbS5hY2UuZm9yRWFjaFNlbGVjdGlvbihmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICAgICAgdmFyIHNlbCA9IGNtLmFjZS5zZWxlY3Rpb247XG4gICAgICAgICAgICAgICAgY20uc3RhdGUudmltLmxhc3RIUG9zID0gc2VsLiRkZXNpcmVkQ29sdW1uID09IG51bGwgPyBzZWwubGVhZC5jb2x1bW4gOiBzZWwuJGRlc2lyZWRDb2x1bW47XG4gICAgICAgICAgICAgICAgY20uc3RhdGUudmltLmlucHV0U3RhdGUuY2hhbmdlUXVldWUgPSBjaGFuZ2VRdWV1ZUxpc3RbaW5kZXhdO1xuICAgICAgICAgICAgICAgIHZhciBoZWFkID0gY20uZ2V0Q3Vyc29yKFwiaGVhZFwiKTtcbiAgICAgICAgICAgICAgICB2YXIgYW5jaG9yID0gY20uZ2V0Q3Vyc29yKFwiYW5jaG9yXCIpO1xuICAgICAgICAgICAgICAgIHZhciBoZWFkT2Zmc2V0ID0gIWN1cnNvcklzQmVmb3JlKGhlYWQsIGFuY2hvcikgPyAtMSA6IDA7XG4gICAgICAgICAgICAgICAgdmFyIGFuY2hvck9mZnNldCA9IGN1cnNvcklzQmVmb3JlKGhlYWQsIGFuY2hvcikgPyAtMSA6IDA7XG4gICAgICAgICAgICAgICAgaGVhZCA9IG9mZnNldEN1cnNvcihoZWFkLCAwLCBoZWFkT2Zmc2V0KTtcbiAgICAgICAgICAgICAgICBhbmNob3IgPSBvZmZzZXRDdXJzb3IoYW5jaG9yLCAwLCBhbmNob3JPZmZzZXQpO1xuICAgICAgICAgICAgICAgIGNtLnN0YXRlLnZpbS5zZWwuaGVhZCA9IGhlYWQ7XG4gICAgICAgICAgICAgICAgY20uc3RhdGUudmltLnNlbC5hbmNob3IgPSBhbmNob3I7XG4gICAgICAgICAgICAgICAgaXNIYW5kbGVkID0gaGFuZGxlS2V5KGNtLCBrZXksIG9yaWdpbik7XG4gICAgICAgICAgICAgICAgc2VsLiRkZXNpcmVkQ29sdW1uID0gY20uc3RhdGUudmltLmxhc3RIUG9zID09IC0xID8gbnVsbCA6IGNtLnN0YXRlLnZpbS5sYXN0SFBvcztcbiAgICAgICAgICAgICAgICBpZiAoY20uYWNlLmluVmlydHVhbFNlbGVjdGlvbk1vZGUpIHtcbiAgICAgICAgICAgICAgICAgICAgY2hhbmdlUXVldWVMaXN0W2luZGV4XSA9IGNtLnN0YXRlLnZpbS5pbnB1dFN0YXRlLmNoYW5nZVF1ZXVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoY20udmlydHVhbFNlbGVjdGlvbk1vZGUoKSkge1xuICAgICAgICAgICAgICAgICAgICBjbS5zdGF0ZS52aW0gPSBjbG9uZVZpbVN0YXRlKG9sZCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGluZGV4Kys7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIGlmIChjbS5jdXJPcC5jdXJzb3JBY3Rpdml0eSAmJiAhaXNIYW5kbGVkKVxuICAgICAgICAgICAgICAgIGNtLmN1ck9wLmN1cnNvckFjdGl2aXR5ID0gZmFsc2U7XG4gICAgICAgICAgICB2aW0uc3RhdHVzID0gY20uc3RhdGUudmltLnN0YXR1cztcbiAgICAgICAgICAgIGNtLnN0YXRlLnZpbSA9IHZpbTtcbiAgICAgICAgICAgIHZpbS5pbnB1dFN0YXRlLmNoYW5nZVF1ZXVlTGlzdCA9IGNoYW5nZVF1ZXVlTGlzdDtcbiAgICAgICAgICAgIHZpbS5pbnB1dFN0YXRlLmNoYW5nZVF1ZXVlID0gbnVsbDtcbiAgICAgICAgfSwgdHJ1ZSk7XG4gICAgfVxuICAgIGlmIChpc0hhbmRsZWQgJiYgIXZpbS52aXN1YWxNb2RlICYmICF2aW0uaW5zZXJ0ICYmIHZpbS52aXN1YWxNb2RlICE9IGNtLnNvbWV0aGluZ1NlbGVjdGVkKCkpIHtcbiAgICAgICAgaGFuZGxlRXh0ZXJuYWxTZWxlY3Rpb24oY20sIHZpbSwgdHJ1ZSk7XG4gICAgfVxuICAgIHJldHVybiBpc0hhbmRsZWQ7XG59XG5yZXNldFZpbUdsb2JhbFN0YXRlKCk7XG5leHBvcnRzLkNvZGVNaXJyb3IgPSBDb2RlTWlycm9yO1xudmFyIGdldFZpbSA9IHZpbUFwaS5tYXliZUluaXRWaW1TdGF0ZV87XG5leHBvcnRzLmhhbmRsZXIgPSB7XG4gICAgJGlkOiBcImFjZS9rZXlib2FyZC92aW1cIixcbiAgICBkcmF3Q3Vyc29yOiBmdW5jdGlvbiAoZWxlbWVudCwgcGl4ZWxQb3MsIGNvbmZpZywgc2VsLCBzZXNzaW9uKSB7XG4gICAgICAgIHZhciB2aW0gPSB0aGlzLnN0YXRlLnZpbSB8fCB7fTtcbiAgICAgICAgdmFyIHcgPSBjb25maWcuY2hhcmFjdGVyV2lkdGg7XG4gICAgICAgIHZhciBoID0gY29uZmlnLmxpbmVIZWlnaHQ7XG4gICAgICAgIHZhciB0b3AgPSBwaXhlbFBvcy50b3A7XG4gICAgICAgIHZhciBsZWZ0ID0gcGl4ZWxQb3MubGVmdDtcbiAgICAgICAgaWYgKCF2aW0uaW5zZXJ0TW9kZSkge1xuICAgICAgICAgICAgdmFyIGlzYmFja3dhcmRzID0gIXNlbC5jdXJzb3JcbiAgICAgICAgICAgICAgICA/IHNlc3Npb24uc2VsZWN0aW9uLmlzQmFja3dhcmRzKCkgfHwgc2Vzc2lvbi5zZWxlY3Rpb24uaXNFbXB0eSgpXG4gICAgICAgICAgICAgICAgOiBSYW5nZS5jb21wYXJlUG9pbnRzKHNlbC5jdXJzb3IsIHNlbC5zdGFydCkgPD0gMDtcbiAgICAgICAgICAgIGlmICghaXNiYWNrd2FyZHMgJiYgbGVmdCA+IHcpXG4gICAgICAgICAgICAgICAgbGVmdCAtPSB3O1xuICAgICAgICB9XG4gICAgICAgIGlmICghdmltLmluc2VydE1vZGUgJiYgdmltLnN0YXR1cykge1xuICAgICAgICAgICAgaCA9IGggLyAyO1xuICAgICAgICAgICAgdG9wICs9IGg7XG4gICAgICAgIH1cbiAgICAgICAgZG9tTGliLnRyYW5zbGF0ZShlbGVtZW50LCBsZWZ0LCB0b3ApO1xuICAgICAgICBkb21MaWIuc2V0U3R5bGUoZWxlbWVudC5zdHlsZSwgXCJ3aWR0aFwiLCB3ICsgXCJweFwiKTtcbiAgICAgICAgZG9tTGliLnNldFN0eWxlKGVsZW1lbnQuc3R5bGUsIFwiaGVpZ2h0XCIsIGggKyBcInB4XCIpO1xuICAgIH0sXG4gICAgJGdldERpcmVjdGlvbkZvckhpZ2hsaWdodDogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICB2YXIgY20gPSBlZGl0b3Iuc3RhdGUuY207XG4gICAgICAgIHZhciB2aW0gPSBnZXRWaW0oY20pO1xuICAgICAgICBpZiAoIXZpbS5pbnNlcnRNb2RlKSB7XG4gICAgICAgICAgICByZXR1cm4gZWRpdG9yLnNlc3Npb24uc2VsZWN0aW9uLmlzQmFja3dhcmRzKCkgfHwgZWRpdG9yLnNlc3Npb24uc2VsZWN0aW9uLmlzRW1wdHkoKTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgaGFuZGxlS2V5Ym9hcmQ6IGZ1bmN0aW9uIChkYXRhLCBoYXNoSWQsIGtleSwga2V5Q29kZSwgZSkge1xuICAgICAgICB2YXIgZWRpdG9yID0gZGF0YS5lZGl0b3I7XG4gICAgICAgIHZhciBjbSA9IGVkaXRvci5zdGF0ZS5jbTtcbiAgICAgICAgdmFyIHZpbSA9IGdldFZpbShjbSk7XG4gICAgICAgIGlmIChrZXlDb2RlID09IC0xKVxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICBpZiAoIXZpbS5pbnNlcnRNb2RlKSB7XG4gICAgICAgICAgICBpZiAoaGFzaElkID09IC0xKSB7XG4gICAgICAgICAgICAgICAgaWYgKGtleS5jaGFyQ29kZUF0KDApID4gMHhGRikge1xuICAgICAgICAgICAgICAgICAgICBpZiAoZGF0YS5pbnB1dEtleSkge1xuICAgICAgICAgICAgICAgICAgICAgICAga2V5ID0gZGF0YS5pbnB1dEtleTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChrZXkgJiYgZGF0YS5pbnB1dEhhc2ggPT0gNClcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBrZXkgPSBrZXkudG9VcHBlckNhc2UoKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBkYXRhLmlucHV0Q2hhciA9IGtleTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGhhc2hJZCA9PSA0IHx8IGhhc2hJZCA9PSAwKSB7XG4gICAgICAgICAgICAgICAgaWYgKGRhdGEuaW5wdXRLZXkgPT0ga2V5ICYmIGRhdGEuaW5wdXRIYXNoID09IGhhc2hJZCAmJiBkYXRhLmlucHV0Q2hhcikge1xuICAgICAgICAgICAgICAgICAgICBrZXkgPSBkYXRhLmlucHV0Q2hhcjtcbiAgICAgICAgICAgICAgICAgICAgaGFzaElkID0gLTE7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICBkYXRhLmlucHV0Q2hhciA9IG51bGw7XG4gICAgICAgICAgICAgICAgICAgIGRhdGEuaW5wdXRLZXkgPSBrZXk7XG4gICAgICAgICAgICAgICAgICAgIGRhdGEuaW5wdXRIYXNoID0gaGFzaElkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGRhdGEuaW5wdXRDaGFyID0gZGF0YS5pbnB1dEtleSA9IG51bGw7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGNtLnN0YXRlLm92ZXJ3cml0ZSAmJiB2aW0uaW5zZXJ0TW9kZSAmJiBrZXkgPT0gXCJiYWNrc3BhY2VcIiAmJiBoYXNoSWQgPT0gMCkge1xuICAgICAgICAgICAgcmV0dXJuIHsgY29tbWFuZDogXCJnb3RvbGVmdFwiIH07XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGtleSA9PSBcImNcIiAmJiBoYXNoSWQgPT0gMSkgeyAvLyBrZXkgPT0gXCJjdHJsLWNcIlxuICAgICAgICAgICAgaWYgKCF1c2VyYWdlbnQuaXNNYWMgJiYgZWRpdG9yLmdldENvcHlUZXh0KCkpIHtcbiAgICAgICAgICAgICAgICBlZGl0b3Iub25jZShcImNvcHlcIiwgZnVuY3Rpb24gKCkge1xuICAgICAgICAgICAgICAgICAgICBpZiAodmltLmluc2VydE1vZGUpXG4gICAgICAgICAgICAgICAgICAgICAgICBlZGl0b3Iuc2VsZWN0aW9uLmNsZWFyU2VsZWN0aW9uKCk7XG4gICAgICAgICAgICAgICAgICAgIGVsc2VcbiAgICAgICAgICAgICAgICAgICAgICAgIGNtLm9wZXJhdGlvbihmdW5jdGlvbiAoKSB7IGV4aXRWaXN1YWxNb2RlKGNtKTsgfSk7XG4gICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHsgY29tbWFuZDogXCJudWxsXCIsIHBhc3NFdmVudDogdHJ1ZSB9O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGlmIChrZXkgPT0gXCJlc2NcIiAmJiAhdmltLmluc2VydE1vZGUgJiYgIXZpbS52aXN1YWxNb2RlICYmICFjbS5hY2UuaW5NdWx0aVNlbGVjdE1vZGUpIHtcbiAgICAgICAgICAgIHZhciBzZWFyY2hTdGF0ZSA9IGdldFNlYXJjaFN0YXRlKGNtKTtcbiAgICAgICAgICAgIHZhciBvdmVybGF5ID0gc2VhcmNoU3RhdGUuZ2V0T3ZlcmxheSgpO1xuICAgICAgICAgICAgaWYgKG92ZXJsYXkpXG4gICAgICAgICAgICAgICAgY20ucmVtb3ZlT3ZlcmxheShvdmVybGF5KTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoaGFzaElkID09IC0xIHx8IGhhc2hJZCAmIDEgfHwgaGFzaElkID09PSAwICYmIGtleS5sZW5ndGggPiAxKSB7XG4gICAgICAgICAgICB2YXIgaW5zZXJ0TW9kZSA9IHZpbS5pbnNlcnRNb2RlO1xuICAgICAgICAgICAgdmFyIG5hbWUgPSBsb29rdXBLZXkoaGFzaElkLCBrZXksIGUgfHwge30sIHZpbSk7XG4gICAgICAgICAgICBpZiAodmltLnN0YXR1cyA9PSBudWxsKVxuICAgICAgICAgICAgICAgIHZpbS5zdGF0dXMgPSBcIlwiO1xuICAgICAgICAgICAgdmFyIGlzSGFuZGxlZCA9IG11bHRpU2VsZWN0SGFuZGxlS2V5KGNtLCBuYW1lLCAndXNlcicpO1xuICAgICAgICAgICAgdmltID0gZ2V0VmltKGNtKTsgLy8gbWF5IGJlIGNoYW5nZWQgYnkgbXVsdGlTZWxlY3RIYW5kbGVLZXlcbiAgICAgICAgICAgIGlmIChpc0hhbmRsZWQgJiYgdmltLnN0YXR1cyAhPSBudWxsKVxuICAgICAgICAgICAgICAgIHZpbS5zdGF0dXMgKz0gbmFtZTtcbiAgICAgICAgICAgIGVsc2UgaWYgKHZpbS5zdGF0dXMgPT0gbnVsbClcbiAgICAgICAgICAgICAgICB2aW0uc3RhdHVzID0gXCJcIjtcbiAgICAgICAgICAgIGNtLl9zaWduYWwoXCJjaGFuZ2VTdGF0dXNcIik7XG4gICAgICAgICAgICBpZiAoIWlzSGFuZGxlZCAmJiAoaGFzaElkICE9IC0xIHx8IGluc2VydE1vZGUpKVxuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIHJldHVybiB7IGNvbW1hbmQ6IFwibnVsbFwiLCBwYXNzRXZlbnQ6ICFpc0hhbmRsZWQgfTtcbiAgICAgICAgfVxuICAgIH0sXG4gICAgYXR0YWNoOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgIGlmICghZWRpdG9yLnN0YXRlKVxuICAgICAgICAgICAgZWRpdG9yLnN0YXRlID0ge307XG4gICAgICAgIHZhciBjbSA9IG5ldyBDb2RlTWlycm9yKGVkaXRvcik7XG4gICAgICAgIGVkaXRvci5zdGF0ZS5jbSA9IGNtO1xuICAgICAgICBlZGl0b3IuJHZpbU1vZGVIYW5kbGVyID0gdGhpcztcbiAgICAgICAgZW50ZXJWaW1Nb2RlKGNtKTtcbiAgICAgICAgZ2V0VmltKGNtKS5zdGF0dXMgPSBudWxsO1xuICAgICAgICBjbS5vbigndmltLWNvbW1hbmQtZG9uZScsIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICAgIGlmIChjbS52aXJ0dWFsU2VsZWN0aW9uTW9kZSgpKVxuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIGdldFZpbShjbSkuc3RhdHVzID0gbnVsbDtcbiAgICAgICAgICAgIGNtLmFjZS5fc2lnbmFsKFwiY2hhbmdlU3RhdHVzXCIpO1xuICAgICAgICAgICAgY20uYWNlLnNlc3Npb24ubWFya1VuZG9Hcm91cCgpO1xuICAgICAgICB9KTtcbiAgICAgICAgY20ub24oXCJjaGFuZ2VTdGF0dXNcIiwgZnVuY3Rpb24gKCkge1xuICAgICAgICAgICAgY20uYWNlLnJlbmRlcmVyLnVwZGF0ZUN1cnNvcigpO1xuICAgICAgICAgICAgY20uYWNlLl9zaWduYWwoXCJjaGFuZ2VTdGF0dXNcIik7XG4gICAgICAgIH0pO1xuICAgICAgICBjbS5vbihcInZpbS1tb2RlLWNoYW5nZVwiLCBmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICBpZiAoY20udmlydHVhbFNlbGVjdGlvbk1vZGUoKSlcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB1cGRhdGVJbnB1dE1vZGUoKTtcbiAgICAgICAgICAgIGNtLl9zaWduYWwoXCJjaGFuZ2VTdGF0dXNcIik7XG4gICAgICAgIH0pO1xuICAgICAgICBmdW5jdGlvbiB1cGRhdGVJbnB1dE1vZGUoKSB7XG4gICAgICAgICAgICB2YXIgaXNJbnRzZXJ0ID0gZ2V0VmltKGNtKS5pbnNlcnRNb2RlO1xuICAgICAgICAgICAgY20uYWNlLnJlbmRlcmVyLnNldFN0eWxlKFwibm9ybWFsLW1vZGVcIiwgIWlzSW50c2VydCk7XG4gICAgICAgICAgICBlZGl0b3IudGV4dElucHV0LnNldENvbW1hbmRNb2RlKCFpc0ludHNlcnQpO1xuICAgICAgICAgICAgZWRpdG9yLnJlbmRlcmVyLiRrZWVwVGV4dEFyZWFBdEN1cnNvciA9IGlzSW50c2VydDtcbiAgICAgICAgICAgIGVkaXRvci5yZW5kZXJlci4kYmxvY2tDdXJzb3IgPSAhaXNJbnRzZXJ0O1xuICAgICAgICB9XG4gICAgICAgIHVwZGF0ZUlucHV0TW9kZSgpO1xuICAgICAgICBlZGl0b3IucmVuZGVyZXIuJGN1cnNvckxheWVyLmRyYXdDdXJzb3IgPSB0aGlzLmRyYXdDdXJzb3IuYmluZChjbSk7XG4gICAgfSxcbiAgICBkZXRhY2g6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgdmFyIGNtID0gZWRpdG9yLnN0YXRlLmNtO1xuICAgICAgICBsZWF2ZVZpbU1vZGUoY20pO1xuICAgICAgICBjbS5kZXN0cm95KCk7XG4gICAgICAgIGVkaXRvci5zdGF0ZS5jbSA9IG51bGw7XG4gICAgICAgIGVkaXRvci4kdmltTW9kZUhhbmRsZXIgPSBudWxsO1xuICAgICAgICBlZGl0b3IucmVuZGVyZXIuJGN1cnNvckxheWVyLmRyYXdDdXJzb3IgPSBudWxsO1xuICAgICAgICBlZGl0b3IucmVuZGVyZXIuc2V0U3R5bGUoXCJub3JtYWwtbW9kZVwiLCBmYWxzZSk7XG4gICAgICAgIGVkaXRvci50ZXh0SW5wdXQuc2V0Q29tbWFuZE1vZGUoZmFsc2UpO1xuICAgICAgICBlZGl0b3IucmVuZGVyZXIuJGtlZXBUZXh0QXJlYUF0Q3Vyc29yID0gdHJ1ZTtcbiAgICB9LFxuICAgIGdldFN0YXR1c1RleHQ6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgdmFyIGNtID0gZWRpdG9yLnN0YXRlLmNtO1xuICAgICAgICB2YXIgdmltID0gZ2V0VmltKGNtKTtcbiAgICAgICAgaWYgKHZpbS5pbnNlcnRNb2RlKVxuICAgICAgICAgICAgcmV0dXJuIFwiSU5TRVJUXCI7XG4gICAgICAgIHZhciBzdGF0dXMgPSBcIlwiO1xuICAgICAgICBpZiAodmltLnZpc3VhbE1vZGUpIHtcbiAgICAgICAgICAgIHN0YXR1cyArPSBcIlZJU1VBTFwiO1xuICAgICAgICAgICAgaWYgKHZpbS52aXN1YWxMaW5lKVxuICAgICAgICAgICAgICAgIHN0YXR1cyArPSBcIiBMSU5FXCI7XG4gICAgICAgICAgICBpZiAodmltLnZpc3VhbEJsb2NrKVxuICAgICAgICAgICAgICAgIHN0YXR1cyArPSBcIiBCTE9DS1wiO1xuICAgICAgICB9XG4gICAgICAgIGlmICh2aW0uc3RhdHVzKVxuICAgICAgICAgICAgc3RhdHVzICs9IChzdGF0dXMgPyBcIiBcIiA6IFwiXCIpICsgdmltLnN0YXR1cztcbiAgICAgICAgcmV0dXJuIHN0YXR1cztcbiAgICB9XG59O1xudmltQXBpLmRlZmluZU9wdGlvbih7XG4gICAgbmFtZTogXCJ3cmFwXCIsXG4gICAgc2V0OiBmdW5jdGlvbiAodmFsdWUsIGNtKSB7XG4gICAgICAgIGlmIChjbSkge1xuICAgICAgICAgICAgY20uYWNlLnNldE9wdGlvbihcIndyYXBcIiwgdmFsdWUpO1xuICAgICAgICB9XG4gICAgfSxcbiAgICB0eXBlOiBcImJvb2xlYW5cIlxufSwgZmFsc2UpO1xudmltQXBpLmRlZmluZUV4KCd3cml0ZScsICd3JywgZnVuY3Rpb24gKCkge1xuICAgIGNvbnNvbGUubG9nKCc6d3JpdGUgaXMgbm90IGltcGxlbWVudGVkJyk7XG59KTtcbmRlZmF1bHRLZXltYXAucHVzaCh7IGtleXM6ICd6YycsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdmb2xkJywgYWN0aW9uQXJnczogeyBvcGVuOiBmYWxzZSB9IH0sIHsga2V5czogJ3pDJywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2ZvbGQnLCBhY3Rpb25BcmdzOiB7IG9wZW46IGZhbHNlLCBhbGw6IHRydWUgfSB9LCB7IGtleXM6ICd6bycsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdmb2xkJywgYWN0aW9uQXJnczogeyBvcGVuOiB0cnVlIH0gfSwgeyBrZXlzOiAnek8nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZm9sZCcsIGFjdGlvbkFyZ3M6IHsgb3BlbjogdHJ1ZSwgYWxsOiB0cnVlIH0gfSwgeyBrZXlzOiAnemEnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZm9sZCcsIGFjdGlvbkFyZ3M6IHsgdG9nZ2xlOiB0cnVlIH0gfSwgeyBrZXlzOiAnekEnLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnZm9sZCcsIGFjdGlvbkFyZ3M6IHsgdG9nZ2xlOiB0cnVlLCBhbGw6IHRydWUgfSB9LCB7IGtleXM6ICd6ZicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdmb2xkJywgYWN0aW9uQXJnczogeyBvcGVuOiB0cnVlLCBhbGw6IHRydWUgfSB9LCB7IGtleXM6ICd6ZCcsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdmb2xkJywgYWN0aW9uQXJnczogeyBvcGVuOiB0cnVlLCBhbGw6IHRydWUgfSB9LCB7IGtleXM6ICc8Qy1BLWs+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2FjZUNvbW1hbmQnLCBhY3Rpb25BcmdzOiB7IG5hbWU6IFwiYWRkQ3Vyc29yQWJvdmVcIiB9IH0sIHsga2V5czogJzxDLUEtaj4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnYWNlQ29tbWFuZCcsIGFjdGlvbkFyZ3M6IHsgbmFtZTogXCJhZGRDdXJzb3JCZWxvd1wiIH0gfSwgeyBrZXlzOiAnPEMtQS1TLWs+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2FjZUNvbW1hbmQnLCBhY3Rpb25BcmdzOiB7IG5hbWU6IFwiYWRkQ3Vyc29yQWJvdmVTa2lwQ3VycmVudFwiIH0gfSwgeyBrZXlzOiAnPEMtQS1TLWo+JywgdHlwZTogJ2FjdGlvbicsIGFjdGlvbjogJ2FjZUNvbW1hbmQnLCBhY3Rpb25BcmdzOiB7IG5hbWU6IFwiYWRkQ3Vyc29yQmVsb3dTa2lwQ3VycmVudFwiIH0gfSwgeyBrZXlzOiAnPEMtQS1oPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdhY2VDb21tYW5kJywgYWN0aW9uQXJnczogeyBuYW1lOiBcInNlbGVjdE1vcmVCZWZvcmVcIiB9IH0sIHsga2V5czogJzxDLUEtbD4nLCB0eXBlOiAnYWN0aW9uJywgYWN0aW9uOiAnYWNlQ29tbWFuZCcsIGFjdGlvbkFyZ3M6IHsgbmFtZTogXCJzZWxlY3RNb3JlQWZ0ZXJcIiB9IH0sIHsga2V5czogJzxDLUEtUy1oPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdhY2VDb21tYW5kJywgYWN0aW9uQXJnczogeyBuYW1lOiBcInNlbGVjdE5leHRCZWZvcmVcIiB9IH0sIHsga2V5czogJzxDLUEtUy1sPicsIHR5cGU6ICdhY3Rpb24nLCBhY3Rpb246ICdhY2VDb21tYW5kJywgYWN0aW9uQXJnczogeyBuYW1lOiBcInNlbGVjdE5leHRBZnRlclwiIH0gfSk7XG5kZWZhdWx0S2V5bWFwLnB1c2goe1xuICAgIGtleXM6ICdncScsXG4gICAgdHlwZTogJ29wZXJhdG9yJyxcbiAgICBvcGVyYXRvcjogJ2hhcmRXcmFwJ1xufSk7XG52aW1BcGkuZGVmaW5lT3BlcmF0b3IoXCJoYXJkV3JhcFwiLCBmdW5jdGlvbiAoY20sIG9wZXJhdG9yQXJncywgcmFuZ2VzLCBvbGRBbmNob3IsIG5ld0hlYWQpIHtcbiAgICB2YXIgYW5jaG9yID0gcmFuZ2VzWzBdLmFuY2hvci5saW5lO1xuICAgIHZhciBoZWFkID0gcmFuZ2VzWzBdLmhlYWQubGluZTtcbiAgICBpZiAob3BlcmF0b3JBcmdzLmxpbmV3aXNlKVxuICAgICAgICBoZWFkLS07XG4gICAgaGFyZFdyYXAoY20uYWNlLCB7IHN0YXJ0Um93OiBhbmNob3IsIGVuZFJvdzogaGVhZCB9KTtcbiAgICByZXR1cm4gUG9zKGhlYWQsIDApO1xufSk7XG5kZWZpbmVPcHRpb24oJ3RleHR3aWR0aCcsIHVuZGVmaW5lZCwgJ251bWJlcicsIFsndHcnXSwgZnVuY3Rpb24gKHdpZHRoLCBjbSkge1xuICAgIGlmIChjbSA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIHJldHVybjtcbiAgICB9XG4gICAgaWYgKHdpZHRoID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgdmFyIHZhbHVlID0gY20uYWNlLmdldE9wdGlvbigncHJpbnRNYXJnaW5Db2x1bW4nKTtcbiAgICAgICAgcmV0dXJuIHZhbHVlO1xuICAgIH1cbiAgICBlbHNlIHtcbiAgICAgICAgdmFyIGNvbHVtbiA9IE1hdGgucm91bmQod2lkdGgpO1xuICAgICAgICBpZiAoY29sdW1uID4gMSkge1xuICAgICAgICAgICAgY20uYWNlLnNldE9wdGlvbigncHJpbnRNYXJnaW5Db2x1bW4nLCBjb2x1bW4pO1xuICAgICAgICB9XG4gICAgfVxufSk7XG5hY3Rpb25zLmFjZUNvbW1hbmQgPSBmdW5jdGlvbiAoY20sIGFjdGlvbkFyZ3MsIHZpbSkge1xuICAgIGNtLnZpbUNtZCA9IGFjdGlvbkFyZ3M7XG4gICAgaWYgKGNtLmFjZS5pblZpcnR1YWxTZWxlY3Rpb25Nb2RlKVxuICAgICAgICBjbS5hY2Uub24oXCJiZWZvcmVFbmRPcGVyYXRpb25cIiwgZGVsYXllZEV4ZWNBY2VDb21tYW5kKTtcbiAgICBlbHNlXG4gICAgICAgIGRlbGF5ZWRFeGVjQWNlQ29tbWFuZChudWxsLCBjbS5hY2UpO1xufTtcbmZ1bmN0aW9uIGRlbGF5ZWRFeGVjQWNlQ29tbWFuZChvcCwgYWNlKSB7XG4gICAgYWNlLm9mZihcImJlZm9yZUVuZE9wZXJhdGlvblwiLCBkZWxheWVkRXhlY0FjZUNvbW1hbmQpO1xuICAgIHZhciBjbWQgPSBhY2Uuc3RhdGUuY20udmltQ21kO1xuICAgIGlmIChjbWQpIHtcbiAgICAgICAgYWNlLmV4ZWNDb21tYW5kKGNtZC5leGVjID8gY21kIDogY21kLm5hbWUsIGNtZC5hcmdzKTtcbiAgICB9XG4gICAgYWNlLmN1ck9wID0gYWNlLnByZXZPcDtcbn1cbmFjdGlvbnMuZm9sZCA9IGZ1bmN0aW9uIChjbSwgYWN0aW9uQXJncywgdmltKSB7XG4gICAgY20uYWNlLmV4ZWNDb21tYW5kKFsndG9nZ2xlRm9sZFdpZGdldCcsICd0b2dnbGVGb2xkV2lkZ2V0JywgJ2ZvbGRPdGhlcicsICd1bmZvbGRhbGwnXG4gICAgXVsoYWN0aW9uQXJncy5hbGwgPyAyIDogMCkgKyAoYWN0aW9uQXJncy5vcGVuID8gMSA6IDApXSk7XG59O1xuZGVmYXVsdEtleW1hcExlbmd0aCA9IGRlZmF1bHRLZXltYXAubGVuZ3RoOyAvLyBhY2VfcGF0Y2hcbmV4cG9ydHMuaGFuZGxlci5kZWZhdWx0S2V5bWFwID0gZGVmYXVsdEtleW1hcDtcbmV4cG9ydHMuaGFuZGxlci5hY3Rpb25zID0gYWN0aW9ucztcbmV4cG9ydHMuVmltID0gdmltQXBpO1xuXG59KTsgICAgICAgICAgICAgICAgKGZ1bmN0aW9uKCkge1xuICAgICAgICAgICAgICAgICAgICBhY2UucmVxdWlyZShbXCJhY2Uva2V5Ym9hcmQvdmltXCJdLCBmdW5jdGlvbihtKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAodHlwZW9mIG1vZHVsZSA9PSBcIm9iamVjdFwiICYmIHR5cGVvZiBleHBvcnRzID09IFwib2JqZWN0XCIgJiYgbW9kdWxlKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgbW9kdWxlLmV4cG9ydHMgPSBtO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgICAgICB9KSgpO1xuICAgICAgICAgICAgIl0sIm5hbWVzIjpbXSwic291cmNlUm9vdCI6IiJ9