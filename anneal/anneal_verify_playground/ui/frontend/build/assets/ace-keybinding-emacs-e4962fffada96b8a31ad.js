(globalThis["webpackChunkui"] = globalThis["webpackChunkui"] || []).push([["ace-keybinding-emacs"],{

/***/ "./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-emacs.js"
/*!*********************************************************************************************************!*\
  !*** ./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-emacs.js ***!
  \*********************************************************************************************************/
(module, __unused_webpack_exports, __webpack_require__) {

/* module decorator */ module = __webpack_require__.nmd(module);
ace.define("ace/occur",["require","exports","module","ace/lib/oop","ace/search","ace/edit_session","ace/search_highlight","ace/lib/dom"], function(require, exports, module){"use strict";
var __extends = (this && this.__extends) || (function () {
    var extendStatics = function (d, b) {
        extendStatics = Object.setPrototypeOf ||
            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
            function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };
        return extendStatics(d, b);
    };
    return function (d, b) {
        if (typeof b !== "function" && b !== null)
            throw new TypeError("Class extends value " + String(b) + " is not a constructor or null");
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
var oop = require("./lib/oop");
var Search = require("./search").Search;
var EditSession = require("./edit_session").EditSession;
var SearchHighlight = require("./search_highlight").SearchHighlight;
var Occur = /** @class */ (function (_super) {
    __extends(Occur, _super);
    function Occur() {
        return _super !== null && _super.apply(this, arguments) || this;
    }
    Occur.prototype.enter = function (editor, options) {
        if (!options.needle)
            return false;
        var pos = editor.getCursorPosition();
        this.displayOccurContent(editor, options);
        var translatedPos = this.originalToOccurPosition(editor.session, pos);
        editor.moveCursorToPosition(translatedPos);
        return true;
    };
    Occur.prototype.exit = function (editor, options) {
        var pos = options.translatePosition && editor.getCursorPosition();
        var translatedPos = pos && this.occurToOriginalPosition(editor.session, pos);
        this.displayOriginalContent(editor);
        if (translatedPos)
            editor.moveCursorToPosition(translatedPos);
        return true;
    };
    Occur.prototype.highlight = function (sess, regexp) {
        var hl = sess.$occurHighlight = sess.$occurHighlight || sess.addDynamicMarker(new SearchHighlight(null, "ace_occur-highlight", "text"));
        hl.setRegexp(regexp);
        sess._emit("changeBackMarker"); // force highlight layer redraw
    };
    Occur.prototype.displayOccurContent = function (editor, options) {
        this.$originalSession = editor.session;
        var found = this.matchingLines(editor.session, options);
        var lines = found.map(function (foundLine) { return foundLine.content; });
        var occurSession = new EditSession(lines.join('\n'));
        occurSession.$occur = this;
        occurSession.$occurMatchingLines = found;
        editor.setSession(occurSession);
        this.$useEmacsStyleLineStart = this.$originalSession.$useEmacsStyleLineStart;
        occurSession.$useEmacsStyleLineStart = this.$useEmacsStyleLineStart;
        this.highlight(occurSession, options.re);
        occurSession._emit('changeBackMarker');
    };
    Occur.prototype.displayOriginalContent = function (editor) {
        editor.setSession(this.$originalSession);
        this.$originalSession.$useEmacsStyleLineStart = this.$useEmacsStyleLineStart;
    };
    Occur.prototype.originalToOccurPosition = function (session, pos) {
        var lines = session.$occurMatchingLines;
        var nullPos = { row: 0, column: 0 };
        if (!lines)
            return nullPos;
        for (var i = 0; i < lines.length; i++) {
            if (lines[i].row === pos.row)
                return { row: i, column: pos.column };
        }
        return nullPos;
    };
    Occur.prototype.occurToOriginalPosition = function (session, pos) {
        var lines = session.$occurMatchingLines;
        if (!lines || !lines[pos.row])
            return pos;
        return { row: lines[pos.row].row, column: pos.column };
    };
    Occur.prototype.matchingLines = function (session, options) {
        options = oop.mixin({}, options);
        if (!session || !options.needle)
            return [];
        var search = new Search();
        search.set(options);
        return search.findAll(session).reduce(function (lines, range) {
            var row = range.start.row;
            var last = lines[lines.length - 1];
            return last && last.row === row ?
                lines :
                lines.concat({ row: row, content: session.getLine(row) });
        }, []);
    };
    return Occur;
}(Search));
var dom = require('./lib/dom');
dom.importCssString(".ace_occur-highlight {\n\
    border-radius: 4px;\n\
    background-color: rgba(87, 255, 8, 0.25);\n\
    position: absolute;\n\
    z-index: 4;\n\
    box-sizing: border-box;\n\
    box-shadow: 0 0 4px rgb(91, 255, 50);\n\
}\n\
.ace_dark .ace_occur-highlight {\n\
    background-color: rgb(80, 140, 85);\n\
    box-shadow: 0 0 4px rgb(60, 120, 70);\n\
}\n", "incremental-occur-highlighting", false);
exports.Occur = Occur;

});

ace.define("ace/commands/occur_commands",["require","exports","module","ace/config","ace/occur","ace/keyboard/hash_handler","ace/lib/oop"], function(require, exports, module){var config = require("../config"), Occur = require("../occur").Occur;
var occurStartCommand = {
    name: "occur",
    exec: function (editor, options) {
        var alreadyInOccur = !!editor.session.$occur;
        var occurSessionActive = new Occur().enter(editor, options);
        if (occurSessionActive && !alreadyInOccur)
            OccurKeyboardHandler.installIn(editor);
    },
    readOnly: true
};
var occurCommands = [{
        name: "occurexit",
        bindKey: 'esc|Ctrl-G',
        exec: function (editor) {
            var occur = editor.session.$occur;
            if (!occur)
                return;
            occur.exit(editor, {});
            if (!editor.session.$occur)
                OccurKeyboardHandler.uninstallFrom(editor);
        },
        readOnly: true
    }, {
        name: "occuraccept",
        bindKey: 'enter',
        exec: function (editor) {
            var occur = editor.session.$occur;
            if (!occur)
                return;
            occur.exit(editor, { translatePosition: true });
            if (!editor.session.$occur)
                OccurKeyboardHandler.uninstallFrom(editor);
        },
        readOnly: true
    }];
var HashHandler = require("../keyboard/hash_handler").HashHandler;
var oop = require("../lib/oop");
function OccurKeyboardHandler() { }
oop.inherits(OccurKeyboardHandler, HashHandler);
(function () {
    this.isOccurHandler = true;
    this.attach = function (editor) {
        HashHandler.call(this, occurCommands, editor.commands.platform);
        this.$editor = editor;
    };
    var handleKeyboard$super = this.handleKeyboard;
    this.handleKeyboard = function (data, hashId, key, keyCode) {
        var cmd = handleKeyboard$super.call(this, data, hashId, key, keyCode);
        return (cmd && cmd.command) ? cmd : undefined;
    };
}).call(OccurKeyboardHandler.prototype);
OccurKeyboardHandler.installIn = function (editor) {
    var handler = new this();
    editor.keyBinding.addKeyboardHandler(handler);
    editor.commands.addCommands(occurCommands);
};
OccurKeyboardHandler.uninstallFrom = function (editor) {
    editor.commands.removeCommands(occurCommands);
    var handler = editor.getKeyboardHandler();
    if (handler.isOccurHandler)
        editor.keyBinding.removeKeyboardHandler(handler);
};
exports.occurStartCommand = occurStartCommand;

});

ace.define("ace/commands/incremental_search_commands",["require","exports","module","ace/config","ace/lib/oop","ace/keyboard/hash_handler","ace/commands/occur_commands"], function(require, exports, module){var config = require("../config");
var oop = require("../lib/oop");
var HashHandler = require("../keyboard/hash_handler").HashHandler;
var occurStartCommand = require("./occur_commands").occurStartCommand;
exports.iSearchStartCommands = [{
        name: "iSearch",
        bindKey: { win: "Ctrl-F", mac: "Command-F" },
        exec: function (editor, options) {
            config.loadModule(["core", "ace/incremental_search"], function (e) {
                var iSearch = e.iSearch = e.iSearch || new e.IncrementalSearch();
                iSearch.activate(editor, options.backwards);
                if (options.jumpToFirstMatch)
                    iSearch.next(options);
            });
        },
        readOnly: true
    }, {
        name: "iSearchBackwards",
        exec: function (editor, jumpToNext) { editor.execCommand('iSearch', { backwards: true }); },
        readOnly: true
    }, {
        name: "iSearchAndGo",
        bindKey: { win: "Ctrl-K", mac: "Command-G" },
        exec: function (editor, jumpToNext) { editor.execCommand('iSearch', { jumpToFirstMatch: true, useCurrentOrPrevSearch: true }); },
        readOnly: true
    }, {
        name: "iSearchBackwardsAndGo",
        bindKey: { win: "Ctrl-Shift-K", mac: "Command-Shift-G" },
        exec: function (editor) { editor.execCommand('iSearch', { jumpToFirstMatch: true, backwards: true, useCurrentOrPrevSearch: true }); },
        readOnly: true
    }];
exports.iSearchCommands = [{
        name: "restartSearch",
        bindKey: { win: "Ctrl-F", mac: "Command-F" },
        exec: function (iSearch) {
            iSearch.cancelSearch(true);
        }
    }, {
        name: "searchForward",
        bindKey: { win: "Ctrl-S|Ctrl-K", mac: "Ctrl-S|Command-G" },
        exec: function (iSearch, options) {
            options.useCurrentOrPrevSearch = true;
            iSearch.next(options);
        }
    }, {
        name: "searchBackward",
        bindKey: { win: "Ctrl-R|Ctrl-Shift-K", mac: "Ctrl-R|Command-Shift-G" },
        exec: function (iSearch, options) {
            options.useCurrentOrPrevSearch = true;
            options.backwards = true;
            iSearch.next(options);
        }
    }, {
        name: "extendSearchTerm",
        exec: function (iSearch, string) {
            iSearch.addString(string);
        }
    }, {
        name: "extendSearchTermSpace",
        bindKey: "space",
        exec: function (iSearch) { iSearch.addString(' '); }
    }, {
        name: "shrinkSearchTerm",
        bindKey: "backspace",
        exec: function (iSearch) {
            iSearch.removeChar();
        }
    }, {
        name: 'confirmSearch',
        bindKey: 'return',
        exec: function (iSearch) { iSearch.deactivate(); }
    }, {
        name: 'cancelSearch',
        bindKey: 'esc|Ctrl-G',
        exec: function (iSearch) { iSearch.deactivate(true); }
    }, {
        name: 'occurisearch',
        bindKey: 'Ctrl-O',
        exec: function (iSearch) {
            var options = oop.mixin({}, iSearch.$options);
            iSearch.deactivate();
            occurStartCommand.exec(iSearch.$editor, options);
        }
    }, {
        name: "yankNextWord",
        bindKey: "Ctrl-w",
        exec: function (iSearch) {
            var ed = iSearch.$editor, range = ed.selection.getRangeOfMovements(function (sel) { sel.moveCursorWordRight(); }), string = ed.session.getTextRange(range);
            iSearch.addString(string);
        }
    }, {
        name: "yankNextChar",
        bindKey: "Ctrl-Alt-y",
        exec: function (iSearch) {
            var ed = iSearch.$editor, range = ed.selection.getRangeOfMovements(function (sel) { sel.moveCursorRight(); }), string = ed.session.getTextRange(range);
            iSearch.addString(string);
        }
    }, {
        name: 'recenterTopBottom',
        bindKey: 'Ctrl-l',
        exec: function (iSearch) { iSearch.$editor.execCommand('recenterTopBottom'); }
    }, {
        name: 'selectAllMatches',
        bindKey: 'Ctrl-space',
        exec: function (iSearch) {
            var ed = iSearch.$editor, hl = ed.session.$isearchHighlight, ranges = hl && hl.cache ? hl.cache
                .reduce(function (ranges, ea) {
                return ranges.concat(ea ? ea : []);
            }, []) : [];
            iSearch.deactivate(false);
            ranges.forEach(ed.selection.addRange.bind(ed.selection));
        }
    }, {
        name: 'searchAsRegExp',
        bindKey: 'Alt-r',
        exec: function (iSearch) {
            iSearch.convertNeedleToRegExp();
        }
    }].map(function (cmd) {
    cmd.readOnly = true;
    cmd.isIncrementalSearchCommand = true;
    cmd.scrollIntoView = "animate-cursor";
    return cmd;
});
function IncrementalSearchKeyboardHandler(iSearch) {
    this.$iSearch = iSearch;
}
oop.inherits(IncrementalSearchKeyboardHandler, HashHandler);
(function () {
    this.attach = function (editor) {
        var iSearch = this.$iSearch;
        HashHandler.call(this, exports.iSearchCommands, editor.commands.platform);
        this.$commandExecHandler = editor.commands.on('exec', function (e) {
            if (!e.command.isIncrementalSearchCommand)
                return iSearch.deactivate();
            e.stopPropagation();
            e.preventDefault();
            var scrollTop = editor.session.getScrollTop();
            var result = e.command.exec(iSearch, e.args || {});
            editor.renderer.scrollCursorIntoView(null, 0.5);
            editor.renderer.animateScrolling(scrollTop);
            return result;
        });
    };
    this.detach = function (editor) {
        if (!this.$commandExecHandler)
            return;
        editor.commands.off('exec', this.$commandExecHandler);
        delete this.$commandExecHandler;
    };
    var handleKeyboard$super = this.handleKeyboard;
    this.handleKeyboard = function (data, hashId, key, keyCode) {
        if (((hashId === 1 /*ctrl*/ || hashId === 8 /*command*/) && key === 'v')
            || (hashId === 1 /*ctrl*/ && key === 'y'))
            return null;
        var cmd = handleKeyboard$super.call(this, data, hashId, key, keyCode);
        if (cmd && cmd.command) {
            return cmd;
        }
        if (hashId == -1) {
            var extendCmd = this.commands.extendSearchTerm;
            if (extendCmd) {
                return { command: extendCmd, args: key };
            }
        }
        return false;
    };
}).call(IncrementalSearchKeyboardHandler.prototype);
exports.IncrementalSearchKeyboardHandler = IncrementalSearchKeyboardHandler;

});

ace.define("ace/incremental_search",["require","exports","module","ace/range","ace/search","ace/search_highlight","ace/commands/incremental_search_commands","ace/lib/dom","ace/commands/command_manager","ace/editor","ace/config"], function(require, exports, module){"use strict";
var __extends = (this && this.__extends) || (function () {
    var extendStatics = function (d, b) {
        extendStatics = Object.setPrototypeOf ||
            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
            function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };
        return extendStatics(d, b);
    };
    return function (d, b) {
        if (typeof b !== "function" && b !== null)
            throw new TypeError("Class extends value " + String(b) + " is not a constructor or null");
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
var Range = require("./range").Range;
var Search = require("./search").Search;
var SearchHighlight = require("./search_highlight").SearchHighlight;
var iSearchCommandModule = require("./commands/incremental_search_commands");
var ISearchKbd = iSearchCommandModule.IncrementalSearchKeyboardHandler;
function isRegExp(obj) {
    return obj instanceof RegExp;
}
function regExpToObject(re) {
    var string = String(re), start = string.indexOf('/'), flagStart = string.lastIndexOf('/');
    return {
        expression: string.slice(start + 1, flagStart),
        flags: string.slice(flagStart + 1)
    };
}
function stringToRegExp(string, flags) {
    try {
        return new RegExp(string, flags);
    }
    catch (e) {
        return string;
    }
}
function objectToRegExp(obj) {
    return stringToRegExp(obj.expression, obj.flags);
}
var IncrementalSearch = /** @class */ (function (_super) {
    __extends(IncrementalSearch, _super);
    function IncrementalSearch() {
        var _this = _super.call(this) || this;
        _this.$options = { wrap: false, skipCurrent: false };
        _this.$keyboardHandler = new ISearchKbd(_this);
        return _this;
    }
    IncrementalSearch.prototype.activate = function (editor, backwards) {
        this.$editor = editor;
        this.$startPos = this.$currentPos = editor.getCursorPosition();
        this.$options.needle = '';
        this.$options.backwards = backwards;
        editor.keyBinding.addKeyboardHandler(this.$keyboardHandler);
        this.$originalEditorOnPaste = editor.onPaste;
        editor.onPaste = this.onPaste.bind(this);
        this.$mousedownHandler = editor.on('mousedown', this.onMouseDown.bind(this));
        this.selectionFix(editor);
        this.statusMessage(true);
    };
    IncrementalSearch.prototype.deactivate = function (reset) {
        this.cancelSearch(reset);
        var editor = this.$editor;
        editor.keyBinding.removeKeyboardHandler(this.$keyboardHandler);
        if (this.$mousedownHandler) {
            editor.off('mousedown', this.$mousedownHandler);
            delete this.$mousedownHandler;
        }
        editor.onPaste = this.$originalEditorOnPaste;
        this.message('');
    };
    IncrementalSearch.prototype.selectionFix = function (editor) {
        if (editor.selection.isEmpty() && !editor.session.$emacsMark) {
            editor.clearSelection();
        }
    };
    IncrementalSearch.prototype.highlight = function (regexp) {
        var sess = this.$editor.session, hl = sess.$isearchHighlight = sess.$isearchHighlight || sess.addDynamicMarker(new SearchHighlight(null, "ace_isearch-result", "text"));
        hl.setRegexp(regexp);
        sess._emit("changeBackMarker"); // force highlight layer redraw
    };
    IncrementalSearch.prototype.cancelSearch = function (reset) {
        var e = this.$editor;
        this.$prevNeedle = this.$options.needle;
        this.$options.needle = '';
        if (reset) {
            e.moveCursorToPosition(this.$startPos);
            this.$currentPos = this.$startPos;
        }
        else {
            e.pushEmacsMark && e.pushEmacsMark(this.$startPos, false);
        }
        this.highlight(null);
        return Range.fromPoints(this.$currentPos, this.$currentPos);
    };
    IncrementalSearch.prototype.highlightAndFindWithNeedle = function (moveToNext, needleUpdateFunc) {
        if (!this.$editor)
            return null;
        var options = this.$options;
        if (needleUpdateFunc) {
            options.needle = needleUpdateFunc.call(this, options.needle || '') || '';
        }
        if (options.needle.length === 0) {
            this.statusMessage(true);
            return this.cancelSearch(true);
        }
        options.start = this.$currentPos;
        var session = this.$editor.session, found = this.find(session), shouldSelect = this.$editor.emacsMark ?
            !!this.$editor.emacsMark() : !this.$editor.selection.isEmpty();
        if (found) {
            if (options.backwards)
                found = Range.fromPoints(found.end, found.start);
            this.$editor.selection.setRange(Range.fromPoints(shouldSelect ? this.$startPos : found.end, found.end));
            if (moveToNext)
                this.$currentPos = found.end;
            this.highlight(options.re);
        }
        this.statusMessage(found);
        return found;
    };
    IncrementalSearch.prototype.addString = function (s) {
        return this.highlightAndFindWithNeedle(false, function (needle) {
            if (!isRegExp(needle))
                return needle + s;
            var reObj = regExpToObject(needle);
            reObj.expression += s;
            return objectToRegExp(reObj);
        });
    };
    IncrementalSearch.prototype.removeChar = function (c) {
        return this.highlightAndFindWithNeedle(false, function (needle) {
            if (!isRegExp(needle))
                return needle.substring(0, needle.length - 1);
            var reObj = regExpToObject(needle);
            reObj.expression = reObj.expression.substring(0, reObj.expression.length - 1);
            return objectToRegExp(reObj);
        });
    };
    IncrementalSearch.prototype.next = function (options) {
        options = options || {};
        this.$options.backwards = !!options.backwards;
        this.$currentPos = this.$editor.getCursorPosition();
        return this.highlightAndFindWithNeedle(true, function (needle) {
            return options.useCurrentOrPrevSearch && needle.length === 0 ?
                this.$prevNeedle || '' : needle;
        });
    };
    IncrementalSearch.prototype.onMouseDown = function (evt) {
        this.deactivate();
        return true;
    };
    IncrementalSearch.prototype.onPaste = function (text) {
        this.addString(text);
    };
    IncrementalSearch.prototype.convertNeedleToRegExp = function () {
        return this.highlightAndFindWithNeedle(false, function (needle) {
            return isRegExp(needle) ? needle : stringToRegExp(needle, 'ig');
        });
    };
    IncrementalSearch.prototype.convertNeedleToString = function () {
        return this.highlightAndFindWithNeedle(false, function (needle) {
            return isRegExp(needle) ? regExpToObject(needle).expression : needle;
        });
    };
    IncrementalSearch.prototype.statusMessage = function (found) {
        var options = this.$options, msg = '';
        msg += options.backwards ? 'reverse-' : '';
        msg += 'isearch: ' + options.needle;
        msg += found ? '' : ' (not found)';
        this.message(msg);
    };
    IncrementalSearch.prototype.message = function (msg) {
        if (this.$editor.showCommandLine) {
            this.$editor.showCommandLine(msg);
            this.$editor.focus();
        }
    };
    return IncrementalSearch;
}(Search));
exports.IncrementalSearch = IncrementalSearch;
var dom = require('./lib/dom');
dom.importCssString("\n.ace_marker-layer .ace_isearch-result {\n  position: absolute;\n  z-index: 6;\n  box-sizing: border-box;\n}\ndiv.ace_isearch-result {\n  border-radius: 4px;\n  background-color: rgba(255, 200, 0, 0.5);\n  box-shadow: 0 0 4px rgb(255, 200, 0);\n}\n.ace_dark div.ace_isearch-result {\n  background-color: rgb(100, 110, 160);\n  box-shadow: 0 0 4px rgb(80, 90, 140);\n}", "incremental-search-highlighting", false);
var commands = require("./commands/command_manager");
(function () {
    this.setupIncrementalSearch = function (editor, val) {
        if (this.usesIncrementalSearch == val)
            return;
        this.usesIncrementalSearch = val;
        var iSearchCommands = iSearchCommandModule.iSearchStartCommands;
        var method = val ? 'addCommands' : 'removeCommands';
        this[method](iSearchCommands);
    };
}).call(commands.CommandManager.prototype);
var Editor = require("./editor").Editor;
require("./config").defineOptions(Editor.prototype, "editor", {
    useIncrementalSearch: {
        set: function (val) {
            this.keyBinding.$handlers.forEach(function (handler) {
                if (handler.setupIncrementalSearch) {
                    handler.setupIncrementalSearch(this, val);
                }
            });
            this._emit('incrementalSearchSettingChanged', { isEnabled: val });
        }
    }
});

});

ace.define("ace/keyboard/emacs",["require","exports","module","ace/lib/dom","ace/incremental_search","ace/commands/incremental_search_commands","ace/keyboard/hash_handler","ace/lib/keys"], function(require, exports, module){"use strict";
var dom = require("../lib/dom");
require("../incremental_search");
var iSearchCommandModule = require("../commands/incremental_search_commands");
var HashHandler = require("./hash_handler").HashHandler;
exports.handler = new HashHandler();
exports.handler.isEmacs = true;
exports.handler.$id = "ace/keyboard/emacs";
dom.importCssString("\n.emacs-mode .ace_cursor{\n    border: 1px rgba(50,250,50,0.8) solid!important;\n    box-sizing: border-box!important;\n    background-color: rgba(0,250,0,0.9);\n    opacity: 0.5;\n}\n.emacs-mode .ace_hidden-cursors .ace_cursor{\n    opacity: 1;\n    background-color: transparent;\n}\n.emacs-mode .ace_overwrite-cursors .ace_cursor {\n    opacity: 1;\n    background-color: transparent;\n    border-width: 0 0 2px 2px !important;\n}\n.emacs-mode .ace_text-layer {\n    z-index: 4\n}\n.emacs-mode .ace_cursor-layer {\n    z-index: 2\n}", 'emacsMode', false);
var $formerLongWords;
var $formerLineStart;
exports.handler.attach = function (editor) {
    $formerLongWords = editor.session.$selectLongWords;
    editor.session.$selectLongWords = true;
    $formerLineStart = editor.session.$useEmacsStyleLineStart;
    editor.session.$useEmacsStyleLineStart = true;
    editor.session.$emacsMark = null; // the active mark
    editor.session.$emacsMarkRing = editor.session.$emacsMarkRing || [];
    editor.emacsMark = function () {
        return this.session.$emacsMark;
    };
    editor.setEmacsMark = function (p) {
        this.session.$emacsMark = p;
    };
    editor.pushEmacsMark = function (p, activate) {
        var prevMark = this.session.$emacsMark;
        if (prevMark)
            pushUnique(this.session.$emacsMarkRing, prevMark);
        if (!p || activate)
            this.setEmacsMark(p);
        else
            pushUnique(this.session.$emacsMarkRing, p);
    };
    editor.popEmacsMark = function () {
        var mark = this.emacsMark();
        if (mark) {
            this.setEmacsMark(null);
            return mark;
        }
        return this.session.$emacsMarkRing.pop();
    };
    editor.getLastEmacsMark = function (p) {
        return this.session.$emacsMark || this.session.$emacsMarkRing.slice(-1)[0];
    };
    editor.emacsMarkForSelection = function (replacement) {
        var sel = this.selection, multiRangeLength = this.multiSelect ?
            this.multiSelect.getAllRanges().length : 1, selIndex = sel.index || 0, markRing = this.session.$emacsMarkRing, markIndex = markRing.length - (multiRangeLength - selIndex), lastMark = markRing[markIndex] || sel.anchor;
        if (replacement) {
            markRing.splice(markIndex, 1, "row" in replacement && "column" in replacement ?
                replacement : undefined);
        }
        return lastMark;
    };
    editor.on("click", $resetMarkMode);
    editor.on("changeSession", $kbSessionChange);
    editor.renderer.$blockCursor = true;
    editor.setStyle("emacs-mode");
    editor.commands.addCommands(commands);
    exports.handler.platform = editor.commands.platform;
    editor.$emacsModeHandler = this;
    editor.on('copy', this.onCopy);
    editor.on('paste', this.onPaste);
};
function pushUnique(ring, mark) {
    var last = ring[ring.length - 1];
    if (last && last.row === mark.row && last.column === mark.column) {
        return;
    }
    ring.push(mark);
}
exports.handler.detach = function (editor) {
    editor.renderer.$blockCursor = false;
    editor.session.$selectLongWords = $formerLongWords;
    editor.session.$useEmacsStyleLineStart = $formerLineStart;
    editor.off("click", $resetMarkMode);
    editor.off("changeSession", $kbSessionChange);
    editor.unsetStyle("emacs-mode");
    editor.commands.removeCommands(commands);
    editor.off('copy', this.onCopy);
    editor.off('paste', this.onPaste);
    editor.$emacsModeHandler = null;
};
var $kbSessionChange = function (e) {
    if (e.oldSession) {
        e.oldSession.$selectLongWords = $formerLongWords;
        e.oldSession.$useEmacsStyleLineStart = $formerLineStart;
    }
    $formerLongWords = e.session.$selectLongWords;
    e.session.$selectLongWords = true;
    $formerLineStart = e.session.$useEmacsStyleLineStart;
    e.session.$useEmacsStyleLineStart = true;
    if (!e.session.hasOwnProperty('$emacsMark'))
        e.session.$emacsMark = null;
    if (!e.session.hasOwnProperty('$emacsMarkRing'))
        e.session.$emacsMarkRing = [];
};
var $resetMarkMode = function (e) {
    e.editor.session.$emacsMark = null;
};
var keys = require("../lib/keys").KEY_MODS;
var eMods = { C: "ctrl", S: "shift", M: "alt", CMD: "command" };
var combinations = ["C-S-M-CMD",
    "S-M-CMD", "C-M-CMD", "C-S-CMD", "C-S-M",
    "M-CMD", "S-CMD", "S-M", "C-CMD", "C-M", "C-S",
    "CMD", "M", "S", "C"];
combinations.forEach(function (c) {
    var hashId = 0;
    c.split("-").forEach(function (c) {
        hashId = hashId | keys[eMods[c]];
    });
    eMods[hashId] = c.toLowerCase() + "-";
});
exports.handler.onCopy = function (e, editor) {
    if (editor.$handlesEmacsOnCopy)
        return;
    editor.$handlesEmacsOnCopy = true;
    exports.handler.commands.killRingSave.exec(editor);
    editor.$handlesEmacsOnCopy = false;
};
exports.handler.onPaste = function (e, editor) {
    editor.pushEmacsMark(editor.getCursorPosition());
};
exports.handler.bindKey = function (key, command) {
    if (typeof key == "object")
        key = key[this.platform];
    if (!key)
        return;
    var ckb = this.commandKeyBinding;
    key.split("|").forEach(function (keyPart) {
        keyPart = keyPart.toLowerCase();
        ckb[keyPart] = command;
        var keyParts = keyPart.split(" ").slice(0, -1);
        keyParts.reduce(function (keyMapKeys, keyPart, i) {
            var prefix = keyMapKeys[i - 1] ? keyMapKeys[i - 1] + ' ' : '';
            return keyMapKeys.concat([prefix + keyPart]);
        }, []).forEach(function (keyPart) {
            if (!ckb[keyPart])
                ckb[keyPart] = "null";
        });
    }, this);
};
exports.handler.getStatusText = function (editor, data) {
    var str = "";
    if (data.count)
        str += data.count;
    if (data.keyChain)
        str += " " + data.keyChain;
    return str;
};
exports.handler.handleKeyboard = function (data, hashId, key, keyCode) {
    if (keyCode === -1)
        return undefined;
    var editor = data.editor;
    editor._signal("changeStatus");
    if (hashId == -1) {
        editor.pushEmacsMark();
        if (data.count) {
            var str = new Array(data.count + 1).join(key);
            data.count = null;
            return { command: "insertstring", args: str };
        }
    }
    var modifier = eMods[hashId];
    if (modifier == "c-" || data.count) {
        var count = parseInt(key[key.length - 1]);
        if (typeof count === 'number' && !isNaN(count)) {
            data.count = Math.max(data.count, 0) || 0;
            data.count = 10 * data.count + count;
            return { command: "null" };
        }
    }
    if (modifier)
        key = modifier + key;
    if (data.keyChain)
        key = data.keyChain += " " + key;
    var command = this.commandKeyBinding[key];
    data.keyChain = command == "null" ? key : "";
    if (!command)
        return undefined;
    if (command === "null")
        return { command: "null" };
    if (command === "universalArgument") {
        data.count = -4;
        return { command: "null" };
    }
    var args;
    if (typeof command !== "string") {
        args = command.args;
        if (command.command)
            command = command.command;
        if (command === "goorselect") {
            command = editor.emacsMark() ? args[1] : args[0];
            args = null;
        }
    }
    if (typeof command === "string") {
        if (command === "insertstring" ||
            command === "splitline" ||
            command === "togglecomment") {
            editor.pushEmacsMark();
        }
        command = this.commands[command] || editor.commands.commands[command];
        if (!command)
            return undefined;
    }
    if (!command.readOnly && !command.isYank)
        data.lastCommand = null;
    if (!command.readOnly && editor.emacsMark())
        editor.setEmacsMark(null);
    if (data.count) {
        var count = data.count;
        data.count = 0;
        if (!command || !command.handlesCount) {
            return {
                args: args,
                command: {
                    exec: function (editor, args) {
                        for (var i = 0; i < count; i++)
                            command.exec(editor, args);
                    },
                    multiSelectAction: command.multiSelectAction
                }
            };
        }
        else {
            if (!args)
                args = {};
            if (typeof args === 'object')
                args.count = count;
        }
    }
    return { command: command, args: args };
};
exports.emacsKeys = {
    "Up|C-p": { command: "goorselect", args: ["golineup", "selectup"] },
    "Down|C-n": { command: "goorselect", args: ["golinedown", "selectdown"] },
    "Left|C-b": { command: "goorselect", args: ["gotoleft", "selectleft"] },
    "Right|C-f": { command: "goorselect", args: ["gotoright", "selectright"] },
    "C-Left|M-b": { command: "goorselect", args: ["gotowordleft", "selectwordleft"] },
    "C-Right|M-f": { command: "goorselect", args: ["gotowordright", "selectwordright"] },
    "Home|C-a": { command: "goorselect", args: ["gotolinestart", "selecttolinestart"] },
    "End|C-e": { command: "goorselect", args: ["gotolineend", "selecttolineend"] },
    "C-Home|S-M-,": { command: "goorselect", args: ["gotostart", "selecttostart"] },
    "C-End|S-M-.": { command: "goorselect", args: ["gotoend", "selecttoend"] },
    "S-Up|S-C-p": "selectup",
    "S-Down|S-C-n": "selectdown",
    "S-Left|S-C-b": "selectleft",
    "S-Right|S-C-f": "selectright",
    "S-C-Left|S-M-b": "selectwordleft",
    "S-C-Right|S-M-f": "selectwordright",
    "S-Home|S-C-a": "selecttolinestart",
    "S-End|S-C-e": "selecttolineend",
    "S-C-Home": "selecttostart",
    "S-C-End": "selecttoend",
    "C-l": "recenterTopBottom",
    "M-s": "centerselection",
    "M-g": "gotoline",
    "C-x C-p": "selectall",
    "C-Down": { command: "goorselect", args: ["gotopagedown", "selectpagedown"] },
    "C-Up": { command: "goorselect", args: ["gotopageup", "selectpageup"] },
    "PageDown|C-v": { command: "goorselect", args: ["gotopagedown", "selectpagedown"] },
    "PageUp|M-v": { command: "goorselect", args: ["gotopageup", "selectpageup"] },
    "S-C-Down": "selectpagedown",
    "S-C-Up": "selectpageup",
    "C-s": "iSearch",
    "C-r": "iSearchBackwards",
    "M-C-s": "findnext",
    "M-C-r": "findprevious",
    "S-M-5": "replace",
    "Backspace": "backspace",
    "Delete|C-d": "del",
    "Return|C-m": { command: "insertstring", args: "\n" }, // "newline"
    "C-o": "splitline",
    "M-d|C-Delete": { command: "killWord", args: "right" },
    "C-Backspace|M-Backspace|M-Delete": { command: "killWord", args: "left" },
    "C-k": "killLine",
    "C-y|S-Delete": "yank",
    "M-y": "yankRotate",
    "C-g": "keyboardQuit",
    "C-w|C-S-W": "killRegion",
    "M-w": "killRingSave",
    "C-Space": "setMark",
    "C-x C-x": "exchangePointAndMark",
    "C-t": "transposeletters",
    "M-u": "touppercase", // Doesn't work
    "M-l": "tolowercase",
    "M-/": "autocomplete", // Doesn't work
    "C-u": "universalArgument",
    "M-;": "togglecomment",
    "C-/|C-x u|S-C--|C-z": "undo",
    "S-C-/|S-C-x u|C--|S-C-z": "redo", // infinite undo?
    "C-x r": "selectRectangularRegion",
    "M-x": { command: "focusCommandLine", args: "M-x " }
};
exports.handler.bindKeys(exports.emacsKeys);
exports.handler.addCommands({
    recenterTopBottom: function (editor) {
        var renderer = editor.renderer;
        var pos = renderer.$cursorLayer.getPixelPosition();
        var h = renderer.$size.scrollerHeight - renderer.lineHeight;
        var scrollTop = renderer.scrollTop;
        if (Math.abs(pos.top - scrollTop) < 2) {
            scrollTop = pos.top - h;
        }
        else if (Math.abs(pos.top - scrollTop - h * 0.5) < 2) {
            scrollTop = pos.top;
        }
        else {
            scrollTop = pos.top - h * 0.5;
        }
        editor.session.setScrollTop(scrollTop);
    },
    selectRectangularRegion: function (editor) {
        editor.multiSelect.toggleBlockSelection();
    },
    setMark: {
        exec: function (editor, args) {
            if (args && args.count) {
                if (editor.inMultiSelectMode)
                    editor.forEachSelection(moveToMark);
                else
                    moveToMark();
                moveToMark();
                return;
            }
            var mark = editor.emacsMark(), ranges = editor.selection.getAllRanges(), rangePositions = ranges.map(function (r) { return { row: r.start.row, column: r.start.column }; }), transientMarkModeActive = true, hasNoSelection = ranges.every(function (range) { return range.isEmpty(); });
            if (transientMarkModeActive && (mark || !hasNoSelection)) {
                if (editor.inMultiSelectMode)
                    editor.forEachSelection({ exec: editor.clearSelection.bind(editor) });
                else
                    editor.clearSelection();
                if (mark)
                    editor.pushEmacsMark(null);
                return;
            }
            if (!mark) {
                rangePositions.forEach(function (pos) { editor.pushEmacsMark(pos); });
                editor.setEmacsMark(rangePositions[rangePositions.length - 1]);
                return;
            }
            function moveToMark() {
                var mark = editor.popEmacsMark();
                mark && editor.moveCursorToPosition(mark);
            }
        },
        readOnly: true,
        handlesCount: true
    },
    exchangePointAndMark: {
        exec: function exchangePointAndMark$exec(editor, args) {
            var sel = editor.selection;
            if (!args.count && !sel.isEmpty()) { // just invert selection
                sel.setSelectionRange(sel.getRange(), !sel.isBackwards());
                return;
            }
            if (args.count) { // replace mark and point
                var pos = { row: sel.lead.row, column: sel.lead.column };
                sel.clearSelection();
                sel.moveCursorToPosition(editor.emacsMarkForSelection(pos));
            }
            else { // create selection to last mark
                sel.selectToPosition(editor.emacsMarkForSelection());
            }
        },
        readOnly: true,
        handlesCount: true,
        multiSelectAction: "forEach"
    },
    killWord: {
        exec: function (editor, dir) {
            editor.clearSelection();
            if (dir == "left")
                editor.selection.selectWordLeft();
            else
                editor.selection.selectWordRight();
            var range = editor.getSelectionRange();
            var text = editor.session.getTextRange(range);
            exports.killRing.add(text);
            editor.session.remove(range);
            editor.clearSelection();
        },
        multiSelectAction: "forEach"
    },
    killLine: function (editor) {
        editor.pushEmacsMark(null);
        editor.clearSelection();
        var range = editor.getSelectionRange();
        var line = editor.session.getLine(range.start.row);
        range.end.column = line.length;
        line = line.substr(range.start.column);
        var foldLine = editor.session.getFoldLine(range.start.row);
        if (foldLine && range.end.row != foldLine.end.row) {
            range.end.row = foldLine.end.row;
            line = "x";
        }
        if (/^\s*$/.test(line)) {
            range.end.row++;
            line = editor.session.getLine(range.end.row);
            range.end.column = /^\s*$/.test(line) ? line.length : 0;
        }
        var text = editor.session.getTextRange(range);
        if (editor.prevOp.command == this)
            exports.killRing.append(text);
        else
            exports.killRing.add(text);
        editor.session.remove(range);
        editor.clearSelection();
    },
    yank: function (editor) {
        editor.onPaste(exports.killRing.get() || '');
        editor.keyBinding.$data.lastCommand = "yank";
    },
    yankRotate: function (editor) {
        if (editor.keyBinding.$data.lastCommand != "yank")
            return;
        editor.undo();
        editor.session.$emacsMarkRing.pop(); // also undo recording mark
        editor.onPaste(exports.killRing.rotate());
        editor.keyBinding.$data.lastCommand = "yank";
    },
    killRegion: {
        exec: function (editor) {
            exports.killRing.add(editor.getCopyText());
            editor.commands.byName.cut.exec(editor);
            editor.setEmacsMark(null);
        },
        readOnly: true,
        multiSelectAction: "forEach"
    },
    killRingSave: {
        exec: function (editor) {
            editor.$handlesEmacsOnCopy = true;
            var marks = editor.session.$emacsMarkRing.slice(), deselectedMarks = [];
            exports.killRing.add(editor.getCopyText());
            setTimeout(function () {
                function deselect() {
                    var sel = editor.selection, range = sel.getRange(), pos = sel.isBackwards() ? range.end : range.start;
                    deselectedMarks.push({ row: pos.row, column: pos.column });
                    sel.clearSelection();
                }
                editor.$handlesEmacsOnCopy = false;
                if (editor.inMultiSelectMode)
                    editor.forEachSelection({ exec: deselect });
                else
                    deselect();
                editor.setEmacsMark(null);
                editor.session.$emacsMarkRing = marks.concat(deselectedMarks.reverse());
            }, 0);
        },
        readOnly: true
    },
    keyboardQuit: function (editor) {
        editor.selection.clearSelection();
        editor.setEmacsMark(null);
        editor.keyBinding.$data.count = null;
    },
    focusCommandLine: function (editor, arg) {
        if (editor.showCommandLine)
            editor.showCommandLine(arg);
    }
});
exports.handler.addCommands(iSearchCommandModule.iSearchStartCommands);
var commands = exports.handler.commands;
commands.yank.isYank = true;
commands.yankRotate.isYank = true;
exports.killRing = {
    $data: [],
    add: function (str) {
        str && this.$data.push(str);
        if (this.$data.length > 30)
            this.$data.shift();
    },
    append: function (str) {
        var idx = this.$data.length - 1;
        var text = this.$data[idx] || "";
        if (str)
            text += str;
        if (text)
            this.$data[idx] = text;
    },
    get: function (n) {
        n = n || 1;
        return this.$data.slice(this.$data.length - n, this.$data.length).reverse().join('\n');
    },
    pop: function () {
        if (this.$data.length > 1)
            this.$data.pop();
        return this.get();
    },
    rotate: function () {
        this.$data.unshift(this.$data.pop());
        return this.get();
    }
};

});                (function() {
                    ace.require(["ace/keyboard/emacs"], function(m) {
                        if ( true && module) {
                            module.exports = m;
                        }
                    });
                })();
            

/***/ }

}]);
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYWNlLWtleWJpbmRpbmctZW1hY3MtZTQ5NjJmZmZhZGE5NmI4YTMxYWQuanMiLCJtYXBwaW5ncyI6Ijs7Ozs7Ozs7O0FBQUEsNktBQTZLO0FBQzdLO0FBQ0E7QUFDQTtBQUNBLGVBQWUsZ0JBQWdCLHNDQUFzQyxrQkFBa0I7QUFDdkYsOEJBQThCO0FBQzlCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3QjtBQUN4QjtBQUNBO0FBQ0EsQ0FBQztBQUNEO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3Q0FBd0M7QUFDeEM7QUFDQTtBQUNBO0FBQ0E7QUFDQSxxREFBcUQsMkJBQTJCO0FBQ2hGO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHdCQUF3QjtBQUN4QjtBQUNBO0FBQ0Esd0JBQXdCLGtCQUFrQjtBQUMxQztBQUNBLHlCQUF5QjtBQUN6QjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0EsOEJBQThCO0FBQzlCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLCtCQUErQix5Q0FBeUM7QUFDeEUsU0FBUztBQUNUO0FBQ0E7QUFDQSxDQUFDO0FBQ0Q7QUFDQSwyQ0FBMkM7QUFDM0MsdUJBQXVCO0FBQ3ZCLDZDQUE2QztBQUM3Qyx1QkFBdUI7QUFDdkIsZUFBZTtBQUNmLDJCQUEyQjtBQUMzQix5Q0FBeUM7QUFDekMsQ0FBQztBQUNELGdDQUFnQztBQUNoQyx1Q0FBdUM7QUFDdkMseUNBQXlDO0FBQ3pDLENBQUM7QUFDRDs7QUFFQSxDQUFDOztBQUVELCtL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QUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSwyQkFBMkI7QUFDM0I7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSx3Q0FBd0M7QUFDeEM7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxDQUFDO0FBQ0Q7QUFDQTtBQUNBLDhEQUE4RCx1QkFBdUIsZUFBZSwyQkFBMkIsR0FBRywwQkFBMEIsdUJBQXVCLDZDQUE2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QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSw2Q0FBNkM7QUFDN0M7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLDJDQUEyQyxrQ0FBa0M7QUFDN0U7QUFDQTtBQUNBO0FBQ0E7QUFDQSw4Q0FBOEMsZ0JBQWdCO0FBQzlEO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsYUFBYTtBQUNiLFNBQVM7QUFDVDtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLENBQUM7QUFDRDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTs7QUFFQSxDQUFDLGtCQUFrQjtBQUNuQjtBQUNBLDRCQUE0QixLQUF1RDtBQUNuRjtBQUNBO0FBQ0EscUJBQXFCO0FBQ3JCLGlCQUFpQjtBQUNqQixZIiwic291cmNlcyI6WyJ3ZWJwYWNrOi8vdWkvLi9ub2RlX21vZHVsZXMvLnBucG0vYWNlLWJ1aWxkc0AxLjQzLjYvbm9kZV9tb2R1bGVzL2FjZS1idWlsZHMvc3JjLW5vY29uZmxpY3Qva2V5YmluZGluZy1lbWFjcy5qcyJdLCJzb3VyY2VzQ29udGVudCI6WyJhY2UuZGVmaW5lKFwiYWNlL29jY3VyXCIsW1wicmVxdWlyZVwiLFwiZXhwb3J0c1wiLFwibW9kdWxlXCIsXCJhY2UvbGliL29vcFwiLFwiYWNlL3NlYXJjaFwiLFwiYWNlL2VkaXRfc2Vzc2lvblwiLFwiYWNlL3NlYXJjaF9oaWdobGlnaHRcIixcImFjZS9saWIvZG9tXCJdLCBmdW5jdGlvbihyZXF1aXJlLCBleHBvcnRzLCBtb2R1bGUpe1widXNlIHN0cmljdFwiO1xudmFyIF9fZXh0ZW5kcyA9ICh0aGlzICYmIHRoaXMuX19leHRlbmRzKSB8fCAoZnVuY3Rpb24gKCkge1xuICAgIHZhciBleHRlbmRTdGF0aWNzID0gZnVuY3Rpb24gKGQsIGIpIHtcbiAgICAgICAgZXh0ZW5kU3RhdGljcyA9IE9iamVjdC5zZXRQcm90b3R5cGVPZiB8fFxuICAgICAgICAgICAgKHsgX19wcm90b19fOiBbXSB9IGluc3RhbmNlb2YgQXJyYXkgJiYgZnVuY3Rpb24gKGQsIGIpIHsgZC5fX3Byb3RvX18gPSBiOyB9KSB8fFxuICAgICAgICAgICAgZnVuY3Rpb24gKGQsIGIpIHsgZm9yICh2YXIgcCBpbiBiKSBpZiAoT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eS5jYWxsKGIsIHApKSBkW3BdID0gYltwXTsgfTtcbiAgICAgICAgcmV0dXJuIGV4dGVuZFN0YXRpY3MoZCwgYik7XG4gICAgfTtcbiAgICByZXR1cm4gZnVuY3Rpb24gKGQsIGIpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBiICE9PSBcImZ1bmN0aW9uXCIgJiYgYiAhPT0gbnVsbClcbiAgICAgICAgICAgIHRocm93IG5ldyBUeXBlRXJyb3IoXCJDbGFzcyBleHRlbmRzIHZhbHVlIFwiICsgU3RyaW5nKGIpICsgXCIgaXMgbm90IGEgY29uc3RydWN0b3Igb3IgbnVsbFwiKTtcbiAgICAgICAgZXh0ZW5kU3RhdGljcyhkLCBiKTtcbiAgICAgICAgZnVuY3Rpb24gX18oKSB7IHRoaXMuY29uc3RydWN0b3IgPSBkOyB9XG4gICAgICAgIGQucHJvdG90eXBlID0gYiA9PT0gbnVsbCA/IE9iamVjdC5jcmVhdGUoYikgOiAoX18ucHJvdG90eXBlID0gYi5wcm90b3R5cGUsIG5ldyBfXygpKTtcbiAgICB9O1xufSkoKTtcbnZhciBvb3AgPSByZXF1aXJlKFwiLi9saWIvb29wXCIpO1xudmFyIFNlYXJjaCA9IHJlcXVpcmUoXCIuL3NlYXJjaFwiKS5TZWFyY2g7XG52YXIgRWRpdFNlc3Npb24gPSByZXF1aXJlKFwiLi9lZGl0X3Nlc3Npb25cIikuRWRpdFNlc3Npb247XG52YXIgU2VhcmNoSGlnaGxpZ2h0ID0gcmVxdWlyZShcIi4vc2VhcmNoX2hpZ2hsaWdodFwiKS5TZWFyY2hIaWdobGlnaHQ7XG52YXIgT2NjdXIgPSAvKiogQGNsYXNzICovIChmdW5jdGlvbiAoX3N1cGVyKSB7XG4gICAgX19leHRlbmRzKE9jY3VyLCBfc3VwZXIpO1xuICAgIGZ1bmN0aW9uIE9jY3VyKCkge1xuICAgICAgICByZXR1cm4gX3N1cGVyICE9PSBudWxsICYmIF9zdXBlci5hcHBseSh0aGlzLCBhcmd1bWVudHMpIHx8IHRoaXM7XG4gICAgfVxuICAgIE9jY3VyLnByb3RvdHlwZS5lbnRlciA9IGZ1bmN0aW9uIChlZGl0b3IsIG9wdGlvbnMpIHtcbiAgICAgICAgaWYgKCFvcHRpb25zLm5lZWRsZSlcbiAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgdmFyIHBvcyA9IGVkaXRvci5nZXRDdXJzb3JQb3NpdGlvbigpO1xuICAgICAgICB0aGlzLmRpc3BsYXlPY2N1ckNvbnRlbnQoZWRpdG9yLCBvcHRpb25zKTtcbiAgICAgICAgdmFyIHRyYW5zbGF0ZWRQb3MgPSB0aGlzLm9yaWdpbmFsVG9PY2N1clBvc2l0aW9uKGVkaXRvci5zZXNzaW9uLCBwb3MpO1xuICAgICAgICBlZGl0b3IubW92ZUN1cnNvclRvUG9zaXRpb24odHJhbnNsYXRlZFBvcyk7XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgIH07XG4gICAgT2NjdXIucHJvdG90eXBlLmV4aXQgPSBmdW5jdGlvbiAoZWRpdG9yLCBvcHRpb25zKSB7XG4gICAgICAgIHZhciBwb3MgPSBvcHRpb25zLnRyYW5zbGF0ZVBvc2l0aW9uICYmIGVkaXRvci5nZXRDdXJzb3JQb3NpdGlvbigpO1xuICAgICAgICB2YXIgdHJhbnNsYXRlZFBvcyA9IHBvcyAmJiB0aGlzLm9jY3VyVG9PcmlnaW5hbFBvc2l0aW9uKGVkaXRvci5zZXNzaW9uLCBwb3MpO1xuICAgICAgICB0aGlzLmRpc3BsYXlPcmlnaW5hbENvbnRlbnQoZWRpdG9yKTtcbiAgICAgICAgaWYgKHRyYW5zbGF0ZWRQb3MpXG4gICAgICAgICAgICBlZGl0b3IubW92ZUN1cnNvclRvUG9zaXRpb24odHJhbnNsYXRlZFBvcyk7XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgIH07XG4gICAgT2NjdXIucHJvdG90eXBlLmhpZ2hsaWdodCA9IGZ1bmN0aW9uIChzZXNzLCByZWdleHApIHtcbiAgICAgICAgdmFyIGhsID0gc2Vzcy4kb2NjdXJIaWdobGlnaHQgPSBzZXNzLiRvY2N1ckhpZ2hsaWdodCB8fCBzZXNzLmFkZER5bmFtaWNNYXJrZXIobmV3IFNlYXJjaEhpZ2hsaWdodChudWxsLCBcImFjZV9vY2N1ci1oaWdobGlnaHRcIiwgXCJ0ZXh0XCIpKTtcbiAgICAgICAgaGwuc2V0UmVnZXhwKHJlZ2V4cCk7XG4gICAgICAgIHNlc3MuX2VtaXQoXCJjaGFuZ2VCYWNrTWFya2VyXCIpOyAvLyBmb3JjZSBoaWdobGlnaHQgbGF5ZXIgcmVkcmF3XG4gICAgfTtcbiAgICBPY2N1ci5wcm90b3R5cGUuZGlzcGxheU9jY3VyQ29udGVudCA9IGZ1bmN0aW9uIChlZGl0b3IsIG9wdGlvbnMpIHtcbiAgICAgICAgdGhpcy4kb3JpZ2luYWxTZXNzaW9uID0gZWRpdG9yLnNlc3Npb247XG4gICAgICAgIHZhciBmb3VuZCA9IHRoaXMubWF0Y2hpbmdMaW5lcyhlZGl0b3Iuc2Vzc2lvbiwgb3B0aW9ucyk7XG4gICAgICAgIHZhciBsaW5lcyA9IGZvdW5kLm1hcChmdW5jdGlvbiAoZm91bmRMaW5lKSB7IHJldHVybiBmb3VuZExpbmUuY29udGVudDsgfSk7XG4gICAgICAgIHZhciBvY2N1clNlc3Npb24gPSBuZXcgRWRpdFNlc3Npb24obGluZXMuam9pbignXFxuJykpO1xuICAgICAgICBvY2N1clNlc3Npb24uJG9jY3VyID0gdGhpcztcbiAgICAgICAgb2NjdXJTZXNzaW9uLiRvY2N1ck1hdGNoaW5nTGluZXMgPSBmb3VuZDtcbiAgICAgICAgZWRpdG9yLnNldFNlc3Npb24ob2NjdXJTZXNzaW9uKTtcbiAgICAgICAgdGhpcy4kdXNlRW1hY3NTdHlsZUxpbmVTdGFydCA9IHRoaXMuJG9yaWdpbmFsU2Vzc2lvbi4kdXNlRW1hY3NTdHlsZUxpbmVTdGFydDtcbiAgICAgICAgb2NjdXJTZXNzaW9uLiR1c2VFbWFjc1N0eWxlTGluZVN0YXJ0ID0gdGhpcy4kdXNlRW1hY3NTdHlsZUxpbmVTdGFydDtcbiAgICAgICAgdGhpcy5oaWdobGlnaHQob2NjdXJTZXNzaW9uLCBvcHRpb25zLnJlKTtcbiAgICAgICAgb2NjdXJTZXNzaW9uLl9lbWl0KCdjaGFuZ2VCYWNrTWFya2VyJyk7XG4gICAgfTtcbiAgICBPY2N1ci5wcm90b3R5cGUuZGlzcGxheU9yaWdpbmFsQ29udGVudCA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgZWRpdG9yLnNldFNlc3Npb24odGhpcy4kb3JpZ2luYWxTZXNzaW9uKTtcbiAgICAgICAgdGhpcy4kb3JpZ2luYWxTZXNzaW9uLiR1c2VFbWFjc1N0eWxlTGluZVN0YXJ0ID0gdGhpcy4kdXNlRW1hY3NTdHlsZUxpbmVTdGFydDtcbiAgICB9O1xuICAgIE9jY3VyLnByb3RvdHlwZS5vcmlnaW5hbFRvT2NjdXJQb3NpdGlvbiA9IGZ1bmN0aW9uIChzZXNzaW9uLCBwb3MpIHtcbiAgICAgICAgdmFyIGxpbmVzID0gc2Vzc2lvbi4kb2NjdXJNYXRjaGluZ0xpbmVzO1xuICAgICAgICB2YXIgbnVsbFBvcyA9IHsgcm93OiAwLCBjb2x1bW46IDAgfTtcbiAgICAgICAgaWYgKCFsaW5lcylcbiAgICAgICAgICAgIHJldHVybiBudWxsUG9zO1xuICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGxpbmVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgICAgICBpZiAobGluZXNbaV0ucm93ID09PSBwb3Mucm93KVxuICAgICAgICAgICAgICAgIHJldHVybiB7IHJvdzogaSwgY29sdW1uOiBwb3MuY29sdW1uIH07XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG51bGxQb3M7XG4gICAgfTtcbiAgICBPY2N1ci5wcm90b3R5cGUub2NjdXJUb09yaWdpbmFsUG9zaXRpb24gPSBmdW5jdGlvbiAoc2Vzc2lvbiwgcG9zKSB7XG4gICAgICAgIHZhciBsaW5lcyA9IHNlc3Npb24uJG9jY3VyTWF0Y2hpbmdMaW5lcztcbiAgICAgICAgaWYgKCFsaW5lcyB8fCAhbGluZXNbcG9zLnJvd10pXG4gICAgICAgICAgICByZXR1cm4gcG9zO1xuICAgICAgICByZXR1cm4geyByb3c6IGxpbmVzW3Bvcy5yb3ddLnJvdywgY29sdW1uOiBwb3MuY29sdW1uIH07XG4gICAgfTtcbiAgICBPY2N1ci5wcm90b3R5cGUubWF0Y2hpbmdMaW5lcyA9IGZ1bmN0aW9uIChzZXNzaW9uLCBvcHRpb25zKSB7XG4gICAgICAgIG9wdGlvbnMgPSBvb3AubWl4aW4oe30sIG9wdGlvbnMpO1xuICAgICAgICBpZiAoIXNlc3Npb24gfHwgIW9wdGlvbnMubmVlZGxlKVxuICAgICAgICAgICAgcmV0dXJuIFtdO1xuICAgICAgICB2YXIgc2VhcmNoID0gbmV3IFNlYXJjaCgpO1xuICAgICAgICBzZWFyY2guc2V0KG9wdGlvbnMpO1xuICAgICAgICByZXR1cm4gc2VhcmNoLmZpbmRBbGwoc2Vzc2lvbikucmVkdWNlKGZ1bmN0aW9uIChsaW5lcywgcmFuZ2UpIHtcbiAgICAgICAgICAgIHZhciByb3cgPSByYW5nZS5zdGFydC5yb3c7XG4gICAgICAgICAgICB2YXIgbGFzdCA9IGxpbmVzW2xpbmVzLmxlbmd0aCAtIDFdO1xuICAgICAgICAgICAgcmV0dXJuIGxhc3QgJiYgbGFzdC5yb3cgPT09IHJvdyA/XG4gICAgICAgICAgICAgICAgbGluZXMgOlxuICAgICAgICAgICAgICAgIGxpbmVzLmNvbmNhdCh7IHJvdzogcm93LCBjb250ZW50OiBzZXNzaW9uLmdldExpbmUocm93KSB9KTtcbiAgICAgICAgfSwgW10pO1xuICAgIH07XG4gICAgcmV0dXJuIE9jY3VyO1xufShTZWFyY2gpKTtcbnZhciBkb20gPSByZXF1aXJlKCcuL2xpYi9kb20nKTtcbmRvbS5pbXBvcnRDc3NTdHJpbmcoXCIuYWNlX29jY3VyLWhpZ2hsaWdodCB7XFxuXFxcbiAgICBib3JkZXItcmFkaXVzOiA0cHg7XFxuXFxcbiAgICBiYWNrZ3JvdW5kLWNvbG9yOiByZ2JhKDg3LCAyNTUsIDgsIDAuMjUpO1xcblxcXG4gICAgcG9zaXRpb246IGFic29sdXRlO1xcblxcXG4gICAgei1pbmRleDogNDtcXG5cXFxuICAgIGJveC1zaXppbmc6IGJvcmRlci1ib3g7XFxuXFxcbiAgICBib3gtc2hhZG93OiAwIDAgNHB4IHJnYig5MSwgMjU1LCA1MCk7XFxuXFxcbn1cXG5cXFxuLmFjZV9kYXJrIC5hY2Vfb2NjdXItaGlnaGxpZ2h0IHtcXG5cXFxuICAgIGJhY2tncm91bmQtY29sb3I6IHJnYig4MCwgMTQwLCA4NSk7XFxuXFxcbiAgICBib3gtc2hhZG93OiAwIDAgNHB4IHJnYig2MCwgMTIwLCA3MCk7XFxuXFxcbn1cXG5cIiwgXCJpbmNyZW1lbnRhbC1vY2N1ci1oaWdobGlnaHRpbmdcIiwgZmFsc2UpO1xuZXhwb3J0cy5PY2N1ciA9IE9jY3VyO1xuXG59KTtcblxuYWNlLmRlZmluZShcImFjZS9jb21tYW5kcy9vY2N1cl9jb21tYW5kc1wiLFtcInJlcXVpcmVcIixcImV4cG9ydHNcIixcIm1vZHVsZVwiLFwiYWNlL2NvbmZpZ1wiLFwiYWNlL29jY3VyXCIsXCJhY2Uva2V5Ym9hcmQvaGFzaF9oYW5kbGVyXCIsXCJhY2UvbGliL29vcFwiXSwgZnVuY3Rpb24ocmVxdWlyZSwgZXhwb3J0cywgbW9kdWxlKXt2YXIgY29uZmlnID0gcmVxdWlyZShcIi4uL2NvbmZpZ1wiKSwgT2NjdXIgPSByZXF1aXJlKFwiLi4vb2NjdXJcIikuT2NjdXI7XG52YXIgb2NjdXJTdGFydENvbW1hbmQgPSB7XG4gICAgbmFtZTogXCJvY2N1clwiLFxuICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IsIG9wdGlvbnMpIHtcbiAgICAgICAgdmFyIGFscmVhZHlJbk9jY3VyID0gISFlZGl0b3Iuc2Vzc2lvbi4kb2NjdXI7XG4gICAgICAgIHZhciBvY2N1clNlc3Npb25BY3RpdmUgPSBuZXcgT2NjdXIoKS5lbnRlcihlZGl0b3IsIG9wdGlvbnMpO1xuICAgICAgICBpZiAob2NjdXJTZXNzaW9uQWN0aXZlICYmICFhbHJlYWR5SW5PY2N1cilcbiAgICAgICAgICAgIE9jY3VyS2V5Ym9hcmRIYW5kbGVyLmluc3RhbGxJbihlZGl0b3IpO1xuICAgIH0sXG4gICAgcmVhZE9ubHk6IHRydWVcbn07XG52YXIgb2NjdXJDb21tYW5kcyA9IFt7XG4gICAgICAgIG5hbWU6IFwib2NjdXJleGl0XCIsXG4gICAgICAgIGJpbmRLZXk6ICdlc2N8Q3RybC1HJyxcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgdmFyIG9jY3VyID0gZWRpdG9yLnNlc3Npb24uJG9jY3VyO1xuICAgICAgICAgICAgaWYgKCFvY2N1cilcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICBvY2N1ci5leGl0KGVkaXRvciwge30pO1xuICAgICAgICAgICAgaWYgKCFlZGl0b3Iuc2Vzc2lvbi4kb2NjdXIpXG4gICAgICAgICAgICAgICAgT2NjdXJLZXlib2FyZEhhbmRsZXIudW5pbnN0YWxsRnJvbShlZGl0b3IpO1xuICAgICAgICB9LFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJvY2N1cmFjY2VwdFwiLFxuICAgICAgICBiaW5kS2V5OiAnZW50ZXInLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICB2YXIgb2NjdXIgPSBlZGl0b3Iuc2Vzc2lvbi4kb2NjdXI7XG4gICAgICAgICAgICBpZiAoIW9jY3VyKVxuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIG9jY3VyLmV4aXQoZWRpdG9yLCB7IHRyYW5zbGF0ZVBvc2l0aW9uOiB0cnVlIH0pO1xuICAgICAgICAgICAgaWYgKCFlZGl0b3Iuc2Vzc2lvbi4kb2NjdXIpXG4gICAgICAgICAgICAgICAgT2NjdXJLZXlib2FyZEhhbmRsZXIudW5pbnN0YWxsRnJvbShlZGl0b3IpO1xuICAgICAgICB9LFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH1dO1xudmFyIEhhc2hIYW5kbGVyID0gcmVxdWlyZShcIi4uL2tleWJvYXJkL2hhc2hfaGFuZGxlclwiKS5IYXNoSGFuZGxlcjtcbnZhciBvb3AgPSByZXF1aXJlKFwiLi4vbGliL29vcFwiKTtcbmZ1bmN0aW9uIE9jY3VyS2V5Ym9hcmRIYW5kbGVyKCkgeyB9XG5vb3AuaW5oZXJpdHMoT2NjdXJLZXlib2FyZEhhbmRsZXIsIEhhc2hIYW5kbGVyKTtcbihmdW5jdGlvbiAoKSB7XG4gICAgdGhpcy5pc09jY3VySGFuZGxlciA9IHRydWU7XG4gICAgdGhpcy5hdHRhY2ggPSBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgIEhhc2hIYW5kbGVyLmNhbGwodGhpcywgb2NjdXJDb21tYW5kcywgZWRpdG9yLmNvbW1hbmRzLnBsYXRmb3JtKTtcbiAgICAgICAgdGhpcy4kZWRpdG9yID0gZWRpdG9yO1xuICAgIH07XG4gICAgdmFyIGhhbmRsZUtleWJvYXJkJHN1cGVyID0gdGhpcy5oYW5kbGVLZXlib2FyZDtcbiAgICB0aGlzLmhhbmRsZUtleWJvYXJkID0gZnVuY3Rpb24gKGRhdGEsIGhhc2hJZCwga2V5LCBrZXlDb2RlKSB7XG4gICAgICAgIHZhciBjbWQgPSBoYW5kbGVLZXlib2FyZCRzdXBlci5jYWxsKHRoaXMsIGRhdGEsIGhhc2hJZCwga2V5LCBrZXlDb2RlKTtcbiAgICAgICAgcmV0dXJuIChjbWQgJiYgY21kLmNvbW1hbmQpID8gY21kIDogdW5kZWZpbmVkO1xuICAgIH07XG59KS5jYWxsKE9jY3VyS2V5Ym9hcmRIYW5kbGVyLnByb3RvdHlwZSk7XG5PY2N1cktleWJvYXJkSGFuZGxlci5pbnN0YWxsSW4gPSBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgdmFyIGhhbmRsZXIgPSBuZXcgdGhpcygpO1xuICAgIGVkaXRvci5rZXlCaW5kaW5nLmFkZEtleWJvYXJkSGFuZGxlcihoYW5kbGVyKTtcbiAgICBlZGl0b3IuY29tbWFuZHMuYWRkQ29tbWFuZHMob2NjdXJDb21tYW5kcyk7XG59O1xuT2NjdXJLZXlib2FyZEhhbmRsZXIudW5pbnN0YWxsRnJvbSA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICBlZGl0b3IuY29tbWFuZHMucmVtb3ZlQ29tbWFuZHMob2NjdXJDb21tYW5kcyk7XG4gICAgdmFyIGhhbmRsZXIgPSBlZGl0b3IuZ2V0S2V5Ym9hcmRIYW5kbGVyKCk7XG4gICAgaWYgKGhhbmRsZXIuaXNPY2N1ckhhbmRsZXIpXG4gICAgICAgIGVkaXRvci5rZXlCaW5kaW5nLnJlbW92ZUtleWJvYXJkSGFuZGxlcihoYW5kbGVyKTtcbn07XG5leHBvcnRzLm9jY3VyU3RhcnRDb21tYW5kID0gb2NjdXJTdGFydENvbW1hbmQ7XG5cbn0pO1xuXG5hY2UuZGVmaW5lKFwiYWNlL2NvbW1hbmRzL2luY3JlbWVudGFsX3NlYXJjaF9jb21tYW5kc1wiLFtcInJlcXVpcmVcIixcImV4cG9ydHNcIixcIm1vZHVsZVwiLFwiYWNlL2NvbmZpZ1wiLFwiYWNlL2xpYi9vb3BcIixcImFjZS9rZXlib2FyZC9oYXNoX2hhbmRsZXJcIixcImFjZS9jb21tYW5kcy9vY2N1cl9jb21tYW5kc1wiXSwgZnVuY3Rpb24ocmVxdWlyZSwgZXhwb3J0cywgbW9kdWxlKXt2YXIgY29uZmlnID0gcmVxdWlyZShcIi4uL2NvbmZpZ1wiKTtcbnZhciBvb3AgPSByZXF1aXJlKFwiLi4vbGliL29vcFwiKTtcbnZhciBIYXNoSGFuZGxlciA9IHJlcXVpcmUoXCIuLi9rZXlib2FyZC9oYXNoX2hhbmRsZXJcIikuSGFzaEhhbmRsZXI7XG52YXIgb2NjdXJTdGFydENvbW1hbmQgPSByZXF1aXJlKFwiLi9vY2N1cl9jb21tYW5kc1wiKS5vY2N1clN0YXJ0Q29tbWFuZDtcbmV4cG9ydHMuaVNlYXJjaFN0YXJ0Q29tbWFuZHMgPSBbe1xuICAgICAgICBuYW1lOiBcImlTZWFyY2hcIixcbiAgICAgICAgYmluZEtleTogeyB3aW46IFwiQ3RybC1GXCIsIG1hYzogXCJDb21tYW5kLUZcIiB9LFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yLCBvcHRpb25zKSB7XG4gICAgICAgICAgICBjb25maWcubG9hZE1vZHVsZShbXCJjb3JlXCIsIFwiYWNlL2luY3JlbWVudGFsX3NlYXJjaFwiXSwgZnVuY3Rpb24gKGUpIHtcbiAgICAgICAgICAgICAgICB2YXIgaVNlYXJjaCA9IGUuaVNlYXJjaCA9IGUuaVNlYXJjaCB8fCBuZXcgZS5JbmNyZW1lbnRhbFNlYXJjaCgpO1xuICAgICAgICAgICAgICAgIGlTZWFyY2guYWN0aXZhdGUoZWRpdG9yLCBvcHRpb25zLmJhY2t3YXJkcyk7XG4gICAgICAgICAgICAgICAgaWYgKG9wdGlvbnMuanVtcFRvRmlyc3RNYXRjaClcbiAgICAgICAgICAgICAgICAgICAgaVNlYXJjaC5uZXh0KG9wdGlvbnMpO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgIH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcImlTZWFyY2hCYWNrd2FyZHNcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvciwganVtcFRvTmV4dCkgeyBlZGl0b3IuZXhlY0NvbW1hbmQoJ2lTZWFyY2gnLCB7IGJhY2t3YXJkczogdHJ1ZSB9KTsgfSxcbiAgICAgICAgcmVhZE9ubHk6IHRydWVcbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwiaVNlYXJjaEFuZEdvXCIsXG4gICAgICAgIGJpbmRLZXk6IHsgd2luOiBcIkN0cmwtS1wiLCBtYWM6IFwiQ29tbWFuZC1HXCIgfSxcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvciwganVtcFRvTmV4dCkgeyBlZGl0b3IuZXhlY0NvbW1hbmQoJ2lTZWFyY2gnLCB7IGp1bXBUb0ZpcnN0TWF0Y2g6IHRydWUsIHVzZUN1cnJlbnRPclByZXZTZWFyY2g6IHRydWUgfSk7IH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcImlTZWFyY2hCYWNrd2FyZHNBbmRHb1wiLFxuICAgICAgICBiaW5kS2V5OiB7IHdpbjogXCJDdHJsLVNoaWZ0LUtcIiwgbWFjOiBcIkNvbW1hbmQtU2hpZnQtR1wiIH0sXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHsgZWRpdG9yLmV4ZWNDb21tYW5kKCdpU2VhcmNoJywgeyBqdW1wVG9GaXJzdE1hdGNoOiB0cnVlLCBiYWNrd2FyZHM6IHRydWUsIHVzZUN1cnJlbnRPclByZXZTZWFyY2g6IHRydWUgfSk7IH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfV07XG5leHBvcnRzLmlTZWFyY2hDb21tYW5kcyA9IFt7XG4gICAgICAgIG5hbWU6IFwicmVzdGFydFNlYXJjaFwiLFxuICAgICAgICBiaW5kS2V5OiB7IHdpbjogXCJDdHJsLUZcIiwgbWFjOiBcIkNvbW1hbmQtRlwiIH0sXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7XG4gICAgICAgICAgICBpU2VhcmNoLmNhbmNlbFNlYXJjaCh0cnVlKTtcbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJzZWFyY2hGb3J3YXJkXCIsXG4gICAgICAgIGJpbmRLZXk6IHsgd2luOiBcIkN0cmwtU3xDdHJsLUtcIiwgbWFjOiBcIkN0cmwtU3xDb21tYW5kLUdcIiB9LFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCwgb3B0aW9ucykge1xuICAgICAgICAgICAgb3B0aW9ucy51c2VDdXJyZW50T3JQcmV2U2VhcmNoID0gdHJ1ZTtcbiAgICAgICAgICAgIGlTZWFyY2gubmV4dChvcHRpb25zKTtcbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJzZWFyY2hCYWNrd2FyZFwiLFxuICAgICAgICBiaW5kS2V5OiB7IHdpbjogXCJDdHJsLVJ8Q3RybC1TaGlmdC1LXCIsIG1hYzogXCJDdHJsLVJ8Q29tbWFuZC1TaGlmdC1HXCIgfSxcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGlTZWFyY2gsIG9wdGlvbnMpIHtcbiAgICAgICAgICAgIG9wdGlvbnMudXNlQ3VycmVudE9yUHJldlNlYXJjaCA9IHRydWU7XG4gICAgICAgICAgICBvcHRpb25zLmJhY2t3YXJkcyA9IHRydWU7XG4gICAgICAgICAgICBpU2VhcmNoLm5leHQob3B0aW9ucyk7XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwiZXh0ZW5kU2VhcmNoVGVybVwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCwgc3RyaW5nKSB7XG4gICAgICAgICAgICBpU2VhcmNoLmFkZFN0cmluZyhzdHJpbmcpO1xuICAgICAgICB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcImV4dGVuZFNlYXJjaFRlcm1TcGFjZVwiLFxuICAgICAgICBiaW5kS2V5OiBcInNwYWNlXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7IGlTZWFyY2guYWRkU3RyaW5nKCcgJyk7IH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwic2hyaW5rU2VhcmNoVGVybVwiLFxuICAgICAgICBiaW5kS2V5OiBcImJhY2tzcGFjZVwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCkge1xuICAgICAgICAgICAgaVNlYXJjaC5yZW1vdmVDaGFyKCk7XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6ICdjb25maXJtU2VhcmNoJyxcbiAgICAgICAgYmluZEtleTogJ3JldHVybicsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7IGlTZWFyY2guZGVhY3RpdmF0ZSgpOyB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiAnY2FuY2VsU2VhcmNoJyxcbiAgICAgICAgYmluZEtleTogJ2VzY3xDdHJsLUcnLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCkgeyBpU2VhcmNoLmRlYWN0aXZhdGUodHJ1ZSk7IH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6ICdvY2N1cmlzZWFyY2gnLFxuICAgICAgICBiaW5kS2V5OiAnQ3RybC1PJyxcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGlTZWFyY2gpIHtcbiAgICAgICAgICAgIHZhciBvcHRpb25zID0gb29wLm1peGluKHt9LCBpU2VhcmNoLiRvcHRpb25zKTtcbiAgICAgICAgICAgIGlTZWFyY2guZGVhY3RpdmF0ZSgpO1xuICAgICAgICAgICAgb2NjdXJTdGFydENvbW1hbmQuZXhlYyhpU2VhcmNoLiRlZGl0b3IsIG9wdGlvbnMpO1xuICAgICAgICB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcInlhbmtOZXh0V29yZFwiLFxuICAgICAgICBiaW5kS2V5OiBcIkN0cmwtd1wiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCkge1xuICAgICAgICAgICAgdmFyIGVkID0gaVNlYXJjaC4kZWRpdG9yLCByYW5nZSA9IGVkLnNlbGVjdGlvbi5nZXRSYW5nZU9mTW92ZW1lbnRzKGZ1bmN0aW9uIChzZWwpIHsgc2VsLm1vdmVDdXJzb3JXb3JkUmlnaHQoKTsgfSksIHN0cmluZyA9IGVkLnNlc3Npb24uZ2V0VGV4dFJhbmdlKHJhbmdlKTtcbiAgICAgICAgICAgIGlTZWFyY2guYWRkU3RyaW5nKHN0cmluZyk7XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwieWFua05leHRDaGFyXCIsXG4gICAgICAgIGJpbmRLZXk6IFwiQ3RybC1BbHQteVwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoaVNlYXJjaCkge1xuICAgICAgICAgICAgdmFyIGVkID0gaVNlYXJjaC4kZWRpdG9yLCByYW5nZSA9IGVkLnNlbGVjdGlvbi5nZXRSYW5nZU9mTW92ZW1lbnRzKGZ1bmN0aW9uIChzZWwpIHsgc2VsLm1vdmVDdXJzb3JSaWdodCgpOyB9KSwgc3RyaW5nID0gZWQuc2Vzc2lvbi5nZXRUZXh0UmFuZ2UocmFuZ2UpO1xuICAgICAgICAgICAgaVNlYXJjaC5hZGRTdHJpbmcoc3RyaW5nKTtcbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogJ3JlY2VudGVyVG9wQm90dG9tJyxcbiAgICAgICAgYmluZEtleTogJ0N0cmwtbCcsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7IGlTZWFyY2guJGVkaXRvci5leGVjQ29tbWFuZCgncmVjZW50ZXJUb3BCb3R0b20nKTsgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogJ3NlbGVjdEFsbE1hdGNoZXMnLFxuICAgICAgICBiaW5kS2V5OiAnQ3RybC1zcGFjZScsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7XG4gICAgICAgICAgICB2YXIgZWQgPSBpU2VhcmNoLiRlZGl0b3IsIGhsID0gZWQuc2Vzc2lvbi4kaXNlYXJjaEhpZ2hsaWdodCwgcmFuZ2VzID0gaGwgJiYgaGwuY2FjaGUgPyBobC5jYWNoZVxuICAgICAgICAgICAgICAgIC5yZWR1Y2UoZnVuY3Rpb24gKHJhbmdlcywgZWEpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gcmFuZ2VzLmNvbmNhdChlYSA/IGVhIDogW10pO1xuICAgICAgICAgICAgfSwgW10pIDogW107XG4gICAgICAgICAgICBpU2VhcmNoLmRlYWN0aXZhdGUoZmFsc2UpO1xuICAgICAgICAgICAgcmFuZ2VzLmZvckVhY2goZWQuc2VsZWN0aW9uLmFkZFJhbmdlLmJpbmQoZWQuc2VsZWN0aW9uKSk7XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6ICdzZWFyY2hBc1JlZ0V4cCcsXG4gICAgICAgIGJpbmRLZXk6ICdBbHQtcicsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChpU2VhcmNoKSB7XG4gICAgICAgICAgICBpU2VhcmNoLmNvbnZlcnROZWVkbGVUb1JlZ0V4cCgpO1xuICAgICAgICB9XG4gICAgfV0ubWFwKGZ1bmN0aW9uIChjbWQpIHtcbiAgICBjbWQucmVhZE9ubHkgPSB0cnVlO1xuICAgIGNtZC5pc0luY3JlbWVudGFsU2VhcmNoQ29tbWFuZCA9IHRydWU7XG4gICAgY21kLnNjcm9sbEludG9WaWV3ID0gXCJhbmltYXRlLWN1cnNvclwiO1xuICAgIHJldHVybiBjbWQ7XG59KTtcbmZ1bmN0aW9uIEluY3JlbWVudGFsU2VhcmNoS2V5Ym9hcmRIYW5kbGVyKGlTZWFyY2gpIHtcbiAgICB0aGlzLiRpU2VhcmNoID0gaVNlYXJjaDtcbn1cbm9vcC5pbmhlcml0cyhJbmNyZW1lbnRhbFNlYXJjaEtleWJvYXJkSGFuZGxlciwgSGFzaEhhbmRsZXIpO1xuKGZ1bmN0aW9uICgpIHtcbiAgICB0aGlzLmF0dGFjaCA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgdmFyIGlTZWFyY2ggPSB0aGlzLiRpU2VhcmNoO1xuICAgICAgICBIYXNoSGFuZGxlci5jYWxsKHRoaXMsIGV4cG9ydHMuaVNlYXJjaENvbW1hbmRzLCBlZGl0b3IuY29tbWFuZHMucGxhdGZvcm0pO1xuICAgICAgICB0aGlzLiRjb21tYW5kRXhlY0hhbmRsZXIgPSBlZGl0b3IuY29tbWFuZHMub24oJ2V4ZWMnLCBmdW5jdGlvbiAoZSkge1xuICAgICAgICAgICAgaWYgKCFlLmNvbW1hbmQuaXNJbmNyZW1lbnRhbFNlYXJjaENvbW1hbmQpXG4gICAgICAgICAgICAgICAgcmV0dXJuIGlTZWFyY2guZGVhY3RpdmF0ZSgpO1xuICAgICAgICAgICAgZS5zdG9wUHJvcGFnYXRpb24oKTtcbiAgICAgICAgICAgIGUucHJldmVudERlZmF1bHQoKTtcbiAgICAgICAgICAgIHZhciBzY3JvbGxUb3AgPSBlZGl0b3Iuc2Vzc2lvbi5nZXRTY3JvbGxUb3AoKTtcbiAgICAgICAgICAgIHZhciByZXN1bHQgPSBlLmNvbW1hbmQuZXhlYyhpU2VhcmNoLCBlLmFyZ3MgfHwge30pO1xuICAgICAgICAgICAgZWRpdG9yLnJlbmRlcmVyLnNjcm9sbEN1cnNvckludG9WaWV3KG51bGwsIDAuNSk7XG4gICAgICAgICAgICBlZGl0b3IucmVuZGVyZXIuYW5pbWF0ZVNjcm9sbGluZyhzY3JvbGxUb3ApO1xuICAgICAgICAgICAgcmV0dXJuIHJlc3VsdDtcbiAgICAgICAgfSk7XG4gICAgfTtcbiAgICB0aGlzLmRldGFjaCA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgaWYgKCF0aGlzLiRjb21tYW5kRXhlY0hhbmRsZXIpXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIGVkaXRvci5jb21tYW5kcy5vZmYoJ2V4ZWMnLCB0aGlzLiRjb21tYW5kRXhlY0hhbmRsZXIpO1xuICAgICAgICBkZWxldGUgdGhpcy4kY29tbWFuZEV4ZWNIYW5kbGVyO1xuICAgIH07XG4gICAgdmFyIGhhbmRsZUtleWJvYXJkJHN1cGVyID0gdGhpcy5oYW5kbGVLZXlib2FyZDtcbiAgICB0aGlzLmhhbmRsZUtleWJvYXJkID0gZnVuY3Rpb24gKGRhdGEsIGhhc2hJZCwga2V5LCBrZXlDb2RlKSB7XG4gICAgICAgIGlmICgoKGhhc2hJZCA9PT0gMSAvKmN0cmwqLyB8fCBoYXNoSWQgPT09IDggLypjb21tYW5kKi8pICYmIGtleSA9PT0gJ3YnKVxuICAgICAgICAgICAgfHwgKGhhc2hJZCA9PT0gMSAvKmN0cmwqLyAmJiBrZXkgPT09ICd5JykpXG4gICAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgdmFyIGNtZCA9IGhhbmRsZUtleWJvYXJkJHN1cGVyLmNhbGwodGhpcywgZGF0YSwgaGFzaElkLCBrZXksIGtleUNvZGUpO1xuICAgICAgICBpZiAoY21kICYmIGNtZC5jb21tYW5kKSB7XG4gICAgICAgICAgICByZXR1cm4gY21kO1xuICAgICAgICB9XG4gICAgICAgIGlmIChoYXNoSWQgPT0gLTEpIHtcbiAgICAgICAgICAgIHZhciBleHRlbmRDbWQgPSB0aGlzLmNvbW1hbmRzLmV4dGVuZFNlYXJjaFRlcm07XG4gICAgICAgICAgICBpZiAoZXh0ZW5kQ21kKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuIHsgY29tbWFuZDogZXh0ZW5kQ21kLCBhcmdzOiBrZXkgfTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgfTtcbn0pLmNhbGwoSW5jcmVtZW50YWxTZWFyY2hLZXlib2FyZEhhbmRsZXIucHJvdG90eXBlKTtcbmV4cG9ydHMuSW5jcmVtZW50YWxTZWFyY2hLZXlib2FyZEhhbmRsZXIgPSBJbmNyZW1lbnRhbFNlYXJjaEtleWJvYXJkSGFuZGxlcjtcblxufSk7XG5cbmFjZS5kZWZpbmUoXCJhY2UvaW5jcmVtZW50YWxfc2VhcmNoXCIsW1wicmVxdWlyZVwiLFwiZXhwb3J0c1wiLFwibW9kdWxlXCIsXCJhY2UvcmFuZ2VcIixcImFjZS9zZWFyY2hcIixcImFjZS9zZWFyY2hfaGlnaGxpZ2h0XCIsXCJhY2UvY29tbWFuZHMvaW5jcmVtZW50YWxfc2VhcmNoX2NvbW1hbmRzXCIsXCJhY2UvbGliL2RvbVwiLFwiYWNlL2NvbW1hbmRzL2NvbW1hbmRfbWFuYWdlclwiLFwiYWNlL2VkaXRvclwiLFwiYWNlL2NvbmZpZ1wiXSwgZnVuY3Rpb24ocmVxdWlyZSwgZXhwb3J0cywgbW9kdWxlKXtcInVzZSBzdHJpY3RcIjtcbnZhciBfX2V4dGVuZHMgPSAodGhpcyAmJiB0aGlzLl9fZXh0ZW5kcykgfHwgKGZ1bmN0aW9uICgpIHtcbiAgICB2YXIgZXh0ZW5kU3RhdGljcyA9IGZ1bmN0aW9uIChkLCBiKSB7XG4gICAgICAgIGV4dGVuZFN0YXRpY3MgPSBPYmplY3Quc2V0UHJvdG90eXBlT2YgfHxcbiAgICAgICAgICAgICh7IF9fcHJvdG9fXzogW10gfSBpbnN0YW5jZW9mIEFycmF5ICYmIGZ1bmN0aW9uIChkLCBiKSB7IGQuX19wcm90b19fID0gYjsgfSkgfHxcbiAgICAgICAgICAgIGZ1bmN0aW9uIChkLCBiKSB7IGZvciAodmFyIHAgaW4gYikgaWYgKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChiLCBwKSkgZFtwXSA9IGJbcF07IH07XG4gICAgICAgIHJldHVybiBleHRlbmRTdGF0aWNzKGQsIGIpO1xuICAgIH07XG4gICAgcmV0dXJuIGZ1bmN0aW9uIChkLCBiKSB7XG4gICAgICAgIGlmICh0eXBlb2YgYiAhPT0gXCJmdW5jdGlvblwiICYmIGIgIT09IG51bGwpXG4gICAgICAgICAgICB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2xhc3MgZXh0ZW5kcyB2YWx1ZSBcIiArIFN0cmluZyhiKSArIFwiIGlzIG5vdCBhIGNvbnN0cnVjdG9yIG9yIG51bGxcIik7XG4gICAgICAgIGV4dGVuZFN0YXRpY3MoZCwgYik7XG4gICAgICAgIGZ1bmN0aW9uIF9fKCkgeyB0aGlzLmNvbnN0cnVjdG9yID0gZDsgfVxuICAgICAgICBkLnByb3RvdHlwZSA9IGIgPT09IG51bGwgPyBPYmplY3QuY3JlYXRlKGIpIDogKF9fLnByb3RvdHlwZSA9IGIucHJvdG90eXBlLCBuZXcgX18oKSk7XG4gICAgfTtcbn0pKCk7XG52YXIgUmFuZ2UgPSByZXF1aXJlKFwiLi9yYW5nZVwiKS5SYW5nZTtcbnZhciBTZWFyY2ggPSByZXF1aXJlKFwiLi9zZWFyY2hcIikuU2VhcmNoO1xudmFyIFNlYXJjaEhpZ2hsaWdodCA9IHJlcXVpcmUoXCIuL3NlYXJjaF9oaWdobGlnaHRcIikuU2VhcmNoSGlnaGxpZ2h0O1xudmFyIGlTZWFyY2hDb21tYW5kTW9kdWxlID0gcmVxdWlyZShcIi4vY29tbWFuZHMvaW5jcmVtZW50YWxfc2VhcmNoX2NvbW1hbmRzXCIpO1xudmFyIElTZWFyY2hLYmQgPSBpU2VhcmNoQ29tbWFuZE1vZHVsZS5JbmNyZW1lbnRhbFNlYXJjaEtleWJvYXJkSGFuZGxlcjtcbmZ1bmN0aW9uIGlzUmVnRXhwKG9iaikge1xuICAgIHJldHVybiBvYmogaW5zdGFuY2VvZiBSZWdFeHA7XG59XG5mdW5jdGlvbiByZWdFeHBUb09iamVjdChyZSkge1xuICAgIHZhciBzdHJpbmcgPSBTdHJpbmcocmUpLCBzdGFydCA9IHN0cmluZy5pbmRleE9mKCcvJyksIGZsYWdTdGFydCA9IHN0cmluZy5sYXN0SW5kZXhPZignLycpO1xuICAgIHJldHVybiB7XG4gICAgICAgIGV4cHJlc3Npb246IHN0cmluZy5zbGljZShzdGFydCArIDEsIGZsYWdTdGFydCksXG4gICAgICAgIGZsYWdzOiBzdHJpbmcuc2xpY2UoZmxhZ1N0YXJ0ICsgMSlcbiAgICB9O1xufVxuZnVuY3Rpb24gc3RyaW5nVG9SZWdFeHAoc3RyaW5nLCBmbGFncykge1xuICAgIHRyeSB7XG4gICAgICAgIHJldHVybiBuZXcgUmVnRXhwKHN0cmluZywgZmxhZ3MpO1xuICAgIH1cbiAgICBjYXRjaCAoZSkge1xuICAgICAgICByZXR1cm4gc3RyaW5nO1xuICAgIH1cbn1cbmZ1bmN0aW9uIG9iamVjdFRvUmVnRXhwKG9iaikge1xuICAgIHJldHVybiBzdHJpbmdUb1JlZ0V4cChvYmouZXhwcmVzc2lvbiwgb2JqLmZsYWdzKTtcbn1cbnZhciBJbmNyZW1lbnRhbFNlYXJjaCA9IC8qKiBAY2xhc3MgKi8gKGZ1bmN0aW9uIChfc3VwZXIpIHtcbiAgICBfX2V4dGVuZHMoSW5jcmVtZW50YWxTZWFyY2gsIF9zdXBlcik7XG4gICAgZnVuY3Rpb24gSW5jcmVtZW50YWxTZWFyY2goKSB7XG4gICAgICAgIHZhciBfdGhpcyA9IF9zdXBlci5jYWxsKHRoaXMpIHx8IHRoaXM7XG4gICAgICAgIF90aGlzLiRvcHRpb25zID0geyB3cmFwOiBmYWxzZSwgc2tpcEN1cnJlbnQ6IGZhbHNlIH07XG4gICAgICAgIF90aGlzLiRrZXlib2FyZEhhbmRsZXIgPSBuZXcgSVNlYXJjaEtiZChfdGhpcyk7XG4gICAgICAgIHJldHVybiBfdGhpcztcbiAgICB9XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLmFjdGl2YXRlID0gZnVuY3Rpb24gKGVkaXRvciwgYmFja3dhcmRzKSB7XG4gICAgICAgIHRoaXMuJGVkaXRvciA9IGVkaXRvcjtcbiAgICAgICAgdGhpcy4kc3RhcnRQb3MgPSB0aGlzLiRjdXJyZW50UG9zID0gZWRpdG9yLmdldEN1cnNvclBvc2l0aW9uKCk7XG4gICAgICAgIHRoaXMuJG9wdGlvbnMubmVlZGxlID0gJyc7XG4gICAgICAgIHRoaXMuJG9wdGlvbnMuYmFja3dhcmRzID0gYmFja3dhcmRzO1xuICAgICAgICBlZGl0b3Iua2V5QmluZGluZy5hZGRLZXlib2FyZEhhbmRsZXIodGhpcy4ka2V5Ym9hcmRIYW5kbGVyKTtcbiAgICAgICAgdGhpcy4kb3JpZ2luYWxFZGl0b3JPblBhc3RlID0gZWRpdG9yLm9uUGFzdGU7XG4gICAgICAgIGVkaXRvci5vblBhc3RlID0gdGhpcy5vblBhc3RlLmJpbmQodGhpcyk7XG4gICAgICAgIHRoaXMuJG1vdXNlZG93bkhhbmRsZXIgPSBlZGl0b3Iub24oJ21vdXNlZG93bicsIHRoaXMub25Nb3VzZURvd24uYmluZCh0aGlzKSk7XG4gICAgICAgIHRoaXMuc2VsZWN0aW9uRml4KGVkaXRvcik7XG4gICAgICAgIHRoaXMuc3RhdHVzTWVzc2FnZSh0cnVlKTtcbiAgICB9O1xuICAgIEluY3JlbWVudGFsU2VhcmNoLnByb3RvdHlwZS5kZWFjdGl2YXRlID0gZnVuY3Rpb24gKHJlc2V0KSB7XG4gICAgICAgIHRoaXMuY2FuY2VsU2VhcmNoKHJlc2V0KTtcbiAgICAgICAgdmFyIGVkaXRvciA9IHRoaXMuJGVkaXRvcjtcbiAgICAgICAgZWRpdG9yLmtleUJpbmRpbmcucmVtb3ZlS2V5Ym9hcmRIYW5kbGVyKHRoaXMuJGtleWJvYXJkSGFuZGxlcik7XG4gICAgICAgIGlmICh0aGlzLiRtb3VzZWRvd25IYW5kbGVyKSB7XG4gICAgICAgICAgICBlZGl0b3Iub2ZmKCdtb3VzZWRvd24nLCB0aGlzLiRtb3VzZWRvd25IYW5kbGVyKTtcbiAgICAgICAgICAgIGRlbGV0ZSB0aGlzLiRtb3VzZWRvd25IYW5kbGVyO1xuICAgICAgICB9XG4gICAgICAgIGVkaXRvci5vblBhc3RlID0gdGhpcy4kb3JpZ2luYWxFZGl0b3JPblBhc3RlO1xuICAgICAgICB0aGlzLm1lc3NhZ2UoJycpO1xuICAgIH07XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLnNlbGVjdGlvbkZpeCA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgaWYgKGVkaXRvci5zZWxlY3Rpb24uaXNFbXB0eSgpICYmICFlZGl0b3Iuc2Vzc2lvbi4kZW1hY3NNYXJrKSB7XG4gICAgICAgICAgICBlZGl0b3IuY2xlYXJTZWxlY3Rpb24oKTtcbiAgICAgICAgfVxuICAgIH07XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLmhpZ2hsaWdodCA9IGZ1bmN0aW9uIChyZWdleHApIHtcbiAgICAgICAgdmFyIHNlc3MgPSB0aGlzLiRlZGl0b3Iuc2Vzc2lvbiwgaGwgPSBzZXNzLiRpc2VhcmNoSGlnaGxpZ2h0ID0gc2Vzcy4kaXNlYXJjaEhpZ2hsaWdodCB8fCBzZXNzLmFkZER5bmFtaWNNYXJrZXIobmV3IFNlYXJjaEhpZ2hsaWdodChudWxsLCBcImFjZV9pc2VhcmNoLXJlc3VsdFwiLCBcInRleHRcIikpO1xuICAgICAgICBobC5zZXRSZWdleHAocmVnZXhwKTtcbiAgICAgICAgc2Vzcy5fZW1pdChcImNoYW5nZUJhY2tNYXJrZXJcIik7IC8vIGZvcmNlIGhpZ2hsaWdodCBsYXllciByZWRyYXdcbiAgICB9O1xuICAgIEluY3JlbWVudGFsU2VhcmNoLnByb3RvdHlwZS5jYW5jZWxTZWFyY2ggPSBmdW5jdGlvbiAocmVzZXQpIHtcbiAgICAgICAgdmFyIGUgPSB0aGlzLiRlZGl0b3I7XG4gICAgICAgIHRoaXMuJHByZXZOZWVkbGUgPSB0aGlzLiRvcHRpb25zLm5lZWRsZTtcbiAgICAgICAgdGhpcy4kb3B0aW9ucy5uZWVkbGUgPSAnJztcbiAgICAgICAgaWYgKHJlc2V0KSB7XG4gICAgICAgICAgICBlLm1vdmVDdXJzb3JUb1Bvc2l0aW9uKHRoaXMuJHN0YXJ0UG9zKTtcbiAgICAgICAgICAgIHRoaXMuJGN1cnJlbnRQb3MgPSB0aGlzLiRzdGFydFBvcztcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGUucHVzaEVtYWNzTWFyayAmJiBlLnB1c2hFbWFjc01hcmsodGhpcy4kc3RhcnRQb3MsIGZhbHNlKTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLmhpZ2hsaWdodChudWxsKTtcbiAgICAgICAgcmV0dXJuIFJhbmdlLmZyb21Qb2ludHModGhpcy4kY3VycmVudFBvcywgdGhpcy4kY3VycmVudFBvcyk7XG4gICAgfTtcbiAgICBJbmNyZW1lbnRhbFNlYXJjaC5wcm90b3R5cGUuaGlnaGxpZ2h0QW5kRmluZFdpdGhOZWVkbGUgPSBmdW5jdGlvbiAobW92ZVRvTmV4dCwgbmVlZGxlVXBkYXRlRnVuYykge1xuICAgICAgICBpZiAoIXRoaXMuJGVkaXRvcilcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB2YXIgb3B0aW9ucyA9IHRoaXMuJG9wdGlvbnM7XG4gICAgICAgIGlmIChuZWVkbGVVcGRhdGVGdW5jKSB7XG4gICAgICAgICAgICBvcHRpb25zLm5lZWRsZSA9IG5lZWRsZVVwZGF0ZUZ1bmMuY2FsbCh0aGlzLCBvcHRpb25zLm5lZWRsZSB8fCAnJykgfHwgJyc7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9wdGlvbnMubmVlZGxlLmxlbmd0aCA9PT0gMCkge1xuICAgICAgICAgICAgdGhpcy5zdGF0dXNNZXNzYWdlKHRydWUpO1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuY2FuY2VsU2VhcmNoKHRydWUpO1xuICAgICAgICB9XG4gICAgICAgIG9wdGlvbnMuc3RhcnQgPSB0aGlzLiRjdXJyZW50UG9zO1xuICAgICAgICB2YXIgc2Vzc2lvbiA9IHRoaXMuJGVkaXRvci5zZXNzaW9uLCBmb3VuZCA9IHRoaXMuZmluZChzZXNzaW9uKSwgc2hvdWxkU2VsZWN0ID0gdGhpcy4kZWRpdG9yLmVtYWNzTWFyayA/XG4gICAgICAgICAgICAhIXRoaXMuJGVkaXRvci5lbWFjc01hcmsoKSA6ICF0aGlzLiRlZGl0b3Iuc2VsZWN0aW9uLmlzRW1wdHkoKTtcbiAgICAgICAgaWYgKGZvdW5kKSB7XG4gICAgICAgICAgICBpZiAob3B0aW9ucy5iYWNrd2FyZHMpXG4gICAgICAgICAgICAgICAgZm91bmQgPSBSYW5nZS5mcm9tUG9pbnRzKGZvdW5kLmVuZCwgZm91bmQuc3RhcnQpO1xuICAgICAgICAgICAgdGhpcy4kZWRpdG9yLnNlbGVjdGlvbi5zZXRSYW5nZShSYW5nZS5mcm9tUG9pbnRzKHNob3VsZFNlbGVjdCA/IHRoaXMuJHN0YXJ0UG9zIDogZm91bmQuZW5kLCBmb3VuZC5lbmQpKTtcbiAgICAgICAgICAgIGlmIChtb3ZlVG9OZXh0KVxuICAgICAgICAgICAgICAgIHRoaXMuJGN1cnJlbnRQb3MgPSBmb3VuZC5lbmQ7XG4gICAgICAgICAgICB0aGlzLmhpZ2hsaWdodChvcHRpb25zLnJlKTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLnN0YXR1c01lc3NhZ2UoZm91bmQpO1xuICAgICAgICByZXR1cm4gZm91bmQ7XG4gICAgfTtcbiAgICBJbmNyZW1lbnRhbFNlYXJjaC5wcm90b3R5cGUuYWRkU3RyaW5nID0gZnVuY3Rpb24gKHMpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaGlnaGxpZ2h0QW5kRmluZFdpdGhOZWVkbGUoZmFsc2UsIGZ1bmN0aW9uIChuZWVkbGUpIHtcbiAgICAgICAgICAgIGlmICghaXNSZWdFeHAobmVlZGxlKSlcbiAgICAgICAgICAgICAgICByZXR1cm4gbmVlZGxlICsgcztcbiAgICAgICAgICAgIHZhciByZU9iaiA9IHJlZ0V4cFRvT2JqZWN0KG5lZWRsZSk7XG4gICAgICAgICAgICByZU9iai5leHByZXNzaW9uICs9IHM7XG4gICAgICAgICAgICByZXR1cm4gb2JqZWN0VG9SZWdFeHAocmVPYmopO1xuICAgICAgICB9KTtcbiAgICB9O1xuICAgIEluY3JlbWVudGFsU2VhcmNoLnByb3RvdHlwZS5yZW1vdmVDaGFyID0gZnVuY3Rpb24gKGMpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaGlnaGxpZ2h0QW5kRmluZFdpdGhOZWVkbGUoZmFsc2UsIGZ1bmN0aW9uIChuZWVkbGUpIHtcbiAgICAgICAgICAgIGlmICghaXNSZWdFeHAobmVlZGxlKSlcbiAgICAgICAgICAgICAgICByZXR1cm4gbmVlZGxlLnN1YnN0cmluZygwLCBuZWVkbGUubGVuZ3RoIC0gMSk7XG4gICAgICAgICAgICB2YXIgcmVPYmogPSByZWdFeHBUb09iamVjdChuZWVkbGUpO1xuICAgICAgICAgICAgcmVPYmouZXhwcmVzc2lvbiA9IHJlT2JqLmV4cHJlc3Npb24uc3Vic3RyaW5nKDAsIHJlT2JqLmV4cHJlc3Npb24ubGVuZ3RoIC0gMSk7XG4gICAgICAgICAgICByZXR1cm4gb2JqZWN0VG9SZWdFeHAocmVPYmopO1xuICAgICAgICB9KTtcbiAgICB9O1xuICAgIEluY3JlbWVudGFsU2VhcmNoLnByb3RvdHlwZS5uZXh0ID0gZnVuY3Rpb24gKG9wdGlvbnMpIHtcbiAgICAgICAgb3B0aW9ucyA9IG9wdGlvbnMgfHwge307XG4gICAgICAgIHRoaXMuJG9wdGlvbnMuYmFja3dhcmRzID0gISFvcHRpb25zLmJhY2t3YXJkcztcbiAgICAgICAgdGhpcy4kY3VycmVudFBvcyA9IHRoaXMuJGVkaXRvci5nZXRDdXJzb3JQb3NpdGlvbigpO1xuICAgICAgICByZXR1cm4gdGhpcy5oaWdobGlnaHRBbmRGaW5kV2l0aE5lZWRsZSh0cnVlLCBmdW5jdGlvbiAobmVlZGxlKSB7XG4gICAgICAgICAgICByZXR1cm4gb3B0aW9ucy51c2VDdXJyZW50T3JQcmV2U2VhcmNoICYmIG5lZWRsZS5sZW5ndGggPT09IDAgP1xuICAgICAgICAgICAgICAgIHRoaXMuJHByZXZOZWVkbGUgfHwgJycgOiBuZWVkbGU7XG4gICAgICAgIH0pO1xuICAgIH07XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLm9uTW91c2VEb3duID0gZnVuY3Rpb24gKGV2dCkge1xuICAgICAgICB0aGlzLmRlYWN0aXZhdGUoKTtcbiAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgfTtcbiAgICBJbmNyZW1lbnRhbFNlYXJjaC5wcm90b3R5cGUub25QYXN0ZSA9IGZ1bmN0aW9uICh0ZXh0KSB7XG4gICAgICAgIHRoaXMuYWRkU3RyaW5nKHRleHQpO1xuICAgIH07XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLmNvbnZlcnROZWVkbGVUb1JlZ0V4cCA9IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuaGlnaGxpZ2h0QW5kRmluZFdpdGhOZWVkbGUoZmFsc2UsIGZ1bmN0aW9uIChuZWVkbGUpIHtcbiAgICAgICAgICAgIHJldHVybiBpc1JlZ0V4cChuZWVkbGUpID8gbmVlZGxlIDogc3RyaW5nVG9SZWdFeHAobmVlZGxlLCAnaWcnKTtcbiAgICAgICAgfSk7XG4gICAgfTtcbiAgICBJbmNyZW1lbnRhbFNlYXJjaC5wcm90b3R5cGUuY29udmVydE5lZWRsZVRvU3RyaW5nID0gZnVuY3Rpb24gKCkge1xuICAgICAgICByZXR1cm4gdGhpcy5oaWdobGlnaHRBbmRGaW5kV2l0aE5lZWRsZShmYWxzZSwgZnVuY3Rpb24gKG5lZWRsZSkge1xuICAgICAgICAgICAgcmV0dXJuIGlzUmVnRXhwKG5lZWRsZSkgPyByZWdFeHBUb09iamVjdChuZWVkbGUpLmV4cHJlc3Npb24gOiBuZWVkbGU7XG4gICAgICAgIH0pO1xuICAgIH07XG4gICAgSW5jcmVtZW50YWxTZWFyY2gucHJvdG90eXBlLnN0YXR1c01lc3NhZ2UgPSBmdW5jdGlvbiAoZm91bmQpIHtcbiAgICAgICAgdmFyIG9wdGlvbnMgPSB0aGlzLiRvcHRpb25zLCBtc2cgPSAnJztcbiAgICAgICAgbXNnICs9IG9wdGlvbnMuYmFja3dhcmRzID8gJ3JldmVyc2UtJyA6ICcnO1xuICAgICAgICBtc2cgKz0gJ2lzZWFyY2g6ICcgKyBvcHRpb25zLm5lZWRsZTtcbiAgICAgICAgbXNnICs9IGZvdW5kID8gJycgOiAnIChub3QgZm91bmQpJztcbiAgICAgICAgdGhpcy5tZXNzYWdlKG1zZyk7XG4gICAgfTtcbiAgICBJbmNyZW1lbnRhbFNlYXJjaC5wcm90b3R5cGUubWVzc2FnZSA9IGZ1bmN0aW9uIChtc2cpIHtcbiAgICAgICAgaWYgKHRoaXMuJGVkaXRvci5zaG93Q29tbWFuZExpbmUpIHtcbiAgICAgICAgICAgIHRoaXMuJGVkaXRvci5zaG93Q29tbWFuZExpbmUobXNnKTtcbiAgICAgICAgICAgIHRoaXMuJGVkaXRvci5mb2N1cygpO1xuICAgICAgICB9XG4gICAgfTtcbiAgICByZXR1cm4gSW5jcmVtZW50YWxTZWFyY2g7XG59KFNlYXJjaCkpO1xuZXhwb3J0cy5JbmNyZW1lbnRhbFNlYXJjaCA9IEluY3JlbWVudGFsU2VhcmNoO1xudmFyIGRvbSA9IHJlcXVpcmUoJy4vbGliL2RvbScpO1xuZG9tLmltcG9ydENzc1N0cmluZyhcIlxcbi5hY2VfbWFya2VyLWxheWVyIC5hY2VfaXNlYXJjaC1yZXN1bHQge1xcbiAgcG9zaXRpb246IGFic29sdXRlO1xcbiAgei1pbmRleDogNjtcXG4gIGJveC1zaXppbmc6IGJvcmRlci1ib3g7XFxufVxcbmRpdi5hY2VfaXNlYXJjaC1yZXN1bHQge1xcbiAgYm9yZGVyLXJhZGl1czogNHB4O1xcbiAgYmFja2dyb3VuZC1jb2xvcjogcmdiYSgyNTUsIDIwMCwgMCwgMC41KTtcXG4gIGJveC1zaGFkb3c6IDAgMCA0cHggcmdiKDI1NSwgMjAwLCAwKTtcXG59XFxuLmFjZV9kYXJrIGRpdi5hY2VfaXNlYXJjaC1yZXN1bHQge1xcbiAgYmFja2dyb3VuZC1jb2xvcjogcmdiKDEwMCwgMTEwLCAxNjApO1xcbiAgYm94LXNoYWRvdzogMCAwIDRweCByZ2IoODAsIDkwLCAxNDApO1xcbn1cIiwgXCJpbmNyZW1lbnRhbC1zZWFyY2gtaGlnaGxpZ2h0aW5nXCIsIGZhbHNlKTtcbnZhciBjb21tYW5kcyA9IHJlcXVpcmUoXCIuL2NvbW1hbmRzL2NvbW1hbmRfbWFuYWdlclwiKTtcbihmdW5jdGlvbiAoKSB7XG4gICAgdGhpcy5zZXR1cEluY3JlbWVudGFsU2VhcmNoID0gZnVuY3Rpb24gKGVkaXRvciwgdmFsKSB7XG4gICAgICAgIGlmICh0aGlzLnVzZXNJbmNyZW1lbnRhbFNlYXJjaCA9PSB2YWwpXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgIHRoaXMudXNlc0luY3JlbWVudGFsU2VhcmNoID0gdmFsO1xuICAgICAgICB2YXIgaVNlYXJjaENvbW1hbmRzID0gaVNlYXJjaENvbW1hbmRNb2R1bGUuaVNlYXJjaFN0YXJ0Q29tbWFuZHM7XG4gICAgICAgIHZhciBtZXRob2QgPSB2YWwgPyAnYWRkQ29tbWFuZHMnIDogJ3JlbW92ZUNvbW1hbmRzJztcbiAgICAgICAgdGhpc1ttZXRob2RdKGlTZWFyY2hDb21tYW5kcyk7XG4gICAgfTtcbn0pLmNhbGwoY29tbWFuZHMuQ29tbWFuZE1hbmFnZXIucHJvdG90eXBlKTtcbnZhciBFZGl0b3IgPSByZXF1aXJlKFwiLi9lZGl0b3JcIikuRWRpdG9yO1xucmVxdWlyZShcIi4vY29uZmlnXCIpLmRlZmluZU9wdGlvbnMoRWRpdG9yLnByb3RvdHlwZSwgXCJlZGl0b3JcIiwge1xuICAgIHVzZUluY3JlbWVudGFsU2VhcmNoOiB7XG4gICAgICAgIHNldDogZnVuY3Rpb24gKHZhbCkge1xuICAgICAgICAgICAgdGhpcy5rZXlCaW5kaW5nLiRoYW5kbGVycy5mb3JFYWNoKGZ1bmN0aW9uIChoYW5kbGVyKSB7XG4gICAgICAgICAgICAgICAgaWYgKGhhbmRsZXIuc2V0dXBJbmNyZW1lbnRhbFNlYXJjaCkge1xuICAgICAgICAgICAgICAgICAgICBoYW5kbGVyLnNldHVwSW5jcmVtZW50YWxTZWFyY2godGhpcywgdmFsKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIHRoaXMuX2VtaXQoJ2luY3JlbWVudGFsU2VhcmNoU2V0dGluZ0NoYW5nZWQnLCB7IGlzRW5hYmxlZDogdmFsIH0pO1xuICAgICAgICB9XG4gICAgfVxufSk7XG5cbn0pO1xuXG5hY2UuZGVmaW5lKFwiYWNlL2tleWJvYXJkL2VtYWNzXCIsW1wicmVxdWlyZVwiLFwiZXhwb3J0c1wiLFwibW9kdWxlXCIsXCJhY2UvbGliL2RvbVwiLFwiYWNlL2luY3JlbWVudGFsX3NlYXJjaFwiLFwiYWNlL2NvbW1hbmRzL2luY3JlbWVudGFsX3NlYXJjaF9jb21tYW5kc1wiLFwiYWNlL2tleWJvYXJkL2hhc2hfaGFuZGxlclwiLFwiYWNlL2xpYi9rZXlzXCJdLCBmdW5jdGlvbihyZXF1aXJlLCBleHBvcnRzLCBtb2R1bGUpe1widXNlIHN0cmljdFwiO1xudmFyIGRvbSA9IHJlcXVpcmUoXCIuLi9saWIvZG9tXCIpO1xucmVxdWlyZShcIi4uL2luY3JlbWVudGFsX3NlYXJjaFwiKTtcbnZhciBpU2VhcmNoQ29tbWFuZE1vZHVsZSA9IHJlcXVpcmUoXCIuLi9jb21tYW5kcy9pbmNyZW1lbnRhbF9zZWFyY2hfY29tbWFuZHNcIik7XG52YXIgSGFzaEhhbmRsZXIgPSByZXF1aXJlKFwiLi9oYXNoX2hhbmRsZXJcIikuSGFzaEhhbmRsZXI7XG5leHBvcnRzLmhhbmRsZXIgPSBuZXcgSGFzaEhhbmRsZXIoKTtcbmV4cG9ydHMuaGFuZGxlci5pc0VtYWNzID0gdHJ1ZTtcbmV4cG9ydHMuaGFuZGxlci4kaWQgPSBcImFjZS9rZXlib2FyZC9lbWFjc1wiO1xuZG9tLmltcG9ydENzc1N0cmluZyhcIlxcbi5lbWFjcy1tb2RlIC5hY2VfY3Vyc29ye1xcbiAgICBib3JkZXI6IDFweCByZ2JhKDUwLDI1MCw1MCwwLjgpIHNvbGlkIWltcG9ydGFudDtcXG4gICAgYm94LXNpemluZzogYm9yZGVyLWJveCFpbXBvcnRhbnQ7XFxuICAgIGJhY2tncm91bmQtY29sb3I6IHJnYmEoMCwyNTAsMCwwLjkpO1xcbiAgICBvcGFjaXR5OiAwLjU7XFxufVxcbi5lbWFjcy1tb2RlIC5hY2VfaGlkZGVuLWN1cnNvcnMgLmFjZV9jdXJzb3J7XFxuICAgIG9wYWNpdHk6IDE7XFxuICAgIGJhY2tncm91bmQtY29sb3I6IHRyYW5zcGFyZW50O1xcbn1cXG4uZW1hY3MtbW9kZSAuYWNlX292ZXJ3cml0ZS1jdXJzb3JzIC5hY2VfY3Vyc29yIHtcXG4gICAgb3BhY2l0eTogMTtcXG4gICAgYmFja2dyb3VuZC1jb2xvcjogdHJhbnNwYXJlbnQ7XFxuICAgIGJvcmRlci13aWR0aDogMCAwIDJweCAycHggIWltcG9ydGFudDtcXG59XFxuLmVtYWNzLW1vZGUgLmFjZV90ZXh0LWxheWVyIHtcXG4gICAgei1pbmRleDogNFxcbn1cXG4uZW1hY3MtbW9kZSAuYWNlX2N1cnNvci1sYXllciB7XFxuICAgIHotaW5kZXg6IDJcXG59XCIsICdlbWFjc01vZGUnLCBmYWxzZSk7XG52YXIgJGZvcm1lckxvbmdXb3JkcztcbnZhciAkZm9ybWVyTGluZVN0YXJ0O1xuZXhwb3J0cy5oYW5kbGVyLmF0dGFjaCA9IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAkZm9ybWVyTG9uZ1dvcmRzID0gZWRpdG9yLnNlc3Npb24uJHNlbGVjdExvbmdXb3JkcztcbiAgICBlZGl0b3Iuc2Vzc2lvbi4kc2VsZWN0TG9uZ1dvcmRzID0gdHJ1ZTtcbiAgICAkZm9ybWVyTGluZVN0YXJ0ID0gZWRpdG9yLnNlc3Npb24uJHVzZUVtYWNzU3R5bGVMaW5lU3RhcnQ7XG4gICAgZWRpdG9yLnNlc3Npb24uJHVzZUVtYWNzU3R5bGVMaW5lU3RhcnQgPSB0cnVlO1xuICAgIGVkaXRvci5zZXNzaW9uLiRlbWFjc01hcmsgPSBudWxsOyAvLyB0aGUgYWN0aXZlIG1hcmtcbiAgICBlZGl0b3Iuc2Vzc2lvbi4kZW1hY3NNYXJrUmluZyA9IGVkaXRvci5zZXNzaW9uLiRlbWFjc01hcmtSaW5nIHx8IFtdO1xuICAgIGVkaXRvci5lbWFjc01hcmsgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHJldHVybiB0aGlzLnNlc3Npb24uJGVtYWNzTWFyaztcbiAgICB9O1xuICAgIGVkaXRvci5zZXRFbWFjc01hcmsgPSBmdW5jdGlvbiAocCkge1xuICAgICAgICB0aGlzLnNlc3Npb24uJGVtYWNzTWFyayA9IHA7XG4gICAgfTtcbiAgICBlZGl0b3IucHVzaEVtYWNzTWFyayA9IGZ1bmN0aW9uIChwLCBhY3RpdmF0ZSkge1xuICAgICAgICB2YXIgcHJldk1hcmsgPSB0aGlzLnNlc3Npb24uJGVtYWNzTWFyaztcbiAgICAgICAgaWYgKHByZXZNYXJrKVxuICAgICAgICAgICAgcHVzaFVuaXF1ZSh0aGlzLnNlc3Npb24uJGVtYWNzTWFya1JpbmcsIHByZXZNYXJrKTtcbiAgICAgICAgaWYgKCFwIHx8IGFjdGl2YXRlKVxuICAgICAgICAgICAgdGhpcy5zZXRFbWFjc01hcmsocCk7XG4gICAgICAgIGVsc2VcbiAgICAgICAgICAgIHB1c2hVbmlxdWUodGhpcy5zZXNzaW9uLiRlbWFjc01hcmtSaW5nLCBwKTtcbiAgICB9O1xuICAgIGVkaXRvci5wb3BFbWFjc01hcmsgPSBmdW5jdGlvbiAoKSB7XG4gICAgICAgIHZhciBtYXJrID0gdGhpcy5lbWFjc01hcmsoKTtcbiAgICAgICAgaWYgKG1hcmspIHtcbiAgICAgICAgICAgIHRoaXMuc2V0RW1hY3NNYXJrKG51bGwpO1xuICAgICAgICAgICAgcmV0dXJuIG1hcms7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRoaXMuc2Vzc2lvbi4kZW1hY3NNYXJrUmluZy5wb3AoKTtcbiAgICB9O1xuICAgIGVkaXRvci5nZXRMYXN0RW1hY3NNYXJrID0gZnVuY3Rpb24gKHApIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuc2Vzc2lvbi4kZW1hY3NNYXJrIHx8IHRoaXMuc2Vzc2lvbi4kZW1hY3NNYXJrUmluZy5zbGljZSgtMSlbMF07XG4gICAgfTtcbiAgICBlZGl0b3IuZW1hY3NNYXJrRm9yU2VsZWN0aW9uID0gZnVuY3Rpb24gKHJlcGxhY2VtZW50KSB7XG4gICAgICAgIHZhciBzZWwgPSB0aGlzLnNlbGVjdGlvbiwgbXVsdGlSYW5nZUxlbmd0aCA9IHRoaXMubXVsdGlTZWxlY3QgP1xuICAgICAgICAgICAgdGhpcy5tdWx0aVNlbGVjdC5nZXRBbGxSYW5nZXMoKS5sZW5ndGggOiAxLCBzZWxJbmRleCA9IHNlbC5pbmRleCB8fCAwLCBtYXJrUmluZyA9IHRoaXMuc2Vzc2lvbi4kZW1hY3NNYXJrUmluZywgbWFya0luZGV4ID0gbWFya1JpbmcubGVuZ3RoIC0gKG11bHRpUmFuZ2VMZW5ndGggLSBzZWxJbmRleCksIGxhc3RNYXJrID0gbWFya1JpbmdbbWFya0luZGV4XSB8fCBzZWwuYW5jaG9yO1xuICAgICAgICBpZiAocmVwbGFjZW1lbnQpIHtcbiAgICAgICAgICAgIG1hcmtSaW5nLnNwbGljZShtYXJrSW5kZXgsIDEsIFwicm93XCIgaW4gcmVwbGFjZW1lbnQgJiYgXCJjb2x1bW5cIiBpbiByZXBsYWNlbWVudCA/XG4gICAgICAgICAgICAgICAgcmVwbGFjZW1lbnQgOiB1bmRlZmluZWQpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBsYXN0TWFyaztcbiAgICB9O1xuICAgIGVkaXRvci5vbihcImNsaWNrXCIsICRyZXNldE1hcmtNb2RlKTtcbiAgICBlZGl0b3Iub24oXCJjaGFuZ2VTZXNzaW9uXCIsICRrYlNlc3Npb25DaGFuZ2UpO1xuICAgIGVkaXRvci5yZW5kZXJlci4kYmxvY2tDdXJzb3IgPSB0cnVlO1xuICAgIGVkaXRvci5zZXRTdHlsZShcImVtYWNzLW1vZGVcIik7XG4gICAgZWRpdG9yLmNvbW1hbmRzLmFkZENvbW1hbmRzKGNvbW1hbmRzKTtcbiAgICBleHBvcnRzLmhhbmRsZXIucGxhdGZvcm0gPSBlZGl0b3IuY29tbWFuZHMucGxhdGZvcm07XG4gICAgZWRpdG9yLiRlbWFjc01vZGVIYW5kbGVyID0gdGhpcztcbiAgICBlZGl0b3Iub24oJ2NvcHknLCB0aGlzLm9uQ29weSk7XG4gICAgZWRpdG9yLm9uKCdwYXN0ZScsIHRoaXMub25QYXN0ZSk7XG59O1xuZnVuY3Rpb24gcHVzaFVuaXF1ZShyaW5nLCBtYXJrKSB7XG4gICAgdmFyIGxhc3QgPSByaW5nW3JpbmcubGVuZ3RoIC0gMV07XG4gICAgaWYgKGxhc3QgJiYgbGFzdC5yb3cgPT09IG1hcmsucm93ICYmIGxhc3QuY29sdW1uID09PSBtYXJrLmNvbHVtbikge1xuICAgICAgICByZXR1cm47XG4gICAgfVxuICAgIHJpbmcucHVzaChtYXJrKTtcbn1cbmV4cG9ydHMuaGFuZGxlci5kZXRhY2ggPSBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgZWRpdG9yLnJlbmRlcmVyLiRibG9ja0N1cnNvciA9IGZhbHNlO1xuICAgIGVkaXRvci5zZXNzaW9uLiRzZWxlY3RMb25nV29yZHMgPSAkZm9ybWVyTG9uZ1dvcmRzO1xuICAgIGVkaXRvci5zZXNzaW9uLiR1c2VFbWFjc1N0eWxlTGluZVN0YXJ0ID0gJGZvcm1lckxpbmVTdGFydDtcbiAgICBlZGl0b3Iub2ZmKFwiY2xpY2tcIiwgJHJlc2V0TWFya01vZGUpO1xuICAgIGVkaXRvci5vZmYoXCJjaGFuZ2VTZXNzaW9uXCIsICRrYlNlc3Npb25DaGFuZ2UpO1xuICAgIGVkaXRvci51bnNldFN0eWxlKFwiZW1hY3MtbW9kZVwiKTtcbiAgICBlZGl0b3IuY29tbWFuZHMucmVtb3ZlQ29tbWFuZHMoY29tbWFuZHMpO1xuICAgIGVkaXRvci5vZmYoJ2NvcHknLCB0aGlzLm9uQ29weSk7XG4gICAgZWRpdG9yLm9mZigncGFzdGUnLCB0aGlzLm9uUGFzdGUpO1xuICAgIGVkaXRvci4kZW1hY3NNb2RlSGFuZGxlciA9IG51bGw7XG59O1xudmFyICRrYlNlc3Npb25DaGFuZ2UgPSBmdW5jdGlvbiAoZSkge1xuICAgIGlmIChlLm9sZFNlc3Npb24pIHtcbiAgICAgICAgZS5vbGRTZXNzaW9uLiRzZWxlY3RMb25nV29yZHMgPSAkZm9ybWVyTG9uZ1dvcmRzO1xuICAgICAgICBlLm9sZFNlc3Npb24uJHVzZUVtYWNzU3R5bGVMaW5lU3RhcnQgPSAkZm9ybWVyTGluZVN0YXJ0O1xuICAgIH1cbiAgICAkZm9ybWVyTG9uZ1dvcmRzID0gZS5zZXNzaW9uLiRzZWxlY3RMb25nV29yZHM7XG4gICAgZS5zZXNzaW9uLiRzZWxlY3RMb25nV29yZHMgPSB0cnVlO1xuICAgICRmb3JtZXJMaW5lU3RhcnQgPSBlLnNlc3Npb24uJHVzZUVtYWNzU3R5bGVMaW5lU3RhcnQ7XG4gICAgZS5zZXNzaW9uLiR1c2VFbWFjc1N0eWxlTGluZVN0YXJ0ID0gdHJ1ZTtcbiAgICBpZiAoIWUuc2Vzc2lvbi5oYXNPd25Qcm9wZXJ0eSgnJGVtYWNzTWFyaycpKVxuICAgICAgICBlLnNlc3Npb24uJGVtYWNzTWFyayA9IG51bGw7XG4gICAgaWYgKCFlLnNlc3Npb24uaGFzT3duUHJvcGVydHkoJyRlbWFjc01hcmtSaW5nJykpXG4gICAgICAgIGUuc2Vzc2lvbi4kZW1hY3NNYXJrUmluZyA9IFtdO1xufTtcbnZhciAkcmVzZXRNYXJrTW9kZSA9IGZ1bmN0aW9uIChlKSB7XG4gICAgZS5lZGl0b3Iuc2Vzc2lvbi4kZW1hY3NNYXJrID0gbnVsbDtcbn07XG52YXIga2V5cyA9IHJlcXVpcmUoXCIuLi9saWIva2V5c1wiKS5LRVlfTU9EUztcbnZhciBlTW9kcyA9IHsgQzogXCJjdHJsXCIsIFM6IFwic2hpZnRcIiwgTTogXCJhbHRcIiwgQ01EOiBcImNvbW1hbmRcIiB9O1xudmFyIGNvbWJpbmF0aW9ucyA9IFtcIkMtUy1NLUNNRFwiLFxuICAgIFwiUy1NLUNNRFwiLCBcIkMtTS1DTURcIiwgXCJDLVMtQ01EXCIsIFwiQy1TLU1cIixcbiAgICBcIk0tQ01EXCIsIFwiUy1DTURcIiwgXCJTLU1cIiwgXCJDLUNNRFwiLCBcIkMtTVwiLCBcIkMtU1wiLFxuICAgIFwiQ01EXCIsIFwiTVwiLCBcIlNcIiwgXCJDXCJdO1xuY29tYmluYXRpb25zLmZvckVhY2goZnVuY3Rpb24gKGMpIHtcbiAgICB2YXIgaGFzaElkID0gMDtcbiAgICBjLnNwbGl0KFwiLVwiKS5mb3JFYWNoKGZ1bmN0aW9uIChjKSB7XG4gICAgICAgIGhhc2hJZCA9IGhhc2hJZCB8IGtleXNbZU1vZHNbY11dO1xuICAgIH0pO1xuICAgIGVNb2RzW2hhc2hJZF0gPSBjLnRvTG93ZXJDYXNlKCkgKyBcIi1cIjtcbn0pO1xuZXhwb3J0cy5oYW5kbGVyLm9uQ29weSA9IGZ1bmN0aW9uIChlLCBlZGl0b3IpIHtcbiAgICBpZiAoZWRpdG9yLiRoYW5kbGVzRW1hY3NPbkNvcHkpXG4gICAgICAgIHJldHVybjtcbiAgICBlZGl0b3IuJGhhbmRsZXNFbWFjc09uQ29weSA9IHRydWU7XG4gICAgZXhwb3J0cy5oYW5kbGVyLmNvbW1hbmRzLmtpbGxSaW5nU2F2ZS5leGVjKGVkaXRvcik7XG4gICAgZWRpdG9yLiRoYW5kbGVzRW1hY3NPbkNvcHkgPSBmYWxzZTtcbn07XG5leHBvcnRzLmhhbmRsZXIub25QYXN0ZSA9IGZ1bmN0aW9uIChlLCBlZGl0b3IpIHtcbiAgICBlZGl0b3IucHVzaEVtYWNzTWFyayhlZGl0b3IuZ2V0Q3Vyc29yUG9zaXRpb24oKSk7XG59O1xuZXhwb3J0cy5oYW5kbGVyLmJpbmRLZXkgPSBmdW5jdGlvbiAoa2V5LCBjb21tYW5kKSB7XG4gICAgaWYgKHR5cGVvZiBrZXkgPT0gXCJvYmplY3RcIilcbiAgICAgICAga2V5ID0ga2V5W3RoaXMucGxhdGZvcm1dO1xuICAgIGlmICgha2V5KVxuICAgICAgICByZXR1cm47XG4gICAgdmFyIGNrYiA9IHRoaXMuY29tbWFuZEtleUJpbmRpbmc7XG4gICAga2V5LnNwbGl0KFwifFwiKS5mb3JFYWNoKGZ1bmN0aW9uIChrZXlQYXJ0KSB7XG4gICAgICAgIGtleVBhcnQgPSBrZXlQYXJ0LnRvTG93ZXJDYXNlKCk7XG4gICAgICAgIGNrYltrZXlQYXJ0XSA9IGNvbW1hbmQ7XG4gICAgICAgIHZhciBrZXlQYXJ0cyA9IGtleVBhcnQuc3BsaXQoXCIgXCIpLnNsaWNlKDAsIC0xKTtcbiAgICAgICAga2V5UGFydHMucmVkdWNlKGZ1bmN0aW9uIChrZXlNYXBLZXlzLCBrZXlQYXJ0LCBpKSB7XG4gICAgICAgICAgICB2YXIgcHJlZml4ID0ga2V5TWFwS2V5c1tpIC0gMV0gPyBrZXlNYXBLZXlzW2kgLSAxXSArICcgJyA6ICcnO1xuICAgICAgICAgICAgcmV0dXJuIGtleU1hcEtleXMuY29uY2F0KFtwcmVmaXggKyBrZXlQYXJ0XSk7XG4gICAgICAgIH0sIFtdKS5mb3JFYWNoKGZ1bmN0aW9uIChrZXlQYXJ0KSB7XG4gICAgICAgICAgICBpZiAoIWNrYltrZXlQYXJ0XSlcbiAgICAgICAgICAgICAgICBja2Jba2V5UGFydF0gPSBcIm51bGxcIjtcbiAgICAgICAgfSk7XG4gICAgfSwgdGhpcyk7XG59O1xuZXhwb3J0cy5oYW5kbGVyLmdldFN0YXR1c1RleHQgPSBmdW5jdGlvbiAoZWRpdG9yLCBkYXRhKSB7XG4gICAgdmFyIHN0ciA9IFwiXCI7XG4gICAgaWYgKGRhdGEuY291bnQpXG4gICAgICAgIHN0ciArPSBkYXRhLmNvdW50O1xuICAgIGlmIChkYXRhLmtleUNoYWluKVxuICAgICAgICBzdHIgKz0gXCIgXCIgKyBkYXRhLmtleUNoYWluO1xuICAgIHJldHVybiBzdHI7XG59O1xuZXhwb3J0cy5oYW5kbGVyLmhhbmRsZUtleWJvYXJkID0gZnVuY3Rpb24gKGRhdGEsIGhhc2hJZCwga2V5LCBrZXlDb2RlKSB7XG4gICAgaWYgKGtleUNvZGUgPT09IC0xKVxuICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgIHZhciBlZGl0b3IgPSBkYXRhLmVkaXRvcjtcbiAgICBlZGl0b3IuX3NpZ25hbChcImNoYW5nZVN0YXR1c1wiKTtcbiAgICBpZiAoaGFzaElkID09IC0xKSB7XG4gICAgICAgIGVkaXRvci5wdXNoRW1hY3NNYXJrKCk7XG4gICAgICAgIGlmIChkYXRhLmNvdW50KSB7XG4gICAgICAgICAgICB2YXIgc3RyID0gbmV3IEFycmF5KGRhdGEuY291bnQgKyAxKS5qb2luKGtleSk7XG4gICAgICAgICAgICBkYXRhLmNvdW50ID0gbnVsbDtcbiAgICAgICAgICAgIHJldHVybiB7IGNvbW1hbmQ6IFwiaW5zZXJ0c3RyaW5nXCIsIGFyZ3M6IHN0ciB9O1xuICAgICAgICB9XG4gICAgfVxuICAgIHZhciBtb2RpZmllciA9IGVNb2RzW2hhc2hJZF07XG4gICAgaWYgKG1vZGlmaWVyID09IFwiYy1cIiB8fCBkYXRhLmNvdW50KSB7XG4gICAgICAgIHZhciBjb3VudCA9IHBhcnNlSW50KGtleVtrZXkubGVuZ3RoIC0gMV0pO1xuICAgICAgICBpZiAodHlwZW9mIGNvdW50ID09PSAnbnVtYmVyJyAmJiAhaXNOYU4oY291bnQpKSB7XG4gICAgICAgICAgICBkYXRhLmNvdW50ID0gTWF0aC5tYXgoZGF0YS5jb3VudCwgMCkgfHwgMDtcbiAgICAgICAgICAgIGRhdGEuY291bnQgPSAxMCAqIGRhdGEuY291bnQgKyBjb3VudDtcbiAgICAgICAgICAgIHJldHVybiB7IGNvbW1hbmQ6IFwibnVsbFwiIH07XG4gICAgICAgIH1cbiAgICB9XG4gICAgaWYgKG1vZGlmaWVyKVxuICAgICAgICBrZXkgPSBtb2RpZmllciArIGtleTtcbiAgICBpZiAoZGF0YS5rZXlDaGFpbilcbiAgICAgICAga2V5ID0gZGF0YS5rZXlDaGFpbiArPSBcIiBcIiArIGtleTtcbiAgICB2YXIgY29tbWFuZCA9IHRoaXMuY29tbWFuZEtleUJpbmRpbmdba2V5XTtcbiAgICBkYXRhLmtleUNoYWluID0gY29tbWFuZCA9PSBcIm51bGxcIiA/IGtleSA6IFwiXCI7XG4gICAgaWYgKCFjb21tYW5kKVxuICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgIGlmIChjb21tYW5kID09PSBcIm51bGxcIilcbiAgICAgICAgcmV0dXJuIHsgY29tbWFuZDogXCJudWxsXCIgfTtcbiAgICBpZiAoY29tbWFuZCA9PT0gXCJ1bml2ZXJzYWxBcmd1bWVudFwiKSB7XG4gICAgICAgIGRhdGEuY291bnQgPSAtNDtcbiAgICAgICAgcmV0dXJuIHsgY29tbWFuZDogXCJudWxsXCIgfTtcbiAgICB9XG4gICAgdmFyIGFyZ3M7XG4gICAgaWYgKHR5cGVvZiBjb21tYW5kICE9PSBcInN0cmluZ1wiKSB7XG4gICAgICAgIGFyZ3MgPSBjb21tYW5kLmFyZ3M7XG4gICAgICAgIGlmIChjb21tYW5kLmNvbW1hbmQpXG4gICAgICAgICAgICBjb21tYW5kID0gY29tbWFuZC5jb21tYW5kO1xuICAgICAgICBpZiAoY29tbWFuZCA9PT0gXCJnb29yc2VsZWN0XCIpIHtcbiAgICAgICAgICAgIGNvbW1hbmQgPSBlZGl0b3IuZW1hY3NNYXJrKCkgPyBhcmdzWzFdIDogYXJnc1swXTtcbiAgICAgICAgICAgIGFyZ3MgPSBudWxsO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmICh0eXBlb2YgY29tbWFuZCA9PT0gXCJzdHJpbmdcIikge1xuICAgICAgICBpZiAoY29tbWFuZCA9PT0gXCJpbnNlcnRzdHJpbmdcIiB8fFxuICAgICAgICAgICAgY29tbWFuZCA9PT0gXCJzcGxpdGxpbmVcIiB8fFxuICAgICAgICAgICAgY29tbWFuZCA9PT0gXCJ0b2dnbGVjb21tZW50XCIpIHtcbiAgICAgICAgICAgIGVkaXRvci5wdXNoRW1hY3NNYXJrKCk7XG4gICAgICAgIH1cbiAgICAgICAgY29tbWFuZCA9IHRoaXMuY29tbWFuZHNbY29tbWFuZF0gfHwgZWRpdG9yLmNvbW1hbmRzLmNvbW1hbmRzW2NvbW1hbmRdO1xuICAgICAgICBpZiAoIWNvbW1hbmQpXG4gICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgIH1cbiAgICBpZiAoIWNvbW1hbmQucmVhZE9ubHkgJiYgIWNvbW1hbmQuaXNZYW5rKVxuICAgICAgICBkYXRhLmxhc3RDb21tYW5kID0gbnVsbDtcbiAgICBpZiAoIWNvbW1hbmQucmVhZE9ubHkgJiYgZWRpdG9yLmVtYWNzTWFyaygpKVxuICAgICAgICBlZGl0b3Iuc2V0RW1hY3NNYXJrKG51bGwpO1xuICAgIGlmIChkYXRhLmNvdW50KSB7XG4gICAgICAgIHZhciBjb3VudCA9IGRhdGEuY291bnQ7XG4gICAgICAgIGRhdGEuY291bnQgPSAwO1xuICAgICAgICBpZiAoIWNvbW1hbmQgfHwgIWNvbW1hbmQuaGFuZGxlc0NvdW50KSB7XG4gICAgICAgICAgICByZXR1cm4ge1xuICAgICAgICAgICAgICAgIGFyZ3M6IGFyZ3MsXG4gICAgICAgICAgICAgICAgY29tbWFuZDoge1xuICAgICAgICAgICAgICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yLCBhcmdzKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGNvdW50OyBpKyspXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY29tbWFuZC5leGVjKGVkaXRvciwgYXJncyk7XG4gICAgICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAgICAgICAgIG11bHRpU2VsZWN0QWN0aW9uOiBjb21tYW5kLm11bHRpU2VsZWN0QWN0aW9uXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGlmICghYXJncylcbiAgICAgICAgICAgICAgICBhcmdzID0ge307XG4gICAgICAgICAgICBpZiAodHlwZW9mIGFyZ3MgPT09ICdvYmplY3QnKVxuICAgICAgICAgICAgICAgIGFyZ3MuY291bnQgPSBjb3VudDtcbiAgICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4geyBjb21tYW5kOiBjb21tYW5kLCBhcmdzOiBhcmdzIH07XG59O1xuZXhwb3J0cy5lbWFjc0tleXMgPSB7XG4gICAgXCJVcHxDLXBcIjogeyBjb21tYW5kOiBcImdvb3JzZWxlY3RcIiwgYXJnczogW1wiZ29saW5ldXBcIiwgXCJzZWxlY3R1cFwiXSB9LFxuICAgIFwiRG93bnxDLW5cIjogeyBjb21tYW5kOiBcImdvb3JzZWxlY3RcIiwgYXJnczogW1wiZ29saW5lZG93blwiLCBcInNlbGVjdGRvd25cIl0gfSxcbiAgICBcIkxlZnR8Qy1iXCI6IHsgY29tbWFuZDogXCJnb29yc2VsZWN0XCIsIGFyZ3M6IFtcImdvdG9sZWZ0XCIsIFwic2VsZWN0bGVmdFwiXSB9LFxuICAgIFwiUmlnaHR8Qy1mXCI6IHsgY29tbWFuZDogXCJnb29yc2VsZWN0XCIsIGFyZ3M6IFtcImdvdG9yaWdodFwiLCBcInNlbGVjdHJpZ2h0XCJdIH0sXG4gICAgXCJDLUxlZnR8TS1iXCI6IHsgY29tbWFuZDogXCJnb29yc2VsZWN0XCIsIGFyZ3M6IFtcImdvdG93b3JkbGVmdFwiLCBcInNlbGVjdHdvcmRsZWZ0XCJdIH0sXG4gICAgXCJDLVJpZ2h0fE0tZlwiOiB7IGNvbW1hbmQ6IFwiZ29vcnNlbGVjdFwiLCBhcmdzOiBbXCJnb3Rvd29yZHJpZ2h0XCIsIFwic2VsZWN0d29yZHJpZ2h0XCJdIH0sXG4gICAgXCJIb21lfEMtYVwiOiB7IGNvbW1hbmQ6IFwiZ29vcnNlbGVjdFwiLCBhcmdzOiBbXCJnb3RvbGluZXN0YXJ0XCIsIFwic2VsZWN0dG9saW5lc3RhcnRcIl0gfSxcbiAgICBcIkVuZHxDLWVcIjogeyBjb21tYW5kOiBcImdvb3JzZWxlY3RcIiwgYXJnczogW1wiZ290b2xpbmVlbmRcIiwgXCJzZWxlY3R0b2xpbmVlbmRcIl0gfSxcbiAgICBcIkMtSG9tZXxTLU0tLFwiOiB7IGNvbW1hbmQ6IFwiZ29vcnNlbGVjdFwiLCBhcmdzOiBbXCJnb3Rvc3RhcnRcIiwgXCJzZWxlY3R0b3N0YXJ0XCJdIH0sXG4gICAgXCJDLUVuZHxTLU0tLlwiOiB7IGNvbW1hbmQ6IFwiZ29vcnNlbGVjdFwiLCBhcmdzOiBbXCJnb3RvZW5kXCIsIFwic2VsZWN0dG9lbmRcIl0gfSxcbiAgICBcIlMtVXB8Uy1DLXBcIjogXCJzZWxlY3R1cFwiLFxuICAgIFwiUy1Eb3dufFMtQy1uXCI6IFwic2VsZWN0ZG93blwiLFxuICAgIFwiUy1MZWZ0fFMtQy1iXCI6IFwic2VsZWN0bGVmdFwiLFxuICAgIFwiUy1SaWdodHxTLUMtZlwiOiBcInNlbGVjdHJpZ2h0XCIsXG4gICAgXCJTLUMtTGVmdHxTLU0tYlwiOiBcInNlbGVjdHdvcmRsZWZ0XCIsXG4gICAgXCJTLUMtUmlnaHR8Uy1NLWZcIjogXCJzZWxlY3R3b3JkcmlnaHRcIixcbiAgICBcIlMtSG9tZXxTLUMtYVwiOiBcInNlbGVjdHRvbGluZXN0YXJ0XCIsXG4gICAgXCJTLUVuZHxTLUMtZVwiOiBcInNlbGVjdHRvbGluZWVuZFwiLFxuICAgIFwiUy1DLUhvbWVcIjogXCJzZWxlY3R0b3N0YXJ0XCIsXG4gICAgXCJTLUMtRW5kXCI6IFwic2VsZWN0dG9lbmRcIixcbiAgICBcIkMtbFwiOiBcInJlY2VudGVyVG9wQm90dG9tXCIsXG4gICAgXCJNLXNcIjogXCJjZW50ZXJzZWxlY3Rpb25cIixcbiAgICBcIk0tZ1wiOiBcImdvdG9saW5lXCIsXG4gICAgXCJDLXggQy1wXCI6IFwic2VsZWN0YWxsXCIsXG4gICAgXCJDLURvd25cIjogeyBjb21tYW5kOiBcImdvb3JzZWxlY3RcIiwgYXJnczogW1wiZ290b3BhZ2Vkb3duXCIsIFwic2VsZWN0cGFnZWRvd25cIl0gfSxcbiAgICBcIkMtVXBcIjogeyBjb21tYW5kOiBcImdvb3JzZWxlY3RcIiwgYXJnczogW1wiZ290b3BhZ2V1cFwiLCBcInNlbGVjdHBhZ2V1cFwiXSB9LFxuICAgIFwiUGFnZURvd258Qy12XCI6IHsgY29tbWFuZDogXCJnb29yc2VsZWN0XCIsIGFyZ3M6IFtcImdvdG9wYWdlZG93blwiLCBcInNlbGVjdHBhZ2Vkb3duXCJdIH0sXG4gICAgXCJQYWdlVXB8TS12XCI6IHsgY29tbWFuZDogXCJnb29yc2VsZWN0XCIsIGFyZ3M6IFtcImdvdG9wYWdldXBcIiwgXCJzZWxlY3RwYWdldXBcIl0gfSxcbiAgICBcIlMtQy1Eb3duXCI6IFwic2VsZWN0cGFnZWRvd25cIixcbiAgICBcIlMtQy1VcFwiOiBcInNlbGVjdHBhZ2V1cFwiLFxuICAgIFwiQy1zXCI6IFwiaVNlYXJjaFwiLFxuICAgIFwiQy1yXCI6IFwiaVNlYXJjaEJhY2t3YXJkc1wiLFxuICAgIFwiTS1DLXNcIjogXCJmaW5kbmV4dFwiLFxuICAgIFwiTS1DLXJcIjogXCJmaW5kcHJldmlvdXNcIixcbiAgICBcIlMtTS01XCI6IFwicmVwbGFjZVwiLFxuICAgIFwiQmFja3NwYWNlXCI6IFwiYmFja3NwYWNlXCIsXG4gICAgXCJEZWxldGV8Qy1kXCI6IFwiZGVsXCIsXG4gICAgXCJSZXR1cm58Qy1tXCI6IHsgY29tbWFuZDogXCJpbnNlcnRzdHJpbmdcIiwgYXJnczogXCJcXG5cIiB9LCAvLyBcIm5ld2xpbmVcIlxuICAgIFwiQy1vXCI6IFwic3BsaXRsaW5lXCIsXG4gICAgXCJNLWR8Qy1EZWxldGVcIjogeyBjb21tYW5kOiBcImtpbGxXb3JkXCIsIGFyZ3M6IFwicmlnaHRcIiB9LFxuICAgIFwiQy1CYWNrc3BhY2V8TS1CYWNrc3BhY2V8TS1EZWxldGVcIjogeyBjb21tYW5kOiBcImtpbGxXb3JkXCIsIGFyZ3M6IFwibGVmdFwiIH0sXG4gICAgXCJDLWtcIjogXCJraWxsTGluZVwiLFxuICAgIFwiQy15fFMtRGVsZXRlXCI6IFwieWFua1wiLFxuICAgIFwiTS15XCI6IFwieWFua1JvdGF0ZVwiLFxuICAgIFwiQy1nXCI6IFwia2V5Ym9hcmRRdWl0XCIsXG4gICAgXCJDLXd8Qy1TLVdcIjogXCJraWxsUmVnaW9uXCIsXG4gICAgXCJNLXdcIjogXCJraWxsUmluZ1NhdmVcIixcbiAgICBcIkMtU3BhY2VcIjogXCJzZXRNYXJrXCIsXG4gICAgXCJDLXggQy14XCI6IFwiZXhjaGFuZ2VQb2ludEFuZE1hcmtcIixcbiAgICBcIkMtdFwiOiBcInRyYW5zcG9zZWxldHRlcnNcIixcbiAgICBcIk0tdVwiOiBcInRvdXBwZXJjYXNlXCIsIC8vIERvZXNuJ3Qgd29ya1xuICAgIFwiTS1sXCI6IFwidG9sb3dlcmNhc2VcIixcbiAgICBcIk0tL1wiOiBcImF1dG9jb21wbGV0ZVwiLCAvLyBEb2Vzbid0IHdvcmtcbiAgICBcIkMtdVwiOiBcInVuaXZlcnNhbEFyZ3VtZW50XCIsXG4gICAgXCJNLTtcIjogXCJ0b2dnbGVjb21tZW50XCIsXG4gICAgXCJDLS98Qy14IHV8Uy1DLS18Qy16XCI6IFwidW5kb1wiLFxuICAgIFwiUy1DLS98Uy1DLXggdXxDLS18Uy1DLXpcIjogXCJyZWRvXCIsIC8vIGluZmluaXRlIHVuZG8/XG4gICAgXCJDLXggclwiOiBcInNlbGVjdFJlY3Rhbmd1bGFyUmVnaW9uXCIsXG4gICAgXCJNLXhcIjogeyBjb21tYW5kOiBcImZvY3VzQ29tbWFuZExpbmVcIiwgYXJnczogXCJNLXggXCIgfVxufTtcbmV4cG9ydHMuaGFuZGxlci5iaW5kS2V5cyhleHBvcnRzLmVtYWNzS2V5cyk7XG5leHBvcnRzLmhhbmRsZXIuYWRkQ29tbWFuZHMoe1xuICAgIHJlY2VudGVyVG9wQm90dG9tOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgIHZhciByZW5kZXJlciA9IGVkaXRvci5yZW5kZXJlcjtcbiAgICAgICAgdmFyIHBvcyA9IHJlbmRlcmVyLiRjdXJzb3JMYXllci5nZXRQaXhlbFBvc2l0aW9uKCk7XG4gICAgICAgIHZhciBoID0gcmVuZGVyZXIuJHNpemUuc2Nyb2xsZXJIZWlnaHQgLSByZW5kZXJlci5saW5lSGVpZ2h0O1xuICAgICAgICB2YXIgc2Nyb2xsVG9wID0gcmVuZGVyZXIuc2Nyb2xsVG9wO1xuICAgICAgICBpZiAoTWF0aC5hYnMocG9zLnRvcCAtIHNjcm9sbFRvcCkgPCAyKSB7XG4gICAgICAgICAgICBzY3JvbGxUb3AgPSBwb3MudG9wIC0gaDtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmIChNYXRoLmFicyhwb3MudG9wIC0gc2Nyb2xsVG9wIC0gaCAqIDAuNSkgPCAyKSB7XG4gICAgICAgICAgICBzY3JvbGxUb3AgPSBwb3MudG9wO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgc2Nyb2xsVG9wID0gcG9zLnRvcCAtIGggKiAwLjU7XG4gICAgICAgIH1cbiAgICAgICAgZWRpdG9yLnNlc3Npb24uc2V0U2Nyb2xsVG9wKHNjcm9sbFRvcCk7XG4gICAgfSxcbiAgICBzZWxlY3RSZWN0YW5ndWxhclJlZ2lvbjogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICBlZGl0b3IubXVsdGlTZWxlY3QudG9nZ2xlQmxvY2tTZWxlY3Rpb24oKTtcbiAgICB9LFxuICAgIHNldE1hcms6IHtcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvciwgYXJncykge1xuICAgICAgICAgICAgaWYgKGFyZ3MgJiYgYXJncy5jb3VudCkge1xuICAgICAgICAgICAgICAgIGlmIChlZGl0b3IuaW5NdWx0aVNlbGVjdE1vZGUpXG4gICAgICAgICAgICAgICAgICAgIGVkaXRvci5mb3JFYWNoU2VsZWN0aW9uKG1vdmVUb01hcmspO1xuICAgICAgICAgICAgICAgIGVsc2VcbiAgICAgICAgICAgICAgICAgICAgbW92ZVRvTWFyaygpO1xuICAgICAgICAgICAgICAgIG1vdmVUb01hcmsoKTtcbiAgICAgICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICB2YXIgbWFyayA9IGVkaXRvci5lbWFjc01hcmsoKSwgcmFuZ2VzID0gZWRpdG9yLnNlbGVjdGlvbi5nZXRBbGxSYW5nZXMoKSwgcmFuZ2VQb3NpdGlvbnMgPSByYW5nZXMubWFwKGZ1bmN0aW9uIChyKSB7IHJldHVybiB7IHJvdzogci5zdGFydC5yb3csIGNvbHVtbjogci5zdGFydC5jb2x1bW4gfTsgfSksIHRyYW5zaWVudE1hcmtNb2RlQWN0aXZlID0gdHJ1ZSwgaGFzTm9TZWxlY3Rpb24gPSByYW5nZXMuZXZlcnkoZnVuY3Rpb24gKHJhbmdlKSB7IHJldHVybiByYW5nZS5pc0VtcHR5KCk7IH0pO1xuICAgICAgICAgICAgaWYgKHRyYW5zaWVudE1hcmtNb2RlQWN0aXZlICYmIChtYXJrIHx8ICFoYXNOb1NlbGVjdGlvbikpIHtcbiAgICAgICAgICAgICAgICBpZiAoZWRpdG9yLmluTXVsdGlTZWxlY3RNb2RlKVxuICAgICAgICAgICAgICAgICAgICBlZGl0b3IuZm9yRWFjaFNlbGVjdGlvbih7IGV4ZWM6IGVkaXRvci5jbGVhclNlbGVjdGlvbi5iaW5kKGVkaXRvcikgfSk7XG4gICAgICAgICAgICAgICAgZWxzZVxuICAgICAgICAgICAgICAgICAgICBlZGl0b3IuY2xlYXJTZWxlY3Rpb24oKTtcbiAgICAgICAgICAgICAgICBpZiAobWFyaylcbiAgICAgICAgICAgICAgICAgICAgZWRpdG9yLnB1c2hFbWFjc01hcmsobnVsbCk7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKCFtYXJrKSB7XG4gICAgICAgICAgICAgICAgcmFuZ2VQb3NpdGlvbnMuZm9yRWFjaChmdW5jdGlvbiAocG9zKSB7IGVkaXRvci5wdXNoRW1hY3NNYXJrKHBvcyk7IH0pO1xuICAgICAgICAgICAgICAgIGVkaXRvci5zZXRFbWFjc01hcmsocmFuZ2VQb3NpdGlvbnNbcmFuZ2VQb3NpdGlvbnMubGVuZ3RoIC0gMV0pO1xuICAgICAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGZ1bmN0aW9uIG1vdmVUb01hcmsoKSB7XG4gICAgICAgICAgICAgICAgdmFyIG1hcmsgPSBlZGl0b3IucG9wRW1hY3NNYXJrKCk7XG4gICAgICAgICAgICAgICAgbWFyayAmJiBlZGl0b3IubW92ZUN1cnNvclRvUG9zaXRpb24obWFyayk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlLFxuICAgICAgICBoYW5kbGVzQ291bnQ6IHRydWVcbiAgICB9LFxuICAgIGV4Y2hhbmdlUG9pbnRBbmRNYXJrOiB7XG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIGV4Y2hhbmdlUG9pbnRBbmRNYXJrJGV4ZWMoZWRpdG9yLCBhcmdzKSB7XG4gICAgICAgICAgICB2YXIgc2VsID0gZWRpdG9yLnNlbGVjdGlvbjtcbiAgICAgICAgICAgIGlmICghYXJncy5jb3VudCAmJiAhc2VsLmlzRW1wdHkoKSkgeyAvLyBqdXN0IGludmVydCBzZWxlY3Rpb25cbiAgICAgICAgICAgICAgICBzZWwuc2V0U2VsZWN0aW9uUmFuZ2Uoc2VsLmdldFJhbmdlKCksICFzZWwuaXNCYWNrd2FyZHMoKSk7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKGFyZ3MuY291bnQpIHsgLy8gcmVwbGFjZSBtYXJrIGFuZCBwb2ludFxuICAgICAgICAgICAgICAgIHZhciBwb3MgPSB7IHJvdzogc2VsLmxlYWQucm93LCBjb2x1bW46IHNlbC5sZWFkLmNvbHVtbiB9O1xuICAgICAgICAgICAgICAgIHNlbC5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICAgICAgICAgIHNlbC5tb3ZlQ3Vyc29yVG9Qb3NpdGlvbihlZGl0b3IuZW1hY3NNYXJrRm9yU2VsZWN0aW9uKHBvcykpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7IC8vIGNyZWF0ZSBzZWxlY3Rpb24gdG8gbGFzdCBtYXJrXG4gICAgICAgICAgICAgICAgc2VsLnNlbGVjdFRvUG9zaXRpb24oZWRpdG9yLmVtYWNzTWFya0ZvclNlbGVjdGlvbigpKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfSxcbiAgICAgICAgcmVhZE9ubHk6IHRydWUsXG4gICAgICAgIGhhbmRsZXNDb3VudDogdHJ1ZSxcbiAgICAgICAgbXVsdGlTZWxlY3RBY3Rpb246IFwiZm9yRWFjaFwiXG4gICAgfSxcbiAgICBraWxsV29yZDoge1xuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yLCBkaXIpIHtcbiAgICAgICAgICAgIGVkaXRvci5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICAgICAgaWYgKGRpciA9PSBcImxlZnRcIilcbiAgICAgICAgICAgICAgICBlZGl0b3Iuc2VsZWN0aW9uLnNlbGVjdFdvcmRMZWZ0KCk7XG4gICAgICAgICAgICBlbHNlXG4gICAgICAgICAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi5zZWxlY3RXb3JkUmlnaHQoKTtcbiAgICAgICAgICAgIHZhciByYW5nZSA9IGVkaXRvci5nZXRTZWxlY3Rpb25SYW5nZSgpO1xuICAgICAgICAgICAgdmFyIHRleHQgPSBlZGl0b3Iuc2Vzc2lvbi5nZXRUZXh0UmFuZ2UocmFuZ2UpO1xuICAgICAgICAgICAgZXhwb3J0cy5raWxsUmluZy5hZGQodGV4dCk7XG4gICAgICAgICAgICBlZGl0b3Iuc2Vzc2lvbi5yZW1vdmUocmFuZ2UpO1xuICAgICAgICAgICAgZWRpdG9yLmNsZWFyU2VsZWN0aW9uKCk7XG4gICAgICAgIH0sXG4gICAgICAgIG11bHRpU2VsZWN0QWN0aW9uOiBcImZvckVhY2hcIlxuICAgIH0sXG4gICAga2lsbExpbmU6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgZWRpdG9yLnB1c2hFbWFjc01hcmsobnVsbCk7XG4gICAgICAgIGVkaXRvci5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICB2YXIgcmFuZ2UgPSBlZGl0b3IuZ2V0U2VsZWN0aW9uUmFuZ2UoKTtcbiAgICAgICAgdmFyIGxpbmUgPSBlZGl0b3Iuc2Vzc2lvbi5nZXRMaW5lKHJhbmdlLnN0YXJ0LnJvdyk7XG4gICAgICAgIHJhbmdlLmVuZC5jb2x1bW4gPSBsaW5lLmxlbmd0aDtcbiAgICAgICAgbGluZSA9IGxpbmUuc3Vic3RyKHJhbmdlLnN0YXJ0LmNvbHVtbik7XG4gICAgICAgIHZhciBmb2xkTGluZSA9IGVkaXRvci5zZXNzaW9uLmdldEZvbGRMaW5lKHJhbmdlLnN0YXJ0LnJvdyk7XG4gICAgICAgIGlmIChmb2xkTGluZSAmJiByYW5nZS5lbmQucm93ICE9IGZvbGRMaW5lLmVuZC5yb3cpIHtcbiAgICAgICAgICAgIHJhbmdlLmVuZC5yb3cgPSBmb2xkTGluZS5lbmQucm93O1xuICAgICAgICAgICAgbGluZSA9IFwieFwiO1xuICAgICAgICB9XG4gICAgICAgIGlmICgvXlxccyokLy50ZXN0KGxpbmUpKSB7XG4gICAgICAgICAgICByYW5nZS5lbmQucm93Kys7XG4gICAgICAgICAgICBsaW5lID0gZWRpdG9yLnNlc3Npb24uZ2V0TGluZShyYW5nZS5lbmQucm93KTtcbiAgICAgICAgICAgIHJhbmdlLmVuZC5jb2x1bW4gPSAvXlxccyokLy50ZXN0KGxpbmUpID8gbGluZS5sZW5ndGggOiAwO1xuICAgICAgICB9XG4gICAgICAgIHZhciB0ZXh0ID0gZWRpdG9yLnNlc3Npb24uZ2V0VGV4dFJhbmdlKHJhbmdlKTtcbiAgICAgICAgaWYgKGVkaXRvci5wcmV2T3AuY29tbWFuZCA9PSB0aGlzKVxuICAgICAgICAgICAgZXhwb3J0cy5raWxsUmluZy5hcHBlbmQodGV4dCk7XG4gICAgICAgIGVsc2VcbiAgICAgICAgICAgIGV4cG9ydHMua2lsbFJpbmcuYWRkKHRleHQpO1xuICAgICAgICBlZGl0b3Iuc2Vzc2lvbi5yZW1vdmUocmFuZ2UpO1xuICAgICAgICBlZGl0b3IuY2xlYXJTZWxlY3Rpb24oKTtcbiAgICB9LFxuICAgIHlhbms6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgZWRpdG9yLm9uUGFzdGUoZXhwb3J0cy5raWxsUmluZy5nZXQoKSB8fCAnJyk7XG4gICAgICAgIGVkaXRvci5rZXlCaW5kaW5nLiRkYXRhLmxhc3RDb21tYW5kID0gXCJ5YW5rXCI7XG4gICAgfSxcbiAgICB5YW5rUm90YXRlOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgIGlmIChlZGl0b3Iua2V5QmluZGluZy4kZGF0YS5sYXN0Q29tbWFuZCAhPSBcInlhbmtcIilcbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgZWRpdG9yLnVuZG8oKTtcbiAgICAgICAgZWRpdG9yLnNlc3Npb24uJGVtYWNzTWFya1JpbmcucG9wKCk7IC8vIGFsc28gdW5kbyByZWNvcmRpbmcgbWFya1xuICAgICAgICBlZGl0b3Iub25QYXN0ZShleHBvcnRzLmtpbGxSaW5nLnJvdGF0ZSgpKTtcbiAgICAgICAgZWRpdG9yLmtleUJpbmRpbmcuJGRhdGEubGFzdENvbW1hbmQgPSBcInlhbmtcIjtcbiAgICB9LFxuICAgIGtpbGxSZWdpb246IHtcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgZXhwb3J0cy5raWxsUmluZy5hZGQoZWRpdG9yLmdldENvcHlUZXh0KCkpO1xuICAgICAgICAgICAgZWRpdG9yLmNvbW1hbmRzLmJ5TmFtZS5jdXQuZXhlYyhlZGl0b3IpO1xuICAgICAgICAgICAgZWRpdG9yLnNldEVtYWNzTWFyayhudWxsKTtcbiAgICAgICAgfSxcbiAgICAgICAgcmVhZE9ubHk6IHRydWUsXG4gICAgICAgIG11bHRpU2VsZWN0QWN0aW9uOiBcImZvckVhY2hcIlxuICAgIH0sXG4gICAga2lsbFJpbmdTYXZlOiB7XG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIGVkaXRvci4kaGFuZGxlc0VtYWNzT25Db3B5ID0gdHJ1ZTtcbiAgICAgICAgICAgIHZhciBtYXJrcyA9IGVkaXRvci5zZXNzaW9uLiRlbWFjc01hcmtSaW5nLnNsaWNlKCksIGRlc2VsZWN0ZWRNYXJrcyA9IFtdO1xuICAgICAgICAgICAgZXhwb3J0cy5raWxsUmluZy5hZGQoZWRpdG9yLmdldENvcHlUZXh0KCkpO1xuICAgICAgICAgICAgc2V0VGltZW91dChmdW5jdGlvbiAoKSB7XG4gICAgICAgICAgICAgICAgZnVuY3Rpb24gZGVzZWxlY3QoKSB7XG4gICAgICAgICAgICAgICAgICAgIHZhciBzZWwgPSBlZGl0b3Iuc2VsZWN0aW9uLCByYW5nZSA9IHNlbC5nZXRSYW5nZSgpLCBwb3MgPSBzZWwuaXNCYWNrd2FyZHMoKSA/IHJhbmdlLmVuZCA6IHJhbmdlLnN0YXJ0O1xuICAgICAgICAgICAgICAgICAgICBkZXNlbGVjdGVkTWFya3MucHVzaCh7IHJvdzogcG9zLnJvdywgY29sdW1uOiBwb3MuY29sdW1uIH0pO1xuICAgICAgICAgICAgICAgICAgICBzZWwuY2xlYXJTZWxlY3Rpb24oKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWRpdG9yLiRoYW5kbGVzRW1hY3NPbkNvcHkgPSBmYWxzZTtcbiAgICAgICAgICAgICAgICBpZiAoZWRpdG9yLmluTXVsdGlTZWxlY3RNb2RlKVxuICAgICAgICAgICAgICAgICAgICBlZGl0b3IuZm9yRWFjaFNlbGVjdGlvbih7IGV4ZWM6IGRlc2VsZWN0IH0pO1xuICAgICAgICAgICAgICAgIGVsc2VcbiAgICAgICAgICAgICAgICAgICAgZGVzZWxlY3QoKTtcbiAgICAgICAgICAgICAgICBlZGl0b3Iuc2V0RW1hY3NNYXJrKG51bGwpO1xuICAgICAgICAgICAgICAgIGVkaXRvci5zZXNzaW9uLiRlbWFjc01hcmtSaW5nID0gbWFya3MuY29uY2F0KGRlc2VsZWN0ZWRNYXJrcy5yZXZlcnNlKCkpO1xuICAgICAgICAgICAgfSwgMCk7XG4gICAgICAgIH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfSxcbiAgICBrZXlib2FyZFF1aXQ6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICBlZGl0b3Iuc2V0RW1hY3NNYXJrKG51bGwpO1xuICAgICAgICBlZGl0b3Iua2V5QmluZGluZy4kZGF0YS5jb3VudCA9IG51bGw7XG4gICAgfSxcbiAgICBmb2N1c0NvbW1hbmRMaW5lOiBmdW5jdGlvbiAoZWRpdG9yLCBhcmcpIHtcbiAgICAgICAgaWYgKGVkaXRvci5zaG93Q29tbWFuZExpbmUpXG4gICAgICAgICAgICBlZGl0b3Iuc2hvd0NvbW1hbmRMaW5lKGFyZyk7XG4gICAgfVxufSk7XG5leHBvcnRzLmhhbmRsZXIuYWRkQ29tbWFuZHMoaVNlYXJjaENvbW1hbmRNb2R1bGUuaVNlYXJjaFN0YXJ0Q29tbWFuZHMpO1xudmFyIGNvbW1hbmRzID0gZXhwb3J0cy5oYW5kbGVyLmNvbW1hbmRzO1xuY29tbWFuZHMueWFuay5pc1lhbmsgPSB0cnVlO1xuY29tbWFuZHMueWFua1JvdGF0ZS5pc1lhbmsgPSB0cnVlO1xuZXhwb3J0cy5raWxsUmluZyA9IHtcbiAgICAkZGF0YTogW10sXG4gICAgYWRkOiBmdW5jdGlvbiAoc3RyKSB7XG4gICAgICAgIHN0ciAmJiB0aGlzLiRkYXRhLnB1c2goc3RyKTtcbiAgICAgICAgaWYgKHRoaXMuJGRhdGEubGVuZ3RoID4gMzApXG4gICAgICAgICAgICB0aGlzLiRkYXRhLnNoaWZ0KCk7XG4gICAgfSxcbiAgICBhcHBlbmQ6IGZ1bmN0aW9uIChzdHIpIHtcbiAgICAgICAgdmFyIGlkeCA9IHRoaXMuJGRhdGEubGVuZ3RoIC0gMTtcbiAgICAgICAgdmFyIHRleHQgPSB0aGlzLiRkYXRhW2lkeF0gfHwgXCJcIjtcbiAgICAgICAgaWYgKHN0cilcbiAgICAgICAgICAgIHRleHQgKz0gc3RyO1xuICAgICAgICBpZiAodGV4dClcbiAgICAgICAgICAgIHRoaXMuJGRhdGFbaWR4XSA9IHRleHQ7XG4gICAgfSxcbiAgICBnZXQ6IGZ1bmN0aW9uIChuKSB7XG4gICAgICAgIG4gPSBuIHx8IDE7XG4gICAgICAgIHJldHVybiB0aGlzLiRkYXRhLnNsaWNlKHRoaXMuJGRhdGEubGVuZ3RoIC0gbiwgdGhpcy4kZGF0YS5sZW5ndGgpLnJldmVyc2UoKS5qb2luKCdcXG4nKTtcbiAgICB9LFxuICAgIHBvcDogZnVuY3Rpb24gKCkge1xuICAgICAgICBpZiAodGhpcy4kZGF0YS5sZW5ndGggPiAxKVxuICAgICAgICAgICAgdGhpcy4kZGF0YS5wb3AoKTtcbiAgICAgICAgcmV0dXJuIHRoaXMuZ2V0KCk7XG4gICAgfSxcbiAgICByb3RhdGU6IGZ1bmN0aW9uICgpIHtcbiAgICAgICAgdGhpcy4kZGF0YS51bnNoaWZ0KHRoaXMuJGRhdGEucG9wKCkpO1xuICAgICAgICByZXR1cm4gdGhpcy5nZXQoKTtcbiAgICB9XG59O1xuXG59KTsgICAgICAgICAgICAgICAgKGZ1bmN0aW9uKCkge1xuICAgICAgICAgICAgICAgICAgICBhY2UucmVxdWlyZShbXCJhY2Uva2V5Ym9hcmQvZW1hY3NcIl0sIGZ1bmN0aW9uKG0pIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICh0eXBlb2YgbW9kdWxlID09IFwib2JqZWN0XCIgJiYgdHlwZW9mIGV4cG9ydHMgPT0gXCJvYmplY3RcIiAmJiBtb2R1bGUpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2R1bGUuZXhwb3J0cyA9IG07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgIH0pKCk7XG4gICAgICAgICAgICAiXSwibmFtZXMiOltdLCJzb3VyY2VSb290IjoiIn0=