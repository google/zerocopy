(globalThis["webpackChunkui"] = globalThis["webpackChunkui"] || []).push([["ace-keybinding-sublime"],{

/***/ "./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-sublime.js"
/*!***********************************************************************************************************!*\
  !*** ./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-sublime.js ***!
  \***********************************************************************************************************/
(module, __unused_webpack_exports, __webpack_require__) {

/* module decorator */ module = __webpack_require__.nmd(module);
ace.define("ace/keyboard/sublime",["require","exports","module","ace/keyboard/hash_handler"], function(require, exports, module){"use strict";
var HashHandler = require("../keyboard/hash_handler").HashHandler;
function moveBySubWords(editor, direction, extend) {
    var selection = editor.selection;
    var row = selection.lead.row;
    var column = selection.lead.column;
    var line = editor.session.getLine(row);
    if (!line[column + direction]) {
        var method = (extend ? "selectWord" : "moveCursorShortWord")
            + (direction == 1 ? "Right" : "Left");
        return editor.selection[method]();
    }
    if (direction == -1)
        column--;
    while (line[column]) {
        var type = getType(line[column]) + getType(line[column + direction]);
        column += direction;
        if (direction == 1) {
            if (type == "WW" && getType(line[column + 1]) == "w")
                break;
        }
        else {
            if (type == "wW") {
                if (getType(line[column - 1]) == "W") {
                    column -= 1;
                    break;
                }
                else {
                    continue;
                }
            }
            if (type == "Ww")
                break;
        }
        if (/w[s_oW]|_[sWo]|o[s_wW]|s[W]|W[so]/.test(type))
            break;
    }
    if (direction == -1)
        column++;
    if (extend)
        editor.selection.moveCursorTo(row, column);
    else
        editor.selection.moveTo(row, column);
    function getType(x) {
        if (!x)
            return "-";
        if (/\s/.test(x))
            return "s";
        if (x == "_")
            return "_";
        if (x.toUpperCase() == x && x.toLowerCase() != x)
            return "W";
        if (x.toUpperCase() != x && x.toLowerCase() == x)
            return "w";
        return "o";
    }
}
exports.handler = new HashHandler();
exports.handler.addCommands([{
        name: "find_all_under",
        exec: function (editor) {
            if (editor.selection.isEmpty())
                editor.selection.selectWord();
            editor.findAll();
        },
        readOnly: true
    }, {
        name: "find_under",
        exec: function (editor) {
            if (editor.selection.isEmpty())
                editor.selection.selectWord();
            editor.findNext();
        },
        readOnly: true
    }, {
        name: "find_under_prev",
        exec: function (editor) {
            if (editor.selection.isEmpty())
                editor.selection.selectWord();
            editor.findPrevious();
        },
        readOnly: true
    }, {
        name: "find_under_expand",
        exec: function (editor) {
            editor.selectMore(1, false, true);
        },
        scrollIntoView: "animate",
        readOnly: true
    }, {
        name: "find_under_expand_skip",
        exec: function (editor) {
            editor.selectMore(1, true, true);
        },
        scrollIntoView: "animate",
        readOnly: true
    }, {
        name: "delete_to_hard_bol",
        exec: function (editor) {
            var pos = editor.selection.getCursor();
            editor.session.remove({
                start: { row: pos.row, column: 0 },
                end: pos
            });
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "delete_to_hard_eol",
        exec: function (editor) {
            var pos = editor.selection.getCursor();
            editor.session.remove({
                start: pos,
                end: { row: pos.row, column: Infinity }
            });
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "moveToWordStartLeft",
        exec: function (editor) {
            editor.selection.moveCursorLongWordLeft();
            editor.clearSelection();
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "moveToWordEndRight",
        exec: function (editor) {
            editor.selection.moveCursorLongWordRight();
            editor.clearSelection();
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "selectToWordStartLeft",
        exec: function (editor) {
            var sel = editor.selection;
            sel.$moveSelection(sel.moveCursorLongWordLeft);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "selectToWordEndRight",
        exec: function (editor) {
            var sel = editor.selection;
            sel.$moveSelection(sel.moveCursorLongWordRight);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor"
    }, {
        name: "selectSubWordRight",
        exec: function (editor) {
            moveBySubWords(editor, 1, true);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor",
        readOnly: true
    }, {
        name: "selectSubWordLeft",
        exec: function (editor) {
            moveBySubWords(editor, -1, true);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor",
        readOnly: true
    }, {
        name: "moveSubWordRight",
        exec: function (editor) {
            moveBySubWords(editor, 1);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor",
        readOnly: true
    }, {
        name: "moveSubWordLeft",
        exec: function (editor) {
            moveBySubWords(editor, -1);
        },
        multiSelectAction: "forEach",
        scrollIntoView: "cursor",
        readOnly: true
    }]);
[{
        bindKey: { mac: "cmd-k cmd-backspace|cmd-backspace", win: "ctrl-shift-backspace|ctrl-k ctrl-backspace" },
        name: "removetolinestarthard"
    }, {
        bindKey: { mac: "cmd-k cmd-k|cmd-delete|ctrl-k", win: "ctrl-shift-delete|ctrl-k ctrl-k" },
        name: "removetolineendhard"
    }, {
        bindKey: { mac: "cmd-shift-d", win: "ctrl-shift-d" },
        name: "duplicateSelection"
    }, {
        bindKey: { mac: "cmd-l", win: "ctrl-l" },
        name: "expandtoline"
    },
    {
        bindKey: { mac: "cmd-shift-a", win: "ctrl-shift-a" },
        name: "expandSelection",
        args: { to: "tag" }
    }, {
        bindKey: { mac: "cmd-shift-j", win: "ctrl-shift-j" },
        name: "expandSelection",
        args: { to: "indentation" }
    }, {
        bindKey: { mac: "ctrl-shift-m", win: "ctrl-shift-m" },
        name: "expandSelection",
        args: { to: "brackets" }
    }, {
        bindKey: { mac: "cmd-shift-space", win: "ctrl-shift-space" },
        name: "expandSelection",
        args: { to: "scope" }
    },
    {
        bindKey: { mac: "ctrl-cmd-g", win: "alt-f3" },
        name: "find_all_under"
    }, {
        bindKey: { mac: "alt-cmd-g", win: "ctrl-f3" },
        name: "find_under"
    }, {
        bindKey: { mac: "shift-alt-cmd-g", win: "ctrl-shift-f3" },
        name: "find_under_prev"
    }, {
        bindKey: { mac: "cmd-g", win: "f3" },
        name: "findnext"
    }, {
        bindKey: { mac: "shift-cmd-g", win: "shift-f3" },
        name: "findprevious"
    }, {
        bindKey: { mac: "cmd-d", win: "ctrl-d" },
        name: "find_under_expand"
    }, {
        bindKey: { mac: "cmd-k cmd-d", win: "ctrl-k ctrl-d" },
        name: "find_under_expand_skip"
    },
    {
        bindKey: { mac: "cmd-alt-[", win: "ctrl-shift-[" },
        name: "toggleFoldWidget"
    }, {
        bindKey: { mac: "cmd-alt-]", win: "ctrl-shift-]" },
        name: "unfold"
    }, {
        bindKey: { mac: "cmd-k cmd-0|cmd-k cmd-j", win: "ctrl-k ctrl-0|ctrl-k ctrl-j" },
        name: "unfoldall"
    }, {
        bindKey: { mac: "cmd-k cmd-1", win: "ctrl-k ctrl-1" },
        name: "foldOther",
        args: { level: 1 }
    },
    {
        bindKey: { win: "ctrl-left", mac: "alt-left" },
        name: "moveToWordStartLeft"
    }, {
        bindKey: { win: "ctrl-right", mac: "alt-right" },
        name: "moveToWordEndRight"
    }, {
        bindKey: { win: "ctrl-shift-left", mac: "alt-shift-left" },
        name: "selectToWordStartLeft"
    }, {
        bindKey: { win: "ctrl-shift-right", mac: "alt-shift-right" },
        name: "selectToWordEndRight"
    },
    {
        bindKey: { mac: "ctrl-alt-shift-right|ctrl-shift-right", win: "alt-shift-right" },
        name: "selectSubWordRight"
    }, {
        bindKey: { mac: "ctrl-alt-shift-left|ctrl-shift-left", win: "alt-shift-left" },
        name: "selectSubWordLeft"
    }, {
        bindKey: { mac: "ctrl-alt-right|ctrl-right", win: "alt-right" },
        name: "moveSubWordRight"
    }, {
        bindKey: { mac: "ctrl-alt-left|ctrl-left", win: "alt-left" },
        name: "moveSubWordLeft"
    },
    {
        bindKey: { mac: "ctrl-m", win: "ctrl-m" },
        name: "jumptomatching",
        args: { to: "brackets" }
    },
    {
        bindKey: { mac: "ctrl-f6", win: "ctrl-f6" },
        name: "goToNextError"
    }, {
        bindKey: { mac: "ctrl-shift-f6", win: "ctrl-shift-f6" },
        name: "goToPreviousError"
    },
    {
        bindKey: { mac: "ctrl-o" },
        name: "splitline"
    },
    {
        bindKey: { mac: "ctrl-shift-w", win: "alt-shift-w" },
        name: "surrowndWithTag"
    }, {
        bindKey: { mac: "cmd-alt-.", win: "alt-." },
        name: "close_tag"
    },
    {
        bindKey: { mac: "cmd-j", win: "ctrl-j" },
        name: "joinlines"
    },
    {
        bindKey: { mac: "ctrl--", win: "alt--" },
        name: "jumpBack"
    }, {
        bindKey: { mac: "ctrl-shift--", win: "alt-shift--" },
        name: "jumpForward"
    },
    {
        bindKey: { mac: "cmd-k cmd-l", win: "ctrl-k ctrl-l" },
        name: "tolowercase"
    }, {
        bindKey: { mac: "cmd-k cmd-u", win: "ctrl-k ctrl-u" },
        name: "touppercase"
    },
    {
        bindKey: { mac: "cmd-shift-v", win: "ctrl-shift-v" },
        name: "paste_and_indent"
    }, {
        bindKey: { mac: "cmd-k cmd-v|cmd-alt-v", win: "ctrl-k ctrl-v" },
        name: "paste_from_history"
    },
    {
        bindKey: { mac: "cmd-shift-enter", win: "ctrl-shift-enter" },
        name: "addLineBefore"
    }, {
        bindKey: { mac: "cmd-enter", win: "ctrl-enter" },
        name: "addLineAfter"
    }, {
        bindKey: { mac: "ctrl-shift-k", win: "ctrl-shift-k" },
        name: "removeline"
    }, {
        bindKey: { mac: "ctrl-alt-up", win: "ctrl-up" },
        name: "scrollup"
    }, {
        bindKey: { mac: "ctrl-alt-down", win: "ctrl-down" },
        name: "scrolldown"
    }, {
        bindKey: { mac: "cmd-a", win: "ctrl-a" },
        name: "selectall"
    }, {
        bindKey: { linux: "alt-shift-down", mac: "ctrl-shift-down", win: "ctrl-alt-down" },
        name: "addCursorBelow"
    }, {
        bindKey: { linux: "alt-shift-up", mac: "ctrl-shift-up", win: "ctrl-alt-up" },
        name: "addCursorAbove"
    },
    {
        bindKey: { mac: "cmd-k cmd-c|ctrl-l", win: "ctrl-k ctrl-c" },
        name: "centerselection"
    },
    {
        bindKey: { mac: "f5", win: "f9" },
        name: "sortlines"
    },
    {
        bindKey: { mac: "ctrl-f5", win: "ctrl-f9" },
        name: "sortlines",
        args: { caseSensitive: true }
    },
    {
        bindKey: { mac: "cmd-shift-l", win: "ctrl-shift-l" },
        name: "splitSelectionIntoLines"
    }, {
        bindKey: { mac: "ctrl-cmd-down", win: "ctrl-shift-down" },
        name: "movelinesdown"
    }, {
        bindKey: { mac: "ctrl-cmd-up", win: "ctrl-shift-up" },
        name: "movelinesup"
    }, {
        bindKey: { mac: "alt-down", win: "alt-down" },
        name: "modifyNumberDown"
    }, {
        bindKey: { mac: "alt-up", win: "alt-up" },
        name: "modifyNumberUp"
    }, {
        bindKey: { mac: "cmd-/", win: "ctrl-/" },
        name: "togglecomment"
    }, {
        bindKey: { mac: "cmd-alt-/", win: "ctrl-shift-/" },
        name: "toggleBlockComment"
    },
    {
        bindKey: { linux: "ctrl-alt-q", mac: "ctrl-q", win: "ctrl-q" },
        name: "togglerecording"
    }, {
        bindKey: { linux: "ctrl-alt-shift-q", mac: "ctrl-shift-q", win: "ctrl-shift-q" },
        name: "replaymacro"
    },
    {
        bindKey: { mac: "ctrl-t", win: "ctrl-t" },
        name: "transpose"
    }
].forEach(function (binding) {
    var command = exports.handler.commands[binding.name];
    if (command)
        command.bindKey = binding.bindKey;
    exports.handler.bindKey(binding.bindKey, command || binding.name);
});

});                (function() {
                    ace.require(["ace/keyboard/sublime"], function(m) {
                        if ( true && module) {
                            module.exports = m;
                        }
                    });
                })();
            

/***/ }

}]);
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYWNlLWtleWJpbmRpbmctc3VibGltZS05MTQ1MGJkMzk4NmQ3OTg4YTRiYS5qcyIsIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7QUFBQSxpSUFBaUk7QUFDakk7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsU0FBUztBQUNUO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLHlCQUF5Qix5QkFBeUI7QUFDbEQ7QUFDQSxhQUFhO0FBQ2IsU0FBUztBQUNUO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLHVCQUF1QjtBQUN2QixhQUFhO0FBQ2IsU0FBUztBQUNUO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVM7QUFDVDtBQUNBO0FBQ0EsS0FBSztBQUNM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bkY7QUFDQTtBQUNBLHFCQUFxQjtBQUNyQixpQkFBaUI7QUFDakIsWSIsInNvdXJjZXMiOlsid2VicGFjazovL3VpLy4vbm9kZV9tb2R1bGVzLy5wbnBtL2FjZS1idWlsZHNAMS40My42L25vZGVfbW9kdWxlcy9hY2UtYnVpbGRzL3NyYy1ub2NvbmZsaWN0L2tleWJpbmRpbmctc3VibGltZS5qcyJdLCJzb3VyY2VzQ29udGVudCI6WyJhY2UuZGVmaW5lKFwiYWNlL2tleWJvYXJkL3N1YmxpbWVcIixbXCJyZXF1aXJlXCIsXCJleHBvcnRzXCIsXCJtb2R1bGVcIixcImFjZS9rZXlib2FyZC9oYXNoX2hhbmRsZXJcIl0sIGZ1bmN0aW9uKHJlcXVpcmUsIGV4cG9ydHMsIG1vZHVsZSl7XCJ1c2Ugc3RyaWN0XCI7XG52YXIgSGFzaEhhbmRsZXIgPSByZXF1aXJlKFwiLi4va2V5Ym9hcmQvaGFzaF9oYW5kbGVyXCIpLkhhc2hIYW5kbGVyO1xuZnVuY3Rpb24gbW92ZUJ5U3ViV29yZHMoZWRpdG9yLCBkaXJlY3Rpb24sIGV4dGVuZCkge1xuICAgIHZhciBzZWxlY3Rpb24gPSBlZGl0b3Iuc2VsZWN0aW9uO1xuICAgIHZhciByb3cgPSBzZWxlY3Rpb24ubGVhZC5yb3c7XG4gICAgdmFyIGNvbHVtbiA9IHNlbGVjdGlvbi5sZWFkLmNvbHVtbjtcbiAgICB2YXIgbGluZSA9IGVkaXRvci5zZXNzaW9uLmdldExpbmUocm93KTtcbiAgICBpZiAoIWxpbmVbY29sdW1uICsgZGlyZWN0aW9uXSkge1xuICAgICAgICB2YXIgbWV0aG9kID0gKGV4dGVuZCA/IFwic2VsZWN0V29yZFwiIDogXCJtb3ZlQ3Vyc29yU2hvcnRXb3JkXCIpXG4gICAgICAgICAgICArIChkaXJlY3Rpb24gPT0gMSA/IFwiUmlnaHRcIiA6IFwiTGVmdFwiKTtcbiAgICAgICAgcmV0dXJuIGVkaXRvci5zZWxlY3Rpb25bbWV0aG9kXSgpO1xuICAgIH1cbiAgICBpZiAoZGlyZWN0aW9uID09IC0xKVxuICAgICAgICBjb2x1bW4tLTtcbiAgICB3aGlsZSAobGluZVtjb2x1bW5dKSB7XG4gICAgICAgIHZhciB0eXBlID0gZ2V0VHlwZShsaW5lW2NvbHVtbl0pICsgZ2V0VHlwZShsaW5lW2NvbHVtbiArIGRpcmVjdGlvbl0pO1xuICAgICAgICBjb2x1bW4gKz0gZGlyZWN0aW9uO1xuICAgICAgICBpZiAoZGlyZWN0aW9uID09IDEpIHtcbiAgICAgICAgICAgIGlmICh0eXBlID09IFwiV1dcIiAmJiBnZXRUeXBlKGxpbmVbY29sdW1uICsgMV0pID09IFwid1wiKVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgaWYgKHR5cGUgPT0gXCJ3V1wiKSB7XG4gICAgICAgICAgICAgICAgaWYgKGdldFR5cGUobGluZVtjb2x1bW4gLSAxXSkgPT0gXCJXXCIpIHtcbiAgICAgICAgICAgICAgICAgICAgY29sdW1uIC09IDE7XG4gICAgICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgaWYgKHR5cGUgPT0gXCJXd1wiKVxuICAgICAgICAgICAgICAgIGJyZWFrO1xuICAgICAgICB9XG4gICAgICAgIGlmICgvd1tzX29XXXxfW3NXb118b1tzX3dXXXxzW1ddfFdbc29dLy50ZXN0KHR5cGUpKVxuICAgICAgICAgICAgYnJlYWs7XG4gICAgfVxuICAgIGlmIChkaXJlY3Rpb24gPT0gLTEpXG4gICAgICAgIGNvbHVtbisrO1xuICAgIGlmIChleHRlbmQpXG4gICAgICAgIGVkaXRvci5zZWxlY3Rpb24ubW92ZUN1cnNvclRvKHJvdywgY29sdW1uKTtcbiAgICBlbHNlXG4gICAgICAgIGVkaXRvci5zZWxlY3Rpb24ubW92ZVRvKHJvdywgY29sdW1uKTtcbiAgICBmdW5jdGlvbiBnZXRUeXBlKHgpIHtcbiAgICAgICAgaWYgKCF4KVxuICAgICAgICAgICAgcmV0dXJuIFwiLVwiO1xuICAgICAgICBpZiAoL1xccy8udGVzdCh4KSlcbiAgICAgICAgICAgIHJldHVybiBcInNcIjtcbiAgICAgICAgaWYgKHggPT0gXCJfXCIpXG4gICAgICAgICAgICByZXR1cm4gXCJfXCI7XG4gICAgICAgIGlmICh4LnRvVXBwZXJDYXNlKCkgPT0geCAmJiB4LnRvTG93ZXJDYXNlKCkgIT0geClcbiAgICAgICAgICAgIHJldHVybiBcIldcIjtcbiAgICAgICAgaWYgKHgudG9VcHBlckNhc2UoKSAhPSB4ICYmIHgudG9Mb3dlckNhc2UoKSA9PSB4KVxuICAgICAgICAgICAgcmV0dXJuIFwid1wiO1xuICAgICAgICByZXR1cm4gXCJvXCI7XG4gICAgfVxufVxuZXhwb3J0cy5oYW5kbGVyID0gbmV3IEhhc2hIYW5kbGVyKCk7XG5leHBvcnRzLmhhbmRsZXIuYWRkQ29tbWFuZHMoW3tcbiAgICAgICAgbmFtZTogXCJmaW5kX2FsbF91bmRlclwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBpZiAoZWRpdG9yLnNlbGVjdGlvbi5pc0VtcHR5KCkpXG4gICAgICAgICAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi5zZWxlY3RXb3JkKCk7XG4gICAgICAgICAgICBlZGl0b3IuZmluZEFsbCgpO1xuICAgICAgICB9LFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJmaW5kX3VuZGVyXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIGlmIChlZGl0b3Iuc2VsZWN0aW9uLmlzRW1wdHkoKSlcbiAgICAgICAgICAgICAgICBlZGl0b3Iuc2VsZWN0aW9uLnNlbGVjdFdvcmQoKTtcbiAgICAgICAgICAgIGVkaXRvci5maW5kTmV4dCgpO1xuICAgICAgICB9LFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJmaW5kX3VuZGVyX3ByZXZcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgaWYgKGVkaXRvci5zZWxlY3Rpb24uaXNFbXB0eSgpKVxuICAgICAgICAgICAgICAgIGVkaXRvci5zZWxlY3Rpb24uc2VsZWN0V29yZCgpO1xuICAgICAgICAgICAgZWRpdG9yLmZpbmRQcmV2aW91cygpO1xuICAgICAgICB9LFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJmaW5kX3VuZGVyX2V4cGFuZFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBlZGl0b3Iuc2VsZWN0TW9yZSgxLCBmYWxzZSwgdHJ1ZSk7XG4gICAgICAgIH0sXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImFuaW1hdGVcIixcbiAgICAgICAgcmVhZE9ubHk6IHRydWVcbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwiZmluZF91bmRlcl9leHBhbmRfc2tpcFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBlZGl0b3Iuc2VsZWN0TW9yZSgxLCB0cnVlLCB0cnVlKTtcbiAgICAgICAgfSxcbiAgICAgICAgc2Nyb2xsSW50b1ZpZXc6IFwiYW5pbWF0ZVwiLFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJkZWxldGVfdG9faGFyZF9ib2xcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgdmFyIHBvcyA9IGVkaXRvci5zZWxlY3Rpb24uZ2V0Q3Vyc29yKCk7XG4gICAgICAgICAgICBlZGl0b3Iuc2Vzc2lvbi5yZW1vdmUoe1xuICAgICAgICAgICAgICAgIHN0YXJ0OiB7IHJvdzogcG9zLnJvdywgY29sdW1uOiAwIH0sXG4gICAgICAgICAgICAgICAgZW5kOiBwb3NcbiAgICAgICAgICAgIH0pO1xuICAgICAgICB9LFxuICAgICAgICBtdWx0aVNlbGVjdEFjdGlvbjogXCJmb3JFYWNoXCIsXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImN1cnNvclwiXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcImRlbGV0ZV90b19oYXJkX2VvbFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICB2YXIgcG9zID0gZWRpdG9yLnNlbGVjdGlvbi5nZXRDdXJzb3IoKTtcbiAgICAgICAgICAgIGVkaXRvci5zZXNzaW9uLnJlbW92ZSh7XG4gICAgICAgICAgICAgICAgc3RhcnQ6IHBvcyxcbiAgICAgICAgICAgICAgICBlbmQ6IHsgcm93OiBwb3Mucm93LCBjb2x1bW46IEluZmluaXR5IH1cbiAgICAgICAgICAgIH0pO1xuICAgICAgICB9LFxuICAgICAgICBtdWx0aVNlbGVjdEFjdGlvbjogXCJmb3JFYWNoXCIsXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImN1cnNvclwiXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcIm1vdmVUb1dvcmRTdGFydExlZnRcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi5tb3ZlQ3Vyc29yTG9uZ1dvcmRMZWZ0KCk7XG4gICAgICAgICAgICBlZGl0b3IuY2xlYXJTZWxlY3Rpb24oKTtcbiAgICAgICAgfSxcbiAgICAgICAgbXVsdGlTZWxlY3RBY3Rpb246IFwiZm9yRWFjaFwiLFxuICAgICAgICBzY3JvbGxJbnRvVmlldzogXCJjdXJzb3JcIlxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJtb3ZlVG9Xb3JkRW5kUmlnaHRcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi5tb3ZlQ3Vyc29yTG9uZ1dvcmRSaWdodCgpO1xuICAgICAgICAgICAgZWRpdG9yLmNsZWFyU2VsZWN0aW9uKCk7XG4gICAgICAgIH0sXG4gICAgICAgIG11bHRpU2VsZWN0QWN0aW9uOiBcImZvckVhY2hcIixcbiAgICAgICAgc2Nyb2xsSW50b1ZpZXc6IFwiY3Vyc29yXCJcbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwic2VsZWN0VG9Xb3JkU3RhcnRMZWZ0XCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIHZhciBzZWwgPSBlZGl0b3Iuc2VsZWN0aW9uO1xuICAgICAgICAgICAgc2VsLiRtb3ZlU2VsZWN0aW9uKHNlbC5tb3ZlQ3Vyc29yTG9uZ1dvcmRMZWZ0KTtcbiAgICAgICAgfSxcbiAgICAgICAgbXVsdGlTZWxlY3RBY3Rpb246IFwiZm9yRWFjaFwiLFxuICAgICAgICBzY3JvbGxJbnRvVmlldzogXCJjdXJzb3JcIlxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJzZWxlY3RUb1dvcmRFbmRSaWdodFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICB2YXIgc2VsID0gZWRpdG9yLnNlbGVjdGlvbjtcbiAgICAgICAgICAgIHNlbC4kbW92ZVNlbGVjdGlvbihzZWwubW92ZUN1cnNvckxvbmdXb3JkUmlnaHQpO1xuICAgICAgICB9LFxuICAgICAgICBtdWx0aVNlbGVjdEFjdGlvbjogXCJmb3JFYWNoXCIsXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImN1cnNvclwiXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcInNlbGVjdFN1YldvcmRSaWdodFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBtb3ZlQnlTdWJXb3JkcyhlZGl0b3IsIDEsIHRydWUpO1xuICAgICAgICB9LFxuICAgICAgICBtdWx0aVNlbGVjdEFjdGlvbjogXCJmb3JFYWNoXCIsXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImN1cnNvclwiLFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJzZWxlY3RTdWJXb3JkTGVmdFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBtb3ZlQnlTdWJXb3JkcyhlZGl0b3IsIC0xLCB0cnVlKTtcbiAgICAgICAgfSxcbiAgICAgICAgbXVsdGlTZWxlY3RBY3Rpb246IFwiZm9yRWFjaFwiLFxuICAgICAgICBzY3JvbGxJbnRvVmlldzogXCJjdXJzb3JcIixcbiAgICAgICAgcmVhZE9ubHk6IHRydWVcbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwibW92ZVN1YldvcmRSaWdodFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBtb3ZlQnlTdWJXb3JkcyhlZGl0b3IsIDEpO1xuICAgICAgICB9LFxuICAgICAgICBtdWx0aVNlbGVjdEFjdGlvbjogXCJmb3JFYWNoXCIsXG4gICAgICAgIHNjcm9sbEludG9WaWV3OiBcImN1cnNvclwiLFxuICAgICAgICByZWFkT25seTogdHJ1ZVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJtb3ZlU3ViV29yZExlZnRcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgbW92ZUJ5U3ViV29yZHMoZWRpdG9yLCAtMSk7XG4gICAgICAgIH0sXG4gICAgICAgIG11bHRpU2VsZWN0QWN0aW9uOiBcImZvckVhY2hcIixcbiAgICAgICAgc2Nyb2xsSW50b1ZpZXc6IFwiY3Vyc29yXCIsXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfV0pO1xuW3tcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWsgY21kLWJhY2tzcGFjZXxjbWQtYmFja3NwYWNlXCIsIHdpbjogXCJjdHJsLXNoaWZ0LWJhY2tzcGFjZXxjdHJsLWsgY3RybC1iYWNrc3BhY2VcIiB9LFxuICAgICAgICBuYW1lOiBcInJlbW92ZXRvbGluZXN0YXJ0aGFyZFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtayBjbWQta3xjbWQtZGVsZXRlfGN0cmwta1wiLCB3aW46IFwiY3RybC1zaGlmdC1kZWxldGV8Y3RybC1rIGN0cmwta1wiIH0sXG4gICAgICAgIG5hbWU6IFwicmVtb3ZldG9saW5lZW5kaGFyZFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtc2hpZnQtZFwiLCB3aW46IFwiY3RybC1zaGlmdC1kXCIgfSxcbiAgICAgICAgbmFtZTogXCJkdXBsaWNhdGVTZWxlY3Rpb25cIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWxcIiwgd2luOiBcImN0cmwtbFwiIH0sXG4gICAgICAgIG5hbWU6IFwiZXhwYW5kdG9saW5lXCJcbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLXNoaWZ0LWFcIiwgd2luOiBcImN0cmwtc2hpZnQtYVwiIH0sXG4gICAgICAgIG5hbWU6IFwiZXhwYW5kU2VsZWN0aW9uXCIsXG4gICAgICAgIGFyZ3M6IHsgdG86IFwidGFnXCIgfVxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLXNoaWZ0LWpcIiwgd2luOiBcImN0cmwtc2hpZnQtalwiIH0sXG4gICAgICAgIG5hbWU6IFwiZXhwYW5kU2VsZWN0aW9uXCIsXG4gICAgICAgIGFyZ3M6IHsgdG86IFwiaW5kZW50YXRpb25cIiB9XG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLXNoaWZ0LW1cIiwgd2luOiBcImN0cmwtc2hpZnQtbVwiIH0sXG4gICAgICAgIG5hbWU6IFwiZXhwYW5kU2VsZWN0aW9uXCIsXG4gICAgICAgIGFyZ3M6IHsgdG86IFwiYnJhY2tldHNcIiB9XG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtc2hpZnQtc3BhY2VcIiwgd2luOiBcImN0cmwtc2hpZnQtc3BhY2VcIiB9LFxuICAgICAgICBuYW1lOiBcImV4cGFuZFNlbGVjdGlvblwiLFxuICAgICAgICBhcmdzOiB7IHRvOiBcInNjb3BlXCIgfVxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLWNtZC1nXCIsIHdpbjogXCJhbHQtZjNcIiB9LFxuICAgICAgICBuYW1lOiBcImZpbmRfYWxsX3VuZGVyXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImFsdC1jbWQtZ1wiLCB3aW46IFwiY3RybC1mM1wiIH0sXG4gICAgICAgIG5hbWU6IFwiZmluZF91bmRlclwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJzaGlmdC1hbHQtY21kLWdcIiwgd2luOiBcImN0cmwtc2hpZnQtZjNcIiB9LFxuICAgICAgICBuYW1lOiBcImZpbmRfdW5kZXJfcHJldlwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtZ1wiLCB3aW46IFwiZjNcIiB9LFxuICAgICAgICBuYW1lOiBcImZpbmRuZXh0XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcInNoaWZ0LWNtZC1nXCIsIHdpbjogXCJzaGlmdC1mM1wiIH0sXG4gICAgICAgIG5hbWU6IFwiZmluZHByZXZpb3VzXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1kXCIsIHdpbjogXCJjdHJsLWRcIiB9LFxuICAgICAgICBuYW1lOiBcImZpbmRfdW5kZXJfZXhwYW5kXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1rIGNtZC1kXCIsIHdpbjogXCJjdHJsLWsgY3RybC1kXCIgfSxcbiAgICAgICAgbmFtZTogXCJmaW5kX3VuZGVyX2V4cGFuZF9za2lwXCJcbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWFsdC1bXCIsIHdpbjogXCJjdHJsLXNoaWZ0LVtcIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZUZvbGRXaWRnZXRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWFsdC1dXCIsIHdpbjogXCJjdHJsLXNoaWZ0LV1cIiB9LFxuICAgICAgICBuYW1lOiBcInVuZm9sZFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtayBjbWQtMHxjbWQtayBjbWQtalwiLCB3aW46IFwiY3RybC1rIGN0cmwtMHxjdHJsLWsgY3RybC1qXCIgfSxcbiAgICAgICAgbmFtZTogXCJ1bmZvbGRhbGxcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWsgY21kLTFcIiwgd2luOiBcImN0cmwtayBjdHJsLTFcIiB9LFxuICAgICAgICBuYW1lOiBcImZvbGRPdGhlclwiLFxuICAgICAgICBhcmdzOiB7IGxldmVsOiAxIH1cbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyB3aW46IFwiY3RybC1sZWZ0XCIsIG1hYzogXCJhbHQtbGVmdFwiIH0sXG4gICAgICAgIG5hbWU6IFwibW92ZVRvV29yZFN0YXJ0TGVmdFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IHdpbjogXCJjdHJsLXJpZ2h0XCIsIG1hYzogXCJhbHQtcmlnaHRcIiB9LFxuICAgICAgICBuYW1lOiBcIm1vdmVUb1dvcmRFbmRSaWdodFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IHdpbjogXCJjdHJsLXNoaWZ0LWxlZnRcIiwgbWFjOiBcImFsdC1zaGlmdC1sZWZ0XCIgfSxcbiAgICAgICAgbmFtZTogXCJzZWxlY3RUb1dvcmRTdGFydExlZnRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyB3aW46IFwiY3RybC1zaGlmdC1yaWdodFwiLCBtYWM6IFwiYWx0LXNoaWZ0LXJpZ2h0XCIgfSxcbiAgICAgICAgbmFtZTogXCJzZWxlY3RUb1dvcmRFbmRSaWdodFwiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtYWx0LXNoaWZ0LXJpZ2h0fGN0cmwtc2hpZnQtcmlnaHRcIiwgd2luOiBcImFsdC1zaGlmdC1yaWdodFwiIH0sXG4gICAgICAgIG5hbWU6IFwic2VsZWN0U3ViV29yZFJpZ2h0XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtYWx0LXNoaWZ0LWxlZnR8Y3RybC1zaGlmdC1sZWZ0XCIsIHdpbjogXCJhbHQtc2hpZnQtbGVmdFwiIH0sXG4gICAgICAgIG5hbWU6IFwic2VsZWN0U3ViV29yZExlZnRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY3RybC1hbHQtcmlnaHR8Y3RybC1yaWdodFwiLCB3aW46IFwiYWx0LXJpZ2h0XCIgfSxcbiAgICAgICAgbmFtZTogXCJtb3ZlU3ViV29yZFJpZ2h0XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtYWx0LWxlZnR8Y3RybC1sZWZ0XCIsIHdpbjogXCJhbHQtbGVmdFwiIH0sXG4gICAgICAgIG5hbWU6IFwibW92ZVN1YldvcmRMZWZ0XCJcbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY3RybC1tXCIsIHdpbjogXCJjdHJsLW1cIiB9LFxuICAgICAgICBuYW1lOiBcImp1bXB0b21hdGNoaW5nXCIsXG4gICAgICAgIGFyZ3M6IHsgdG86IFwiYnJhY2tldHNcIiB9XG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtZjZcIiwgd2luOiBcImN0cmwtZjZcIiB9LFxuICAgICAgICBuYW1lOiBcImdvVG9OZXh0RXJyb3JcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY3RybC1zaGlmdC1mNlwiLCB3aW46IFwiY3RybC1zaGlmdC1mNlwiIH0sXG4gICAgICAgIG5hbWU6IFwiZ29Ub1ByZXZpb3VzRXJyb3JcIlxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLW9cIiB9LFxuICAgICAgICBuYW1lOiBcInNwbGl0bGluZVwiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtc2hpZnQtd1wiLCB3aW46IFwiYWx0LXNoaWZ0LXdcIiB9LFxuICAgICAgICBuYW1lOiBcInN1cnJvd25kV2l0aFRhZ1wiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtYWx0LS5cIiwgd2luOiBcImFsdC0uXCIgfSxcbiAgICAgICAgbmFtZTogXCJjbG9zZV90YWdcIlxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtalwiLCB3aW46IFwiY3RybC1qXCIgfSxcbiAgICAgICAgbmFtZTogXCJqb2lubGluZXNcIlxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLS1cIiwgd2luOiBcImFsdC0tXCIgfSxcbiAgICAgICAgbmFtZTogXCJqdW1wQmFja1wiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLXNoaWZ0LS1cIiwgd2luOiBcImFsdC1zaGlmdC0tXCIgfSxcbiAgICAgICAgbmFtZTogXCJqdW1wRm9yd2FyZFwiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1rIGNtZC1sXCIsIHdpbjogXCJjdHJsLWsgY3RybC1sXCIgfSxcbiAgICAgICAgbmFtZTogXCJ0b2xvd2VyY2FzZVwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtayBjbWQtdVwiLCB3aW46IFwiY3RybC1rIGN0cmwtdVwiIH0sXG4gICAgICAgIG5hbWU6IFwidG91cHBlcmNhc2VcIlxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjbWQtc2hpZnQtdlwiLCB3aW46IFwiY3RybC1zaGlmdC12XCIgfSxcbiAgICAgICAgbmFtZTogXCJwYXN0ZV9hbmRfaW5kZW50XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1rIGNtZC12fGNtZC1hbHQtdlwiLCB3aW46IFwiY3RybC1rIGN0cmwtdlwiIH0sXG4gICAgICAgIG5hbWU6IFwicGFzdGVfZnJvbV9oaXN0b3J5XCJcbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLXNoaWZ0LWVudGVyXCIsIHdpbjogXCJjdHJsLXNoaWZ0LWVudGVyXCIgfSxcbiAgICAgICAgbmFtZTogXCJhZGRMaW5lQmVmb3JlXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1lbnRlclwiLCB3aW46IFwiY3RybC1lbnRlclwiIH0sXG4gICAgICAgIG5hbWU6IFwiYWRkTGluZUFmdGVyXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtc2hpZnQta1wiLCB3aW46IFwiY3RybC1zaGlmdC1rXCIgfSxcbiAgICAgICAgbmFtZTogXCJyZW1vdmVsaW5lXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtYWx0LXVwXCIsIHdpbjogXCJjdHJsLXVwXCIgfSxcbiAgICAgICAgbmFtZTogXCJzY3JvbGx1cFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLWFsdC1kb3duXCIsIHdpbjogXCJjdHJsLWRvd25cIiB9LFxuICAgICAgICBuYW1lOiBcInNjcm9sbGRvd25cIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWFcIiwgd2luOiBcImN0cmwtYVwiIH0sXG4gICAgICAgIG5hbWU6IFwic2VsZWN0YWxsXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbGludXg6IFwiYWx0LXNoaWZ0LWRvd25cIiwgbWFjOiBcImN0cmwtc2hpZnQtZG93blwiLCB3aW46IFwiY3RybC1hbHQtZG93blwiIH0sXG4gICAgICAgIG5hbWU6IFwiYWRkQ3Vyc29yQmVsb3dcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBsaW51eDogXCJhbHQtc2hpZnQtdXBcIiwgbWFjOiBcImN0cmwtc2hpZnQtdXBcIiwgd2luOiBcImN0cmwtYWx0LXVwXCIgfSxcbiAgICAgICAgbmFtZTogXCJhZGRDdXJzb3JBYm92ZVwiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC1rIGNtZC1jfGN0cmwtbFwiLCB3aW46IFwiY3RybC1rIGN0cmwtY1wiIH0sXG4gICAgICAgIG5hbWU6IFwiY2VudGVyc2VsZWN0aW9uXCJcbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiZjVcIiwgd2luOiBcImY5XCIgfSxcbiAgICAgICAgbmFtZTogXCJzb3J0bGluZXNcIlxuICAgIH0sXG4gICAge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJjdHJsLWY1XCIsIHdpbjogXCJjdHJsLWY5XCIgfSxcbiAgICAgICAgbmFtZTogXCJzb3J0bGluZXNcIixcbiAgICAgICAgYXJnczogeyBjYXNlU2Vuc2l0aXZlOiB0cnVlIH1cbiAgICB9LFxuICAgIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLXNoaWZ0LWxcIiwgd2luOiBcImN0cmwtc2hpZnQtbFwiIH0sXG4gICAgICAgIG5hbWU6IFwic3BsaXRTZWxlY3Rpb25JbnRvTGluZXNcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY3RybC1jbWQtZG93blwiLCB3aW46IFwiY3RybC1zaGlmdC1kb3duXCIgfSxcbiAgICAgICAgbmFtZTogXCJtb3ZlbGluZXNkb3duXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtY21kLXVwXCIsIHdpbjogXCJjdHJsLXNoaWZ0LXVwXCIgfSxcbiAgICAgICAgbmFtZTogXCJtb3ZlbGluZXN1cFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJhbHQtZG93blwiLCB3aW46IFwiYWx0LWRvd25cIiB9LFxuICAgICAgICBuYW1lOiBcIm1vZGlmeU51bWJlckRvd25cIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiYWx0LXVwXCIsIHdpbjogXCJhbHQtdXBcIiB9LFxuICAgICAgICBuYW1lOiBcIm1vZGlmeU51bWJlclVwXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImNtZC0vXCIsIHdpbjogXCJjdHJsLS9cIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZWNvbW1lbnRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiY21kLWFsdC0vXCIsIHdpbjogXCJjdHJsLXNoaWZ0LS9cIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZUJsb2NrQ29tbWVudFwiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbGludXg6IFwiY3RybC1hbHQtcVwiLCBtYWM6IFwiY3RybC1xXCIsIHdpbjogXCJjdHJsLXFcIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZXJlY29yZGluZ1wiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IGxpbnV4OiBcImN0cmwtYWx0LXNoaWZ0LXFcIiwgbWFjOiBcImN0cmwtc2hpZnQtcVwiLCB3aW46IFwiY3RybC1zaGlmdC1xXCIgfSxcbiAgICAgICAgbmFtZTogXCJyZXBsYXltYWNyb1wiXG4gICAgfSxcbiAgICB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcImN0cmwtdFwiLCB3aW46IFwiY3RybC10XCIgfSxcbiAgICAgICAgbmFtZTogXCJ0cmFuc3Bvc2VcIlxuICAgIH1cbl0uZm9yRWFjaChmdW5jdGlvbiAoYmluZGluZykge1xuICAgIHZhciBjb21tYW5kID0gZXhwb3J0cy5oYW5kbGVyLmNvbW1hbmRzW2JpbmRpbmcubmFtZV07XG4gICAgaWYgKGNvbW1hbmQpXG4gICAgICAgIGNvbW1hbmQuYmluZEtleSA9IGJpbmRpbmcuYmluZEtleTtcbiAgICBleHBvcnRzLmhhbmRsZXIuYmluZEtleShiaW5kaW5nLmJpbmRLZXksIGNvbW1hbmQgfHwgYmluZGluZy5uYW1lKTtcbn0pO1xuXG59KTsgICAgICAgICAgICAgICAgKGZ1bmN0aW9uKCkge1xuICAgICAgICAgICAgICAgICAgICBhY2UucmVxdWlyZShbXCJhY2Uva2V5Ym9hcmQvc3VibGltZVwiXSwgZnVuY3Rpb24obSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHR5cGVvZiBtb2R1bGUgPT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgZXhwb3J0cyA9PSBcIm9iamVjdFwiICYmIG1vZHVsZSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIG1vZHVsZS5leHBvcnRzID0gbTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgfSkoKTtcbiAgICAgICAgICAgICJdLCJuYW1lcyI6W10sInNvdXJjZVJvb3QiOiIifQ==