(globalThis["webpackChunkui"] = globalThis["webpackChunkui"] || []).push([["ace-keybinding-vscode"],{

/***/ "./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-vscode.js"
/*!**********************************************************************************************************!*\
  !*** ./node_modules/.pnpm/ace-builds@1.43.6/node_modules/ace-builds/src-noconflict/keybinding-vscode.js ***!
  \**********************************************************************************************************/
(module, __unused_webpack_exports, __webpack_require__) {

/* module decorator */ module = __webpack_require__.nmd(module);
ace.define("ace/keyboard/vscode",["require","exports","module","ace/keyboard/hash_handler","ace/config"], function(require, exports, module){"use strict";
var HashHandler = require("../keyboard/hash_handler").HashHandler;
var config = require("../config");
exports.handler = new HashHandler();
exports.handler.$id = "ace/keyboard/vscode";
exports.handler.addCommands([{
        name: "toggleWordWrap",
        exec: function (editor) {
            var wrapUsed = editor.session.getUseWrapMode();
            editor.session.setUseWrapMode(!wrapUsed);
        },
        readOnly: true
    }, {
        name: "navigateToLastEditLocation",
        exec: function (editor) {
            var lastDelta = editor.session.getUndoManager().$lastDelta;
            var range = (lastDelta.action == "remove") ? lastDelta.start : lastDelta.end;
            editor.moveCursorTo(range.row, range.column);
            editor.clearSelection();
        }
    }, {
        name: "replaceAll",
        exec: function (editor) {
            if (!editor.searchBox) {
                config.loadModule("ace/ext/searchbox", function (e) {
                    e.Search(editor, true);
                });
            }
            else {
                if (editor.searchBox.active === true && editor.searchBox.replaceOption.checked === true) {
                    editor.searchBox.replaceAll();
                }
            }
        }
    }, {
        name: "replaceOne",
        exec: function (editor) {
            if (!editor.searchBox) {
                config.loadModule("ace/ext/searchbox", function (e) {
                    e.Search(editor, true);
                });
            }
            else {
                if (editor.searchBox.active === true && editor.searchBox.replaceOption.checked === true) {
                    editor.searchBox.replace();
                }
            }
        }
    }, {
        name: "selectAllMatches",
        exec: function (editor) {
            if (!editor.searchBox) {
                config.loadModule("ace/ext/searchbox", function (e) {
                    e.Search(editor, false);
                });
            }
            else {
                if (editor.searchBox.active === true) {
                    editor.searchBox.findAll();
                }
            }
        }
    }, {
        name: "toggleFindCaseSensitive",
        exec: function (editor) {
            config.loadModule("ace/ext/searchbox", function (e) {
                e.Search(editor, false);
                var sb = editor.searchBox;
                sb.caseSensitiveOption.checked = !sb.caseSensitiveOption.checked;
                sb.$syncOptions();
            });
        }
    }, {
        name: "toggleFindInSelection",
        exec: function (editor) {
            config.loadModule("ace/ext/searchbox", function (e) {
                e.Search(editor, false);
                var sb = editor.searchBox;
                sb.searchOption.checked = !sb.searchRange;
                sb.setSearchRange(sb.searchOption.checked && sb.editor.getSelectionRange());
                sb.$syncOptions();
            });
        }
    }, {
        name: "toggleFindRegex",
        exec: function (editor) {
            config.loadModule("ace/ext/searchbox", function (e) {
                e.Search(editor, false);
                var sb = editor.searchBox;
                sb.regExpOption.checked = !sb.regExpOption.checked;
                sb.$syncOptions();
            });
        }
    }, {
        name: "toggleFindWholeWord",
        exec: function (editor) {
            config.loadModule("ace/ext/searchbox", function (e) {
                e.Search(editor, false);
                var sb = editor.searchBox;
                sb.wholeWordOption.checked = !sb.wholeWordOption.checked;
                sb.$syncOptions();
            });
        }
    }, {
        name: "removeSecondaryCursors",
        exec: function (editor) {
            var ranges = editor.selection.ranges;
            if (ranges && ranges.length > 1)
                editor.selection.toSingleRange(ranges[ranges.length - 1]);
            else
                editor.selection.clearSelection();
        }
    }]);
[{
        bindKey: { mac: "Ctrl-G", win: "Ctrl-G" },
        name: "gotoline"
    }, {
        bindKey: { mac: "Command-Shift-L|Command-F2", win: "Ctrl-Shift-L|Ctrl-F2" },
        name: "findAll"
    }, {
        bindKey: { mac: "Shift-F8|Shift-Option-F8", win: "Shift-F8|Shift-Alt-F8" },
        name: "goToPreviousError"
    }, {
        bindKey: { mac: "F8|Option-F8", win: "F8|Alt-F8" },
        name: "goToNextError"
    }, {
        bindKey: { mac: "Command-Shift-P|F1", win: "Ctrl-Shift-P|F1" },
        name: "openCommandPalette"
    }, {
        bindKey: { mac: "Shift-Option-Up", win: "Alt-Shift-Up" },
        name: "copylinesup"
    }, {
        bindKey: { mac: "Shift-Option-Down", win: "Alt-Shift-Down" },
        name: "copylinesdown"
    }, {
        bindKey: { mac: "Command-Shift-K", win: "Ctrl-Shift-K" },
        name: "removeline"
    }, {
        bindKey: { mac: "Command-Enter", win: "Ctrl-Enter" },
        name: "addLineAfter"
    }, {
        bindKey: { mac: "Command-Shift-Enter", win: "Ctrl-Shift-Enter" },
        name: "addLineBefore"
    }, {
        bindKey: { mac: "Command-Shift-\\", win: "Ctrl-Shift-\\" },
        name: "jumptomatching"
    }, {
        bindKey: { mac: "Command-]", win: "Ctrl-]" },
        name: "blockindent"
    }, {
        bindKey: { mac: "Command-[", win: "Ctrl-[" },
        name: "blockoutdent"
    }, {
        bindKey: { mac: "Ctrl-PageDown", win: "Alt-PageDown" },
        name: "pagedown"
    }, {
        bindKey: { mac: "Ctrl-PageUp", win: "Alt-PageUp" },
        name: "pageup"
    }, {
        bindKey: { mac: "Shift-Option-A", win: "Shift-Alt-A" },
        name: "toggleBlockComment"
    }, {
        bindKey: { mac: "Option-Z", win: "Alt-Z" },
        name: "toggleWordWrap"
    }, {
        bindKey: { mac: "Command-G", win: "F3|Ctrl-K Ctrl-D" },
        name: "findnext"
    }, {
        bindKey: { mac: "Command-Shift-G", win: "Shift-F3" },
        name: "findprevious"
    }, {
        bindKey: { mac: "Option-Enter", win: "Alt-Enter" },
        name: "selectAllMatches"
    }, {
        bindKey: { mac: "Command-D", win: "Ctrl-D" },
        name: "selectMoreAfter"
    }, {
        bindKey: { mac: "Command-K Command-D", win: "Ctrl-K Ctrl-D" },
        name: "selectOrFindNext"
    }, {
        bindKey: { mac: "Shift-Option-I", win: "Shift-Alt-I" },
        name: "splitSelectionIntoLines"
    }, {
        bindKey: { mac: "Command-K M", win: "Ctrl-K M" },
        name: "modeSelect"
    }, {
        bindKey: { mac: "Command-Option-[", win: "Ctrl-Shift-[" },
        name: "toggleFoldWidget"
    }, {
        bindKey: { mac: "Command-Option-]", win: "Ctrl-Shift-]" },
        name: "toggleFoldWidget"
    }, {
        bindKey: { mac: "Command-K Command-0", win: "Ctrl-K Ctrl-0" },
        name: "foldall"
    }, {
        bindKey: { mac: "Command-K Command-J", win: "Ctrl-K Ctrl-J" },
        name: "unfoldall"
    }, {
        bindKey: { mac: "Command-K Command-1", win: "Ctrl-K Ctrl-1" },
        name: "foldOther"
    }, {
        bindKey: { mac: "Command-K Command-Q", win: "Ctrl-K Ctrl-Q" },
        name: "navigateToLastEditLocation"
    }, {
        bindKey: { mac: "Command-K Command-R|Command-K Command-S", win: "Ctrl-K Ctrl-R|Ctrl-K Ctrl-S" },
        name: "showKeyboardShortcuts"
    }, {
        bindKey: { mac: "Command-K Command-X", win: "Ctrl-K Ctrl-X" },
        name: "trimTrailingSpace"
    }, {
        bindKey: { mac: "Shift-Down|Command-Shift-Down", win: "Shift-Down|Ctrl-Shift-Down" },
        name: "selectdown"
    }, {
        bindKey: { mac: "Shift-Up|Command-Shift-Up", win: "Shift-Up|Ctrl-Shift-Up" },
        name: "selectup"
    }, {
        bindKey: { mac: "Command-Alt-Enter", win: "Ctrl-Alt-Enter" },
        name: "replaceAll"
    }, {
        bindKey: { mac: "Command-Shift-1", win: "Ctrl-Shift-1" },
        name: "replaceOne"
    }, {
        bindKey: { mac: "Option-C", win: "Alt-C" },
        name: "toggleFindCaseSensitive"
    }, {
        bindKey: { mac: "Option-L", win: "Alt-L" },
        name: "toggleFindInSelection"
    }, {
        bindKey: { mac: "Option-R", win: "Alt-R" },
        name: "toggleFindRegex"
    }, {
        bindKey: { mac: "Option-W", win: "Alt-W" },
        name: "toggleFindWholeWord"
    }, {
        bindKey: { mac: "Command-L", win: "Ctrl-L" },
        name: "expandtoline"
    }, {
        bindKey: { mac: "Shift-Esc", win: "Shift-Esc" },
        name: "removeSecondaryCursors"
    }
].forEach(function (binding) {
    var command = exports.handler.commands[binding.name];
    if (command)
        command.bindKey = binding.bindKey;
    exports.handler.bindKey(binding.bindKey, command || binding.name);
});

});                (function() {
                    ace.require(["ace/keyboard/vscode"], function(m) {
                        if ( true && module) {
                            module.exports = m;
                        }
                    });
                })();
            

/***/ }

}]);
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiYWNlLWtleWJpbmRpbmctdnNjb2RlLWU3NDNjMTNkZjg3OGJlN2NiZGU1LmpzIiwibWFwcGluZ3MiOiI7Ozs7Ozs7OztBQUFBLDZJQUE2STtBQUM3STtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxTQUFTO0FBQ1Q7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGlCQUFpQjtBQUNqQjtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsaUJBQWlCO0FBQ2pCO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxpQkFBaUI7QUFDakI7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxhQUFhO0FBQ2I7QUFDQSxLQUFLO0FBQ0w7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLGFBQWE7QUFDYjtBQUNBLEtBQUs7QUFDTDtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsS0FBSztBQUNMO0FBQ0EsbUJBQW1CLDhCQUE4QjtBQUNqRDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsZ0VBQWdFO0FBQ25GO0FBQ0EsS0FBSztBQUNMLG1CQUFtQiwrREFBK0Q7QUFDbEY7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLHVDQUF1QztBQUMxRDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsbURBQW1EO0FBQ3RFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQiw2Q0FBNkM7QUFDaEU7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLGlEQUFpRDtBQUNwRTtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsNkNBQTZDO0FBQ2hFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQix5Q0FBeUM7QUFDNUQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLHFEQUFxRDtBQUN4RTtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsK0NBQStDO0FBQ2xFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixpQ0FBaUM7QUFDcEQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLGlDQUFpQztBQUNwRDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsMkNBQTJDO0FBQzlEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQix1Q0FBdUM7QUFDMUQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLDJDQUEyQztBQUM5RDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsK0JBQStCO0FBQ2xEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQiwyQ0FBMkM7QUFDOUQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLHlDQUF5QztBQUM1RDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsdUNBQXVDO0FBQzFEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixpQ0FBaUM7QUFDcEQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLGtEQUFrRDtBQUNyRTtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsMkNBQTJDO0FBQzlEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixxQ0FBcUM7QUFDeEQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLDhDQUE4QztBQUNqRTtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsOENBQThDO0FBQ2pFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixrREFBa0Q7QUFDckU7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLGtEQUFrRDtBQUNyRTtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsa0RBQWtEO0FBQ3JFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixrREFBa0Q7QUFDckU7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLG9GQUFvRjtBQUN2RztBQUNBLEtBQUs7QUFDTCxtQkFBbUIsa0RBQWtEO0FBQ3JFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQix5RUFBeUU7QUFDNUY7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLGlFQUFpRTtBQUNwRjtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsaURBQWlEO0FBQ3BFO0FBQ0EsS0FBSztBQUNMLG1CQUFtQiw2Q0FBNkM7QUFDaEU7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLCtCQUErQjtBQUNsRDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsK0JBQStCO0FBQ2xEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQiwrQkFBK0I7QUFDbEQ7QUFDQSxLQUFLO0FBQ0wsbUJBQW1CLCtCQUErQjtBQUNsRDtBQUNBLEtBQUs7QUFDTCxtQkFBbUIsaUNBQWlDO0FBQ3BEO0FBQ0EsS0FBSztBQUNMLG1CQUFtQixvQ0FBb0M7QUFDdkQ7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxDQUFDOztBQUVELENBQUMsa0JBQWtCO0FBQ25CO0FBQ0EsNEJBQTRCLEtBQXVEO0FBQ25GO0FBQ0E7QUFDQSxxQkFBcUI7QUFDckIsaUJBQWlCO0FBQ2pCLFkiLCJzb3VyY2VzIjpbIndlYnBhY2s6Ly91aS8uL25vZGVfbW9kdWxlcy8ucG5wbS9hY2UtYnVpbGRzQDEuNDMuNi9ub2RlX21vZHVsZXMvYWNlLWJ1aWxkcy9zcmMtbm9jb25mbGljdC9rZXliaW5kaW5nLXZzY29kZS5qcyJdLCJzb3VyY2VzQ29udGVudCI6WyJhY2UuZGVmaW5lKFwiYWNlL2tleWJvYXJkL3ZzY29kZVwiLFtcInJlcXVpcmVcIixcImV4cG9ydHNcIixcIm1vZHVsZVwiLFwiYWNlL2tleWJvYXJkL2hhc2hfaGFuZGxlclwiLFwiYWNlL2NvbmZpZ1wiXSwgZnVuY3Rpb24ocmVxdWlyZSwgZXhwb3J0cywgbW9kdWxlKXtcInVzZSBzdHJpY3RcIjtcbnZhciBIYXNoSGFuZGxlciA9IHJlcXVpcmUoXCIuLi9rZXlib2FyZC9oYXNoX2hhbmRsZXJcIikuSGFzaEhhbmRsZXI7XG52YXIgY29uZmlnID0gcmVxdWlyZShcIi4uL2NvbmZpZ1wiKTtcbmV4cG9ydHMuaGFuZGxlciA9IG5ldyBIYXNoSGFuZGxlcigpO1xuZXhwb3J0cy5oYW5kbGVyLiRpZCA9IFwiYWNlL2tleWJvYXJkL3ZzY29kZVwiO1xuZXhwb3J0cy5oYW5kbGVyLmFkZENvbW1hbmRzKFt7XG4gICAgICAgIG5hbWU6IFwidG9nZ2xlV29yZFdyYXBcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgdmFyIHdyYXBVc2VkID0gZWRpdG9yLnNlc3Npb24uZ2V0VXNlV3JhcE1vZGUoKTtcbiAgICAgICAgICAgIGVkaXRvci5zZXNzaW9uLnNldFVzZVdyYXBNb2RlKCF3cmFwVXNlZCk7XG4gICAgICAgIH0sXG4gICAgICAgIHJlYWRPbmx5OiB0cnVlXG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcIm5hdmlnYXRlVG9MYXN0RWRpdExvY2F0aW9uXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIHZhciBsYXN0RGVsdGEgPSBlZGl0b3Iuc2Vzc2lvbi5nZXRVbmRvTWFuYWdlcigpLiRsYXN0RGVsdGE7XG4gICAgICAgICAgICB2YXIgcmFuZ2UgPSAobGFzdERlbHRhLmFjdGlvbiA9PSBcInJlbW92ZVwiKSA/IGxhc3REZWx0YS5zdGFydCA6IGxhc3REZWx0YS5lbmQ7XG4gICAgICAgICAgICBlZGl0b3IubW92ZUN1cnNvclRvKHJhbmdlLnJvdywgcmFuZ2UuY29sdW1uKTtcbiAgICAgICAgICAgIGVkaXRvci5jbGVhclNlbGVjdGlvbigpO1xuICAgICAgICB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcInJlcGxhY2VBbGxcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgaWYgKCFlZGl0b3Iuc2VhcmNoQm94KSB7XG4gICAgICAgICAgICAgICAgY29uZmlnLmxvYWRNb2R1bGUoXCJhY2UvZXh0L3NlYXJjaGJveFwiLCBmdW5jdGlvbiAoZSkge1xuICAgICAgICAgICAgICAgICAgICBlLlNlYXJjaChlZGl0b3IsIHRydWUpO1xuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGVkaXRvci5zZWFyY2hCb3guYWN0aXZlID09PSB0cnVlICYmIGVkaXRvci5zZWFyY2hCb3gucmVwbGFjZU9wdGlvbi5jaGVja2VkID09PSB0cnVlKSB7XG4gICAgICAgICAgICAgICAgICAgIGVkaXRvci5zZWFyY2hCb3gucmVwbGFjZUFsbCgpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJyZXBsYWNlT25lXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIGlmICghZWRpdG9yLnNlYXJjaEJveCkge1xuICAgICAgICAgICAgICAgIGNvbmZpZy5sb2FkTW9kdWxlKFwiYWNlL2V4dC9zZWFyY2hib3hcIiwgZnVuY3Rpb24gKGUpIHtcbiAgICAgICAgICAgICAgICAgICAgZS5TZWFyY2goZWRpdG9yLCB0cnVlKTtcbiAgICAgICAgICAgICAgICB9KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGlmIChlZGl0b3Iuc2VhcmNoQm94LmFjdGl2ZSA9PT0gdHJ1ZSAmJiBlZGl0b3Iuc2VhcmNoQm94LnJlcGxhY2VPcHRpb24uY2hlY2tlZCA9PT0gdHJ1ZSkge1xuICAgICAgICAgICAgICAgICAgICBlZGl0b3Iuc2VhcmNoQm94LnJlcGxhY2UoKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwic2VsZWN0QWxsTWF0Y2hlc1wiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBpZiAoIWVkaXRvci5zZWFyY2hCb3gpIHtcbiAgICAgICAgICAgICAgICBjb25maWcubG9hZE1vZHVsZShcImFjZS9leHQvc2VhcmNoYm94XCIsIGZ1bmN0aW9uIChlKSB7XG4gICAgICAgICAgICAgICAgICAgIGUuU2VhcmNoKGVkaXRvciwgZmFsc2UpO1xuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgaWYgKGVkaXRvci5zZWFyY2hCb3guYWN0aXZlID09PSB0cnVlKSB7XG4gICAgICAgICAgICAgICAgICAgIGVkaXRvci5zZWFyY2hCb3guZmluZEFsbCgpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJ0b2dnbGVGaW5kQ2FzZVNlbnNpdGl2ZVwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBjb25maWcubG9hZE1vZHVsZShcImFjZS9leHQvc2VhcmNoYm94XCIsIGZ1bmN0aW9uIChlKSB7XG4gICAgICAgICAgICAgICAgZS5TZWFyY2goZWRpdG9yLCBmYWxzZSk7XG4gICAgICAgICAgICAgICAgdmFyIHNiID0gZWRpdG9yLnNlYXJjaEJveDtcbiAgICAgICAgICAgICAgICBzYi5jYXNlU2Vuc2l0aXZlT3B0aW9uLmNoZWNrZWQgPSAhc2IuY2FzZVNlbnNpdGl2ZU9wdGlvbi5jaGVja2VkO1xuICAgICAgICAgICAgICAgIHNiLiRzeW5jT3B0aW9ucygpO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICB9LCB7XG4gICAgICAgIG5hbWU6IFwidG9nZ2xlRmluZEluU2VsZWN0aW9uXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIGNvbmZpZy5sb2FkTW9kdWxlKFwiYWNlL2V4dC9zZWFyY2hib3hcIiwgZnVuY3Rpb24gKGUpIHtcbiAgICAgICAgICAgICAgICBlLlNlYXJjaChlZGl0b3IsIGZhbHNlKTtcbiAgICAgICAgICAgICAgICB2YXIgc2IgPSBlZGl0b3Iuc2VhcmNoQm94O1xuICAgICAgICAgICAgICAgIHNiLnNlYXJjaE9wdGlvbi5jaGVja2VkID0gIXNiLnNlYXJjaFJhbmdlO1xuICAgICAgICAgICAgICAgIHNiLnNldFNlYXJjaFJhbmdlKHNiLnNlYXJjaE9wdGlvbi5jaGVja2VkICYmIHNiLmVkaXRvci5nZXRTZWxlY3Rpb25SYW5nZSgpKTtcbiAgICAgICAgICAgICAgICBzYi4kc3luY09wdGlvbnMoKTtcbiAgICAgICAgICAgIH0pO1xuICAgICAgICB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcInRvZ2dsZUZpbmRSZWdleFwiLFxuICAgICAgICBleGVjOiBmdW5jdGlvbiAoZWRpdG9yKSB7XG4gICAgICAgICAgICBjb25maWcubG9hZE1vZHVsZShcImFjZS9leHQvc2VhcmNoYm94XCIsIGZ1bmN0aW9uIChlKSB7XG4gICAgICAgICAgICAgICAgZS5TZWFyY2goZWRpdG9yLCBmYWxzZSk7XG4gICAgICAgICAgICAgICAgdmFyIHNiID0gZWRpdG9yLnNlYXJjaEJveDtcbiAgICAgICAgICAgICAgICBzYi5yZWdFeHBPcHRpb24uY2hlY2tlZCA9ICFzYi5yZWdFeHBPcHRpb24uY2hlY2tlZDtcbiAgICAgICAgICAgICAgICBzYi4kc3luY09wdGlvbnMoKTtcbiAgICAgICAgICAgIH0pO1xuICAgICAgICB9XG4gICAgfSwge1xuICAgICAgICBuYW1lOiBcInRvZ2dsZUZpbmRXaG9sZVdvcmRcIixcbiAgICAgICAgZXhlYzogZnVuY3Rpb24gKGVkaXRvcikge1xuICAgICAgICAgICAgY29uZmlnLmxvYWRNb2R1bGUoXCJhY2UvZXh0L3NlYXJjaGJveFwiLCBmdW5jdGlvbiAoZSkge1xuICAgICAgICAgICAgICAgIGUuU2VhcmNoKGVkaXRvciwgZmFsc2UpO1xuICAgICAgICAgICAgICAgIHZhciBzYiA9IGVkaXRvci5zZWFyY2hCb3g7XG4gICAgICAgICAgICAgICAgc2Iud2hvbGVXb3JkT3B0aW9uLmNoZWNrZWQgPSAhc2Iud2hvbGVXb3JkT3B0aW9uLmNoZWNrZWQ7XG4gICAgICAgICAgICAgICAgc2IuJHN5bmNPcHRpb25zKCk7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgfVxuICAgIH0sIHtcbiAgICAgICAgbmFtZTogXCJyZW1vdmVTZWNvbmRhcnlDdXJzb3JzXCIsXG4gICAgICAgIGV4ZWM6IGZ1bmN0aW9uIChlZGl0b3IpIHtcbiAgICAgICAgICAgIHZhciByYW5nZXMgPSBlZGl0b3Iuc2VsZWN0aW9uLnJhbmdlcztcbiAgICAgICAgICAgIGlmIChyYW5nZXMgJiYgcmFuZ2VzLmxlbmd0aCA+IDEpXG4gICAgICAgICAgICAgICAgZWRpdG9yLnNlbGVjdGlvbi50b1NpbmdsZVJhbmdlKHJhbmdlc1tyYW5nZXMubGVuZ3RoIC0gMV0pO1xuICAgICAgICAgICAgZWxzZVxuICAgICAgICAgICAgICAgIGVkaXRvci5zZWxlY3Rpb24uY2xlYXJTZWxlY3Rpb24oKTtcbiAgICAgICAgfVxuICAgIH1dKTtcblt7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkN0cmwtR1wiLCB3aW46IFwiQ3RybC1HXCIgfSxcbiAgICAgICAgbmFtZTogXCJnb3RvbGluZVwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLVNoaWZ0LUx8Q29tbWFuZC1GMlwiLCB3aW46IFwiQ3RybC1TaGlmdC1MfEN0cmwtRjJcIiB9LFxuICAgICAgICBuYW1lOiBcImZpbmRBbGxcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiU2hpZnQtRjh8U2hpZnQtT3B0aW9uLUY4XCIsIHdpbjogXCJTaGlmdC1GOHxTaGlmdC1BbHQtRjhcIiB9LFxuICAgICAgICBuYW1lOiBcImdvVG9QcmV2aW91c0Vycm9yXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkY4fE9wdGlvbi1GOFwiLCB3aW46IFwiRjh8QWx0LUY4XCIgfSxcbiAgICAgICAgbmFtZTogXCJnb1RvTmV4dEVycm9yXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtU2hpZnQtUHxGMVwiLCB3aW46IFwiQ3RybC1TaGlmdC1QfEYxXCIgfSxcbiAgICAgICAgbmFtZTogXCJvcGVuQ29tbWFuZFBhbGV0dGVcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiU2hpZnQtT3B0aW9uLVVwXCIsIHdpbjogXCJBbHQtU2hpZnQtVXBcIiB9LFxuICAgICAgICBuYW1lOiBcImNvcHlsaW5lc3VwXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIlNoaWZ0LU9wdGlvbi1Eb3duXCIsIHdpbjogXCJBbHQtU2hpZnQtRG93blwiIH0sXG4gICAgICAgIG5hbWU6IFwiY29weWxpbmVzZG93blwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLVNoaWZ0LUtcIiwgd2luOiBcIkN0cmwtU2hpZnQtS1wiIH0sXG4gICAgICAgIG5hbWU6IFwicmVtb3ZlbGluZVwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLUVudGVyXCIsIHdpbjogXCJDdHJsLUVudGVyXCIgfSxcbiAgICAgICAgbmFtZTogXCJhZGRMaW5lQWZ0ZXJcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1TaGlmdC1FbnRlclwiLCB3aW46IFwiQ3RybC1TaGlmdC1FbnRlclwiIH0sXG4gICAgICAgIG5hbWU6IFwiYWRkTGluZUJlZm9yZVwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLVNoaWZ0LVxcXFxcIiwgd2luOiBcIkN0cmwtU2hpZnQtXFxcXFwiIH0sXG4gICAgICAgIG5hbWU6IFwianVtcHRvbWF0Y2hpbmdcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1dXCIsIHdpbjogXCJDdHJsLV1cIiB9LFxuICAgICAgICBuYW1lOiBcImJsb2NraW5kZW50XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtW1wiLCB3aW46IFwiQ3RybC1bXCIgfSxcbiAgICAgICAgbmFtZTogXCJibG9ja291dGRlbnRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ3RybC1QYWdlRG93blwiLCB3aW46IFwiQWx0LVBhZ2VEb3duXCIgfSxcbiAgICAgICAgbmFtZTogXCJwYWdlZG93blwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDdHJsLVBhZ2VVcFwiLCB3aW46IFwiQWx0LVBhZ2VVcFwiIH0sXG4gICAgICAgIG5hbWU6IFwicGFnZXVwXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIlNoaWZ0LU9wdGlvbi1BXCIsIHdpbjogXCJTaGlmdC1BbHQtQVwiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlQmxvY2tDb21tZW50XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIk9wdGlvbi1aXCIsIHdpbjogXCJBbHQtWlwiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlV29yZFdyYXBcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1HXCIsIHdpbjogXCJGM3xDdHJsLUsgQ3RybC1EXCIgfSxcbiAgICAgICAgbmFtZTogXCJmaW5kbmV4dFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLVNoaWZ0LUdcIiwgd2luOiBcIlNoaWZ0LUYzXCIgfSxcbiAgICAgICAgbmFtZTogXCJmaW5kcHJldmlvdXNcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiT3B0aW9uLUVudGVyXCIsIHdpbjogXCJBbHQtRW50ZXJcIiB9LFxuICAgICAgICBuYW1lOiBcInNlbGVjdEFsbE1hdGNoZXNcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1EXCIsIHdpbjogXCJDdHJsLURcIiB9LFxuICAgICAgICBuYW1lOiBcInNlbGVjdE1vcmVBZnRlclwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLUsgQ29tbWFuZC1EXCIsIHdpbjogXCJDdHJsLUsgQ3RybC1EXCIgfSxcbiAgICAgICAgbmFtZTogXCJzZWxlY3RPckZpbmROZXh0XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIlNoaWZ0LU9wdGlvbi1JXCIsIHdpbjogXCJTaGlmdC1BbHQtSVwiIH0sXG4gICAgICAgIG5hbWU6IFwic3BsaXRTZWxlY3Rpb25JbnRvTGluZXNcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1LIE1cIiwgd2luOiBcIkN0cmwtSyBNXCIgfSxcbiAgICAgICAgbmFtZTogXCJtb2RlU2VsZWN0XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtT3B0aW9uLVtcIiwgd2luOiBcIkN0cmwtU2hpZnQtW1wiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlRm9sZFdpZGdldFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLU9wdGlvbi1dXCIsIHdpbjogXCJDdHJsLVNoaWZ0LV1cIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZUZvbGRXaWRnZXRcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1LIENvbW1hbmQtMFwiLCB3aW46IFwiQ3RybC1LIEN0cmwtMFwiIH0sXG4gICAgICAgIG5hbWU6IFwiZm9sZGFsbFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLUsgQ29tbWFuZC1KXCIsIHdpbjogXCJDdHJsLUsgQ3RybC1KXCIgfSxcbiAgICAgICAgbmFtZTogXCJ1bmZvbGRhbGxcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1LIENvbW1hbmQtMVwiLCB3aW46IFwiQ3RybC1LIEN0cmwtMVwiIH0sXG4gICAgICAgIG5hbWU6IFwiZm9sZE90aGVyXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtSyBDb21tYW5kLVFcIiwgd2luOiBcIkN0cmwtSyBDdHJsLVFcIiB9LFxuICAgICAgICBuYW1lOiBcIm5hdmlnYXRlVG9MYXN0RWRpdExvY2F0aW9uXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtSyBDb21tYW5kLVJ8Q29tbWFuZC1LIENvbW1hbmQtU1wiLCB3aW46IFwiQ3RybC1LIEN0cmwtUnxDdHJsLUsgQ3RybC1TXCIgfSxcbiAgICAgICAgbmFtZTogXCJzaG93S2V5Ym9hcmRTaG9ydGN1dHNcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiQ29tbWFuZC1LIENvbW1hbmQtWFwiLCB3aW46IFwiQ3RybC1LIEN0cmwtWFwiIH0sXG4gICAgICAgIG5hbWU6IFwidHJpbVRyYWlsaW5nU3BhY2VcIlxuICAgIH0sIHtcbiAgICAgICAgYmluZEtleTogeyBtYWM6IFwiU2hpZnQtRG93bnxDb21tYW5kLVNoaWZ0LURvd25cIiwgd2luOiBcIlNoaWZ0LURvd258Q3RybC1TaGlmdC1Eb3duXCIgfSxcbiAgICAgICAgbmFtZTogXCJzZWxlY3Rkb3duXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIlNoaWZ0LVVwfENvbW1hbmQtU2hpZnQtVXBcIiwgd2luOiBcIlNoaWZ0LVVwfEN0cmwtU2hpZnQtVXBcIiB9LFxuICAgICAgICBuYW1lOiBcInNlbGVjdHVwXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIkNvbW1hbmQtQWx0LUVudGVyXCIsIHdpbjogXCJDdHJsLUFsdC1FbnRlclwiIH0sXG4gICAgICAgIG5hbWU6IFwicmVwbGFjZUFsbFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLVNoaWZ0LTFcIiwgd2luOiBcIkN0cmwtU2hpZnQtMVwiIH0sXG4gICAgICAgIG5hbWU6IFwicmVwbGFjZU9uZVwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJPcHRpb24tQ1wiLCB3aW46IFwiQWx0LUNcIiB9LFxuICAgICAgICBuYW1lOiBcInRvZ2dsZUZpbmRDYXNlU2Vuc2l0aXZlXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIk9wdGlvbi1MXCIsIHdpbjogXCJBbHQtTFwiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlRmluZEluU2VsZWN0aW9uXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIk9wdGlvbi1SXCIsIHdpbjogXCJBbHQtUlwiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlRmluZFJlZ2V4XCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIk9wdGlvbi1XXCIsIHdpbjogXCJBbHQtV1wiIH0sXG4gICAgICAgIG5hbWU6IFwidG9nZ2xlRmluZFdob2xlV29yZFwiXG4gICAgfSwge1xuICAgICAgICBiaW5kS2V5OiB7IG1hYzogXCJDb21tYW5kLUxcIiwgd2luOiBcIkN0cmwtTFwiIH0sXG4gICAgICAgIG5hbWU6IFwiZXhwYW5kdG9saW5lXCJcbiAgICB9LCB7XG4gICAgICAgIGJpbmRLZXk6IHsgbWFjOiBcIlNoaWZ0LUVzY1wiLCB3aW46IFwiU2hpZnQtRXNjXCIgfSxcbiAgICAgICAgbmFtZTogXCJyZW1vdmVTZWNvbmRhcnlDdXJzb3JzXCJcbiAgICB9XG5dLmZvckVhY2goZnVuY3Rpb24gKGJpbmRpbmcpIHtcbiAgICB2YXIgY29tbWFuZCA9IGV4cG9ydHMuaGFuZGxlci5jb21tYW5kc1tiaW5kaW5nLm5hbWVdO1xuICAgIGlmIChjb21tYW5kKVxuICAgICAgICBjb21tYW5kLmJpbmRLZXkgPSBiaW5kaW5nLmJpbmRLZXk7XG4gICAgZXhwb3J0cy5oYW5kbGVyLmJpbmRLZXkoYmluZGluZy5iaW5kS2V5LCBjb21tYW5kIHx8IGJpbmRpbmcubmFtZSk7XG59KTtcblxufSk7ICAgICAgICAgICAgICAgIChmdW5jdGlvbigpIHtcbiAgICAgICAgICAgICAgICAgICAgYWNlLnJlcXVpcmUoW1wiYWNlL2tleWJvYXJkL3ZzY29kZVwiXSwgZnVuY3Rpb24obSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHR5cGVvZiBtb2R1bGUgPT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgZXhwb3J0cyA9PSBcIm9iamVjdFwiICYmIG1vZHVsZSkge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIG1vZHVsZS5leHBvcnRzID0gbTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfSk7XG4gICAgICAgICAgICAgICAgfSkoKTtcbiAgICAgICAgICAgICJdLCJuYW1lcyI6W10sInNvdXJjZVJvb3QiOiIifQ==