"use strict";
(globalThis["webpackChunkui"] = globalThis["webpackChunkui"] || []).push([["editor_MonacoEditorCore_tsx"],{

/***/ "./editor/MonacoEditorCore.tsx"
/*!*************************************!*\
  !*** ./editor/MonacoEditorCore.tsx ***!
  \*************************************/
(__unused_webpack_module, __webpack_exports__, __webpack_require__) {

__webpack_require__.r(__webpack_exports__);
/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   "default": () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony import */ var monaco_editor__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(/*! monaco-editor */ "./node_modules/.pnpm/monaco-editor@0.55.1/node_modules/monaco-editor/esm/vs/editor/editor.main.js?acb8");
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_1__ = __webpack_require__(/*! react */ "./node_modules/.pnpm/react@19.2.5/node_modules/react/index.js");
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_1___default = /*#__PURE__*/__webpack_require__.n(react__WEBPACK_IMPORTED_MODULE_1__);
/* harmony import */ var _hooks__WEBPACK_IMPORTED_MODULE_2__ = __webpack_require__(/*! ../hooks */ "./hooks.ts");
/* harmony import */ var _selectors__WEBPACK_IMPORTED_MODULE_3__ = __webpack_require__(/*! ../selectors */ "./selectors/index.ts");
/* harmony import */ var _rust_monaco_def__WEBPACK_IMPORTED_MODULE_4__ = __webpack_require__(/*! ./rust_monaco_def */ "./editor/rust_monaco_def.ts");
/* harmony import */ var _Editor_module_css__WEBPACK_IMPORTED_MODULE_5__ = __webpack_require__(/*! ./Editor.module.css */ "./editor/Editor.module.css");
/* harmony import */ var react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__ = __webpack_require__(/*! react/jsx-runtime */ "./node_modules/.pnpm/react@19.2.5/node_modules/react/jsx-runtime.js");







async function remeasureFontWhenReady(fonts, font) {
  while (!fonts.check(font)) {
    await fonts.ready;
  }
  monaco_editor__WEBPACK_IMPORTED_MODULE_0__.editor.remeasureFonts();
}
function useEditorProp(editor, prop, whenPresent) {
  (0,react__WEBPACK_IMPORTED_MODULE_1__.useEffect)(() => {
    if (!editor) {
      return;
    }
    const model = editor.getModel();
    if (!model) {
      return;
    }
    return whenPresent(editor, model, prop);
  }, [editor, prop, whenPresent]);
}
const MonacoEditorCore = props => {
  const [editor, setEditor] = (0,react__WEBPACK_IMPORTED_MODULE_1__.useState)(null);
  const theme = (0,_hooks__WEBPACK_IMPORTED_MODULE_2__.useAppSelector)(s => s.configuration.monaco.theme);
  const completionProvider = (0,react__WEBPACK_IMPORTED_MODULE_1__.useRef)(null);
  const autocompleteOnUse = (0,_hooks__WEBPACK_IMPORTED_MODULE_2__.useAppSelector)(_selectors__WEBPACK_IMPORTED_MODULE_3__.offerCrateAutocompleteOnUse);
  // Replace `initialCode` and `initialTheme` with an "effect event"
  // when those stabilize.
  //
  // https://react.dev/learn/separating-events-from-effects#declaring-an-effect-event
  const initialCode = (0,react__WEBPACK_IMPORTED_MODULE_1__.useRef)(props.code);
  const initialTheme = (0,react__WEBPACK_IMPORTED_MODULE_1__.useRef)(theme);
  // One-time setup
  (0,react__WEBPACK_IMPORTED_MODULE_1__.useEffect)(() => {
    monaco_editor__WEBPACK_IMPORTED_MODULE_0__.editor.defineTheme('vscode-dark-plus', _rust_monaco_def__WEBPACK_IMPORTED_MODULE_4__.themeVsDarkPlus);
  }, []);
  // Construct the editor
  const child = (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)(node => {
    if (!node) {
      return;
    }
    const nodeStyle = window.getComputedStyle(node);
    const editor = monaco_editor__WEBPACK_IMPORTED_MODULE_0__.editor.create(node, {
      language: 'rust',
      value: initialCode.current,
      theme: initialTheme.current,
      fontSize: parseInt(nodeStyle.fontSize, 10),
      fontFamily: nodeStyle.fontFamily,
      automaticLayout: true,
      'semanticHighlighting.enabled': true,
      autoClosingOvertype: 'always'
    });
    setEditor(editor);
    remeasureFontWhenReady(document.fonts, nodeStyle.font);
    editor.focus();
  }, []);
  useEditorProp(editor, props.onEditCode, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((_editor, model, onEditCode) => {
    model.onDidChangeContent(() => {
      onEditCode(model.getValue());
    });
  }, []));
  useEditorProp(editor, props.execute, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((editor, _model, execute) => {
    editor.addCommand(monaco_editor__WEBPACK_IMPORTED_MODULE_0__.KeyMod.CtrlCmd | monaco_editor__WEBPACK_IMPORTED_MODULE_0__.KeyCode.Enter, () => {
      execute();
    });
    // Ace's Vim mode runs code with :w, so let's do the same
    editor.addCommand(monaco_editor__WEBPACK_IMPORTED_MODULE_0__.KeyMod.CtrlCmd | monaco_editor__WEBPACK_IMPORTED_MODULE_0__.KeyCode.KeyS, () => {
      execute();
    });
  }, []));
  useEditorProp(editor, props.code, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((editor, model, code) => {
    // Short-circuit if nothing interesting to change.
    if (code === model.getValue()) {
      return;
    }
    editor.executeEdits('redux', [{
      text: code,
      range: model.getFullModelRange()
    }]);
  }, []));
  useEditorProp(editor, theme, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((editor, _model, theme) => {
    editor.updateOptions({
      theme
    });
  }, []));
  const autocompleteProps = (0,react__WEBPACK_IMPORTED_MODULE_1__.useMemo)(() => ({
    autocompleteOnUse,
    crates: props.crates
  }), [autocompleteOnUse, props.crates]);
  useEditorProp(editor, autocompleteProps, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((_editor, _model, {
    autocompleteOnUse,
    crates
  }) => {
    completionProvider.current = monaco_editor__WEBPACK_IMPORTED_MODULE_0__.languages.registerCompletionItemProvider('rust', {
      triggerCharacters: [' '],
      provideCompletionItems(model, position, _context, _token) {
        const word = model.getWordUntilPosition(position);
        function wordBefore(word) {
          const prevPos = {
            lineNumber: position.lineNumber,
            column: word.startColumn - 1
          };
          return model.getWordAtPosition(prevPos);
        }
        const preWord = wordBefore(word);
        const prePreWord = preWord && wordBefore(preWord);
        const oldStyle = prePreWord?.word === 'extern' && preWord?.word === 'crate';
        const newStyle = autocompleteOnUse && preWord?.word === 'use';
        const triggerPrefix = oldStyle || newStyle;
        if (!triggerPrefix) {
          return {
            suggestions: []
          };
        }
        const range = {
          startLineNumber: position.lineNumber,
          endLineNumber: position.lineNumber,
          startColumn: word.startColumn,
          endColumn: word.endColumn
        };
        const suggestions = crates.map(({
          name,
          version,
          id
        }) => ({
          kind: monaco_editor__WEBPACK_IMPORTED_MODULE_0__.languages.CompletionItemKind.Module,
          label: `${name} (${version})`,
          insertText: `${id}; // ${version}`,
          range
        }));
        return {
          suggestions
        };
      }
    });
    return () => {
      completionProvider.current?.dispose();
    };
  }, []));
  useEditorProp(editor, props.position, (0,react__WEBPACK_IMPORTED_MODULE_1__.useCallback)((editor, _model, {
    line,
    column
  }) => {
    editor.setPosition({
      lineNumber: line,
      column
    });
    editor.focus();
  }, []));
  return /*#__PURE__*/(0,react_jsx_runtime__WEBPACK_IMPORTED_MODULE_6__.jsx)("div", {
    className: _Editor_module_css__WEBPACK_IMPORTED_MODULE_5__.monaco,
    ref: child
  });
};
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (MonacoEditorCore);

/***/ },

/***/ "./editor/rust_monaco_def.ts"
/*!***********************************!*\
  !*** ./editor/rust_monaco_def.ts ***!
  \***********************************/
(__unused_webpack_module, __webpack_exports__, __webpack_require__) {

__webpack_require__.r(__webpack_exports__);
/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   themeVsDarkPlus: () => (/* binding */ themeVsDarkPlus)
/* harmony export */ });
// This is left as a placeholder theme to avoid having to migrate
// everyone away.
const themeVsDarkPlus = {
  base: 'vs-dark',
  inherit: true,
  colors: {},
  rules: []
};

/***/ }

}]);
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiZWRpdG9yX01vbmFjb0VkaXRvckNvcmVfdHN4LTI1NGE2NWY4ZGI0ZTNmZjhhZDA2LmpzIiwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQUF3QztBQUN5QztBQUV2QztBQUNpQjtBQUVQO0FBRU47QUFBQTtBQUU5QyxlQUFlYSxzQkFBc0JBLENBQUNDLEtBQWtCLEVBQUVDLElBQVk7RUFDcEUsT0FBTyxDQUFDRCxLQUFLLENBQUNFLEtBQUssQ0FBQ0QsSUFBSSxDQUFDLEVBQUU7SUFDekIsTUFBTUQsS0FBSyxDQUFDRyxLQUFLO0VBQ25CO0VBRUFqQixpREFBYSxDQUFDbUIsY0FBYyxFQUFFO0FBQ2hDO0FBRUEsU0FBU0MsYUFBYUEsQ0FDcEJGLE1BQWtELEVBQ2xERyxJQUFPLEVBQ1BDLFdBSXdCO0VBRXhCbkIsZ0RBQVMsQ0FBQyxNQUFLO0lBQ2IsSUFBSSxDQUFDZSxNQUFNLEVBQUU7TUFDWDtJQUNGO0lBRUEsTUFBTUssS0FBSyxHQUFHTCxNQUFNLENBQUNNLFFBQVEsRUFBRTtJQUMvQixJQUFJLENBQUNELEtBQUssRUFBRTtNQUNWO0lBQ0Y7SUFFQSxPQUFPRCxXQUFXLENBQUNKLE1BQU0sRUFBRUssS0FBSyxFQUFFRixJQUFJLENBQUM7RUFDekMsQ0FBQyxFQUFFLENBQUNILE1BQU0sRUFBRUcsSUFBSSxFQUFFQyxXQUFXLENBQUMsQ0FBQztBQUNqQztBQUVBLE1BQU1HLGdCQUFnQixHQUFpQ0MsS0FBSyxJQUFJO0VBQzlELE1BQU0sQ0FBQ1IsTUFBTSxFQUFFUyxTQUFTLENBQUMsR0FBR3JCLCtDQUFRLENBQTZDLElBQUksQ0FBQztFQUN0RixNQUFNc0IsS0FBSyxHQUFHckIsc0RBQWMsQ0FBRXNCLENBQUMsSUFBS0EsQ0FBQyxDQUFDQyxhQUFhLENBQUM5QixNQUFNLENBQUM0QixLQUFLLENBQUM7RUFDakUsTUFBTUcsa0JBQWtCLEdBQUcxQiw2Q0FBTSxDQUE0QixJQUFJLENBQUM7RUFDbEUsTUFBTTJCLGlCQUFpQixHQUFHekIsc0RB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LEtBQUssQ0FBQ2tELFFBQVEsRUFDZDFFLGtEQUFXLENBQUMsQ0FBQ2dCLE1BQU0sRUFBRXdDLE1BQU0sRUFBRTtJQUFFZ0QsSUFBSTtJQUFFdEI7RUFBTSxDQUFFLEtBQUk7SUFDL0NsRSxNQUFNLENBQUN5RixXQUFXLENBQUM7TUFBRXhCLFVBQVUsRUFBRXVCLElBQUk7TUFBRXRCO0lBQU0sQ0FBRSxDQUFDO0lBQ2hEbEUsTUFBTSxDQUFDa0MsS0FBSyxFQUFFO0VBQ2hCLENBQUMsRUFBRSxFQUFFLENBQUMsQ0FDUDtFQUVELG9CQUFPeEMsc0RBQUE7SUFBS2dHLFNBQVMsRUFBRWxHLHNEQUFjO0lBQUNtRyxHQUFHLEVBQUV4RTtFQUFNLEVBQUc7QUFDdEQsQ0FBQztBQUVELGlFQUFlWixnQkFBZ0IsRTs7Ozs7Ozs7Ozs7Ozs7QUMxTS9CO0FBQ0E7QUFDTyxNQUFNaEIsZUFBZSxHQUFnQztFQUMxRHFHLElBQUksRUFBRSxTQUFTO0VBQ2ZDLE9BQU8sRUFBRSxJQUFJO0VBQ2JDLE1BQU0sRUFBRSxFQUFFO0VBQ1ZDLEtBQUssRUFBRTtDQUNSLEMiLCJzb3VyY2VzIjpbIndlYnBhY2s6Ly91aS8uL2VkaXRvci9Nb25hY29FZGl0b3JDb3JlLnRzeCIsIndlYnBhY2s6Ly91aS8uL2VkaXRvci9ydXN0X21vbmFjb19kZWYudHMiXSwic291cmNlc0NvbnRlbnQiOlsiaW1wb3J0ICogYXMgbW9uYWNvIGZyb20gJ21vbmFjby1lZGl0b3InO1xuaW1wb3J0IFJlYWN0LCB7IHVzZUNhbGxiYWNrLCB1c2VFZmZlY3QsIHVzZU1lbW8sIHVzZVJlZiwgdXNlU3RhdGUgfSBmcm9tICdyZWFjdCc7XG5cbmltcG9ydCB7IHVzZUFwcFNlbGVjdG9yIH0gZnJvbSAnLi4vaG9va3MnO1xuaW1wb3J0IHsgb2ZmZXJDcmF0ZUF1dG9jb21wbGV0ZU9uVXNlIH0gZnJvbSAnLi4vc2VsZWN0b3JzJztcbmltcG9ydCB7IENvbW1vbkVkaXRvclByb3BzIH0gZnJvbSAnLi4vdHlwZXMnO1xuaW1wb3J0IHsgdGhlbWVWc0RhcmtQbHVzIH0gZnJvbSAnLi9ydXN0X21vbmFjb19kZWYnO1xuXG5pbXBvcnQgKiBhcyBzdHlsZXMgZnJvbSAnLi9FZGl0b3IubW9kdWxlLmNzcyc7XG5cbmFzeW5jIGZ1bmN0aW9uIHJlbWVhc3VyZUZvbnRXaGVuUmVhZHkoZm9udHM6IEZvbnRGYWNlU2V0LCBmb250OiBzdHJpbmcpIHtcbiAgd2hpbGUgKCFmb250cy5jaGVjayhmb250KSkge1xuICAgIGF3YWl0IGZvbnRzLnJlYWR5O1xuICB9XG5cbiAgbW9uYWNvLmVkaXRvci5yZW1lYXN1cmVGb250cygpO1xufVxuXG5mdW5jdGlvbiB1c2VFZGl0b3JQcm9wPFQ+KFxuICBlZGl0b3I6IG1vbmFjby5lZGl0b3IuSVN0YW5kYWxvbmVDb2RlRWRpdG9yIHwgbnVsbCxcbiAgcHJvcDogVCxcbiAgd2hlblByZXNlbnQ6IChcbiAgICBlZGl0b3I6IG1vbmFjby5lZGl0b3IuSVN0YW5kYWxvbmVDb2RlRWRpdG9yLFxuICAgIG1vZGVsOiBtb25hY28uZWRpdG9yLklUZXh0TW9kZWwsXG4gICAgcHJvcDogVCxcbiAgKSA9PiB2b2lkIHwgKCgpID0+IHZvaWQpLFxuKSB7XG4gIHVzZUVmZmVjdCgoKSA9PiB7XG4gICAgaWYgKCFlZGl0b3IpIHtcbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICBjb25zdCBtb2RlbCA9IGVkaXRvci5nZXRNb2RlbCgpO1xuICAgIGlmICghbW9kZWwpIHtcbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICByZXR1cm4gd2hlblByZXNlbnQoZWRpdG9yLCBtb2RlbCwgcHJvcCk7XG4gIH0sIFtlZGl0b3IsIHByb3AsIHdoZW5QcmVzZW50XSk7XG59XG5cbmNvbnN0IE1vbmFjb0VkaXRvckNvcmU6IFJlYWN0LkZDPENvbW1vbkVkaXRvclByb3BzPiA9IChwcm9wcykgPT4ge1xuICBjb25zdCBbZWRpdG9yLCBzZXRFZGl0b3JdID0gdXNlU3RhdGU8bW9uYWNvLmVkaXRvci5JU3RhbmRhbG9uZUNvZGVFZGl0b3IgfCBudWxsPihudWxsKTtcbiAgY29uc3QgdGhlbWUgPSB1c2VBcHBTZWxlY3RvcigocykgPT4gcy5jb25maWd1cmF0aW9uLm1vbmFjby50aGVtZSk7XG4gIGNvbnN0IGNvbXBsZXRpb25Qcm92aWRlciA9IHVzZVJlZjxtb25hY28uSURpc3Bvc2FibGUgfCBudWxsPihudWxsKTtcbiAgY29uc3QgYXV0b2NvbXBsZXRlT25Vc2UgPSB1c2VBcHBTZWxlY3RvcihvZmZlckNyYXRlQXV0b2NvbXBsZXRlT25Vc2UpO1xuXG4gIC8vIFJlcGxhY2UgYGluaXRpYWxDb2RlYCBhbmQgYGluaXRpYWxUaGVtZWAgd2l0aCBhbiBcImVmZmVjdCBldmVudFwiXG4gIC8vIHdoZW4gdGhvc2Ugc3RhYmlsaXplLlxuICAvL1xuICAvLyBodHRwczovL3JlYWN0LmRldi9sZWFybi9zZXBhcmF0aW5nLWV2ZW50cy1mcm9tLWVmZmVjdHMjZGVjbGFyaW5nLWFuLWVmZmVjdC1ldmVudFxuICBjb25zdCBpbml0aWFsQ29kZSA9IHVzZVJlZihwcm9wcy5jb2RlKTtcbiAgY29uc3QgaW5pdGlhbFRoZW1lID0gdXNlUmVmKHRoZW1lKTtcblxuICAvLyBPbmUtdGltZSBzZXR1cFxuICB1c2VFZmZlY3QoKCkgPT4ge1xuICAgIG1vbmFjby5lZGl0b3IuZGVmaW5lVGhlbWUoJ3ZzY29kZS1kYXJrLXBsdXMnLCB0aGVtZVZzRGFya1BsdXMpO1xuICB9LCBbXSk7XG5cbiAgLy8gQ29uc3RydWN0IHRoZSBlZGl0b3JcbiAgY29uc3QgY2hpbGQgPSB1c2VDYWxsYmFjaygobm9kZTogSFRNTERpdkVsZW1lbnQgfCBudWxsKSA9PiB7XG4gICAgaWYgKCFub2RlKSB7XG4gICAgICByZXR1cm47XG4gICAgfVxuXG4gICAgY29uc3Qgbm9kZVN0eWxlID0gd2luZG93LmdldENvbXB1dGVkU3R5bGUobm9kZSk7XG5cbiAgICBjb25zdCBlZGl0b3IgPSBtb25hY28uZWRpdG9yLmNyZWF0ZShub2RlLCB7XG4gICAgICBsYW5ndWFnZTogJ3J1c3QnLFxuICAgICAgdmFsdWU6IGluaXRpYWxDb2RlLmN1cnJlbnQsXG4gICAgICB0aGVtZTogaW5pdGlhbFRoZW1lLmN1cnJlbnQsXG4gICAgICBmb250U2l6ZTogcGFyc2VJbnQobm9kZVN0eWxlLmZvbnRTaXplLCAxMCksXG4gICAgICBmb250RmFtaWx5OiBub2RlU3R5bGUuZm9udEZhbWlseSxcbiAgICAgIGF1dG9tYXRpY0xheW91dDogdHJ1ZSxcbiAgICAgICdzZW1hbnRpY0hpZ2hsaWdodGluZy5lbmFibGVkJzogdHJ1ZSxcbiAgICAgIGF1dG9DbG9zaW5nT3ZlcnR5cGU6ICdhbHdheXMnLFxuICAgIH0pO1xuICAgIHNldEVkaXRvcihlZGl0b3IpO1xuXG4gICAgcmVtZWFzdXJlRm9udFdoZW5SZWFkeShkb2N1bWVudC5mb250cywgbm9kZVN0eWxlLmZvbnQpO1xuXG4gICAgZWRpdG9yLmZvY3VzKCk7XG4gIH0sIFtdKTtcblxuICB1c2VFZGl0b3JQcm9wKFxuICAgIGVkaXRvcixcbiAgICBwcm9wcy5vbkVkaXRDb2RlLFxuICAgIHVzZUNhbGxiYWNrKChfZWRpdG9yLCBtb2RlbCwgb25FZGl0Q29kZSkgPT4ge1xuICAgICAgbW9kZWwub25EaWRDaGFuZ2VDb250ZW50KCgpID0+IHtcbiAgICAgICAgb25FZGl0Q29kZShtb2RlbC5nZXRWYWx1ZSgpKTtcbiAgICAgIH0pO1xuICAgIH0sIFtdKSxcbiAgKTtcblxuICB1c2VFZGl0b3JQcm9wKFxuICAgIGVkaXRvcixcbiAgICBwcm9wcy5leGVjdXRlLFxuICAgIHVzZUNhbGxiYWNrKChlZGl0b3IsIF9tb2RlbCwgZXhlY3V0ZSkgPT4ge1xuICAgICAgZWRpdG9yLmFkZENvbW1hbmQobW9uYWNvLktleU1vZC5DdHJsQ21kIHwgbW9uYWNvLktleUNvZGUuRW50ZXIsICgpID0+IHtcbiAgICAgICAgZXhlY3V0ZSgpO1xuICAgICAgfSk7XG4gICAgICAvLyBBY2UncyBWaW0gbW9kZSBydW5zIGNvZGUgd2l0aCA6dywgc28gbGV0J3MgZG8gdGhlIHNhbWVcbiAgICAgIGVkaXRvci5hZGRDb21tYW5kKG1vbmFjby5LZXlNb2QuQ3RybENtZCB8IG1vbmFjby5LZXlDb2RlLktleVMsICgpID0+IHtcbiAgICAgICAgZXhlY3V0ZSgpO1xuICAgICAgfSk7XG4gICAgfSwgW10pLFxuICApO1xuXG4gIHVzZUVkaXRvclByb3AoXG4gICAgZWRpdG9yLFxuICAgIHByb3BzLmNvZGUsXG4gICAgdXNlQ2FsbGJhY2soKGVkaXRvciwgbW9kZWwsIGNvZGUpID0+IHtcbiAgICAgIC8vIFNob3J0LWNpcmN1aXQgaWYgbm90aGluZyBpbnRlcmVzdGluZyB0byBjaGFuZ2UuXG4gICAgICBpZiAoY29kZSA9PT0gbW9kZWwuZ2V0VmFsdWUoKSkge1xuICAgICAgICByZXR1cm47XG4gICAgICB9XG5cbiAgICAgIGVkaXRvci5leGVjdXRlRWRpdHMoJ3JlZHV4JywgW1xuICAgICAgICB7XG4gICAgICAgICAgdGV4dDogY29kZSxcbiAgICAgICAgICByYW5nZTogbW9kZWwuZ2V0RnVsbE1vZGVsUmFuZ2UoKSxcbiAgICAgICAgfSxcbiAgICAgIF0pO1xuICAgIH0sIFtdKSxcbiAgKTtcblxuICB1c2VFZGl0b3JQcm9wKFxuICAgIGVkaXRvcixcbiAgICB0aGVtZSxcbiAgICB1c2VDYWxsYmFjaygoZWRpdG9yLCBfbW9kZWwsIHRoZW1lKSA9PiB7XG4gICAgICBlZGl0b3IudXBkYXRlT3B0aW9ucyh7IHRoZW1lIH0pO1xuICAgIH0sIFtdKSxcbiAgKTtcblxuICBjb25zdCBhdXRvY29tcGxldGVQcm9wcyA9IHVzZU1lbW8oXG4gICAgKCkgPT4gKHsgYXV0b2NvbXBsZXRlT25Vc2UsIGNyYXRlczogcHJvcHMuY3JhdGVzIH0pLFxuICAgIFthdXRvY29tcGxldGVPblVzZSwgcHJvcHMuY3JhdGVzXSxcbiAgKTtcblxuICB1c2VFZGl0b3JQcm9wKFxuICAgIGVkaXRvcixcbiAgICBhdXRvY29tcGxldGVQcm9wcyxcbiAgICB1c2VDYWxsYmFjaygoX2VkaXRvciwgX21vZGVsLCB7IGF1dG9jb21wbGV0ZU9uVXNlLCBjcmF0ZXMgfSkgPT4ge1xuICAgICAgY29tcGxldGlvblByb3ZpZGVyLmN1cnJlbnQgPSBtb25hY28ubGFuZ3VhZ2VzLnJlZ2lzdGVyQ29tcGxldGlvbkl0ZW1Qcm92aWRlcigncnVzdCcsIHtcbiAgICAgICAgdHJpZ2dlckNoYXJhY3RlcnM6IFsnICddLFxuXG4gICAgICAgIHByb3ZpZGVDb21wbGV0aW9uSXRlbXMobW9kZWwsIHBvc2l0aW9uLCBfY29udGV4dCwgX3Rva2VuKSB7XG4gICAgICAgICAgY29uc3Qgd29yZCA9IG1vZGVsLmdldFdvcmRVbnRpbFBvc2l0aW9uKHBvc2l0aW9uKTtcblxuICAgICAgICAgIGZ1bmN0aW9uIHdvcmRCZWZvcmUoXG4gICAgICAgICAgICB3b3JkOiBtb25hY28uZWRpdG9yLklXb3JkQXRQb3NpdGlvbixcbiAgICAgICAgICApOiBtb25hY28uZWRpdG9yLklXb3JkQXRQb3NpdGlvbiB8IG51bGwge1xuICAgICAgICAgICAgY29uc3QgcHJldlBvcyA9IHsgbGluZU51bWJlcjogcG9zaXRpb24ubGluZU51bWJlciwgY29sdW1uOiB3b3JkLnN0YXJ0Q29sdW1uIC0gMSB9O1xuICAgICAgICAgICAgcmV0dXJuIG1vZGVsLmdldFdvcmRBdFBvc2l0aW9uKHByZXZQb3MpO1xuICAgICAgICAgIH1cblxuICAgICAgICAgIGNvbnN0IHByZVdvcmQgPSB3b3JkQmVmb3JlKHdvcmQpO1xuICAgICAgICAgIGNvbnN0IHByZVByZVdvcmQgPSBwcmVXb3JkICYmIHdvcmRCZWZvcmUocHJlV29yZCk7XG5cbiAgICAgICAgICBjb25zdCBvbGRTdHlsZSA9IHByZVByZVdvcmQ/LndvcmQgPT09ICdleHRlcm4nICYmIHByZVdvcmQ/LndvcmQgPT09ICdjcmF0ZSc7XG4gICAgICAgICAgY29uc3QgbmV3U3R5bGUgPSBhdXRvY29tcGxldGVPblVzZSAmJiBwcmVXb3JkPy53b3JkID09PSAndXNlJztcblxuICAgICAgICAgIGNvbnN0IHRyaWdnZXJQcmVmaXggPSBvbGRTdHlsZSB8fCBuZXdTdHlsZTtcblxuICAgICAgICAgIGlmICghdHJpZ2dlclByZWZpeCkge1xuICAgICAgICAgICAgcmV0dXJuIHsgc3VnZ2VzdGlvbnM6IFtdIH07XG4gICAgICAgICAgfVxuXG4gICAgICAgICAgY29uc3QgcmFuZ2UgPSB7XG4gICAgICAgICAgICBzdGFydExpbmVOdW1iZXI6IHBvc2l0aW9uLmxpbmVOdW1iZXIsXG4gICAgICAgICAgICBlbmRMaW5lTnVtYmVyOiBwb3NpdGlvbi5saW5lTnVtYmVyLFxuICAgICAgICAgICAgc3RhcnRDb2x1bW46IHdvcmQuc3RhcnRDb2x1bW4sXG4gICAgICAgICAgICBlbmRDb2x1bW46IHdvcmQuZW5kQ29sdW1uLFxuICAgICAgICAgIH07XG5cbiAgICAgICAgICBjb25zdCBzdWdnZXN0aW9ucyA9IGNyYXRlcy5tYXAoKHsgbmFtZSwgdmVyc2lvbiwgaWQgfSkgPT4gKHtcbiAgICAgICAgICAgIGtpbmQ6IG1vbmFjby5sYW5ndWFnZXMuQ29tcGxldGlvbkl0ZW1LaW5kLk1vZHVsZSxcbiAgICAgICAgICAgIGxhYmVsOiBgJHtuYW1lfSAoJHt2ZXJzaW9ufSlgLFxuICAgICAgICAgICAgaW5zZXJ0VGV4dDogYCR7aWR9OyAvLyAke3ZlcnNpb259YCxcbiAgICAgICAgICAgIHJhbmdlLFxuICAgICAgICAgIH0pKTtcblxuICAgICAgICAgIHJldHVybiB7IHN1Z2dlc3Rpb25zIH07XG4gICAgICAgIH0sXG4gICAgICB9KTtcblxuICAgICAgcmV0dXJuICgpID0+IHtcbiAgICAgICAgY29tcGxldGlvblByb3ZpZGVyLmN1cnJlbnQ/LmRpc3Bvc2UoKTtcbiAgICAgIH07XG4gICAgfSwgW10pLFxuICApO1xuXG4gIHVzZUVkaXRvclByb3AoXG4gICAgZWRpdG9yLFxuICAgIHByb3BzLnBvc2l0aW9uLFxuICAgIHVzZUNhbGxiYWNrKChlZGl0b3IsIF9tb2RlbCwgeyBsaW5lLCBjb2x1bW4gfSkgPT4ge1xuICAgICAgZWRpdG9yLnNldFBvc2l0aW9uKHsgbGluZU51bWJlcjogbGluZSwgY29sdW1uIH0pO1xuICAgICAgZWRpdG9yLmZvY3VzKCk7XG4gICAgfSwgW10pLFxuICApO1xuXG4gIHJldHVybiA8ZGl2IGNsYXNzTmFtZT17c3R5bGVzLm1vbmFjb30gcmVmPXtjaGlsZH0gLz47XG59O1xuXG5leHBvcnQgZGVmYXVsdCBNb25hY29FZGl0b3JDb3JlO1xuIiwiaW1wb3J0IHsgZWRpdG9yIH0gZnJvbSAnbW9uYWNvLWVkaXRvcic7XG5cbi8vIFRoaXMgaXMgbGVmdCBhcyBhIHBsYWNlaG9sZGVyIHRoZW1lIHRvIGF2b2lkIGhhdmluZyB0byBtaWdyYXRlXG4vLyBldmVyeW9uZSBhd2F5LlxuZXhwb3J0IGNvbnN0IHRoZW1lVnNEYXJrUGx1czogZWRpdG9yLklTdGFuZGFsb25lVGhlbWVEYXRhID0ge1xuICBiYXNlOiAndnMtZGFyaycsXG4gIGluaGVyaXQ6IHRydWUsXG4gIGNvbG9yczoge30sXG4gIHJ1bGVzOiBbXSxcbn07XG4iXSwibmFtZXMiOlsibW9uYWNvIiwiUmVhY3QiLCJ1c2VDYWxsYmFjayIsInVzZUVmZmVjdCIsInVzZU1lbW8iLCJ1c2VSZWYiLCJ1c2VTdGF0ZSIsInVzZUFwcFNlbGVjdG9yIiwib2ZmZXJDcmF0ZUF1dG9jb21wbGV0ZU9uVXNlIiwidGhlbWVWc0RhcmtQbHVzIiwic3R5bGVzIiwianN4IiwiX2pzeCIsInJlbWVhc3VyZUZvbnRXaGVuUmVhZHkiLCJmb250cyIsImZvbnQiLCJjaGVjayIsInJlYWR5IiwiZWRpdG9yIiwicmVtZWFzdXJlRm9udHMiLCJ1c2VFZGl0b3JQcm9wIiwicHJvcCIsIndoZW5QcmVzZW50IiwibW9kZWwiLCJnZXRNb2RlbCIsIk1vbmFjb0VkaXRvckNvcmUiLCJwcm9wcyIsInNldEVkaXRvciIsInRoZW1lIiwicyIsImNvbmZpZ3VyYXRpb24iLCJjb21wbGV0aW9uUHJvdmlkZXIiLCJhdXRvY29tcGxldGVPblVzZSIsImluaXRpYWxDb2RlIiwiY29kZSIsImluaXRpYWxUaGVtZSIsImRlZmluZVRoZW1lIiwiY2hpbGQiLCJub2RlIiwibm9kZVN0eWxlIiwid2luZG93IiwiZ2V0Q29tcHV0ZWRTdHlsZSIsImNyZWF0ZSIsImxhbmd1YWdlIiwidmFsdWUiLCJjdXJyZW50IiwiZm9udFNpemUiLCJwYXJzZUludCIsImZvbnRGYW1pbHkiLCJhdXRvbWF0aWNMYXlvdXQiLCJhdXRvQ2xvc2luZ092ZXJ0eXBlIiwiZG9jdW1lbnQiLCJmb2N1cyIsIm9uRWRpdENvZGUiLCJfZWRpdG9yIiwib25EaWRDaGFuZ2VDb250ZW50IiwiZ2V0VmFsdWUiLCJleGVjdXRlIiwiX21vZGVsIiwiYWRkQ29tbWFuZCIsIktleU1vZCIsIkN0cmxDbWQiLCJLZXlDb2RlIiwiRW50ZXIiLCJLZXlTIiwiZXhlY3V0ZUVkaXRzIiwidGV4dCIsInJhbmdlIiwiZ2V0RnVsbE1vZGVsUmFuZ2UiLCJ1cGRhdGVPcHRpb25zIiwiYXV0b2NvbXBsZXRlUHJvcHMiLCJjcmF0ZXMiLCJsYW5ndWFnZXMiLCJyZWdpc3RlckNvbXBsZXRpb25JdGVtUHJvdmlkZXIiLCJ0cmlnZ2VyQ2hhcmFjdGVycyIsInByb3ZpZGVDb21wbGV0aW9uSXRlbXMiLCJwb3NpdGlvbiIsIl9jb250ZXh0IiwiX3Rva2VuIiwid29yZCIsImdldFdvcmRVbnRpbFBvc2l0aW9uIiwid29yZEJlZm9yZSIsInByZXZQb3MiLCJsaW5lTnVtYmVyIiwiY29sdW1uIiwic3RhcnRDb2x1bW4iLCJnZXRXb3JkQXRQb3NpdGlvbiIsInByZVdvcmQiLCJwcmVQcmVXb3JkIiwib2xkU3R5bGUiLCJuZXdTdHlsZSIsInRyaWdnZXJQcmVmaXgiLCJzdWdnZXN0aW9ucyIsInN0YXJ0TGluZU51bWJlciIsImVuZExpbmVOdW1iZXIiLCJlbmRDb2x1bW4iLCJtYXAiLCJuYW1lIiwidmVyc2lvbiIsImlkIiwia2luZCIsIkNvbXBsZXRpb25JdGVtS2luZCIsIk1vZHVsZSIsImxhYmVsIiwiaW5zZXJ0VGV4dCIsImRpc3Bvc2UiLCJsaW5lIiwic2V0UG9zaXRpb24iLCJjbGFzc05hbWUiLCJyZWYiLCJiYXNlIiwiaW5oZXJpdCIsImNvbG9ycyIsInJ1bGVzIl0sInNvdXJjZVJvb3QiOiIifQ==