Content-Length: 1540

{"id":1,"jsonrpc":"2.0","result":{"capabilities":{"callHierarchyProvider":true,"codeActionProvider":{"codeActionKinds":["quickfix","refactor","source.organizeImports"],"resolveProvider":true,"workDoneProgress":false},"colorProvider":{"workDoneProgress":false},"completionProvider":{"resolveProvider":true,"triggerCharacters":["."]},"declarationProvider":true,"definitionProvider":true,"documentHighlightProvider":true,"documentSymbolProvider":true,"experimental":{"moduleHierarchyProvider":{},"rpcProvider":{"highlightMatchesProvider":{},"rpcWireFormat":"v1"}},"foldingRangeProvider":true,"hoverProvider":true,"inlayHintProvider":{"resolveProvider":false,"workDoneProgress":false},"referencesProvider":true,"renameProvider":{"prepareProvider":true},"semanticTokensProvider":{"full":true,"legend":{"tokenModifiers":["declaration","definition","readonly","static","deprecated","abstract","async","modification","documentation","defaultLibrary"],"tokenTypes":["keyword","variable","property","function","namespace","type","class","enum","interface","struct","typeParameter","parameter","enumMember","event","method","macro","modifier","comment","string","number","regexp","operator","decorator","leanSorryLike"]},"range":true},"signatureHelpProvider":{"triggerCharacters":[" "],"workDoneProgress":false},"textDocumentSync":{"change":2,"openClose":true,"save":{"includeText":true},"willSave":false,"willSaveWaitUntil":false},"typeDefinitionProvider":true,"workspaceSymbolProvider":true},"serverInfo":{"name":"Lean 4 Server","version":"0.3.0"}}}Content-Length: 267

{"id":"register_lean_watcher","jsonrpc":"2.0","method":"client/registerCapability","params":{"registrations":[{"id":"lean_watcher","method":"workspace/didChangeWatchedFiles","registerOptions":{"watchers":[{"globPattern":"**/*.lean"},{"globPattern":"**/*.ilean"}]}}]}}Content-Length: 330

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[{"kind":1,"range":{"end":{"character":0,"line":2},"start":{"character":0,"line":0}}}],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 242

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}Content-Length: 330

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[{"kind":1,"range":{"end":{"character":0,"line":2},"start":{"character":0,"line":0}}}],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 242

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}Content-Length: 63

{"id":0,"jsonrpc":"2.0","method":"workspace/inlayHint/refresh"}Content-Length: 63

{"id":1,"jsonrpc":"2.0","method":"workspace/inlayHint/refresh"}Content-Length: 416

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[{"kind":1,"range":{"end":{"character":15,"line":0},"start":{"character":0,"line":0}}},{"kind":1,"range":{"end":{"character":0,"line":2},"start":{"character":0,"line":1}}}],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 415

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[{"kind":1,"range":{"end":{"character":0,"line":0},"start":{"character":0,"line":0}}},{"kind":1,"range":{"end":{"character":0,"line":2},"start":{"character":0,"line":1}}}],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 502

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[{"code":"lean.unknownIdentifier","fullRange":{"end":{"character":15,"line":0},"start":{"character":7,"line":0}},"message":"Unknown identifier `unknownA`","range":{"end":{"character":15,"line":0},"start":{"character":7,"line":0}},"severity":1,"source":"Lean 4"}],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}Content-Length: 763

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[{"code":"lean.unknownIdentifier","fullRange":{"end":{"character":15,"line":0},"start":{"character":7,"line":0}},"message":"Unknown identifier `unknownA`","range":{"end":{"character":15,"line":0},"start":{"character":7,"line":0}},"severity":1,"source":"Lean 4"},{"code":"lean.unknownIdentifier","fullRange":{"end":{"character":15,"line":1},"start":{"character":7,"line":1}},"message":"Unknown identifier `unknownB`","range":{"end":{"character":15,"line":1},"start":{"character":7,"line":1}},"severity":1,"source":"Lean 4"}],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}Content-Length: 246

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 246

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":1}}}Content-Length: 36

{"id":2,"jsonrpc":"2.0","result":{}}Content-Length: 63

{"id":2,"jsonrpc":"2.0","method":"workspace/inlayHint/refresh"}Content-Length: 63

{"id":3,"jsonrpc":"2.0","method":"workspace/inlayHint/refresh"}Content-Length: 68

{"id":4,"jsonrpc":"2.0","method":"workspace/semanticTokens/refresh"}Content-Length: 246

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":2}}}Content-Length: 246

{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"processing":[],"textDocument":{"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":2}}}Content-Length: 714

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[{"fullRange":{"end":{"character":6,"line":0},"start":{"character":0,"line":0}},"message":"Nat.zero : Nat","range":{"end":{"character":6,"line":0},"start":{"character":0,"line":0}},"severity":3,"source":"Lean 4"},{"code":"lean.unknownIdentifier","fullRange":{"end":{"character":15,"line":1},"start":{"character":7,"line":1}},"message":"Unknown identifier `unknownB`","range":{"end":{"character":15,"line":1},"start":{"character":7,"line":1}},"severity":1,"source":"Lean 4"}],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":2}}Content-Length: 36

{"id":3,"jsonrpc":"2.0","result":{}}Content-Length: 63

{"id":5,"jsonrpc":"2.0","method":"workspace/inlayHint/refresh"}Content-Length: 242

{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"diagnostics":[],"uri":"file:///Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-incremental-diagnostic-ab-20261001/raw/old-absent/Probe.lean","version":2}}Content-Length: 38

{"id":4,"jsonrpc":"2.0","result":null}