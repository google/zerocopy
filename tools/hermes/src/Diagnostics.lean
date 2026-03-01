import Lean
-- We import the project's root module so dependencies are loaded
import «Generated»

open Lean Elab Frontend Json

-- This script acts as a headless Lean language server strictly for extracting
-- diagnostics. 
--
-- Why not just parse Lean's standard CLI `stderr` string output?
-- Lean's CLI formats errors for human consumption (`file:line:col`) and drops
-- raw byte offsets. However, to correctly map an error back to the originating
-- inline `.rs` file block, Hermes requires exact byte offsets.
-- 
-- By running the Lean `Frontend` programmatically, we capture the raw `Message`
-- objects from Lean's compiler state. We then convert the Lean `Lsp.Position`
-- back into Utf8 byte indices, and emit a structured JSON array that the Rust
-- `diagnostics.rs` mapper can seamlessly consume.
unsafe def main : IO Unit := do
  try
    -- 1. Initialize the Lean environment using Lake's search paths
    initSearchPath (← findSysroot)
    let env ← importModules #[{ module := `Generated }] {}

    -- 2. Read the target file (injected by Rust)
    let fileName := "__TARGET_FILE__"
    let fileContent ← IO.FS.readFile fileName

    -- 3. Run the Frontend (Parse + Elaborate)
    let (ctx, state) ← IO.FS.withFile fileName IO.FS.Mode.read fun h => do
      let inputCtx := Parser.mkInputContext fileContent fileName
      let (header, parserState, messages) ← Parser.parseHeader inputCtx

      -- Abort if imports fail (prevents cascading errors)
      if messages.hasErrors then
        let cmdState := Command.mkState env messages {}
        return (inputCtx, { commandState := cmdState, parserState := parserState, cmdPos := parserState.pos })

      let (env, messages) ← processHeader header {} messages inputCtx
      if messages.hasErrors then
        let cmdState := Command.mkState env messages {}
        return (inputCtx, { commandState := cmdState, parserState := parserState, cmdPos := parserState.pos })

      let cmdState := Command.mkState env messages {}
      let frontendState ← IO.processCommands inputCtx parserState cmdState
      return (inputCtx, frontendState)

    -- 4. Extract and Serialize Messages
    let messages := state.commandState.messages.toArray
    let jsonMsgs ← messages.mapM fun msg => do
      let severity := match msg.severity with
        | MessageSeverity.information => "info"
        | MessageSeverity.warning     => "warning"
        | MessageSeverity.error       => "error"

      let text ← msg.data.toString

      -- Convert Lean Position (1-based line) to LSP Position (0-based line)
      let lspStart : Lean.Lsp.Position := { line := msg.pos.line - 1, character := msg.pos.column }
      let endPos := msg.endPos.getD msg.pos
      let lspEnd : Lean.Lsp.Position := { line := endPos.line - 1, character := endPos.column }

      let byteStart := Lean.FileMap.lspPosToUtf8Pos ctx.fileMap lspStart
      let byteEnd := Lean.FileMap.lspPosToUtf8Pos ctx.fileMap lspEnd

      return Json.mkObj [
        ("file_name", fileName),
        ("byte_start", byteStart.byteIdx),
        ("byte_end", byteEnd.byteIdx),
        ("line_start", msg.pos.line),
        ("column_start", msg.pos.column),
        ("line_end", endPos.line),
        ("column_end", endPos.column),
        ("level", severity),
        ("message", text)
      ]

    -- 5. Print JSON to stdout (compact single line)
    IO.println (Json.arr jsonMsgs).compress
  catch e =>
    IO.eprintln s!"INTERNAL DIAGNOSTICS ERROR: {e}"
    IO.Process.exit 1
