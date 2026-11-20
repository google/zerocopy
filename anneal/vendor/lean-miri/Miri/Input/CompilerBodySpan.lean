import Miri.Input.CompilerProviders

/-! eval_context.rs::unwind_to_block records the exact current Body.span,
including before unwind termination. It does not use the preamble definition
span or an arbitrary statement span. Shared backtrace preparation interns this
compiler span; queries may not append isolated span identities at runtime. -/
namespace Miri.Input.CompilerBodySpan
open Miri.Interpreter

def get (p : CompilerProviders.Prepared) (frame : Frame P L E) :
    Except StepError MIR.SpanRef := do
  let some body := p.program.bundle.bodies[frame.bodyIdentity.index]?
    | throw (.invalidProgram "unwind body identity absent from canonical compilation")
  unless body.body == frame.body do
    throw (.invalidProgram "unwind body identity/content mismatch")
  let source ← ((body.input.payload.getObjVal? "span").bind p.loweringContext.decodeCompilerValue).mapError StepError.unsupported
  let (span,tables) ← lowerCompilerSpan p.program.compilerTables source |>.mapError StepError.unsupported
  unless tables.spans == p.program.compilerTables.spans do
    throw (.unsupported "compiler body span absent from final shared span table")
  pure span
end Miri.Input.CompilerBodySpan
