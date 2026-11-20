import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.RandomDispatchMachine

/-! Source entropy shim signatures are rustc-built named queries. Physical
machine binding is RandomDispatchMachine; host entropy remains an explicit
external effect, whose absence cannot be interpreted as success. -/
namespace Miri.Input.CompilerRandomDispatch
open Miri.Interpreter

def unix (abis : CompilerNamedShimAbi.Prepared)
    (base : UnixRandomDispatch.Hooks S D B I) : UnixRandomDispatch.Hooks S D B I :=
  {base with signature := fun name => do
    unless #["getentropy","getrandom","arc4random_buf"].contains name do
      throw (.unsupported "unknown Unix entropy shim signature")
    CompilerNamedShimAbi.query abis name}

def windows (abis : CompilerNamedShimAbi.Prepared)
    (base : WindowsRandomDispatch.Hooks S D B I) : WindowsRandomDispatch.Hooks S D B I :=
  {base with signature := fun name => do
    unless #["SystemFunction036","ProcessPrng","BCryptGenRandom"].contains name do
      throw (.unsupported "unknown Windows entropy shim signature")
    CompilerNamedShimAbi.query abis name}
end Miri.Input.CompilerRandomDispatch
