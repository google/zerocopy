import Sail
import THE_MODULE_NAME.Defs

open Sail ArchSem

namespace THE_MODULE_NAME

@[simp_sail]
def sailTryCatch (e : SailM α) (h : exception → SailM α) : SailM α := PreSail.sailTryCatch e h

@[simp_sail]
def sailThrow (e : exception) : SailM α := PreSail.sailThrow e

abbrev undefined_unit (_ : Unit) : SailM Unit := PreSail.undefined_unit ()
abbrev undefined_bit (_ : Unit) : SailM (BitVec 1) := PreSail.undefined_bit ()
abbrev undefined_bool (_ : Unit) : SailM Bool := PreSail.undefined_bool ()
abbrev undefined_range (low high : Int) : SailM Int := PreSail.undefined_range low high
abbrev undefined_bitvector (n : Nat) : SailM (BitVec n) := PreSail.undefined_bitvector n
abbrev undefined_int (_ : Unit) : SailM Int := PreSail.undefined_int ()
abbrev undefined_nat (_ : Unit) : SailM Nat := PreSail.undefined_nat ()
abbrev undefined_string (_ : Unit) : SailM String := PreSail.undefined_string ()
abbrev undefined_vector (n : Nat) (a : α) : SailM (Vector α n) := PreSail.undefined_vector n a

abbrev internal_pick {α : Type} : List α → SailM α := PreSail.internal_pick

abbrev writeReg (reg : Register) (v : RegisterType reg) : SailM PUnit := PreSail.writeReg reg v

abbrev readReg (reg : Register) : SailM (RegisterType reg) := PreSail.readReg reg

abbrev RegisterRef := @Sail.ArchSem.RegisterRef

abbrev readRegRef (reg_ref : RegisterRef α) : SailM α := PreSail.readRegRef reg_ref

abbrev writeRegRef (reg_ref : RegisterRef α) (a : α) : SailM Unit := PreSail.writeRegRef reg_ref a

abbrev reg_deref (reg_ref : RegisterRef α) : SailM α := PreSail.reg_deref reg_ref

abbrev sail_assert (p : Bool) (s : String) : SailM Unit := PreSail.sail_assert p s

namespace ArchSem

abbrev sail_mem_read (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    SailM (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) :=
  PreSail.sail_mem_read req

def sail_mem_write (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) (valueBytes : Vector (BitVec 8) n) (tags : Vector Bool nt) :
    SailM (Result (Option Bool) Arch.abort) := do
  PreSail.sail_mem_write req valueBytes tags

abbrev sail_sys_reg_read (id : Arch.sys_reg_id) (r : RegisterRef α) : SailM α :=
  PreSail.sail_sys_reg_read id r

abbrev sail_sys_reg_write (id : Arch.sys_reg_id) (r : RegisterRef α) (v : α) : SailM Unit :=
  PreSail.sail_sys_reg_write id r v

abbrev sail_mem_address_announce (ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) : SailM Unit :=
  PreSail.sail_mem_address_announce ann

abbrev sail_barrier (b : Arch.barrier) : SailM Unit := PreSail.sail_barrier b
abbrev sail_cache_op (op : Arch.cache_op) : SailM Unit := PreSail.sail_cache_op op
abbrev sail_tlbi (op : Arch.tlbi) : SailM Unit := PreSail.sail_tlbi op
abbrev sail_translation_start (ts : Arch.trans_start) : SailM Unit := PreSail.sail_translation_start ts
abbrev sail_translation_end (te : Arch.trans_end) : SailM Unit := PreSail.sail_translation_end te
abbrev sail_take_exception (f : Arch.exn) : SailM Unit := PreSail.sail_take_exception f
abbrev sail_return_exception (a : Unit) : SailM Unit := PreSail.sail_return_exception a

end ArchSem

abbrev cycle_count (a : Unit) : SailM Unit := PreSail.cycle_count a
abbrev get_cycle_count (a : Unit) : SailM Nat := PreSail.get_cycle_count a
abbrev print_effect (str : String) : SailM Unit := PreSail.print_effect str
abbrev print_int_effect (str : String) (n : Int) : SailM Unit := PreSail.print_int_effect str n
abbrev print_bits_effect {w : Nat} (str : String) (x : BitVec w) : SailM Unit := PreSail.print_bits_effect str x
abbrev print_endline_effect (str : String) : SailM Unit := PreSail.print_endline_effect str

def SailME.run (m : SailME α α) : SailM α := PreSail.PreSailME.run m
def SailME.throw (e : α) : SailME α β := PreSail.PreSailME.throw e
abbrev sailTryCatchE (e : SailME β α) (h : exception → SailME β α) : SailME β α := PreSail.sailTryCatchE e h
def unwrapValue [Inhabited α] (x : SailM α) := PreSail.unwrapValue x
