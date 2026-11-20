import Miri.Interpreter.IntrinsicX86.Basic
/-! Direct u32 fixslice hazmat port from pinned aes 0.9.3. The library supports
u32/u64 backends; this implements its concrete u32 software circuit, not a
replacement AES specification. Cross-backend equivalence remains a QA obligation. -/
namespace Miri.Interpreter.IntrinsicX86.Aes
open Miri.ABI
/-- Rust's fixed [u32; 8], materialized after each assignment. A function-valued
state would re-evaluate the predecessor swap circuit on every lane access. -/
abbrev State := Vector UInt32 8
instance : CoeFun State (fun _ => Fin 8 → UInt32) where
  coe state := fun index => state[index]
private def pack (a b c d e f g h : UInt32) : State :=
  ⟨#[a,b,c,d,e,f,g,h],rfl⟩

def subBytes (state : State) : State :=
  let u7 := (state 0)
  let u6 := (state 1)
  let u5 := (state 2)
  let u4 := (state 3)
  let u3 := (state 4)
  let u2 := (state 5)
  let u1 := (state 6)
  let u0 := (state 7)
  let y14 := u3 ^^^ u5
  let y13 := u0 ^^^ u6
  let y12 := y13 ^^^ y14
  let t1 := u4 ^^^ y12
  let y15 := t1 ^^^ u5
  let t2 := y12 &&& y15
  let y6 := y15 ^^^ u7
  let y20 := t1 ^^^ u1
  let y9 := u0 ^^^ u3
  let y11 := y20 ^^^ y9
  let t12 := y9 &&& y11
  let y7 := u7 ^^^ y11
  let y8 := u0 ^^^ u5
  let t0 := u1 ^^^ u2
  let y10 := y15 ^^^ t0
  let y17 := y10 ^^^ y11
  let t13 := y14 &&& y17
  let t14 := t13 ^^^ t12
  let y19 := y10 ^^^ y8
  let t15 := y8 &&& y10
  let t16 := t15 ^^^ t12
  let y16 := t0 ^^^ y11
  let y21 := y13 ^^^ y16
  let t7 := y13 &&& y16
  let y18 := u0 ^^^ y16
  let y1 := t0 ^^^ u7
  let y4 := y1 ^^^ u3
  let t5 := y4 &&& u7
  let t6 := t5 ^^^ t2
  let t18 := t6 ^^^ t16
  let t22 := t18 ^^^ y19
  let y2 := y1 ^^^ u0
  let t10 := y2 &&& y7
  let t11 := t10 ^^^ t7
  let t20 := t11 ^^^ t16
  let t24 := t20 ^^^ y18
  let y5 := y1 ^^^ u6
  let t8 := y5 &&& y1
  let t9 := t8 ^^^ t7
  let t19 := t9 ^^^ t14
  let t23 := t19 ^^^ y21
  let y3 := y5 ^^^ y8
  let t3 := y3 &&& y6
  let t4 := t3 ^^^ t2
  let t17 := t4 ^^^ y20
  let t21 := t17 ^^^ t14
  let t26 := t21 &&& t23
  let t27 := t24 ^^^ t26
  let t31 := t22 ^^^ t26
  let t25 := t21 ^^^ t22
  let t28 := t25 &&& t27
  let t29 := t28 ^^^ t22
  let z14 := t29 &&& y2
  let z5 := t29 &&& y7
  let t30 := t23 ^^^ t24
  let t32 := t31 &&& t30
  let t33 := t32 ^^^ t24
  let t35 := t27 ^^^ t33
  let t36 := t24 &&& t35
  let t38 := t27 ^^^ t36
  let t39 := t29 &&& t38
  let t40 := t25 ^^^ t39
  let t43 := t29 ^^^ t40
  let z3 := t43 &&& y16
  let tc12 := z3 ^^^ z5
  let z12 := t43 &&& y13
  let z13 := t40 &&& y5
  let z4 := t40 &&& y1
  let tc6 := z3 ^^^ z4
  let t34 := t23 ^^^ t33
  let t37 := t36 ^^^ t34
  let t41 := t40 ^^^ t37
  let z8 := t41 &&& y10
  let z17 := t41 &&& y8
  let t44 := t33 ^^^ t37
  let z0 := t44 &&& y15
  let z9 := t44 &&& y12
  let z10 := t37 &&& y3
  let z1 := t37 &&& y6
  let tc5 := z1 ^^^ z0
  let tc11 := tc6 ^^^ tc5
  let z11 := t33 &&& y4
  let t42 := t29 ^^^ t33
  let t45 := t42 ^^^ t41
  let z7 := t45 &&& y17
  let tc8 := z7 ^^^ tc6
  let z16 := t45 &&& y14
  let z6 := t42 &&& y11
  let tc16 := z6 ^^^ tc8
  let z15 := t42 &&& y9
  let tc20 := z15 ^^^ tc16
  let tc1 := z15 ^^^ z16
  let tc2 := z10 ^^^ tc1
  let tc21 := tc2 ^^^ z11
  let tc3 := z9 ^^^ tc2
  let s0 := tc3 ^^^ tc16
  let s3 := tc3 ^^^ tc11
  let s1 := s3 ^^^ tc16
  let tc13 := z13 ^^^ tc1
  let z2 := t33 &&& u7
  let tc4 := z0 ^^^ z2
  let tc7 := z12 ^^^ tc4
  let tc9 := z8 ^^^ tc7
  let tc10 := tc8 ^^^ tc9
  let tc17 := z14 ^^^ tc10
  let s5 := tc21 ^^^ tc17
  let tc26 := tc17 ^^^ tc20
  let s2 := tc26 ^^^ z17
  let tc14 := tc4 ^^^ tc12
  let tc18 := tc13 ^^^ tc14
  let s6 := tc10 ^^^ tc18
  let s7 := z12 ^^^ tc18
  let s4 := tc14 ^^^ s3
  pack s7 s6 s5 s4 s3 s2 s1 s0

def invSubBytes (state : State) : State :=
  let u7 := (state 0)
  let u6 := (state 1)
  let u5 := (state 2)
  let u4 := (state 3)
  let u3 := (state 4)
  let u2 := (state 5)
  let u1 := (state 6)
  let u0 := (state 7)
  let t23 := u0 ^^^ u3
  let t8 := u1 ^^^ t23
  let m2 := t23 &&& t8
  let t4 := u4 ^^^ t8
  let t22 := u1 ^^^ u3
  let t2 := u0 ^^^ u1
  let t1 := u3 ^^^ u4
  let t9 := u7 ^^^ t1
  let m7 := t22 &&& t9
  let t24 := u4 ^^^ u7
  let t10 := t2 ^^^ t24
  let m14 := t2 &&& t10
  let r5 := u6 ^^^ u7
  let t3 := t1 ^^^ r5
  let t13 := t2 ^^^ r5
  let t19 := t22 ^^^ r5
  let t17 := u2 ^^^ t19
  let t25 := u2 ^^^ t1
  let r13 := u1 ^^^ u6
  let t20 := t24 ^^^ r13
  let m9 := t20 &&& t17
  let r17 := u2 ^^^ u5
  let t6 := t22 ^^^ r17
  let m1 := t13 &&& t6
  let y5 := u0 ^^^ r17
  let m4 := t19 &&& y5
  let m5 := m4 ^^^ m1
  let m17 := m5 ^^^ t24
  let r18 := u5 ^^^ u6
  let t27 := t1 ^^^ r18
  let t15 := t10 ^^^ t27
  let m11 := t1 &&& t15
  let m15 := m14 ^^^ m11
  let m21 := m17 ^^^ m15
  let m12 := t4 &&& t27
  let m13 := m12 ^^^ m11
  let t14 := t10 ^^^ r18
  let m3 := t14 ^^^ m1
  let m16 := m3 ^^^ m2
  let m20 := m16 ^^^ m13
  let r19 := u2 ^^^ u4
  let t16 := r13 ^^^ r19
  let t26 := t3 ^^^ t16
  let m6 := t3 &&& t16
  let m8 := t26 ^^^ m6
  let m18 := m8 ^^^ m7
  let m22 := m18 ^^^ m13
  let m25 := m22 &&& m20
  let m26 := m21 ^^^ m25
  let m10 := m9 ^^^ m6
  let m19 := m10 ^^^ m15
  let m23 := m19 ^^^ t25
  let m28 := m23 ^^^ m25
  let m24 := m22 ^^^ m23
  let m30 := m26 &&& m24
  let m39 := m23 ^^^ m30
  let m48 := m39 &&& y5
  let m57 := m39 &&& t19
  let m36 := m24 ^^^ m25
  let m31 := m20 &&& m23
  let m27 := m20 ^^^ m21
  let m32 := m27 &&& m31
  let m29 := m28 &&& m27
  let m37 := m21 ^^^ m29
  let m42 := m37 ^^^ m39
  let m52 := m42 &&& t15
  let m61 := m42 &&& t1
  let p0 := m52 ^^^ m61
  let p16 := m57 ^^^ m61
  let m60 := m37 &&& t20
  let m51 := m37 &&& t17
  let m33 := m27 ^^^ m25
  let m38 := m32 ^^^ m33
  let m43 := m37 ^^^ m38
  let m49 := m43 &&& t16
  let p6 := m49 ^^^ m60
  let p13 := m49 ^^^ m51
  let m58 := m43 &&& t3
  let m50 := m38 &&& t9
  let m59 := m38 &&& t22
  let p1 := m58 ^^^ m59
  let p7 := p0 ^^^ p1
  let m34 := m21 &&& m22
  let m35 := m24 &&& m34
  let m40 := m35 ^^^ m36
  let m41 := m38 ^^^ m40
  let m45 := m42 ^^^ m41
  let m53 := m45 &&& t27
  let p8 := m50 ^^^ m53
  let p23 := p7 ^^^ p8
  let m62 := m45 &&& t4
  let p14 := m49 ^^^ m62
  let s6 := p14 ^^^ p23
  let m54 := m41 &&& t10
  let p2 := m54 ^^^ m62
  let p22 := p2 ^^^ p7
  let s0 := p13 ^^^ p22
  let p17 := m58 ^^^ p2
  let p15 := m54 ^^^ m59
  let m63 := m41 &&& t2
  let m44 := m39 ^^^ m40
  let m46 := m44 &&& t6
  let p5 := m46 ^^^ m51
  let p18 := m63 ^^^ p5
  let p24 := p5 ^^^ p7
  let p12 := m46 ^^^ m48
  let s3 := p12 ^^^ p22
  let m55 := m44 &&& t13
  let p9 := m55 ^^^ m63
  let s7 := p9 ^^^ p16
  let m47 := m40 &&& t8
  let p3 := m47 ^^^ m50
  let p19 := p2 ^^^ p3
  let s5 := p19 ^^^ p24
  let p11 := p0 ^^^ p3
  let p26 := p9 ^^^ p11
  let m56 := m40 &&& t23
  let p4 := m48 ^^^ m56
  let p20 := p4 ^^^ p6
  let p29 := p15 ^^^ p20
  let s1 := p26 ^^^ p29
  let p10 := m57 ^^^ p4
  let p27 := p10 ^^^ p18
  let s4 := p23 ^^^ p27
  let p25 := p6 ^^^ p10
  let p28 := p11 ^^^ p25
  let s2 := p17 ^^^ p28
  pack s7 s6 s5 s4 s3 s2 s1 s0

def subBytesNots (state : State) : State := Vector.ofFn fun i =>
  if i == 0 || i == 1 || i == 5 || i == 6 then ~~~(state i) else state i
private def rotr (value amount : UInt32) : UInt32 := (value >>> amount) ||| (value <<< (32-amount))
private def swap (state : State) (a b : Fin 8) (shift mask : UInt32) : State :=
  let t := (state a ^^^ (state b >>> shift)) &&& mask
  Vector.ofFn fun i => if i == a then state a ^^^ t else if i == b then state b ^^^ (t <<< shift) else state i

def bitsliceSwaps (state : State) : State := Id.run do
  let mut state := state
  for (a,b,shift,mask) in [(1,0,1,0x55555555),(3,2,1,0x55555555),(5,4,1,0x55555555),(7,6,1,0x55555555),
      (2,0,2,0x33333333),(3,1,2,0x33333333),(6,4,2,0x33333333),(7,5,2,0x33333333),
      (4,0,4,0x0f0f0f0f),(5,1,4,0x0f0f0f0f),(6,2,4,0x0f0f0f0f),(7,3,4,0x0f0f0f0f)] do
    state := swap state a b shift mask
  return state

def bitslice (block : U128) : State :=
  let a := UInt32.ofNat block.toNat
  let b := UInt32.ofNat (block.toNat >>> 32)
  let c := UInt32.ofNat (block.toNat >>> 64)
  let d := UInt32.ofNat (block.toNat >>> 96)
  bitsliceSwaps (pack a a b b c c d d)

def invBitslice (state : State) : U128 :=
  let state := bitsliceSwaps state
  BitVec.ofNat 128 ((state 0).toNat ||| ((state 2).toNat <<< 32) ||| ((state 4).toNat <<< 64) ||| ((state 6).toNat <<< 96))

private def deltaSwap (value shift mask : UInt32) : UInt32 :=
  let t := (value ^^^ (value >>> shift)) &&& mask
  value ^^^ t ^^^ (t <<< shift)

def shiftRows (inverse : Bool) (state : State) : State := Vector.ofFn fun i =>
  let value := deltaSwap (state i) 4 (if inverse then 0x030f0c00 else 0x0c0f0300)
  deltaSwap value 2 0x33003300

def mixColumnsState (state : State) : State :=
  let a0 := (state 0)
  let a1 := (state 1)
  let a2 := (state 2)
  let a3 := (state 3)
  let a4 := (state 4)
  let a5 := (state 5)
  let a6 := (state 6)
  let a7 := (state 7)
  let b0 := (rotr a0 8)
  let b1 := (rotr a1 8)
  let b2 := (rotr a2 8)
  let b3 := (rotr a3 8)
  let b4 := (rotr a4 8)
  let b5 := (rotr a5 8)
  let b6 := (rotr a6 8)
  let b7 := (rotr a7 8)
  let c0 := a0 ^^^ b0
  let c1 := a1 ^^^ b1
  let c2 := a2 ^^^ b2
  let c3 := a3 ^^^ b3
  let c4 := a4 ^^^ b4
  let c5 := a5 ^^^ b5
  let c6 := a6 ^^^ b6
  let c7 := a7 ^^^ b7
  pack (b0      ^^^ c7 ^^^ (rotr c0 16)) (b1 ^^^ c0 ^^^ c7 ^^^ (rotr c1 16)) (b2 ^^^ c1      ^^^ (rotr c2 16)) (b3 ^^^ c2 ^^^ c7 ^^^ (rotr c3 16)) (b4 ^^^ c3 ^^^ c7 ^^^ (rotr c4 16)) (b5 ^^^ c4      ^^^ (rotr c5 16)) (b6 ^^^ c5      ^^^ (rotr c6 16)) (b7 ^^^ c6      ^^^ (rotr c7 16))

def invMixColumnsState (state : State) : State :=
  let a0 := (state 0)
  let a1 := (state 1)
  let a2 := (state 2)
  let a3 := (state 3)
  let a4 := (state 4)
  let a5 := (state 5)
  let a6 := (state 6)
  let a7 := (state 7)
  let b0 := (rotr a0 8)
  let b1 := (rotr a1 8)
  let b2 := (rotr a2 8)
  let b3 := (rotr a3 8)
  let b4 := (rotr a4 8)
  let b5 := (rotr a5 8)
  let b6 := (rotr a6 8)
  let b7 := (rotr a7 8)
  let c0 := a0 ^^^ b0
  let c1 := a1 ^^^ b1
  let c2 := a2 ^^^ b2
  let c3 := a3 ^^^ b3
  let c4 := a4 ^^^ b4
  let c5 := a5 ^^^ b5
  let c6 := a6 ^^^ b6
  let c7 := a7 ^^^ b7
  let d0 := a0      ^^^ c7
  let d1 := a1 ^^^ c0 ^^^ c7
  let d2 := a2 ^^^ c1
  let d3 := a3 ^^^ c2 ^^^ c7
  let d4 := a4 ^^^ c3 ^^^ c7
  let d5 := a5 ^^^ c4
  let d6 := a6 ^^^ c5
  let d7 := a7 ^^^ c6
  let e0 := c0      ^^^ d6
  let e1 := c1      ^^^ d6 ^^^ d7
  let e2 := c2 ^^^ d0      ^^^ d7
  let e3 := c3 ^^^ d1 ^^^ d6
  let e4 := c4 ^^^ d2 ^^^ d6 ^^^ d7
  let e5 := c5 ^^^ d3      ^^^ d7
  let e6 := c6 ^^^ d4
  let e7 := c7 ^^^ d5
  pack (d0 ^^^ e0 ^^^ (rotr e0 16)) (d1 ^^^ e1 ^^^ (rotr e1 16)) (d2 ^^^ e2 ^^^ (rotr e2 16)) (d3 ^^^ e3 ^^^ (rotr e3 16)) (d4 ^^^ e4 ^^^ (rotr e4 16)) (d5 ^^^ e5 ^^^ (rotr e5 16)) (d6 ^^^ e6 ^^^ (rotr e6 16)) (d7 ^^^ e7 ^^^ (rotr e7 16))

def mixColumns (inverse : Bool) (block : U128) : U128 :=
  invBitslice ((if inverse then invMixColumnsState else mixColumnsState) (bitslice block))

def round (inverse : Bool) (block key : U128) : U128 :=
  let state := bitslice block
  let state := if inverse then invSubBytes (subBytesNots state) else subBytesNots (subBytes state)
  let state := shiftRows inverse state
  let state := (if inverse then invMixColumnsState else mixColumnsState) state
  invBitslice state ^^^ key

end Miri.Interpreter.IntrinsicX86.Aes
