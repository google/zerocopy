"""Finite mathematical reconstructions; no invalid Rust and no upstream interpreter."""
import json, platform
def bound(i,bits,signed=False):
    u=i%(1<<bits)
    return u-(1<<bits) if signed and u >= 1<<(bits-1) else u
def signed_valid(value,bits):
    return -(1<<(bits-1)) <= value < (1<<(bits-1))
def shift_valid(count,bits):
    return 0 <= count < bits
def ptr_valid(bits,addr,elem,count,align,allocation_len,trait_ok=True,safe=True,inhabited=True):
    if not 0 <= addr < 1<<bits: return False
    if not 0 <= count < 1<<bits or not trait_ok: return False
    if not safe: return True
    size=elem*count
    return size < 1<<(bits-1) and addr != 0 and addr%align == 0 and inhabited and (size == 0 or allocation_len is not None and size <= allocation_len)
families=[]
for bits in (32,64):
 for endian in ("little","big"):
    max_signed=(1<<(bits-1))-1
    if not (signed_valid(max_signed,bits) and signed_valid(-(1<<(bits-1)),bits) and not signed_valid(max_signed+1,bits) and shift_valid(bits-1,bits) and not shift_valid(bits,bits)):
        raise SystemExit("boundary predicate control failed")
    families.append({"pointer_bits":bits,"endianness":endian,
      "encode_0x01020304":list((0x01020304).to_bytes(4,endian)),
      "max_plus_one_signed_wrapping":bound(max_signed+1,bits,True),
      "max_plus_one_unchecked_valid":signed_valid(max_signed+1,bits),
      "regular_shl_by_width":bound(1 << (bits%bits),bits),
      "unchecked_shl_by_width_valid":shift_valid(bits,bits),
      "ptr_wrapping_from_max_plus_two":bound((1<<bits)-1+2,bits),
      "oversized_safe_slice":ptr_valid(bits,8,1,1<<(bits-1),8,1<<bits),
      "same_raw_slice":ptr_valid(bits,8,1,1<<(bits-1),8,None,safe=False),
      "max_usize_zst_slice":ptr_valid(bits,8,0,(1<<bits)-1,8,None),
      "metadata_valid_data_invalid":ptr_valid(bits,8,4,2,4,None),
      "wrong_trait_vtable":ptr_valid(bits,8,4,1,4,4,trait_ok=False),
      "zero_size_misaligned_safe":ptr_valid(bits,3,0,0,4,None),
      "zero_size_null_safe":ptr_valid(bits,0,0,0,4,None)})
# A tiny address-space enumeration uses the BasicMemory predicate exactly.
def candidates(live):
 return [a for a in range(1,256) if a%4==0 and a+8<256 and all(not (a+8>b and b+n>a) for b,n in live)]
before=candidates([(4,8)])
after=candidates([])
# Packed unsized tail formula, head end=1, head align=1, tail size=8 align=4.
def layout(cap):
 a=min(4,cap) if cap else 4
 off=((1+a-1)//a)*a
 return {"tail_offset":off,"align":a,"size":((off+8+a-1)//a)*a}
print(json.dumps({"python":platform.python_version(),"families":families,
 "packed_tail":{"ordinary":layout(None),"packed_1":layout(1)},
 "allocator":{"8bit_size8_align4_live_at4":before,"after_deallocation":after,
 "reuse_address4_before":4 in before,"reuse_address4_after":4 in after,
 "scope":"candidate-address predicate only; no pick, exhaustion, allocator failure or provenance generation"}},
 indent=2))

