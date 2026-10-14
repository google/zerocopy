module
import Kraken.AArch64.Semantics
import Kraken.AArch64.Parser
import Kraken.SeparationMem
meta import Kraken.AArch64.Semantics
meta import Kraken.AArch64.Parser
open Kraken.AArch64 Kraken.AArch64.Parser
#check UInt8.toNat_ofNat
#check UInt8.toNat_lt
#check UInt8.toBitVec
#check UInt8.At
#check UInt8.toBytes
#check UInt8.toBytes_length
#check Mem.loadInt_sep
#check BitVec.ofInt_ofBytes_toBytes
#check UInt64.ofBitVec
#eval parseAArch64("ldrb w0, [x0]\nret")
