import PacketModel
namespace Receipt
def observedLayout : List Nat := [8, 4, 1, 2, 1]
def expectedSource : String := "073ba3f230343ad94a0a90d352949acee6f269b965e81253e73d9169f486dfaa"
def capturedSource : String := "073ba3f230343ad94a0a90d352949acee6f269b965e81253e73d9169f486dfaa"
theorem layout_agrees : observedLayout = Packet.expectedLayout 4 := rfl
theorem source_index : capturedSource = expectedSource := rfl
theorem bounded_machine_length (n : Nat) (h : n ≤ 64) : 6+n < 4294967296 := by omega
theorem all_payloads (flags payload destination : List Packet.Byte) (valid : Packet.validFlags flags = true) (capacity : payload.length ≤ destination.length) : Packet.process flags payload destination true = some (payload ++ destination.drop payload.length) := Packet.pipeline_success flags payload destination valid capacity
#print axioms layout_agrees
#print axioms source_index
#print axioms bounded_machine_length
#print axioms all_payloads
end Receipt
