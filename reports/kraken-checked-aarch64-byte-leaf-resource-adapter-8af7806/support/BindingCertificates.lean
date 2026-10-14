module
public import Adapter
@[expose] public section
open CheckedByteLeaf
-- Artifact SHA256 00a36a89f187860e786618082bdfebd8c61c3f13f221f14c6ed6cc8997abe583; external importer file offset 632.
def bytes_O0_object : List UInt8 := [0,0,64,57,192,3,95,214]
theorem bound_O0_object : certificate 0 bytes_O0_object = some (executable 0 0) := by rfl
theorem mutation_O0_object : certificate 0 [1,0,64,57,192,3,95,214] = none := by decide
#print axioms bound_O0_object
#print axioms mutation_O0_object
-- Artifact SHA256 22597cc71edde5270deb25a79593df09709bb79a8bd9e9483b9087ea41acd1b6; external importer file offset 2240.
def bytes_O0_linked : List UInt8 := [0,0,64,57,192,3,95,214]
theorem bound_O0_linked : certificate 4294969536 bytes_O0_linked = some (executable 4294969536 0) := by rfl
theorem mutation_O0_linked : certificate 4294969536 [1,0,64,57,192,3,95,214] = none := by decide
#print axioms bound_O0_linked
#print axioms mutation_O0_linked
-- Artifact SHA256 9ef7a9c48efe01d74914fb1470fb2ad33bdae770b1351ef7b169b1d8961ae7f6; external importer file offset 568.
def bytes_O3_object : List UInt8 := [0,0,64,57,192,3,95,214]
theorem bound_O3_object : certificate 0 bytes_O3_object = some (executable 0 0) := by rfl
theorem mutation_O3_object : certificate 0 [1,0,64,57,192,3,95,214] = none := by decide
#print axioms bound_O3_object
#print axioms mutation_O3_object
-- Artifact SHA256 54e7f113dc80248213ffcd2aff2b361c62a0d2118d9cbe0227cf3e6b11d112b4; external importer file offset 2240.
def bytes_O3_linked : List UInt8 := [0,0,64,57,192,3,95,214]
theorem bound_O3_linked : certificate 4294969536 bytes_O3_linked = some (executable 4294969536 0) := by rfl
theorem mutation_O3_linked : certificate 4294969536 [1,0,64,57,192,3,95,214] = none := by decide
#print axioms bound_O3_linked
#print axioms mutation_O3_linked
