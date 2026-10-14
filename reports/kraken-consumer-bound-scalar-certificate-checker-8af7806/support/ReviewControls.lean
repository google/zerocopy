module
import Consumer
open BoundConsumer CheckedByteLeaf
def fileImage : List UInt8 := [0,0,64,57,192,3,95,214]
def fileRaw : List UInt8 := [75,82,67,1,1,1,1,0,0,0,0,0,16,0,0,0,0,0,0]
theorem actual_file_literals_accepted : check fixedRequest fileImage fileRaw = some (executable 4096 0) := by rfl
theorem actual_file_literals_meaning : Meaning fixedRequest (executable 4096 0) := consumer_sound fixedRequest fileImage fileRaw _ actual_file_literals_accepted
def changedConsumer : Request := {fixedRequest with image := ownedImage ++ [0]}
theorem changing_consumer_authority_changes_subject : check changedConsumer (ownedImage ++ [0]) goodRaw = some (executable 4096 0) := by rfl
theorem changed_consumer_still_cannot_weaken_claim : check {changedConsumer with claim := .resultOnly} (ownedImage ++ [0]) goodRaw = none := by rfl
#print axioms actual_file_literals_accepted
#print axioms actual_file_literals_meaning
#print axioms changing_consumer_authority_changes_subject
#print axioms changed_consumer_still_cannot_weaken_claim
