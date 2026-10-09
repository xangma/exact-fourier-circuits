import UniformCalendarAtomCollapse
import UniformActualCalendarMacroOrder
import UniformDirectLeafCacheChronology

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarActualAtoms
noncomputable section
open UniformLocalCacheTiming UniformLocalRequestPlan UniformCalendarIntervalPartition
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology

/-- Exactly the charged rectangle slots and the native direct operation word. -/
def durations (n:ℕ):UniformLocalCacheTiming.Event→List ℕ
 | .rectangle q=>List.replicate (slotCount n q) 28
 | .direct v o=>(leafRecords v o 0).map duration

theorem durations_sum (n:ℕ)(e:UniformLocalCacheTiming.Event):
 (durations n e).sum=e.duration:=by
 cases e with
 | rectangle q=>
  simp only[durations,List.sum_replicate,Nat.nsmul_eq_mul,Event.duration]
  change (352*UniformWorkspacePlanner.exponent q.a q.e+330)*28=
   28*(4*(8*UniformWorkspacePlanner.exponent q.a q.e+7)+2)*11
  ring
 | direct v o=>exact leaf_elapsed v o 0

lemma durations_values (n:ℕ)(e:UniformLocalCacheTiming.Event)(j:Fin (durations n e).length):
 (durations n e).get j=1 ∨(durations n e).get j=28:=by
 cases e with
 | rectangle q=>right;exact List.getElem_replicate j.isLt
 | direct v o=>
  have bound:j.val<(leafRecords v o 0).length:=by
   simpa only[durations,List.length_map] using j.isLt
  have value:(durations n (.direct v o)).get j=duration ((leafRecords v o 0)[j.val]'bound):=
   List.getElem_map duration
  rw[value]
  by_cases scale:((leafRecords v o 0)[j.val]'bound).kind=0
  · left;exact ite_eq_left scale
  · right;exact ite_eq_right scale

def kind (d:ℕ):ℕ:=if d=1 then 1 else 0
lemma kind_duration (d:ℕ)(value:d=1∨d=28):UniformGlobalCalendarSelector.duration (kind d)=d:=by
 rcases value with rfl|rfl <;>decide

def records (n:ℕ)(e:TimedEvent):List (ℕ×ℕ):=
 List.ofFn (fun j:Fin (durations n e.event).length=>
  (e.start+prefixDuration (durations n e.event) j.val,kind ((durations n e.event).get j)))
lemma records_length (n:ℕ)(e:TimedEvent):(records n e).length=(durations n e.event).length:=List.length_ofFn
lemma records_get (n:ℕ)(e:TimedEvent)(j:Fin (records n e).length):
 (records n e).get j=(e.start+prefixDuration (durations n e.event) j.val,
  kind ((durations n e.event).get ⟨j.val,by simpa only[records_length] using j.isLt⟩)):=by
 exact List.getElem_ofFn j.isLt

/-- The literal selector kind recovers the exact native operation duration. -/
lemma records_duration (n:ℕ)(e:TimedEvent)(j:Fin (records n e).length):
 UniformGlobalCalendarSelector.duration ((records n e).get j).2=
 (durations n e.event).get ⟨j.val,by simpa only[records_length] using j.isLt⟩:=by
 rw[records_get]
 exact kind_duration _ (durations_values n e.event _)

lemma rectangle_prefix (n:ℕ)(q:UniformLocalRectangleDescriptors.Row)(j:ℕ)
 (bound:j ≤ slotCount n q):prefixDuration (durations n (.rectangle q)) j=28*j:=by
 simp only[prefixDuration,durations,List.take_replicate,List.sum_replicate,Nat.nsmul_eq_mul,
  Nat.min_eq_left bound,Nat.mul_comm]

lemma direct_prefix (n v o j:ℕ):
 prefixDuration (durations n (.direct v o)) j=elapsed ((leafRecords v o 0).take j):=by
 simp only[prefixDuration,durations,←List.map_take,elapsed]

end
end ExactFourierCircuits.UniformCalendarActualAtoms
