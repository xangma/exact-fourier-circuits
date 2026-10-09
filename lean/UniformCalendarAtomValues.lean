import UniformCalendarPreparationRecordPrefixes

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarAtomValues
noncomputable section
open UniformCalendarActualAtoms UniformCalendarIntervalPartition UniformTransposeDescriptorMachine
open UniformDirectLeafCacheChronology UniformDirectToeplitz

lemma get_replicate {L:List ℕ}(n d:ℕ)(eq:L=List.replicate n d)(i:Fin L.length):L.get i=d:=by
 subst L
 exact List.getElem_replicate i.isLt

lemma direct_values (n v o K:ℕ):
 durations n (.direct v o)=(topology v).map (fun op=>duration (ofOperation o K op)):=by
 simp only[durations,leafRecords,List.map_map]
 apply congrArg (List.map · (topology v))
 funext op
 cases op <;>rfl

lemma direct_get (n v o K:ℕ)(j:Fin (durations n (.direct v o)).length):
 (durations n (.direct v o)).get j=
 duration (ofOperation o K ((topology v).get ⟨j.val,by
  simpa only[durations,leafRecords,List.length_map] using j.isLt⟩)):=by
 have values:=direct_values n v o K
 have get_congr {α:Type}{L M:List α}(eq:L=M)(i:Fin L.length):
  L.get i=M.get (finCongr (congrArg List.length eq) i):=by cases eq;rfl
 exact (get_congr values j).trans (List.getElem_map _)

lemma elapsed_lt (start before duration t:ℕ)(lo:start+before≤t)(hi:t<start+before+duration):
 t-(start+before)<duration:=by omega

lemma clock (start before t:ℕ)(lo:start+before≤t):
 before+(t-(start+before))=t-start:=by omega

end
end ExactFourierCircuits.UniformCalendarAtomValues
