import UniformCacheRangeSelectorMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace S
abbrev Source:=UniformGlobalCalendarSelector.Source
abbrev selected:=UniformGlobalCalendarSelector.selected
abbrev writeSelections:=UniformGlobalCalendarSelector.writeSelections
end S
structure Range where
 base:ℕ
 count:ℕ
 records:ℕ → ℕ × ℕ
def stride (r:ℕ):ℕ:=3*r+11
def endAddress (r:ℕ)(q:Range):ℕ:=q.base+stride r*q.count+7
def total:List Range → ℕ
 | []=>0
 | q::qs=>q.count+total qs
def selectedRanges (r tick:ℕ):List Range → List (ℕ × ℕ)
 | []=>[]
 | q::qs=>S.selected q.base (stride r) tick q.records 0 q.count++selectedRanges r tick qs
lemma selectedRanges_length (r tick:ℕ)(qs:List Range):(selectedRanges r tick qs).length ≤ total qs:=by
 induction qs with
 | nil=>simp[selectedRanges,total]
 | cons q qs ih=>
  simp only[selectedRanges,List.length_append,total]
  exact Nat.add_le_add (UniformGlobalCalendarSelector.selected_length _ _ _ _ _ _) ih

def NodeSource (r tasks i:ℕ)(qs:List Range)(heap:ℕ → Option ℕ):Prop:=
 ∀j,(hj:j<qs.length)→heap (tasks+2*(i+j))=some (qs[j]'hj).base ∧
  heap (tasks+2*(i+j)+1)=some (qs[j]'hj).count ∧ S.Source (qs[j]'hj).base (stride r) (qs[j]'hj).count (qs[j]'hj).records heap
structure RangeSource (r tasks control rectangleCount:ℕ)(rectangle:ℕ → ℕ × ℕ)(qs:List Range)(heap:ℕ → Option ℕ):Prop where
 rectangleCountCell:heap (tasks+4*r+4)=some rectangleCount
 nodeCount:heap (tasks+4*r+5)=some qs.length
 rectangle:S.Source (control+3*r+4) (stride r) rectangleCount rectangle heap
 nodes:NodeSource r tasks 0 qs heap
structure Layout (r tasks control rectangleCount O B:ℕ)(qs:List Range):Prop where
 header:tasks+4*r+6 ≤ O
 nodeRows:tasks+2*qs.length+2 ≤ O
 rectangle:control+3*r+4+stride r*rectangleCount+7 ≤ O
 nodes:∀q∈qs,endAddress r q ≤ O
 output:O+2*(rectangleCount+total qs) ≤ B
structure Args (r tasks control tick O:ℕ)(s:State):Prop where
 radix:s.natReg 6800=r
 tasks:s.natReg 6810=tasks
 control:s.natReg 6813=control
 tick:s.natReg 6703=tick
 output:s.natReg 7050=O
structure Control (r tasks N tick O used i:ℕ)(s:State):Prop where
 zero:s.natReg 7100=0
 one:s.natReg 7101=1
 two:s.natReg 7102=2
 spacing:s.natReg 7110=stride r
 nodeCount:s.natReg 7107=N
 index:s.natReg 7106=i
 pointer:s.natReg 7108=tasks+2*i
 tick:s.natReg 6703=tick
 output:s.natReg 6704=O
 used:s.natReg 6705=used
lemma Control.withPC {r tasks N tick O used i s}(h:Control r tasks N tick O used i s)(pc:ℕ):
 Control r tasks N tick O used i (setPC s pc):=
 ⟨h.zero,h.one,h.two,h.spacing,h.nodeCount,h.index,h.pointer,h.tick,h.output,h.used⟩

lemma writeSelections_low (O used:ℕ)(qs:List (ℕ × ℕ))(heap:ℕ → Option ℕ)(a:ℕ)(ha:a<O):
 S.writeSelections O used qs heap a=heap a:=by
 simp only [S.writeSelections]
 induction qs generalizing used heap with
 | nil=>rfl
 | cons q qs ih=>
  rw[UniformGlobalCalendarSelector.writeSelections,ih]
  exact UniformGlobalCalendarSelector.storeSelection_low _ _ _ _ _ _ ha
lemma writeSelections_append (O used:ℕ)(xs ys:List (ℕ × ℕ))(heap:ℕ → Option ℕ):
 S.writeSelections O used (xs++ys) heap=
 S.writeSelections O (used+xs.length) ys (S.writeSelections O used xs heap):=by
 simp only [S.writeSelections]
 induction xs generalizing used heap with
 | nil=>simp[UniformGlobalCalendarSelector.writeSelections]
 | cons q qs ih=>
  simp only[List.cons_append,UniformGlobalCalendarSelector.writeSelections,List.length_cons]
  rw[ih];congr 1;omega
lemma NodeSource.low {r tasks i qs heap after O}(h:NodeSource r tasks i qs heap)
 (banks:tasks+2*(i+qs.length)+2 ≤ O)(fit:∀q∈qs,endAddress r q ≤ O)
 (same:∀a,a<O → after a=heap a):NodeSource r tasks i qs after:=by
 intro j hj
 obtain ⟨a,b,c⟩:=h j hj
 have member:qs[j]'hj∈qs:=List.getElem_mem hj
 have e:=fit _ member
 refine ⟨(same _ (by omega)).trans a,(same _ (by omega)).trans b,?_⟩
 intro k hk
 have mul:=Nat.mul_le_mul_left (stride r) (Nat.le_of_lt hk)
 obtain ⟨x,y⟩:=c k hk
 exact ⟨(same _ (by unfold endAddress at e;omega)).trans x,(same _ (by unfold endAddress at e;omega)).trans y⟩
lemma NodeSource.tail {r tasks i q qs heap}(h:NodeSource r tasks i (q::qs) heap):
 NodeSource r tasks (i+1) qs heap:=by
 intro j hj
 have e:=h (j+1) (by simp;omega)
 simpa only[List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using e
end ExactFourierCircuits.UniformCacheRangeSelector

