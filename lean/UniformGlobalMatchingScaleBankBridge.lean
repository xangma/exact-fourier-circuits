import UniformGlobalMatchingPoolPreparation
import UniformMatchingAxisTableMachine
import UniformTensorDiagonalBankMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalMatchingScaleBankBridge
open UniformMachine UniformColoring
open UniformPairMachine (prepared)
open UniformGlobalMatchingScaleMachine (factor address)
noncomputable section
/-- Semantic formula only; the physical bank is produced by MatchingPool139. -/
def nativeFactor {M : ℕ} (E:Fin M→Edge) (mu:Fin M→ℂ) (lane:Fin 9) (d:ℕ) : ℂ :=
 if h:∃i,Incident (E i) d then
  factor (mu (Classical.choose h)) lane (if d=(E (Classical.choose h)).left then 0 else 1)
 else 1
lemma incident_unique {M : ℕ} (E:Fin M→Edge)
 (hm:UniformMatchingAxisTableMachine.Matching E) (i j:Fin M) (d:ℕ)
 (hi:Incident (E i) d) (hj:Incident (E j) d) : i=j := by
 by_contra ne
 have no:=hm i j ne
 apply no
 rcases hi with hi|hi
 · exact Or.inl (by simpa only [hi] using hj)
 · exact Or.inr (by simpa only [hi] using hj)
lemma nativeFactor_left {M : ℕ} (E:Fin M→Edge) (mu:Fin M→ℂ)
 (hm:UniformMatchingAxisTableMachine.Matching E) (lane:Fin 9) (i:Fin M) :
 nativeFactor E mu lane (E i).left=factor (mu i) lane 0 := by
 have ex:∃j,Incident (E j) (E i).left:=⟨i,Or.inl rfl⟩
 unfold nativeFactor
 rw [dite_eq_left ex]
 have eq:=incident_unique E hm _ i _ (Classical.choose_spec ex) (Or.inl rfl)
 simp only [eq,ite_true]
lemma nativeFactor_right {M : ℕ} (E:Fin M→Edge) (mu:Fin M→ℂ)
 (hm:UniformMatchingAxisTableMachine.Matching E) (lane:Fin 9) (i:Fin M) :
 nativeFactor E mu lane (E i).right=factor (mu i) lane 1 := by
 have ex:∃j,Incident (E j) (E i).right:=⟨i,Or.inr rfl⟩
 unfold nativeFactor
 rw [dite_eq_left ex]
 have eq:=incident_unique E hm _ i _ (Classical.choose_spec ex) (Or.inr rfl)
 simp only [eq,ite_eq_right (Ne.symm (E i).different)]
lemma nativeFactor_unused {M : ℕ} (E:Fin M→Edge) (mu:Fin M→ℂ)
 (lane:Fin 9) (d:ℕ) (hn:∀i,¬Incident (E i) d) : nativeFactor E mu lane d=1 := by
 unfold nativeFactor
 rw [dite_eq_right (by rintro ⟨i,hi⟩;exact hn i hi)]
def rowEdges (rows:List UniformInPlaceMachine.Row)
 (different:UniformGlobalMatchingPoolPreparation.Different rows) : Fin rows.length→Edge :=
 fun i=>⟨(rows[i.val]'i.isLt).dst,(rows[i.val]'i.isLt).src,different i⟩
lemma rowEdges_matching (rows:List UniformInPlaceMachine.Row)
 (different:UniformGlobalMatchingPoolPreparation.Different rows)
 (matching:UniformGlobalMatchingPoolPreparation.Matching rows) :
 UniformMatchingAxisTableMachine.Matching (rowEdges rows different) := by
 intro i j ne
 have h:=matching i j ne
 simp only [Conflict,Incident,rowEdges]
 rintro ((hij|hij)|(hij|hij))
 · exact h.1 hij.symm
 · exact h.2.1 hij.symm
 · exact h.2.2.1 hij.symm
 · exact h.2.2.2 hij.symm
lemma rowEdges_range (r:ℕ) (rows:List UniformInPlaceMachine.Row)
 (different:UniformGlobalMatchingPoolPreparation.Different rows)
 (bounds:UniformGlobalMatchingPoolPreparation.Bounds r rows) :
 UniformMatchingAxisTableMachine.InRange r (rowEdges rows different) := bounds
/-- Every coefficient, including singleton1, follows from the actual139 postcondition. -/
lemma pool_coefficients {R K pool r : ℕ} {rows:List UniformInPlaceMachine.Row}
 {bank:Fin R→ℂ} {co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R}
 {s:State} (different:UniformGlobalMatchingPoolPreparation.Different rows)
 (matching:UniformGlobalMatchingPoolPreparation.Matching rows)
 (done:UniformGlobalMatchingPoolPreparation.PoolInvariant (K:=K) pool r rows bank co rows.length s)
 (lane:Fin 9) : UniformTensorDiagonalBankMachine.Coefficients r (pool+lane.val*r)
 (fun d=>nativeFactor (rowEdges rows different)
  (fun i=>UniformMatchingConjugateLoadMachine.value K bank (co i)) lane d.val) s := by
 intro d
 let E:=rowEdges rows different
 let mu:=fun i=>UniformMatchingConjugateLoadMachine.value K bank (co i)
 have hm:=rowEdges_matching rows different matching
 by_cases h:∃i,Incident (E i) d.val
 · obtain ⟨i,hi|hi⟩:=h
   · have table:=done.done i i.isLt lane 0
     have nf:=nativeFactor_left E mu hm lane i
     have eq:d.val=(rows[i.val]'i.isLt).dst:=hi.symm
     change s.scalarHeap (pool+lane.val*r+d.val)=some (prepared (nativeFactor E mu lane d.val))
     rw [eq,show (rows[i.val]'i.isLt).dst=(E i).left from rfl,nf]
     simpa [address,E,rowEdges,mu] using table
   · have table:=done.done i i.isLt lane 1
     have nf:=nativeFactor_right E mu hm lane i
     have eq:d.val=(rows[i.val]'i.isLt).src:=hi.symm
     change s.scalarHeap (pool+lane.val*r+d.val)=some (prepared (nativeFactor E mu lane d.val))
     rw [eq,show (rows[i.val]'i.isLt).src=(E i).right from rfl,nf]
     simpa [address,E,rowEdges,mu] using table
 · have hn:∀i,¬Incident (E i) d.val:=by intro i hi;exact h ⟨i,hi⟩
   have none:=nativeFactor_unused E mu lane d.val hn
   have un:=done.untouched d.val d.isLt (by
    intro i
    constructor
    · intro eq;exact hn i (Or.inl eq.symm)
    · intro eq;exact hn i (Or.inr eq.symm)) lane
   change s.scalarHeap (pool+lane.val*r+d.val)=some (prepared (nativeFactor E mu lane d.val))
   rw [none];exact un

/-- Actual endpoint reads identify generated rows with the79 producer's edge
family. Matching/range are inherited from that producer, not supplied row geometry. -/
lemma rows_geometry {r D : ℕ} {rows:List UniformInPlaceMachine.Row}
 {E:Fin rows.length→Edge} {s:State}
 (edgeRows:UniformMatchingAxisTableMachine.Edges E D s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (hm:UniformMatchingAxisTableMachine.Matching E)
 (hr:UniformMatchingAxisTableMachine.InRange r E) :
 UniformGlobalMatchingPoolPreparation.Bounds r rows ∧
 UniformGlobalMatchingPoolPreparation.Different rows ∧
 UniformGlobalMatchingPoolPreparation.Matching rows := by
 have endpoints:∀i:Fin rows.length,(rows[i.val]'i.isLt).dst=(E i).left ∧
  (rows[i.val]'i.isLt).src=(E i).right:=by
  intro i
  have fields:=table i.val i.isLt
  exact ⟨Option.some.inj (fields.1.symm.trans (edgeRows i).1),
   Option.some.inj (fields.2.1.symm.trans (edgeRows i).2)⟩
 refine ⟨?_,?_,?_⟩
 · intro i;rw [(endpoints i).1,(endpoints i).2];exact hr i
 · intro i;rw [(endpoints i).1,(endpoints i).2];exact (E i).different
 · intro i j ne
   rw [(endpoints i).1,(endpoints i).2,(endpoints j).1,(endpoints j).2]
   have no:=hm i j ne
   exact ⟨fun eq=>no (Or.inl (Or.inl eq.symm)),
    fun eq=>no (Or.inl (Or.inr eq.symm)),
    fun eq=>no (Or.inr (Or.inl eq.symm)),
    fun eq=>no (Or.inr (Or.inr eq.symm))⟩

end
end ExactFourierCircuits.UniformGlobalMatchingScaleBankBridge
