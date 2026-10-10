import DFTModelClockBatch

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualBatch
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelClockBatch
open scoped BigOperators
noncomputable section

/-- One actual call per complete child group, with a single final flatten. -/
def program (s t:Ty) : Code false (Port s t) (Input s t) (a t) :=
  .comp (.fork (.importClosed (geometry s t)) (calls s t))
    (.comp (.importClosed (arrange t)) (.importClosed (flatten t)))

attribute [local irreducible] calls flatten geometry arrange childArgument

theorem lookup (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T:ℕ)
  (bank:Tape t.T) (j:Fin (G*T)) :
  (Code.run (program s t) h (p,(G,(T,bank)))).val.look j.val t.blank=
    (h (p,sliced T (j.val/T) bank t.blank)).val.look (j.val%T) t.blank := by
  simp only [program,Code.run,geometry,arrange,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (run (flatten t) (G,(T,(Code.run (calls s t) h (p,(G,(T,bank)))).val))).val.look j.val t.blank=_
  rw [flatten_value,calls_value]
  have group:j.val/T<G:=Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using j.isLt)
  rw [Tape.look_of_lt _ _ j.isLt]
  change ((Tape.tab G (fun g=>(h (p,sliced T g bank t.blank)).val)).look
    (j.val/T) (Tape.empty t.T)).look (j.val%T) t.blank=_
  have looked:(Tape.tab G (fun g=>(h (p,sliced T g bank t.blank)).val)).look
    (j.val/T) (Tape.empty t.T)=(h (p,sliced T (j.val/T) bank t.blank)).val :=
      Tape.look_of_lt _ _ group
  rw [looked]


theorem length (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T:ℕ) (bank:Tape t.T) :
  (Code.run (program s t) h (p,(G,(T,bank)))).val.len=G*T := by
  simp only [program,Code.run,geometry,arrange,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (run (flatten t) (G,(T,(Code.run (calls s t) h (p,(G,(T,bank)))).val))).val.len=_
  rw [flatten_value];rfl

theorem work (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T:ℕ) (bank:Tape t.T) :
  (Code.run (program s t) h (p,(G,(T,bank)))).work=
    38+68*(G*T)+21*G+∑g∈Finset.range G,(h (p,sliced T g bank t.blank)).work := by
  simp only [program,Code.run,geometry,arrange,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (7+1+(Code.run (calls s t) h (p,(G,(T,bank)))).work+1)+
    (9+1+((run (flatten t) (G,(T,(Code.run (calls s t) h (p,(G,(T,bank)))).val))).work+1)+1)+1=_
  rw [flatten_work,calls_work];ring

theorem valid (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T:ℕ) (bank:Tape t.T)
  (children:∀g<G,(h (p,sliced T g bank t.blank)).valid) :
  (Code.run (program s t) h (p,(G,(T,bank)))).valid := by
  have good:=(calls_valid s t h p G T bank).2 children
  have final:=flatten_valid t G T (Code.run (calls s t) h (p,(G,(T,bank)))).val
  simpa only [program,geometry,arrange,Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    true_and,and_true] using And.intro good final

theorem calls_peak (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T B:ℕ)
  (bank:Tape t.T) (count:G≤B) (size:T≤B) (extent:G*T≤B)
  (children:∀g<G,(h (p,sliced T g bank t.blank)).peak≤B) :
  (Code.run (calls s t) h (p,(G,(T,bank)))).peak≤B := by
  unfold calls
  rw [tab_peak]
  change max (max 0 (Bill.tab G (a t).blank (fun g=>Code.run
    (.comp (.importClosed (childArgument s t)) .call) h ((p,(G,(T,bank))),g))).peak) 0≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero]
  refine max_le count (Finset.sup_le ?_)
  intro g hg
  have live:=Finset.mem_range.mp hg
  have ending:g*T+T≤B:=by
    calc
      _=(g+1)*T:=by ring
      _≤G*T:=Nat.mul_le_mul_right T (by omega)
      _≤B:=extent
  have arg:=childArgument_peak s t p G T g B bank size ending
  change max (max (max (run (childArgument s t) ((p,(G,(T,bank))),g)).peak 0)
    (max (h (run (childArgument s t) ((p,(G,(T,bank))),g)).val).peak 0)) 0≤B
  rw [childArgument_run]
  exact max_le (max_le (max_le arg (Nat.zero_le _))
    (max_le (children g live) (Nat.zero_le _))) (Nat.zero_le _)

theorem peak (s t:Ty) (h:Handler (Port s t)) (p:s.T) (G T B:ℕ)
  (bank:Tape t.T) (count:G≤B) (size:T≤B) (extent:G*T≤B)
  (children:∀g<G,(h (p,sliced T g bank t.blank)).peak≤B) :
  (Code.run (program s t) h (p,(G,(T,bank)))).peak≤B := by
  have hc:=calls_peak s t h p G T B bank count size extent children
  have hf:=flatten_peak t G T B (Code.run (calls s t) h (p,(G,(T,bank)))).val extent
  simpa only [program,geometry,arrange,Code.run,run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero,max_le_iff] using And.intro hc hf

end
end ExactFourierCircuits.DFTModelSavingResidualBatch
