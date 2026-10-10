import DFTModelCacheSelectedCoefficientsRows

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] program constants cell decode

/-- Physical row addresses, in their actual published order. No factor, action
or predecoded scalar tape occurs in this contract. -/
theorem tab_lookup {α : Type} (n : ℕ) (f : ℕ→α) (i : ℕ) (z : α) (hi:i<n) :
    (Tape.tab n f).look i z=f i := Tape.look_of_lt (Tape.tab n f) z hi

def RowSource {R M : ℕ} (C T P : ℕ) (rs : Tape Row.T)
    (labels : Fin M→UniformMatchingConjugateLoadMachine.Coefficient R) : Prop :=
  rs.len=M ∧ ∀i:Fin M,(rs.look i.val Row.blank).2.2=
    UniformMatchingConjugateLoadMachine.address C T P (labels i)

theorem program_coefficients {R M : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ))
    (bank : Fin R→ℂ) (rs : Tape Row.T)
    (labels : Fin M→UniformMatchingConjugateLoadMachine.Coefficient R)
    (source:PairSource b bank) (rows:RowSource C T P rs labels)
    (positive:C+R≤T) (negative:T+R≤P) :
    DFTModelCacheMatchingFactors.CoefficientSource
      (run program (args K C T P b rs)).val.2.2
      (fun i=>UniformMatchingConjugateLoadMachine.value K bank (labels i)) := by
  rw [program_value]
  refine ⟨rows.1,?_⟩
  intro i
  have hi:i.val<rs.len:=rows.1.symm ▸ i.isLt
  change (Tape.tab rs.len _).look i.val (0,0)=_
  rw [tab_lookup _ _ _ _ hi]
  change (run decode (argument C T P (rs.look i.val Row.blank).2.2 b (constantValues K))).val=_
  rw [rows.2 i]
  exact (decode_native K C T P b bank source positive negative (labels i)).1

theorem program_bounds {R M : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ))
    (bank : Fin R→ℂ) (rs : Tape Row.T)
    (labels : Fin M→UniformMatchingConjugateLoadMachine.Coefficient R)
    (source:PairSource b bank) (rows:RowSource C T P rs labels)
    (positive:C+R≤T) (negative:T+R≤P) :
    (run program (args K C T P b rs)).valid ∧
    (run program (args K C T P b rs)).work≤40*(Nat.log2 (K+1)+1)+99*M+521 ∧
    (run program (args K C T P b rs)).peak≤ max (K+6) (max M (max R 6)) := by
  have cst:=constants_bounds K
  have cells:∀j,j<rs.len→
      (run cell ((args K C T P b rs,constantValues K),j)).valid ∧
      (run cell ((args K C T P b rs,constantValues K),j)).work≤95 ∧
      (run cell ((args K C T P b rs,constantValues K),j)).peak≤ max R 6 := by
    intro j hj
    let i:Fin M:=⟨j,rows.1 ▸ hj⟩
    have value:=decode_native K C T P b bank source positive negative (labels i)
    have pointer:=rows.2 i
    change (rs.look j Row.blank).2.2=_ at pointer
    rw [cell_run,pointer]
    exact ⟨value.2.1,by change _+36≤95;omega,by simpa only [Bill.pay,max_zero] using value.2.2.2⟩
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one,constants_value,max_zero,and_true]
  constructor
  · exact ⟨cst.1,(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr (fun j hj=>(cells j hj).1)⟩
  constructor
  · rw [ModelEquivalenceInterpreter.tab_work]
    have sum:(∑j∈Finset.range rs.len,(run cell ((args K C T P b rs,constantValues K),j)).work)≤95*rs.len := by
      calc
        _≤∑_j∈Finset.range rs.len,95:=Finset.sum_le_sum (fun j hj=>(cells j (Finset.mem_range.mp hj)).2.1)
        _=95*rs.len:=by simp [Nat.mul_comm]
    have :=cst.2.1
    rw [rows.1] at sum ⊢
    omega
  · rw [ModelEquivalenceInterpreter.tab_peak]
    have sup:(Finset.range rs.len).sup (fun j=>(run cell ((args K C T P b rs,constantValues K),j)).peak)≤ max R 6 :=
      Finset.sup_le (fun j hj=>(cells j (Finset.mem_range.mp hj)).2.2)
    have :=cst.2.2
    rw [rows.1] at sup ⊢
    omega

/-- Forward logical leaves use the proved forward policy only. -/
theorem forward_rows {R M : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ))
    (bank : Fin R→ℂ) (rs : Tape Row.T) (labels : Fin M→UniformReplayPrint.Coefficient R)
    (leaves:∀i,UniformMatchingCoefficientValueBridge.ForwardLeaf K (labels i))
    (source:PairSource b bank)
    (rows:RowSource C T P rs (fun i=>UniformMatchingConjugateLoadMachine.fromReference (labels i)))
    (positive:C+R≤T) (negative:T+R≤P) :
    DFTModelCacheMatchingFactors.CoefficientSource
      (run program (args K C T P b rs)).val.2.2 (fun i=>(labels i).eval bank) := by
  have value:=program_coefficients K C T P b bank rs _ source rows positive negative
  simpa only [UniformMatchingCoefficientValueBridge.forward_value K bank _ (leaves _)] using value

/-- Inverse rows explicitly use the separate signed routing policy. -/
theorem inverse_rows {R M : ℕ} (K C T P : ℕ) (b : Tape (ℂ × ℂ))
    (bank : Fin R→ℂ) (rs : Tape Row.T) (labels : Fin M→UniformReplayPrint.Coefficient R)
    (leaves:∀i,UniformMatchingCoefficientValueBridge.ForwardLeaf K (labels i))
    (source:PairSource b bank)
    (rows:RowSource C T P rs (fun i=>UniformMatchingCoefficientValueBridge.inverseReference (labels i)))
    (positive:C+R≤T) (negative:T+R≤P) :
    DFTModelCacheMatchingFactors.CoefficientSource
      (run program (args K C T P b rs)).val.2.2 (fun i=>(labels i).negate.eval bank) := by
  have value:=program_coefficients K C T P b bank rs _ source rows positive negative
  simpa only [UniformMatchingCoefficientValueBridge.inverse_value K bank _ (leaves _)] using value

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
