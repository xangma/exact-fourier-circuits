import DFTModelSavingBinarySuffixProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingBinarySuffix
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
open UniformBinaryTensorCoordinates
noncomputable section
attribute [local irreducible] program body DFTModelRecursiveBinary.body

def stages (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) (j : ℕ) : Bill DFTModelRecursiveBinary.Acc.T :=
  Bill.steps (2^b,v) (fun i z=>run body ((b,((k,I),v)),(i,z))) j

def partialAxes {R : ℕ} (k b j : ℕ) (f : Fin R → Fin (2^k) → Scalar) : Fin R → Fin (2^k) → Scalar :=
  fun r=>applyAxes k (((List.finRange k).drop b).take j) (f r)

theorem partialAxes_succ {R k b j : ℕ} (hj : b+j<k) (f : Fin R → Fin (2^k) → Scalar) :
    partialAxes k b (j+1) f=fun r=>axisAction k ⟨b+j,hj⟩ (partialAxes k b j f r) := by
  funext r
  unfold partialAxes
  rw [List.take_succ_eq_append_getElem (show j<((List.finRange k).drop b).length by simp;omega)]
  simp [applyAxes,List.foldl_append]

theorem stages_value {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b j : ℕ) (cap : b+j≤k) :
    (stages b k Complex.I (paired f f0) j).val=
      (2^(b+j),paired (partialAxes k b j f) (partialAxes k b j f0)) := by
  induction j with
  | zero => simp only [stages,Bill.steps,Bill.one,Nat.add_zero];rfl
  | succ j ih =>
    have hj : b+j<k := by omega
    change (run body ((b,((k,Complex.I),paired f f0)),
      (j,(stages b k Complex.I (paired f f0) j).val))).val=_
    rw [ih (by omega),body_run]
    simp only [Bill.pay]
    rw [DFTModelRecursiveBinary.body_value]
    change (2*2^(b+j),DFTModelRecursiveBinary.next Complex.I (2^(b+j))
      (paired (partialAxes k b j f) (partialAxes k b j f0)))=_
    rw [DFTModelSavingBinary.next_paired (⟨b+j,hj⟩ : Fin k),
      partialAxes_succ hj f,partialAxes_succ hj f0]
    congr 1
    rw [show b+(j+1)=(b+j)+1 by omega,Nat.pow_succ,Nat.mul_comm]

theorem stages_valid (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    (stages b k I v j).valid := by
  induction j with
  | zero => trivial
  | succ j ih =>
    change (stages b k I v j).valid ∧
      (run body ((b,((k,I),v)),(j,(stages b k I v j).val))).valid
    rcases he : (stages b k I v j).val with ⟨P,bank⟩
    rw [body_run]
    exact ⟨ih,DFTModelRecursiveBinary.body_valid _ _ _ _ _ _⟩

theorem loop_run (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run loop (b,((k,I),v))=
      ⟨(stages b k I v (k-b)).val,(stages b k I v (k-b)).work+18+8*b,
        max (max (k-b) (run power (b,((k,I),v))).peak) (stages b k I v (k-b)).peak,
        (stages b k I v (k-b)).valid⟩ := by
  rw [loop,typed_loop_run,count_run,start_run]
  simp only [Bill.pass,Bill.pay,true_and,stages]
  congr 1
  · omega
  · omega

theorem tapeProgram_paired {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) :
    (run tapeProgram (b,((k,Complex.I),paired f f0))).val=
      paired (fun r=>applyAxes k ((List.finRange k).drop b) (f r))
        (fun r=>applyAxes k ((List.finRange k).drop b) (f0 r)) := by
  rw [tapeProgram,comp_run,loop_run]
  simp only [Bill.pass,Bill.pay,atom_run,Atom.run,Bill.one]
  rw [stages_value f f0 b (k-b) (by omega)]
  change paired (fun r=>applyAxes k (((List.finRange k).drop b).take (k-b)) (f r))
    (fun r=>applyAxes k (((List.finRange k).drop b).take (k-b)) (f0 r))=_
  rw [show ((List.finRange k).drop b).take (k-b)=(List.finRange k).drop b from by simp]

theorem program_run (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run program (b,((k,I),v))=
      {run tapeProgram (b,((k,I),v)) with
        val:=((k,I),(run tapeProgram (b,((k,I),v))).val),
        work:=(run tapeProgram (b,((k,I),v))).work+4} := by
  rw [program,fork_run,comp_run]
  simp only [atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,zero_max,max_zero,true_and,and_true]
  congr 1
  omega

theorem program_paired {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) :
    (run program (b,((k,Complex.I),paired f f0))).val=
      ((k,Complex.I),paired (fun r=>applyAxes k ((List.finRange k).drop b) (f r))
        (fun r=>applyAxes k ((List.finRange k).drop b) (f0 r))) := by
  rw [program_run,tapeProgram_paired f f0 b cap]

theorem program_lookup {R k : ℕ} (f f0 : Fin R → Fin (2^k) → Scalar)
    (b : ℕ) (cap : b≤k) (r : Fin R) (z : Fin (2^k)) :
    (run program (b,((k,Complex.I),paired f f0))).val.2.look (r.val*2^k+z.val) Tagged.blank=
      encodePaired (applyAxes k ((List.finRange k).drop b) (f r) z)
        (applyAxes k ((List.finRange k).drop b) (f0 r) z) := by
  rw [program_paired f f0 b cap]
  exact paired_lookup _ _ r z

theorem program_valid (b k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run program (b,((k,I),v))).valid := by
  rw [program_run,tapeProgram,comp_run,loop_run]
  exact ⟨stages_valid _ _ _ _ _,trivial⟩

end
end ExactFourierCircuits.DFTModelSavingBinarySuffix
