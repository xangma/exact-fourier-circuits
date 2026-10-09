import DFTModelRecursiveScalarCore
import DFTModelClockControl
import DFTModelBinaryBaseline

set_option autoImplicit false

/-! Concrete ordinary tensor base/spectator loop. Each physical binary stage
is the already proved paired-channel Code primitive. Runtime stride doubles
once per axis and every stage rebuilds the whole bank once, not once per cell.
This module does not implement saving-network recursion. -/
namespace ExactFourierCircuits.DFTModelRecursiveBinary
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore DFTModelClockControl
noncomputable section

abbrev Acc := p w (Ty.a Tagged)
abbrev Iter := p Node (p w Acc)

def stride : Prog false Iter w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def bank : Prog false Iter (Ty.a Tagged) := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def imaginary : Prog false Iter sc := .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def pairs : Prog false Iter w :=
  .comp (.fork (.comp bank (.atom .len)) (.atom (.lit 2))) (.atom (.int .div))
def coefficients : Prog false Iter DFTModelBinaryPair.Coefficients :=
  .comp imaginary DFTModelBinaryCoefficients.program

def argument : Prog false Iter DFTModelBinaryStage.Input :=
  .fork pairs (.fork stride (.fork coefficients bank))
def doubled : Prog false Iter w :=
  .comp (.fork stride (.atom (.lit 2))) (.atom (.int .mul))
def body : Prog false Iter Acc :=
  .fork doubled (.comp argument DFTModelBinaryStage.program)
def initial : Prog false Node Acc := .fork (.atom (.lit 1)) (.atom .snd)
def bits : Prog false Node w := .comp (.atom .fst) (.atom .fst)
def loop : Prog false Node Acc := .loop bits initial body
def program : Prog false Node (Ty.a Tagged) := .comp loop (.atom .snd)

def next (I : ℂ) (P : ℕ) (v : Tape Tagged.T) : Tape Tagged.T :=
  (run DFTModelBinaryStage.program (v.len/2,(P,(((1+I)/2,(1-I)/2),v)))).val

def states (I : ℂ) (v : Tape Tagged.T) : ℕ → ℕ × Tape Tagged.T
  | 0 => (1,v)
  | i+1 => let z:=states I v i; (2*z.1,next I z.1 z.2)

theorem argument_run (k i P : ℕ) (I : ℂ) (v old : Tape Tagged.T) :
    run argument (((k,I),old),(i,(P,v))) =
      ⟨(v.len/2,(P,(((1+I)/2,(1-I)/2),v))),61,max 2 v.len,True⟩ := by
  simp only [argument,pairs,stride,bank,coefficients,imaginary,
    comp_run,fork_run,atom_run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rw [DFTModelBinaryCoefficients.program_run]
  simp [max_comm,Nat.div_le_self]

theorem doubled_run (k i P : ℕ) (I : ℂ) (v old : Tape Tagged.T) :
    run doubled (((k,I),old),(i,(P,v)))=⟨2*P,9,max 2 (2*P),True⟩ := by
  simp [doubled,stride,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.pass,Bill.pay,Bill.word,Nat.mul_comm]

theorem body_value (k i P : ℕ) (I : ℂ) (v old : Tape Tagged.T) :
    (run body (((k,I),old),(i,(P,v)))).val=(2*P,next I P v) := by
  rw [body,fork_run,doubled_run,comp_run,argument_run]
  rfl

theorem body_work (k i P : ℕ) (I : ℂ) (v old : Tape Tagged.T) :
    (run body (((k,I),old),(i,(P,v)))).work=420*(v.len/2)+116 := by
  rw [body,fork_run,doubled_run,comp_run,argument_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelBinaryStage.program_work]
  omega

theorem body_valid (k i P : ℕ) (I : ℂ) (v old : Tape Tagged.T) :
    (run body (((k,I),old),(i,(P,v)))).valid := by
  rw [body,fork_run,doubled_run,comp_run,argument_run]
  simp only [Bill.pass,Bill.pay,Bill.one,true_and,and_true]
  exact DFTModelBinaryStage.program_valid _ _ _ _ _

def stages (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (j : ℕ) : Bill (ℕ × Tape Tagged.T) :=
  Bill.steps (1,v) (fun i z => run body (((k,I),v),(i,z))) j

theorem stages_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    (stages k I v j).val=states I v j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (run body (((k,I),v),(j,(stages k I v j).val))).val=_
    rw [ih,body_value]
    rfl

theorem stages_valid (k : ℕ) (I : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    (stages k I v j).valid := by
  induction j with
  | zero => trivial
  | succ j ih =>
    change (stages k I v j).valid ∧ (run body (((k,I),v),(j,(stages k I v j).val))).valid
    exact ⟨ih,body_valid _ _ _ _ _ _⟩

theorem program_value (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run program ((k,I),v)).val=(states I v k).2 := by
  change (stages k I v k).val.2=_
  rw [stages_value]

theorem bits_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run bits ((k,I),v)=⟨k,3,0,True⟩ := by
  simp [bits,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem initial_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run initial ((k,I),v)=⟨(1,v),3,1,True⟩ := by
  simp [initial,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass]

theorem loop_run (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    run loop ((k,I),v)=⟨(stages k I v k).val,(stages k I v k).work+7,
      max 1 (stages k I v k).peak,(stages k I v k).valid⟩ := by
  change ((run bits ((k,I),v)).pass (fun l => (run initial ((k,I),v)).pass
    (fun z => Bill.steps z (fun i a => run body (((k,I),v),(i,a))) l))).pay 1 0=_
  rw [bits_run,initial_run]
  simp only [stages,Bill.pass,Bill.pay,zero_max,max_zero,true_and]
  congr 1; ac_rfl

theorem program_valid (k : ℕ) (I : ℂ) (v : Tape Tagged.T) :
    (run program ((k,I),v)).valid := by
  rw [program,comp_run,loop_run]
  simpa only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one,and_true] using stages_valid k I v k


theorem next_len (I : ℂ) (P : ℕ) (v : Tape Tagged.T) :
    (next I P v).len=2*(v.len/2) := by
  rw [next,DFTModelBinaryStage.program_value,DFTModelBinaryUnpacking.program_value]
  change (v.len/2)*2=2*(v.len/2)
  omega

theorem states_stride (I : ℂ) (v : Tape Tagged.T) (j : ℕ) :
    (states I v j).1=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change 2*(states I v j).1=2^(j+1)
    rw [ih,Nat.pow_succ,Nat.mul_comm]

theorem states_len (I : ℂ) (v : Tape Tagged.T) (even : 2*(v.len/2)=v.len) (j : ℕ) :
    (states I v j).2.len=v.len := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (next I (states I v j).1 (states I v j).2).len=v.len
    rw [next_len,ih,even]

theorem stages_work (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) (j : ℕ) :
    (stages k I v j).work=1+j*(420*(v.len/2)+117) := by
  induction j with
  | zero => simp [stages,Bill.steps,Bill.one]
  | succ j ih =>
    change (stages k I v j).work+
      (run body (((k,I),v),(j,(stages k I v j).val))).work+1=_
    rw [stages_value,body_work,states_len I v even,ih]
    ring

theorem program_work (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) :
    (run program ((k,I),v)).work=10+k*(420*(v.len/2)+117) := by
  rw [program,comp_run,loop_run]
  simp only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [stages_work k I v even]
  omega

theorem program_len (k : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) : (run program ((k,I),v)).val.len=v.len := by
  rw [program_value,states_len I v even]

theorem base_work_bound (k threshold : ℕ) (I : ℂ) (v : Tape Tagged.T)
    (even : 2*(v.len/2)=v.len) (small : k<threshold) :
    (run program ((k,I),v)).work≤(537*threshold+10)*(v.len+1) := by
  rw [program_work k I v even]
  have div := Nat.div_le_self v.len 2
  have per : 420*(v.len/2)+117≤537*(v.len+1) := by omega
  have times := Nat.mul_le_mul_left k per
  have kfit := Nat.mul_le_mul_right (537*(v.len+1)) (show k≤threshold by omega)
  calc
    _ ≤ 10+threshold*(537*(v.len+1)) := by omega
    _ ≤ _ := by nlinarith


/-- One real loop body is the actual thirty-instruction physical stage,
including exact actual/zero-source output pairing. The whole-loop tensor
induction is deliberately not assumed by this theorem. -/
theorem actual_stage {n B P A Q : ℕ} (x : Fin n → ℂ)
    (z z0 : Fin (P*2*Q) → UniformMachine.Scalar) (v : Tape Tagged.T)
    (s s0 : UniformMachine.State) (k i : ℕ) (old : Tape Tagged.T)
    (same : DFTModelAdmissibilityControl.StateMatch s s0)
    (len : v.len=P*2*Q)
    (encoded : ∀ j : Fin (P*2*Q),v.look j.val Tagged.blank=encodePaired (z j) (z0 j))
    (source : ∀ j : Fin (P*2*Q),s.scalarHeap (A+j.val)=some (z j))
    (baseline : ∀ j : Fin (P*2*Q),s0.scalarHeap (A+j.val)=some (z0 j))
    (pc : s.pc=0) (stride : s.natReg 2800=P) (base : s.natReg 2801=A)
    (count : s.natReg 2802=Q) (positive : 0<P) (separate : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (wb : UniformMachine.WordBound B s) (code : 30≤B) (extent : A+P*2*Q≤B)
    (doubleFit : 2*P≤B) :
    ∃ u u0,
      UniformMachine.BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(P*Q)+6) u ∧
      UniformMachine.BoundedExecution UniformBinaryCStageMachine.program n (fun _ => 0) B s0 (25*(P*Q)+6) u0 ∧
      DFTModelAdmissibilityControl.StateMatch u u0 ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s u ∧
      UniformBinaryCStageMachine.Frame A (P*2*Q) s0 u0 ∧
      (∀ j : Fin (P*2*Q),∃ a a0,
        u.scalarHeap (A+j.val)=some a ∧ u0.scalarHeap (A+j.val)=some a0 ∧
        (run body (((k,Complex.I),old),(i,(P,v)))).val.2.look j.val Tagged.blank=encodePaired a a0) ∧
      (run body (((k,Complex.I),old),(i,(P,v)))).valid ∧
      (run body (((k,Complex.I),old),(i,(P,v)))).work≤20*(25*(P*Q)+6) ∧
      (run body (((k,Complex.I),old),(i,(P,v)))).peak≤B := by
  have M : v.len/2=P*Q := by
    rw [len,show P*2*Q=(P*Q)*2 by ring,Nat.mul_div_cancel _ (by decide : 0<2)]
  obtain ⟨u,u0,r,r0,matched,frame,frame0,output,_valid,_work,peak⟩ :=
    DFTModelBinaryBaseline.actual_execution x z z0 v s s0 same encoded source baseline
      pc stride base count positive separate constants wb code extent
  have value : (run body (((k,Complex.I),old),(i,(P,v)))).val.2=
      (run DFTModelBinaryStage.program (P*Q,(P,((ExactFourierCircuits.a,ExactFourierCircuits.b),v)))).val := by
    rw [body_value]
    dsimp only [next]
    rw [M]
    rfl
  refine ⟨u,u0,r,r0,matched,frame,frame0,?_,body_valid _ _ _ _ _ _,?_,?_⟩
  · intro j
    obtain ⟨a,a0,ha,ha0,he,_⟩:=output j
    exact ⟨a,a0,ha,ha0,by rw [value];exact he⟩
  · rw [body_work,M]
    omega
  · rw [body,fork_run,doubled_run,comp_run,argument_run]
    simp only [Bill.pass,Bill.pay,Bill.one,max_zero]
    rw [M]
    exact max_le (max_le (by omega) doubleFit)
      (max_le (max_le (by omega) (by omega)) peak)

end
end ExactFourierCircuits.DFTModelRecursiveBinary
