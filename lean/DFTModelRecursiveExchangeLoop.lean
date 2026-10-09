import DFTModelRecursiveExchangePair

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section

abbrev PairTape := Ty.a PairNat
abbrev PairsInput := p PairTape DFTModelClockControl.Node
abbrev Body := p PairsInput (p w DFTModelClockControl.Node)

def readPair : Prog false Body PairNat :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst))
    (.comp (.atom .snd) (.atom .fst))) (.atom .look)
def oldNode : Prog false Body DFTModelClockControl.Node := .comp (.atom .snd) (.atom .snd)
def body (R : ℕ) : Prog false Body DFTModelClockControl.Node :=
  .comp (.fork readPair oldNode) (pairProgram R)
def pairsProgram (R : ℕ) : Prog false PairsInput DFTModelClockControl.Node :=
  .loop (.comp (.atom .fst) (.atom .len)) (.atom .snd) (body R)

attribute [local irreducible] pairProgram body pairsProgram

def pairTape {R : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R)) : Tape PairNat.T :=
  ⟨ps.length,fun i => ((ps[i]).first.val,(ps[i]).second.val)⟩

def steps (R : ℕ) (ps : Tape PairNat.T) (initial : DFTModelClockControl.Node.T) (C : ℕ) :=
  Bill.steps initial (fun i old => run (body R) ((ps,initial),(i,old))) C

theorem body_run (R i k : ℕ) (I : ℂ) (ps : Tape PairNat.T)
    (initial : DFTModelClockControl.Node.T) (v : Tape Tagged.T) :
    run (body R) ((ps,initial),(i,((k,I),v)))=
      (run (pairProgram R) (ps.look i PairNat.blank,((k,I),v))).pay 14 0 := by
  simp only [body,comp_run,fork_run,readPair,oldNode,comp_run,fork_run,atom_run,
    Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [max_zero,zero_max,true_and,and_true]
  congr 1
  omega

theorem pairs_run (R : ℕ) (ps : Tape PairNat.T) (initial : DFTModelClockControl.Node.T) :
    run (pairsProgram R) (ps,initial)=(steps R ps initial ps.len).pay 5 ps.len := by
  simp only [pairsProgram,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,steps,true_and,and_true]
  congr 1
  · omega
  · omega

theorem pairTape_lookup {R : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (i : ℕ) (hi : i<ps.length) :
    (pairTape ps).look i PairNat.blank=((ps[i]).first.val,(ps[i]).second.val) := by
  exact Tape.look_of_lt _ _ hi

theorem actions_take_succ {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (f : Fin R → Fin V → UniformMachine.Scalar) (i : ℕ) (hi : i<ps.length) :
    UniformNativeExchangeRecordMachine.actions (ps.take (i+1)) f=
      UniformFixedNetworkExchangeChildMachine.values (ps[i]).first (ps[i]).second
        (UniformNativeExchangeRecordMachine.actions (ps.take i) f) := by
  induction ps generalizing f i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change UniformNativeExchangeRecordMachine.actions (ps.take (i+1))
        (UniformFixedNetworkExchangeChildMachine.values p.first p.second f)=_
      exact ih _ i (by simpa using hi)

theorem steps_paired {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k C : ℕ) (I : ℂ) (cap : C≤ps.length) :
    (steps R (pairTape ps) ((k,I),paired f f0) C).val=
      ((k,I),paired (UniformNativeExchangeRecordMachine.actions (ps.take C) f)
        (UniformNativeExchangeRecordMachine.actions (ps.take C) f0)) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    have ci : C<ps.length := by omega
    change (run (body R) ((pairTape ps,((k,I),paired f f0)),
      (C,(steps R (pairTape ps) ((k,I),paired f f0) C).val))).val=_
    rw [ih (by omega),body_run,pairTape_lookup ps C ci]
    change (run (pairProgram R) (((ps[C]).first.val,(ps[C]).second.val),
      ((k,I),paired (UniformNativeExchangeRecordMachine.actions (ps.take C) f)
        (UniformNativeExchangeRecordMachine.actions (ps.take C) f0)))).val=_
    rw [pair_paired _ _ positive,actions_take_succ ps f C ci,actions_take_succ ps f0 C ci]

theorem steps_valid (R C : ℕ) (ps : Tape PairNat.T) (initial : DFTModelClockControl.Node.T) :
    (steps R ps initial C).valid := by
  induction C with
  | zero => trivial
  | succ C ih =>
    change (steps R ps initial C).valid ∧
      (run (body R) ((ps,initial),(C,(steps R ps initial C).val))).valid
    refine ⟨ih,?_⟩
    obtain ⟨⟨k,I⟩,v⟩ := (steps R ps initial C).val
    rw [body_run]
    obtain ⟨d,s⟩ := ps.look C PairNat.blank
    exact pair_valid R d s k I v

theorem steps_work_bound {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k C : ℕ) (I : ℂ) (cap : C≤ps.length) :
    (steps R (pairTape ps) ((k,I),paired f f0) C).work≤1+(43+131*(R*V))*C := by
  induction C with
  | zero => exact le_rfl
  | succ C ih =>
    have ci : C<ps.length := by omega
    have prior := ih (by omega)
    have cost := pair_work_bound R (ps[C]).first.val (ps[C]).second.val k I
      (paired (UniformNativeExchangeRecordMachine.actions (ps.take C) f)
        (UniformNativeExchangeRecordMachine.actions (ps.take C) f0))
    change _≤28+131*(R*V) at cost
    change (steps R (pairTape ps) ((k,I),paired f f0) C).work+
      (run (body R) ((pairTape ps,((k,I),paired f f0)),
        (C,(steps R (pairTape ps) ((k,I),paired f f0) C).val))).work+1≤_
    rw [steps_paired ps positive f f0 k C I (by omega),body_run,pairTape_lookup ps C ci]
    dsimp only [Bill.pay,Bill.work]
    nlinarith

theorem steps_peak_bound {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (roles : 0<R) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k C B : ℕ) (I : ℂ) (cap : C≤ps.length) (countFit : ps.length≤B) (fit : R*V≤B) :
    (steps R (pairTape ps) ((k,I),paired f f0) C).peak≤B := by
  induction C with
  | zero => exact Nat.zero_le _
  | succ C ih =>
    have ci : C<ps.length := by omega
    have prior := ih (by omega)
    have hp := pair_peak_bound R (ps[C]).first.val (ps[C]).second.val k V B I
      (paired (UniformNativeExchangeRecordMachine.actions (ps.take C) f)
        (UniformNativeExchangeRecordMachine.actions (ps.take C) f0))
      positive roles rfl (ps[C]).first.isLt (ps[C]).second.isLt fit
    change max (max (steps R (pairTape ps) ((k,I),paired f f0) C).peak
      (run (body R) ((pairTape ps,((k,I),paired f f0)),
        (C,(steps R (pairTape ps) ((k,I),paired f f0) C).val))).peak) (C+1)≤_
    rw [steps_paired ps positive f f0 k C I (by omega),body_run,pairTape_lookup ps C ci]
    simp only [Bill.pay,max_zero]
    exact max_le (max_le prior hp) (by omega)

theorem pairs_value {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) (k : ℕ) (I : ℂ) :
    (run (pairsProgram R) (pairTape ps,((k,I),paired f f0))).val=
      ((k,I),paired (UniformNativeExchangeRecordMachine.actions ps f)
        (UniformNativeExchangeRecordMachine.actions ps f0)) := by
  rw [pairs_run]
  change (steps R (pairTape ps) ((k,I),paired f f0) ps.length).val=_
  simpa only [List.take_length] using steps_paired ps positive f f0 k ps.length I (le_refl _)

theorem pairs_valid (R : ℕ) (ps : Tape PairNat.T) (initial : DFTModelClockControl.Node.T) :
    (run (pairsProgram R) (ps,initial)).valid := by
  rw [pairs_run]
  exact steps_valid _ _ _ _

theorem pairs_work_bound {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (f f0 : Fin R → Fin V → UniformMachine.Scalar) (k : ℕ) (I : ℂ) :
    (run (pairsProgram R) (pairTape ps,((k,I),paired f f0))).work≤
      6+(43+131*(R*V))*ps.length := by
  rw [pairs_run]
  have h := steps_work_bound ps positive f f0 k ps.length I (le_refl _)
  change (steps R (pairTape ps) ((k,I),paired f f0) ps.length).work+5≤_
  omega

theorem pairs_peak_bound {R V : ℕ} (ps : List (UniformNativeExchangeRecordMachine.Pair R))
    (positive : 0<V) (roles : 0<R) (f f0 : Fin R → Fin V → UniformMachine.Scalar)
    (k B : ℕ) (I : ℂ) (countFit : ps.length≤B) (fit : R*V≤B) :
    (run (pairsProgram R) (pairTape ps,((k,I),paired f f0))).peak≤B := by
  rw [pairs_run]
  exact max_le (steps_peak_bound ps positive roles f f0 k ps.length B I
    (le_refl _) countFit fit) countFit

end
end ExactFourierCircuits.DFTModelRecursiveExchange
