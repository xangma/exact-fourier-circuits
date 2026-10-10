import DFTModelOuterTailCRT
import DFTModelAffinePaired

set_option autoImplicit false

/-! Paper §5.3: multiply the actual transformed data role by the saved
prepared spectrum, then perform the original BI and AP gathers. One typed
execution retains both gathered banks, the prepared spectrum and spectator
input tape. No two homogeneous data values are ever multiplied. -/
namespace ExactFourierCircuits.DFTModelOuterMiddle
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Input := p DFTModelOuterTailCRT.Input (Ty.a sc)
abbrev Output := p DFTModelOuterTailCRT.Output (p (Ty.a sc) (Ty.a Datum))
abbrev Joined := p Input (Ty.a Datum)
def volume : Prog false Input w := .comp (.atom .fst) (.atom .fst)
def alpha : Prog false Input (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def beta : Prog false Input (Ty.a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def data : Prog false Input (Ty.a Datum) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def kernel : Prog false Input (Ty.a sc) := .atom .snd
def pointwise : Prog false Input (Ty.a Datum) :=
  .comp (.fork volume (.fork data kernel)) DFTModelMemoryAffinePointwise.program
def gather : Prog false Joined DFTModelOuterTailCRT.Output :=
  .comp (.fork (.comp (.atom .fst) volume)
    (.fork (.comp (.atom .fst) alpha) (.fork (.comp (.atom .fst) beta) (.atom .snd))))
    DFTModelOuterTailCRT.program
def retained : Prog false Joined (p (Ty.a sc) (Ty.a Datum)) :=
  .fork (.comp (.atom .fst) kernel) (.comp (.atom .fst) data)
def program : Prog false Input Output :=
  .comp (.fork (.atom .id) pointwise) (.fork gather retained)

def input (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) : Input.T :=
  (DFTModelOuterTailCRT.input V a b z,k)
def multiplied (V : ℕ) (z : Tape Datum.T) (k : Tape ℂ) : Tape Datum.T :=
  Tape.tab V (fun j => DFTModelMemoryAffinePointwise.scaled
    (z.look j (0,(0,0))) (k.look j 0))

attribute [local irreducible] DFTModelMemoryAffinePointwise.program DFTModelOuterTailCRT.program
theorem program_run (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    run program (input V a b z k) =
      ((run DFTModelMemoryAffinePointwise.program (V,(z,k))).pass (fun m =>
        (run DFTModelOuterTailCRT.program (DFTModelOuterTailCRT.input V a b m)).pass
          (fun t => Bill.one (t,(k,z))))).pay 56 0 := by
  simp only [program,pointwise,gather,retained,volume,alpha,beta,data,kernel,input,
    DFTModelOuterTailCRT.input,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  simp only [zero_max,max_zero,true_and,and_true]
  congr 1
  · omega

theorem program_value (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a b z k)).val =
      ((DFTModelOuterTailCRT.gatherValue V a
          (DFTModelOuterTailCRT.gatherValue V b (multiplied V z k)),
        DFTModelOuterTailCRT.gatherValue V b (multiplied V z k)),(k,z)) := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelMemoryAffinePointwise.program_value,DFTModelOuterTailCRT.program_value]
  rfl

theorem program_work (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a b z k)).work = 91*V+100 := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelMemoryAffinePointwise.program_work,DFTModelOuterTailCRT.program_work]
  omega

theorem program_peak (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a b z k)).peak = V := by
  rw [program_run]
  simp only [Bill.pass,Bill.pay,Bill.one]
  rw [DFTModelMemoryAffinePointwise.program_peak,DFTModelOuterTailCRT.program_peak]
  omega

theorem program_valid (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a b z k)).valid := by
  rw [program_run]
  exact ⟨DFTModelMemoryAffinePointwise.program_valid _ _ _,
    DFTModelOuterTailCRT.program_valid _ _ _ _,trivial⟩

theorem work_preserved (V : ℕ) (a b : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ) :
    (run program (input V a b z k)).work ≤ 4*(27*V+27) := by
  rw [program_work]
  omega

theorem multiplied_lookup {V : ℕ} (z : Tape Datum.T) (k : Tape ℂ) (j : Fin V) :
    (multiplied V z k).look j.val (0,(0,0))=
      DFTModelMemoryAffinePointwise.scaled (z.look j.val (0,(0,0))) (k.look j.val 0) := by
  change (Tape.tab V _).look j.val (0,(0,0)) = _
  rw [Tape.look_of_lt]
  rfl

theorem scaled_paired (v v0 : UniformMachine.Scalar) (y : ℂ) :
    DFTModelMemoryAffinePointwise.scaled (DFTModelAffine.encodePaired v v0) y=
      DFTModelAffine.encodePaired (UniformChirpPointwiseMachine.productScalar v y)
        (UniformChirpPointwiseMachine.productScalar v0 y) := by
  dsimp only [DFTModelMemoryAffinePointwise.scaled,DFTModelAffine.encodePaired,
    DFTModelAffine.tagged,UniformChirpPointwiseMachine.productScalar]
  simp only [mul_sub,mul_comm]

end
end ExactFourierCircuits.DFTModelOuterMiddle
