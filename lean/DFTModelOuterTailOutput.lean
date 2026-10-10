import DFTModelOuterTailCRT
import DFTModelAffinePaired
import DFTModelResidualCore
import UniformChirpOutputMachine

set_option autoImplicit false

/-! Paper §5.2 inverse formula and §5.3 (5.7): negative-frequency lookup,
prepared normalization, prepared chirp and ordered output tabulation. Both
affine components are scaled by actual upstream primitives; flags survive. -/
namespace ExactFourierCircuits.DFTModelOuterTailOutput
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Datum := DFTModelAffine.Tagged
abbrev Input := p (p w w) (p (Ty.a sc) (p sc (Ty.a Datum)))
abbrev CellInput := p Input w
def count : Prog false Input w := .comp (.atom .fst) (.atom .fst)
def width : Prog false Input w := .comp (.atom .fst) (.atom .snd)
def coefficients : Prog false Input (Ty.a sc) := .comp (.atom .snd) (.atom .fst)
def normalization : Prog false Input sc :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def data : Prog false Input (Ty.a Datum) :=
  .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def negative : Prog false CellInput w :=
  binary .mod (binary .sub (.comp (.atom .fst) width) (.atom .snd))
    (.comp (.atom .fst) width)
def dataRead : Prog false CellInput Datum :=
  .comp (.fork (.comp (.atom .fst) data) negative) (.atom .look)
def normalizationRead : Prog false CellInput sc := .comp (.atom .fst) normalization
def normalized : Prog false CellInput Datum :=
  .comp (.fork dataRead normalizationRead) DFTModelMemoryAffinePointwise.multiply
def coefficientIndex : Prog false CellInput w := binary .mul (.atom .snd) (.atom (.lit 2))
def coefficientRead : Prog false CellInput sc :=
  .comp (.fork (.comp (.atom .fst) coefficients) coefficientIndex) (.atom .look)
def cell : Prog false CellInput Datum :=
  .comp (.fork normalized coefficientRead) DFTModelMemoryAffinePointwise.multiply
def program : Prog false Input (Ty.a Datum) := .tab count cell

def input (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) : Input.T :=
  ((n,V),(c,(k,z)))
def value (V j : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) : Datum.T :=
  DFTModelMemoryAffinePointwise.scaled
    (DFTModelMemoryAffinePointwise.scaled
      (z.look ((V-j)%V) (0,(0,0))) k) (c.look (j*2) 0)

theorem cell_run (n V j : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    run cell (input n V c k z,j) =
      ⟨value V j c k z,101,max (max (V-j) ((V-j)%V)) (max 2 (j*2)),True⟩ := by
  simp [cell,normalized,normalizationRead,normalization,dataRead,data,negative,width,
    coefficientRead,coefficients,coefficientIndex,input,binary,
    DFTModelMemoryAffinePointwise.multiply,DFTModelAffine.scale,
    DFTModelMemoryAffinePointwise.scaled,value,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem program_value (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V c k z)).val = Tape.tab n (fun j => value V j c k z) := by
  change (Bill.tab n Datum.blank (fun j => run cell (input n V c k z,j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab n) (funext (fun j => congrArg Bill.val (cell_run n V j c k z)))

theorem program_work (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V c k z)).work = 105*n+6 := by
  change 3+(Bill.tab n Datum.blank (fun j => run cell (input n V c k z,j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell (input n V c k z,j)).work) = (fun _ => 101) := by
    funext j
    exact congrArg Bill.work (cell_run n V j c k z)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V c k z)).valid := by
  change (True ∧ True) ∧ (Bill.tab n Datum.blank (fun j => run cell (input n V c k z,j))).valid
  refine ⟨⟨trivial,trivial⟩,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
  intro j _
  rw [cell_run]
  trivial

theorem program_peak (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V c k z)).peak ≤ max V (2*n) := by
  change max (max 0 (Bill.tab n Datum.blank
    (fun j => run cell (input n V c k z,j))).peak) 0 ≤ _
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [zero_max,max_zero,max_le_iff]
  constructor
  · omega
  · apply Finset.sup_le
    intro j hj
    have hn : j<n := Finset.mem_range.mp hj
    rw [cell_run]
    dsimp only [Bill.peak]
    have hmod : (V-j)%V≤V-j := Nat.mod_le _ _
    omega

theorem work_preserved (n V : ℕ) (c : Tape ℂ) (k : ℂ) (z : Tape Datum.T) :
    (run program (input n V c k z)).work ≤ 9*(13*n+6) := by
  rw [program_work]
  omega

theorem scaled_represents (z : Datum.T) (v : UniformMachine.Scalar) (k : ℂ)
    (h : DFTModelAffine.Represents z v) :
    DFTModelAffine.Represents (DFTModelMemoryAffinePointwise.scaled z k)
      (UniformChirpOutputMachine.scaled k v) := by
  rcases h with ⟨flag,value,prepared⟩
  refine ⟨flag,?_,?_⟩
  · change k*v.value=k*z.2.1+k*z.2.2
    rw [value,mul_add]
  · intro h
    change k*z.2.2=0
    rw [prepared h,mul_zero]

theorem scaled_paired (z : Datum.T) (v v0 : UniformMachine.Scalar) (k : ℂ)
    (h : z=DFTModelAffine.encodePaired v v0) :
    DFTModelMemoryAffinePointwise.scaled z k =
      DFTModelAffine.encodePaired (UniformChirpOutputMachine.scaled k v)
        (UniformChirpOutputMachine.scaled k v0) := by
  rw [h]
  dsimp only [DFTModelMemoryAffinePointwise.scaled,DFTModelAffine.encodePaired,
    DFTModelAffine.tagged,UniformChirpOutputMachine.scaled]
  simp only [mul_sub]

end
end ExactFourierCircuits.DFTModelOuterTailOutput
