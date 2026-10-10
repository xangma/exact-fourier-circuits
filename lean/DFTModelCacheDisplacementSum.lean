import DFTModelCacheKernelBanks
import UniformRankKernelMachine

set_option autoImplicit false

/-! The actual finite Toeplitz border sum, evaluated by charged prepared
arithmetic and random reads from the produced H/G banks. -/
namespace ExactFourierCircuits.DFTModelCacheDisplacementSum
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Banks := p (Ty.a sc) (Ty.a sc)
abbrev Input := p Banks (p w (p w w))
abbrev TermInput := p Input (p w sc)

def integer {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def scalar {s : Ty} (op : Atom false (p sc sc) sc)
    (f g : Prog false s sc) : Prog false s sc := .comp (.fork f g) (.atom op)
def split : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def column : Prog false Input w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def count : Prog false Input w := integer .sub split column
def index : Prog false TermInput w := .comp (.atom .snd) (.atom .fst)
def row : Prog false TermInput w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def col : Prog false TermInput w := .comp (.atom .fst) column
def hBank : Prog false TermInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def gBank : Prog false TermInput (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def hRead : Prog false TermInput sc :=
  .comp (.fork hBank (integer .sub (integer .sub row col) index)) (.atom .look)
def gRead : Prog false TermInput sc := .comp (.fork gBank index) (.atom .look)
def term : Prog false TermInput sc := scalar (.add .scalar)
  (.comp (.atom .snd) (.atom .snd)) (scalar (.scale .scalar) hRead gRead)
def program : Prog false Input sc := .loop count (.atom (.cz .scalar)) term

theorem term_run (h g : Tape ℂ) (s I J u : ℕ) (z : ℂ) :
    run term (((h,g),(s,(I,J))),(u,z))=
      ⟨z+h.look (I-J-u) 0*g.look u 0,51,I-J,True⟩ := by
  simp [term,scalar,hRead,gRead,integer,hBank,gBank,row,col,column,index,
    run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

attribute [local irreducible] term

def value (h g : Tape ℂ) (I J k : ℕ) : ℂ :=
  ∑u∈Finset.range k,h.look (I-J-u) 0*g.look u 0

theorem steps_run (h g : Tape ℂ) (s I J k : ℕ) :
    Bill.steps (0:ℂ) (fun u z=>run term (((h,g),(s,(I,J))),(u,z))) k=
      ⟨value h g I J k,52*k+1,if k=0 then 0 else max k (I-J),True⟩ := by
  induction k with
  | zero => simp [Bill.steps,Bill.one,value]
  | succ k ih =>
    rw [Bill.steps,ih]
    dsimp only [Bill.pass]
    rw [term_run]
    simp only [Bill.pay,value,Finset.sum_range_succ]
    congr 1
    · by_cases hk:k=0 <;> simp [hk,max_comm]
    · simp

theorem count_run (h g : Tape ℂ) (s I J : ℕ) :
    run count ((h,g),(s,(I,J)))=⟨s-J,11,s-J,True⟩ := by
  simp [count,integer,split,column,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem program_run (h g : Tape ℂ) (s I J : ℕ) :
    run program ((h,g),(s,(I,J)))=
      ⟨value h g I J (s-J),52*(s-J)+14,
        max (s-J) (if s-J=0 then 0 else I-J),True⟩ := by
  change ((run count ((h,g),(s,(I,J)))).pass (fun n=>(Bill.one (0:ℂ)).pass
    (fun z=>Bill.steps z (fun u v=>run term (((h,g),(s,(I,J))),(u,v))) n))).pay 1 0=_
  rw [count_run]
  dsimp only [Bill.pass,Bill.one]
  rw [steps_run]
  simp only [Bill.pay]
  congr 1 <;> first | omega | simp
  split_ifs <;> omega

theorem program_valid (h g : Tape ℂ) (s I J : ℕ) :
    (run program ((h,g),(s,(I,J)))).valid := by rw [program_run];trivial

theorem program_work (h g : Tape ℂ) (s I J : ℕ) :
    (run program ((h,g),(s,(I,J)))).work=52*(s-J)+14 := by rw [program_run]

theorem program_peak (h g : Tape ℂ) (s I J B : ℕ) (hs:s≤B) (hI:I≤B) :
    (run program ((h,g),(s,(I,J)))).peak≤B := by
  rw [program_run]
  dsimp only [Bill.peak]
  split_ifs <;> omega

theorem source_value (h g : Tape ℂ) (s I J : ℕ) (hf gf : ℕ→ℂ)
    (hh:∀u,u<s-J → h.look (I-J-u) 0=hf (I-J-u))
    (hg:∀u,u<s-J → g.look u 0=gf u) :
    (run program ((h,g),(s,(I,J)))).val=
      OAI.ExactFourier.ToeplitzLayers.cross s hf gf I J := by
  rw [program_run]
  dsimp only [Bill.val]
  unfold value OAI.ExactFourier.ToeplitzLayers.cross
  apply Finset.sum_congr rfl
  intro u hu
  rw [hh u (Finset.mem_range.mp hu),hg u (Finset.mem_range.mp hu)]

end
end ExactFourierCircuits.DFTModelCacheDisplacementSum
