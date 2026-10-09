import DFTModelRecursiveScalarSource
import UniformNativeExchangeRecordMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveExchange
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore
noncomputable section

abbrev PairNat := p w w
abbrev PairInput := p PairNat DFTModelClockControl.Node
abbrev Row := p PairNat (p w (Ty.a Tagged))
abbrev Cell := p Row w

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

def negated (z : Tagged.T) : Tagged.T := (z.1,(-z.2.1,-z.2.2))
def negate : Prog false Tagged Tagged :=
  .fork (.atom .fst)
    (.fork
      (.comp (.fork (.atom (.cz .scalar)) (.comp (.atom .snd) (.atom .fst)))
        (.atom (.sub .scalar)))
      (.comp (.fork (.atom (.cz .left)) (.comp (.atom .snd) (.atom .snd)))
        (.atom (.sub .left))))

theorem negate_run (z : Tagged.T) : run negate z=⟨negated z,17,0,True⟩ := by
  simp [negate,negated,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem negated_paired (a a0 : UniformMachine.Scalar) :
    negated (encodePaired a a0)=encodePaired
      (UniformFixedNetworkExchangeChildMachine.negative a)
      (UniformFixedNetworkExchangeChildMachine.negative a0) := by
  simp only [negated,encodePaired,tagged,UniformFixedNetworkExchangeChildMachine.negative]
  congr 2
  ring

def first : Prog false Cell w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def second : Prog false Cell w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def volume : Prog false Cell w := .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def source : Prog false Cell (Ty.a Tagged) := .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def role : Prog false Cell w := nat .div (.atom .snd) volume
def test (d : Prog false Cell w) : Prog false Cell w :=
  nat .add (nat .sub role d) (nat .sub d role)
def address (d : Prog false Cell w) : Prog false Cell w :=
  nat .add (nat .mul d volume) (nat .mod (.atom .snd) volume)
def readRole (d : Prog false Cell w) : Prog false Cell Tagged :=
  .comp (.fork source (address d)) (.atom .look)
def current : Prog false Cell Tagged := .comp (.fork source (.atom .snd)) (.atom .look)
def cell : Prog false Cell Tagged :=
  .ifz (test first) (readRole second)
    (.ifz (test second) (.comp (readRole first) negate) current)

def rowSource : Prog false Row (Ty.a Tagged) := .comp (.atom .snd) (.atom .snd)
def rowLength : Prog false Row w := .comp rowSource (.atom .len)
def rows : Prog false Row (Ty.a Tagged) := .tab rowLength cell

def setup (R : ℕ) : Prog false PairInput Row :=
  .fork (.atom .fst)
    (.fork
      (nat .div (.comp (.atom .snd) (.comp (.atom .snd) (.atom .len))) (.atom (.lit R)))
      (.comp (.atom .snd) (.atom .snd)))
def pairProgram (R : ℕ) : Prog false PairInput DFTModelClockControl.Node :=
  .fork (.comp (.atom .snd) (.atom .fst)) (.comp (setup R) rows)

def result (d s V : ℕ) (v : Tape Tagged.T) (j : ℕ) : Tagged.T :=
  if j/V=d then v.look (s*V+j%V) Tagged.blank
  else if j/V=s then negated (v.look (d*V+j%V) Tagged.blank)
  else v.look j Tagged.blank

theorem first_run (d s V j : ℕ) (v : Tape Tagged.T) :
    run first (((d,s),(V,v)),j)=⟨d,5,0,True⟩ := by
  simp [first,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
theorem second_run (d s V j : ℕ) (v : Tape Tagged.T) :
    run second (((d,s),(V,v)),j)=⟨s,5,0,True⟩ := by
  simp [second,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
theorem role_run (d s V j : ℕ) (v : Tape Tagged.T) :
    run role (((d,s),(V,v)),j)=⟨j/V,9,j/V,True⟩ := by
  simp [role,nat,volume,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem test_run (dir : Prog false Cell w) (d s V j t : ℕ) (v : Tape Tagged.T)
    (h : run dir (((d,s),(V,v)),j)=⟨t,5,0,True⟩) :
    run (test dir) (((d,s),(V,v)),j)=⟨j/V-t+(t-j/V),37,max (j/V) (j/V-t+(t-j/V)),True⟩ := by
  simp only [test,nat,comp_run,fork_run]
  rw [role_run,h]
  simp only [atom_run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,and_true]
  apply congrArg (fun p => Bill.mk (j/V-t+(t-j/V)) 37 p True)
  simp only [max_zero,zero_max]
  omega

theorem readRole_run (dir : Prog false Cell w) (d s V j t : ℕ) (v : Tape Tagged.T)
    (h : run dir (((d,s),(V,v)),j)=⟨t,5,0,True⟩) :
    run (readRole dir) (((d,s),(V,v)),j)=
      ⟨v.look (t*V+j%V) Tagged.blank,33,t*V+j%V,True⟩ := by
  simp only [readRole,address,nat,comp_run,fork_run,atom_run,Atom.run]
  rw [h]
  simp [source,volume,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem current_run (d s V j : ℕ) (v : Tape Tagged.T) :
    run current (((d,s),(V,v)),j)=⟨v.look j Tagged.blank,9,0,True⟩ := by
  simp [current,source,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem cell_value (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell (((d,s),(V,v)),j)).val=result d s V v j := by
  rw [cell,ifz_run,test_run first d s V j d v (first_run _ _ _ _ _)]
  have hd : (j/V-d+(d-j/V)=0)↔j/V=d := by omega
  simp only [Bill.pass,Bill.pay,hd,result]
  by_cases h : j/V=d
  · simp only [h,ite_true]
    rw [readRole_run second d s V j s v (second_run _ _ _ _ _)]
  · simp only [h,ite_false]
    rw [ifz_run,test_run second d s V j s v (second_run _ _ _ _ _)]
    have hs : (j/V-s+(s-j/V)=0)↔j/V=s := by omega
    simp only [Bill.pass,Bill.pay,hs]
    split_ifs
    · rw [comp_run,readRole_run first d s V j d v (first_run _ _ _ _ _)]
      simp only [Bill.pass,Bill.pay]
      rw [negate_run]
    · rw [current_run]

theorem cell_valid (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell (((d,s),(V,v)),j)).valid := by
  rw [cell,ifz_run,test_run first d s V j d v (first_run _ _ _ _ _)]
  simp only [Bill.pass,Bill.pay,true_and]
  split_ifs
  · rw [readRole_run second d s V j s v (second_run _ _ _ _ _)]
    trivial
  · rw [ifz_run,test_run second d s V j s v (second_run _ _ _ _ _)]
    simp only [Bill.pass,Bill.pay,true_and]
    split_ifs
    · rw [comp_run,readRole_run first d s V j d v (first_run _ _ _ _ _)]
      simp only [Bill.pass,Bill.pay,true_and]
      rw [negate_run]
      trivial
    · rw [current_run]
      trivial

theorem cell_work_bound (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell (((d,s),(V,v)),j)).work≤127 := by
  rw [cell,ifz_run,test_run first d s V j d v (first_run _ _ _ _ _)]
  simp only [Bill.pass,Bill.pay]
  split_ifs
  · rw [readRole_run second d s V j s v (second_run _ _ _ _ _)]
    norm_num
  · rw [ifz_run,test_run second d s V j s v (second_run _ _ _ _ _)]
    simp only [Bill.pass,Bill.pay]
    split_ifs
    · rw [comp_run,readRole_run first d s V j d v (first_run _ _ _ _ _)]
      simp only [Bill.pass,Bill.pay]
      rw [negate_run]
      norm_num
    · rw [current_run]
      norm_num

end
end ExactFourierCircuits.DFTModelRecursiveExchange
