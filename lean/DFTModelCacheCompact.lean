import DFTModelCacheOddAxesCorrect

set_option autoImplicit false

/-! Charged conversion of the produced Newton/G pair to the historical
lane-major compact ABI [H,scale,inverseDiagonal,inverseH,G]. -/
namespace ExactFourierCircuits.DFTModelCacheCompact
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Input := DFTModelCacheKernelBanks.Output
abbrev Cell := p Input w

def count : Prog false Input w :=
  .comp (.fork (.comp (.atom .fst) (.atom .len)) (.atom (.lit 5))) (.atom (.int .mul))
def width : Prog false Cell w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .len))
def indexOp (op : NOp) : Prog false Cell w :=
  .comp (.fork (.atom .snd) width) (.atom (.int op))
def row : Prog false Cell DFTModelCacheForest.Row :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (indexOp .mod)) (.atom .look)
def H : Prog false Cell sc := .comp row (.atom .fst)
def scale : Prog false Cell sc := .comp row (.comp (.atom .snd) (.atom .fst))
def inverseH : Prog false Cell sc :=
  .comp row (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def inverseDiagonal : Prog false Cell sc :=
  .comp row (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))))
def G : Prog false Cell sc :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (indexOp .mod)) (.atom .look)
def fields : List (Prog false Cell sc) := [H,scale,inverseDiagonal,inverseH]
def cell : Prog false Cell sc :=
  .comp (.fork (.atom .id) (indexOp .div)) (DFTModelCacheLiteral.choose G fields)
def program : Prog false Input (Ty.a sc) := .tab count cell

theorem count_run (v : Input.T) : run count v=⟨5*v.1.len,7,max (max v.1.len 5) (5*v.1.len),True⟩ := by
  simp [count,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Nat.mul_comm]

theorem width_run (v : Input.T) (i : ℕ) : run width (v,i)=⟨v.1.len,5,v.1.len,True⟩ := by
  simp [width,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem index_run (op : NOp) (v : Input.T) (i : ℕ) :
    run (indexOp op) (v,i)=⟨(op.run (i,v.1.len)).val,9,max v.1.len ((op.run (i,v.1.len)).val),True⟩ := by
  cases op <;> simp [indexOp,width,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem row_run (v : Input.T) (i : ℕ) : run row (v,i)=
    ⟨v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank,15,max v.1.len (i%v.1.len),True⟩ := by
  simp [row,indexOp,width,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

def expected (v : Input.T) (i : ℕ) : ℂ :=
  let q:=i/v.1.len
  let z:=v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank
  if q=0 then z.1 else if q=1 then z.2.1 else
  if q=2 then z.2.2.2.2 else if q=3 then z.2.2.1 else v.2.look (i%v.1.len) 0

theorem fields_run (v : Input.T) (i : ℕ) :
    run H (v,i)=⟨(v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank).1,17,max v.1.len (i%v.1.len),True⟩ ∧
    run scale (v,i)=⟨(v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank).2.1,19,max v.1.len (i%v.1.len),True⟩ ∧
    run inverseDiagonal (v,i)=⟨(v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank).2.2.2.2,23,max v.1.len (i%v.1.len),True⟩ ∧
    run inverseH (v,i)=⟨(v.1.look (i%v.1.len) DFTModelCacheForest.Row.blank).2.2.1,21,max v.1.len (i%v.1.len),True⟩ ∧
    run G (v,i)=⟨v.2.look (i%v.1.len) 0,15,max v.1.len (i%v.1.len),True⟩ := by
  simp [H,scale,inverseDiagonal,inverseH,G,row,indexOp,width,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

attribute [local irreducible] H scale inverseDiagonal inverseH G

theorem cell_value (v : Input.T) (i : ℕ) : (run cell (v,i)).val=expected v i := by
  change (run (DFTModelCacheLiteral.choose G fields) ((v,i),i/v.1.len)).val=_
  rw [DFTModelCacheLiteral.choose_value]
  have hs:=fields_run v i
  by_cases h0:i/v.1.len=0
  · simpa [fields,expected,h0] using congrArg Bill.val hs.1
  by_cases h1:i/v.1.len=1
  · simpa [fields,expected,h0,h1] using congrArg Bill.val hs.2.1
  by_cases h2:i/v.1.len=2
  · simpa [fields,expected,h0,h1,h2] using congrArg Bill.val hs.2.2.1
  by_cases h3:i/v.1.len=3
  · simpa [fields,expected,h0,h1,h2,h3] using congrArg Bill.val hs.2.2.2.1
  have bound : ∀k : ℕ,k≠0→k≠1→k≠2→k≠3→4≤k := by
    intro k h0 h1 h2 h3;omega
  have h4 : 4 ≤ (i/v.1.len):=bound _ h0 h1 h2 h3
  have hl : fields.length ≤ (i/v.1.len):=by simpa [fields] using h4
  rw [List.getElem?_eq_none hl]
  simpa [expected,h0,h1,h2,h3] using congrArg Bill.val hs.2.2.2.2

theorem cell_valid (v : Input.T) (i : ℕ) : (run cell (v,i)).valid := by
  rw [cell,comp_run,fork_run,index_run]
  simp only [atom_run,Atom.run,NOp.run,Bill.one,Bill.pass,Bill.pay,true_and]
  apply DFTModelCacheLiteral.choose_valid G fields (v,i) _
  · exact (congrArg Bill.valid (fields_run v i).2.2.2.2).mpr trivial
  · intro f hf
    simp [fields] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · rw [(fields_run v i).1];trivial
    · rw [(fields_run v i).2.1];trivial
    · rw [(fields_run v i).2.2.1];trivial
    · rw [(fields_run v i).2.2.2.1];trivial

end
end ExactFourierCircuits.DFTModelCacheCompact
