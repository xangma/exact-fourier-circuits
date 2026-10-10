import DFTModelCacheDirectLeafBounds
import DFTModelCacheForestInverseH

set_option autoImplicit false

/-! Direct-leaf coefficient extraction from genuinely computed inverse-H banks.
The coefficient base is an address label; the subtree offset never shifts H.
No nine-lane matching factors or calendar entries are produced here. -/
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelCacheForest.prepareInverseH
  DFTModelCacheDirectLeaf.orientations

abbrev Banks := p (Ty.a sc) (Ty.a sc)
abbrev Pairs := Ty.a (p sc sc)
abbrev AnnotateInput := p (p w Banks) (Ty.a DFTModelCacheDirectLeaf.Record4)
abbrev AnnotateCell := p AnnotateInput w
abbrev Input := p (p w sc) DFTModelCacheDirectLeaf.Input
abbrev Seed := p Input (p Banks DFTModelCacheDirectLeaf.Orientations)
abbrev Output := p Banks (p DFTModelCacheDirectLeaf.Orientations (p Pairs Pairs))

def record : Prog false AnnotateCell DFTModelCacheDirectLeaf.Record4 :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look)
def coefficient : Prog false AnnotateCell w :=
  .comp record (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def coefficientBase : Prog false AnnotateCell w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def index : Prog false AnnotateCell w :=
  .comp (.fork coefficient coefficientBase) (.atom (.int .sub))
def bank (conjugate : Bool) : Prog false AnnotateCell (Ty.a sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .snd)
    (if conjugate then .atom .snd else .atom .fst)))
def scalar (conjugate : Bool) : Prog false AnnotateCell sc :=
  .comp (.fork (bank conjugate) index) (.atom .look)
def pair : Prog false AnnotateCell (p sc sc) := .fork (scalar false) (scalar true)
def annotate : Prog false AnnotateInput Pairs :=
  .tab (.comp (.atom .snd) (.atom .len)) pair

def inverseRoot : Prog false (p w sc) (p w sc) :=
  .fork (.atom .fst) (.comp (.atom .snd) (.atom .inv))
def banks : Prog false (p w sc) Banks :=
  .fork DFTModelCacheForest.prepareInverseH
    (.comp inverseRoot DFTModelCacheForest.prepareInverseH)
def setup : Prog false Input Seed :=
  .fork (.atom .id) (.fork (.comp (.atom .fst) banks)
    (.comp (.atom .snd) DFTModelCacheDirectLeaf.orientations))
def seedBanks : Prog false Seed Banks := .comp (.atom .snd) (.atom .fst)
def seedRecords : Prog false Seed DFTModelCacheDirectLeaf.Orientations :=
  .comp (.atom .snd) (.atom .snd)
def seedBase : Prog false Seed w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def annotateArgument (transposed : Bool) : Prog false Seed AnnotateInput :=
  .fork (.fork seedBase seedBanks)
    (.comp seedRecords (if transposed then .atom .snd else .atom .fst))
def body : Prog false Seed Output :=
  .fork seedBanks (.fork seedRecords
    (.fork (.comp (annotateArgument false) annotate) (.comp (annotateArgument true) annotate)))
def program : Prog false Input Output := .comp setup body

theorem pair_run (K i : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T) :
    run pair (((K,(h,hc)),rs),i)=
      ⟨(h.look ((rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K) 0,
        hc.look ((rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K) 0),
        63,(rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K,True⟩ := by
  simp [pair,scalar,bank,index,coefficient,coefficientBase,record,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem annotate_run (K : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T) :
    run annotate ((K,(h,hc)),rs)=
      (Bill.tab rs.len (p sc sc).blank (fun i=>run pair (((K,(h,hc)),rs),i))).pay 4 rs.len := by
  simp [annotate,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem annotate_value (K : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run annotate ((K,(h,hc)),rs)).val=Tape.tab rs.len (fun i=>
      (h.look ((rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K) 0,
        hc.look ((rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K) 0)) := by
  rw [annotate_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply congrArg (Tape.tab rs.len)
  funext i
  exact congrArg Bill.val (pair_run K i h hc rs)

theorem annotate_valid (K : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run annotate ((K,(h,hc)),rs)).valid := by
  rw [annotate_run]
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).mpr (fun i _=>by rw [pair_run];trivial)

theorem annotate_work (K : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run annotate ((K,(h,hc)),rs)).work=6+67*rs.len := by
  rw [annotate_run]
  change (Bill.tab _ _ _).work+4=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum : (∑i∈Finset.range rs.len,(run pair (((K,(h,hc)),rs),i)).work)=63*rs.len := by
    trans ∑_i∈Finset.range rs.len,63
    · apply Finset.sum_congr rfl
      intro i _
      exact congrArg Bill.work (pair_run K i h hc rs)
    · simp [Nat.mul_comm]
  rw [sum]
  omega

theorem annotate_peak (K B : ℕ) (h hc : Tape ℂ) (rs : Tape DFTModelCacheDirectLeaf.Record4.T)
    (length : rs.len≤B)
    (indices : ∀i,i<rs.len→(rs.look i DFTModelCacheDirectLeaf.Record4.blank).2.2.2-K≤B) :
    (run annotate ((K,(h,hc)),rs)).peak≤B := by
  rw [annotate_run]
  change max (Bill.tab _ _ _).peak rs.len≤B
  rw [ModelEquivalenceInterpreter.tab_peak]
  refine max_le (max_le length ?_) length
  apply Finset.sup_le
  intro i hi
  rw [pair_run]
  exact indices i (Finset.mem_range.mp hi)

theorem inverseRoot_run (r : ℕ) (omega : ℂ) :
    run inverseRoot (r,omega)=⟨(r,omega⁻¹),5,0,omega≠0⟩ := by
  simp [inverseRoot,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem banks_run (r : ℕ) (omega : ℂ) : run banks (r,omega)=
    ⟨((run DFTModelCacheForest.prepareInverseH (r,omega)).val,
      (run DFTModelCacheForest.prepareInverseH (r,omega⁻¹)).val),
      (run DFTModelCacheForest.prepareInverseH (r,omega)).work+
        (run DFTModelCacheForest.prepareInverseH (r,omega⁻¹)).work+7,
      max (run DFTModelCacheForest.prepareInverseH (r,omega)).peak
        (run DFTModelCacheForest.prepareInverseH (r,omega⁻¹)).peak,
      (run DFTModelCacheForest.prepareInverseH (r,omega)).valid ∧
        ((omega≠0 ∧ (run DFTModelCacheForest.prepareInverseH (r,omega⁻¹)).valid) ∧ True)⟩ := by
  rw [banks,fork_run,comp_run,inverseRoot_run]
  simp [Bill.pass,Bill.pay,Bill.one]
  omega

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients
