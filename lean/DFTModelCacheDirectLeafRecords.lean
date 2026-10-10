import DFTModelCacheTraversalWordBound
import UniformDirectLeafCacheChronology

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.1–3.5, pp.13–18: direct lower Toeplitz leaves. The four fields
are exactly those printed by the native 82-instruction orientations caller.
The coefficient base is retained independently of the subtree offset. -/
namespace ExactFourierCircuits.DFTModelCacheDirectLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Record4 := p w (p w (p w w))
abbrev Input := p w (p w w)
abbrev RowInput := p (p w w) w
abbrev CellInput := p RowInput w

def encode (q : UniformTransposeDescriptorMachine.Record) : Record4.T :=
  (q.kind,(q.dest,(q.source,q.coefficient)))
def rowRecords (i o K : ℕ) : List UniformTransposeDescriptorMachine.Record :=
  ⟨0,o+i,o+i,K⟩ :: List.ofFn (fun j : Fin i=>⟨1,o+i,o+j.val,K+(i-j.val)⟩)
def records (o K : ℕ) : ℕ→List UniformTransposeDescriptorMachine.Record
  | 0=>[]
  | i+1=>rowRecords i o K++records o K i

theorem partial_records {v : ℕ} (o K k : ℕ) (hk : k≤v) :
    (UniformDirectToeplitz.partialTopology k hk).map
      (UniformTransposeDescriptorMachine.ofOperation o K)=records o K k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    simp only [UniformDirectToeplitz.partialTopology,List.map_append,ih]
    congr 1
    simp [UniformDirectToeplitz.rowTopology,UniformTransposeDescriptorMachine.ofOperation,
      rowRecords,List.map_ofFn,Function.comp_def]

theorem records_native (v o K : ℕ) :
    records o K v=UniformTransposeDescriptorMachine.leafRecords v o K :=
  (partial_records o K v (le_refl _)).symm
theorem records_length (v o K : ℕ) : (records o K v).length=v+v*(v-1)/2 := by
  rw [records_native,UniformTransposeDescriptorMachine.leafRecords_length]
theorem records_length_bound (v o K : ℕ) : (records o K v).length≤(v+1)^2 := by
  rw [records_length]
  have h:=Nat.div_le_self (v*(v-1)) 2
  have h':=Nat.sub_le v 1
  nlinarith

def integer {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def cellO : Prog false CellInput w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def cellK : Prog false CellInput w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def cellI : Prog false CellInput w := .comp (.atom .fst) (.atom .snd)
def cellJ : Prog false CellInput w := integer .sub (.atom .snd) (.atom (.lit 1))
def cellDest : Prog false CellInput w := integer .add cellO cellI
def scaleCell : Prog false CellInput Record4 :=
  .fork (.atom (.lit 0)) (.fork cellDest (.fork cellDest cellK))
def shearCell : Prog false CellInput Record4 :=
  .fork (.atom (.lit 1)) (.fork cellDest
    (.fork (integer .add cellO cellJ) (integer .add cellK (integer .sub cellI cellJ))))
def rowCell : Prog false CellInput Record4 := .ifz (.atom .snd) scaleCell shearCell
def row : Prog false RowInput (Ty.a Record4) :=
  .tab (integer .add (.atom .snd) (.atom (.lit 1))) rowCell

theorem rowCell_run (o K i j : ℕ) :
    run rowCell (((o,K),i),j)=
      ⟨encode (if j=0 then ⟨0,o+i,o+i,K⟩ else
        ⟨1,o+i,o+(j-1),K+(i-(j-1))⟩),
        if j=0 then 33 else 49,
        if j=0 then max (o+i) 0 else
          max (o+i) (max (o+(j-1)) (max 1 (max (j-1) (K+(i-(j-1)))))),True⟩ := by
  by_cases h:j=0 <;> simp [rowCell,scaleCell,shearCell,cellDest,cellO,cellK,cellI,cellJ,
    integer,encode,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,h]

theorem row_run (o K i : ℕ) :
    run row ((o,K),i)=
      (Bill.tab (i+1) Record4.blank (fun j=>run rowCell (((o,K),i),j))).pay 6 (i+1) := by
  simp [row,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem row_value (o K i : ℕ) :
    (run row ((o,K),i)).val=DFTModelCacheTraversal.ofList ((rowRecords i o K).map encode) := by
  change (Bill.tab (i+1) Record4.blank (fun j=>run rowCell (((o,K),i),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  have list : List.ofFn (fun j : Fin (i+1)=>(run rowCell (((o,K),i),j.val)).val)=
      (rowRecords i o K).map encode := by
    rw [List.ofFn_succ]
    simp only [rowRecords,List.map_cons,List.map_ofFn]
    apply congrArg₂ List.cons
    · exact congrArg Bill.val (rowCell_run o K i 0)
    · rfl
  rw [←list]
  exact (DFTModelCacheDescriptor.listTape_ofFn _).symm

theorem row_valid (o K i : ℕ) : (run row ((o,K),i)).valid := by
  rw [row_run]
  change (Bill.tab (i+1) Record4.blank (fun j=>run rowCell (((o,K),i),j))).valid
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    (fun j _=>by rw[rowCell_run];trivial)

theorem row_work (o K i : ℕ) : (run row ((o,K),i)).work≤100*(i+1)+20 := by
  rw [row_run]
  change (Bill.tab (i+1) Record4.blank (fun j=>run rowCell (((o,K),i),j))).work+6≤_
  rw [ModelEquivalenceInterpreter.tab_work]
  have bound : (∑j∈Finset.range (i+1),(run rowCell (((o,K),i),j)).work)≤68*(i+1) := by
    calc
      _≤∑_j∈Finset.range (i+1),68 := Finset.sum_le_sum (fun j _=>by
        rw[rowCell_run];change (if j=0 then 33 else 49)≤68;split_ifs <;> omega)
      _=_:=by simp [Nat.mul_comm]
  omega

theorem row_peak (o K i : ℕ) : (run row ((o,K),i)).peak≤o+K+i+1 := by
  rw [row_run]
  change max (Bill.tab (i+1) Record4.blank
    (fun j=>run rowCell (((o,K),i),j))).peak (i+1)≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  apply max_le
  · apply max_le (by omega)
    apply Finset.sup_le
    intro j hj
    have hj' : j < i+1:=Finset.mem_range.mp hj
    rw[rowCell_run]
    change (if j=0 then _ else _)≤_
    split_ifs <;> simp only [max_le_iff] <;> omega
  · omega

end
end ExactFourierCircuits.DFTModelCacheDirectLeaf
