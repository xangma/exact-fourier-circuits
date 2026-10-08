import UniformMultiAxisSectorMetadataPreparation
import UniformMatchingAxisTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisMatchingTablePreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
open UniformAllAxisSeedPreparation (axisCount)
namespace A
abbrev Edge := UniformColoring.Edge
end A

/-- Readonly3240=edge directory,3241=permutation pool,3242=width pool,
3243=shared markers,3244=output four-word rows. Only3245..3254 are driver scratch. -/
def boot : List Op := [.literal 3247 0,.literal 3248 1,.literal 3249 2,.literal 3250 4,
 .add 3245 102 3248,.literal 3246 0]
def setup : List Op := [.mul 3251 3246 3250,.add 3252 102 3251,.add 3252 105 3252,.getNat 840 3252,
 .mul 3253 3246 3249,.add 3253 3240 3253,.getNat 841 3253,.add 3253 3253 3248,.getNat 842 3253,
 .mul 3254 3246 103,.add 843 3241 3254,.add 844 3242 3254,.add 845 3243 3247,.add 846 3244 3251]
def program : Program := boot.map Op.code++[.branchLT 3246 3245 7 78]++setup.map Op.code++
 UniformMatchingAxisTableMachine.program.map (relocate 21 76)++
 [.natBinary .add 3246 3246 3248,.jump 6,.halt]
lemma boot_length : boot.length=6 :=rfl
lemma setup_length : setup.length=14 :=rfl
lemma program_length : program.length=79 :=by
 simp only [program,List.length_append,List.length_map,boot_length,setup_length,
  UniformMatchingAxisTableMachine.program_length];rfl
lemma boot_code : BlockAt boot program 0 :=by intro i hi;change i < 6 at hi;interval_cases i <;>rfl
lemma setup_code : BlockAt setup program 7 :=by intro i hi;change i < 14 at hi;interval_cases i <;>rfl
lemma axis_code : CodeAt UniformMatchingAxisTableMachine.program program 21 76 :=by
 exact UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 3246 3245 7 78]++setup.map Op.code)
  [.natBinary .add 3246 3246 3248,.jump 6,.halt] _ 21 76 (by
   simp only [List.length_append,List.length_map,boot_length,setup_length];rfl)
lemma branch_at : program[6]?=some (.branchLT 3246 3245 7 78) :=rfl
lemma advance_at : program[76]?=some (.natBinary .add 3246 3246 3248) :=by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,boot_length,
  setup_length,UniformMatchingAxisTableMachine.program_length,List.length_singleton];omega)]
 simp only [List.length_append,List.length_map,boot_length,setup_length,
  UniformMatchingAxisTableMachine.program_length,List.length_singleton];rfl
lemma jump_at : program[77]?=some (.jump 6) :=by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,boot_length,
  setup_length,UniformMatchingAxisTableMachine.program_length,List.length_singleton];omega)]
 simp only [List.length_append,List.length_map,boot_length,setup_length,
  UniformMatchingAxisTableMachine.program_length,List.length_singleton];rfl
lemma halt_at : program[78]?=some .halt :=by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,boot_length,
  setup_length,UniformMatchingAxisTableMachine.program_length,List.length_singleton];omega)]
 simp only [List.length_append,List.length_map,boot_length,setup_length,
  UniformMatchingAxisTableMachine.program_length,List.length_singleton];rfl

noncomputable section
structure Family (n:ℕ) where
 count : Fin (axisCount n) → ℕ
 source : Fin (axisCount n) → ℕ
 edges : (j:Fin (axisCount n)) → Fin (count j) → A.Edge
 matching : ∀j,UniformMatchingAxisTableMachine.Matching (edges j)
 range : ∀j,UniformMatchingAxisTableMachine.InRange (UniformSelectedCRT.radices n j) (edges j)

def Source {n:ℕ} (f:Family n) (d:ℕ) (s:State):Prop :=∀j,
 s.natHeap (d+2*j.val)=some (f.count j) ∧s.natHeap (d+2*j.val+1)=some (f.source j) ∧
 UniformMatchingAxisTableMachine.Edges (f.edges j) (f.source j) s
structure Layout (n:ℕ) (f:Family n) where
 directory : ℕ
 permutations : ℕ
 widths : ℕ
 markers : ℕ
 rows : ℕ
 B : ℕ
 sourceBelow : ∀j,f.source j+3*f.count j ≤ permutations
 directoryBelow : directory+2*axisCount n ≤ permutations
 protectedBelow : copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n) ≤ permutations
 permutationsBelow : permutations+len n*axisCount n ≤ widths
 widthsBelow : widths+len n*axisCount n ≤ markers
 markersBelow : markers+len n ≤ rows
 rowsBound : rows+4*axisCount n ≤ B
 code : 79 ≤ B
structure Header {n:ℕ} {f:Family n} (l:Layout n f) (s:State):Prop where
 directory : s.natReg 3240=l.directory
 permutations : s.natReg 3241=l.permutations
 widths : s.natReg 3242=l.widths
 markers : s.natReg 3243=l.markers
 rows : s.natReg 3244=l.rows
structure Driver {n:ℕ} {f:Family n} (l:Layout n f) (j:ℕ) (s:State):Prop where
 header : Header l s
 count : s.natReg 3245=axisCount n
 index : s.natReg 3246=j
 zero : s.natReg 3247=0
 one : s.natReg 3248=1
 two : s.natReg 3249=2
 four : s.natReg 3250=4

def Retention (s u:State):Prop := u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 ∀i,(i < 840 ∨ 847 ≤ i) → (i < 850 ∨ 862 ≤ i) →
  (i < 3245 ∨ 3255 ≤ i) →u.natReg i=s.natReg i
lemma Retention.refl (s:State):Retention s s :=⟨rfl,rfl,rfl,rfl,fun _ _ _ _=>rfl⟩
lemma Retention.trans {s u v:State} (h:Retention s u) (k:Retention u v):Retention s v :=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.1.trans h.2.2.2.1,
 fun i hi hj hk=>(k.2.2.2.2 i hi hj hk).trans (h.2.2.2.2 i hi hj hk)⟩
lemma Retention.metadataFrame {s u:State} (h:Retention s u):
 UniformMultiAxisSectorMetadataPreparation.Retention s u :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i hi hj=>h.2.2.2.2 i (by omega) (by omega) (by omega)⟩
lemma boot_retention (s:State):Retention s (applyBlock boot s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i _ _ hi
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma setup_retention (s:State):Retention s (applyBlock setup s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i hi _ hj
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma axis_retention {s u:State} (h:UniformMatchingAxisTableMachine.Frame s u):Retention s u :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i _ hi _=>h.2.2.2.2 i hi⟩
lemma Driver.withPC {n j pc:ℕ} {f:Family n} {l:Layout n f} {s:State} (h:Driver l j s):
 Driver l j (setPC s pc) :=
 ⟨⟨h.header.directory,h.header.permutations,h.header.widths,h.header.markers,h.header.rows⟩,
  h.count,h.index,h.zero,h.one,h.two,h.four⟩
lemma boot_driver {n:ℕ} {f:Family n} (l:Layout n f) (s:State) (hm:Metadata n s) (hh:Header l s):
 Driver l 0 (applyBlock boot s) :=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,hh.directory,hh.permutations,
    hh.widths,hh.markers,hh.rows]
 · simp [boot,applyBlock,Op.apply,writeNat,next,hm.saved.count]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · simp [boot,applyBlock,Op.apply,writeNat,next]


lemma root_cell {n:ℕ} (j:Fin (axisCount n)) (s:State) (h:Metadata n s):
 s.natHeap (copyBase n+ell n+4*j.val)=some (UniformSelectedCRT.radices n j) :=by
 simpa only [UniformInitialPreparation.protectedView,UniformCRTHeaderMachine.tableAddress,Nat.add_zero,
  Nat.add_assoc] using (h.crt j).1
lemma slot_bounds {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)):
 f.source j+3*f.count j ≤ l.permutations+j.val*len n ∧
 l.permutations+j.val*len n+UniformSelectedCRT.radices n j ≤ l.widths+j.val*len n ∧
 l.widths+j.val*len n+UniformSelectedCRT.radices n j ≤ l.markers ∧
 l.markers+UniformSelectedCRT.radices n j ≤ l.rows+4*j.val ∧
 l.rows+4*j.val+4 ≤ l.B :=by
 have radixBound:UniformSelectedCRT.radices n j ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n j
 have jl:=j.isLt
 have off:j.val*len n+len n ≤ len n*axisCount n:=by
  simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_comm] using
   Nat.mul_le_mul_right (len n) (show j.val+1 ≤ axisCount n by omega)
 have t:=l.sourceBelow j;have p:=l.permutationsBelow;have w:=l.widthsBelow
 have u:=l.markersBelow;have a:=l.rowsBound
 exact ⟨by omega,by omega,by omega,by omega,by omega⟩
lemma setup_header {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)) (s:State)
 (hm:Metadata n s) (h:Driver l j.val s) (src:Source f l.directory s):
 UniformMatchingAxisTableMachine.Header (UniformSelectedCRT.radices n j) (f.count j) (f.source j)
  (l.permutations+j.val*len n) (l.widths+j.val*len n) l.markers (l.rows+4*j.val)
  (applyBlock setup s) :=by
 have root:=root_cell j s hm
 have row:=src j
 have root':s.natHeap (UniformGlobalNatPreparation.destination (ell n) (len n)+(ell n+j.val*4))=
  some (UniformSelectedCRT.radices n j):=by
  simpa only [UniformInitialPreparation.copyBase,Nat.add_assoc,Nat.mul_comm] using root
 have row0:s.natHeap (l.directory+j.val*2)=some (f.count j):=by
  simpa only [Nat.mul_comm] using row.1
 have row1:s.natHeap (l.directory+(j.val*2+1))=some (f.source j):=by
  simpa only [Nat.mul_comm,Nat.add_assoc] using row.2.1
 constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,
  h.index,h.zero,h.one,h.two,h.four,h.header.directory,h.header.permutations,
  h.header.widths,h.header.markers,h.header.rows,hm.saved.count,hm.saved.workingLength,
  hm.saved.copyAddress,Nat.add_assoc,root',row0,row1]
 all_goals omega
lemma setup_driver {n:ℕ} {f:Family n} (l:Layout n f) (j:ℕ) (s:State) (h:Driver l j s):
 Driver l j (applyBlock setup s) :=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h.header.directory,h.header.permutations,
    h.header.widths,h.header.markers,h.header.rows]
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.count
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.index
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.zero
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.one
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.two
 · simpa [setup,applyBlock,Op.apply,writeNat,next] using h.four


lemma setup_safe {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)) (s:State)
 (hm:Metadata n s) (h:Driver l j.val s) (src:Source f l.directory s):
 readable setup s ∧peak setup s ≤ l.B :=by
 have root:=root_cell j s hm
 have row:=src j
 have root':s.natHeap (UniformGlobalNatPreparation.destination (ell n) (len n)+(ell n+j.val*4))=
  some (UniformSelectedCRT.radices n j):=by
  simpa only [UniformInitialPreparation.copyBase,Nat.add_assoc,Nat.mul_comm] using root
 have row0:s.natHeap (l.directory+j.val*2)=some (f.count j):=by
  simpa only [Nat.mul_comm] using row.1
 have row1:s.natHeap (l.directory+(j.val*2+1))=some (f.source j):=by
  simpa only [Nat.mul_comm,Nat.add_assoc] using row.2.1
 have rbound:UniformSelectedCRT.radices n j ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n j
 have capacity:=UniformMatchingAxisTableMachine.matching_capacity
  (UniformSelectedCRT.radices n j) (f.edges j) (f.matching j) (f.range j)
 have slot:=slot_bounds l j
 have off:j.val*len n+len n ≤ len n*axisCount n:=by
  simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_comm] using
   Nat.mul_le_mul_right (len n) (show j.val+1 ≤ axisCount n by omega)
 have jl:=j.isLt;have db:=l.directoryBelow;have pb:=l.permutationsBelow
 have wb:=l.widthsBelow;have mb:=l.markersBelow;have ab:=l.rowsBound;have code:=l.code
 have protectedBound:=l.protectedBelow
 unfold UniformGlobalNatPreparation.amount UniformInitialPreparation.copyBase at protectedBound
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.index,h.zero,h.one,h.two,h.four,h.header.directory,h.header.permutations,
  h.header.widths,h.header.markers,h.header.rows,hm.saved.count,hm.saved.workingLength,
  hm.saved.copyAddress,Nat.add_assoc,root',row0,row1]
 omega

/-- The shared marker workspace is reused. Every new bank and four-word row
has disjoint physical addresses from all previously completed axes. -/
def Complete {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)) (s:State):Prop :=
 UniformMatchingAxisTableMachine.Bank (l.permutations+j.val*len n)
  (UniformMatchingAxisTableMachine.ordered (UniformSelectedCRT.radices n j) (f.edges j)) s ∧
 UniformMatchingAxisTableMachine.Bank (l.widths+j.val*len n)
  (UniformMatchingAxisTableMachine.widths (UniformSelectedCRT.radices n j) (f.count j)) s ∧
 UniformMatchingAxisTableMachine.AxisRow (l.rows+4*j.val)
  (UniformSelectedCRT.radices n j) (f.count j) (l.widths+j.val*len n) (l.permutations+j.val*len n) s
lemma complete_transfer {n:ℕ} {f:Family n} (l:Layout n f) (i j:Fin (axisCount n))
 (s u:State) (h:Complete l i s) (ij:i.val < j.val)
 (out:UniformMatchingAxisTableMachine.Outside (l.permutations+j.val*len n)
  (l.widths+j.val*len n) l.markers (l.rows+4*j.val) (UniformSelectedCRT.radices n j) s u):
 Complete l i u :=by
 have rb:UniformSelectedCRT.radices n i ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n i
 have rbj:UniformSelectedCRT.radices n j ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n j
 have jmax:j.val*len n+len n ≤ len n*axisCount n:=by
  simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_comm] using
   Nat.mul_le_mul_right (len n) (show j.val+1 ≤ axisCount n by have h:=j.isLt;omega)
 have off:i.val*len n+len n ≤ j.val*len n:=by
  simpa only [Nat.add_mul,Nat.one_mul] using
   Nat.mul_le_mul_right (len n) (show i.val+1 ≤ j.val by omega)
 have p:=l.permutationsBelow;have w:=l.widthsBelow;have a:=l.markersBelow
 have pmax:i.val*len n+len n ≤ len n*axisCount n:=by
  simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_comm] using
   Nat.mul_le_mul_right (len n) (show i.val+1 ≤ axisCount n by have h:=i.isLt;omega)
 refine ⟨?_,?_,?_⟩
 · intro k hk
   have original:=hk
   have ord:=UniformMatchingAxisTableMachine.ordered_length (UniformSelectedCRT.radices n i)
    (f.edges i) (f.matching i) (f.range i)
   rw [ord] at hk
   rw [out _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
   exact h.1 k original
 · intro k hk
   have original:=hk
   have cap:=UniformMatchingAxisTableMachine.matching_capacity (UniformSelectedCRT.radices n i)
    (f.edges i) (f.matching i) (f.range i)
   have wl:=UniformMatchingAxisTableMachine.widths_length (UniformSelectedCRT.radices n i) (f.count i) cap
   rw [wl] at hk
   rw [out _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
   exact h.2.1 k original
 · rcases h.2.2 with ⟨h0,h1,h2,h3⟩
   refine ⟨?_,?_,?_,?_⟩
   all_goals rw [out _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
   · exact h0
   · exact h1
   · exact h2
   · exact h3


lemma source_transfer {n:ℕ} {f:Family n} (l:Layout n f) (s u:State) (src:Source f l.directory s)
 (low:∀t,t < l.permutations → u.natHeap t=s.natHeap t):Source f l.directory u :=by
 intro j
 have jl:=j.isLt;have db:=l.directoryBelow;have sb:=l.sourceBelow j
 refine ⟨(low _ (by omega)).trans (src j).1,(low _ (by omega)).trans (src j).2.1,?_⟩
 intro i
 have il:=i.isLt
 exact ⟨(low _ (by omega)).trans ((src j).2.2 i).1,
  (low _ (by omega)).trans ((src j).2.2 i).2⟩
lemma axis_prefix {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)) (s u:State)
 (out:UniformMatchingAxisTableMachine.Outside (l.permutations+j.val*len n)
  (l.widths+j.val*len n) l.markers (l.rows+4*j.val) (UniformSelectedCRT.radices n j) s u):
 ∀t,t < l.permutations → u.natHeap t=s.natHeap t :=by
 intro t ht
 have p:=l.permutationsBelow;have w:=l.widthsBelow;have a:=l.markersBelow
 exact out t (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
structure Invariant {n:ℕ} {f:Family n} (l:Layout n f) (j:ℕ) (s:State):Prop where
 driver : Driver l j s
 metadata : Metadata n s
 source : Source f l.directory s
 completed : ∀i:Fin (axisCount n),i.val < j → Complete l i s


lemma Driver.axis {n j:ℕ} {f:Family n} {l:Layout n f} {s u:State}
 (d:Driver l j s) (fr:UniformMatchingAxisTableMachine.Frame s u):Driver l j u :=
 ⟨⟨(fr.2.2.2.2 _ (by omega)).trans d.header.directory,
   (fr.2.2.2.2 _ (by omega)).trans d.header.permutations,
   (fr.2.2.2.2 _ (by omega)).trans d.header.widths,
   (fr.2.2.2.2 _ (by omega)).trans d.header.markers,
   (fr.2.2.2.2 _ (by omega)).trans d.header.rows⟩,
  (fr.2.2.2.2 _ (by omega)).trans d.count,(fr.2.2.2.2 _ (by omega)).trans d.index,
  (fr.2.2.2.2 _ (by omega)).trans d.zero,(fr.2.2.2.2 _ (by omega)).trans d.one,
  (fr.2.2.2.2 _ (by omega)).trans d.two,(fr.2.2.2.2 _ (by omega)).trans d.four⟩
structure Printed {n:ℕ} {f:Family n} (l:Layout n f) (j:ℕ) (s:State):Prop where
 driver : Driver l j s
 metadata : Metadata n s
 source : Source f l.directory s
 completed : ∀i:Fin (axisCount n),i.val < j+1 → Complete l i s


lemma Invariant.withPC {n j pc:ℕ} {f:Family n} {l:Layout n f} {s:State} (h:Invariant l j s):
 Invariant l j (setPC s pc) :=by
 refine ⟨h.driver.withPC,?_,h.source,h.completed⟩
 exact UniformMultiAxisSectorMetadataPreparation.retained_metadata h.metadata
  (Retention.refl s).metadataFrame l.permutations l.protectedBelow (fun _ _=>rfl)
lemma setup_invariant {n j:ℕ} {f:Family n} (l:Layout n f) (s:State) (h:Invariant l j s):
 Invariant l j (applyBlock setup s) :=by
 refine ⟨setup_driver l j s h.driver,?_,h.source,h.completed⟩
 exact UniformMultiAxisSectorMetadataPreparation.retained_metadata h.metadata
  (setup_retention s).metadataFrame l.permutations l.protectedBelow (fun _ _=>rfl)

/-- Opaque-state boundary for the actual placed55 helper. The caller proves
these literal headers by charged setup; no generated bank/action is an input. -/
theorem print_prepared {n:ℕ} {f:Family n} (l:Layout n f) (j:Fin (axisCount n)) (x:Fin n → ℂ)
 (s:State) (inv:Invariant l j.val s)
 (header:UniformMatchingAxisTableMachine.Header (UniformSelectedCRT.radices n j) (f.count j) (f.source j)
  (l.permutations+j.val*len n) (l.widths+j.val*len n) l.markers (l.rows+4*j.val) s)
 (pc:s.pc=21) (wb:WordBound l.B s):∃u,
 BoundedRuns program n x l.B s
  (UniformMatchingAxisTableMachine.runtime (UniformSelectedCRT.radices n j) (f.count j)) u ∧
 Printed l j.val u ∧u.pc=76 ∧Retention s u ∧
 (∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 have code:=l.code
 let ready:=setPC s 0
 have rb:=changePC_bound l.B s 0 wb (by omega)
 have slots:=slot_bounds l j
 obtain ⟨v,run,_vpc,_header,wp,ww,_markers,row,_edges,out,frame⟩:=
  UniformMatchingAxisTableMachine.execution (UniformSelectedCRT.radices n j) (f.count j) (f.source j)
   (l.permutations+j.val*len n) (l.widths+j.val*len n) l.markers (l.rows+4*j.val) l.B n x (f.edges j) ready
   ⟨header.radix,header.count,header.source,header.permutation,header.widths,header.markers,header.row⟩
   rfl (inv.source j).2.2 (f.matching j) (f.range j)
   slots.1 slots.2.1 slots.2.2.1 slots.2.2.2.1 slots.2.2.2.2 (by omega) rb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed axis_code
  (by rw [UniformMatchingAxisTableMachine.program_length];omega) (by omega) run
 rw [show placed 21 ready=s from UniformMultiAxisSectorMetadataPreparation.placed_zero s 21 pc] at placedRun
 let u:=setPC v 76
 have driver:Driver l j.val u:=(inv.driver.withPC.axis frame).withPC
 have fullFrame:Retention s u:=axis_retention frame
 have low:∀t,t < l.permutations → u.natHeap t=s.natHeap t:=axis_prefix l j ready u out
 have metadata:Metadata n u:=UniformMultiAxisSectorMetadataPreparation.retained_metadata inv.metadata
  fullFrame.metadataFrame l.permutations l.protectedBelow low
 have completed:∀i:Fin (axisCount n),i.val < j.val+1 → Complete l i u:=by
  intro i hi
  by_cases eq:i=j
  · subst i;exact ⟨wp,ww,row⟩
  · have ij:i.val < j.val:=by have ne:i.val≠j.val:=fun h=>eq (Fin.ext h);omega
    have old:Complete l i ready:=inv.completed i ij
    exact complete_transfer l i j ready u old ij out
 exact ⟨u,placedRun,⟨driver,metadata,source_transfer l s u inv.source low,completed⟩,rfl,fullFrame,low⟩

lemma setup_heap (s:State):(applyBlock setup s).natHeap=s.natHeap :=rfl
lemma Retention.withPC (s:State) (pc:ℕ):Retention s (setPC s pc) :=⟨rfl,rfl,rfl,rfl,fun _ _ _ _=>rfl⟩

/-- Branch, charged physical header reads, and the actual55 printer. -/
theorem print_axis {n:ℕ} {f:Family n} (l:Layout n f)
 (j:Fin (axisCount n)) (x:Fin n → ℂ) (s:State) (inv:Invariant l j.val s)
 (pc:s.pc=6) (wb:WordBound l.B s):∃u,
 BoundedRuns program n x l.B s
  (UniformMatchingAxisTableMachine.runtime (UniformSelectedCRT.radices n j) (f.count j)+15) u ∧
 Printed l j.val u ∧u.pc=76 ∧Retention s u ∧
 (∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 have code:=l.code
 let entered:=setPC s 7
 have eb:=changePC_bound l.B s 7 wb (by omega)
 have first:BoundedRuns program n x l.B s 1 entered:=.next wb
  (by simp [step,pc,branch_at,inv.driver.index,inv.driver.count,j.isLt,entered,setPC]) (.refl eb)
 have ei:Invariant l j.val entered:=inv.withPC
 have safe:=setup_safe l j entered ei.metadata ei.driver ei.source
 have installed:=block_runs setup program 7 n l.B x entered setup_code rfl eb
  (by rw [setup_length];omega) safe.1 safe.2
 have hi:=setup_invariant l entered ei
 have head:=setup_header l j entered ei.metadata ei.driver ei.source
 have setupPC:(applyBlock setup entered).pc=21:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
 have vf0:=setup_retention entered
 have heap0:=setup_heap entered
 generalize hv:applyBlock setup entered=v at installed hi head setupPC vf0 heap0
 obtain ⟨u,run,up,pc',frame,low⟩:=print_prepared l j x v hi head setupPC installed.final_bound
 have vf:Retention s v:=(Retention.withPC s 7).trans vf0
 have heap:v.natHeap=s.natHeap:=heap0
 refine ⟨u,?_,up,pc',vf.trans frame,?_⟩
 · convert first.trans (installed.trans run) using 1
   simp only [setup_length];omega
 · intro t ht
   exact (low t ht).trans (congrFun heap t)


lemma Driver.advance {n j:ℕ} {f:Family n} {l:Layout n f} {s:State} (h:Driver l j s):
 Driver l (j+1) (setPC (writeNat s 3246 (j+1)) 6) :=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · constructor
   · simpa [setPC,writeNat,next] using h.header.directory
   · simpa [setPC,writeNat,next] using h.header.permutations
   · simpa [setPC,writeNat,next] using h.header.widths
   · simpa [setPC,writeNat,next] using h.header.markers
   · simpa [setPC,writeNat,next] using h.header.rows
 · simpa [setPC,writeNat,next] using h.count
 · simp [setPC,writeNat,next]
 · simpa [setPC,writeNat,next] using h.zero
 · simpa [setPC,writeNat,next] using h.one
 · simpa [setPC,writeNat,next] using h.two
 · simpa [setPC,writeNat,next] using h.four

/-- An actual full loop iteration, including the charged index increment and jump. -/
theorem iteration {n:ℕ} {f:Family n} (l:Layout n f)
 (j:Fin (axisCount n)) (x:Fin n → ℂ) (s:State) (inv:Invariant l j.val s)
 (pc:s.pc=6) (wb:WordBound l.B s):∃u,
 BoundedRuns program n x l.B s
  (UniformMatchingAxisTableMachine.runtime (UniformSelectedCRT.radices n j) (f.count j)+17) u ∧
 Invariant l (j.val+1) u ∧u.pc=6 ∧Retention s u ∧
 (∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 obtain ⟨v,body,pi,vpc,vf,low⟩:=print_axis l j x s inv pc wb
 have code:=l.code
 let advanced:=writeNat v 3246 (j.val+1)
 have ab:=writeNat_bound l.B v 3246 (j.val+1) body.final_bound
  (by rw [vpc];omega) (by have a:=l.rowsBound;have ji:=j.isLt;omega)
 have index:v.natReg 3246+v.natReg 3248=j.val+1:=by rw [pi.driver.index,pi.driver.one]
 have advance:BoundedRuns program n x l.B v 1 advanced:=.next body.final_bound
  (by simp only [step,vpc,advance_at,evalNat,index];rfl) (.refl ab)
 let u:=setPC advanced 6
 have ub:=changePC_bound l.B advanced 6 ab (by omega)
 have ret:BoundedRuns program n x l.B advanced 1 u:=.next ab
  (by simp [step,advanced,writeNat,next,vpc,jump_at,u,setPC]) (.refl ub)
 have frame:Retention v u:=by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i _ _ hi
  simp (disch:=omega) [u,advanced,setPC,writeNat,next]
 have metadata:Metadata n u:=UniformMultiAxisSectorMetadataPreparation.retained_metadata pi.metadata
  frame.metadataFrame l.permutations l.protectedBelow (fun _ _=>rfl)
 refine ⟨u,?_,⟨pi.driver.advance,metadata,pi.source,pi.completed⟩,rfl,vf.trans frame,low⟩
 convert body.trans (advance.trans ret) using 1


def axisCost {n:ℕ} (f:Family n) (j:ℕ):ℕ :=if h:j < axisCount n then
 UniformMatchingAxisTableMachine.runtime (UniformSelectedCRT.radices n ⟨j,h⟩) (f.count ⟨j,h⟩)+17 else 0
def loopCost {n:ℕ} (f:Family n):ℕ → ℕ → ℕ
 | _,0=>0
 | j,k+1=>axisCost f j+loopCost f (j+1) k
lemma axisCost_eq {n:ℕ} (f:Family n) (j:Fin (axisCount n)):
 axisCost f j.val=UniformMatchingAxisTableMachine.runtime (UniformSelectedCRT.radices n j) (f.count j)+17 :=by
 simp [axisCost,j.isLt]
/-- Actual finite outer-loop induction; neither per-axis ready states nor the
final axis tables are supplied by the caller. -/
theorem loop {n:ℕ} {f:Family n} (l:Layout n f) (j fuel:ℕ) (x:Fin n → ℂ) (s:State)
 (inv:Invariant l j s) (left:j+fuel=axisCount n) (pc:s.pc=6) (wb:WordBound l.B s):∃u,
 BoundedRuns program n x l.B s (loopCost f j fuel) u ∧Invariant l (axisCount n) u ∧
 u.pc=6 ∧Retention s u ∧(∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 induction fuel generalizing j s with
 | zero=>
  have eq:j=axisCount n:=by omega
  subst j
  exact ⟨s,.refl wb,inv,pc,Retention.refl s,fun _ _=>rfl⟩
 | succ fuel ih=>
  let index:Fin (axisCount n):=⟨j,by omega⟩
  obtain ⟨v,first,vi,vp,vf,low⟩:=iteration l index x s inv pc wb
  obtain ⟨u,rest,ui,up,uf,low'⟩:=ih (j+1) v vi (by omega) vp first.final_bound
  refine ⟨u,?_,ui,up,vf.trans uf,fun t ht=>(low' t ht).trans (low t ht)⟩
  convert first.trans rest using 1
  rw [loopCost,←axisCost_eq f index]

lemma boot_heap (s:State):(applyBlock boot s).natHeap=s.natHeap :=rfl
/-- A single stored79-instruction program prints and retains every actual
selected-axis matching table, with all loops/loads/headers/helper calls charged. -/
theorem execution {n:ℕ} {f:Family n} (l:Layout n f) (x:Fin n → ℂ) (s:State)
 (hm:Metadata n s) (hh:Header l s) (src:Source f l.directory s) (pc:s.pc=0)
 (wb:WordBound l.B s):∃u,
 BoundedExecution program n x l.B s (loopCost f 0 (axisCount n)+8) u ∧u.pc=78 ∧
 (∀j:Fin (axisCount n),Complete l j u) ∧Metadata n u ∧Source f l.directory u ∧
 Retention s u ∧(∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 have code:=l.code;have bounds:=l.rowsBound
 have safe:readable boot s ∧peak boot s ≤ l.B:=by
  simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,hm.saved.count]
  simp only [axisCount] at bounds
  omega
 have initialized:=block_runs boot program 0 n l.B x s boot_code pc wb
  (by rw [boot_length];omega) safe.1 safe.2
 have ret:=boot_retention s
 have metadata:=UniformMultiAxisSectorMetadataPreparation.retained_metadata hm
  ret.metadataFrame l.permutations l.protectedBelow (fun _ _=>rfl)
 have inv:Invariant l 0 (applyBlock boot s):=⟨boot_driver l s hm hh,metadata,src,fun _ hi=>by omega⟩
 have bp:(applyBlock boot s).pc=6:=by rw [UniformTensorMonomialMachine.applyBlock_pc,boot_length,pc]
 have heap:=boot_heap s
 generalize hv:applyBlock boot s=v at initialized ret inv bp heap
 obtain ⟨t,run,ti,tp,tf,low⟩:=loop l 0 (axisCount n) x v inv (by omega) bp initialized.final_bound
 let u:=setPC t 78
 have ub:=changePC_bound l.B t 78 run.final_bound (by omega)
 have stop:BoundedRuns program n x l.B t 1 u:=.next run.final_bound
  (by simp [step,tp,branch_at,ti.driver.index,ti.driver.count,u,setPC]) (.refl ub)
 have halt:BoundedExecution program n x l.B u 1 u:=.halt ub (by simp [step,u,setPC,halt_at])
 have fullFrame:Retention s u:=ret.trans tf
 have lowFinal:∀z,z < l.permutations → u.natHeap z=s.natHeap z:=by
  intro z hz
  exact (low z hz).trans (congrFun heap z)
 have finalMeta:=UniformMultiAxisSectorMetadataPreparation.retained_metadata hm
  fullFrame.metadataFrame l.permutations l.protectedBelow lowFinal
 refine ⟨u,?_,rfl,fun j=>ti.completed j j.isLt,finalMeta,ti.source,fullFrame,lowFinal⟩
 convert initialized.executes (run.executes (stop.executes halt)) using 1
 simp only [boot_length];omega

lemma loopCost_bound {n:ℕ} (f:Family n) (j fuel:ℕ) (left:j+fuel ≤ axisCount n):
 loopCost f j fuel ≤ fuel*(21*len n+38) :=by
 induction fuel generalizing j with
 | zero=>simp [loopCost]
 | succ fuel ih=>
  let index:Fin (axisCount n):=⟨j,by omega⟩
  have cap:=UniformMatchingAxisTableMachine.matching_capacity (UniformSelectedCRT.radices n index)
   (f.edges index) (f.matching index) (f.range index)
  have cost:=UniformMatchingAxisTableMachine.runtime_linear
   (UniformSelectedCRT.radices n index) (f.count index) cap
  have radixBound:UniformSelectedCRT.radices n index ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n index
  have tail:=ih (j+1) (by omega)
  rw [loopCost,axisCost_eq f index]
  have mul:(fuel+1)*(21*len n+38)=fuel*(21*len n+38)+(21*len n+38):=by ring
  rw [mul];omega

/-- Convert literal per-axis four-word rows to the list-row interface in CRT order. -/
lemma rows_ofFn {m:ℕ} (f:Fin m → UniformSectorPackingMachine.PhysicalAxis)
 (depth base:ℕ) (s:State)
 (h:∀j,UniformSectorPackingMachine.Rows [f j] 0 (base+4*(depth+j.val)) s):
 UniformSectorPackingMachine.Rows (List.ofFn f) depth base s :=by
 induction m generalizing depth with
 | zero=>simp [UniformSectorPackingMachine.Rows]
 | succ m ih=>
  rw [List.ofFn_succ]
  have first:=h 0
  change s.natHeap (base+4*depth)=some (f 0).geometry.widths.length ∧
   s.natHeap (base+4*depth+1)=some (f 0).widthsBase ∧
   s.natHeap (base+4*depth+2)=some (f 0).geometry.widths.sum ∧
   s.natHeap (base+4*depth+3)=some (f 0).permutationBase ∧True at first
  refine ⟨first.1,first.2.1,first.2.2.1,first.2.2.2.1,ih _ (depth+1) ?_⟩
  intro j
  convert h j.succ using 1
  congr 1
  simp only [Fin.val_succ]
  omega

def physicalAxis {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f) (j:Fin (axisCount n)):
 UniformSectorPackingMachine.PhysicalAxis :=
 UniformMatchingAxisTableMachine.physicalAxis (UniformSelectedCRT.radices n j)
  (l.widths+j.val*len n) (l.permutations+j.val*len n) (f.edges j)
  (f.matching j) (f.range j) (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j)
def axes {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f):List UniformSectorPackingMachine.PhysicalAxis :=
 List.ofFn (physicalAxis hn l)
lemma axes_length {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f):
 (axes hn l).length=axisCount n :=by simp [axes]
lemma axis_volume {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f) (j:Fin (axisCount n)):
 (physicalAxis hn l j).geometry.widths.sum=UniformSelectedCRT.radices n j :=by
 exact UniformMatchingAxisTableMachine.widths_sum _ _
  (UniformMatchingAxisTableMachine.matching_capacity _ (f.edges j) (f.matching j) (f.range j))
lemma axes_volume {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f):
 UniformSectorPackingMachine.physicalVolume (axes hn l)=len n :=by
 unfold UniformSectorPackingMachine.physicalVolume UniformSectorPackingMachine.physicalAxes
  UniformSectorPacking.radices axes
 rw [List.map_map]
 change ((List.ofFn (physicalAxis hn l)).map (fun a=>a.geometry.widths.sum)).prod=len n
 rw [List.map_ofFn]
 simp only [List.prod_ofFn,Function.comp_apply,axis_volume]
 exact UniformSelectedCRT.radices_product n

lemma complete_physical {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f) (s:State)
 (h:∀j,Complete l j s):
 UniformSectorPackingMachine.Rows (axes hn l) 0 l.rows s ∧
 UniformSectorPackingMachine.Widths (axes hn l) s ∧
 UniformSectorPackingMachine.Permutations (axes hn l) s :=by
 have each:∀j,UniformSectorPackingMachine.Rows [physicalAxis hn l j] 0 (l.rows+4*j.val) s ∧
  UniformSectorPackingMachine.Widths [physicalAxis hn l j] s ∧
  UniformSectorPackingMachine.Permutations [physicalAxis hn l j] s:=by
  intro j
  exact UniformMatchingAxisTableMachine.physical_axis (f.edges j) s (f.matching j) (f.range j)
   (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn j) (h j).2.2 (h j).1 (h j).2.1
 refine ⟨rows_ofFn _ 0 l.rows s (fun j=>by simpa only [Nat.zero_add] using (each j).1),?_,?_⟩
 · intro a ha j
   obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
   exact (each i).2.1 _ (by simp) j
 · intro a ha j
   obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
   exact (each i).2.2 _ (by simp) j

/-- The actual fixed79 producer supplies genuine ell+1-axis physical packing inputs.
Only the physical per-axis matched edge banks and ordinary allocation are entry
premises; no populated widths/permutations, whole permutation or action is assumed. -/
theorem execution_axes {n:ℕ} {f:Family n} (hn:0 < n) (l:Layout n f)
 (x:Fin n → ℂ) (s:State) (hm:Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
 (hh:Header l s) (src:Source f l.directory s) (pc:s.pc=0) (wb:WordBound l.B s):∃u,
 BoundedExecution program n x l.B s (loopCost f 0 (axisCount n)+8) u ∧u.pc=78 ∧
 UniformSectorPackingMachine.Rows (axes hn l) 0 l.rows u ∧
 UniformSectorPackingMachine.Widths (axes hn l) u ∧
 UniformSectorPackingMachine.Permutations (axes hn l) u ∧Metadata n u ∧
 UniformInitialPreparation.Operands n x u ∧Source f l.directory u ∧Retention s u ∧
 (∀t,t < l.permutations → u.natHeap t=s.natHeap t) :=by
 obtain ⟨u,run,upc,all,metadata,source,frame,low⟩:=execution l x s hm hh src pc wb
 obtain ⟨rows,widths,perms⟩:=complete_physical hn l u all
 exact ⟨u,run,upc,rows,widths,perms,metadata,ho.transport frame.1,source,frame,low⟩

lemma execution_cost {n:ℕ} (f:Family n):
 loopCost f 0 (axisCount n)+8 ≤ axisCount n*(21*len n+38)+8 :=by
 exact Nat.add_le_add_right (loopCost_bound f 0 (axisCount n) (by omega)) 8

end
end ExactFourierCircuits.UniformAllAxisMatchingTablePreparation
