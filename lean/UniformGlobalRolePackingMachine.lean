import UniformSectorPackingMachine
import UniformBoundedAssembly
import UniformRankCrossPreparationMachine
import UniformScalarCopyMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalRolePackingMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
noncomputable section

/-- One physical packing permutation on each of the fixed W role arrays.
The same actual137 computes the inverse addresses using shared scratch; the
source/destination role offsets are computed by these actual eight moves. -/
def boot (W : ℕ) : List Op := [.literal 5810 W,.literal 5811 0,.literal 5812 1,.literal 5813 0]
def setup : List Op := [.add 600 5823 5811,.add 601 5824 5811,.add 602 5825 5811,
 .add 603 5826 5811,.add 637 5827 5811,.mul 5814 5813 5820,
 .add 604 5821 5814,.add 605 5822 5814]
def programFor (W : ℕ) : Program := (boot W).map Op.code ++ [.branchLT 5813 5810 5 152] ++
 setup.map Op.code ++ UniformSectorPackingMachine.program.map (relocate 13 150) ++
 [.natBinary .add 5813 5813 5812,.jump 4,.halt]
def program : Program := programFor ExplicitSeedBudget.paddedRoles
lemma boot_length (W : ℕ) : (boot W).length=4 := rfl
lemma setup_length : setup.length=8 := rfl
lemma program_length (W : ℕ) : (programFor W).length=153 := by
 simp only [programFor,List.length_append,List.length_map,boot_length,setup_length,
  UniformSectorPackingMachine.program_length,List.length_cons,List.length_nil]
lemma boot_code (W : ℕ) : BlockAt (boot W) (programFor W) 0 := by
 intro i hi;change i < 4 at hi;interval_cases i <;> rfl
lemma setup_code (W : ℕ) : BlockAt setup (programFor W) 5 := by
 intro i hi;change i < 8 at hi;interval_cases i <;> rfl
lemma packing_code (W : ℕ) : CodeAt UniformSectorPackingMachine.program (programFor W) 13 150 := by
 exact UniformRankCrossPreparationMachine.segment_code
  ((boot W).map Op.code ++ [.branchLT 5813 5810 5 152] ++ setup.map Op.code)
  [.natBinary .add 5813 5813 5812,.jump 4,.halt] UniformSectorPackingMachine.program 13 150 rfl
lemma branch_at (W : ℕ) : (programFor W)[4]?=some (.branchLT 5813 5810 5 152) := rfl
lemma advance_at (W : ℕ) : (programFor W)[150]?=some (.natBinary .add 5813 5813 5812) := rfl
lemma jump_at (W : ℕ) : (programFor W)[151]?=some (.jump 4) := rfl
lemma halt_at (W : ℕ) : (programFor W)[152]?=some .halt := rfl

structure Geometry (W : ℕ) where
 B : ℕ
 ell : ℕ
 rows : ℕ
 suffix : ℕ
 stack : ℕ
 inverse : ℕ
 source : ℕ
 destination : ℕ
 volume : ℕ
 code : 153 ≤ B
 roles : W ≤ B
 rowsBelow : rows+4*ell ≤ suffix
 suffixBelow : suffix+ell+1 ≤ stack
 stackBelow : stack+9*ell ≤ inverse
 inverseFit : inverse+volume ≤ B
 sourceBelow : source+W*volume ≤ destination
 destinationFit : destination+W*volume ≤ B
 volumeFit : volume ≤ B

def Geometry.local {W : ℕ} (g : Geometry W) (i : Fin W) : UniformSectorPackingMachine.Layout where
 B := g.B
 ell := g.ell
 rows := g.rows
 suffix := g.suffix
 stack := g.stack
 inverse := g.inverse
 source := g.source+i.val*g.volume
 destination := g.destination+i.val*g.volume
 total := g.volume
 code := by have := g.code;omega
 rowsBelow := g.rowsBelow
 suffixBelow := g.suffixBelow
 stackBelow := g.stackBelow
 inverseBound := g.inverseFit
 sourceBelow := by have := g.sourceBelow;have := i.isLt;nlinarith
 destinationBound := by have := g.destinationFit;have := i.isLt;nlinarith
 volumeBound := g.volumeFit

structure Header {W : ℕ} (g : Geometry W) (s : State) : Prop where
 volume : s.natReg 5820=g.volume
 source : s.natReg 5821=g.source
 destination : s.natReg 5822=g.destination
 axes : s.natReg 5823=g.ell
 rows : s.natReg 5824=g.rows
 suffix : s.natReg 5825=g.suffix
 stack : s.natReg 5826=g.stack
 inverse : s.natReg 5827=g.inverse
structure Cursor {W : ℕ} (g : Geometry W) (i : ℕ) (s : State) : Prop extends Header g s where
 roles : s.natReg 5810=W
 zero : s.natReg 5811=0
 one : s.natReg 5812=1
 index : s.natReg 5813=i
lemma Cursor.withPC {W i pc : ℕ} {g : Geometry W} {s : State} (h : Cursor g i s) :
 Cursor g i (setPC s pc) := ⟨⟨h.volume,h.source,h.destination,h.axes,h.rows,h.suffix,h.stack,h.inverse⟩,h.roles,h.zero,h.one,h.index⟩

def Protected (q : ℕ) : Prop := (q < 600 ∨ 650 ≤ q) ∧ (q < 5810 ∨ 5815 ≤ q)
def Frame (s u : State) : Prop := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ q,Protected q → u.natReg q=s.natReg q) ∧ (∀ q,q ≠ 70 → u.scalarReg q=s.scalarReg q)
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
lemma Frame.trans {s t u : State} (a : Frame s t) (b : Frame t u) : Frame s u :=
 ⟨b.1.trans a.1,b.2.1.trans a.2.1,fun q h => (b.2.2.1 q h).trans (a.2.2.1 q h),
  fun q h => (b.2.2.2 q h).trans (a.2.2.2 q h)⟩
lemma boot_frame (W : ℕ) (s : State) : Frame s (applyBlock (boot W) s) := by
 refine ⟨rfl,rfl,?_,fun _ _ => rfl⟩
 intro q h
 simp (disch := omega) [boot,applyBlock,Op.apply,writeNat,next,Protected] at *
lemma setup_frame (s : State) : Frame s (applyBlock setup s) := by
 refine ⟨rfl,rfl,?_,fun _ _ => rfl⟩
 intro q h
 simp (disch := omega) [setup,applyBlock,Op.apply,writeNat,next,Protected] at *
lemma local_frame {s t : State} (h : UniformSectorPackingMachine.FinalFrame s t) : Frame s t :=
 ⟨h.1,h.2.1,fun q hq => h.2.2.1 q (by rcases hq.1 with h0|h0;exact Or.inl (by omega);exact Or.inr (Or.inl h0)),h.2.2.2⟩

def Source {W : ℕ} (g : Geometry W) (v : ℕ → Fin g.volume → Scalar) (s : State) : Prop :=
 ∀ i,i < W → ∀ j,s.scalarHeap (g.source+i*g.volume+j.val)=some (v i j)
def Filled {W : ℕ} (g : Geometry W) (p : Equiv.Perm (Fin g.volume))
 (v : ℕ → Fin g.volume → Scalar) (done : ℕ) (s : State) : Prop :=
 ∀ i,i < done → ∀ j,s.scalarHeap (g.destination+i*g.volume+j.val)=some (v i (p j))
def Banks {W : ℕ} (g : Geometry W) (as : List PhysicalAxis) (s : State) : Prop :=
 Rows as 0 g.rows s ∧ Widths as s ∧ Permutations as s
def NatOutside {W : ℕ} (g : Geometry W) (s t : State) : Prop :=
 ∀ q,(q < g.suffix ∨ g.suffix+g.ell+1 ≤ q) → (q < g.stack ∨ g.stack+9*g.ell ≤ q) →
  (q < g.inverse ∨ g.inverse+g.volume ≤ q) → t.natHeap q=s.natHeap q
def ScalarOutside {W : ℕ} (g : Geometry W) (s t : State) : Prop :=
 UniformScalarCopyMachine.Outside g.destination (W*g.volume) s.scalarHeap t

def permutation {W : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hvolume : UniformSectorPackingMachine.physicalVolume as=g.volume) : Equiv.Perm (Fin g.volume) :=
 (finCongr hvolume).symm.trans
  ((UniformSectorPacking.unpackingPermutation (UniformSectorPackingMachine.physicalAxes as)).trans (finCongr hvolume))
lemma permutation_local {W : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hvolume : UniformSectorPackingMachine.physicalVolume as=g.volume) (i : Fin W) :
 UniformSectorPackingMachine.physicalUnpacking as (g.local i) hvolume=permutation g as hvolume := rfl

lemma setup_headers {W : ℕ} {g : Geometry W} {s : State} (i : Fin W) (h : Cursor g i.val s) :
 UniformSectorPackingMachine.Header (g.local i) (applyBlock setup s) := by
 constructor <;> simp [Geometry.local,setup,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,
  h.axes,h.rows,h.suffix,h.stack,h.inverse,h.zero,h.index]
lemma setup_cursor {W i : ℕ} {g : Geometry W} {s : State} (h : Cursor g i s) :
 Cursor g i (applyBlock setup s) := by
 constructor
 · constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,
    h.axes,h.rows,h.suffix,h.stack,h.inverse]
 all_goals simp [setup,applyBlock,Op.apply,writeNat,next,h.roles,h.zero,h.one,h.index]
lemma setup_safe {W : ℕ} {g : Geometry W} {s : State} (i : Fin W) (h : Cursor g i.val s) :
 readable setup s ∧ peak setup s ≤ g.B := by
 have h0 := g.inverseFit;have h1 := g.destinationFit;have h2 := g.sourceBelow
 have h3 := g.rowsBelow;have h4 := g.suffixBelow;have h5 := g.stackBelow;have hi := i.isLt
 have off := Nat.mul_le_mul_right g.volume (Nat.le_of_lt hi)
 simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,h.volume,h.source,h.destination,
  h.axes,h.rows,h.suffix,h.stack,h.inverse,h.zero,h.index]
 omega
lemma local_cursor {W i : ℕ} {g : Geometry W} {s u : State}
 (h : Cursor g i s) (f : UniformSectorPackingMachine.FinalFrame s u) : Cursor g i u := by
 constructor
 · constructor
   all_goals first | exact (f.2.2.1 _ (Or.inr (by omega))).trans h.volume |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.source |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.destination |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.axes |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.rows |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.suffix |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.stack |
    exact (f.2.2.1 _ (Or.inr (by omega))).trans h.inverse
 all_goals first | exact (f.2.2.1 _ (Or.inr (by omega))).trans h.roles |
  exact (f.2.2.1 _ (Or.inr (by omega))).trans h.zero |
  exact (f.2.2.1 _ (Or.inr (by omega))).trans h.one |
  exact (f.2.2.1 _ (Or.inr (by omega))).trans h.index

def tick (s : State) : State := setPC (writeNat (setPC s 150) 5813 (s.natReg 5813+s.natReg 5812)) 4
lemma tick_frame (s : State) : Frame s (tick s) := by
 refine ⟨rfl,rfl,?_,fun _ _ => rfl⟩
 intro q h
 simp (disch := omega) [tick,setPC,writeNat,next,Protected] at *
lemma tick_cursor {W i : ℕ} {g : Geometry W} {s : State} (h : Cursor g i s) :
 Cursor g (i+1) (tick s) := by
 constructor
 · constructor <;> simp [tick,setPC,writeNat,next,h.volume,h.source,h.destination,h.axes,h.rows,h.suffix,h.stack,h.inverse]
 all_goals simp [tick,setPC,writeNat,next,h.roles,h.zero,h.one,h.index]

lemma iteration {W n : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hvolume : UniformSectorPackingMachine.physicalVolume as=g.volume) (hlen : as.length=g.ell)
 (v : ℕ → Fin g.volume → Scalar) (x : Fin n → ℂ) (s : State) (i : Fin W)
 (h : Cursor g i.val s) (banks : Banks g as s)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ g.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ g.suffix)
 (source : Source g v s) (pc : s.pc=4) (wb : WordBound g.B s) :
 ∃ u t,BoundedRuns (programFor W) n x g.B s t u ∧ t ≤ 213*g.volume+31 ∧ u.pc=4 ∧
 (∀ j:Fin g.volume,u.scalarHeap (g.destination+i.val*g.volume+j.val)=some (v i.val (permutation g as hvolume j))) ∧
 Cursor g (i.val+1) u ∧ Frame s u ∧ NatOutside g s u ∧
 (∀ q,q < g.destination+i.val*g.volume ∨ g.destination+(i.val+1)*g.volume ≤ q →
  u.scalarHeap q=s.scalarHeap q) := by
 let e := setPC s 5
 have eb := changePC_bound g.B s 5 wb (by have := g.code;omega)
 have branch : BoundedRuns (programFor W) n x g.B s 1 e :=
  .next wb (by simp [step,pc,branch_at,h.roles,h.index,i.isLt,e,setPC]) (.refl eb)
 have first := block_runs setup (programFor W) 5 n g.B x e (setup_code W) rfl eb
  (by rw [setup_length];have := g.code;omega) (setup_safe i h.withPC).1 (setup_safe i h.withPC).2
 let b := applyBlock setup e
 let ready := setPC b 0
 have rb := changePC_bound g.B b 0 first.final_bound (by have := g.code;omega)
 have head := setup_headers i (h.withPC (pc := 5))
 have hh : UniformSectorPackingMachine.Header (g.local i) ready :=
  ⟨head.count,head.rows,head.suffix,head.stack,head.inverse,head.source,head.destination⟩
 have localSource : UniformSectorPackingMachine.SourceReady (g.local i) (v i.val) ready :=
  source i.val i.isLt
 have localRows : Rows as 0 (g.local i).rows ready :=
  UniformSectorPackingMachine.rows_transfer as 0 (g.local i) s ready (by change 0+as.length ≤ g.ell;omega)
   banks.1 (fun _ _ => rfl)
 have localWidths : Widths as ready :=
  UniformSectorPackingMachine.widths_transfer as (g.local i) s ready banks.2.1 widthsBelow (fun _ _ => rfl)
 have localPermutations : Permutations as ready := by
  intro a ha j;exact banks.2.2 a ha j
 obtain ⟨t,ticks,cost,run,tp,inverse,values,out,nat,frame⟩ :=
  UniformSectorPackingMachine.execution as (g.local i) n x (v i.val) ready hlen hvolume hh
   localRows localWidths localPermutations widthsBelow permutationsBelow localSource rfl rb
 have run' : BoundedExecution UniformSectorPackingMachine.program n x g.B ready ticks t := run
 have moved := UniformBoundedAssembly.boundedExecution_placed (packing_code W)
  (by rw [UniformSectorPackingMachine.program_length];have := g.code;omega) (by have := g.code;omega) run'
 have bp : b.pc=13 := by rw [applyBlock_pc,setup_length];rfl
 rw [show placed 13 ready=b by
  change setPC b 13=b
  rw [←bp]
  cases b;rfl] at moved
 have cur := local_cursor (setup_cursor (h.withPC (pc := 5))) frame
 have ib : i.val+1 ≤ g.B := (Nat.succ_le_of_lt i.isLt).trans g.roles
 let a := writeNat (setPC t 150) 5813 (i.val+1)
 have ab := writeNat_bound g.B (setPC t 150) 5813 (i.val+1) moved.final_bound
  (by have := g.code;change 150+1 ≤ g.B;omega) ib
 have advance : BoundedRuns (programFor W) n x g.B (setPC t 150) 1 a := .next moved.final_bound
  (by simp [step,advance_at,setPC,evalNat,cur.index,cur.one,a]) (.refl ab)
 have same : tick t=setPC a 4 := by simp [tick,a,cur.index,cur.one]
 have last : BoundedRuns (programFor W) n x g.B a 1 (tick t) := by
  rw [same]
  exact .next ab (by simp [step,a,setPC,writeNat,next,jump_at])
   (.refl (changePC_bound g.B a 4 ab (by have := g.code;omega)))
 have localCost : ticks ≤ 213*g.volume+20 := cost
 refine ⟨tick t,1+(8+ticks)+2,?_,by omega,rfl,?_,tick_cursor cur,
  (setup_frame e).trans ((local_frame frame).trans (tick_frame t)),nat,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using branch.trans (first.trans (moved.trans (advance.trans last)))
 · rw [permutation_local] at values
   intro j
   exact values j
 · intro q hq
   apply out q
   rcases hq with before|after
   · exact Or.inl before
   · exact Or.inr (by dsimp only [Geometry.local];nlinarith)

end
end ExactFourierCircuits.UniformGlobalRolePackingMachine
