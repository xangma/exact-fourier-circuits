import UniformCalendarPrintedPrefix
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarIterationFrame
open UniformMachine UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformActualGlobalConstants (constants)
open UniformFourierAxisWorkspace UniformCalendarPrintedPrefix
noncomputable section

lemma trans {n:ℕ} (j:Fin (axisCount n)) {s t u:State}
 (first:StepFrame j s t) (second:StepFrame j t u):StepFrame j s u where
 natLow:=fun z a b=>(second.natLow z a b).trans (first.natLow z a b)
 natHigh:=fun z a b=>(second.natHigh z a b).trans (first.natHigh z a b)
 scalar:=fun z a b=>(second.scalar z a b).trans (first.scalar z a b)

/-- Every actual389 branch's strong Outside frame preserves earlier axes. -/
lemma preparation {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (s u:State)
 (nat:∀z,z<(axis constants n j).selected∨(axis constants n j).phase≤z→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<U n∨U n+9*radix n j≤z→u.scalarHeap z=s.scalarHeap z):
 StepFrame j s u:=by
 have fits:=(axis_fit constants hn j).1
 change (axis constants n j).endNat≤2*U n at fits
 have geo:=axis_geometry constants n j
 have before:=boundary_before_caches constants n j
 change U n+9*radix n j≤UniformJointCacheAllocation.scalarStart constants n at before
 have old:UniformJointCacheAllocation.scalarStart constants n≤Arena.scalarBase constants n:=by
  change _≤UniformJointCacheAllocation.scalarEnd constants n
  unfold UniformJointCacheAllocation.scalarEnd
  omega
 refine ⟨?_,?_,?_⟩
 · intro z lo _;exact nat z (Or.inl lo)
 · intro z lo _;exact nat z (Or.inr (by omega))
 · intro z lo _;exact scalar z (Or.inr (by change _≤Arena.scalarBase constants n at old;omega))

/-- The real281/69 output footprint, specialized to the actual shared banks.
The region facts are derived from Workspace and genuine ordered-call capacity. -/
lemma dispatch {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (es:List Event)
 (position:(Σ _:Fin (callTotal (radix n j) es),Fin 2) ↪ Fin (radix n j)) (s u:State)
 (nat:∀z,(z<(axis constants n j).phase∨(axis constants n j).phase+56≤z)→
  (z<(axis constants n j).rawRows∨(axis constants n j).rawRows+3*callTotal (radix n j) es≤z)→
  (z<U n+2*j.val∨U n+2*j.val+2≤z)→
  (z<(axis constants n j).permutation∨(axis constants n j).permutation+radix n j≤z)→
  (z<(axis constants n j).widths∨(axis constants n j).widths+radix n j≤z)→
  (z<(axis constants n j).markers∨(axis constants n j).markers+radix n j≤z)→
  (z<5*U n+4*j.val∨5*U n+4*j.val+4≤z)→u.natHeap z=s.natHeap z)
 (scalar:∀z,z<(axis constants n j).pool∨(axis constants n j).pool+9*radix n j≤z→
  u.scalarHeap z=s.scalarHeap z):StepFrame j s u:=by
 have cap:=UniformMatchingAxisTableMachine.matching_capacity _ _
  (UniformMatchingKernelAmbient.matching position) (UniformMatchingKernelAmbient.range position)
 have count:callTotal (radix n j) es≤radix n j:=by omega
 have fits:=(axis_fit constants hn j).1
 change (axis constants n j).endNat≤2*U n at fits
 have geo:=axis_geometry constants n j
 have dirs:=UniformCalendarWorkspaceOrder.directory_before constants n
 have base:Arena.natBase constants n≤(axis constants n j).selected:=by
  change _≤Arena.natBase constants n+natPrefix n j.val;omega
 have currentDir:U n+2*j.val+2≤(axis constants n j).selected:=by
  change U n+2*axisCount n≤Arena.natBase constants n at dirs
  have h:=j.isLt
  omega
 have rows:2*U n≤5*U n+4*j.val:=by omega
 refine ⟨?_,?_,?_⟩
 · intro z lo outside
   apply nat z (Or.inl (by omega)) (Or.inl (by omega)) outside
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
 · intro z lo outside
   apply nat z (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) outside
 · intro z _ hi;exact scalar z (Or.inl hi)
end
end ExactFourierCircuits.UniformCalendarIterationFrame
