import UniformProducedCalendarBanks
import UniformCalendarWorkspaceOrder
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarPrintedPrefix
open UniformMachine UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformActualGlobalConstants (constants)
open UniformFourierAxisWorkspace
noncomputable section

abbrev U (n:ℕ):ℕ:=UniformJointAllocation.slab constants n
abbrev physical {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)):=
 UniformProducedCalendarFamily.physical hn es position

structure AxisBanks {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (i:Fin (axisCount n)) (s:State):Prop where
 rows:UniformSectorPackingMachine.Rows [physical hn es position i] 0 (5*U n+4*i.val) s
 widths:UniformSectorPackingMachine.Widths [physical hn es position i] s
 permutations:UniformSectorPackingMachine.Permutations [physical hn es position i] s
 directory:s.natHeap (U n+2*i.val)=some (radix n i) ∧
  s.natHeap (U n+2*i.val+1)=some (axis constants n i).pool
 pool:∀lane:Fin 9,∀j:Fin (radix n i),
  s.scalarHeap ((axis constants n i).pool+lane.val*radix n i+j.val)=
  some (UniformPairMachine.prepared (if lane.val=0 then foldValues (es i) (fun _=>1) j.val else 1))

def Printed {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (k:ℕ) (s:State):Prop:=∀i,i.val<k→AxisBanks hn es position i s

/-- Exactly the memory bands needed by earlier printed axes. -/
structure StepFrame {n:ℕ} (j:Fin (axisCount n)) (s u:State):Prop where
 natLow:∀z,z<(axis constants n j).selected→(z<U n+2*j.val∨U n+2*j.val+2≤z)→
  u.natHeap z=s.natHeap z
 natHigh:∀z,2*U n≤z→(z<5*U n+4*j.val∨5*U n+4*j.val+4≤z)→
  u.natHeap z=s.natHeap z
 scalar:∀z,Arena.scalarBase constants n≤z→z<(axis constants n j).pool→
  u.scalarHeap z=s.scalarHeap z

lemma table_regions {n:ℕ} (i:Fin (axisCount n)):
 Arena.natBase constants n≤(axis constants n i).permutation ∧
 Arena.natBase constants n≤(axis constants n i).widths ∧
 Arena.scalarBase constants n≤(axis constants n i).pool:=by
 dsimp only[axis,axisBank]
 omega

lemma small_count {n:ℕ} (hn:0<n):4*axisCount n≤U n:=by
 have h:=UniformJointAllocation.actual_arithmetic constants n hn
 change _≤U n at h
 omega

lemma transfer {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (i j:Fin (axisCount n)) (before:i.val<j.val) (s u:State)
 (old:AxisBanks hn es position i s) (frame:StepFrame j s u):AxisBanks hn es position i u:=by
 have natBefore:=UniformCalendarWorkspaceOrder.nat_before constants n i j before
 have scalarBefore:=UniformCalendarWorkspaceOrder.scalar_before constants n i j before
 have dirs:=UniformCalendarWorkspaceOrder.directory_before constants n
 have currentBase:Arena.natBase constants n≤(axis constants n j).selected:=by
  change _≤Arena.natBase constants n+natPrefix n j.val
  omega
 have currentDir:U n+2*j.val+2≤Arena.natBase constants n:=by
  have h:=j.isLt
  change U n+2*axisCount n≤Arena.natBase constants n at dirs
  omega
 have regions:=table_regions i
 have tableEnds:=UniformProducedCalendarFamily.workspace_regions (radix n i)
  (Arena.natBase constants n+natPrefix n i.val)
  (Arena.scalarBase constants n+9*prefixSum n i.val)
 have pEnd:(axis constants n i).permutation+radix n i≤(axis constants n i).endNat:=tableEnds.1
 have wEnd:(axis constants n i).widths+radix n i≤(axis constants n i).endNat:=tableEnds.2
 have tableFrame:∀z,Arena.natBase constants n≤z→z<(axis constants n i).endNat→
  u.natHeap z=s.natHeap z:=by
  intro z lo hi
  exact frame.natLow z (by omega) (Or.inr (by omega))
 have rowFrame:∀b,b<4→u.natHeap (5*U n+4*i.val+b)=s.natHeap (5*U n+4*i.val+b):=by
  intro b hb
  exact frame.natHigh _ (by omega) (Or.inl (by omega))
 refine ⟨?_,?_,?_,?_,?_⟩
 · have h:=old.rows
   simp only[UniformSectorPackingMachine.Rows,Nat.mul_zero,Nat.add_zero] at h ⊢
   have first:u.natHeap (5*U n+4*i.val)=s.natHeap (5*U n+4*i.val):=by
    simpa only[Nat.add_zero] using rowFrame 0 (by omega)
   exact ⟨first.trans h.1,
    (rowFrame 1 (by omega)).trans h.2.1,(rowFrame 2 (by omega)).trans h.2.2.1,
    (rowFrame 3 (by omega)).trans h.2.2.2.1,trivial⟩
 · intro a ha k
   have eq:a=physical hn es position i:=List.mem_singleton.mp ha
   subst a
   have bound: (physical hn es position i).geometry.widths.length≤radix n i:=by
    change (UniformMatchingAxisTableMachine.widths (radix n i) (callTotal (radix n i) (es i))).length≤_
    have cap:=UniformMatchingAxisTableMachine.matching_capacity _ _
     (UniformMatchingKernelAmbient.matching (position i)) (UniformMatchingKernelAmbient.range (position i))
    rw[UniformMatchingAxisTableMachine.widths_length _ _ cap]
    exact Nat.sub_le _ _
   have addr:(physical hn es position i).widthsBase=(axis constants n i).widths:=rfl
   rw[addr,tableFrame _ (by omega) (by have h:=k.isLt;omega)]
   exact old.widths _ (by simp) k
 · intro a ha k
   have eq:a=physical hn es position i:=List.mem_singleton.mp ha
   subst a
   have rad:(physical hn es position i).geometry.widths.sum=radix n i:=
    UniformProducedCalendarFamily.physical_radix hn es position i
   have kb:k.val<radix n i:=k.isLt.trans_le rad.le
   have addr:(physical hn es position i).permutationBase=(axis constants n i).permutation:=rfl
   rw[addr,tableFrame _ (by omega) (by omega)]
   exact old.permutations _ (by simp) k
 · constructor
   · rw[frame.natLow _ (by omega) (Or.inl (by omega))];exact old.directory.1
   · rw[frame.natLow _ (by omega) (Or.inl (by omega))];exact old.directory.2
 · intro lane k
   have endPool:(axis constants n i).endScalar=(axis constants n i).pool+9*radix n i:=rfl
   have inside:lane.val*radix n i+k.val<9*radix n i:=by
    have h:lane.val+1≤9:=lane.isLt
    have m:=Nat.mul_le_mul_right (radix n i) h
    have hk:=k.isLt
    nlinarith only[m,hk]
   rw[frame.scalar _ (by omega) (by omega)]
   exact old.pool lane k

lemma zero {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i)) (s:State):
 Printed hn es position 0 s:=by intro i hi;omega

lemma step {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (j:Fin (axisCount n)) (s u:State) (old:Printed hn es position j.val s)
 (frame:StepFrame j s u) (current:AxisBanks hn es position j u):
 Printed hn es position (j.val+1) u:=by
 intro i hi
 by_cases h:i.val<j.val
 · exact transfer hn es position i j h s u (old i h) frame
 · have eq:i=j:=Fin.ext (by omega)
   subst i
   exact current

lemma complete {n:ℕ} (hn:0<n) (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (s:State) (done:Printed hn es position (axisCount n) s):
 let f:=UniformProducedCalendarFamily.family hn es position
 UniformGlobalRolePackingMachine.Banks
  (UniformActualGlobalTickContext.kernel hn (UniformProducedAllAxisGeometry.geometry f)).packing
  (UniformProducedAllAxisGeometry.geometry f).physical s ∧
 UniformGlobalDiagonalRowsMachine.Directory
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).rows.directory
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).entries 0 s ∧
 UniformGlobalDiagonalRowsMachine.Pools
  (UniformActualGlobalTickContext.diagonal hn (UniformProducedAllAxisGeometry.geometry f)).entries s:=by
 intro f
 exact ⟨UniformProducedCalendarBanks.banks hn es position s (fun i=>(done i i.isLt).rows)
  (fun i=>(done i i.isLt).widths) (fun i=>(done i i.isLt).permutations),
  UniformProducedCalendarBanks.directory hn es position s (fun i=>(done i i.isLt).directory),
  UniformProducedCalendarBanks.pools hn es position s (fun i=>(done i i.isLt).pool)⟩
end
end ExactFourierCircuits.UniformCalendarPrintedPrefix
