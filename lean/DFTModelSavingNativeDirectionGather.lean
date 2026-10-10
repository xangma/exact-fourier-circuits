import DFTModelSavingNativePivotRecordFrame
import DFTModelSavingResidualNativeGroupGeometry

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
noncomputable section

/-- Full physical gather result; the least pivot remains attached to the actual
produced bank, metadata and charged halted execution. -/
structure GatherResult (n B T nRoles R A F q w r : ℕ) (x : Fin n→ℂ)
 (emb : Fin nRoles↪Fin R) {old new : Label (w+1)} (role : Fin nRoles)
 (edge : NestedEdge old new) (j : Fin edge.dimension)
 (X : Fin (2^(q*(w+1)+r))→Scalar) (p : Fin (w+1)) (hp : edgeVectors edge j p=1)
 (s u : State) (ticks : ℕ) : Prop where
 run : BoundedExecution UniformRecursiveResidualGatherRecordMachine.program n x B s ticks u
 time : ticks  ≤  UniformFixedNetworkOpcodeMachine.headCost (macroRecord q emb (.edge old new role edge))+18+
    UniformResidualGeneralPreparation.runtimeBound q (w+1) r+11*2^(q*(w+1)+r)+11
 pc : u.pc=365
 data : (∀b:Fin (2^(q*w+r)),∀t:Fin (2^q),u.scalarHeap (F+4*2^(q*(w+1)+r)+b.val*2^q+t.val)=
    some (X (UniformResidualExtendedPermutation.fibers q w r (edgeVectors edge j) p hp (b,t))))
 outside : (∀z,z  <  F+4*2^(q*(w+1)+r) ∨ F+5*2^(q*(w+1)+r)  ≤  z→u.scalarHeap z=s.scalarHeap z)
 permutation : (∀z:Fin (2^(q*(w+1)+r)),u.natHeap (F+2*2^(q*(w+1)+r)+z.val)=some
    ((UniformResidualSpectators.extend (q*(w+1)) r (UniformResidualPermutation.permutation q w (edgeVectors edge j) p hp) z).val))
 size : u.natReg 4015=2^q
 volume : u.natReg 4023=2^(q*(w+1)+r)
 columns : u.natReg 4060=q
 source : u.natReg 4090=A+(emb role).val*2^(q*(w+1)+r)
 destination : u.natReg 4091=F+4*2^(q*(w+1)+r)
 fresh : u.natReg 4133=F+5*2^(q*(w+1)+r)
 roots : u.rootOrders=s.rootOrders
 outputs : u.outputs=s.outputs
 entries : UniformXorTableMachine.Entries q (F+3*2^(q*(w+1)+r)) (2^q*2^q) u
 nat : (∀z,z < F→u.natHeap z=s.natHeap z)
 width : u.natReg 4061=w+1
 permPointer : u.natReg 4067=F+2*2^(q*(w+1)+r)
 xorPointer : u.natReg 4068=F+3*2^(q*(w+1)+r)
 kept : (∀z,z∈UniformRecursiveResidualGatherFrame.keptRegisters→u.natReg z=s.natReg z)
 finish : u.natReg 4130=T+(macroRecord q emb (.edge old new role edge)).data.length
 inverse : u.natReg 4131=(macroRecord q emb (.edge old new role edge)).inverse
 dimension : u.natReg 4132=edge.dimension
 one : u.natReg 4069=1
 directionPointer : u.natReg 4062=T+8+j.val*(w+1)
 direction : UniformRepeatedMaskMachine.Source (T+8+j.val*(w+1)) (edgeVectors edge j) u
 first : (∀i:Fin (w+1),i.val<p.val→edgeVectors edge j i=0)

theorem gather_first (n B T nRoles R A F q w r:ℕ) (x:Fin n→ℂ) (s:State)
 (emb:Fin nRoles↪Fin R) {old new:Label (w+1)} (role:Fin nRoles)
 (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=0) (cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val) (base:s.natReg 3300=A)
 (volume:s.natReg 4122=2^(q*(w+1)+r)) (frontier:s.natReg 4123=F) (rest:s.natReg 4127=r)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1  ≤  q) (m2:2  ≤  w+1) (rp:r  <  w+1)
 (bound:WordBound B s) (code:366  ≤  B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length  ≤  F)
 (widthBound:(w+1)+1  ≤  B) (arrayEnd:A+R*2^(q*(w+1)+r)  ≤  F)
 (poolEnd:F+5*2^(q*(w+1)+r)  ≤  B) (square:(2^(q*(w+1)+r))^2  ≤  B) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u ticks,
 GatherResult n B T nRoles R A F q w r x emb role edge j X p hp s u ticks := by
 obtain ⟨p,hp,u,ticks,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26⟩:=UniformRecursiveResidualGatherFrame.execution_frame_first
  n B T nRoles R A F q w r x s emb role edge j X pc cursor printed index base volume frontier rest data qp m2 rp bound code recordEnd widthBound arrayEnd poolEnd square
 exact ⟨p,hp,u,ticks,⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26⟩⟩

theorem paired_gather (n B T nRoles R A F q w r:ℕ) (x:Fin n→ℂ) (s:State)
 (emb:Fin nRoles↪Fin R) {old new:Label (w+1)} (role:Fin nRoles)
 (edge:NestedEdge old new) (j:Fin edge.dimension)
 (X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=0) (cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val) (base:s.natReg 3300=A)
 (volume:s.natReg 4122=2^(q*(w+1)+r)) (frontier:s.natReg 4123=F) (rest:s.natReg 4127=r)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1  ≤  q) (m2:2  ≤  w+1) (rp:r  <  w+1)
 (bound:WordBound B s) (code:366  ≤  B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length  ≤  F)
 (widthBound:(w+1)+1  ≤  B) (arrayEnd:A+R*2^(q*(w+1)+r)  ≤  F)
 (poolEnd:F+5*2^(q*(w+1)+r)  ≤  B) (square:(2^(q*(w+1)+r))^2  ≤  B)
 (X0:Fin (2^(q*(w+1)+r))→Scalar) (s0:State) (same:StateMatch s s0)
 (data0:∀z,s0.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X0 z)) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u u0 ticks,
 GatherResult n B T nRoles R A F q w r x emb role edge j X p hp s u ticks ∧
 GatherResult n B T nRoles R A F q w r (fun _=>0) emb role edge j X0 p hp s0 u0 ticks ∧
 StateMatch u u0 := by
 obtain ⟨p,hp,u,ticks,a⟩:=gather_first
  n B T nRoles R A F q w r x s emb role edge j X pc cursor printed index base volume frontier rest data qp m2 rp bound code recordEnd widthBound arrayEnd poolEnd square
 have print0:Printed T (macroRecord q emb (.edge old new role edge)).data s0 := by
  intro i hi;rw [same.natHeap];exact printed i hi
 obtain ⟨p0,hp0,u0,ticks0,z⟩:=gather_first n B T nRoles R A F q w r (fun _=>0) s0 emb role edge j X0
  (same.pc.trans pc) (by rw [same.natReg];exact cursor) print0
  (by rw [same.natReg];exact index) (by rw [same.natReg];exact base)
  (by rw [same.natReg];exact volume) (by rw [same.natReg];exact frontier)
  (by rw [same.natReg];exact rest) data0 qp m2 rp (same.wordBound bound) code recordEnd widthBound arrayEnd poolEnd square
 have pivots:p=p0:=DFTModelSavingResidualNativeGroup.first_unique hp hp0 a.first z.first
 cases pivots
 obtain ⟨times,matched⟩:=DFTModelSavingResidualNativeGroup.paired_execution a.run z.run same
 subst ticks0
 exact ⟨p,hp,u,u0,ticks,a,z,matched⟩

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
