import DFTModelSavingNativeDirectionBoot

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeDirection
open UniformMachine UniformAssembly BinaryFrames DFTModelAdmissibilityControl
open UniformFixedNetworkScheduleMachine (Printed macroRecord)
open UniformFixedNetwork (edgeVectors)
open FramedScheduleWords (Label NestedEdge)
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

theorem paired_boot (n B T nRoles R A F q w r stack depth:ℕ)
 (x:Fin n→ℂ)(s:State)(emb:Fin nRoles↪Fin R){old new:Label (w+1)}(role:Fin nRoles)
 (edge:NestedEdge old new)(j:Fin edge.dimension)(X:Fin (2^(q*(w+1)+r))→Scalar)
 (pc:s.pc=P.address .gather)(cursor:s.natReg 2850=T)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s)
 (index:s.natReg 4134=j.val)(base:s.natReg 3300=A)(original:s.natReg 4121=A)
 (bits:s.natReg 4120=q*(w+1)+r)(volume:s.natReg 4122=2^(q*(w+1)+r))
 (frontier:s.natReg 4123=F)(rest:s.natReg 4127=r)
 (st:s.natReg 4150=stack)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (data:∀z,s.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X z))
 (qp:1 ≤ q)(m2:2 ≤ w+1)(rp:r < w+1)(fits:ExplicitSeedBudget.roleBits ≤ q*w+r)
 (bound:WordBound B s)(code:P.program.length ≤ B)
 (recordEnd:T+(macroRecord q emb (.edge old new role edge)).data.length ≤ F)
 (widthBound:(w+1)+1 ≤ B)(arrayEnd:A+R*2^(q*(w+1)+r) ≤ F)
 (poolEnd:F+5*2^(q*(w+1)+r) ≤ B)(square:(2^(q*(w+1)+r))^2 ≤ B)
 (X0:Fin (2^(q*(w+1)+r))→Scalar) (s0:State) (same:StateMatch s s0)
 (data0:∀z,s0.scalarHeap (A+(emb role).val*2^(q*(w+1)+r)+z.val)=some (X0 z)) :
 ∃p:Fin (w+1),∃hp:edgeVectors edge j p=1,∃u u0 ticks,
 BootResult n B T nRoles R A F q w r stack depth x emb role edge j X p hp s u ticks ∧
 BootResult n B T nRoles R A F q w r stack depth (fun _=>0) emb role edge j X0 p hp s0 u0 ticks ∧
 StateMatch u u0 := by
 have cb:WordBound B {s with pc:=0}:=changePC_bound B s 0 bound (Nat.zero_le B)
 have gatherCode:366≤B:=(Nat.le_add_left 366 (P.address .gather)).trans
  (UniformRecursiveParentReturn.code_bound .gather 366 B rfl code)
 obtain ⟨p,hp,a,a0,gt,g,g0,_gmatch⟩:=paired_gather n B T nRoles R A F q w r x {s with pc:=0}
  emb role edge j X rfl cursor printed index base volume frontier rest data qp m2 rp cb gatherCode
  recordEnd widthBound arrayEnd poolEnd square X0 {s0 with pc:=0} (same.withPC 0) data0
 obtain ⟨u,result⟩:=boot_of_gather n B T nRoles R A F q w r stack depth x s emb role edge j X p hp a gt g
  pc base original bits volume rest st dp one fits code poolEnd
 obtain ⟨u0,result0⟩:=boot_of_gather n B T nRoles R A F q w r stack depth (fun _=>0) s0 emb role edge j X0 p hp a0 gt g0
  (same.pc.trans pc) (by rw [same.natReg];exact base) (by rw [same.natReg];exact original)
  (by rw [same.natReg];exact bits) (by rw [same.natReg];exact volume)
  (by rw [same.natReg];exact rest) (by rw [same.natReg];exact st)
  (by rw [same.natReg];exact dp) (by rw [same.natReg];exact one) fits code poolEnd
 obtain ⟨v0,run0,matched⟩:=DFTModelSavingResidualNativeGroup.boundedRuns_match (y:=fun _=>0) result.run same
 have last:v0=u0:=DFTModelSavingResidualNativeGroup.boundedRuns_unique run0 result0.run
 subst v0
 exact ⟨p,hp,u,u0,gt+5,result,result0,matched⟩

end
end ExactFourierCircuits.DFTModelSavingNativeDirection
