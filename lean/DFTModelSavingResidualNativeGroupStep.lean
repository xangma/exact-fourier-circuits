import DFTModelSavingResidualNativeGroupData

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualNativeGroup
open UniformMachine UniformBinaryTensorCoordinates DFTModelAdmissibilityControl
open OAI.PowerSaving OAI.PowerSaving.RAM
open DFTModelAffine DFTModelSavingResidualSetup
open UniformRecursiveGroupLoop (Control)
namespace Stack
export UniformRecursiveReturnStackMachine (fields Bank)
end Stack
noncomputable section
attribute [local irreducible] P.program UniformBatching.width

structure CallResult (n B q D V i groups F stack depth : ℕ) (x : Fin n → ℂ) (s c : State) : Prop where
  run : BoundedRuns P.program n x B s 84 c
  pc : c.pc=0
  bits : c.natReg 4120=q
  base : c.natReg 4121=D+i*(W*2^q)
  size : c.natReg 4122=2^q
  fresh : c.natReg 4123=F
  stackReg : c.natReg 4150=stack
  depthReg : c.natReg 4151=depth+1
  bank : Stack.Bank Stack.fields (stack+34*depth) s.natReg c
  nat : ∀z,z < stack+34*depth∨stack+34*(depth+1) ≤ z→c.natHeap z=s.natHeap z
  scalar : c.scalarHeap=s.scalarHeap
  scalarReg : c.scalarReg=s.scalarReg
  outputs : c.outputs=s.outputs
  roots : c.rootOrders=s.rootOrders

 theorem call (n B k q m r D V A i groups F stack depth : ℕ) (x : Fin n → ℂ) (s : State)
  (control : Control k q m r A D V F stack depth groups i s)
  (pc : s.pc=P.address .groupTest) (partition : groups*(W*2^q)=V) (hi : i < groups)
  (wb : WordBound B s) (code : P.program.length ≤ B) (dataEnd : D+V ≤ B)
  (stackEnd : stack+34*(depth+1) ≤ B) : ∃c,CallResult n B q D V i groups F stack depth x s c := by
  obtain ⟨c,run,pc,bits,base,size,fresh,stack,depth,bank,nat,scalar,scalarReg,outputs,roots⟩:=
    UniformRecursiveGroupExecution.call_from_group n B q D V i groups stack depth F x s pc
      control.index control.count control.columns control.size control.dataBase control.frontier
      control.stack control.depth partition hi wb code dataEnd stackEnd
  exact ⟨c,run,pc,bits,base,size,fresh,stack,depth,bank,nat,scalar,scalarReg,outputs,roots⟩

structure GroupResult (n B k q m r D V A i groups F stack depth stackTop : ℕ)
  (cost : ℕ → ℕ) (x : Fin n → ℂ) (input : Fin W → Fin (2^q) → Scalar) (s u : State) (ticks : ℕ) : Prop where
  run : BoundedRuns P.program n x B s ticks u
  pc : u.pc=P.address .groupTest
  control : Control k q m r A D V F stack depth groups (i+1) u
  fields : ∀j∈Stack.fields,u.natReg j=if j=4125 then s.natReg j+1 else s.natReg j
  present : ∀(j : Fin W)(t : Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).isSome=true
  values : ∀(j : Fin W)(t : Fin (2^q)),(u.scalarHeap (D+i*(W*2^q)+j.val*2^q+t.val)).map Scalar.value=
    some ((physicalMatrix q).mulVec (fun z=>(input j z).value) t)
  scalar : ∀z,z < F→(z < D+i*(W*2^q)∨D+(i+1)*(W*2^q) ≤ z)→u.scalarHeap z=s.scalarHeap z
  nat : ∀z,z < F→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z
  constants : UniformBinaryCStageMachine.Constants u
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  nativeBits : u.natReg 5300=k
  nativeRest : u.natReg 5301=r
  time : ticks ≤ cost q+169

 theorem resume_child (n B k q m r D V A i groups F stack depth stackTop : ℕ)
  (cost : ℕ → ℕ) (x : Fin n → ℂ) (input : Fin W → Fin (2^q) → Scalar) (s c v : State) (ticks : ℕ)
  (control : Control k q m r A D V F stack depth groups i s)
  (partition : groups*(W*2^q)=V) (hi : i < groups) (dataEnd : D+V ≤ F)
  (stackRoom : stack+34*(depth+q+2) ≤ stackTop) (stackEnd : stackTop ≤ F)
  (wb : WordBound B s) (code : P.program.length ≤ B) (fb : F ≤ B)
  (called : CallResult n B q D V i groups F stack depth x s c)
  (child : ChildResult n B q (D+i*(W*2^q)) F stack stackTop (depth+1) cost x input c v ticks) :
  ∃u,GroupResult n B k q m r D V A i groups F stack depth stackTop cost x input s u
    (84+ticks+(76+P.size .restored)) ∧ u.scalarHeap=v.scalarHeap := by
  have localStack : stack+34*(depth+1) ≤ B := by nlinarith only [stackRoom,stackEnd,fb]
  have savedBank : Stack.Bank Stack.fields (stack+34*depth) s.natReg v := by
    intro j hj
    have jl : j < 34 := by simpa only [UniformRecursiveReturnStackMachine.fields_length] using hj
    have below : stack+34*depth+j < F := by nlinarith only [stackRoom,stackEnd,jl]
    rw [child.nat _ below (Or.inl (by omega))]
    exact called.bank j hj
  have next : i+1 ≤ B := by
    have gp : 0 < W*2^q := Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos _)
    have gb : groups ≤ V := (Nat.le_mul_of_pos_right _ gp).trans_eq partition
    omega
  obtain ⟨u,ret,up,fields,usp,udp,globalOne,ut,uv,uone,uk,ur,uq,um,unh,ush,usr,uou,uro⟩:=
    UniformRecursiveParentReturn.resume_fields n B k q m r A V (2^q) stack depth s.natReg x v
      child.pc child.stackReg child.depthReg savedBank (fun j _=>wb.2.1 j)
      (by rwa [control.index]) control.savedSize control.volume control.bits control.rest control.original
      control.columns control.width control.nativeBase child.run.final_bound code localStack
  have index : u.natReg 4125=i+1 := by simpa only [ite_true,control.index] using fields 4125 (by decide)
  refine ⟨u,⟨called.run.trans (child.run.trans ret),up,
    control.advance index usp udp globalOne ut fields,fields,?_,?_,?_,?_,?_,?_,?_,uk,ur,?_⟩,ush⟩
  · intro j t;rw [ush];exact child.present j t
  · intro j t;rw [ush];exact child.values j t
  · intro z hz out
    rw [ush,child.scalar z hz (by
      rcases out with out|out
      · exact Or.inl out
      · right;rw [Nat.add_assoc,←Nat.succ_mul];exact out),called.scalar]
  · intro z hz out
    rw [unh,child.nat z hz (by rcases out with h|h;exact Or.inl (by omega);exact Or.inr h)]
    exact called.nat z (by rcases out with h|h;exact Or.inl h;right;nlinarith only [stackRoom,h])
  · simpa only [UniformBinaryCStageMachine.Constants,ush] using child.constants
  · exact uou.trans (child.outputs.trans called.outputs)
  · exact uro.trans (child.roots.trans called.roots)
  · change 84+ticks+(76+9) ≤ cost q+169
    have time:=child.time
    omega

end
end ExactFourierCircuits.DFTModelSavingResidualNativeGroup
