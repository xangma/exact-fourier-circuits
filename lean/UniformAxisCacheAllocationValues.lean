import UniformAxisCacheAllocationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAllocationMachine
open UniformMachine UniformNatBlockMachine
noncomputable section
lemma applyBlock_append (a b:List Op)(s:State):applyBlock (a++b) s=applyBlock b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>rfl
 | cons o a ih=>exact ih (o.apply s)
structure BaseValues (r N S:ℕ)(s:State):Prop where
 v6800:s.natReg 6800=r
 v6801:s.natReg 6801=N
 v6802:s.natReg 6802=S
 v6803:s.natReg 6803=0
 v6804:s.natReg 6804=2
 v6540:s.natReg 6540=2*r
 v6542:s.natReg 6542=D.amount (2*r) 0
structure CapacityValues (r N S:ℕ)(s:State):Prop where
 v6800:s.natReg 6800=r
 v6801:s.natReg 6801=N
 v6802:s.natReg 6802=S
 v6803:s.natReg 6803=0
 v6804:s.natReg 6804=2
 v6540:s.natReg 6540=2*r
 v6542:s.natReg 6542=D.amount (2*r) 0
 v6822:s.natReg 6822=28
 v6823:s.natReg 6823=4
 v6805:s.natReg 6805=UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4
 v6806:s.natReg 6806=r^2
 v6807:s.natReg 6807=UniformJointCacheExtent.capacity r
structure FrontValues (r N S:ℕ)(s:State):Prop where
 v6800:s.natReg 6800=r
 v6801:s.natReg 6801=N
 v6802:s.natReg 6802=S
 v6803:s.natReg 6803=0
 v6804:s.natReg 6804=2
 v6540:s.natReg 6540=2*r
 v6542:s.natReg 6542=D.amount (2*r) 0
 v6822:s.natReg 6822=28
 v6823:s.natReg 6823=4
 v6805:s.natReg 6805=UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4
 v6806:s.natReg 6806=r^2
 v6807:s.natReg 6807=UniformJointCacheExtent.capacity r
 v6824:s.natReg 6824=7
 v6808:s.natReg 6808=(2*r+2)
 v6809:s.natReg 6809=7*(2*r+2)
 v6810:s.natReg 6810=(C.axisBank r N S).tasks
 v6811:s.natReg 6811=(C.axisBank r N S).nodes
 v6812:s.natReg 6812=(C.axisBank r N S).requests
structure ControlValues (r N S:ℕ)(s:State):Prop where
 v6800:s.natReg 6800=r
 v6801:s.natReg 6801=N
 v6802:s.natReg 6802=S
 v6803:s.natReg 6803=0
 v6804:s.natReg 6804=2
 v6540:s.natReg 6540=2*r
 v6542:s.natReg 6542=D.amount (2*r) 0
 v6822:s.natReg 6822=28
 v6823:s.natReg 6823=4
 v6805:s.natReg 6805=UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4
 v6806:s.natReg 6806=r^2
 v6807:s.natReg 6807=UniformJointCacheExtent.capacity r
 v6824:s.natReg 6824=7
 v6808:s.natReg 6808=(2*r+2)
 v6809:s.natReg 6809=(3*r+11)*UniformJointCacheExtent.capacity r
 v6810:s.natReg 6810=(C.axisBank r N S).tasks
 v6811:s.natReg 6811=(C.axisBank r N S).nodes
 v6812:s.natReg 6812=(C.axisBank r N S).requests
 v6825:s.natReg 6825=3
 v6826:s.natReg 6826=11
 v6813:s.natReg 6813=(C.axisBank r N S).control
 v6814:s.natReg 6814=(C.axisBank r N S).leafForward
structure TimeValues (r N S:ℕ)(s:State):Prop where
 v6800:s.natReg 6800=r
 v6801:s.natReg 6801=N
 v6802:s.natReg 6802=S
 v6803:s.natReg 6803=0
 v6804:s.natReg 6804=2
 v6540:s.natReg 6540=2*r
 v6542:s.natReg 6542=D.amount (2*r) 0
 v6822:s.natReg 6822=28
 v6823:s.natReg 6823=4
 v6805:s.natReg 6805=UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4
 v6806:s.natReg 6806=r^2
 v6807:s.natReg 6807=UniformJointCacheExtent.capacity r
 v6824:s.natReg 6824=7
 v6808:s.natReg 6808=(2*r+2)
 v6809:s.natReg 6809=2*(2*r+2)
 v6810:s.natReg 6810=(C.axisBank r N S).tasks
 v6811:s.natReg 6811=(C.axisBank r N S).nodes
 v6812:s.natReg 6812=(C.axisBank r N S).requests
 v6825:s.natReg 6825=3
 v6826:s.natReg 6826=11
 v6813:s.natReg 6813=(C.axisBank r N S).control
 v6814:s.natReg 6814=(C.axisBank r N S).leafForward
 v6827:s.natReg 6827=8
 v6815:s.natReg 6815=(C.axisBank r N S).leafTranspose
 v6816:s.natReg 6816=(C.axisBank r N S).durations
 v6817:s.natReg 6817=(C.axisBank r N S).nodeStarts
 v6818:s.natReg 6818=(C.axisBank r N S).requestStarts
 v6819:s.natReg 6819=(C.axisBank r N S).endNat

lemma capacity_values (r N S:ℕ)(s:State)(h:BaseValues r N S s):
 CapacityValues r N S (applyBlock capacityOps s):=by
 have div:D.amount (2*r) 0/28=UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r)):=Nat.add_right_cancel (capacity_amount r)
 constructor
 all_goals simp [capacityOps,applyBlock,Op.apply,evalNat,writeNat,next,h.v6800,h.v6801,h.v6802,h.v6803,h.v6804,h.v6540,h.v6542,div,UniformJointCacheExtent.capacity,pow_two,Nat.mul_assoc]

lemma front_values (r N S:ℕ)(s:State)(h:CapacityValues r N S s):
 FrontValues r N S (applyBlock frontOps s):=by
 constructor
 all_goals simp [frontOps,applyBlock,Op.apply,evalNat,writeNat,next,h.v6800,h.v6801,h.v6802,h.v6803,h.v6804,h.v6540,h.v6542,h.v6822,h.v6823,h.v6805,h.v6806,h.v6807,C.axisBank,UniformJointCacheAllocation.axisBank,UniformJointCacheExtent.capacity,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

lemma control_values (r N S:ℕ)(s:State)(h:FrontValues r N S s):
 ControlValues r N S (applyBlock controlOps s):=by
 constructor
 all_goals simp [controlOps,applyBlock,Op.apply,evalNat,writeNat,next,h.v6800,h.v6801,h.v6802,h.v6803,h.v6804,h.v6540,h.v6542,h.v6822,h.v6823,h.v6805,h.v6806,h.v6807,h.v6824,h.v6808,h.v6809,h.v6810,h.v6811,h.v6812,C.axisBank,UniformJointCacheAllocation.axisBank,UniformJointCacheExtent.capacity,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

lemma time_values (r N S:ℕ)(s:State)(h:ControlValues r N S s):
 TimeValues r N S (applyBlock timeOps s):=by
 constructor
 all_goals simp [timeOps,applyBlock,Op.apply,evalNat,writeNat,next,h.v6800,h.v6801,h.v6802,h.v6803,h.v6804,h.v6540,h.v6542,h.v6822,h.v6823,h.v6805,h.v6806,h.v6807,h.v6824,h.v6808,h.v6810,h.v6811,h.v6812,h.v6825,h.v6826,h.v6813,h.v6814,C.axisBank,UniformJointCacheAllocation.axisBank,UniformJointCacheExtent.capacity,pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

lemma post_result (r N S:ℕ)(s:State)(args:Arguments r N S s)
 (zero:s.natReg 6803=0)(two:s.natReg 6804=2)(twice:s.natReg 6540=2*r)
 (amount:s.natReg 6542=D.amount (2*r) 0) : Result r N S (applyBlock post s) := by
 have b:BaseValues r N S s:=⟨args.radix,args.natFrontier,args.scalarFrontier,zero,two,twice,amount⟩
 have c:=capacity_values r N S s b
 have f:=front_values r N S _ c
 have d:=control_values r N S _ f
 have t:=time_values r N S _ d
 rw [post]
 simp only [applyBlock_append]
 constructor
 all_goals simp [scalarOps,applyBlock,Op.apply,evalNat,writeNat,next,t.v6800,t.v6802,t.v6803,t.v6807,t.v6810,t.v6811,t.v6812,t.v6813,t.v6814,t.v6815,t.v6816,t.v6817,t.v6818,t.v6819,C.axisBank,UniformJointCacheAllocation.axisBank,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

lemma boot_values (r N S:ℕ)(s:State)(args:Arguments r N S s):
 (applyBlock boot s).natReg 6540=2*r ∧ (applyBlock boot s).natReg 6541=0 ∧
 (applyBlock boot s).natReg 6803=0 ∧ (applyBlock boot s).natReg 6804=2 ∧
 Arguments r N S (applyBlock boot s) := by
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [boot,applyBlock,Op.apply,evalNat,writeNat,next,args.radix,args.natFrontier,args.scalarFrontier,Nat.mul_comm]
end
end ExactFourierCircuits.UniformAxisCacheAllocationMachine
