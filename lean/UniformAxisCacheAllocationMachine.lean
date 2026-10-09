import UniformCacheRowDurationMachine
import UniformJointCacheAllocation
import UniformNatBlockMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAllocationMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
namespace C
export UniformJointCacheAllocation (AxisAddresses axisBank)
end C
namespace D
export UniformCacheRowDurationMachine (program amount budget)
end D

/-- Ordinary inputs6800=radix,6801=current Nat frontier,6802=current scalar frontier.
All13 axis addresses are produced in6810..6821; no cached timing is supplied. -/
def boot : List Op := [.literal 6803 0,.literal 6804 2,
 .binary .mul 6540 6800 6804,.binary .add 6541 6803 6803]
def capacityOps : List Op := [.literal 6822 28,.binary .div 6805 6542 6822,
 .literal 6823 4,.binary .add 6805 6805 6823,
 .binary .mul 6806 6800 6800,.binary .mul 6807 6806 6805]
def frontOps : List Op := [.literal 6824 7,.binary .add 6808 6540 6804,
 .binary .mul 6809 6808 6823,.binary .add 6810 6801 6803,
 .binary .add 6811 6801 6809,.binary .mul 6809 6808 6824,
 .binary .add 6812 6811 6809]
def controlOps : List Op := [.binary .mul 6809 6809 6806,.binary .add 6813 6812 6809,
 .literal 6825 3,.literal 6826 11,.binary .mul 6809 6825 6800,
 .binary .add 6809 6809 6826,.binary .mul 6809 6809 6807,
 .binary .add 6814 6813 6809]
def timeOps : List Op := [.binary .mul 6809 6823 6806,.binary .add 6815 6814 6809,
 .literal 6827 8,.binary .mul 6809 6827 6806,.binary .add 6816 6814 6809,
 .binary .add 6817 6816 6808,.binary .mul 6809 6804 6808,
 .binary .add 6818 6816 6809,.binary .add 6819 6818 6806]
def scalarOps : List Op := [.binary .add 6820 6802 6803,.literal 6828 9,
 .binary .mul 6809 6828 6800,.binary .mul 6809 6809 6807,
 .binary .add 6821 6802 6809]
def post := capacityOps++frontOps++controlOps++timeOps++scalarOps
lemma boot_length:boot.length=4:=rfl
lemma post_length:post.length=35:=rfl

def program : Program := boot.map Op.code++D.program.map (relocate 4 22)++post.map Op.code++[.halt]
lemma program_length:program.length=58:=rfl
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma duration_code:CodeAt D.program program 4 22:=by
 change CodeAt D.program (boot.map Op.code++D.program.map (relocate 4 22)++(post.map Op.code++[.halt])) 4 22
 exact UniformRankCrossPreparationMachine.segment_code (boot.map Op.code) (post.map Op.code++[.halt]) _ 4 22 rfl
lemma post_code:BlockAt post program 22:=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (boot.map Op.code++D.program.map (relocate 4 22)) (post.map Op.code) [.halt] i (by simpa using hi)
 simpa only [program,List.append_assoc,List.length_append,List.length_map,boot_length,
  UniformCacheRowDurationMachine.program_length,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some] using h
lemma halt_at:program[57]?=some .halt:=rfl

noncomputable section
structure Arguments (r N S:ℕ)(s:State) : Prop where
 radix:s.natReg 6800=r
 natFrontier:s.natReg 6801=N
 scalarFrontier:s.natReg 6802=S
structure Result (r N S:ℕ)(s:State) : Prop where
 tasks:s.natReg 6810=(C.axisBank r N S).tasks
 nodes:s.natReg 6811=(C.axisBank r N S).nodes
 requests:s.natReg 6812=(C.axisBank r N S).requests
 control:s.natReg 6813=(C.axisBank r N S).control
 leafForward:s.natReg 6814=(C.axisBank r N S).leafForward
 leafTranspose:s.natReg 6815=(C.axisBank r N S).leafTranspose
 durations:s.natReg 6816=(C.axisBank r N S).durations
 nodeStarts:s.natReg 6817=(C.axisBank r N S).nodeStarts
 requestStarts:s.natReg 6818=(C.axisBank r N S).requestStarts
 endNat:s.natReg 6819=(C.axisBank r N S).endNat
 pool:s.natReg 6820=(C.axisBank r N S).pool
 endScalar:s.natReg 6821=(C.axisBank r N S).endScalar

/-- Address and integer bounds only; all generated values remain conclusions. -/
def wordBudget (r N S:ℕ):ℕ:=
 D.budget (2*r) 0+(C.axisBank r N S).endNat+(C.axisBank r N S).endScalar+100

lemma capacity_amount (r:ℕ): D.amount (2*r) 0/28+4=
 UniformJointCacheExtent.slotCount (Nat.clog 2 (4*r))+4:=by
 rw [UniformJointCacheExtent.slotCount_formula]
 unfold D.amount
 have h:2*(2*r+0)=4*r:=by omega
 rw [h,Nat.mul_div_right]
 decide
end
end ExactFourierCircuits.UniformAxisCacheAllocationMachine
