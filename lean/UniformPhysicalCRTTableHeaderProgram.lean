import UniformNatBlockMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalCRTTableHeaders
open UniformNatBlockMachine
noncomputable section
/-- Install physical table addresses and the real low source tables; no table
contents or output permutation are inserted by these header operations. -/
def operations:List Op:=[
 .literal 7390 0,.literal 7391 2,.literal 7394 6,.literal 7395 5,
 .binary .mul 7392 103 7391,.binary .sub 7310 6026 7392,
 .binary .sub 7311 6026 103,.binary .add 7300 7311 7390,
 .literal 7790 1,.binary .add 7790 102 7790,.binary .add 7791 103 7390,
 .binary .add 7792 6904 7390,.binary .mul 7793 102 7394,
 .binary .add 7793 7793 7395,.binary .add 7793 105 7793,
 .binary .add 7794 7793 103,.binary .add 7795 7310 7390,
 .binary .add 7796 7311 7390,.binary .add 7797 6026 7390]
lemma operations_length:operations.length=19:=rfl
end
end ExactFourierCircuits.UniformPhysicalCRTTableHeaders
