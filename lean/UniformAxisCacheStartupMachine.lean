import UniformAxisCacheAllocationEnvelope
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheStartupMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
namespace C
export UniformJointCacheAllocation (natStart scalarStart ell offsetSum)
end C
namespace A
export UniformJointAllocation (Constants slab envelope)
end A
namespace Seed
export UniformAllAxisSeedPreparation (Header Retained directoryBase prefixSum radix axisCount)
end Seed
noncomputable section
/-- Reads actual62 allocator bank6020=U and actual all-axis seed header201/202/204.
The selector reads each radix from the retained two-word seed directory. -/
def boot:List Op:=[.literal 6900 0,.literal 6901 1,.literal 6902 2,.literal 6903 9,
 .binary .mul 6801 202 6902,.binary .add 6801 6020 6801,
 .binary .mul 6802 201 6903,.binary .add 6802 6020 6802,
 .binary .add 6904 204 6900,.binary .add 6905 202 6900,.literal 6906 0]
def select:List Op:=[.binary .mul 6167 6906 6902,.binary .add 6167 6904 6167,
 .binary .add 6907 6167 6901,.load 6800 6907,.binary .add 4200 6906 6900]
def program:Program:=boot.map Op.code++select.map Op.code++[.halt]
lemma boot_length:boot.length=11:=rfl
lemma select_length:select.length=5:=rfl
lemma program_length:program.length=17:=rfl
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<11 at hi;interval_cases i <;>rfl
lemma select_code:BlockAt select program 11:=by
 intro i hi;change i<5 at hi;interval_cases i <;>rfl
lemma halt_at:program[16]?=some .halt:=rfl

structure Control (n j:ℕ)(s:State):Prop where
 zero:s.natReg 6900=0
 one:s.natReg 6901=1
 two:s.natReg 6902=2
 nine:s.natReg 6903=9
 source:s.natReg 6904=Seed.directoryBase n
 count:s.natReg 6905=C.ell n
 index:s.natReg 6906=j
structure Frontiers (c:A.Constants)(n j:ℕ)(s:State):Prop where
 natFrontier:s.natReg 6801=C.natStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.natSize (UniformAllAxisSeedPreparation.radixAt n i)) j
 scalarFrontier:s.natReg 6802=C.scalarStart c n+C.offsetSum (fun i=>UniformJointCacheExtent.scalarSize (UniformAllAxisSeedPreparation.radixAt n i)) j

lemma boot_values (c:A.Constants)(n:ℕ)(s:State)
 (seed:Seed.Header n (C.ell n) s)(slab:s.natReg 6020=A.slab c n):
 Control n 0 (applyBlock boot s) ∧Frontiers c n 0 (applyBlock boot s):=by
 constructor
 · constructor <;>simp [boot,applyBlock,Op.apply,evalNat,writeNat,next,seed.directory,seed.count,C.ell]
 · constructor <;>simp [boot,applyBlock,Op.apply,evalNat,writeNat,next,slab,seed.count,seed.offset,
    C.natStart,C.scalarStart,C.offsetSum,UniformJointCacheAllocation.natStart,
    UniformJointCacheAllocation.scalarStart,UniformJointCacheAllocation.offsetSum,Nat.mul_comm]

lemma select_values_of_width (c:A.Constants)(n:ℕ)(j:Fin (C.ell n))(s:State)
 (control:Control n j.val s)(front:Frontiers c n j.val s)
 (width:s.natHeap (Seed.directoryBase n+j.val*2+1)=some (Seed.radix n j)):
 Control n j.val (applyBlock select s) ∧Frontiers c n j.val (applyBlock select s) ∧
 (applyBlock select s).natReg 6800=Seed.radix n j ∧
 (applyBlock select s).natReg 6167=Seed.directoryBase n+2*j.val ∧
 (applyBlock select s).natReg 4200=j.val:=by
 refine ⟨?_,?_,?_,?_,?_⟩
 · constructor <;>simp [select,applyBlock,Op.apply,evalNat,writeNat,next,control.zero,control.one,
   control.two,control.nine,control.source,control.count,control.index]
 · exact ⟨front.natFrontier,front.scalarFrontier⟩
 · simp [select,applyBlock,Op.apply,evalNat,writeNat,next,control.one,control.two,control.source,control.index,width]
 · simp [select,applyBlock,Op.apply,evalNat,writeNat,next,control.two,control.source,control.index,Nat.mul_comm]
 · simp [select,applyBlock,Op.apply,evalNat,writeNat,next,control.zero,control.index]
end
end ExactFourierCircuits.UniformAxisCacheStartupMachine
