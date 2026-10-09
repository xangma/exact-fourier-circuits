import UniformDirectLeafForestModel
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestProgram
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section
/-- Read actual measured rectangle-pool end; derive the current cache ordinal
by charged subtraction/division, never by misreading the pool as a count. -/
def boot:List Op:=[.literal 6679 0,.literal 6669 1,.literal 6670 2,.literal 6671 7,
 .literal 6672 4,.literal 6673 14,.literal 6662 0,.add 6663 6660 6679,
 .getNat 6666 6665,.add 6601 6690 6679,.add 6602 6691 6679,.add 6604 6692 6679,
 .add 6603 6160 6679,.add 6605 6162 6679,.add 6606 6163 6679,
 .add 6607 6164 6679,.add 6608 6165 6679,.add 6609 6166 6679,
 .add 5602 6814 6679,.add 5603 6815 6679,
 .literal 6681 9,.mul 6681 6681 6800,.sub 6680 6160 6820,.add 6693 6810 6679]
/-- Durable axis header follows all per-node ranges inside the completed task arena.
Both counts are read from executed producer state. -/
def durable:List Op:=[.mul 6684 6672 6800,.add 6684 6684 6672,
 .add 6684 6693 6684,.putNat 6684 6680,.add 6684 6684 6669,.putNat 6684 6661]
def read:List Op:=[.getNat 6667 6663,.add 6674 6663 6670,.getNat 6668 6674,
 .add 6674 6664 6662,.getNat 6676 6674]
def forward:List Op:=[.add 5600 6663 6679,.add 6600 5602 6679,
 .sub 6674 6667 6669,.mul 6675 6667 6674,.mul 6675 6673 6675,.add 6675 6667 6675,
 .literal 6610 0,.add 6610 6610 6676,.literal 6611 0]
/-- The measured helper count and endpoint ABI pointer generate a genuine
forward-only range. Transpose descriptor caches are not globally selected. -/
def capture:List Op:=[.mul 6682 6628 6634,.sub 6682 6609 6682,
 .mul 6683 6662 6670,.add 6683 6693 6683,.putNat 6683 6682,
 .add 6683 6683 6669,.putNat 6683 6628,.add 6680 6680 6628]
def skip:List Op:=[.mul 6683 6662 6670,.add 6683 6693 6683,
 .putNat 6683 6609,.add 6683 6683 6669,.putNat 6683 6679]
def advance:List Op:=[.add 6663 6663 6671,.add 6662 6662 6669]
def finish:List Op:=[.add 6160 6603 6679,.add 6162 6605 6679,.add 6163 6606 6679,
 .add 6164 6607 6679,.add 6165 6608 6679,.add 6166 6609 6679,.add 6128 6603 6679]
/-- One actual388 per genuine leaf, followed by a charged forward-only
range write; split nodes print a zero count. Every movement is literal. -/
def frontCode:Program:=boot.map Op.code++[.natBinary .div 6680 6680 6681]++durable.map Op.code++[
 .branchLT 6662 6661 32 453]++read.map Op.code++[.branchLT 6667 6670 39 38,
 .branchLT 6679 6668 445 39]++forward.map Op.code
def suffix:Program:=capture.map Op.code++[.jump 450]++skip.map Op.code++advance.map Op.code++
 [.jump 31]++finish.map Op.code++[.halt]
def program:Program:=frontCode++(UniformDirectLeafCacheLeafProgram.program.map (relocate 48 436)++suffix)
lemma boot_length:boot.length=24:=rfl
lemma durable_length:durable.length=6:=rfl
lemma read_length:read.length=5:=rfl
lemma forward_length:forward.length=9:=rfl
lemma capture_length:capture.length=8:=rfl
lemma skip_length:skip.length=5:=rfl
lemma advance_length:advance.length=2:=rfl
lemma finish_length:finish.length=7:=rfl
lemma prefix_length:frontCode.length=48:=rfl
lemma suffix_length:suffix.length=25:=rfl
lemma program_length:program.length=461:=by
 simp only[program,List.length_append,List.length_map,prefix_length,suffix_length,
  UniformDirectLeafCacheLeafProgram.program_length]
lemma prefix_at(i:ℕ)(hi:i<48):program[i]?=frontCode[i]?:=by
 rw[program,List.getElem?_append_left (by rw[prefix_length];exact hi)]
lemma suffix_at(i:ℕ)(hi:i<25):program[436+i]?=suffix[i]?:=by
 rw[program,List.getElem?_append_right (by rw[prefix_length];omega),prefix_length]
 rw[List.getElem?_append_right (by rw[List.length_map,UniformDirectLeafCacheLeafProgram.program_length];omega),
  List.length_map,UniformDirectLeafCacheLeafProgram.program_length]
 have sub:436+i-48-388=i:=by omega
 rw[sub]
lemma boot_code:BlockAt boot program 0:=by
 intro i hi;change i<24 at hi
 rw[show 0+i=i by omega,prefix_at i (by omega)]
 interval_cases i <;>rfl
lemma division_at:program[24]?=some (.natBinary .div 6680 6680 6681):=by
 rw[prefix_at 24 (by decide)];rfl
lemma durable_code:BlockAt durable program 25:=by
 intro i hi;change i<6 at hi
 rw[prefix_at (25+i) (by omega)]
 interval_cases i <;>rfl
lemma branch_at:program[31]?=some (.branchLT 6662 6661 32 453):=by
 rw[prefix_at 31 (by decide)];rfl
lemma read_code:BlockAt read program 32:=by
 intro i hi;change i<5 at hi
 rw[prefix_at (32+i) (by omega)]
 interval_cases i <;>rfl
lemma width_at:program[37]?=some (.branchLT 6667 6670 39 38):=by
 rw[prefix_at 37 (by decide)];rfl
lemma selected_at:program[38]?=some (.branchLT 6679 6668 445 39):=by
 rw[prefix_at 38 (by decide)];rfl
lemma forward_code:BlockAt forward program 39:=by
 intro i hi;change i<9 at hi
 rw[prefix_at (39+i) (by omega)]
 interval_cases i <;>rfl
lemma first_code:CodeAt UniformDirectLeafCacheLeafProgram.program program 48 436:=by
 exact UniformRankCrossPreparationMachine.segment_code frontCode suffix
  UniformDirectLeafCacheLeafProgram.program 48 436 prefix_length
lemma capture_code:BlockAt capture program 436:=by
 intro i hi;change i<8 at hi
 rw[suffix_at i (by omega)]
 interval_cases i <;>rfl
lemma skip_at:program[444]?=some (.jump 450):=by
 rw[show 444=436+8 by rfl,suffix_at 8 (by decide)];rfl
lemma skip_code:BlockAt skip program 445:=by
 intro i hi;change i<5 at hi
 rw[show 445+i=436+(9+i) by omega,suffix_at (9+i) (by omega)]
 interval_cases i <;>rfl
lemma advance_code:BlockAt advance program 450:=by
 intro i hi;change i<2 at hi
 rw[show 450+i=436+(14+i) by omega,suffix_at (14+i) (by omega)]
 interval_cases i <;>rfl
lemma next_at:program[452]?=some (.jump 31):=by
 rw[show 452=436+16 by rfl,suffix_at 16 (by decide)];rfl
lemma finish_code:BlockAt finish program 453:=by
 intro i hi;change i<7 at hi
 rw[show 453+i=436+(17+i) by omega,suffix_at (17+i) (by omega)]
 interval_cases i <;>rfl
lemma halt_at:program[460]?=some .halt:=by
 rw[show 460=436+24 by rfl,suffix_at 24 (by decide)];rfl
end
end ExactFourierCircuits.UniformDirectLeafForestProgram
