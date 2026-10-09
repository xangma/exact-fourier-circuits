import UniformNatBlockMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTMachine
open UniformMachine UniformNatBlockMachine
noncomputable section

def boot:List Op:=[.literal 7800 0,.literal 7801 1,.literal 7802 2,
 .literal 7803 0,.literal 7806 0,.literal 7805 0,.literal 7814 1]
def initBody:List Op:=[.binary .mul 7812 7802 7805,.binary .add 7808 7797 7812,
 .store 7808 7800,.binary .add 7808 7808 7801,.store 7808 7814,
 .binary .add 7808 7792 7812,.binary .add 7808 7808 7801,.load 7809 7808,
 .binary .mul 7814 7814 7809,.binary .add 7805 7805 7801]
def emitBody:List Op:=[.binary .add 7808 7793 7806,.load 7812 7808,
 .binary .add 7808 7795 7803,.store 7808 7812,
 .binary .add 7808 7794 7806,.load 7813 7808,
 .binary .add 7808 7796 7813,.store 7808 7803,.binary .add 7803 7803 7801]
def carryInit:List Op:=[.binary .add 7804 7790 7800]
def carryBody:List Op:=[.binary .sub 7804 7804 7801,.binary .mul 7808 7802 7804,
 .binary .add 7815 7797 7808,.binary .add 7808 7792 7808,
 .binary .add 7808 7808 7801,.load 7809 7808,.load 7810 7815,
 .binary .add 7816 7815 7801,.load 7811 7816,.binary .mul 7812 7810 7811,
 .binary .sub 7806 7806 7812,.binary .add 7813 7810 7801]
def successBody:List Op:=[.binary .mul 7812 7813 7811,.binary .add 7806 7806 7812,.store 7815 7813]
def wrapBody:List Op:=[.literal 7813 0,.store 7815 7813]
def program:Program:=boot.map Op.code++[.branchLT 7805 7790 8 19]++initBody.map Op.code++[.jump 7]++
 emitBody.map Op.code++[.branchLT 7803 7791 29 52]++carryInit.map Op.code++[.jump 31,
 .branchLT 7800 7804 32 52]++carryBody.map Op.code++[.branchLT 7813 7809 45 49]++
 successBody.map Op.code++[.jump 19]++wrapBody.map Op.code++[.jump 31,.halt]
lemma program_length:program.length=53:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma init_code:BlockAt initBody program 8:=by intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma emit_code:BlockAt emitBody program 19:=by intro i hi;change i<9 at hi;interval_cases i <;> rfl
lemma carry_init_code:BlockAt carryInit program 29:=by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma carry_code:BlockAt carryBody program 32:=by intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma success_code:BlockAt successBody program 45:=by intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma wrap_code:BlockAt wrapBody program 49:=by intro i hi;change i<2 at hi;interval_cases i <;> rfl
lemma init_test:program[7]?=some (.branchLT 7805 7790 8 19):=rfl
lemma init_jump:program[18]?=some (.jump 7):=rfl
lemma emit_test:program[28]?=some (.branchLT 7803 7791 29 52):=rfl
lemma carry_init_jump:program[30]?=some (.jump 31):=rfl
lemma carry_test:program[31]?=some (.branchLT 7800 7804 32 52):=rfl
lemma success_test:program[44]?=some (.branchLT 7813 7809 45 49):=rfl
lemma success_jump:program[48]?=some (.jump 19):=rfl
lemma wrap_jump:program[51]?=some (.jump 31):=rfl
lemma halt_code:program[52]?=some .halt:=rfl
structure Addresses where
 directory:ℕ
 alpha:ℕ
 beta:ℕ
 physicalAlpha:ℕ
 inverseBeta:ℕ
 work:ℕ
structure Args (a V:ℕ) (L:Addresses) (s:State):Prop where
 axes:s.natReg 7790=a
 volume:s.natReg 7791=V
 directory:s.natReg 7792=L.directory
 alpha:s.natReg 7793=L.alpha
 beta:s.natReg 7794=L.beta
 physicalAlpha:s.natReg 7795=L.physicalAlpha
 inverseBeta:s.natReg 7796=L.inverseBeta
 work:s.natReg 7797=L.work
structure Constants (s:State):Prop where
 zero:s.natReg 7800=0
 one:s.natReg 7801=1
 two:s.natReg 7802=2
structure Frame (s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,(j<7800∨7816<j)→u.natReg j=s.natReg j
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {s t u:State} (h:Frame s t) (k:Frame t u):Frame s u:=
 ⟨k.scalarHeap.trans h.scalarHeap,k.scalarReg.trans h.scalarReg,k.outputs.trans h.outputs,
 k.roots.trans h.roots,fun j hj=>(k.natReg j hj).trans (h.natReg j hj)⟩
lemma Frame.args {a V:ℕ} {L:Addresses} {s u:State} (h:Frame s u) (args:Args a V L s):Args a V L u:=by
 constructor
 all_goals first|exact (h.natReg _ (by omega)).trans args.axes|
  exact (h.natReg _ (by omega)).trans args.volume|exact (h.natReg _ (by omega)).trans args.directory|
  exact (h.natReg _ (by omega)).trans args.alpha|exact (h.natReg _ (by omega)).trans args.beta|
  exact (h.natReg _ (by omega)).trans args.physicalAlpha|exact (h.natReg _ (by omega)).trans args.inverseBeta|
  exact (h.natReg _ (by omega)).trans args.work
lemma Frame.pc {s t:State} (h:Frame s t) (pc:ℕ):Frame s {t with pc:=pc}:=by
 cases h;constructor <;> assumption
lemma args_pc {a V:ℕ} {L:Addresses} {s:State} (h:Args a V L s) (pc:ℕ):Args a V L {s with pc:=pc}:=by
 cases h;constructor <;> assumption
lemma constants_pc {s:State} (h:Constants s) (pc:ℕ):Constants {s with pc:=pc}:=by
 cases h;constructor <;> assumption
lemma block_pc (b:List Op) (s:State):(applyBlock b s).pc=s.pc+b.length:=by
 induction b generalizing s with
 | nil=>rfl
 | cons o b ih=>rw[applyBlock,ih,Op.apply_pc,List.length_cons];omega
end
end ExactFourierCircuits.UniformFastPhysicalCRTMachine
