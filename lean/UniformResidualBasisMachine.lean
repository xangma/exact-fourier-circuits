import UniformResidualPivotMachine
import UniformRepeatedMaskMachine
import UniformResidualNativeCoordinates
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualBasisMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- Physical basis-image writer. Selected q images occupy the first q cells;
the remaining images are literal native unit bits with one pivot per column
omitted. No precomputed image bank or bitwise instruction is supplied. -/
def boot : List Op := [.literal 4045 1,.literal 4046 2,.literal 4047 0,
 .literal 4048 0,.literal 4049 1,.binary .mul 4050 4040 4041,
 .binary .sub 4051 4041 4045]
def positions : List Op := [.binary .div 4052 4048 4041,.binary .mod 4053 4048 4041]
def selected : List Op := [.binary .mul 4054 4049 4043,
 .binary .add 4055 4044 4052,.store 4055 4054]
def lower : List Op := [.binary .add 4056 4053 4047]
def upper : List Op := [.binary .sub 4056 4053 4045]
def representative : List Op := [.binary .mul 4055 4052 4051,
 .binary .add 4055 4055 4056,.binary .add 4055 4055 4040,
 .binary .add 4055 4055 4044,.store 4055 4049]
def advance : List Op := [.binary .mul 4049 4049 4046,.binary .add 4048 4048 4045]
def program : Program := boot.map Op.code++[.branchLT 4048 4050 8 28]++positions.map Op.code++
 [.branchLT 4053 4045 11 15]++selected.map Op.code++[.jump 15,.branchLT 4053 4042 19 16,
 .branchLT 4042 4053 17 25]++upper.map Op.code++[.jump 20]++lower.map Op.code++
 representative.map Op.code++advance.map Op.code++[.jump 7,.halt]
theorem program_length : program.length=29 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<7 at hi;interval_cases i <;> rfl
theorem positions_code : BlockAt positions program 8 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem selected_code : BlockAt selected program 11 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem lower_code : BlockAt lower program 19 := by intro i hi;change i<1 at hi;interval_cases i;rfl
theorem upper_code : BlockAt upper program 17 := by intro i hi;change i<1 at hi;interval_cases i;rfl
theorem representative_code : BlockAt representative program 20 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem advance_code : BlockAt advance program 25 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem branch_at : program[7]?=some (.branchLT 4048 4050 8 28) := rfl
theorem selected_at : program[10]?=some (.branchLT 4053 4045 11 15) := rfl
theorem selected_jump : program[14]?=some (.jump 15) := rfl
theorem low_at : program[15]?=some (.branchLT 4053 4042 19 16) := rfl
theorem high_at : program[16]?=some (.branchLT 4042 4053 17 25) := rfl
theorem high_jump : program[18]?=some (.jump 20) := rfl
theorem loop_at : program[27]?=some (.jump 7) := rfl
theorem halt_at : program[28]?=some .halt := rfl

structure Control (q w p mask A j : ℕ) (s : State) : Prop where
 pc : s.pc=7
 columns : s.natReg 4040=q
 width : s.natReg 4041=w
 pivot : s.natReg 4042=p
 mask : s.natReg 4043=mask
 base : s.natReg 4044=A
 one : s.natReg 4045=1
 two : s.natReg 4046=2
 zero : s.natReg 4047=0
 index : s.natReg 4048=j
 place : s.natReg 4049=2^j
 length : s.natReg 4050=q*w
 reduced : s.natReg 4051=w-1

/-- Source-coordinate ordering, with the pivot removed in every column. -/
def omitted (p i : ℕ) : ℕ := if i<p then i else i-1
def repSlot (q w p j : ℕ) : ℕ := q+(j/w)*(w-1)+omitted p (j%w)

def Partial (q w p mask A j : ℕ) (s : State) : Prop :=
 (∀c, c<q → c*w<j → s.natHeap (A+c)=some (2^(c*w)*mask)) ∧
 (∀t, t<j → t%w≠p → s.natHeap (A+repSlot q w p t)=some (2^t))

structure Frame (A length : ℕ) (s u : State) : Prop where
 outside : ∀z, z<A ∨ A+length≤z → u.natHeap z=s.natHeap z
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r, r<4045 ∨ 4056<r → u.natReg r=s.natReg r
lemma Frame.refl (A length : ℕ) (s : State) : Frame A length s s := ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.trans {A length : ℕ} {s u v : State} (f : Frame A length s u) (g : Frame A length u v) : Frame A length s v :=
 ⟨fun z h=>(g.outside z h).trans (f.outside z h),g.scalarHeap.trans f.scalarHeap,
  g.scalarReg.trans f.scalarReg,g.outputs.trans f.outputs,g.roots.trans f.roots,
  fun r h=>(g.natReg r h).trans (f.natReg r h)⟩

lemma slot_bounds (q w p j : ℕ) (wp : 0<w) (pp : p<w) (jp : j<q*w) (different : j%w≠p) :
 q≤repSlot q w p j ∧ repSlot q w p j<q*w := by
 have col:= (Nat.div_lt_iff_lt_mul wp).2 jp
 have rem:=Nat.mod_lt j wp
 have adjust : omitted p (j%w)<w-1 := by unfold omitted;split <;> omega
 have wm : 0<w-1 := by omega
 have rhs := Nat.mul_le_mul_right (w-1) (show j/w+1≤q by omega)
 simp only [Nat.add_mul,Nat.one_mul] at rhs
 have shape : q*(w-1)+q=q*w := by
  calc
   q*(w-1)+q=q*((w-1)+1) := by ring
   _=q*w := by congr 1;omega
 simp only [repSlot]
 constructor
 · omega
 · nlinarith

lemma selected_bounds (q w mask j : ℕ) (wp : 0<w) (small : mask<2^w)
 (jp : j<q*w) (zero : j%w=0) : 2^j*mask<2^(q*w) := by
 have div:=Nat.div_add_mod j w
 rw [Nat.mul_comm w (j/w)] at div
 have block : j+w≤q*w := by
  have col:= (Nat.div_lt_iff_lt_mul wp).2 jp
  have mul:=Nat.mul_le_mul_right w (show j/w+1≤q by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mul
  omega
 have term:=Nat.mul_lt_mul_of_pos_left small (Nat.two_pow_pos j)
 rw [←Nat.pow_add] at term
 exact term.trans_le (Nat.pow_le_pow_right (by omega : 1≤2) block)


lemma slot_injective (q w p t j : ℕ) (wp : 0<w) (pp : p<w)
 (_tp : t<q*w) (_jp : j<q*w) (tn : t%w≠p) (jn : j%w≠p)
 (eq : repSlot q w p t=repSlot q w p j) : t=j := by
 have tr:=Nat.mod_lt t wp
 have jr:=Nat.mod_lt j wp
 have adjT : omitted p (t%w)<w-1 := by unfold omitted;split <;> omega
 have aj : omitted p (j%w)<w-1 := by unfold omitted;split <;> omega
 have positive : 0<w-1:=by omega
 have vals : (t/w)*(w-1)+omitted p (t%w)=(j/w)*(w-1)+omitted p (j%w) := by
  unfold repSlot at eq;omega
 have cols : t/w=j/w := by
  rcases lt_trichotomy (t/w) (j/w) with lt|eq|gt
  · have bound:=Nat.mul_le_mul_right (w-1) (show t/w+1≤j/w by omega)
    simp only [Nat.add_mul,Nat.one_mul] at bound
    omega
  · exact eq
  · have bound:=Nat.mul_le_mul_right (w-1) (show j/w+1≤t/w by omega)
    simp only [Nat.add_mul,Nat.one_mul] at bound
    omega
 have remainders : t%w=j%w := by
  rw [cols] at vals
  have adj : omitted p (t%w)=omitted p (j%w) := by omega
  unfold omitted at adj
  split_ifs at adj <;> omega
 have te:=Nat.div_add_mod t w
 have je:=Nat.div_add_mod j w
 rw [cols,remainders] at te
 omega

def picked (s : State) : State :=
 if s.natReg 4053=0 then {applyBlock selected {s with pc:=11} with pc:=15}
 else {s with pc:=15}
def represented (s : State) : State :=
 if s.natReg 4053<s.natReg 4042 then
  applyBlock representative (applyBlock lower {s with pc:=19})
 else if s.natReg 4042<s.natReg 4053 then
  applyBlock representative {applyBlock upper {s with pc:=17} with pc:=20}
 else {s with pc:=25}
def round (s : State) : State :=
 let pos:=applyBlock positions {s with pc:=8}
 let copied:=represented (picked pos)
 {applyBlock advance copied with pc:=7}
def roundCost (w p j : ℕ) : ℕ :=
 6+(if j%w=0 then 5 else 1)+(if j%w<p then 7 else if p<j%w then 9 else 2)
lemma roundCost_bound (w p j : ℕ) : roundCost w p j≤20 := by
 unfold roundCost;split_ifs <;> omega

lemma round_control (q w p mask A j : ℕ) (s : State) (c : Control q w p mask A j s)
 (wp : 0<w) (_pp : p<w) : Control q w p mask A (j+1) (round s) := by
 have wn : w≠0:=by omega
 constructor <;> simp [round,represented,picked,positions,selected,lower,upper,representative,
  advance,applyBlock,Op.apply,evalNat,writeNat,next,c.columns,c.width,c.pivot,c.mask,c.base,
  c.one,c.two,c.zero,c.index,c.place,c.length,c.reduced,Nat.pow_succ,wn]
 all_goals split_ifs <;> simp_all [applyBlock,Op.apply,evalNat,writeNat,next,
  c.columns,c.width,c.pivot,c.mask,c.base,c.one,c.two,c.zero,c.index,c.place,c.length,c.reduced,Nat.pow_succ]

lemma round_heap (q w p mask A j : ℕ) (s : State) (c : Control q w p mask A j s) (wp : 0<w) :
 (round s).natHeap=
 let first := if j%w=0 then Function.update s.natHeap (A+j/w) (some (2^j*mask)) else s.natHeap
 if j%w=p then first else Function.update first (A+repSlot q w p j) (some (2^j)) := by
 have wn : w≠0:=by omega
 simp [round,represented,picked,positions,selected,lower,upper,representative,advance,
  applyBlock,Op.apply,evalNat,writeNat,next,c.columns,c.width,c.pivot,c.mask,c.base,
  c.one,c.two,c.zero,c.index,c.place,c.length,c.reduced,repSlot,omitted,wn]
 split_ifs <;> simp_all [applyBlock,Op.apply,evalNat,writeNat,next,
  c.columns,c.width,c.pivot,c.mask,c.base,c.one,c.two,c.zero,c.index,c.place,c.length,c.reduced,repSlot,omitted,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] <;> omega


lemma round_frame (q w p mask A j : ℕ) (s : State) (c : Control q w p mask A j s)
 (wp : 0<w) (pp : p<w) (jp : j<q*w) : Frame A (q*w) s (round s) := by
 have collt : j/w<q:=(Nat.div_lt_iff_lt_mul wp).2 jp
 have qle : q≤q*w:=Nat.le_mul_of_pos_right _ wp
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro z outside
   have rangeSel : A≤A+(j/w) ∧ A+(j/w)<A+q*w :=
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (collt.trans_le qle) A⟩
   have neSel : z≠A+(j/w) := by omega
   have first :
    (if j%w=0 then Function.update s.natHeap (A+j/w) (some (2^j*mask)) else s.natHeap) z=s.natHeap z := by
    split_ifs <;> simp [Function.update_of_ne neSel]
   rw [round_heap q w p mask A j s c wp]
   dsimp
   by_cases equal:j%w=p
   · simpa only [ite_eq_left equal] using first
   · have slot:=slot_bounds q w p j wp pp jp equal
     simpa only [ite_eq_right equal,Function.update_of_ne (show z≠A+repSlot q w p j by omega)] using first
 · simp [round,represented,picked];split_ifs <;> rfl
 · simp [round,represented,picked];split_ifs <;> rfl
 · simp [round,represented,picked];split_ifs <;> rfl
 · simp [round,represented,picked];split_ifs <;> rfl
 · intro r keep
   simp [round,represented,picked]
   split_ifs <;> simp (disch:=omega) [advance,positions,selected,lower,upper,representative,
    applyBlock,Op.apply,writeNat,next]

lemma round_partial (q w p mask A j : ℕ) (s : State) (c : Control q w p mask A j s)
 (wp : 0<w) (pp : p<w) (jp : j<q*w) (part : Partial q w p mask A j s) :
 Partial q w p mask A (j+1) (round s) := by
 have collt : j/w<q:=(Nat.div_lt_iff_lt_mul wp).2 jp
 have div:=Nat.div_add_mod j w
 rw [Nat.mul_comm w (j/w)] at div
 constructor
 · intro column cp visited
   have oldOr : column*w<j ∨ column*w=j:=by omega
   have selectedNow :
    (if j%w=0 then Function.update s.natHeap (A+j/w) (some (2^j*mask)) else s.natHeap)
     (A+column)=some (2^(column*w)*mask) := by
    rcases oldOr with old|equal
    · by_cases zero:j%w=0
      · have distinct : column≠j/w := by intro same;rw [same] at old;omega
        simp [zero,Function.update_of_ne (show A+column≠A+j/w by omega),part.1 column cp old]
      · simp [zero,part.1 column cp old]
    · have col : j/w=column := by rw [←equal];exact Nat.mul_div_cancel _ wp
      have zero : j%w=0 := by rw [←equal];exact Nat.mul_mod_left _ _
      simp [zero,col,equal]
   rw [round_heap q w p mask A j s c wp]
   dsimp
   by_cases same:j%w=p
   · simpa [same] using selectedNow
   · have slot:=slot_bounds q w p j wp pp jp same
     simp only [ite_eq_right same,Function.update_of_ne (show A+column≠A+repSlot q w p j by omega)]
     exact selectedNow
 · intro t visited notPivot
   have tp : t<q*w:=by omega
   have slotT:=slot_bounds q w p t wp pp tp notPivot
   have oldOr : t<j ∨ t=j:=by omega
   rw [round_heap q w p mask A j s c wp]
   dsimp
   rcases oldOr with old|equal
   · have earlier :=part.2 t old notPivot
     have first :
      (if j%w=0 then Function.update s.natHeap (A+j/w) (some (2^j*mask)) else s.natHeap)
       (A+repSlot q w p t)=some (2^t) := by
      by_cases zero:j%w=0
      · simp [zero,Function.update_of_ne (show A+repSlot q w p t≠A+j/w by omega),earlier]
      · simpa [zero] using earlier
     by_cases same:j%w=p
     · simpa [same] using first
     · have neq : repSlot q w p t≠repSlot q w p j := by
        intro eq
        have equal:=slot_injective q w p t j wp pp tp jp notPivot same eq
        omega
       simpa [same,Function.update_of_ne (show A+repSlot q w p t≠A+repSlot q w p j by omega)] using first
   · subst t
     simp [notPivot]

end
end ExactFourierCircuits.UniformResidualBasisMachine
