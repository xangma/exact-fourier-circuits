import UniformRadixInstructionMachine
import UniformNewtonTableMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformRadixRowTableMachine
open UniformMachine UniformPreparationMachine UniformRadixTwoDAG

/-- Nat70=height; Nat107=chosen natural-heap table base; Nat122=scalar operand offset. Prepared power values
are not read or produced by this natural-only table printer. -/
def setup : List UniformRadixInstructionMachine.AOp := [.lit 108 1,.lit 109 0,.lit 112 0,.lit 113 1,
  .lit 114 2,.lit 115 3,.lit 116 5]
def grow : List UniformRadixInstructionMachine.AOp := [.bin .mul 108 108 114,.bin .add 109 109 113]
def sizes : List UniformRadixInstructionMachine.AOp := [.bin .mul 109 115 70,.bin .mul 109 109 108,
  .bin .div 109 109 114,.bin .add 117 108 109,.lit 71 0,.bin .add 111 107 112]
def head : Program := setup.map UniformRadixInstructionMachine.AOp.code ++ [.branchLT 109 70 8 11] ++
  grow.map UniformRadixInstructionMachine.AOp.code ++ [.jump 7] ++ sizes.map UniformRadixInstructionMachine.AOp.code ++ [.branchLT 71 109 18 113]
def binary : List UniformRadixInstructionMachine.AOp := [.bin .add 119 90 112,.bin .add 120 92 112,.bin .add 121 93 112]
def scale : List UniformRadixInstructionMachine.AOp := [.lit 119 2,.bin .add 121 92 112]
def positivePower : List UniformRadixInstructionMachine.AOp := [.bin .mul 118 116 91,.bin .sub 118 118 114]
def shiftOperands : List UniformRadixInstructionMachine.AOp := [.bin .add 120 120 122,.bin .add 121 121 122]
def stores : List UniformNewtonTableMachine.Op := [.putNat 111 119,.add 111 111 113,.putNat 111 120,
  .add 111 111 113,.putNat 111 121,.add 111 111 113,.add 71 71 113]
def tail : Program := [.branchLT 90 114 91 95] ++ binary.map UniformRadixInstructionMachine.AOp.code ++ [.jump 103] ++
  scale.map UniformRadixInstructionMachine.AOp.code ++ [.branchLT 91 113 98 100,.natLiteral 118 1,.jump 102] ++
  positivePower.map UniformRadixInstructionMachine.AOp.code ++ [.natBinary .add 120 117 118] ++ shiftOperands.map UniformRadixInstructionMachine.AOp.code ++ stores.map UniformNewtonTableMachine.Op.code ++
  [.jump 17,.halt]
def program : Program := UniformAssembly.embed head UniformRadixInstructionMachine.program tail 90

theorem head_length : head.length=18 := rfl
theorem tail_length : tail.length=24 := rfl
theorem program_length : program.length=114 := by rw [program,UniformAssembly.embed_length,head_length,UniformRadixInstructionMachine.program_length,tail_length]
theorem decoder_code : UniformAssembly.CodeAt UniformRadixInstructionMachine.program program 18 90 := by
  simpa only [head_length,program] using UniformAssembly.embed_code head UniformRadixInstructionMachine.program tail 90

theorem coefficient_address (K c:ℕ) (hc:c<width K) :
    UniformRadixTwoMachine.coefficientAddress K c=width K+count K+UniformNewtonTableMachine.powerIndex c := by
  unfold UniformRadixTwoMachine.coefficientAddress
  rw [dite_eq_left hc]
  change (width K+count K)+(UniformNewton.Preparation.powerRef c).val=_
  rw [UniformNewtonTableMachine.powerRef_val]

/-- Physical preparation addresses still refer to the shared Newton power DAG. -/
theorem coefficient_zero (K:ℕ) : UniformRadixTwoMachine.coefficientAddress K 0=width K+count K+1 := by
  rw [coefficient_address K 0 (width_pos K)];rfl

theorem raw_scale_bound (K:ℕ) (j:Fin (count K)) (s:State)
    (h:UniformRadixInstructionMachine.rawInstruction s=instruction K j) (hop:¬s.natReg 90<2) : s.natReg 91<width K := by
  have h0:s.natReg 90≠0:=by omega
  have h1:s.natReg 90≠1:=by omega
  apply instruction_scalar_bound K j
  rw [←h]
  simp [UniformRadixInstructionMachine.rawInstruction,h0,h1,Op.scalars]

structure Constants (s:State) : Prop where
  zero:s.natReg 112=0
  one:s.natReg 113=1
  two:s.natReg 114=2
  three:s.natReg 115=3
  five:s.natReg 116=5

structure Context (K d a j:ℕ) (s:State) : Prop extends Constants s where
  scalarBase:s.natReg 122=a
  height:s.natReg 70=K
  base:s.natReg 107=d
  Nreg:s.natReg 108=width K
  Greg:s.natReg 109=count K
  index:s.natReg 71=j
  pointer:s.natReg 111=d+3*j
  prep:s.natReg 117=width K+count K

def controls : List ℕ := [70,71,107,108,109,111,112,113,114,115,116,117,122]

theorem Constants.withPC {s:State} {pc:ℕ} (h:Constants s) : Constants {s with pc:=pc} := by
  cases h;constructor <;> assumption

theorem Context.withPC {K d a j pc:ℕ} {s:State} (h:Context K d a j s) : Context K d a j {s with pc:=pc} := by
  cases h with | mk hc ha hk hd hn hg hi hp hr => exact ⟨hc.withPC,ha,hk,hd,hn,hg,hi,hp,hr⟩

theorem Context.congr {K d a j:ℕ} {s u:State} (h:Context K d a j s)
    (hk:∀r∈controls,u.natReg r=s.natReg r) : Context K d a j u := by
  constructor
  · constructor <;> (rw [hk _ (by simp [controls])];first | exact h.zero | exact h.one | exact h.two | exact h.three | exact h.five)
  all_goals rw [hk _ (by simp [controls])];first | exact h.scalarBase | exact h.height | exact h.base | exact h.Nreg | exact h.Greg | exact h.index | exact h.pointer | exact h.prep

theorem Context.write {K d a j:ℕ} {s:State} (h:Context K d a j s) (dst value:ℕ) (hd:dst∉controls) :
    Context K d a j (writeNat s dst value) := h.congr (fun r hr=>by
      simp [writeNat,next,Function.update_of_ne (show r≠dst from fun he=>hd (he ▸ hr))])

theorem Context.block {K d a j:ℕ} {s:State} (h:Context K d a j s) (b:List UniformRadixInstructionMachine.AOp)
    (hb:∀o∈b,o.dst∉controls) : Context K d a j (UniformRadixInstructionMachine.block b s) :=
  h.congr (fun r hr=>UniformRadixInstructionMachine.block_keeps b s r (fun o ho he=>hb o ho (he ▸ hr)))

def RowFields (row:Row) (s:State) : Prop := s.natReg 119=opcode row.op ∧
  s.natReg 120=row.left ∧ s.natReg 121=row.right

def Outside (d m:ℕ) (heap:ℕ→Option ℕ) (s:State) : Prop := ∀i,(i < d ∨ d+m ≤ i)→s.natHeap i=heap i

def shiftRow (a:ℕ) (row:Row) : Row := ⟨row.op,a+row.left,a+row.right⟩

def Printed (K d a j:ℕ) (s:State) : Prop := ∀q:Fin (count K),q.val<j→
  s.natHeap (d+3*q.val)=some (opcode (shiftRow a (UniformRadixTwoMachine.row K q)).op) ∧
  s.natHeap (d+3*q.val+1)=some (shiftRow a (UniformRadixTwoMachine.row K q)).left ∧
  s.natHeap (d+3*q.val+2)=some (shiftRow a (UniformRadixTwoMachine.row K q)).right

def allocation (K d a:ℕ) : ℕ := a+UniformRadixInstructionMachine.cap (width K) (count K) K+d+3*count K

theorem allocation_bound (K d a:ℕ) : allocation K d a ≤ a+d+2^(4*K+13) := by
  have hl:=UniformRadixInstructionMachine.cap_linear (width K) (count K) K
  have hp:=UniformRadixInstructionMachine.cap_power K
  have hg:3*count K ≤ UniformRadixInstructionMachine.cap (width K) (count K) K:=by omega
  have he:2^(4*K+13)=2*2^(4*K+12):=by rw [show 4*K+13=(4*K+12)+1 by omega,pow_succ];ring
  unfold allocation;rw [he];omega



open UniformRadixInstructionMachine

theorem block_heap (b:List AOp) (s:State) : (block b s).natHeap=s.natHeap := by
  induction b generalizing s with
  | nil => rfl
  | cons o os ih => rw [block,ih];cases o <;> rfl


structure Initializing (K d a t:ℕ) (s:State) : Prop extends Constants s where
  height:s.natReg 70=K
  base:s.natReg 107=d
  scalarBase:s.natReg 122=a
  Nreg:s.natReg 108=width t
  index:s.natReg 109=t

theorem Initializing.withPC {K d a t pc:ℕ} {s:State} (h:Initializing K d a t s) :
    Initializing K d a t {s with pc:=pc} := by
  cases h with | mk hc hk hd ha hn hi => exact ⟨hc.withPC,hk,hd,ha,hn,hi⟩

theorem setup_at : BlockAt setup program 0 := by intro j;fin_cases j <;> rfl
theorem grow_at : BlockAt grow program 8 := by intro j;fin_cases j <;> rfl
theorem sizes_at : BlockAt sizes program 11 := by intro j;fin_cases j <;> rfl
theorem binary_at : BlockAt binary program 91 := by intro j;fin_cases j <;> rfl
theorem scale_at : BlockAt scale program 95 := by intro j;fin_cases j <;> rfl
theorem positive_at : BlockAt positivePower program 100 := by intro j;fin_cases j <;> rfl
theorem shift_at : BlockAt shiftOperands program 103 := by intro j;fin_cases j <;> rfl
theorem stores_at : UniformNewtonTableMachine.BlockAt stores program 105 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl

theorem setup_spec (K d a:ℕ) (s:State) (hk:s.natReg 70=K) (hd:s.natReg 107=d)
    (ha:s.natReg 122=a) : Initializing K d a 0 (block setup s) := by
  constructor
  · constructor <;> rfl
  all_goals simp [block,setup,AOp.apply,AOp.value,writeNat,next,hk,hd,ha,width]

theorem setup_valid (s:State) : validBlock setup s := by simp [validBlock,setup,AOp.valid]
theorem setup_peak (s:State) : peakBlock setup s=5 := rfl

theorem grow_spec (K d a t:ℕ) (s:State) (h:Initializing K d a t s) :
    Initializing K d a (t+1) (block grow s) := by
  constructor
  · constructor <;> simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three,h.five]
  all_goals simp [block,grow,AOp.apply,AOp.value,evalNat,writeNat,next,
    h.height,h.base,h.scalarBase,h.Nreg,h.index,h.one,h.two,width,Nat.mul_two]

theorem grow_valid (s:State) : validBlock grow s := by simp [validBlock,grow,AOp.valid,evalNat]
theorem grow_peak (K d a t:ℕ) (s:State) (h:Initializing K d a t s) (ht:t<K) :
    peakBlock grow s ≤ cap (width K) (count K) K := by
  have hw:=width_mono (show t≤K by omega)
  have hl:=cap_linear (width K) (count K) K
  simp [peakBlock,grow,AOp.apply,AOp.value,evalNat,writeNat,next,h.Nreg,h.index,h.one,h.two]
  constructor <;> omega

/-- All width/count setup operations are charged, including the doubling loop. -/
theorem initialize_loop (n K d a t fuel B:ℕ) (x:Fin n→ℂ) (s:State)
    (h:Initializing K d a t s) (ht:t+fuel=K) (hs:WordBound B s)
    (hB:cap (width K) (count K) K ≤ B) (hp:s.pc=7) : ∃u,
    BoundedRuns program n x B s (4*fuel+1) u ∧ Initializing K d a K u ∧ u.pc=11 ∧ u.natHeap=s.natHeap := by
  have hcode:100≤B:=(cap_code _ _ _).trans hB
  induction fuel generalizing t s with
  | zero =>
    have he:t=K:=by omega
    subst t
    have hb:=branch_runs program n B 109 70 8 11 x s hs (by omega) (by omega) (by rw [hp];rfl)
    have he:¬s.natReg 109<s.natReg 70:=by rw [h.index,h.height];omega
    simp only [he,ite_false] at hb
    exact ⟨_,by simpa using hb,h.withPC,rfl,rfl⟩
  | succ fuel ih =>
    have htK:t<K:=by omega
    have hb:=branch_runs program n B 109 70 8 11 x s hs (by omega) (by omega) (by rw [hp];rfl)
    have he:s.natReg 109<s.natReg 70:=by rw [h.index,h.height];exact htK
    simp only [he,ite_true] at hb
    let v:State:={s with pc:=8}
    have hg:=block_runs grow program 8 n B x v grow_at rfl hb.final_bound (by change 8+2≤B;omega)
      (grow_valid v) ((grow_peak K d a t v h.withPC htK).trans hB)
    have hv:=grow_spec K d a t v h.withPC
    have hpc:(block grow v).pc=10:=by rw [block_pc];rfl
    have hj:=jump_runs program n B 7 x (block grow v) hg.final_bound (by omega) (by rw [hpc];rfl)
    obtain ⟨u,hu,hi,hpu,hheap⟩:=ih (t+1) {block grow v with pc:=7} hv.withPC (by omega) hj.final_bound rfl
    refine ⟨u,?_,hi,hpu,?_⟩
    · convert hb.trans (hg.trans (hj.trans hu)) using 1
      simp only [show grow.length=2 from rfl];omega
    · exact hheap.trans (by dsimp [v];exact block_heap grow _)

theorem sizes_valid (s:State) (h:s.natReg 114=2) : validBlock sizes s := by
  simp [validBlock,sizes,AOp.valid,AOp.apply,AOp.value,evalNat,writeNat,next,h]

theorem sizes_spec (K d a:ℕ) (s:State) (h:Initializing K d a K s) :
    Context K d a 0 (block sizes s) := by
  constructor
  · constructor <;> simp [block,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,h.one,h.two,h.three,h.five]
  all_goals simp [block,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,
    h.height,h.base,h.scalarBase,h.Nreg,h.zero,h.two,h.three,count_div]

theorem sizes_peak (K d a:ℕ) (s:State) (h:Initializing K d a K s) :
    peakBlock sizes s ≤ cap (width K) (count K) K+d := by
  have hl:=cap_linear (width K) (count K) K
  have he:3*K*width K=2*count K:=by have he:=count_exact K;omega
  simp [peakBlock,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,
    h.height,h.base,h.Nreg,h.zero,h.two,h.three,count_div]
  all_goals omega



theorem code_bound (K:ℕ) : 114≤cap (width K) (count K) K := by unfold cap;omega

theorem one_runs (o:AOp) (pc n B:ℕ) (x:Fin n→ℂ) (s:State)
    (hp:s.pc=pc) (hc:program[pc]?=some o.code) (hs:WordBound B s)
    (hpc:pc+1≤B) (hv:o.valid s) (hval:o.value s≤B) :
    BoundedRuns program n x B s 1 (o.apply s) := by
  have hu:WordBound B (o.apply s):=by cases o <;> exact writeNat_bound B s _ _ hs (by omega) hval
  exact .next hs (AOp.step o program n x s (by rw [hp];exact hc) hv) (.refl hu)


theorem adapter_valid (s:State) : validBlock binary s ∧ validBlock scale s ∧
    validBlock positivePower s ∧ validBlock shiftOperands s := by
  simp [validBlock,binary,scale,positivePower,shiftOperands,AOp.valid,evalNat]

theorem adapter_keep : (∀o∈binary,o.dst∉controls) ∧ (∀o∈scale,o.dst∉controls) ∧
    (∀o∈positivePower,o.dst∉controls) ∧ (∀o∈shiftOperands,o.dst∉controls) := by
  simp [binary,scale,positivePower,shiftOperands,AOp.dst,controls]

theorem row_bounds (K:ℕ) (q:Fin (count K)) :
    (UniformRadixTwoMachine.row K q).left≤cap (width K) (count K) K ∧
    (UniformRadixTwoMachine.row K q).right≤cap (width K) (count K) K := by
  have hr:=UniformRadixTwoMachine.row_addresses K q
  rw [UniformRadixTwoMachine.prepBase,powers_length] at hr
  have hl:=cap_linear (width K) (count K) K
  constructor <;> omega

theorem binary_spec (K d a j:ℕ) (q:Fin (count K)) (s:State) (h:Context K d a j s)
    (hr:rawInstruction s=instruction K q) (hop:s.natReg 90<2) :
    RowFields (UniformRadixTwoMachine.row K q) (block binary s) := by
  have he:UniformRadixTwoMachine.row K q=UniformRadixTwoMachine.rowOf K (rawInstruction s):=by rw [hr];rfl
  rw [he]
  by_cases h0:s.natReg 90=0
  · simp [RowFields,block,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,
      rawInstruction,h0,UniformRadixTwoMachine.rowOf,opcode]
  · have h1:s.natReg 90=1:=by omega
    simp [RowFields,block,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero,
      rawInstruction,h1,UniformRadixTwoMachine.rowOf,opcode]

theorem binary_peak (K d a j:ℕ) (q:Fin (count K)) (s:State) (h:Context K d a j s)
    (hr:rawInstruction s=instruction K q) (hop:s.natReg 90<2) :
    peakBlock binary s≤cap (width K) (count K) K := by
  have hb:=row_bounds K q
  have he:UniformRadixTwoMachine.row K q=UniformRadixTwoMachine.rowOf K (rawInstruction s):=by rw [hr];rfl
  rw [he] at hb
  by_cases h0:s.natReg 90=0
  · simp [rawInstruction,h0,UniformRadixTwoMachine.rowOf] at hb
    have hc:=cap_code (width K) (count K) K
    simp [peakBlock,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero]
    all_goals omega
  · have h1:s.natReg 90=1:=by omega
    simp [rawInstruction,h1,UniformRadixTwoMachine.rowOf] at hb
    have hc:=cap_code (width K) (count K) K
    simp [peakBlock,binary,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero]
    all_goals omega

theorem scale_source (K:ℕ) (q:Fin (count K)) (s:State)
    (hr:rawInstruction s=instruction K q) (hop:¬s.natReg 90<2) :
    UniformRadixTwoMachine.row K q=⟨.mul,UniformRadixTwoMachine.coefficientAddress K (s.natReg 91),s.natReg 92⟩ := by
  have h0:s.natReg 90≠0:=by omega
  have h1:s.natReg 90≠1:=by omega
  have he:UniformRadixTwoMachine.row K q=UniformRadixTwoMachine.rowOf K (rawInstruction s):=by rw [hr];rfl
  simpa [rawInstruction,h0,h1,UniformRadixTwoMachine.rowOf] using he

theorem shift_spec (a:ℕ) (row:Row) (s:State) (ha:s.natReg 122=a) (h:RowFields row s) :
    RowFields (shiftRow a row) (block shiftOperands s) := by
  simp [RowFields,shiftRow,block,shiftOperands,AOp.apply,AOp.value,evalNat,writeNat,next,ha,h.1,h.2.1,h.2.2,Nat.add_comm]

theorem shift_peak (a capB:ℕ) (row:Row) (s:State) (ha:s.natReg 122=a) (h:RowFields row s)
    (hl:row.left≤capB) (hr:row.right≤capB) : peakBlock shiftOperands s≤a+capB := by
  simp [peakBlock,shiftOperands,AOp.apply,AOp.value,evalNat,writeNat,next,ha,h.2.1,h.2.2];omega



/-- The coefficient-address adapter executes six literal instructions on either
scale branch; it does not read a scalar value or a prepared table. -/
theorem scale_path (n K d a j B:ℕ) (q:Fin (count K)) (x:Fin n→ℂ) (s:State)
    (h:Context K d a j s) (hr:rawInstruction s=instruction K q) (hop:¬s.natReg 90<2)
    (hs:WordBound B s) (hB:cap (width K) (count K) K≤B) (hp:s.pc=95) : ∃u,
    BoundedRuns program n x B s 6 u ∧ Context K d a j u ∧ u.pc=103 ∧
    RowFields (UniformRadixTwoMachine.row K q) u ∧ u.natHeap=s.natHeap := by
  have hc:114≤B:=(code_bound K).trans hB
  have he:=scale_source K q s hr hop
  have hx:=raw_scale_bound K q s hr hop
  have hsrc:(s.natReg 92)≤cap (width K) (count K) K:=by
    have hb:=(row_bounds K q).2;rw [he] at hb;exact hb
  have hl:=cap_linear (width K) (count K) K
  have hscale:=block_runs scale program 95 n B x s scale_at hp hs (by change 95+2≤B;omega)
    (adapter_valid s).2.1 (by simp [peakBlock,scale,AOp.value,AOp.apply,evalNat,writeNat,next,h.zero];omega)
  let v:=block scale s
  have hv:Context K d a j v:=h.block scale adapter_keep.2.1
  have hpv:v.pc=97:=by dsimp [v];rw [block_pc,hp];rfl
  have hb:=branch_runs program n B 91 113 98 100 x v hscale.final_bound (by omega) (by omega) (by rw [hpv];rfl)
  have hv91:v.natReg 91=s.natReg 91:=by simp [v,block,scale,AOp.apply,AOp.value,writeNat,next]
  have hv121:v.natReg 121=s.natReg 92:=by simp [v,block,scale,AOp.apply,AOp.value,evalNat,writeNat,next,h.zero]
  have hv119:v.natReg 119=2:=by simp [v,block,scale,AOp.apply,AOp.value,writeNat,next]
  have hfinish : ∀w:State, Context K d a j w→w.pc=102→WordBound B w→
      w.natReg 118=UniformNewtonTableMachine.powerIndex (s.natReg 91)→w.natReg 121=s.natReg 92→
      w.natReg 119=2→w.natHeap=s.natHeap→∃u,
      BoundedRuns program n x B w 1 u ∧ Context K d a j u ∧ u.pc=103 ∧
      RowFields (UniformRadixTwoMachine.row K q) u ∧ u.natHeap=s.natHeap := by
    intro w hw hpw hsw hpow hright hopw hheap
    have hleft:width K+count K+UniformNewtonTableMachine.powerIndex (s.natReg 91)≤cap (width K) (count K) K:=by
      have hrow:=(row_bounds K q).1;rw [he,coefficient_address K _ hx] at hrow;exact hrow
    have hrun:=one_runs (.bin .add 120 117 118) 102 n B x w hpw rfl hsw (by omega)
      (by simp [AOp.valid,evalNat]) (by simp [AOp.value,evalNat,hw.prep,hpow];omega)
    refine ⟨AOp.apply (.bin .add 120 117 118) w,hrun,hw.write 120 _ (by simp [controls]),?_,?_,?_⟩
    · rw [AOp.pc,hpw]
    · rw [he,coefficient_address K _ hx]
      simp [RowFields,AOp.apply,AOp.value,evalNat,writeNat,next,hw.prep,hpow,hright,hopw,opcode]
    · exact hheap
  by_cases hz:s.natReg 91=0
  · have cond:v.natReg 91<v.natReg 113:=by rw [hv91,hv.one,hz];omega
    simp only [cond,ite_true] at hb
    let z:State:={v with pc:=98}
    have hzero:=one_runs (.lit 118 1) 98 n B x z rfl rfl hb.final_bound (by omega)
      (by trivial) (by simp [AOp.value];omega)
    have hpz:(AOp.apply (.lit 118 1) z).pc=99:=rfl
    have hj:=jump_runs program n B 102 x (AOp.apply (.lit 118 1) z) hzero.final_bound (by omega) (by rw [hpz];rfl)
    let w:State:={AOp.apply (.lit 118 1) z with pc:=102}
    have hw:Context K d a j w:=(hv.withPC (pc:=98)).write 118 1 (by simp [controls]) |>.withPC
    obtain ⟨u,hu,hui,hpu,hrow,hheap⟩:=hfinish w hw rfl hj.final_bound
      (by simp [w,AOp.apply,AOp.value,writeNat,next,hz,UniformNewtonTableMachine.powerIndex])
      (by simpa [w,z,AOp.apply,AOp.value,writeNat,next] using hv121)
      (by simpa [w,z,AOp.apply,AOp.value,writeNat,next] using hv119)
      (by simp [w,z,v,AOp.apply,writeNat,next,block_heap])
    refine ⟨u,?_,hui,hpu,hrow,hheap⟩
    convert hscale.trans (hb.trans (hzero.trans (hj.trans hu))) using 1;rfl
  · have cond:¬v.natReg 91<v.natReg 113:=by rw [hv91,hv.one];omega
    simp only [cond,ite_false] at hb
    let z:State:={v with pc:=100}
    have hpos:=block_runs positivePower program 100 n B x z positive_at rfl hb.final_bound
      (by change 100+2≤B;omega) (adapter_valid z).2.2.1
      (by simp [peakBlock,positivePower,AOp.value,AOp.apply,evalNat,writeNat,next,z,hv.five,hv.two,hv91];omega)
    let w:=block positivePower z
    have hw:Context K d a j w:=hv.withPC (pc:=100) |>.block positivePower adapter_keep.2.2.1
    have hpw:w.pc=102:=by dsimp [w];rw [block_pc];rfl
    obtain ⟨u,hu,hui,hpu,hrow,hheap⟩:=hfinish w hw hpw hpos.final_bound
      (by simp [w,z,block,positivePower,AOp.apply,AOp.value,evalNat,writeNat,next,hv.five,hv.two,hv91,UniformNewtonTableMachine.powerIndex,hz])
      (by simpa [w,z,block,positivePower,AOp.apply,AOp.value,evalNat,writeNat,next] using hv121)
      (by simpa [w,z,block,positivePower,AOp.apply,AOp.value,evalNat,writeNat,next] using hv119)
      (by simp [w,z,v,block_heap])
    refine ⟨u,?_,hui,hpu,hrow,hheap⟩
    convert hscale.trans (hb.trans (hpos.trans hu)) using 1;rfl

/-- Converts actual decoder registers into the shifted operand row, charging
every branch, coefficient calculation and scalar-placement addition. -/
theorem adapter_runs (n K d a j B:ℕ) (q:Fin (count K)) (x:Fin n→ℂ) (s:State)
    (h:Context K d a j s) (hr:rawInstruction s=instruction K q)
    (hs:WordBound B s) (hB:a+cap (width K) (count K) K≤B) (hp:s.pc=90) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤9 ∧ Context K d a j u ∧ u.pc=105 ∧
    RowFields (shiftRow a (UniformRadixTwoMachine.row K q)) u ∧ u.natHeap=s.natHeap := by
  have hc:114≤B:=by have:=code_bound K;omega
  have hcap:cap (width K) (count K) K≤B:=by omega
  have hb:=branch_runs program n B 90 114 91 95 x s hs (by omega) (by omega) (by rw [hp];rfl)
  have hfinish : ∀v:State,Context K d a j v→v.pc=103→WordBound B v→
      RowFields (UniformRadixTwoMachine.row K q) v→v.natHeap=s.natHeap→∃u,
      BoundedRuns program n x B v 2 u ∧ Context K d a j u ∧ u.pc=105 ∧
      RowFields (shiftRow a (UniformRadixTwoMachine.row K q)) u ∧ u.natHeap=s.natHeap := by
    intro v hv hpv hsv hrow hheap
    have bounds:=row_bounds K q
    have hrun:=block_runs shiftOperands program 103 n B x v shift_at hpv hsv
      (by change 103+2≤B;omega) (adapter_valid v).2.2.2
      ((shift_peak a _ _ v hv.scalarBase hrow bounds.1 bounds.2).trans hB)
    refine ⟨block shiftOperands v,hrun,hv.block shiftOperands adapter_keep.2.2.2,?_,
      shift_spec a _ v hv.scalarBase hrow,?_⟩
    · rw [block_pc,hpv];rfl
    · exact (block_heap _ _).trans hheap
  by_cases hop:s.natReg 90<2
  · have cond:s.natReg 90<s.natReg 114:=by rw [h.two];exact hop
    simp only [cond,ite_true] at hb
    let z:State:={s with pc:=91}
    have hbinary:=block_runs binary program 91 n B x z binary_at rfl hb.final_bound
      (by change 91+3≤B;omega) (adapter_valid z).1 ((binary_peak K d a j q z h.withPC hr hop).trans hcap)
    have hz:Context K d a j (block binary z):=h.withPC (pc:=91) |>.block binary adapter_keep.1
    have hpz:(block binary z).pc=94:=by rw [block_pc];rfl
    have hj:=jump_runs program n B 103 x (block binary z) hbinary.final_bound (by omega) (by rw [hpz];rfl)
    obtain ⟨u,hu,hui,hpu,hrow,hheap⟩:=hfinish {block binary z with pc:=103} hz.withPC rfl hj.final_bound
      (binary_spec K d a j q z h.withPC hr hop) (block_heap binary z)
    refine ⟨u,7,?_,by omega,hui,hpu,hrow,hheap⟩
    convert hb.trans (hbinary.trans (hj.trans hu)) using 1;rfl
  · have cond:¬s.natReg 90<s.natReg 114:=by rw [h.two];exact hop
    simp only [cond,ite_false] at hb
    obtain ⟨v,hv,hvi,hpv,hrow,hheap⟩:=scale_path n K d a j B q x {s with pc:=95} h.withPC hr hop hb.final_bound hcap rfl
    obtain ⟨u,hu,hui,hpu,hrow',hheap'⟩:=hfinish v hvi hpv hv.final_bound hrow hheap
    refine ⟨u,9,?_,by omega,hui,hpu,hrow',hheap'⟩
    convert hb.trans (hv.trans hu) using 1



/-- Three real store instructions populate one row. -/
def storeRow (heap:ℕ→Option ℕ) (b:ℕ) (row:Row) : ℕ→Option ℕ :=
  Function.update (Function.update (Function.update heap b (some (opcode row.op)))
    (b+1) (some row.left)) (b+2) (some row.right)

theorem storeRow_fields (heap:ℕ→Option ℕ) (b:ℕ) (row:Row) :
    storeRow heap b row b=some (opcode row.op) ∧
    storeRow heap b row (b+1)=some row.left ∧ storeRow heap b row (b+2)=some row.right := by
  simp [storeRow]

theorem storeRow_keeps (heap:ℕ→Option ℕ) (b:ℕ) (row:Row) (i:ℕ)
    (hi:i < b ∨ b+3 ≤ i) : storeRow heap b row i=heap i := by
  simp [storeRow,Function.update_of_ne (show i≠b by omega),
    Function.update_of_ne (show i≠b+1 by omega),Function.update_of_ne (show i≠b+2 by omega)]

theorem stores_readable (s:State) : UniformNewtonTableMachine.readable stores s := by
  simp [UniformNewtonTableMachine.readable,stores,UniformNewtonTableMachine.Op.readable]

theorem stores_spec (K d a j:ℕ) (row:Row) (s:State) (h:Context K d a j s) (hr:RowFields row s) :
    Context K d a (j+1) (UniformNewtonTableMachine.applyBlock stores s) ∧
    (UniformNewtonTableMachine.applyBlock stores s).natHeap=storeRow s.natHeap (d+3*j) row := by
  constructor
  · constructor
    · constructor <;> simp [UniformNewtonTableMachine.applyBlock,stores,UniformNewtonTableMachine.Op.apply,
        writeNat,next,h.zero,h.one,h.two,h.three,h.five]
    all_goals simp [UniformNewtonTableMachine.applyBlock,stores,UniformNewtonTableMachine.Op.apply,
      writeNat,next,h.scalarBase,h.height,h.base,h.Nreg,h.Greg,h.index,h.pointer,h.prep,h.one]
    all_goals omega
  · simp [UniformNewtonTableMachine.applyBlock,stores,UniformNewtonTableMachine.Op.apply,writeNat,next,
      h.one,h.pointer,hr.1,hr.2.1,hr.2.2,storeRow,Nat.add_assoc]

theorem stores_peak (K d a j:ℕ) (q:Fin (count K)) (s:State)
    (h:Context K d a j s) (hr:RowFields (shiftRow a (UniformRadixTwoMachine.row K q)) s)
    (hj:j<count K) (B:ℕ) (ha:a+cap (width K) (count K) K≤B) (hd:d+3*count K≤B) :
    UniformNewtonTableMachine.peak stores s≤B := by
  have hb:=row_bounds K q
  have hc:=code_bound K
  simp [UniformNewtonTableMachine.peak,stores,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,h.one,h.pointer,h.index,hr.1,hr.2.1,hr.2.2,shiftRow]
  have hop:opcode (UniformRadixTwoMachine.row K q).op≤3:=by
    cases (UniformRadixTwoMachine.row K q).op <;> norm_num [opcode]
  all_goals omega

theorem stores_printed (K d a j:ℕ) (s:State) (h:Context K d a j s) (hj:j<count K)
    (hr:RowFields (shiftRow a (UniformRadixTwoMachine.row K ⟨j,hj⟩)) s) (hp:Printed K d a j s) :
    Printed K d a (j+1) (UniformNewtonTableMachine.applyBlock stores s) := by
  intro q hq
  have he:=(stores_spec K d a j _ s h hr).2
  change _∧_∧_
  rw [he]
  by_cases eq:q.val=j
  · have hqq:q=⟨j,hj⟩:=Fin.ext eq
    subst q
    exact storeRow_fields s.natHeap (d+3*j) _
  · have hlt:q.val<j:=by omega
    have h0:=storeRow_keeps s.natHeap (d+3*j) (shiftRow a (UniformRadixTwoMachine.row K ⟨j,hj⟩)) (d+3*q.val) (by omega)
    have h1:=storeRow_keeps s.natHeap (d+3*j) (shiftRow a (UniformRadixTwoMachine.row K ⟨j,hj⟩)) (d+3*q.val+1) (by omega)
    have h2:=storeRow_keeps s.natHeap (d+3*j) (shiftRow a (UniformRadixTwoMachine.row K ⟨j,hj⟩)) (d+3*q.val+2) (by omega)
    rw [h0,h1,h2]
    exact hp q hlt

theorem stores_outside (K d a j:ℕ) (s:State) (h:Context K d a j s) (hj:j<count K)
    (row:Row) (hr:RowFields row s) (heap:ℕ→Option ℕ) (ho:Outside d (3*count K) heap s) :
    Outside d (3*count K) heap (UniformNewtonTableMachine.applyBlock stores s) := by
  intro i hi
  rw [(stores_spec K d a j row s h hr).2,storeRow_keeps s.natHeap (d+3*j) row i (by omega)]
  exact ho i hi

/-- The entire printer leaves all scalar state, outputs, and root requests
unchanged. Only the decoder and printer's designated natural registers vary. -/
def Preserved (s u:State) : Prop :=
  u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ ∀i, (i < 71 ∨ 97 ≤ i)→(i < 108 ∨ 122 ≤ i)→u.natReg i=s.natReg i

theorem Preserved.refl (s:State) : Preserved s s := ⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩
theorem Preserved.trans {s u v:State} (h:Preserved s u) (h':Preserved u v) : Preserved s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
   h'.2.2.2.1.trans h.2.2.2.1,fun i hi hj=>(h'.2.2.2.2 i hi hj).trans (h.2.2.2.2 i hi hj)⟩

def safe : Instruction→Prop
  | .natLiteral d _ | .natBinary _ d _ _ => (71≤d∧d≤96)∨(108≤d∧d≤121)
  | .storeNat _ _ | .branchLT _ _ _ _ | .jump _ | .halt => True
  | _ => False

theorem decoder_safe_relocate (q:Instruction) (hq:UniformRadixInstructionMachine.safe q) :
    safe (UniformAssembly.relocate 18 90 q) := by
  cases q <;> simp_all [UniformRadixInstructionMachine.safe,safe,UniformAssembly.relocate] <;> omega

theorem program_safe : ∀q∈program,safe q := by
  have hh:∀q∈head,safe q:=by simp [head,setup,grow,sizes,AOp.code,safe]
  have ht:∀q∈tail,safe q:=by simp [tail,binary,scale,positivePower,shiftOperands,stores,AOp.code,UniformNewtonTableMachine.Op.code,safe]
  intro q hq
  simp only [program,UniformAssembly.embed,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · exact hh q hq
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hq
    exact decoder_safe_relocate p (UniformRadixInstructionMachine.program_safe p hp)
  · exact ht q hq

theorem step_preserved (n:ℕ) (x:Fin n→ℂ) (s u:State) (h:step program n x s=.running u) : Preserved s u := by
  cases hc:program[s.pc]? with
  | none => simp [step,hc] at h
  | some q =>
    have hs:safe q:=program_safe q (List.mem_of_getElem? hc)
    cases q <;> try {change False at hs;exact False.elim hs}
    case natLiteral d v =>
      change (71≤d∧d≤96)∨(108≤d∧d≤121) at hs
      simp only [step,hc,StepResult.running.injEq] at h;subst u
      refine ⟨rfl,rfl,rfl,rfl,?_⟩
      intro i hi hj;simp [writeNat,next,Function.update_of_ne (show i≠d by omega)]
    case natBinary op d l r =>
      change (71≤d∧d≤96)∨(108≤d∧d≤121) at hs
      cases he:evalNat op (s.natReg l) (s.natReg r) with
      | none => simp [step,hc,he] at h
      | some v =>
        simp only [step,hc,he,StepResult.running.injEq] at h;subst u
        refine ⟨rfl,rfl,rfl,rfl,?_⟩
        intro i hi hj;simp [writeNat,next,Function.update_of_ne (show i≠d by omega)]
    case storeNat a r =>
      simp only [step,hc,StepResult.running.injEq] at h;subst u
      exact .refl s
    case branchLT l r yes no =>
      simp only [step,hc,StepResult.running.injEq] at h;subst u;exact .refl s
    case jump pc =>
      simp only [step,hc,StepResult.running.injEq] at h;subst u;exact .refl s
    case halt => simp [step,hc] at h

theorem execution_preserved {n t:ℕ} {x:Fin n→ℂ} {s u:State} (h:Executes program n x s t u) : Preserved s u := by
  induction h with
  | halt _ => exact .refl _
  | next hs _ ih => exact (step_preserved _ _ _ _ hs).trans ih



theorem Printed.congr {K d a j:ℕ} {s u:State} (h:Printed K d a j s)
    (he:u.natHeap=s.natHeap) : Printed K d a j u := by
  intro q hq;simpa only [he] using h q hq

theorem Outside.congr {d m:ℕ} {heap:ℕ→Option ℕ} {s u:State} (h:Outside d m heap s)
    (he:u.natHeap=s.natHeap) : Outside d m heap u := by
  intro i hi;rw [he];exact h i hi

theorem Context.decoder {K d a j:ℕ} {s u:State} (h:Context K d a j s)
    (hf:UniformRadixInstructionMachine.Frame s u) : Context K d a j u := by
  apply h.congr
  intro r hr
  exact hf.2.2.2.2.2 r (by simp [controls] at hr;omega)

/-- Every ordinal is decoded by the embedded fixed program and then written by
three charged stores. No ready instruction or complete-table hypothesis occurs. -/
theorem rows_loop (n K d a j fuel B:ℕ) (x:Fin n→ℂ) (s:State) (heap:ℕ→Option ℕ)
    (h:Context K d a j s) (hj:j+fuel=count K) (hs:WordBound B s)
    (ha:a+cap (width K) (count K) K≤B) (hd:d+3*count K≤B)
    (hp:s.pc=17) (hprint:Printed K d a j s) (hout:Outside d (3*count K) heap s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤(19*K+63)*fuel+2 ∧
    Context K d a (count K) u ∧ Printed K d a (count K) u ∧ Outside d (3*count K) heap u := by
  have hcap:cap (width K) (count K) K≤B:=by omega
  have hc:114≤B:=(code_bound K).trans hcap
  induction fuel generalizing j s with
  | zero =>
    have he:j=count K:=by omega
    subst j
    have hb:=branch_runs program n B 71 109 18 113 x s hs (by omega) (by omega) (by rw [hp];rfl)
    have cond:¬s.natReg 71<s.natReg 109:=by rw [h.index,h.Greg];omega
    simp only [cond,ite_false] at hb
    have halt:BoundedExecution program n x B {s with pc:=113} 1 {s with pc:=113}:=
      .halt hb.final_bound rfl
    refine ⟨{s with pc:=113},2,?_,by omega,h.withPC,hprint,hout⟩
    exact hb.executes halt
  | succ fuel ih =>
    have hlt:j<count K:=by omega
    have hb:=branch_runs program n B 71 109 18 113 x s hs (by omega) (by omega) (by rw [hp];rfl)
    have cond:s.natReg 71<s.natReg 109:=by rw [h.index,h.Greg];exact hlt
    simp only [cond,ite_true] at hb
    let z:State:={s with pc:=0}
    obtain ⟨du,dt,hdecode,hdt,hraw,hframe⟩:=UniformRadixInstructionMachine.execution n K j B x z hlt rfl
      h.height h.index (changePC_bound B s 0 hs (by omega)) hcap
    have hplaced:=UniformBoundedAssembly.boundedExecution_placed decoder_code
      (by rw [UniformRadixInstructionMachine.program_length];omega) (by omega) hdecode
    have hdec:BoundedRuns program n x B {s with pc:=18} dt {du with pc:=90}:=by
      simpa only [z,UniformAssembly.placed,Nat.add_zero] using hplaced
    let w:State:={du with pc:=90}
    have hw:Context K d a j w:=(h.decoder hframe).withPC
    have wheap:w.natHeap=s.natHeap:=hframe.1
    obtain ⟨v,adapterSteps,hadapt,hat,hv,hpv,hrow,hvheap⟩:=adapter_runs n K d a j B ⟨j,hlt⟩ x w hw hraw hdec.final_bound ha rfl
    have hsrun:=UniformNewtonTableMachine.block_runs stores program 105 n B x v stores_at hpv hadapt.final_bound
      (by change 105+7≤B;omega) (stores_readable v) (stores_peak K d a j ⟨j,hlt⟩ v hv hrow hlt B ha hd)
    let q:=UniformNewtonTableMachine.applyBlock stores v
    have hq:Context K d a (j+1) q:=(stores_spec K d a j _ v hv hrow).1
    have hpq:q.pc=112:=by dsimp [q];rw [UniformNewtonTableMachine.applyBlock_pc,hpv];rfl
    have hprintv:Printed K d a j v:=hprint.congr (hvheap.trans wheap)
    have houtv:Outside d (3*count K) heap v:=hout.congr (hvheap.trans wheap)
    have hprintq:=stores_printed K d a j v hv hlt hrow hprintv
    have houtq:=stores_outside K d a j v hv hlt _ hrow heap houtv
    have hjump:=jump_runs program n B 17 x q hsrun.final_bound (by omega) (by rw [hpq];rfl)
    obtain ⟨u,t,hu,ht,hui,hup,huo⟩:=ih (j+1) {q with pc:=17} hq.withPC (by omega)
      hjump.final_bound rfl hprintq houtq
    refine ⟨u,1+dt+adapterSteps+7+1+t,?_,by nlinarith,hui,hup,huo⟩
    convert hb.executes (hdec.executes (hadapt.executes (hsrun.executes (hjump.executes hu)))) using 1
    norm_num [stores];omega

/-- Literal fixed RAM producer from height, table base and scalar placement
alone. Dirty unrelated state is retained and charged under the SAME word bound. -/
theorem execution (n K d a B:ℕ) (x:Fin n→ℂ) (s:State)
    (hp:s.pc=0) (hk:s.natReg 70=K) (hd:s.natReg 107=d) (ha:s.natReg 122=a)
    (hs:WordBound B s) (hscalar:a+cap (width K) (count K) K≤B) (htable:d+3*count K≤B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤(19*K+63)*count K+4*K+16 ∧
    Printed K d a (count K) u ∧ Outside d (3*count K) s.natHeap u ∧ Preserved s u ∧
    u.natReg 71=count K ∧ u.natReg 111=d+3*count K := by
  have hcap:cap (width K) (count K) K≤B:=by omega
  have hc:114≤B:=(code_bound K).trans hcap
  have hsetup:=block_runs setup program 0 n B x s setup_at hp hs (by change 0+7≤B;omega)
    (setup_valid s) (by rw [setup_peak];omega)
  have hsi:=setup_spec K d a s hk hd ha
  have hsp:(block setup s).pc=7:=by rw [block_pc,hp];rfl
  obtain ⟨v,hv,hvi,hvp,hvheap⟩:=initialize_loop n K d a 0 K B x (block setup s) hsi (by omega) hsetup.final_bound hcap hsp
  have hwidth:width K≤cap (width K) (count K) K:=by have:=cap_linear (width K) (count K) K;omega
  have hsizePeak:peakBlock sizes v≤B:=by
    have he:3*K*width K=2*count K:=by have:=count_exact K;omega
    have hl:=cap_linear (width K) (count K) K
    simp [peakBlock,sizes,AOp.apply,AOp.value,evalNat,writeNat,next,hvi.height,hvi.base,hvi.Nreg,hvi.zero,hvi.two,hvi.three,count_div]
    all_goals omega
  have hsize:=block_runs sizes program 11 n B x v sizes_at hvp hv.final_bound
    (by change 11+6≤B;omega) (sizes_valid v hvi.two) hsizePeak
  have hsizei:=sizes_spec K d a v hvi
  have hsizep:(block sizes v).pc=17:=by rw [block_pc,hvp];rfl
  have hsizeheap:(block sizes v).natHeap=s.natHeap:=
    (block_heap sizes v).trans (hvheap.trans (block_heap setup s))
  obtain ⟨u,t,hu,ht,hui,hup,huo⟩:=rows_loop n K d a 0 (count K) B x (block sizes v) s.natHeap hsizei (by omega)
    hsize.final_bound hscalar htable hsizep (by intro q hq;omega)
    (by intro i hi;rw [hsizeheap])
  have hAll:BoundedExecution program n x B s (7+(4*K+1)+(6+t)) u:=by
    convert hsetup.executes (hv.executes (hsize.executes hu)) using 1
    norm_num [setup,sizes];omega
  exact ⟨u,_,hAll,by omega,hup,huo,execution_preserved hAll.executes,hui.index,hui.pointer⟩

/-- The whole printer costs O((K+1)count K), plus constant empty-table setup. -/
theorem runtime_bound (K:ℕ) : (19*K+63)*count K+4*K+16≤80*(K+1)*(count K+1) := by nlinarith

/-- The canonical zero-offset specialization populates the frozen FFT table. -/
theorem canonical_fields (K:ℕ) (s:State) (h:Printed K 0 0 (count K) s) (j:Fin (count K)) :
    s.natHeap (3*j.val)=some (opcode (UniformRadixTwoMachine.row K j).op) ∧
    s.natHeap (3*j.val+1)=some (UniformRadixTwoMachine.row K j).left ∧
    s.natHeap (3*j.val+2)=some (UniformRadixTwoMachine.row K j).right := by
  simpa [shiftRow] using h j j.isLt

/-- Any protected metadata bank disjoint from the chosen table is retained;
its size need not be bounded by the Newton 24L prefix. -/
theorem protected_prefix (K d:ℕ) (s u:State) (m:ℕ) (hm:m≤d)
    (h:Outside d (3*count K) s.natHeap u) (j:ℕ) (hj:j < m) : u.natHeap j=s.natHeap j :=
  h j (Or.inl (by omega))

theorem saved_headers (s u:State) (h:Preserved s u) (j:ℕ) (hj:100 ≤ j ∧ j ≤ 106) : u.natReg j=s.natReg j :=
  h.2.2.2.2 j (by omega) (by omega)



/-- Relocated table entries: opcode stays unchanged and both scalar operands
are offset. Outside the allocated table the printer retains the caller's heap. -/
def encodedTable (K a i:ℕ) : Option ℕ :=
  (UniformRadixTwoMachine.encodedTable K i).map (fun v=>if i%3=0 then v else a+v)

theorem encodedTable_fields (K a:ℕ) (j:Fin (count K)) :
    encodedTable K a (3*j.val)=some (opcode (shiftRow a (UniformRadixTwoMachine.row K j)).op) ∧
    encodedTable K a (3*j.val+1)=some (shiftRow a (UniformRadixTwoMachine.row K j)).left ∧
    encodedTable K a (3*j.val+2)=some (shiftRow a (UniformRadixTwoMachine.row K j)).right := by
  have hf:=UniformRadixTwoMachine.encodedTable_fields K j
  have h0:(3*j.val)%3=0:=by omega
  have h1:(3*j.val+1)%3=1:=by omega
  have h2:(3*j.val+2)%3=2:=by omega
  simp [encodedTable,hf.1,hf.2.1,hf.2.2,h0,h1,h2,shiftRow]

theorem encodedTable_zero (K i:ℕ) : encodedTable K 0 i=UniformRadixTwoMachine.encodedTable K i := by
  simp [encodedTable]

theorem printed_encoded (K d a:ℕ) (s:State) (h:Printed K d a (count K) s)
    (i:ℕ) (hi:i<3*count K) : s.natHeap (d+i)=encodedTable K a i := by
  have hj:i/3<count K:=by omega
  let q:Fin (count K):=⟨i/3,hj⟩
  have hp:=h q q.isLt
  have he:=encodedTable_fields K a q
  by_cases h0:i%3=0
  · have hi0:i=3*q.val:=by dsimp [q];omega
    simpa only [hi0] using hp.1.trans he.1.symm
  · by_cases h1:i%3=1
    · have hi1:i=3*q.val+1:=by dsimp [q];omega
      simpa only [hi1,Nat.add_assoc] using hp.2.1.trans he.2.1.symm
    · have hi2:i=3*q.val+2:=by dsimp [q];omega
      simpa only [hi2,Nat.add_assoc] using hp.2.2.trans he.2.2.symm

/-- End-to-end materialized table producer, including address relocation.
Prepared powers and subsequent FFT execution are separate charged phases. -/
theorem execution_table (n K d a B:ℕ) (x:Fin n→ℂ) (s:State)
    (hp:s.pc=0) (hk:s.natReg 70=K) (hd:s.natReg 107=d) (ha:s.natReg 122=a)
    (hs:WordBound B s) (hscalar:a+cap (width K) (count K) K≤B) (htable:d+3*count K≤B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤(19*K+63)*count K+4*K+16 ∧
    (∀i,i<3*count K→u.natHeap (d+i)=encodedTable K a i) ∧
    Outside d (3*count K) s.natHeap u ∧ Preserved s u := by
  obtain ⟨u,t,he,ht,hp,ho,hf,_,_⟩:=execution n K d a B x s hp hk hd ha hs hscalar htable
  exact ⟨u,t,he,ht,fun i hi=>printed_encoded K d a u hp i hi,ho,hf⟩

/-- Canonical rows match the previously verified FFT machine exactly, while
heap entries beyond its actual rows may remain dirty. -/
theorem canonical_encoded (K:ℕ) (s:State) (h:Printed K 0 0 (count K) s)
    (i:ℕ) (hi:i<3*count K) : s.natHeap i=UniformRadixTwoMachine.encodedTable K i := by
  simpa only [Nat.zero_add,encodedTable_zero] using printed_encoded K 0 0 s h i hi

end ExactFourierCircuits.UniformRadixRowTableMachine
