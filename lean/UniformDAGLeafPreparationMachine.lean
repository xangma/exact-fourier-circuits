import UniformScalarCopyMachine
import UniformDAGLiteralBankMachine
import UniformOffsetPreparationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDAGLeafPreparationMachine
open UniformMachine UniformAssembly
open UniformScalarPreparation (Instruction)
open UniformOffsetPreparationMachine (DProgram DInstruction RootsReady LiteralsReady)
open scoped BigOperators

/-- Persistent caller headers253=r,254=root source,255=zero/leaf origin b,
256=signed-rational triple source,257=chronological DAG length. Scratch258..259.
All helper argument copies, addresses, halts/continuations are real instructions. -/
def rootSetup : Program := [.natLiteral 258 0,.natLiteral 259 1,
  .natBinary .add 147 253 258,.natBinary .add 148 254 258,.natBinary .add 149 255 259]
def literalSetup : Program := [.natBinary .add 230 257 258,.natBinary .add 231 256 258,
  .natBinary .add 238 255 258,.natBinary .add 232 255 259,.natBinary .add 232 232 253]
def program : Program := rootSetup ++
  UniformScalarCopyMachine.program.map (relocate 5 15) ++ literalSetup ++
  UniformDAGLiteralBankMachine.program.map (relocate 20 69) ++ [.halt]
theorem program_length : program.length=70 := rfl
theorem root_code : CodeAt UniformScalarCopyMachine.program program 5 15 := by
  intro i hi
  rw [UniformScalarCopyMachine.program_length] at hi
  interval_cases i <;> rfl
theorem literal_code : CodeAt UniformDAGLiteralBankMachine.program program 20 69 := by
  intro i hi
  rw [UniformDAGLiteralBankMachine.program_length] at hi
  interval_cases i <;> rfl

/-- A deterministic literal slot per chronological node; nonliteral gaps are
prepared zero. This finite typed topology is not assumed to be a RAM-produced tape. -/
def instructionLiteral {r j : ℕ} : DInstruction r j→ℚ
  | .rational q => q
  | _ => 0
def literalValues {r : ℕ} : {k : ℕ}→DProgram r k→Fin k→ℚ
  | 0,.nil => Fin.elim0
  | _+1,.step p i => Fin.snoc (literalValues p) (instructionLiteral i)
def literalNat {r k : ℕ} (p : DProgram r k) (j : ℕ) : ℚ :=
  if h:j < k then literalValues p ⟨j,h⟩ else 0
theorem literalNat_fin {r k : ℕ} (p : DProgram r k) (j : Fin k) :
    literalNat p j.val=literalValues p j := by simp [literalNat,j.isLt]

noncomputable section

def RootSource {r : ℕ} (source : ℕ) (roots : Fin r→ℂ) (s : State) : Prop :=
  ∀j:Fin r,s.scalarHeap (source+j.val)=some ⟨roots j,false⟩
def LiteralSource {r k : ℕ} (p : DProgram r k) (d : ℕ) (s : State) : Prop :=
  UniformDAGLiteralBankMachine.RationalSource k d (literalNat p) s
def runtime {r k : ℕ} (p : DProgram r k) : ℕ :=
  7*r+15+UniformDAGLiteralBankMachine.runtime k
    (fun j=>(literalNat p j).num.natAbs) (fun j=>(literalNat p j).den)
    (fun j=>if (literalNat p j).num < 0 then 1 else 0)

def Protected (i : ℕ) : Prop := 7 ≤ i ∧ (i < 147 ∨ 154 ≤ i) ∧
  (i < 230 ∨ 239 ≤ i) ∧ (i < 258 ∨ 260 ≤ i)
instance protectedDecidable (i : ℕ) : Decidable (Protected i) :=
  inferInstanceAs (Decidable (7 ≤ i ∧ (i < 147 ∨ 154 ≤ i) ∧
    (i < 230 ∨ 239 ≤ i) ∧ (i < 258 ∨ 260 ≤ i)))
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
  u.rootOrders=s.rootOrders ∧ ∀i,Protected i→u.natReg i=s.natReg i
def Outside (b r k : ℕ) (s u : State) : Prop :=
  ∀i,(i < b ∨ b+1+r+k ≤ i)→u.scalarHeap i=s.scalarHeap i
theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    fun i hi=>(h'.2.2.2 i hi).trans (h.2.2.2 i hi)⟩

theorem literalsReady_of_bank {r k : ℕ} (p : DProgram r k) (b : ℕ) (s : State)
    (h:∀j:Fin k,s.scalarHeap (b+1+r+j.val)=some ⟨literalValues p j,false⟩) :
    LiteralsReady p b s := by
  induction p with
  | nil => trivial
  | @step j p i ih =>
    constructor
    · apply ih
      intro index
      simpa only [literalValues,Fin.snoc_castSucc,Fin.val_castSucc] using h index.castSucc
    · have hlast:=h (Fin.last j)
      simp only [literalValues,Fin.snoc_last,Fin.val_last] at hlast
      cases i <;> first | exact hlast | trivial

/-- Literal natural-only straight-line blocks, with individually bounded writes. -/
inductive Op where
  | lit (d v : ℕ)
  | add (d l r : ℕ)
  deriving DecidableEq
def Op.code : Op→UniformMachine.Instruction
  | .lit d v => .natLiteral d v
  | .add d l r => .natBinary .add d l r
def Op.value : Op→State→ℕ
  | .lit _ v,_ => v
  | .add _ l r,s => s.natReg l+s.natReg r
def Op.apply (o : Op) (s : State) : State := match o with
  | .lit d _ => writeNat s d (o.value s)
  | .add d _ _ => writeNat s d (o.value s)
def applyBlock : List Op→State→State
  | [],s => s
  | o::os,s => applyBlock os (o.apply s)
def peak : List Op→State→ℕ
  | [],_ => 0
  | o::os,s => max (o.value s) (peak os (o.apply s))
def BlockAt (os : List Op) (base : ℕ) : Prop :=
  ∀i,(hi:i < os.length)→program[base+i]?=some (os[i]'hi).code
theorem Op.pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by cases o <;> rfl
theorem applyBlock_pc (os : List Op) (s : State) :
    (applyBlock os s).pc=s.pc+os.length := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp only [applyBlock,ih,Op.pc,List.length_cons];omega
theorem block_runs (os : List Op) (base n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hc:BlockAt os base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+os.length ≤ B) (hv:peak os s ≤ B) :
    BoundedRuns program n x B s os.length (applyBlock os s) := by
  induction os generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have hp1:s.pc+1 ≤ B := by simp only [List.length_cons] at hb;omega
    have ho:WordBound B (o.apply s):=by
      cases o <;> exact writeNat_bound B s _ _ hs hp1 ((le_max_left _ _).trans hv)
    have ht:BlockAt os (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change program[base+(i+1)]?=some (os[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have tail:=ih (base+1) (o.apply s) ht (by rw [Op.pc,hp]) ho
      (by simp only [List.length_cons] at hb;omega) ((le_max_right _ _).trans hv)
    have hfirst:=hc 0 (by simp)
    change program[base]?=some o.code at hfirst
    refine .next hs ?_ tail
    cases o <;> simp [UniformMachine.step,hp,hfirst,Op.code,Op.apply,Op.value,evalNat]

def rootOps : List Op := [.lit 258 0,.lit 259 1,.add 147 253 258,
  .add 148 254 258,.add 149 255 259]
def literalOps : List Op := [.add 230 257 258,.add 231 256 258,.add 238 255 258,
  .add 232 255 259,.add 232 232 253]
theorem rootOps_code : BlockAt rootOps 0 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem literalOps_code : BlockAt literalOps 15 := by
  intro i hi;change i < 5 at hi;interval_cases i <;> rfl
theorem rootOps_frame (s : State) : Frame s (applyBlock rootOps s) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro i hi
  have h147:i≠147:=by unfold Protected at hi;omega
  have h148:i≠148:=by unfold Protected at hi;omega
  have h149:i≠149:=by unfold Protected at hi;omega
  have h258:i≠258:=by unfold Protected at hi;omega
  have h259:i≠259:=by unfold Protected at hi;omega
  simp [applyBlock,rootOps,Op.apply,writeNat,next,h147,h148,h149,h258,h259]
theorem literalOps_frame (s : State) : Frame s (applyBlock literalOps s) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro i hi
  have h230:i≠230:=by unfold Protected at hi;omega
  have h231:i≠231:=by unfold Protected at hi;omega
  have h232:i≠232:=by unfold Protected at hi;omega
  have h238:i≠238:=by unfold Protected at hi;omega
  simp [applyBlock,literalOps,Op.apply,writeNat,next,h230,h231,h232,h238]


theorem reset_placed (s : State) (base : ℕ) (hpc:s.pc=base) :
    placed base {s with pc:=0}=s := by
  cases h:s with
  | mk pc nr sr nh sh out orders =>
    have hp:pc=base:=by simpa only [h] using hpc
    simp [placed,hp]

/-- One fixed70-instruction program constructs the exact localized leaf
postconditions of the actual prepared-DAG interpreter. Original roots and the
physical rational-row tape remain explicit inputs; no new roots are requested. -/
theorem execution {r k : ℕ} (p : DProgram r k) (roots : Fin r→ℂ)
    (n : ℕ) (x : Fin n→ℂ) (source b d B : ℕ) (s : State)
    (hroots:RootSource source roots s) (hliterals:LiteralSource p d s)
    (hsrc:source+r ≤ b) (hb:0 < b) (hspace:b+1+r+k ≤ B)
    (htable:d+3*k ≤ B) (hcode:70 ≤ B) (hpc:s.pc=0)
    (hr:s.natReg 253=r) (hsource:s.natReg 254=source) (hbase:s.natReg 255=b)
    (hd:s.natReg 256=d) (hk:s.natReg 257=k) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime p) u ∧
    RootsReady b roots u ∧ LiteralsReady p b u ∧
    (∀j:Fin k,u.scalarHeap (b+1+r+j.val)=some ⟨literalValues p j,false⟩) ∧
    u.scalarHeap 0=s.scalarHeap 0 ∧
    (∀j:Fin r,u.scalarHeap (source+j.val)=s.scalarHeap (source+j.val)) ∧
    Frame s u ∧ Outside b r k s u ∧ u.pc=69 := by
  have hsetup:BoundedRuns program n x B s 5 (applyBlock rootOps s):=by
    apply block_runs rootOps 0 n B x s rootOps_code hpc hs (by change 0+5 ≤ B;omega)
    simp [peak,rootOps,Op.value,Op.apply,writeNat,next,hr,hsource,hbase]
    have hrB:=hs.2.1 253
    have hsourceB:=hs.2.1 254
    rw [hr] at hrB
    rw [hsource] at hsourceB
    omega
  let initialized:=applyBlock rootOps s
  have hipc:initialized.pc=5:=by rw [applyBlock_pc,hpc];rfl
  have hi147:initialized.natReg 147=r:=by simp [initialized,applyBlock,rootOps,Op.apply,Op.value,writeNat,next,hr]
  have hi148:initialized.natReg 148=source:=by simp [initialized,applyBlock,rootOps,Op.apply,Op.value,writeNat,next,hsource]
  have hi149:initialized.natReg 149=b+1:=by simp [initialized,applyBlock,rootOps,Op.apply,Op.value,writeNat,next,hbase]
  have hisrc:UniformScalarCopyMachine.Source r source initialized.scalarHeap:=by
    intro j hj
    exact ⟨⟨roots ⟨j,hj⟩,false⟩,hroots ⟨j,hj⟩⟩
  have hib:WordBound B {initialized with pc:=0}:=changePC_bound B _ 0 hsetup.final_bound (by omega)
  obtain ⟨v,hv,hcopied,_hretained,houtside,hframe,hnat⟩:=UniformScalarCopyMachine.execution n x
    r source (b+1) B {initialized with pc:=0} hisrc (by omega) (by omega) (by omega)
    rfl hi147 hi148 hi149 hib
  have hcopy:=UniformBoundedAssembly.boundedExecution_placed root_code
    (by rw [UniformScalarCopyMachine.program_length];omega) (by omega) hv
  rw [reset_placed initialized 5 hipc] at hcopy
  let copied:State:={v with pc:=15}
  have hcf:Frame initialized copied:=by
    refine ⟨hframe.1,hframe.2.1,hframe.2.2.1,?_⟩
    intro i hi
    exact hnat i (by unfold Protected at hi;omega)
  have hcopRoots:∀j:Fin r,copied.scalarHeap (b+1+j.val)=some ⟨roots j,false⟩:=by
    intro j
    exact (hcopied j.val j.isLt).trans (hroots j)
  have h253:copied.natReg 253=r:=(hcf.2.2.2 253 (by decide)).trans
    ((rootOps_frame s).2.2.2 253 (by decide) |>.trans hr)
  have h254:copied.natReg 254=source:=(hcf.2.2.2 254 (by decide)).trans
    ((rootOps_frame s).2.2.2 254 (by decide) |>.trans hsource)
  have h255:copied.natReg 255=b:=(hcf.2.2.2 255 (by decide)).trans
    ((rootOps_frame s).2.2.2 255 (by decide) |>.trans hbase)
  have h256:copied.natReg 256=d:=(hcf.2.2.2 256 (by decide)).trans
    ((rootOps_frame s).2.2.2 256 (by decide) |>.trans hd)
  have h257:copied.natReg 257=k:=(hcf.2.2.2 257 (by decide)).trans
    ((rootOps_frame s).2.2.2 257 (by decide) |>.trans hk)
  have h258:copied.natReg 258=0:=by
    simpa [initialized,applyBlock,rootOps,Op.apply,Op.value,writeNat,next] using hnat 258 (by omega)
  have h259:copied.natReg 259=1:=by
    simpa [initialized,applyBlock,rootOps,Op.apply,Op.value,writeNat,next] using hnat 259 (by omega)
  have hsecond:BoundedRuns program n x B copied 5 (applyBlock literalOps copied):=by
    apply block_runs literalOps 15 n B x copied literalOps_code rfl hcopy.final_bound
      (by change 15+5 ≤ B;omega)
    simp [peak,literalOps,Op.value,Op.apply,writeNat,next,h253,h255,h256,h257,h258,h259]
    omega
  let literals:=applyBlock literalOps copied
  have hlpc:literals.pc=20:=by rw [applyBlock_pc];rfl
  have h230:literals.natReg 230=k:=by simp [literals,applyBlock,literalOps,Op.apply,Op.value,writeNat,next,h257,h258]
  have h231:literals.natReg 231=d:=by simp [literals,applyBlock,literalOps,Op.apply,Op.value,writeNat,next,h256,h258]
  have h232:literals.natReg 232=b+1+r:=by simp [literals,applyBlock,literalOps,Op.apply,Op.value,writeNat,next,h253,h255,h259]
  have h238:literals.natReg 238=b:=by simp [literals,applyBlock,literalOps,Op.apply,Op.value,writeNat,next,h255,h258]
  have hlnat:literals.natHeap=s.natHeap:=(literalOps_frame copied).1.trans
    (hcf.1.trans (rootOps_frame s).1)
  have hlsrc:UniformDAGLiteralBankMachine.RationalSource k d (literalNat p) {literals with pc:=0}:=by
    simpa only [LiteralSource,UniformDAGLiteralBankMachine.RationalSource,
      UniformDAGLiteralBankMachine.Source,hlnat] using hliterals
  have hlb:WordBound B {literals with pc:=0}:=changePC_bound B _ 0 hsecond.final_bound (by omega)
  obtain ⟨w,hw,hzero,hleaves,hlframe,hloutside,_hlhalt⟩:=UniformDAGLiteralBankMachine.rational_execution
    n x k d (b+1+r) b B (literalNat p) {literals with pc:=0} hlsrc (by omega)
    htable hspace (by omega) rfl h230 h231 h232 h238 hlb
  have hlrun:=UniformBoundedAssembly.boundedExecution_placed literal_code
    (by rw [UniformDAGLiteralBankMachine.program_length];omega) (by omega) hw
  rw [reset_placed literals 20 hlpc] at hlrun
  let final:State:={w with pc:=69}
  have hfinal:WordBound B final:=hlrun.final_bound
  have halt:BoundedExecution program n x B final 1 final:=.halt hfinal
    (by rw [UniformMachine.step];rfl)
  have hlf:Frame literals final:=by
    refine ⟨hlframe.1,hlframe.2.1,hlframe.2.2.1,?_⟩
    intro i hi
    exact hlframe.2.2.2 i (by unfold Protected UniformDAGLiteralBankMachine.Protected at *;omega)
  have hwhole:Frame s final:=(rootOps_frame s).trans (hcf.trans ((literalOps_frame copied).trans hlf))
  have ho:Outside b r k s final:=by
    intro i hi
    rw [hloutside i (by omega) (by omega)]
    exact houtside i (by omega)
  have hleaves':∀j:Fin k,final.scalarHeap (b+1+r+j.val)=some ⟨literalValues p j,false⟩:=by
    intro j
    simpa only [literalNat_fin] using hleaves j.val j.isLt
  refine ⟨final,?_,⟨hzero,?_⟩,literalsReady_of_bank p b final hleaves',hleaves',
    ho 0 (Or.inl hb),?_,hwhole,ho,rfl⟩
  · have hall:=(((hsetup.trans hcopy).trans hsecond).trans hlrun).executes halt
    convert hall using 1
    unfold runtime
    omega
  · intro j
    rw [hloutside _ (by omega) (Or.inl (by have hj:=j.isLt;omega))]
    exact hcopRoots j
  · intro j
    apply ho
    left;have hj:=j.isLt;omega

/-- Exact source-derived charge, including both callers and main halt. -/
theorem runtime_log_bound {r k : ℕ} (p : DProgram r k) (d B : ℕ) (s : State)
    (hsource:LiteralSource p d s) (hs:WordBound B s) :
    runtime p ≤ 7*r+22+k*(14*(Nat.log2 (B+1)+1)+31) := by
  have h:=UniformDAGLiteralBankMachine.runtime_log_of_source k d B
    (fun j=>(literalNat p j).num.natAbs) (fun j=>(literalNat p j).den)
    (fun j=>if (literalNat p j).num < 0 then 1 else 0) s hsource hs
  unfold runtime
  omega

theorem saved_preserved {s u : State} (h:Frame s u) (i : ℕ)
    (hi:100 ≤ i ∧ i ≤ 106) : u.natReg i=s.natReg i :=
  h.2.2.2 i (by unfold Protected;omega)

theorem row_headers_preserved {s u : State} (h:Frame s u) (i : ℕ)
    (hi:(220 ≤ i ∧ i ≤ 225) ∨ (240 ≤ i ∧ i ≤ 257)) : u.natReg i=s.natReg i :=
  h.2.2.2 i (by unfold Protected;omega)



/-- Allocating the fresh leaf bank after a retained global scalar prefix keeps
that entire prefix, including all already prepared coefficients and input data. -/
theorem prefix_preserved {b r k e : ℕ} {s u : State} (h:Outside b r k s u)
    (he:e ≤ b) : ∀i,i < e→u.scalarHeap i=s.scalarHeap i :=
  fun i hi=>h i (Or.inl (by omega))

/-- All integer data is preserved, so previously produced shifted DAG tables
can be consumed after this leaf producer without reconstruction. -/
theorem row_table_preserved {r k : ℕ} (p : DProgram r k) (b a d : ℕ) {s u : State}
    (h:Frame s u) (ht:UniformOffsetPreparationMachine.NatTable
      (UniformOffsetPreparationMachine.compile p b a) d s) :
    UniformOffsetPreparationMachine.NatTable (UniformOffsetPreparationMachine.compile p b a) d u := by
  simpa only [UniformOffsetPreparationMachine.NatTable,h.1] using ht


end
end ExactFourierCircuits.UniformDAGLeafPreparationMachine
