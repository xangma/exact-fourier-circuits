import UniformPreparedDAGMachine
import UniformRoots

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedDAGConjugateMachine
open UniformMachine UniformAssembly
open UniformOffsetPreparationMachine (DProgram Values)
open OAI.ExactFourier
abbrev Base := UniformPreparedDAGMachine.program

/-- Caller Nat350..358 supplies k,b0,a0,R,b1,a1,l,c,d. Nat359 is scratch.
The inverse of the actual master at heap0 is prepared by five real instructions.
Both DAG passes read the same physical typed and rational tapes. -/
def inverseCode : Program := [.natLiteral 359 0,.loadScalar 33 359,
 .scalarLiteral 34 1,.fieldBinary .div 35 34 33,.storeScalar 353 35]
def firstSetup : Program := [.natBinary .add 273 350 359,.natLiteral 274 1,.natLiteral 275 0,
 .natBinary .add 276 351 359,.natBinary .add 277 356 359,.natBinary .add 278 357 359,
 .natBinary .add 279 358 359,.natBinary .add 280 352 359]
def secondSetup : Program := [.natBinary .add 273 350 359,.natLiteral 274 1,
 .natBinary .add 275 353 359,.natBinary .add 276 354 359,.natBinary .add 277 356 359,
 .natBinary .add 278 357 359,.natBinary .add 279 358 359,.natBinary .add 280 355 359]
def program : Program := inverseCode ++ firstSetup ++ Base.map (relocate 13 170) ++
 secondSetup ++ Base.map (relocate 178 335) ++ [.halt]
theorem program_length : program.length=336 := by
 simp only [program,List.length_append,List.length_map,UniformPreparedDAGMachine.program_length]
 rfl

theorem first_code : CodeAt Base program 13 170 := by
 intro i hi
 rw [UniformPreparedDAGMachine.program_length] at hi
 interval_cases i  <;> rfl

theorem second_code : CodeAt Base program 178 335 := by
 intro i hi
 rw [UniformPreparedDAGMachine.program_length] at hi
 interval_cases i  <;> rfl

noncomputable section
abbrev Op := UniformPreparedDAGMachine.Op
abbrev applyBlock := UniformPreparedDAGMachine.applyBlock
abbrev peak := UniformPreparedDAGMachine.peak
open UniformPreparedDAGMachine (Op.pc applyBlock_pc block_natHeap block_scalarHeap)
def BlockAt (os : List Op) (base : ℕ) : Prop :=
 ∀i,(hi:i < os.length) → program[base+i]?=some (os[i]'hi).code
theorem block_runs (os : List Op) (base n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc:BlockAt os base) (hp:s.pc=base) (hs:WordBound B s)
    (hb:base+os.length  ≤  B) (hv:peak os s  ≤  B) :
    BoundedRuns program n x B s os.length (applyBlock os s) := by
  induction os generalizing base s with
  | nil => exact .refl hs
  | cons o os ih =>
    have hp1:s.pc+1  ≤  B := by simp only [List.length_cons] at hb;omega
    have ho:WordBound B (o.apply s):=by
      cases o  <;> exact writeNat_bound B s _ _ hs hp1 ((le_max_left _ _).trans hv)
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
    cases o  <;> simp [UniformMachine.step,hp,hfirst,UniformPreparedDAGMachine.Op.code,UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,evalNat]


def firstOps : List Op := [.add 273 350 359,.lit 274 1,.lit 275 0,
 .add 276 351 359,.add 277 356 359,.add 278 357 359,
 .add 279 358 359,.add 280 352 359]
def secondOps : List Op := [.add 273 350 359,.lit 274 1,
 .add 275 353 359,.add 276 354 359,.add 277 356 359,
 .add 278 357 359,.add 279 358 359,.add 280 355 359]
theorem firstOps_code : BlockAt firstOps 5 := by
 intro i hi;change i < 8 at hi;interval_cases i  <;> rfl
theorem secondOps_code : BlockAt secondOps 170 := by
 intro i hi;change i < 8 at hi;interval_cases i  <;> rfl

def Protected (i : ℕ) : Prop := UniformPreparedDAGMachine.Protected i  ∧
 (i  <  273  ∨  282  ≤  i)  ∧  i  ≠  359
instance protectedDecidable (i : ℕ) : Decidable (Protected i) :=
 inferInstanceAs (Decidable (UniformPreparedDAGMachine.Protected i  ∧ (i  <  273  ∨  282  ≤  i) ∧  i  ≠  359))
def Frame (s u : State) : Prop := u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧
 ∀i,Protected i → u.natReg i=s.natReg i
structure Header (k b0 a0 rootInv b1 a1 l c d : ℕ) (s : State) : Prop where
 length : s.natReg 350=k
 firstLeaves : s.natReg 351=b0
 firstResults : s.natReg 352=a0
 inverseRoot : s.natReg 353=rootInv
 secondLeaves : s.natReg 354=b1
 secondResults : s.natReg 355=a1
 literals : s.natReg 356=l
 tape : s.natReg 357=c
 rows : s.natReg 358=d

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,fun i hi=>(h'.2.2 i hi).trans (h.2.2 i hi)⟩

theorem Header.transport {k b0 a0 R b1 a1 l c d : ℕ} {s u : State}
 (h:Header k b0 a0 R b1 a1 l c d s) (hf:Frame s u) : Header k b0 a0 R b1 a1 l c d u := by
 constructor
 · exact (hf.2.2 350 (by decide)).trans h.length
 · exact (hf.2.2 351 (by decide)).trans h.firstLeaves
 · exact (hf.2.2 352 (by decide)).trans h.firstResults
 · exact (hf.2.2 353 (by decide)).trans h.inverseRoot
 · exact (hf.2.2 354 (by decide)).trans h.secondLeaves
 · exact (hf.2.2 355 (by decide)).trans h.secondResults
 · exact (hf.2.2 356 (by decide)).trans h.literals
 · exact (hf.2.2 357 (by decide)).trans h.tape
 · exact (hf.2.2 358 (by decide)).trans h.rows

theorem Frame.of_base {s u : State} (h:UniformPreparedDAGMachine.Frame s u) : Frame s u :=
 ⟨h.1,h.2.1,fun i hi=>h.2.2 i hi.1⟩

theorem block_frame (os : List Op) (s : State)
 (h:∀o∈os,¬Protected o.dest) : Frame s (applyBlock os s) := by
 induction os generalizing s with
 | nil => exact ⟨rfl,rfl,fun _ _=>rfl⟩
 | cons o os ih =>
  have ho:=h o (by simp)
  have ht:=ih (o.apply s) (fun t ht=>h t (by simp [ht]))
  apply Frame.trans (u:=o.apply s) ?_ ht
  refine ⟨?_,?_,?_⟩
  · cases o  <;> rfl
  · cases o  <;> rfl
  · intro i hi
    have he:i ≠ o.dest:=by intro he;apply ho;simpa [←he] using hi
    cases o  <;> simp_all [UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.dest,writeNat,next]


theorem firstOps_frame (s : State) : Frame s (applyBlock firstOps s) := by
 apply block_frame
 intro o ho
 simp [firstOps] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;> decide

theorem secondOps_frame (s : State) : Frame s (applyBlock secondOps s) := by
 apply block_frame
 intro o ho
 simp [secondOps] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;> decide

theorem first_arguments {k b0 a0 R b1 a1 l c d : ℕ} (s : State)
 (h:Header k b0 a0 R b1 a1 l c d s) (hz:s.natReg 359=0) :
 UniformPreparedDAGMachine.Header 1 k 0 b0 l c d a0 (applyBlock firstOps s) := by
 constructor  <;> simp [applyBlock,UniformPreparedDAGMachine.applyBlock,firstOps,UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,writeNat,next,
   h.length,h.firstLeaves,h.firstResults,h.literals,h.tape,h.rows,hz]

theorem second_arguments {k b0 a0 R b1 a1 l c d : ℕ} (s : State)
 (h:Header k b0 a0 R b1 a1 l c d s) (hz:s.natReg 359=0) :
 UniformPreparedDAGMachine.Header 1 k R b1 l c d a1 (applyBlock secondOps s) := by
 constructor  <;> simp [applyBlock,UniformPreparedDAGMachine.applyBlock,secondOps,UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,writeNat,next,
   h.length,h.inverseRoot,h.secondLeaves,h.secondResults,h.literals,h.tape,h.rows,hz]

def inverseLoaded (s : State) (omega : ℂ) : State :=
 writeScalar (writeNat s 359 0) 33 ⟨omega,false⟩
def inverseOne (s : State) (omega : ℂ) : State := writeScalar (inverseLoaded s omega) 34 ⟨1,false⟩
def inverseComputed (s : State) (omega : ℂ) : State := writeScalar (inverseOne s omega) 35 ⟨omega⁻¹,false⟩
def inverseEnd (s : State) (omega : ℂ) : State :=
 {next (inverseComputed s omega) with scalarHeap:=Function.update s.scalarHeap (s.natReg 353) (some ⟨omega⁻¹,false⟩)}

theorem inverse_frame (s : State) (omega : ℂ) : Frame s (inverseEnd s omega) := by
 refine ⟨rfl,rfl,?_⟩
 intro i hi
 simp [inverseEnd,inverseComputed,inverseOne,inverseLoaded,writeScalar,writeNat,next,hi.2.2]

theorem inverse_runs (n B : ℕ) (x : Fin n → ℂ) (s : State) (omega : ℂ)
 (hm:s.scalarHeap 0=some ⟨omega,false⟩) (hn:omega ≠ 0) (hp:s.pc=0)
 (hs:WordBound B s) (hc:336 ≤ B) (ha:s.natReg 353 ≤ B) :
 BoundedRuns program n x B s 5 (inverseEnd s omega) := by
 let zero:=writeNat s 359 0
 have hz:WordBound B zero:=writeNat_bound B s 359 0 hs (by omega) (by omega)
 have hl:WordBound B (inverseLoaded s omega):=writeScalar_bound B zero 33 _ hz (by simp [zero,writeNat,next,hp];omega)
 have ho:WordBound B (inverseOne s omega):=writeScalar_bound B _ 34 _ hl (by simp [inverseLoaded,writeScalar,writeNat,next,hp];omega)
 have hv:WordBound B (inverseComputed s omega):=writeScalar_bound B _ 35 _ ho (by simp [inverseOne,inverseLoaded,writeScalar,writeNat,next,hp];omega)
 have he:WordBound B (inverseEnd s omega):=UniformScalarCopyMachine.store_bound B (inverseComputed s omega) _ _ hv
   (by simp [inverseComputed,inverseOne,inverseLoaded,writeScalar,writeNat,next,hp];omega) ha
 refine .next hs ?_ (.next hz ?_ (.next hl ?_ (.next ho ?_ (.next hv ?_ (.refl he)))))
 all_goals simp [step,program,inverseCode,zero,inverseLoaded,inverseOne,inverseComputed,inverseEnd,
   writeNat,writeScalar,next,hp,hm,evalField,hn]

/-- Canonical roots have unit norm with their specified phase. -/
theorem specifiedRoot_norm (D : ℕ) : ‖zeta D‖=1 := by
 simp [zeta,Complex.norm_exp,Complex.div_re,Complex.mul_re,Complex.mul_im]

def wordBudget (l c d b0 a0 R b1 a1 k : ℕ) : ℕ := l+c+d+b0+a0+R+b1+a1+8*k+400

def runtime {k : ℕ} (p : DProgram 1 k) (b0 a0 b1 a1 : ℕ) : ℕ :=
 UniformPreparedDAGMachine.runtime p b0 a0+UniformPreparedDAGMachine.runtime p b1 a1+22

/-- Each physical source cell is outside a disjoint row interval. -/
theorem source_cell_outside (k source rows j t : ℕ)
 (hd:UniformPreparationRowTableMachine.Disjoint k source rows)
 (hj:j < k) (ht:t < 3) : source+3*j+t < rows  ∨  rows+3*k ≤ source+3*j+t := by
 rcases hd with hd|hd
 · left;omega
 · right;omega

theorem literal_source_transport {k : ℕ} (p : DProgram 1 k) (l d : ℕ) (s u : State)
 (hd:UniformPreparationRowTableMachine.Disjoint k l d)
 (hf:UniformPreparedDAGMachine.OutsideNat d k s u)
 (hl:UniformDAGLeafPreparationMachine.LiteralSource p l s) :
 UniformDAGLeafPreparationMachine.LiteralSource p l u := by
 intro j hj
 have h0:=hf (l+3*j) (by simpa using source_cell_outside k l d j 0 hd hj (by omega))
 have h1:=hf (l+3*j+1) (source_cell_outside k l d j 1 hd hj (by omega))
 have h2:=hf (l+3*j+2) (source_cell_outside k l d j 2 hd hj (by omega))
 rw [h0,h1,h2]
 exact hl j hj

theorem node_tape_transport {k : ℕ} (p : DProgram 1 k) (c d : ℕ) (s u : State)
 (hd:UniformPreparationRowTableMachine.Disjoint k c d)
 (hf:UniformPreparedDAGMachine.OutsideNat d k s u)
 (ht:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap) :
 UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c u.natHeap := by
 intro j
 have h0:=hf (c+3*j.val) (by simpa using source_cell_outside k c d j.val 0 hd j.isLt (by omega))
 have h1:=hf (c+3*j.val+1) (source_cell_outside k c d j.val 1 hd j.isLt (by omega))
 have h2:=hf (c+3*j.val+2) (source_cell_outside k c d j.val 2 hd j.isLt (by omega))
 rw [h0,h1,h2]
 exact ht j

def OutsideScalar (b0 a0 R b1 a1 k : ℕ) (s u : State) : Prop :=
 ∀i,i ≠ R → (i < b0  ∨  b0+2+k ≤ i) → (i < a0  ∨  a0+k ≤ i) →
 (i < b1  ∨  b1+2+k ≤ i) → (i < a1  ∨  a1+k ≤ i) → u.scalarHeap i=s.scalarHeap i

def ConjugateValues {k : ℕ} (p : DProgram 1 k) (omega : ℂ) (a : ℕ) (s : State) : Prop :=
 ∀j:Fin k,s.scalarHeap (a+j.val)=some ⟨starRingEnd ℂ (p.eval (fun _:Fin 1=>omega) j),false⟩

/-- Both prepared coefficient banks come from actual execution of the same
physical tapes. The second root is produced by charged inversion of the master;
unit norm identifies that inverse with its conjugate. -/
theorem execution {k : ℕ} (p : DProgram 1 k) (omega : ℂ) (unit:‖omega‖=1)
 (valid:p.Admissible (fun _:Fin 1=>omega)) (n : ℕ) (x : Fin n → ℂ)
 (b0 a0 R b1 a1 l c d B : ℕ) (s : State)
 (hmaster:s.scalarHeap 0=some ⟨omega,false⟩)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hld:UniformPreparationRowTableMachine.Disjoint k l d)
 (hcd:UniformPreparationRowTableMachine.Disjoint k c d)
 (hb:0 < b0) (hba0:b0+2+k ≤ a0) (haR:a0+k ≤ R) (hRb:R+1 ≤ b1) (hba1:b1+2+k ≤ a1)
 (hbudget:wordBudget l c d b0 a0 R b1 a1 k ≤ B)
 (hh:Header k b0 a0 R b1 a1 l c d s) (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b0 a0 b1 a1) u  ∧
 Values p (fun _:Fin 1=>omega) a0 u  ∧  ConjugateValues p omega a1 u  ∧
 u.scalarHeap R=some ⟨starRingEnd ℂ omega,false⟩  ∧ u.scalarHeap 0=s.scalarHeap 0  ∧
 UniformDAGLeafPreparationMachine.LiteralSource p l u  ∧
 UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c u.natHeap  ∧
 OutsideScalar b0 a0 R b1 a1 k s u  ∧ UniformPreparedDAGMachine.OutsideNat d k s u  ∧
 Frame s u  ∧ Header k b0 a0 R b1 a1 l c d u  ∧ u.pc=335 := by
 have hB:l+c+d+b0+a0+R+b1+a1+8*k+400 ≤ B:=hbudget
 have hn:omega ≠ 0:=by intro he;simp [he] at unit
 have hinv:=inverse_runs n B x s omega hmaster hn hpc hs (by omega) (by rw [hh.inverseRoot];omega)
 let inv:=inverseEnd s omega
 have hinvFrame:Frame s inv:=inverse_frame s omega
 have hinvHeader:=hh.transport hinvFrame
 have hinvPC:inv.pc=5:=by simp [inv,inverseEnd,inverseComputed,inverseOne,inverseLoaded,writeNat,writeScalar,next,hpc]
 have hzero:inv.natReg 359=0:=by simp [inv,inverseEnd,inverseComputed,inverseOne,inverseLoaded,writeNat,writeScalar,next]
 have hboot0:BoundedRuns program n x B inv 8 (applyBlock firstOps inv):=by
   apply block_runs firstOps 5 n B x inv firstOps_code hinvPC hinv.final_bound (by change 5+8 ≤ B;omega)
   simp [peak,UniformPreparedDAGMachine.peak,firstOps,UniformPreparedDAGMachine.Op.value,
     UniformPreparedDAGMachine.Op.apply,writeNat,next,hzero,hinvHeader.length,
     hinvHeader.firstLeaves,hinvHeader.firstResults,hinvHeader.literals,hinvHeader.tape,hinvHeader.rows]
   omega
 let beforeFirst:=applyBlock firstOps inv
 have hp0:beforeFirst.pc=13:=by rw [applyBlock_pc,hinvPC];rfl
 have hh0:=first_arguments inv hinvHeader hzero
 have hheap0:beforeFirst.natHeap=s.natHeap:=by rw [block_natHeap];rfl
 have hm0:beforeFirst.scalarHeap 0=some ⟨omega,false⟩:=by
   rw [block_scalarHeap]
   simp [inv,inverseEnd,hh.inverseRoot,show 0 ≠ R by omega,hmaster]
 have hl0:UniformDAGLeafPreparationMachine.LiteralSource p l beforeFirst:=by
   simpa only [UniformDAGLeafPreparationMachine.LiteralSource,UniformDAGLiteralBankMachine.RationalSource,
     UniformDAGLiteralBankMachine.Source,hheap0] using hliterals
 have ht0:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c beforeFirst.natHeap:=by
   simpa only [hheap0] using htape
 have hb0:WordBound B {beforeFirst with pc:=0}:=changePC_bound B _ 0 hboot0.final_bound (by omega)
 obtain ⟨v,hv,hvValues,_hvRoots,_hvLits,_hvTable,hvOutside,hvNat,hvFrame,_hvMaster,_hvSource,_hvHeader,_hvPC⟩:=
   UniformPreparedDAGMachine.execution_single_master p omega valid n x b0 l c d a0 B {beforeFirst with pc:=0}
     hm0 hl0 ht0 hcd hb (by omega) (by unfold UniformPreparedDAGMachine.wordBudget;omega) (by cases hh0;constructor <;> assumption) rfl hb0
 have hfirst:=UniformBoundedAssembly.boundedExecution_placed first_code
   (by rw [UniformPreparedDAGMachine.program_length];omega) (by omega) hv
 rw [UniformDAGLeafPreparationMachine.reset_placed beforeFirst 13 hp0] at hfirst
 let first:State:={v with pc:=170}
 have hfirstFrame:Frame s first:=hinvFrame.trans ((firstOps_frame inv).trans (Frame.of_base hvFrame))
 have hfirstHeader:=hh.transport hfirstFrame
 have hfirstZero:first.natReg 359=0:=(hvFrame.2.2 359 (by decide)).trans
   (by simp [beforeFirst,applyBlock,UniformPreparedDAGMachine.applyBlock,firstOps,
     UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,writeNat,next,hzero])
 have hfirstNat:UniformPreparedDAGMachine.OutsideNat d k s first:=by
   intro i hi
   exact (hvNat i hi).trans (congrFun hheap0 i)
 have htemp:first.scalarHeap R=some ⟨omega⁻¹,false⟩:=by
   rw [hvOutside R (Or.inr (by omega)) (Or.inr haR),block_scalarHeap]
   simp [inv,inverseEnd,hh.inverseRoot]
 have hboot1:BoundedRuns program n x B first 8 (applyBlock secondOps first):=by
   apply block_runs secondOps 170 n B x first secondOps_code rfl hfirst.final_bound (by change 170+8 ≤ B;omega)
   simp [peak,UniformPreparedDAGMachine.peak,secondOps,UniformPreparedDAGMachine.Op.value,
     UniformPreparedDAGMachine.Op.apply,writeNat,next,hfirstZero,hfirstHeader.length,
     hfirstHeader.inverseRoot,hfirstHeader.secondLeaves,hfirstHeader.secondResults,
     hfirstHeader.literals,hfirstHeader.tape,hfirstHeader.rows]
   omega
 let beforeSecond:=applyBlock secondOps first
 have hp1:beforeSecond.pc=178:=by rw [applyBlock_pc];rfl
 have hh1:=second_arguments first hfirstHeader hfirstZero
 have hl1:UniformDAGLeafPreparationMachine.LiteralSource p l beforeSecond:=by
   have hh:=literal_source_transport p l d s first hld hfirstNat hliterals
   simpa only [UniformDAGLeafPreparationMachine.LiteralSource,UniformDAGLiteralBankMachine.RationalSource,
     UniformDAGLiteralBankMachine.Source,beforeSecond,block_natHeap] using hh
 have ht1:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c beforeSecond.natHeap:=by
   simpa only [beforeSecond,block_natHeap] using node_tape_transport p c d s first hcd hfirstNat htape
 have hr1:UniformDAGLeafPreparationMachine.RootSource R (fun _:Fin 1=>omega⁻¹) beforeSecond:=by
   intro j
   have hj:j.val=0:=by have hj:=j.isLt;omega
   simpa only [hj,Nat.add_zero,beforeSecond,block_scalarHeap] using htemp
 have hb1:WordBound B {beforeSecond with pc:=0}:=changePC_bound B _ 0 hboot1.final_bound (by omega)
 have validInv:p.Admissible (fun _:Fin 1=>omega⁻¹):=
   (p.admissible_inverse_roots (fun _:Fin 1=>omega) (fun _=>unit)).mpr valid
 obtain ⟨w,hw,hwValues,_hwRoots,_hwLits,_hwTable,hwOutside,hwNat,hwFrame,_hwMaster,_hwSource,_hwHeader,_hwPC⟩:=
   UniformPreparedDAGMachine.execution p (fun _:Fin 1=>omega⁻¹) validInv n x R b1 l c d a1 B {beforeSecond with pc:=0}
     hr1 hl1 ht1 hcd hRb (by omega) (by omega) (by unfold UniformPreparedDAGMachine.wordBudget;omega) (by cases hh1;constructor <;> assumption) rfl hb1
 have hsecond:=UniformBoundedAssembly.boundedExecution_placed second_code
   (by rw [UniformPreparedDAGMachine.program_length];omega) (by omega) hw
 rw [UniformDAGLeafPreparationMachine.reset_placed beforeSecond 178 hp1] at hsecond
 let final:State:={w with pc:=335}
 have hf:Frame s final:=hfirstFrame.trans ((secondOps_frame first).trans (Frame.of_base hwFrame))
 have hfNat:UniformPreparedDAGMachine.OutsideNat d k s final:=by
   intro i hi
   exact (hwNat i hi).trans ((congrFun (block_natHeap secondOps first) i).trans (hfirstNat i hi))
 have hfOutside:OutsideScalar b0 a0 R b1 a1 k s final:=by
   intro i hi h0 h0a h1 h1a
   rw [hwOutside i (by omega) h1a,block_scalarHeap,hvOutside i (by omega) h0a,block_scalarHeap]
   change Function.update s.scalarHeap (s.natReg 353) (some ⟨omega⁻¹,false⟩) i=s.scalarHeap i
   rw [hh.inverseRoot,Function.update_of_ne hi]
 have hfValues:Values p (fun _:Fin 1=>omega) a0 final:=by
   intro j
   rw [hwOutside _ (Or.inl (by have hj:=j.isLt;omega)) (Or.inl (by have hj:=j.isLt;omega)),block_scalarHeap]
   exact hvValues j
 have hfConjugate:ConjugateValues p omega a1 final:=by
   intro j
   have h:=hwValues j
   change w.scalarHeap (a1+j.val)=some ⟨p.eval (fun _:Fin 1=>omega⁻¹) j,false⟩ at h
   simpa only [p.eval_inverse_roots (fun _:Fin 1=>omega) (fun _=>unit)] using h
 have hfRoot:final.scalarHeap R=some ⟨starRingEnd ℂ omega,false⟩:=by
   rw [hwOutside R (Or.inl (by omega)) (Or.inl (by omega)),block_scalarHeap,htemp,Complex.inv_eq_conj unit]
 have halt:BoundedExecution program n x B final 1 final:=.halt hsecond.final_bound
   (by rw [step];rfl)
 refine ⟨final,?_,hfValues,hfConjugate,hfRoot,?_,literal_source_transport p l d s final hld hfNat hliterals,
   node_tape_transport p c d s final hcd hfNat htape,hfOutside,hfNat,hf,hh.transport hf,rfl⟩
 · have hall:=((((hinv.trans hboot0).trans hfirst).trans hboot1).trans hsecond).executes halt
   convert hall using 1
   unfold runtime
   omega
 · exact hfOutside 0 (by omega) (Or.inl hb) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

/-- The caller's actual canonical master root closes the unit-norm premise;
no primitive-root permutation or supplied conjugate bank is used. -/
theorem execution_specifiedRoot {k : ℕ} (p : DProgram 1 k) (D : ℕ)
 (valid:p.Admissible (fun _:Fin 1=>(zeta D))) (n : ℕ) (x : Fin n → ℂ)
 (b0 a0 R b1 a1 l c d B : ℕ) (s : State)
 (hmaster:s.scalarHeap 0=some ⟨(zeta D),false⟩)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hld:UniformPreparationRowTableMachine.Disjoint k l d)
 (hcd:UniformPreparationRowTableMachine.Disjoint k c d)
 (hb:0 < b0) (hba0:b0+2+k ≤ a0) (haR:a0+k ≤ R) (hRb:R+1 ≤ b1) (hba1:b1+2+k ≤ a1)
 (hbudget:wordBudget l c d b0 a0 R b1 a1 k ≤ B)
 (hh:Header k b0 a0 R b1 a1 l c d s) (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b0 a0 b1 a1) u  ∧
 Values p (fun _:Fin 1=>(zeta D)) a0 u  ∧  ConjugateValues p (zeta D) a1 u  ∧
 u.scalarHeap R=some ⟨starRingEnd ℂ (zeta D),false⟩  ∧ u.scalarHeap 0=s.scalarHeap 0  ∧
 UniformDAGLeafPreparationMachine.LiteralSource p l u  ∧
 UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c u.natHeap  ∧
 OutsideScalar b0 a0 R b1 a1 k s u  ∧ UniformPreparedDAGMachine.OutsideNat d k s u  ∧
 Frame s u  ∧ Header k b0 a0 R b1 a1 l c d u  ∧ u.pc=335 := by
 exact execution p (zeta D) (specifiedRoot_norm D) valid n x b0 a0 R b1 a1 l c d B s
   hmaster hliterals htape hld hcd hb hba0 haR hRb hba1 hbudget hh hpc hs

theorem wordBudget_polynomial (l c d b0 a0 R b1 a1 k : ℕ) :
 wordBudget l c d b0 a0 R b1 a1 k ≤400*(l+c+d+b0+a0+R+b1+a1+k+1) := by
 unfold wordBudget
 simp only [Nat.mul_add,Nat.mul_one]
 omega

theorem runtime_bound {k : ℕ} (p : DProgram 1 k) (l B b0 a0 b1 a1 : ℕ) (s : State)
 (hl:UniformDAGLeafPreparationMachine.LiteralSource p l s) (hs:WordBound B s) :
 runtime p b0 a0 b1 a1 ≤136+2*k*(14*(Nat.log2 (B+1)+1)+77) := by
 have h0:=UniformPreparedDAGMachine.runtime_bound p l B b0 a0 s hl hs
 have h1:=UniformPreparedDAGMachine.runtime_bound p l B b1 a1 s hl hs
 unfold runtime
 simp only [Nat.mul_assoc]
 omega

theorem saved_headers_retained (s u : State) (h:Frame s u) (i : Fin 7) :
 u.natReg (100+i.val)=s.natReg (100+i.val) :=
 h.2.2 _ (by have hi:=i.isLt;unfold Protected UniformPreparedDAGMachine.Protected;omega)

theorem scalar_prefix_retained (b0 a0 R b1 a1 k endAddr : ℕ) (s u : State)
 (h:OutsideScalar b0 a0 R b1 a1 k s u)
 (h0:endAddr≤b0) (ha:endAddr≤a0) (hR:endAddr≤R) (h1:endAddr≤b1) (h1a:endAddr≤a1) :
 ∀i,i<endAddr→u.scalarHeap i=s.scalarHeap i := by
 intro i hi
 exact h i (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

end
end ExactFourierCircuits.UniformPreparedDAGConjugateMachine
