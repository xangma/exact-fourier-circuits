import UniformPreparedDAGConjugateMachine
import UniformZeroFreeDiagonalMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedZeroFreeDAGMachine
open UniformMachine UniformAssembly
open UniformOffsetPreparationMachine (DProgram Values)
open OAI.ExactFourier

/-- Nat350..358 are the frozen conjugate producer's actual caller headers.
Nat380..382 supplies shift/differences/inverse bases. Nat383 is charged zero
scratch; six additional instructions load every diagonal phase argument. -/
def setup : Program := [.natLiteral 383 0,.natBinary .add 370 350 383,
 .natBinary .add 371 352 383,.natBinary .add 372 355 383,
 .natBinary .add 373 380 383,.natBinary .add 374 381 383,.natBinary .add 375 382 383]
def program : Program := UniformPreparedDAGConjugateMachine.program.map (relocate 0 336) ++ setup ++
 UniformZeroFreeDiagonalMachine.program.map (relocate 343 373) ++ [.halt]
theorem program_length : program.length=374 := by
 simp only [program,List.length_append,List.length_map,
   UniformPreparedDAGConjugateMachine.program_length,UniformZeroFreeDiagonalMachine.program_length]
 rfl

theorem conjugate_code : CodeAt UniformPreparedDAGConjugateMachine.program program 0 336 := by
 have h:=embed_code [] UniformPreparedDAGConjugateMachine.program
   (setup ++ UniformZeroFreeDiagonalMachine.program.map (relocate 343 373) ++ [.halt]) 336
 simpa only [embed,program,List.length_nil,List.nil_append,List.append_assoc] using h

theorem diagonal_code : CodeAt UniformZeroFreeDiagonalMachine.program program 343 373 := by
 intro i hi
 rw [UniformZeroFreeDiagonalMachine.program_length] at hi
 interval_cases i <;> rfl

noncomputable section
abbrev Op := UniformPreparedDAGMachine.Op
abbrev applyBlock := UniformPreparedDAGMachine.applyBlock
abbrev peak := UniformPreparedDAGMachine.peak
open UniformPreparedDAGMachine (Op.pc applyBlock_pc block_natHeap block_scalarHeap)
def BlockAt (os : List Op) (base : ℕ) : Prop :=
 ∀i,(hi:i < os.length)→program[base+i]?=some (os[i]'hi).code
theorem block_runs (os : List Op) (base n B : ℕ) (x : Fin n → ℂ) (s : State)
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
    cases o <;> simp [UniformMachine.step,hp,hfirst,UniformPreparedDAGMachine.Op.code,UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,evalNat]


def setupOps : List Op := [.lit 383 0,.add 370 350 383,.add 371 352 383,
 .add 372 355 383,.add 373 380 383,.add 374 381 383,.add 375 382 383]
theorem setup_code : BlockAt setupOps 336 := by
 intro i hi;change i < 7 at hi;interval_cases i <;> rfl

def Protected (i : ℕ) : Prop := UniformPreparedDAGConjugateMachine.Protected i ∧
 (i < 370 ∨ 380 ≤ i) ∧ i≠383
instance protectedDecidable (i : ℕ) : Decidable (Protected i) :=
 inferInstanceAs (Decidable (UniformPreparedDAGConjugateMachine.Protected i ∧
 (i < 370 ∨ 380 ≤ i) ∧ i≠383))
def Frame (s u : State) : Prop := u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 ∀i,Protected i→u.natReg i=s.natReg i
structure Header (k b0 a0 R b1 a1 l c rows d e f : ℕ) (s : State) : Prop where
 original : UniformPreparedDAGConjugateMachine.Header k b0 a0 R b1 a1 l c rows s
 shift : s.natReg 380=d
 differences : s.natReg 381=e
 inverses : s.natReg 382=f

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,fun i hi=>(h'.2.2 i hi).trans (h.2.2 i hi)⟩
theorem Frame.of_conjugate {s u : State} (h:UniformPreparedDAGConjugateMachine.Frame s u) : Frame s u :=
 ⟨h.1,h.2.1,fun i hi=>h.2.2 i hi.1⟩
theorem Frame.of_diagonal {s u : State} (h:UniformZeroFreeDiagonalMachine.Frame s u) : Frame s u :=
 ⟨h.2.2.1,h.2.1,fun i hi=>h.2.2.2.1 i (by rcases hi.2.1 with h|h <;> omega)⟩

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



theorem setup_frame (s : State) : Frame s (applyBlock setupOps s) := by
 apply block_frame
 intro o ho
 simp [setupOps] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem setup_arguments {k b0 a0 R b1 a1 l c rows d e f : ℕ} (s : State)
 (h:Header k b0 a0 R b1 a1 l c rows d e f s) :
 UniformZeroFreeDiagonalMachine.Header k a0 a1 d e f (applyBlock setupOps s) := by
 constructor <;> simp [applyBlock,UniformPreparedDAGMachine.applyBlock,setupOps,
   UniformPreparedDAGMachine.Op.apply,UniformPreparedDAGMachine.Op.value,writeNat,next,
   h.original.length,h.original.firstResults,h.original.secondResults,h.shift,h.differences,h.inverses]

def wordBudget (l c rows b0 a0 R b1 a1 d e f k : ℕ) : ℕ :=
 UniformPreparedDAGConjugateMachine.wordBudget l c rows b0 a0 R b1 a1 k+d+e+f+100

def runtime {k : ℕ} (p : DProgram 1 k) (b0 a0 b1 a1 : ℕ) : ℕ :=
 UniformPreparedDAGConjugateMachine.runtime p b0 a0 b1 a1+20*k+20

def OutsideScalar (b0 a0 R b1 a1 d e f k : ℕ) (s u : State) : Prop :=
 ∀i,i≠R→(i < b0 ∨ b0+2+k ≤ i)→(i < a0 ∨ a0+k ≤ i)→
 (i < b1 ∨ b1+2+k ≤ i)→(i < a1 ∨ a1+k ≤ i)→
 (i < d ∨ d+2 ≤ i)→(i < e ∨ e+k ≤ i)→(i < f ∨ f+k ≤ i)→u.scalarHeap i=s.scalarHeap i

/-- The conjugate source banks and every diagonal guard are derived from the
literal preceding phases. Only the original root and two physical tapes enter
as scalar/tape source contracts. There are no per-phase host writes. -/
theorem execution {k : ℕ} (p : DProgram 1 k) (omega : ℂ) (unit:‖omega‖=1)
 (valid:p.Admissible (fun _:Fin 1=>omega)) (n : ℕ) (x : Fin n→ℂ)
 (b0 a0 R b1 a1 l c rows d e f B : ℕ) (s : State)
 (hmaster:s.scalarHeap 0=some ⟨omega,false⟩)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hld:UniformPreparationRowTableMachine.Disjoint k l rows)
 (hcd:UniformPreparationRowTableMachine.Disjoint k c rows)
 (hb:0 < b0) (hba0:b0+2+k ≤ a0) (haR:a0+k ≤ R) (hRb:R+1 ≤ b1) (hba1:b1+2+k ≤ a1)
 (had:a1+k ≤ d) (hde:d+2 ≤ e) (hef:e+k ≤ f)
 (hbudget:wordBudget l c rows b0 a0 R b1 a1 d e f k ≤ B)
 (hh:Header k b0 a0 R b1 a1 l c rows d e f s) (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b0 a0 b1 a1) u ∧
 Values p (fun _:Fin 1=>omega) a0 u ∧UniformPreparedDAGConjugateMachine.ConjugateValues p omega a1 u ∧
 UniformZeroFreeDiagonalMachine.Result d e f (p.eval (fun _:Fin 1=>omega)) u ∧
 u.scalarHeap R=some ⟨starRingEnd ℂ omega,false⟩ ∧u.scalarHeap 0=s.scalarHeap 0 ∧
 UniformDAGLeafPreparationMachine.LiteralSource p l u ∧
 UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c u.natHeap ∧
 OutsideScalar b0 a0 R b1 a1 d e f k s u ∧UniformPreparedDAGMachine.OutsideNat rows k s u ∧
 Frame s u ∧Header k b0 a0 R b1 a1 l c rows d e f u ∧u.pc=373 := by
 have hB:UniformPreparedDAGConjugateMachine.wordBudget l c rows b0 a0 R b1 a1 k+d+e+f+100 ≤ B:=hbudget
 have hSmall:400+8*k+d+e+f ≤ B:=by
   unfold UniformPreparedDAGConjugateMachine.wordBudget at hB
   omega
 obtain ⟨v,hv,hvValues,hvConj,hvRoot,hvMaster,hvLiterals,hvTape,hvOutside,hvNat,hvFrame,hvHeader,_hvPC⟩:=
   UniformPreparedDAGConjugateMachine.execution p omega unit valid n x b0 a0 R b1 a1 l c rows B s
     hmaster hliterals htape hld hcd hb hba0 haR hRb hba1 (by omega) hh.original hpc hs
 have hConj:=UniformBoundedAssembly.boundedExecution_placed conjugate_code
   (by rw [UniformPreparedDAGConjugateMachine.program_length];omega) (by omega) hv
 simp only [placed,Nat.zero_add] at hConj
 let paired:State:={v with pc:=336}
 have hpairs:UniformZeroFreeDiagonalMachine.Sources a0 a1 (p.eval (fun _:Fin 1=>omega)) paired:=by
   intro j
   exact ⟨hvValues j,hvConj j⟩
 have hpHeader:Header k b0 a0 R b1 a1 l c rows d e f paired:=
   ⟨(by cases hvHeader;constructor <;> assumption),(hvFrame.2.2 380 (by decide)).trans hh.shift,
     (hvFrame.2.2 381 (by decide)).trans hh.differences,
     (hvFrame.2.2 382 (by decide)).trans hh.inverses⟩
 have hboot:BoundedRuns program n x B paired 7 (applyBlock setupOps paired):=by
   apply block_runs setupOps 336 n B x paired setup_code rfl hConj.final_bound (by change 336+7 ≤ B;omega)
   simp [peak,UniformPreparedDAGMachine.peak,setupOps,UniformPreparedDAGMachine.Op.value,
     UniformPreparedDAGMachine.Op.apply,writeNat,next,hpHeader.original.length,
     hpHeader.original.firstResults,hpHeader.original.secondResults,hpHeader.shift,
     hpHeader.differences,hpHeader.inverses]
   unfold UniformPreparedDAGConjugateMachine.wordBudget at hB
   omega
 let beforeDiag:=applyBlock setupOps paired
 have hpDiag:beforeDiag.pc=343:=by rw [applyBlock_pc];rfl
 have hDiagHeader:=setup_arguments paired hpHeader
 have hDiagSources:UniformZeroFreeDiagonalMachine.Sources a0 a1 (p.eval (fun _:Fin 1=>omega)) beforeDiag:=by
   simpa only [UniformZeroFreeDiagonalMachine.Sources,beforeDiag,block_scalarHeap] using hpairs
 have hDiagB:WordBound B {beforeDiag with pc:=0}:=changePC_bound B _ 0 hboot.final_bound (by omega)
 obtain ⟨w,hw,_hwPC,hwResult,hwSources,hwOutside,hwFrame⟩:=UniformZeroFreeDiagonalMachine.execution
   B n a0 a1 d e f x (p.eval (fun _:Fin 1=>omega)) {beforeDiag with pc:=0}
   (by cases hDiagHeader;constructor <;> assumption) rfl hDiagSources
   (by omega) (by omega) had hde hef (by omega) hDiagB
 have hDiag:=UniformBoundedAssembly.boundedExecution_placed diagonal_code
   (by rw [UniformZeroFreeDiagonalMachine.program_length];omega) (by omega) hw
 rw [UniformDAGLeafPreparationMachine.reset_placed beforeDiag 343 hpDiag] at hDiag
 let final:State:={w with pc:=373}
 have hf:Frame s final:=(Frame.of_conjugate hvFrame).trans ((setup_frame paired).trans (Frame.of_diagonal hwFrame))
 have hfHeader:Header k b0 a0 R b1 a1 l c rows d e f final:=by
   refine ⟨?_,?_,?_,?_⟩
   · constructor
     · exact (hf.2.2 350 (by decide)).trans hh.original.length
     · exact (hf.2.2 351 (by decide)).trans hh.original.firstLeaves
     · exact (hf.2.2 352 (by decide)).trans hh.original.firstResults
     · exact (hf.2.2 353 (by decide)).trans hh.original.inverseRoot
     · exact (hf.2.2 354 (by decide)).trans hh.original.secondLeaves
     · exact (hf.2.2 355 (by decide)).trans hh.original.secondResults
     · exact (hf.2.2 356 (by decide)).trans hh.original.literals
     · exact (hf.2.2 357 (by decide)).trans hh.original.tape
     · exact (hf.2.2 358 (by decide)).trans hh.original.rows
   · exact (hf.2.2 380 (by decide)).trans hh.shift
   · exact (hf.2.2 381 (by decide)).trans hh.differences
   · exact (hf.2.2 382 (by decide)).trans hh.inverses
 have hfNat:UniformPreparedDAGMachine.OutsideNat rows k s final:=by
   intro i hi
   rw [hwFrame.1,block_natHeap]
   exact hvNat i hi
 have hNatPair:final.natHeap=paired.natHeap:=hwFrame.1.trans (block_natHeap setupOps paired)
 have hfLiterals:UniformDAGLeafPreparationMachine.LiteralSource p l final:=by
   simpa only [UniformDAGLeafPreparationMachine.LiteralSource,UniformDAGLiteralBankMachine.RationalSource,
     UniformDAGLiteralBankMachine.Source,hNatPair] using hvLiterals
 have hfTape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c final.natHeap:=by
   simpa only [hNatPair] using hvTape
 have hfOutside:OutsideScalar b0 a0 R b1 a1 d e f k s final:=by
   intro i hi hb0 ha0 hb1 ha1 hd he hf'
   rw [hwOutside i hd he hf',block_scalarHeap]
   exact hvOutside i hi hb0 ha0 hb1 ha1
 have hfRoot:final.scalarHeap R=some ⟨starRingEnd ℂ omega,false⟩:=by
   rw [hwOutside R (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),block_scalarHeap]
   exact hvRoot
 have hfMaster:final.scalarHeap 0=s.scalarHeap 0:=by
   rw [hwOutside 0 (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),block_scalarHeap]
   exact hvMaster
 have halt:BoundedExecution program n x B final 1 final:=.halt hDiag.final_bound
   (by rw [step];rfl)
 refine ⟨final,?_,fun j=>(hwSources j).1,fun j=>(hwSources j).2,hwResult,
   hfRoot,hfMaster,hfLiterals,hfTape,hfOutside,hfNat,hf,hfHeader,rfl⟩
 have hall:=((hConj.trans hboot).trans hDiag).executes halt
 convert hall using 1
 unfold runtime
 omega


/-- A supplied canonical master root discharges the norm hypothesis, without
another root instruction or a supplied conjugate source. -/
theorem execution_specifiedRoot {k : ℕ} (p : DProgram 1 k) (D : ℕ)
 (valid:p.Admissible (fun _:Fin 1=>(zeta D))) (n : ℕ) (x : Fin n→ℂ)
 (b0 a0 R b1 a1 l c rows d e f B : ℕ) (s : State)
 (hmaster:s.scalarHeap 0=some ⟨(zeta D),false⟩)
 (hliterals:UniformDAGLeafPreparationMachine.LiteralSource p l s)
 (htape:UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c s.natHeap)
 (hld:UniformPreparationRowTableMachine.Disjoint k l rows)
 (hcd:UniformPreparationRowTableMachine.Disjoint k c rows)
 (hb:0 < b0) (hba0:b0+2+k ≤ a0) (haR:a0+k ≤ R) (hRb:R+1 ≤ b1) (hba1:b1+2+k ≤ a1)
 (had:a1+k ≤ d) (hde:d+2 ≤ e) (hef:e+k ≤ f)
 (hbudget:wordBudget l c rows b0 a0 R b1 a1 d e f k ≤ B)
 (hh:Header k b0 a0 R b1 a1 l c rows d e f s) (hpc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (runtime p b0 a0 b1 a1) u ∧
 Values p (fun _:Fin 1=>(zeta D)) a0 u ∧UniformPreparedDAGConjugateMachine.ConjugateValues p (zeta D) a1 u ∧
 UniformZeroFreeDiagonalMachine.Result d e f (p.eval (fun _:Fin 1=>(zeta D))) u ∧
 u.scalarHeap R=some ⟨starRingEnd ℂ (zeta D),false⟩ ∧u.scalarHeap 0=s.scalarHeap 0 ∧
 UniformDAGLeafPreparationMachine.LiteralSource p l u ∧
 UniformPreparationRowTableMachine.Tape (UniformPreparationRowTableMachine.nodes p) c u.natHeap ∧
 OutsideScalar b0 a0 R b1 a1 d e f k s u ∧UniformPreparedDAGMachine.OutsideNat rows k s u ∧
 Frame s u ∧Header k b0 a0 R b1 a1 l c rows d e f u ∧u.pc=373 := by
 exact execution p (zeta D) (UniformPreparedDAGConjugateMachine.specifiedRoot_norm D) valid n x
   b0 a0 R b1 a1 l c rows d e f B s hmaster hliterals htape hld hcd
   hb hba0 haR hRb hba1 had hde hef hbudget hh hpc hs

theorem wordBudget_polynomial (l c rows b0 a0 R b1 a1 d e f k : ℕ) :
 wordBudget l c rows b0 a0 R b1 a1 d e f k ≤
   500*(l+c+rows+b0+a0+R+b1+a1+d+e+f+k+1) := by
 unfold wordBudget UniformPreparedDAGConjugateMachine.wordBudget
 simp only [Nat.mul_add,Nat.mul_one]
 omega

theorem runtime_bound {k : ℕ} (p : DProgram 1 k) (l B b0 a0 b1 a1 : ℕ) (s : State)
 (hl:UniformDAGLeafPreparationMachine.LiteralSource p l s) (hs:WordBound B s) :
 runtime p b0 a0 b1 a1 ≤156+2*k*(14*(Nat.log2 (B+1)+1)+87) := by
 have h:=UniformPreparedDAGConjugateMachine.runtime_bound p l B b0 a0 b1 a1 s hl hs
 unfold runtime
 simp only [Nat.mul_add] at *
 omega

theorem saved_headers_retained (s u : State) (h:Frame s u) (i : Fin 7) :
 u.natReg (100+i.val)=s.natReg (100+i.val) :=
 h.2.2 _ (by have hi:=i.isLt
             unfold Protected UniformPreparedDAGConjugateMachine.Protected UniformPreparedDAGMachine.Protected
             omega)

theorem scalar_prefix_retained (b0 a0 R b1 a1 d e f k endAddr : ℕ) (s u : State)
 (h:OutsideScalar b0 a0 R b1 a1 d e f k s u)
 (h0:endAddr≤b0) (ha:endAddr≤a0) (hR:endAddr≤R) (h1:endAddr≤b1)
 (h1a:endAddr≤a1) (hd:endAddr≤d) (he:endAddr≤e) (hf:endAddr≤f) :
 ∀i,i<endAddr→u.scalarHeap i=s.scalarHeap i := by
 intro i hi
 exact h i (by omega) (Or.inl (by omega)) (Or.inl (by omega))
   (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
   (Or.inl (by omega)) (Or.inl (by omega))

/-- All diagonal denominators are nonzero consequences of the actually
produced result, rather than additional input bank or guard certificates. -/
theorem produced_nonzero {k : ℕ} (p : DProgram 1 k) (omega : ℂ)
 (d e f : ℕ) (s : State)
 (h:UniformZeroFreeDiagonalMachine.Result d e f (p.eval (fun _:Fin 1=>omega)) s) :
 (∃v,s.scalarHeap d=some v ∧v.dependent=false ∧v.value≠0) ∧
 ∀j:Fin k,∃v,s.scalarHeap (e+j.val)=some v ∧v.dependent=false ∧v.value≠0 :=
 UniformZeroFreeDiagonalMachine.produced_nonzero d e f _ s h

end
end ExactFourierCircuits.UniformPreparedZeroFreeDAGMachine
