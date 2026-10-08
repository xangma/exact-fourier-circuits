import UniformReplayCoefficientMachine
import UniformCrossShearTableMachine
import UniformBoundedAssembly

set_option autoImplicit false

/- Physical coefficient decoding for a generated matching row. Negative
   coefficients use the conjugate positive bank with a charged negation;
   the six normalization constants are real and use their original cells. -/
namespace ExactFourierCircuits.UniformMatchingConjugateLoadMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
noncomputable section

def boot : List Op := [.literalScalar 71 (-1),.getScalar 70 2105,.putScalar 2106 70]
def positive : List Op := [.sub 2112 2105 2100,.add 2112 2103 2112,.getScalar 72 2112]
def negative : List Op := [.sub 2112 2105 2101,.add 2112 2103 2112,
 .getScalar 72 2112,.scalarMul 72 72 71]
def realConstant : List Op := [.getScalar 72 2105]
def store : List Op := [.putScalar 2107 72]
def program : Program := boot.map Op.code ++ [.branchLT 2105 2101 4 8] ++
 positive.map Op.code ++ [.jump 16,.branchLT 2105 2102 9 14] ++
 negative.map Op.code ++ [.jump 16] ++ realConstant.map Op.code ++
 [.jump 16] ++ store.map Op.code ++ [.halt]
theorem program_length : program.length=18 := rfl
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem positive_code : BlockAt positive program 4 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem negative_code : BlockAt negative program 9 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
theorem real_code : BlockAt realConstant program 14 := by
 intro i hi;change i<1 at hi;interval_cases i <;> rfl
theorem store_code : BlockAt store program 16 := by
 intro i hi;change i<1 at hi;interval_cases i <;> rfl
theorem positive_branch : program[3]?=some (.branchLT 2105 2101 4 8) := rfl
theorem negative_branch : program[8]?=some (.branchLT 2105 2102 9 14) := rfl
theorem positive_jump : program[7]?=some (.jump 16) := rfl
theorem negative_jump : program[13]?=some (.jump 16) := rfl
theorem real_jump : program[15]?=some (.jump 16) := rfl
theorem halt_at : program[17]?=some .halt := rfl

inductive Coefficient (R : ℕ) where
 | positive (i : Fin R)
 | negative (i : Fin R)
 | constant (i : Fin 6)

def address {R : ℕ} (C T P : ℕ) : Coefficient R → ℕ
 | .positive i => C+i.val
 | .negative i => T+i.val
 | .constant i => P+i.val
def value {R : ℕ} (K : ℕ) (bank : Fin R→ℂ) : Coefficient R → ℂ
 | .positive i => bank i
 | .negative i => -bank i
 | .constant i => UniformReplayCoefficientMachine.constant K i.val
def runtime {R : ℕ} : Coefficient R → ℕ
 | .positive _ => 10
 | .negative _ => 12
 | .constant _ => 9

structure Header {R : ℕ} (C T P V a b : ℕ) (c : Coefficient R) (s : State) : Prop where
 positive : s.natReg 2100=C
 negative : s.natReg 2101=T
 constants : s.natReg 2102=P
 conjugates : s.natReg 2103=V
 coefficient : s.natReg 2105=address C T P c
 original : s.natReg 2106=a
 conjugate : s.natReg 2107=b

structure Sources {R : ℕ} (K C T P V : ℕ) (bank : Fin R→ℂ) (s : State) : Prop where
 positive : ∀i,s.scalarHeap (C+i.val)=some (prepared (bank i))
 negative : ∀i,s.scalarHeap (T+i.val)=some (prepared (-bank i))
 conjugate : ∀i,s.scalarHeap (V+i.val)=some (prepared (starRingEnd ℂ (bank i)))
 constants : UniformReplayCoefficientMachine.Constants K P s

structure Layout (R C T P V a b B : ℕ) : Prop where
 positiveBelow : C+R≤T
 negativeBelow : T+R≤P
 constantsBelow : P+6≤V
 conjugatesBelow : V+R≤a
 destinations : a<b
 bound : b≤B
 code : 18≤B

def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
 u.rootOrders=s.rootOrders ∧ (∀r,r≠2112→u.natReg r=s.natReg r) ∧
 ∀r, r≠70 → r≠71 → r≠72 → u.scalarReg r=s.scalarReg r
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _ _ _=>rfl⟩
theorem Frame.trans {s t u : State} (h:Frame s t) (h':Frame t u) : Frame s u :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
 fun r hr=>(h'.2.2.2.1 r hr).trans (h.2.2.2.1 r hr),
 fun r h0 h1 h2=>(h'.2.2.2.2 r h0 h1 h2).trans (h.2.2.2.2 r h0 h1 h2)⟩

def ready (s : State) := applyBlock boot s
def decoded {R : ℕ} (s : State) : Coefficient R→State
 | .positive _ => setPC (applyBlock positive (setPC (ready s) 4)) 16
 | .negative _ => setPC (applyBlock negative (setPC (ready s) 9)) 16
 | .constant _ => setPC (applyBlock realConstant (setPC (ready s) 14)) 16
def finalState {R : ℕ} (s : State) (c : Coefficient R) := applyBlock store (decoded s c)

theorem constant_conjugate (K : ℕ) (i : Fin 6) :
 starRingEnd ℂ (UniformReplayCoefficientMachine.constant K i.val)=
 UniformReplayCoefficientMachine.constant K i.val := by
 have hi:=i.isLt
 interval_cases h:i.val <;>
   simp [UniformReplayCoefficientMachine.constant,h,map_inv₀,map_pow,starRingEnd_apply]

theorem source {R K C T P V : ℕ} {bank:Fin R→ℂ} {s:State}
 (src:Sources K C T P V bank s) (c:Coefficient R) :
 s.scalarHeap (address C T P c)=some (prepared (value K bank c)) := by
 cases c with
 | positive i => exact src.positive i
 | negative i => exact src.negative i
 | constant i => exact src.constants i.val i.isLt

theorem final_frame {R : ℕ} (s : State) (c : Coefficient R) : Frame s (finalState s c) := by
 cases c <;> refine ⟨rfl,rfl,rfl,?_,?_⟩
 all_goals intro r hr
 all_goals try intro h1 h2
 all_goals simp [Frame,finalState,decoded,ready,boot,positive,negative,realConstant,store,
   applyBlock,Op.apply,setPC,writeNat,writeScalar,next,hr]
 all_goals simp_all

theorem final_heap {R K C T P V a b B : ℕ} {bank:Fin R→ℂ} {s:State} (c:Coefficient R)
 (args:Header C T P V a b c s) (l:Layout R C T P V a b B)
 (src:Sources K C T P V bank s) :
 (finalState s c).scalarHeap=Function.update
  (Function.update s.scalarHeap a (some (prepared (value K bank c))))
  b (some (prepared (starRingEnd ℂ (value K bank c)))) := by
 cases c with
 | positive i =>
   have hi:=i.isLt
   have ne:V+i.val≠a:=by have:=l.conjugatesBelow;omega
   simp [finalState,decoded,ready,boot,positive,store,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next,args.original,args.conjugate,args.coefficient,
    args.positive,args.conjugates,address,value,ne,src.positive i,src.conjugate i]
 | negative i =>
   have hi:=i.isLt
   have ne:V+i.val≠a:=by have:=l.conjugatesBelow;omega
   simp [finalState,decoded,ready,boot,negative,store,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next,args.original,args.conjugate,args.coefficient,
    args.negative,args.conjugates,address,value,ne,src.negative i,src.conjugate i,prepared,evalField]
 | constant i =>
   have hi:=i.isLt
   have ne:P+i.val≠a:=by have:=l.constantsBelow;have:=l.conjugatesBelow;omega
   simp [finalState,decoded,ready,boot,realConstant,store,applyBlock,Op.apply,setPC,
    writeNat,writeScalar,next,args.original,args.conjugate,args.coefficient,
    address,value,ne,src.constants i.val i.isLt,constant_conjugate K i]

theorem ready_header {R C T P V a b : ℕ} {c:Coefficient R} {s:State}
 (h:Header C T P V a b c s) : Header C T P V a b c (ready s) := by
 rcases h with ⟨h0,h1,h2,h3,h5,h6,h7⟩
 constructor <;> simp [ready,boot,applyBlock,Op.apply,writeScalar,next,h0,h1,h2,h3,h5,h6,h7]

theorem ready_heap {R K C T P V a b : ℕ} {bank:Fin R→ℂ} {s:State}
 (c:Coefficient R) (args:Header C T P V a b c s) (src:Sources K C T P V bank s) :
 (ready s).scalarHeap=Function.update s.scalarHeap a (some (prepared (value K bank c))) := by
 simp [ready,boot,applyBlock,Op.apply,writeScalar,next,args.coefficient,args.original,source src c]

theorem ready_sources {R K C T P V a b B : ℕ} {bank:Fin R→ℂ} {s:State}
 (c:Coefficient R) (args:Header C T P V a b c s) (l:Layout R C T P V a b B)
 (src:Sources K C T P V bank s) : Sources K C T P V bank (ready s) := by
 constructor
 · intro i;rw [ready_heap c args src,Function.update_of_ne];exact src.positive i
   have:=i.isLt;have:=l.positiveBelow;have:=l.negativeBelow
   have:=l.constantsBelow;have:=l.conjugatesBelow;omega
 · intro i;rw [ready_heap c args src,Function.update_of_ne];exact src.negative i
   have:=i.isLt;have:=l.negativeBelow;have:=l.constantsBelow;have:=l.conjugatesBelow;omega
 · intro i;rw [ready_heap c args src,Function.update_of_ne];exact src.conjugate i
   have:=i.isLt;have:=l.conjugatesBelow;omega
 · intro i hi;rw [ready_heap c args src,Function.update_of_ne];exact src.constants i hi
   have:=l.constantsBelow;have:=l.conjugatesBelow;omega

theorem boot_runs {R K C T P V a b B n : ℕ} {bank:Fin R→ℂ} {s:State}
 (c:Coefficient R) (args:Header C T P V a b c s) (src:Sources K C T P V bank s)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) (hcode:18≤B) :
 BoundedRuns program n x B s 3 (ready s) := by
 apply block_runs boot program 0 n B x s boot_code pc hs (by change 0+3≤B;omega)
 · simp [boot,readable,Op.readable,Op.apply,writeScalar,next,args.coefficient,source src c]
 · simp [boot,peak,Op.peak,Op.apply,writeScalar,next]
   exact hs.2.1 2106

/-- Each address branch is a literal Nat branch. Its prepared scalar loads
and (for a signed coefficient) negation are charged, with no complex test. -/
theorem execution {R K C T P V a b B n : ℕ} {bank:Fin R→ℂ} {s:State}
 (c:Coefficient R) (args:Header C T P V a b c s) (l:Layout R C T P V a b B)
 (src:Sources K C T P V bank s) (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) :
 BoundedExecution program n x B s (runtime c) (finalState s c) := by
 have rb:=boot_runs c args src x pc hs l.code
 have rp:(ready s).pc=3:=by rw [ready,UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 have ra:=ready_header args
 have rs:=ready_sources c args l src
 have minus:(ready s).scalarReg 71=prepared (-1):=by
   simp [ready,boot,applyBlock,Op.apply,writeScalar,next,prepared]
 have path : BoundedRuns program n x B (ready s) (runtime c-5) (decoded s c) := by
   cases c with
   | positive i =>
     have hi:=i.isLt
     have hb:C+i.val<T:=by have:=l.positiveBelow;omega
     let v:=setPC (ready s) 4
     have vb:=changePC_bound B (ready s) 4 rb.final_bound (by have:=l.code;omega)
     have branch:BoundedRuns program n x B (ready s) 1 v:=.next rb.final_bound
       (by simp [step,rp,positive_branch,ra.coefficient,ra.negative,address,hb,v,setPC]) (.refl vb)
     have run:=block_runs positive program 4 n B x v positive_code rfl vb
       (by change 4+3≤B;have:=l.code;omega) (by
         simp [positive,readable,Op.readable,Op.apply,v,setPC,ra.coefficient,
           ra.positive,ra.conjugates,address,writeNat,next,rs.conjugate i]) (by
         simp [positive,peak,Op.peak,Op.apply,v,setPC,ra.coefficient,
           ra.positive,ra.conjugates,address,writeNat,next]
         have:=l.conjugatesBelow;have:=l.destinations;have:=l.bound;omega)
     have ep:(applyBlock positive v).pc=7:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
     have jump:BoundedRuns program n x B (applyBlock positive v) 1 (decoded s (.positive i)):=
       .next run.final_bound (by simp only [step,ep,positive_jump];rfl)
         (.refl (changePC_bound B _ 16 run.final_bound (by have:=l.code;omega)))
     exact branch.trans (run.trans jump)
   | negative i =>
     have hi:=i.isLt
     have ha:¬T+i.val<T:=by omega
     have hb:T+i.val<P:=by have:=l.negativeBelow;omega
     let w:=setPC (ready s) 8
     let v:=setPC (ready s) 9
     have wb:=changePC_bound B (ready s) 8 rb.final_bound (by have:=l.code;omega)
     have vb:=changePC_bound B (ready s) 9 rb.final_bound (by have:=l.code;omega)
     have b0:BoundedRuns program n x B (ready s) 1 w:=.next rb.final_bound
       (by simp [step,rp,positive_branch,ra.coefficient,ra.negative,address,ha,w,setPC]) (.refl wb)
     have b1:BoundedRuns program n x B w 1 v:=.next wb
       (by simp [step,w,v,setPC,negative_branch,ra.coefficient,ra.constants,address,hb]) (.refl vb)
     have run:=block_runs negative program 9 n B x v negative_code rfl vb
       (by change 9+4≤B;have:=l.code;omega) (by
         simp [negative,readable,Op.readable,Op.apply,v,setPC,ra.coefficient,
           ra.negative,ra.conjugates,address,writeNat,writeScalar,next,rs.conjugate i,
           minus,prepared,evalField]) (by
         simp [negative,peak,Op.peak,Op.apply,v,setPC,ra.coefficient,
           ra.negative,ra.conjugates,address,writeNat,writeScalar,next]
         have:=l.conjugatesBelow;have:=l.destinations;have:=l.bound;omega)
     have ep:(applyBlock negative v).pc=13:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
     have jump:BoundedRuns program n x B (applyBlock negative v) 1 (decoded s (.negative i)):=
       .next run.final_bound (by simp only [step,ep,negative_jump];rfl)
         (.refl (changePC_bound B _ 16 run.final_bound (by have:=l.code;omega)))
     exact b0.trans (b1.trans (run.trans jump))
   | constant i =>
     have ha:¬P+i.val<T:=by have:=l.negativeBelow;omega
     have hb:¬P+i.val<P:=by omega
     let w:=setPC (ready s) 8
     let v:=setPC (ready s) 14
     have wb:=changePC_bound B (ready s) 8 rb.final_bound (by have:=l.code;omega)
     have vb:=changePC_bound B (ready s) 14 rb.final_bound (by have:=l.code;omega)
     have b0:BoundedRuns program n x B (ready s) 1 w:=.next rb.final_bound
       (by simp [step,rp,positive_branch,ra.coefficient,ra.negative,address,ha,w,setPC]) (.refl wb)
     have b1:BoundedRuns program n x B w 1 v:=.next wb
       (by simp [step,w,v,setPC,negative_branch,ra.coefficient,ra.constants,address,hb]) (.refl vb)
     have run:=block_runs realConstant program 14 n B x v real_code rfl vb
       (by change 14+1≤B;have:=l.code;omega) (by
         simp [realConstant,readable,Op.readable,v,setPC,ra.coefficient,address,
           rs.constants i.val i.isLt]) (by simp [realConstant,peak,Op.peak])
     have ep:(applyBlock realConstant v).pc=15:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
     have jump:BoundedRuns program n x B (applyBlock realConstant v) 1 (decoded (R:=R) s (.constant i)):=
       .next run.final_bound (by simp only [step,ep,real_jump];rfl)
         (.refl (changePC_bound B _ 16 run.final_bound (by have:=l.code;omega)))
     exact b0.trans (b1.trans (run.trans jump))
 have dp:(decoded s c).pc=16:=by cases c <;> rfl
 have db:(decoded s c).natReg 2107=b:=by
   cases c <;> simp [decoded,positive,negative,realConstant,applyBlock,Op.apply,
     setPC,writeNat,writeScalar,next,ra.conjugate]
 have last:=block_runs store program 16 n B x (decoded s c) store_code dp path.final_bound
   (by change 16+1≤B;have:=l.code;omega) (by simp [store,readable,Op.readable])
   (by simp [store,peak,Op.peak,db];exact l.bound)
 have fp:(finalState s c).pc=17:=by rw [finalState,UniformTensorMonomialMachine.applyBlock_pc,dp];rfl
 have halt:BoundedExecution program n x B (finalState s c) 1 (finalState s c):=
   .halt last.final_bound (by simp only [step,fp,halt_at])
 have all:=rb.executes (path.executes (last.executes halt))
 convert all using 1
 cases c <;> rfl

theorem execution_result {R K C T P V a b B n : ℕ} {bank:Fin R→ℂ} {s:State}
 (c:Coefficient R) (args:Header C T P V a b c s) (l:Layout R C T P V a b B)
 (src:Sources K C T P V bank s) (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) :
 BoundedExecution program n x B s (runtime c) (finalState s c) ∧
 (finalState s c).scalarHeap a=some (prepared (value K bank c)) ∧
 (finalState s c).scalarHeap b=some (prepared (starRingEnd ℂ (value K bank c))) ∧
 (∀q,q≠a→q≠b→(finalState s c).scalarHeap q=s.scalarHeap q) ∧ Frame s (finalState s c) := by
 refine ⟨execution c args l src x pc hs,?_,?_,?_,final_frame s c⟩
 · rw [final_heap c args l src];simp [show a≠b by have:=l.destinations;omega]
 · rw [final_heap c args l src];simp
 · intro q h0 h1;rw [final_heap c args l src];simp [h0,h1]

/-- Read the coefficient field of the actual three-word matching row. No
coefficient pointer or decoder scratch is supplied through the entry header. -/
def rowLoad : List Op := [.literal 2110 3,.literal 2111 2,.mul 2112 2141 2110,
 .add 2112 2140 2112,.add 2112 2112 2111,.getNat 2105 2112]
def rowProgram : Program := UniformAssembly.embed (rowLoad.map Op.code) program [.halt] 24
theorem rowProgram_length : rowProgram.length=25 := rfl
theorem rowLoad_code : BlockAt rowLoad rowProgram 0 := by
 intro i hi;change i<6 at hi;interval_cases i <;> rfl
theorem row_helper_code : UniformAssembly.CodeAt program rowProgram 6 24 :=
 UniformAssembly.embed_code (rowLoad.map Op.code) program [.halt] 24
theorem row_halt : rowProgram[24]?=some .halt := rfl

structure RowArgs (C T P V a b D i : ℕ) (s:State) : Prop where
 positive : s.natReg 2100=C
 negative : s.natReg 2101=T
 constants : s.natReg 2102=P
 conjugates : s.natReg 2103=V
 original : s.natReg 2106=a
 conjugate : s.natReg 2107=b
 rows : s.natReg 2140=D
 index : s.natReg 2141=i

theorem address_bound {R C T P V a b B : ℕ} (l:Layout R C T P V a b B)
 (c:Coefficient R) : address C T P c≤B := by
 cases c with
 | positive i => have:=i.isLt;have:=l.positiveBelow;have:=l.negativeBelow
                 have:=l.constantsBelow;have:=l.conjugatesBelow;have:=l.destinations;have:=l.bound
                 simp only [address];omega
 | negative i => have:=i.isLt;have:=l.negativeBelow;have:=l.constantsBelow
                 have:=l.conjugatesBelow;have:=l.destinations;have:=l.bound
                 simp only [address];omega
 | constant i => have:=i.isLt;have:=l.constantsBelow;have:=l.conjugatesBelow
                 have:=l.destinations;have:=l.bound;simp only [address];omega

/-- This is the same rational-alias policy as the existing row printer.
It describes its physical pointer; scalar correctness of rational leaves is
the producer's separate prepared-bank theorem. -/
def fromReference {R : ℕ} : UniformReplayPrint.Coefficient R → Coefficient R
 | .prepared i neg => if neg then .negative i else .positive i
 | .rational q => if q=1 then .constant 0 else if q=(-1) then .constant 1 else .constant 2

theorem reference_address {R : ℕ} (C T P : ℕ) (ref:UniformReplayPrint.Coefficient R) :
 (UniformCrossShearTableMachine.locations R C T P).address ref=
 address C T P (fromReference ref) := by
 cases ref with
 | prepared i neg => cases neg <;> rfl
 | rational q =>
   simp only [UniformInPlaceMachine.Locations.address,UniformCrossShearTableMachine.locations,
     fromReference]
   split_ifs <;> rfl

theorem rowOf_coefficient {R : ℕ} (C T P : ℕ) (code:UniformReplayPrint.ShearCode ℕ R) :
 (UniformInPlaceMachine.rowOf (UniformCrossShearTableMachine.locations R C T P) code).coefficient=
 address C T P (fromReference code.coefficient) := reference_address C T P code.coefficient

def RowFrame (s u:State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧
 u.rootOrders=s.rootOrders ∧
 (∀q,q≠2105 → q≠2110 → q≠2111 → q≠2112 → u.natReg q=s.natReg q) ∧
 ∀q,q≠70 → q≠71 → q≠72 → u.scalarReg q=s.scalarReg q

theorem row_frame {R:ℕ} (s:State) (c:Coefficient R) :
 RowFrame s (finalState (setPC (applyBlock rowLoad s) 0) c) := by
 let e:=setPC (applyBlock rowLoad s) 0
 have f:=final_frame e c
 refine ⟨f.1,f.2.1,f.2.2.1,?_,?_⟩
 · intro q h0 h1 h2 h3
   rw [f.2.2.2.1 q h3]
   simp [e,rowLoad,applyBlock,Op.apply,setPC,writeNat,next,h0,h1,h2,h3]
 · intro q h0 h1 h2
   exact f.2.2.2.2 q h0 h1 h2

/-- The table is the physical output contract of CrossShear/SeedChunk.
The row's mathematical coefficient label identifies the scalar being read;
it does not assume any produced conjugate/scales or an execution action. -/
theorem execution_from_row {R K C T P V a b B n D : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row) (i:Fin rows.length) (c:Coefficient R)
 (args:RowArgs C T P V a b D i.val s) (l:Layout R C T P V a b B)
 (src:Sources K C T P V bank s) (table:UniformCrossShearTableMachine.Table D rows s)
 (coefficient:(rows[i.val]'i.isLt).coefficient=address C T P c)
 (rowBound:D+3*rows.length≤B) (code:25≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution rowProgram n x B s (runtime c+7) u ∧
 u.scalarHeap a=some (prepared (value K bank c)) ∧
 u.scalarHeap b=some (prepared (starRingEnd ℂ (value K bank c))) ∧
 (∀q,q≠a→q≠b→u.scalarHeap q=s.scalarHeap q) ∧
 u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ u.pc=24 ∧ RowFrame s u := by
 have ht:s.natHeap (D+3*i.val+2)=some (address C T P c):=by
   rw [←coefficient];exact (table i.val i.isLt).2.2
 let v:=applyBlock rowLoad s
 have safe:readable rowLoad s ∧ peak rowLoad s≤B:=by
   constructor
   · simp [rowLoad,readable,Op.readable,Op.apply,writeNat,next,args.rows,args.index,
       Nat.mul_comm i.val 3,ht]
   · simp [rowLoad,peak,Op.peak,Op.apply,writeNat,next,args.rows,args.index,
       Nat.mul_comm i.val 3,ht]
     have hi:=i.isLt
     have mul:3*i.val+2≤3*rows.length:=by omega
     have ab:=address_bound l c
     omega
 have head:=block_runs rowLoad rowProgram 0 n B x s rowLoad_code pc hs
   (by change 0+6≤B;omega) safe.1 safe.2
 have vp:v.pc=6:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
 let e:=setPC v 0
 have eh:Header C T P V a b c e:=by
   constructor <;> simp [e,v,rowLoad,applyBlock,Op.apply,setPC,writeNat,next,
    args.positive,args.negative,args.constants,args.conjugates,args.original,
    args.conjugate,args.rows,args.index,Nat.mul_comm i.val 3,ht]
 have es:Sources K C T P V bank e:=⟨src.positive,src.negative,src.conjugate,src.constants⟩
 have eb:=changePC_bound B v 0 head.final_bound (by omega)
 have middle:=execution_result c eh l es x rfl eb
 have moved:=UniformBoundedAssembly.boundedExecution_placed row_helper_code
   (by rw [program_length];omega) (by omega) middle.1
 have ep:UniformAssembly.placed 6 e=v:=by
   change {v with pc:=6}=v
   rw [←vp]
 rw [ep] at moved
 let u:=setPC (finalState e c) 24
 have ub:WordBound B u:=moved.final_bound
 have halt:BoundedExecution rowProgram n x B u 1 u:=.halt ub
   (by simp only [step,u,setPC,row_halt])
 refine ⟨u,?_,middle.2.1,middle.2.2.1,middle.2.2.2.1,
   middle.2.2.2.2.1,middle.2.2.2.2.2.1,middle.2.2.2.2.2.2.1,rfl,row_frame s c⟩
 convert head.executes (moved.executes halt) using 1
 change runtime c+7=6+(runtime c+1)
 omega

end
end ExactFourierCircuits.UniformMatchingConjugateLoadMachine
