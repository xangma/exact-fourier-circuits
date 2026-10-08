import UniformFixedNetworkScalarPaddingLoopMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkExchangeChildMachine
open UniformMachine
open UniformTensorMonomialMachine (setPC Op applyBlock readable peak BlockAt block_runs)
open UniformFixedNetworkShearChildMachine (Present roleBase role_bound role_disjoint role_outside)

/-- Direct signed swap preserves each individual input dependency flag. -/
def boot : List Op := [.literal 3324 1,.literal 3323 0]
def program : Program := boot.map Op.code++[.scalarLiteral 113 (-1),
 .branchLT 3323 3322 4 13,.natBinary .add 3325 3320 3323,
 .natBinary .add 3326 3321 3323,.loadScalar 110 3325,.loadScalar 111 3326,
 .fieldBinary .mul 112 113 110,.storeScalar 3325 111,.storeScalar 3326 112,
 .natBinary .add 3323 3323 3324,.jump 3,.halt]
lemma program_length : program.length=14 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i < 2 at hi;interval_cases i <;> rfl
lemma loop_code (i:ℕ) (hi:i < 11) : program[3+i]?=
 ([.branchLT 3323 3322 4 13,.natBinary .add 3325 3320 3323,
 .natBinary .add 3326 3321 3323,.loadScalar 110 3325,.loadScalar 111 3326,
 .fieldBinary .mul 112 113 110,.storeScalar 3325 111,.storeScalar 3326 112,
 .natBinary .add 3323 3323 3324,.jump 3,.halt]:Program)[i]? := by interval_cases i <;> rfl

noncomputable section
def negative (a:Scalar) : Scalar := ⟨-a.value,a.dependent⟩
structure Header (D S V i:ℕ) (s:State) : Prop where
 pc:s.pc=3
 dst:s.natReg 3320=D
 src:s.natReg 3321=S
 volume:s.natReg 3322=V
 index:s.natReg 3323=i
 one:s.natReg 3324=1
 minus:s.scalarReg 113=UniformInPlaceMachine.prepared (-1)
def PairPresent (D S V i:ℕ) (a b:Fin V → Scalar) (s:State) : Prop :=
 (∀j,s.scalarHeap (D+j.val)=some (if j.val < i then b j else a j)) ∧ (∀j,s.scalarHeap (S+j.val)=some (if j.val < i then negative (a j) else b j))
def entered (s:State) := setPC s 4
def dstAddress (D i:ℕ) (s:State) := writeNat (entered s) 3325 (D+i)
def srcAddress (D S i:ℕ) (s:State) := writeNat (dstAddress D i s) 3326 (S+i)
def dstLoaded (D S i:ℕ) (a:Scalar) (s:State) := writeScalar (srcAddress D S i s) 110 a
def srcLoaded (D S i:ℕ) (a b:Scalar) (s:State) := writeScalar (dstLoaded D S i a s) 111 b
def negated (D S i:ℕ) (a b:Scalar) (s:State) := writeScalar (srcLoaded D S i a b s) 112 (negative a)
def dstStored (D S i:ℕ) (a b:Scalar) (s:State) : State :=
 {next (negated D S i a b s) with scalarHeap:=Function.update s.scalarHeap (D+i) (some b)}
def srcStored (D S i:ℕ) (a b:Scalar) (s:State) : State :=
 {next (dstStored D S i a b s) with scalarHeap:=Function.update (Function.update s.scalarHeap (D+i) (some b)) (S+i) (some (negative a))}
def advanced (D S i:ℕ) (a b:Scalar) (s:State) := writeNat (srcStored D S i a b s) 3323 (i+1)
def rowEnd (D S i:ℕ) (a b:Scalar) (s:State) := setPC (advanced D S i a b s) 3
structure Frame (D S V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,j < 3323 ∨ 3325 ≤ j ∧ j ≠ 3325 ∧ j ≠ 3326 → u.natReg j=s.natReg j
 scalarReg:∀j,j < 110 ∨ 114 ≤ j → u.scalarReg j=s.scalarReg j
 scalarHeap:∀z,(z < D ∨ D+V ≤ z) → (z < S ∨ S+V ≤ z) → u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (D S V:ℕ) (s:State) : Frame D S V s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.pc {D S V:ℕ} {s u:State} (f:Frame D S V s u) (p:ℕ) : Frame D S V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {D S V:ℕ} {s u t:State} (f:Frame D S V s u) (g:Frame D S V u t) : Frame D S V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun j h=>(g.natReg j h).trans (f.natReg j h),fun j h=>(g.scalarReg j h).trans (f.scalarReg j h),
 fun z h k=>(g.scalarHeap z h k).trans (f.scalarHeap z h k)⟩
lemma rowEnd_frame (D S V i:ℕ) (a b:Scalar) (s:State) (hi:i < V) : Frame D S V s (rowEnd D S i a b s) := by
 refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
 · intro j hj;simp (disch:=omega) [rowEnd,advanced,srcStored,dstStored,negated,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next]
 · intro j hj;simp (disch:=omega) [rowEnd,advanced,srcStored,dstStored,negated,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next]
 · intro z hd hs;change (Function.update (Function.update s.scalarHeap (D+i) (some b)) (S+i) (some (negative a))) z=s.scalarHeap z
   rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
lemma rowEnd_header (D S V i:ℕ) (a b:Scalar) (s:State) (h:Header D S V i s) : Header D S V (i+1) (rowEnd D S i a b s) := by
 rcases h with ⟨pc,dd,ss,vv,idx,one,minus⟩
 constructor <;> simp [rowEnd,advanced,srcStored,dstStored,negated,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next,dd,ss,vv,one,minus]
lemma row_bounded (B n D S V i:ℕ) (x:Fin n → ℂ) (a b:Scalar) (s:State)
 (h:Header D S V i s) (hi:i < V) (ha:s.scalarHeap (D+i)=some a) (hb:s.scalarHeap (S+i)=some b)
 (hs:WordBound B s) (code:14 ≤ B) (dst:D+V ≤ B) (src:S+V ≤ B) :
 BoundedRuns program n x B s 10 (rowEnd D S i a b s) := by
 have b0:=changePC_bound B s 4 hs (by omega)
 have b1:=writeNat_bound B _ 3325 (D+i) b0 (by change 5 ≤ B;omega) (by omega)
 have b2:=writeNat_bound B _ 3326 (S+i) b1 (by change 6 ≤ B;omega) (by omega)
 have b3:=writeScalar_bound B _ 110 a b2 (by change 7 ≤ B;omega)
 have b4:=writeScalar_bound B _ 111 b b3 (by change 8 ≤ B;omega)
 have b5:=writeScalar_bound B _ 112 (negative a) b4 (by change 9 ≤ B;omega)
 have b6:=UniformInPlaceMachine.storeScalar_bound B _ (D+i) b b5 (by change 10 ≤ B;omega) (by omega)
 have b7:=UniformInPlaceMachine.storeScalar_bound B _ (S+i) (negative a) b6 (by change 11 ≤ B;omega) (by omega)
 have b8:=writeNat_bound B _ 3323 (i+1) b7 (by change 12 ≤ B;omega) (by omega)
 have b9:=changePC_bound B _ 3 b8 (by omega)
 rcases h with ⟨pc,dd,ss,vv,idx,one,minus⟩
 refine .next hs ?_ (.next b0 ?_ (.next b1 ?_ (.next b2 ?_ (.next b3 ?_ (.next b4 ?_ (.next b5 ?_ (.next b6 ?_ (.next b7 ?_ (.next b8 ?_ (.refl b9))))))))))
 all_goals simp [step,program,boot,rowEnd,advanced,srcStored,dstStored,negated,srcLoaded,dstLoaded,srcAddress,dstAddress,entered,setPC,writeNat,writeScalar,next,evalNat,pc,dd,ss,vv,idx,one,ha,hb,hi,minus,evalField,UniformInPlaceMachine.prepared,negative]
lemma rowEnd_pair (D S V i:ℕ) (a b:Fin V → Scalar) (s:State) (hi:i < V)
 (pair:PairPresent D S V i a b s) (disjoint:∀j l:Fin V,D+j.val ≠ S+l.val) :
 PairPresent D S V (i+1) a b (rowEnd D S i (a ⟨i,hi⟩) (b ⟨i,hi⟩) s) := by
 constructor
 · intro j
   change (Function.update (Function.update s.scalarHeap (D+i) (some (b ⟨i,hi⟩))) (S+i) (some (negative (a ⟨i,hi⟩)))) (D+j.val)=_
   rw [Function.update_of_ne (disjoint j ⟨i,hi⟩)]
   by_cases hj:j.val=i
   · have eq:j=(⟨i,hi⟩:Fin V):=Fin.ext hj
     subst j
     simp [show i < i+1 by omega]
   · rw [Function.update_of_ne (by omega),pair.1 j]
     have eq:(j.val < i)↔j.val < i+1:=by omega
     simp only [eq]
 · intro j
   change (Function.update (Function.update s.scalarHeap (D+i) (some (b ⟨i,hi⟩))) (S+i) (some (negative (a ⟨i,hi⟩)))) (S+j.val)=_
   by_cases hj:j.val=i
   · have eq:j=(⟨i,hi⟩:Fin V):=Fin.ext hj
     subst j
     simp [show i < i+1 by omega]
   · rw [Function.update_of_ne (by omega),Function.update_of_ne (disjoint ⟨i,hi⟩ j).symm,pair.2 j]
     have eq:(j.val < i)↔j.val < i+1:=by omega
     simp only [eq]
theorem loop_execution (B n D S V count:ℕ) (x:Fin n → ℂ) (a b:Fin V → Scalar)
 (code:14 ≤ B) (dst:D+V ≤ B) (src:S+V ≤ B) (disjoint:∀j l:Fin V,D+j.val ≠ S+l.val) :
 ∀i s,i+count=V → Header D S V i s → PairPresent D S V i a b s → WordBound B s → ∃u,
 BoundedExecution program n x B s (10*count+2) u ∧ PairPresent D S V V a b u ∧ Frame D S V s u := by
 induction count with
 | zero=>
   intro i s eq h pair hs
   let u:=setPC s 13
   have ub:=changePC_bound B s 13 hs (by omega)
   refine ⟨u,.next hs ?_ (.halt ub ?_),?_,(Frame.refl D S V s).pc 13⟩
   · simp [step,h.pc,program,boot,h.index,h.volume,u,setPC,show ¬i < V by omega]
   · simp [step,u,setPC,program,boot]
   · have ic:i=V:=by omega
     subst i
     exact pair
 | succ count ih=>
   intro i s eq h pair hs
   have hi:i < V:=by omega
   let j:Fin V:=⟨i,hi⟩
   have ha:s.scalarHeap (D+i)=some (a j):=by simpa [j,show ¬i < i by omega] using pair.1 j
   have hb:s.scalarHeap (S+i)=some (b j):=by simpa [j,show ¬i < i by omega] using pair.2 j
   have run:=row_bounded B n D S V i x (a j) (b j) s h hi ha hb hs code dst src
   obtain ⟨u,last,out,frame⟩:=ih (i+1) (rowEnd D S i (a j) (b j) s) (by omega)
     (rowEnd_header D S V i (a j) (b j) s h) (rowEnd_pair D S V i a b s hi pair disjoint) run.final_bound
   refine ⟨u,?_,out,(rowEnd_frame D S V i (a j) (b j) s hi).trans frame⟩
   convert run.executes last using 1;ring

/-- Actual signed exchange on arbitrary dirty arrays. Its minus-one coefficient
is a charged literal, not an incoming prepared-bank premise. -/
theorem execution (B n D S V:ℕ) (x:Fin n → ℂ) (a b:Fin V → Scalar) (s:State)
 (pc:s.pc=0) (dd:s.natReg 3320=D) (ss:s.natReg 3321=S) (vv:s.natReg 3322=V)
 (data:(∀j,s.scalarHeap (D+j.val)=some (a j)) ∧ (∀j,s.scalarHeap (S+j.val)=some (b j)))
 (hs:WordBound B s) (code:14 ≤ B) (dst:D+V ≤ B) (src:S+V ≤ B)
 (disjoint:∀j l:Fin V,D+j.val ≠ S+l.val) :∃u,
 BoundedExecution program n x B s (10*V+5) u ∧ (∀j,some (b j)=u.scalarHeap (D+j.val)) ∧ (∀j,some (negative (a j))=u.scalarHeap (S+j.val)) ∧ Frame D S V s u := by
 have safe:readable boot s ∧ peak boot s ≤ B:=by simp [boot,readable,peak,Op.readable,Op.peak];omega
 have startup:=block_runs boot program 0 n B x s boot_code pc hs (by change 2 ≤ B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 let loop:=writeScalar ready 113 (UniformInPlaceMachine.prepared (-1))
 have lb:WordBound B loop:=writeScalar_bound B ready 113 (UniformInPlaceMachine.prepared (-1)) startup.final_bound (by simp [ready,UniformTensorMonomialMachine.applyBlock_pc,boot,pc];omega)
 have lit:step program n x ready=.running loop:=by simp [step,ready,boot,applyBlock,Op.apply,loop,program,writeNat,writeScalar,next,pc,UniformInPlaceMachine.prepared]
 have head:Header D S V 0 loop:=by constructor <;> simp [loop,ready,boot,applyBlock,Op.apply,writeNat,writeScalar,next,pc,dd,ss,vv]
 have pair:PairPresent D S V 0 a b loop:=by
   constructor
   · intro j;simpa [loop,ready,boot,applyBlock,Op.apply,writeNat,writeScalar,next] using data.1 j
   · intro j;simpa [loop,ready,boot,applyBlock,Op.apply,writeNat,writeScalar,next] using data.2 j
 obtain ⟨u,last,out,frame⟩:=loop_execution B n D S V V x a b code dst src disjoint 0 loop (by omega) head pair lb
 have before:Frame D S V s loop:=by
   refine ⟨rfl,rfl,rfl,?_,?_,fun _ _ _=>rfl⟩
   · intro j hj;simp (disch:=omega) [loop,ready,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
   · intro j hj;simp (disch:=omega) [loop,ready,boot,applyBlock,Op.apply,writeNat,writeScalar,next]
 refine ⟨u,?_,?_,?_,before.trans frame⟩
 · convert startup.executes (BoundedExecution.next startup.final_bound lit last) using 1
   simp only [boot,List.length_cons,List.length_nil]
   omega
 · intro j;simpa [show j.val < V from j.isLt] using (out.1 j).symm
 · intro j;simpa [show j.val < V from j.isLt] using (out.2 j).symm

def values {R V:ℕ} (d source:Fin R) (f:Fin R → Fin V → Scalar) : Fin R → Fin V → Scalar :=
 fun r j=>if r=d then f source j else if r=source then negative (f d j) else f r j
/-- Whole physical role-bank consequence of the actual two-bank loop. -/
theorem role_execution {R V:ℕ} (A B n:ℕ) (x:Fin n → ℂ) (d source:Fin R) (ne:d≠source)
 (f:Fin R → Fin V → Scalar) (s:State) (pc:s.pc=0)
 (dd:s.natReg 3320=roleBase A V d.val) (ss:s.natReg 3321=roleBase A V source.val)
 (vv:s.natReg 3322=V) (data:Present A R V f s) (hs:WordBound B s) (code:14≤B)
 (extent:A+R*V≤B) : ∃u,
 BoundedExecution program n x B s (10*V+5) u ∧ Present A R V (values d source f) u ∧
 Frame (roleBase A V d.val) (roleBase A V source.val) V s u := by
 obtain ⟨u,run,outD,outS,frame⟩:=execution B n (roleBase A V d.val) (roleBase A V source.val) V x (f d) (f source) s
   pc dd ss vv ⟨data d,data source⟩ hs code ((role_bound A V d).trans extent) ((role_bound A V source).trans extent)
   (role_disjoint A d source ne)
 refine ⟨u,run,?_,frame⟩
 intro r j
 by_cases hd:r=d
 · subst r
   simpa [values,roleBase] using (outD j).symm
 · by_cases ht:r=source
   · subst r
     simpa [values,roleBase,ne.symm] using (outS j).symm
   · rw [frame.scalarHeap _ (role_outside A d r hd j) (role_outside A source r ht j),data r j]
     simp [values,hd,ht]
end
end ExactFourierCircuits.UniformFixedNetworkExchangeChildMachine
