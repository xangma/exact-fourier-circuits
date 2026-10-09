import UniformGlobalMatchingScaleMachine
import UniformGlobalScalePoolMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalMatchingPoolPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalMatchingScaleMachine (factor address FullFactorTable InactiveReady PairOutside)
open UniformPairMachine (prepared)
noncomputable section

/-- Actual count894 is copied once. The11-op initializer is followed by
repeated120-op real row preparation. No phase/table callback occurs. -/
def boot : List Op := [.literal 4361 0,.literal 4362 1,.add 4360 894 4361,
 .add 2141 4361 4361]
def beforeRows : Program := boot.map Op.code++
 UniformGlobalScalePoolMachine.program.map (relocate 4 15)
def program : Program := beforeRows++[.branchLT 2141 4360 16 138]++
 UniformGlobalMatchingScaleMachine.rowProgram.map (relocate 16 136)++
 [.natBinary .add 2141 2141 4362,.jump 15,.halt]
lemma beforeRows_length : beforeRows.length=15 := by
 simp [beforeRows,boot,UniformGlobalScalePoolMachine.program_length]
lemma program_length : program.length=139 := by
 simp [program,beforeRows_length,UniformGlobalMatchingScaleMachine.rowProgram_length]
lemma boot_code : BlockAt boot program 0 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma pool_code : CodeAt UniformGlobalScalePoolMachine.program program 4 15 := by
 let tail:Program:=[.branchLT 2141 4360 16 138]++
  (UniformGlobalMatchingScaleMachine.rowProgram.map (relocate 16 136)++
   [.natBinary .add 2141 2141 4362,.jump 15,.halt])
 have h:=UniformAssembly.embed_code (boot.map Op.code) UniformGlobalScalePoolMachine.program tail 15
 have len:(boot.map Op.code).length=4:=rfl
 have eq:UniformAssembly.embed (boot.map Op.code) UniformGlobalScalePoolMachine.program tail 15=program:=by
  simp only [UniformAssembly.embed,len,program,beforeRows,tail,List.append_assoc]
 rw [eq,len] at h
 exact h
lemma row_code : CodeAt UniformGlobalMatchingScaleMachine.rowProgram program 16 136 := by
 let head:Program:=beforeRows++[.branchLT 2141 4360 16 138]
 let tail:Program:=[.natBinary .add 2141 2141 4362,.jump 15,.halt]
 have len:head.length=16:=by simp [head,beforeRows_length]
 have h:=UniformAssembly.embed_code head UniformGlobalMatchingScaleMachine.rowProgram tail 136
 have eq:UniformAssembly.embed head UniformGlobalMatchingScaleMachine.rowProgram tail 136=program:=by
  simp only [UniformAssembly.embed,len,program,head,tail,List.append_assoc]
 rw [eq,len] at h
 exact h
lemma branch_at : program[15]?=some (.branchLT 2141 4360 16 138) := rfl
lemma advance_at : program[136]?=some (.natBinary .add 2141 2141 4362) := rfl
lemma jump_at : program[137]?=some (.jump 15) := rfl
lemma halt_at : program[138]?=some .halt := rfl

def Bounds (r : ℕ) (rows : List UniformInPlaceMachine.Row) : Prop :=
 ∀i:Fin rows.length,(rows[i.val]'i.isLt).dst<r ∧ (rows[i.val]'i.isLt).src<r
def Different (rows : List UniformInPlaceMachine.Row) : Prop :=
 ∀i:Fin rows.length,(rows[i.val]'i.isLt).dst≠(rows[i.val]'i.isLt).src
def Matching (rows : List UniformInPlaceMachine.Row) : Prop :=
 ∀i j:Fin rows.length,i≠j →
 (rows[i.val]'i.isLt).dst≠(rows[j.val]'j.isLt).dst ∧
 (rows[i.val]'i.isLt).dst≠(rows[j.val]'j.isLt).src ∧
 (rows[i.val]'i.isLt).src≠(rows[j.val]'j.isLt).dst ∧
 (rows[i.val]'i.isLt).src≠(rows[j.val]'j.isLt).src
lemma coordinate_ne (pool r d e l k : ℕ) (hd:d<r) (he:e<r) (ne:d≠e) :
 pool+l*r+d≠pool+k*r+e := by
 intro eq
 have eq':l*r+d=k*r+e:=by
  apply Nat.add_left_cancel (n:=pool)
  simpa only [Nat.add_assoc] using eq
 have h:=congrArg (fun t=>t%r) eq'
 apply ne
 simpa only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt he] using h
lemma pairOutside_other (pool r : ℕ) (rows : List UniformInPlaceMachine.Row)
 (bounds:Bounds r rows) (matching:Matching rows) (i j:Fin rows.length) (ne:i≠j)
 (lane:Fin 9) (side:Fin 2) : PairOutside pool r (rows[i.val]'i.isLt).dst
 (rows[i.val]'i.isLt).src (address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side) := by
 have h:=matching j i (Ne.symm ne)
 intro other
 fin_cases side
 · exact ⟨coordinate_ne pool r _ _ _ _ (bounds j).1 (bounds i).1 h.1,
   coordinate_ne pool r _ _ _ _ (bounds j).1 (bounds i).2 h.2.1⟩
 · exact ⟨coordinate_ne pool r _ _ _ _ (bounds j).2 (bounds i).1 h.2.2.1,
   coordinate_ne pool r _ _ _ _ (bounds j).2 (bounds i).2 h.2.2.2⟩
lemma address_bound (pool r d e : ℕ) (hd:d<r) (he:e<r) (lane:Fin 9) (side:Fin 2) :
 pool ≤ address pool r d e lane side ∧ address pool r d e lane side < pool+9*r := by
 have lm:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
 unfold address;split <;> constructor <;> omega

structure PoolInvariant {R K : ℕ} (pool r : ℕ) (rows : List UniformInPlaceMachine.Row)
 (bank : Fin R→ℂ) (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (i : ℕ) (s : State) : Prop where
 done:∀j:Fin rows.length,j.val < i → FullFactorTable pool r
  (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src
  (UniformMatchingConjugateLoadMachine.value K bank (co j)) s
 remaining:∀j:Fin rows.length,i ≤ j.val → ∀lane side,
  s.scalarHeap (address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side)=
  some (prepared 1)
 untouched:∀d,d<r → (∀j:Fin rows.length,d≠(rows[j.val]'j.isLt).dst ∧ d≠(rows[j.val]'j.isLt).src) →
  ∀lane:Fin 9,s.scalarHeap (pool+lane.val*r+d)=some (prepared 1)

lemma invariant_initial {R K : ℕ} (pool r : ℕ) (rows : List UniformInPlaceMachine.Row)
 (bank:Fin R→ℂ) (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (s : State) (bounds:Bounds r rows) (ones:UniformGlobalScalePoolMachine.Prefix pool (9*r) s) :
 PoolInvariant (K:=K) pool r rows bank co 0 s := by
 constructor
 · intro j hj;omega
 · intro j hj lane side
   have range:=address_bound pool r _ _ (bounds j).1 (bounds j).2 lane side
   have eq:address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side=
    pool+(address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side-pool):=by omega
   rw [eq];exact ones _ (by omega)
 · intro d hd hn lane
   have lm:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
   simpa only [Nat.add_assoc] using ones (lane.val*r+d) (by omega)
lemma invariant_step {R K : ℕ} (a b pool r : ℕ) (rows : List UniformInPlaceMachine.Row)
 (bank:Fin R→ℂ) (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (bounds:Bounds r rows) (matching:Matching rows) (i:Fin rows.length) (s u : State)
 (fresh:b<pool) (ab:a<b) (pre:PoolInvariant (K:=K) pool r rows bank co i.val s)
 (done:FullFactorTable pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src
  (UniformMatchingConjugateLoadMachine.value K bank (co i)) u)
 (outside:∀q,PairOutside pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src q →
  q≠a → q≠b → u.scalarHeap q=s.scalarHeap q) :
 PoolInvariant (K:=K) pool r rows bank co (i.val+1) u := by
 have same:∀j:Fin rows.length,j≠i → ∀lane side,
  u.scalarHeap (address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side)=
  s.scalarHeap (address pool r (rows[j.val]'j.isLt).dst (rows[j.val]'j.isLt).src lane side):=by
  intro j ne lane side
  have range:=address_bound pool r _ _ (bounds j).1 (bounds j).2 lane side
  exact outside _ (pairOutside_other pool r rows bounds matching i j (Ne.symm ne) lane side)
   (by omega) (by omega)
 constructor
 · intro j hj
   by_cases eq:j=i
   · subst j;exact done
   · intro lane side
     exact (same j eq lane side).trans (pre.done j (by have hne:=Fin.val_ne_of_ne eq;omega) lane side)
 · intro j hj lane side
   exact (same j (by intro eq;subst j;omega) lane side).trans (pre.remaining j (by omega) lane side)
 · intro d hd hn lane
   have range:pool ≤ pool+lane.val*r+d:=by omega
   have po:PairOutside pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src (pool+lane.val*r+d):=by
    intro other
    exact ⟨coordinate_ne pool r _ _ _ _ hd (bounds i).1 (hn i).1,
     coordinate_ne pool r _ _ _ _ hd (bounds i).2 (hn i).2⟩
   exact (outside _ po (by omega) (by omega)).trans (pre.untouched d hd hn lane)

lemma coefficient_sources_retained {R K C T P V a b B pool r : ℕ} {bank:Fin R→ℂ} {s u : State}
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B) (fresh:b<pool)
 (src:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (outside:∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → u.scalarHeap q=s.scalarHeap q) :
 UniformMatchingConjugateLoadMachine.Sources K C T P V bank u := by
 have h1:=layout.positiveBelow
 have h2:=layout.negativeBelow
 have h3:=layout.constantsBelow
 have h4:=layout.conjugatesBelow
 have h5:=layout.destinations
 have keep:∀q,q<a → u.scalarHeap q=s.scalarHeap q:=by
  intro q hq;exact outside q (Or.inl (by omega)) (by omega) (by omega)
 constructor
 · intro i
   have hi:=i.isLt
   rw [keep _ (by omega)];exact src.positive i
 · intro i
   have hi:=i.isLt
   rw [keep _ (by omega)];exact src.negative i
 · intro i
   have hi:=i.isLt
   rw [keep _ (by omega)];exact src.conjugate i
 · intro i hi
   rw [keep _ (by omega)];exact src.constants i hi
lemma constants_retained {a b pool r : ℕ} {s u : State} (low:6≤a) (ab:a<b) (fresh:b<pool)
 (src:UniformHadamardPairMachine.Constants s)
 (outside:∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → u.scalarHeap q=s.scalarHeap q) :
 UniformHadamardPairMachine.Constants u := by
 have keep:∀q,q<a → u.scalarHeap q=s.scalarHeap q:=by
  intro q hq;exact outside q (Or.inl (by omega)) (by omega) (by omega)
 exact ⟨(keep 1 (by omega)).trans src.1,(keep 2 (by omega)).trans src.2.1,
  (keep 3 (by omega)).trans src.2.2.1,(keep 4 (by omega)).trans src.2.2.2.1,
  (keep 5 (by omega)).trans src.2.2.2.2⟩

structure Cursor {R K : ℕ} (C T P V a b D pool r : ℕ)
 (rows : List UniformInPlaceMachine.Row) (bank:Fin R→ℂ) (i:ℕ) (s : State) : Prop where
 pc:s.pc=15
 args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i s
 pool:s.natReg 4330=pool
 radix:s.natReg 4331=r
 count:s.natReg 4360=rows.length
 one:s.natReg 4362=1
 sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s
 constants:UniformHadamardPairMachine.Constants s
 table:UniformCrossShearTableMachine.Table D rows s

def advanced (s : State) (i : ℕ) : State := {writeNat {s with pc:=136} 2141 (i+1) with pc:=15}

lemma iteration {R K C T P V a b B D pool r n : ℕ} {bank:Fin R→ℂ}
 (rows:List UniformInPlaceMachine.Row)
 (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (labels:∀j:Fin rows.length,(rows[j.val]'j.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P (co j))
 (bounds:Bounds r rows) (different:Different rows) (matching:Matching rows)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B) (poolBound:pool+9*r≤B)
 (code:139≤B) (i:Fin rows.length) (x:Fin n→ℂ) (s : State)
 (h:Cursor (K:=K) C T P V a b D pool r rows bank i.val s)
 (pre:PoolInvariant (K:=K) pool r rows bank co i.val s) (hs:WordBound B s) : ∃out,
 BoundedRuns program n x B s (UniformMatchingConjugateLoadMachine.runtime (co i)+105) out ∧
 Cursor (K:=K) C T P V a b D pool r rows bank (i.val+1) out ∧
 PoolInvariant (K:=K) pool r rows bank co (i.val+1) out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → out.scalarHeap q=s.scalarHeap q) := by
 let entry:State:={s with pc:=0}
 have eh:WordBound B entry:=changePC_bound B s 0 hs (by omega)
 have inactive:InactiveReady pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src entry:=by
  intro lane side ha;exact pre.remaining i (by omega) lane side
 have entryArgs:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val entry:=
  ⟨h.args.positive,h.args.negative,h.args.constants,h.args.conjugates,
   h.args.original,h.args.conjugate,h.args.rows,h.args.index⟩
 have entrySources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank entry:=
  ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩
 obtain ⟨u,run,last,factors,nh,outs,roots,outside,other⟩:=
  UniformGlobalMatchingScaleMachine.row_complete_execution (s:=entry) rows i (co i) entryArgs layout
   entrySources h.table (labels i) h.constants h.pool h.radix (bounds i).1 (bounds i).2
   (different i) low fresh rowBound poolBound (by omega) inactive x rfl eh
 have keep:∀q,q∉UniformGlobalMatchingScaleMachine.natScratch → u.natReg q=s.natReg q:=by
  intro q hq;exact UniformGlobalMatchingScaleMachine.execution_nat (s:=entry) run hq
 have args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val u:=by
  constructor
  · exact (keep 2100 (by decide)).trans h.args.positive
  · exact (keep 2101 (by decide)).trans h.args.negative
  · exact (keep 2102 (by decide)).trans h.args.constants
  · exact (keep 2103 (by decide)).trans h.args.conjugates
  · exact (keep 2106 (by decide)).trans h.args.original
  · exact (keep 2107 (by decide)).trans h.args.conjugate
  · exact (keep 2140 (by decide)).trans h.args.rows
  · exact (keep 2141 (by decide)).trans h.args.index
 let v:State:={u with pc:=136}
 let out:=advanced u i.val
 have placedRun:BoundedRuns program n x B {s with pc:=16}
   (UniformMatchingConjugateLoadMachine.runtime (co i)+102) v:=by
  have rr:=UniformBoundedAssembly.boundedExecution_placed row_code
   (by rw [UniformGlobalMatchingScaleMachine.rowProgram_length];omega) (by omega) run
  exact rr
 have branch:step program n x s=.running {s with pc:=16}:=by
  simp [step,h.pc,branch_at,h.args.index,h.count,i.isLt]
 have one:u.natReg 4362=1:=(keep 4362 (by decide)).trans h.one
 have wb:WordBound B v:=placedRun.final_bound
 let tick:=writeNat v 2141 (i.val+1)
 have tb:WordBound B tick:=writeNat_bound B v 2141 _ wb (by change 136+1≤B;omega)
  (by have hi:=i.isLt;omega)
 have ob:WordBound B out:=changePC_bound B tick 15 tb (by omega)
 have advance:step program n x v=.running tick:=by
  simp [step,v,advance_at,evalNat,args.index,one,tick]
 have jump:step program n x tick=.running out:=by
  simp only [step,tick,writeNat,next,v];rfl
 have before:BoundedRuns program n x B s
   (UniformMatchingConjugateLoadMachine.runtime (co i)+103) v:=.next hs branch placedRun
 have tail:BoundedRuns program n x B v 2 out:=.next wb advance (.next tb jump (.refl ob))
 have nextArgs:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D (i.val+1) out:=by
  constructor <;> simp [out,advanced,writeNat,next,args.positive,args.negative,args.constants,
   args.conjugates,args.original,args.conjugate,args.rows]
 have next:Cursor (K:=K) C T P V a b D pool r rows bank (i.val+1) out:=by
  refine ⟨rfl,nextArgs,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [out,advanced,writeNat,next] using (keep 4330 (by decide)).trans h.pool
  · simpa [out,advanced,writeNat,next] using (keep 4331 (by decide)).trans h.radix
  · simpa [out,advanced,writeNat,next] using (keep 4360 (by decide)).trans h.count
  · simpa [out,advanced,writeNat,next] using one
  · exact coefficient_sources_retained layout fresh h.sources outside
  · exact constants_retained low layout.destinations fresh h.constants outside
  · intro j hj
    have eq:out.natHeap=s.natHeap:=nh
    change UniformCrossShearTableMachine.RowFields (D+3*j) (rows[j]'hj) out.natHeap
    rw [eq];exact h.table j hj
 have nextInvariant:PoolInvariant (K:=K) pool r rows bank co (i.val+1) out:=
  invariant_step a b pool r rows bank co bounds matching i s out fresh layout.destinations pre factors other
 refine ⟨out,?_,next,nextInvariant,nh,outs,roots,outside⟩
 convert before.trans tail using 1

lemma loop {R K C T P V a b B D pool r n : ℕ} {bank:Fin R→ℂ}
 (rows:List UniformInPlaceMachine.Row)
 (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (labels:∀j:Fin rows.length,(rows[j.val]'j.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P (co j))
 (bounds:Bounds r rows) (different:Different rows) (matching:Matching rows)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B) (poolBound:pool+9*r≤B)
 (code:139≤B) (fuel i : ℕ) (sum:i+fuel=rows.length) (x:Fin n→ℂ) (s : State)
 (h:Cursor (K:=K) C T P V a b D pool r rows bank i s)
 (pre:PoolInvariant (K:=K) pool r rows bank co i s) (hs:WordBound B s) : ∃out t,
 BoundedExecution program n x B s t out ∧ t≤117*fuel+2 ∧ out.pc=138 ∧
 PoolInvariant (K:=K) pool r rows bank co rows.length out ∧
 UniformMatchingConjugateLoadMachine.Sources K C T P V bank out ∧
 UniformHadamardPairMachine.Constants out ∧ UniformCrossShearTableMachine.Table D rows out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → out.scalarHeap q=s.scalarHeap q) := by
 induction fuel generalizing i s with
 | zero =>
  have eq:i=rows.length:=by omega
  let out:State:={s with pc:=138}
  have hb:WordBound B out:=changePC_bound B s 138 hs (by omega)
  have branch:step program n x s=.running out:=by
   simp [step,h.pc,branch_at,h.args.index,h.count,eq,out]
  have halt:step program n x out=.halted out:=by simp only [step,out,halt_at]
  have invariant:PoolInvariant (K:=K) pool r rows bank co rows.length out:=by
   constructor
   · intro j hj;exact pre.done j (by omega)
   · intro j hj;have hi:=j.isLt;omega
   · intro d hd hn lane;exact pre.untouched d hd hn lane
  have sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank out:=
   ⟨h.sources.positive,h.sources.negative,h.sources.conjugate,h.sources.constants⟩
  exact ⟨out,2,.next hs branch (.halt hb halt),by omega,rfl,invariant,
   sources,h.constants,h.table,rfl,rfl,rfl,fun _ _ _ _=>rfl⟩
 | succ fuel ih =>
  let j:Fin rows.length:=⟨i,by omega⟩
  obtain ⟨u,run,next,invariant,nh,outs,roots,outside⟩:=iteration rows co labels bounds different matching
   layout low fresh rowBound poolBound code j x s h pre hs
  obtain ⟨out,t,tail,bound,last,done,sources,constants,table,nh',outs',roots',outside'⟩:=
   ih (i+1) (by omega) u next invariant run.final_bound
  refine ⟨out,UniformMatchingConjugateLoadMachine.runtime (co j)+105+t,
   run.executes tail,?_,last,done,sources,constants,table,
   nh'.trans nh,outs'.trans outs,roots'.trans roots,?_⟩
  · have rt:UniformMatchingConjugateLoadMachine.runtime (co j)≤12:=by
     cases co j <;> simp [UniformMatchingConjugateLoadMachine.runtime]
    omega
  · intro q hq qa qb;exact (outside' q hq qa qb).trans (outside q hq qa qb)

lemma boot_nat (s : State) (q : ℕ) (h0:q≠4360) (h1:q≠4361) (h2:q≠4362) (h3:q≠2141) :
 (applyBlock boot s).natReg q=s.natReg q := by
 simp [boot,applyBlock,Op.apply,writeNat,next,h0,h1,h2,h3]

lemma initialization {R K C T P V a b B D pool r n : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row)
 (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D (s.natReg 2141) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (count:s.natReg 894=rows.length) (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (bounds:Bounds r rows) (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (low:6≤a) (fresh:b<pool) (bound:pool+9*r≤B) (code:139≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃out,
 BoundedRuns program n x B s (45*r+11) out ∧
 Cursor (K:=K) C T P V a b D pool r rows bank 0 out ∧
 PoolInvariant (K:=K) pool r rows bank co 0 out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q) → out.scalarHeap q=s.scalarHeap q) := by
 let h:=applyBlock boot s
 have reads:readable boot s:=by simp [boot,readable,Op.readable]
 have peaks:peak boot s≤B:=by
  simp [boot,peak,Op.peak,Op.apply,writeNat,next,count]
  have hb:rows.length≤B:=by simpa only [count] using hs.2.1 894
  omega
 have start:=block_runs boot program 0 n B x s boot_code pc hs
  (by change 0+4≤B;omega) reads peaks
 have hpc:h.pc=4:=by rw [applyBlock_pc,pc];rfl
 let entry:State:={h with pc:=0}
 have ep:entry.natReg 4330=pool:=(boot_nat s 4330 (by decide) (by decide) (by decide) (by decide)).trans hp
 have er:entry.natReg 4331=r:=(boot_nat s 4331 (by decide) (by decide) (by decide) (by decide)).trans hr
 obtain ⟨u,run,last,ones,outside,frame⟩:=UniformGlobalScalePoolMachine.execution pool r n B x entry ep er bound
  (by omega) rfl (changePC_bound B h 0 start.final_bound (by omega))
 let out:State:={u with pc:=15}
 have placedRun:BoundedRuns program n x B h (45*r+7) out:=by
  have rr:=UniformBoundedAssembly.boundedExecution_placed pool_code
   (by rw [UniformGlobalScalePoolMachine.program_length];omega) (by omega) run
  have eq:placed 4 entry=h:=by change {h with pc:=4}=h;rw [←hpc]
  simpa only [eq] using rr
 have stable:∀q,q≠4360 → q≠4361 → q≠4362 → q≠2141 →
  q≠4356 → q≠4357 → q≠4358 → q≠4359 → out.natReg q=s.natReg q:=by
  intro q h0 h1 h2 h3 h4 h5 h6 h7
  exact (frame.natReg q h4 h5 h6 h7).trans (boot_nat s q h0 h1 h2 h3)
 have nextArgs:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D 0 out:=by
  constructor
  · exact (stable 2100 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.positive
  · exact (stable 2101 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.negative
  · exact (stable 2102 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.constants
  · exact (stable 2103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.conjugates
  · exact (stable 2106 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.original
  · exact (stable 2107 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.conjugate
  · exact (stable 2140 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans args.rows
  · exact (frame.natReg 2141 (by decide) (by decide) (by decide) (by decide)).trans
     (by simp [entry,h,boot,applyBlock,Op.apply,writeNat,next])
 have outPool:out.natReg 4330=pool:=(stable 4330 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide)).trans hp
 have outRadix:out.natReg 4331=r:=(stable 4331 (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide)).trans hr
 have count':out.natReg 4360=rows.length:=
  (frame.natReg 4360 (by decide) (by decide) (by decide) (by decide)).trans
   (by simp [entry,h,boot,applyBlock,Op.apply,writeNat,next,count])
 have one:out.natReg 4362=1:=
  (frame.natReg 4362 (by decide) (by decide) (by decide) (by decide)).trans
   (by simp [entry,h,boot,applyBlock,Op.apply,writeNat,next])
 have limited:∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → out.scalarHeap q=s.scalarHeap q:=by
  intro q hq qa qb;exact outside q hq
 have nextSources:=coefficient_sources_retained layout fresh sources limited
 have nextConstants:=constants_retained low layout.destinations fresh constants limited
 have nextTable:UniformCrossShearTableMachine.Table D rows out:=by
  intro j hj
  have eq:out.natHeap=s.natHeap:=frame.natHeap
  change UniformCrossShearTableMachine.RowFields (D+3*j) (rows[j]'hj) out.natHeap
  rw [eq];exact table j hj
 refine ⟨out,?_,⟨rfl,nextArgs,outPool,outRadix,count',one,nextSources,nextConstants,nextTable⟩,
  invariant_initial pool r rows bank co out bounds ones,frame.natHeap,frame.outputs,frame.roots,outside⟩
 convert start.trans placedRun using 1
 change 45*r+11=4+(45*r+7);omega

/-- One fixed139-instruction program prepares every native diagonal lane from
actual count894 and physical generated rows. Its entry has no factor table. -/
theorem execution {R K C T P V a b B D pool r n : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row)
 (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (labels:∀j:Fin rows.length,(rows[j.val]'j.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P (co j))
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D (s.natReg 2141) s)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (count:s.natReg 894=rows.length) (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (bounds:Bounds r rows) (different:Different rows) (matching:Matching rows)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B) (bound:pool+9*r≤B) (code:139≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃out t,
 BoundedExecution program n x B s t out ∧ t≤45*r+117*rows.length+13 ∧ out.pc=138 ∧
 PoolInvariant (K:=K) pool r rows bank co rows.length out ∧
 UniformMatchingConjugateLoadMachine.Sources K C T P V bank out ∧
 UniformHadamardPairMachine.Constants out ∧ UniformCrossShearTableMachine.Table D rows out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q) → q≠a → q≠b → out.scalarHeap q=s.scalarHeap q) := by
 obtain ⟨u,run,cursor,pre,nh,outs,roots,outside⟩:=initialization rows co args sources constants table
  count hp hr bounds layout low fresh bound code x pc hs
 obtain ⟨out,t,tail,cost,last,done,sources',constants',table',nh',outs',roots',outside'⟩:=
  loop rows co labels bounds different matching layout low fresh rowBound bound code
   rows.length 0 (by omega) x u cursor pre run.final_bound
 refine ⟨out,45*r+11+t,run.executes tail,by omega,last,done,sources',constants',table',
  nh'.trans nh,outs'.trans outs,roots'.trans roots,?_⟩
 intro q hq qa qb;exact (outside' q hq qa qb).trans (outside q hq)


def natScratch:List ℕ:=UniformGlobalMatchingScaleMachine.natScratch++
 [4356,4357,4358,4359,4360,4361,4362,2141]
lemma keeps_nat (q:ℕ) (hq:q∉natScratch):
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 have rowNo:q∉UniformGlobalMatchingScaleMachine.natScratch:=by
  intro h;exact hq (List.mem_append_left _ h)
 have tinyNo:q∉[4356,4357,4358,4359,4360,4361,4362,2141]:=by
  intro h;exact hq (List.mem_append_right _ h)
 simp only[List.mem_cons,List.not_mem_nil,or_false,not_or] at tinyNo
 have head:∀ins∈boot.map Op.code,UniformNewtonTableMachine.KeepsNat q ins:=by
  simp [boot,Op.code,UniformNewtonTableMachine.KeepsNat,ne_comm,tinyNo]
 have pool:∀ins∈UniformGlobalScalePoolMachine.program,UniformNewtonTableMachine.KeepsNat q ins:=by
  simp [UniformGlobalScalePoolMachine.program,UniformGlobalScalePoolMachine.boot,
   UniformGlobalScalePoolMachine.body,Op.code,UniformNewtonTableMachine.KeepsNat,ne_comm,tinyNo]
 have before:=UniformReciprocalMachine.keeps_append q head
  (UniformReciprocalMachine.keeps_relocate q 4 15 pool)
 have branch:∀ins∈[Instruction.branchLT 2141 4360 16 138],
  UniformNewtonTableMachine.KeepsNat q ins:=by simp[UniformNewtonTableMachine.KeepsNat]
 have row:=UniformReciprocalMachine.keeps_relocate q 16 136
  (UniformGlobalMatchingScaleMachine.row_keeps_nat q rowNo)
 have finish:∀ins∈[Instruction.natBinary .add 2141 2141 4362,.jump 15,.halt],
  UniformNewtonTableMachine.KeepsNat q ins:=by
  simp [UniformNewtonTableMachine.KeepsNat,ne_comm,tinyNo]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q (UniformReciprocalMachine.keeps_append q before branch) row) finish
lemma execution_nat {n B t q:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u) (hq:q∉natScratch):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_nat q hq)
lemma execution_saved {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u):
 ∀q,100≤q→q≤106→u.natReg q=s.natReg q:=by
 intro q lo hi
 exact execution_nat run (by
  simp only[natScratch,UniformGlobalMatchingScaleMachine.natScratch,List.mem_append,List.mem_cons,
   List.not_mem_nil,or_false];omega)

end
end ExactFourierCircuits.UniformGlobalMatchingPoolPreparation
