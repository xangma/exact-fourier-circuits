import UniformGlobalDiagonalPhasePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalMatchingDiagonalPreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalMatchingScaleBankBridge
noncomputable section
/-- One continuous172-op program: physical rows/coefficient banks→all9r
scale cells→one actual identity diagonal table. No prepared-factor input. -/
def setup:List Op:=[.literal 4387 0,.add 4330 4381 4387,.add 4331 4380 4387]
def beforePhase:Program:=setup.map Op.code++
 UniformGlobalMatchingPoolPreparation.program.map (relocate 3 142)
def program:Program:=beforePhase++UniformGlobalDiagonalPhasePreparation.program.map
 (relocate 142 171)++[.halt]
lemma setup_length:setup.length=3:=rfl
lemma beforePhase_length:beforePhase.length=142:=by
 simp[beforePhase,setup_length,UniformGlobalMatchingPoolPreparation.program_length]
lemma program_length:program.length=172:=by
 simp[program,beforePhase_length,UniformGlobalDiagonalPhasePreparation.program_length]
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma pool_code:CodeAt UniformGlobalMatchingPoolPreparation.program program 3 142:=by
 let tail:Program:=UniformGlobalDiagonalPhasePreparation.program.map (relocate 142 171)++[.halt]
 have h:=UniformAssembly.embed_code (setup.map Op.code) UniformGlobalMatchingPoolPreparation.program tail 142
 simpa only[UniformAssembly.embed,setup_length,List.length_map,program,beforePhase,tail,List.append_assoc] using h
lemma phase_code:CodeAt UniformGlobalDiagonalPhasePreparation.program program 142 171:=by
 have h:=UniformAssembly.embed_code beforePhase UniformGlobalDiagonalPhasePreparation.program [.halt] 171
 simpa only[UniformAssembly.embed,beforePhase_length,program] using h
lemma halt_at:program[171]?=some .halt:=by
 unfold program
 rw[List.getElem?_append_right (by simp[beforePhase_length,UniformGlobalDiagonalPhasePreparation.program_length])]
 simp only[List.length_append,List.length_map,beforePhase_length,UniformGlobalDiagonalPhasePreparation.program_length]
 rfl
lemma setup_nat (s:State) (q:ℕ) (n0:q≠4387) (n1:q≠4330) (n2:q≠4331):
 (applyBlock setup s).natReg q=s.natReg q:=by
 simp[setup,applyBlock,Op.apply,writeNat,next,n0,n1,n2]
lemma setup_bound {r pool p c b d B n:ℕ} {lane:Fin 9} {s:State}
 (h:UniformGlobalDiagonalPhasePreparation.Args r pool p c b d lane s)
 (bound:pool+9*r≤B) (code:172≤B) (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s):
 BoundedRuns program n x B s 3 (applyBlock setup s):=by
 apply block_runs setup program 0 n B x s setup_code pc hs (by rw[setup_length];omega)
 · simp[readable,setup,Op.readable]
 · simp[peak,setup,Op.peak,Op.apply,writeNat,next,h.radix,h.pool]
   omega
lemma execution {R K C T P V a b B D pool r p c row depth n:ℕ} {lane:Fin 9}
 {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row)
 (co:Fin rows.length→UniformMatchingConjugateLoadMachine.Coefficient R)
 (E:Fin rows.length→UniformColoring.Edge)
 (edgeRows:UniformMatchingAxisTableMachine.Edges E D s)
 (hm:UniformMatchingAxisTableMachine.Matching E) (hr:UniformMatchingAxisTableMachine.InRange r E)
 (labels:∀i:Fin rows.length,(rows[i.val]'i.isLt).coefficient=
   UniformMatchingConjugateLoadMachine.address C T P (co i))
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D (s.natReg 2141) s)
 (phaseArgs:UniformGlobalDiagonalPhasePreparation.Args r pool p c row depth lane s)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (constants:UniformHadamardPairMachine.Constants s)
 (table:UniformCrossShearTableMachine.Table D rows s) (count:s.natReg 894=rows.length)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B) (poolBound:pool+9*r≤B)
 (copySeparate:pool+9*r≤c) (rowSeparate:row+depth*3+3≤p ∨ p+r≤row+depth*3)
 (tableBound:row+depth*3+2≤B) (permutationBound:p+r≤B) (coefficientBound:c+r≤B)
 (code:172≤B) (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s):∃out t,
 BoundedExecution program n x B s t out ∧ t≤54*r+117*rows.length+38 ∧ out.pc=171 ∧
 (∀j:Fin r,out.natHeap (p+j.val)=some j.val) ∧
 (∃different:UniformGlobalMatchingPoolPreparation.Different rows,
  ∀j:Fin r,out.scalarHeap (c+j.val)=some (UniformPairMachine.prepared
   (nativeFactor (rowEdges rows different)
    (fun i=>UniformMatchingConjugateLoadMachine.value K bank (co i)) lane j.val))) ∧
 out.natHeap (row+depth*3)=some r ∧out.natHeap (row+depth*3+1)=some p ∧
 out.natHeap (row+depth*3+2)=some c ∧out.outputs=s.outputs ∧out.rootOrders=s.rootOrders ∧
 (∀q,(q<row+depth*3 ∨ row+depth*3+3≤q)→(q<p ∨ p+r≤q)→ out.natHeap q=s.natHeap q) ∧
 (∀q,(q<pool ∨ pool+9*r≤q)→q≠a→q≠b→(q<c ∨ c+r≤q)→ out.scalarHeap q=s.scalarHeap q):=by
 obtain ⟨bounds,different,matching⟩:=rows_geometry edgeRows table hm hr
 have start:=setup_bound phaseArgs poolBound code x pc hs
 let e:State:=setPC (applyBlock setup s) 0
 have eb:=changePC_bound B (applyBlock setup s) 0 start.final_bound (show 0≤B by omega)
 have ea:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D (e.natReg 2141) e:=by
  constructor
  · exact (setup_nat s 2100 (by decide) (by decide) (by decide)).trans args.positive
  · exact (setup_nat s 2101 (by decide) (by decide) (by decide)).trans args.negative
  · exact (setup_nat s 2102 (by decide) (by decide) (by decide)).trans args.constants
  · exact (setup_nat s 2103 (by decide) (by decide) (by decide)).trans args.conjugates
  · exact (setup_nat s 2106 (by decide) (by decide) (by decide)).trans args.original
  · exact (setup_nat s 2107 (by decide) (by decide) (by decide)).trans args.conjugate
  · exact (setup_nat s 2140 (by decide) (by decide) (by decide)).trans args.rows
  · rfl
 have epool:e.natReg 4330=pool:=by simp[e,setPC,setup,applyBlock,Op.apply,writeNat,next,phaseArgs.pool]
 have eradix:e.natReg 4331=r:=by simp[e,setPC,setup,applyBlock,Op.apply,writeNat,next,phaseArgs.radix]
 have ec:e.natReg 894=rows.length:=(setup_nat s 894 (by decide) (by decide) (by decide)).trans count
 have esources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank e:=
  ⟨sources.positive,sources.negative,sources.conjugate,sources.constants⟩
 obtain ⟨u,t,run,cost,_,done,_,_,_,nh,outs,roots,outside⟩:=
  UniformGlobalMatchingPoolPreparation.execution rows co labels ea esources constants table ec epool eradix
   bounds different matching layout low fresh rowBound poolBound (by omega) x rfl eb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed pool_code
  (by rw[UniformGlobalMatchingPoolPreparation.program_length];omega) (by omega) run
 have eplaced:placed 3 e=applyBlock setup s:=by
  have ep:(applyBlock setup s).pc=3:=by rw[applyBlock_pc,setup_length,pc]
  change {applyBlock setup s with pc:=3+0}=applyBlock setup s
  simp only[Nat.add_zero];rw[←ep]
 rw[eplaced] at placedRun
 let entry:State:=setPC u 0
 have entryBound:=changePC_bound B u 0 run.final_bound (show 0≤B by omega)
 have keep (q:ℕ) (hq:4380≤q) (hqq:q≤4386):u.natReg q=s.natReg q:=by
  have no:q∉UniformGlobalMatchingPoolPreparation.natScratch:=by
   simp only[UniformGlobalMatchingPoolPreparation.natScratch,UniformGlobalMatchingScaleMachine.natScratch,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false];omega
  exact (UniformGlobalMatchingPoolPreparation.execution_nat run no).trans
   (setup_nat s q (by omega) (by omega) (by omega))
 have newArgs:UniformGlobalDiagonalPhasePreparation.Args r pool p c row depth lane entry:=
  ⟨(keep 4380 (by omega) (by omega)).trans phaseArgs.radix,
   (keep 4381 (by omega) (by omega)).trans phaseArgs.pool,
   (keep 4382 (by omega) (by omega)).trans phaseArgs.lane,
   (keep 4383 (by omega) (by omega)).trans phaseArgs.permutation,
   (keep 4384 (by omega) (by omega)).trans phaseArgs.coefficient,
   (keep 4385 (by omega) (by omega)).trans phaseArgs.row,
   (keep 4386 (by omega) (by omega)).trans phaseArgs.depth⟩
 let f:=fun j:Fin r=>nativeFactor (rowEdges rows different)
  (fun i=>UniformMatchingConjugateLoadMachine.value K bank (co i)) lane j.val
 have coefficients:UniformTensorDiagonalBankMachine.Coefficients r (pool+lane.val*r) f entry:=
  pool_coefficients different matching done lane
 have lm:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
 obtain ⟨out,phaseRun,result⟩:=UniformGlobalDiagonalPhasePreparation.execution f newArgs coefficients
  (Or.inl (by omega)) rowSeparate poolBound tableBound permutationBound coefficientBound (by omega)
  x rfl entryBound
 have phasePlaced:=UniformBoundedAssembly.boundedExecution_placed phase_code
  (by rw[UniformGlobalDiagonalPhasePreparation.program_length];omega) (by omega) phaseRun
 have same:placed 142 entry={u with pc:=142}:=rfl
 rw[same] at phasePlaced
 let final:State:={out with pc:=171}
 have finish:BoundedExecution program n x B final 1 final:=
  .halt phasePlaced.final_bound (by simp[UniformMachine.step,final,halt_at])
 refine ⟨final,3+t+(9*r+21)+1,?_,by omega,rfl,result.permutation,⟨different,result.coefficient⟩,
  result.rowWidth,result.rowPermutation,result.rowCoefficient,result.outputs.trans outs,
  result.roots.trans roots,?_,?_⟩
 · exact (start.trans placedRun).executes (phasePlaced.executes finish)
 · intro q hq hp;exact (result.natFrame q hq hp).trans (congrFun nh q)
 · intro q hq qa qb hc;exact (result.scalarFrame q hc).trans (outside q hq qa qb)
end
end ExactFourierCircuits.UniformGlobalMatchingDiagonalPreparation
