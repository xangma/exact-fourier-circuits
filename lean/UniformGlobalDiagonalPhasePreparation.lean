import UniformGlobalMatchingScaleBankBridge
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalDiagonalPhasePreparation
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section
/-- Physical pool lane selection, header installation, then the actual20-op
identity-permutation/coefficient-row producer. Every move is charged. -/
def setup:List Op:=[.literal 4387 0,.mul 171 4382 4380,.add 171 4381 171,
 .add 170 4380 4387,.add 172 4383 4387,.add 173 4384 4387,
 .add 174 4385 4387,.add 175 4386 4387]
def program:Program:=setup.map Op.code++
 UniformTensorDiagonalBankMachine.program.map (relocate 8 28)++[.halt]
lemma setup_length:setup.length=8:=rfl
lemma program_length:program.length=29:=rfl
lemma setup_code:BlockAt setup program 0:=by
 intro i hi;change i<8 at hi;interval_cases i <;>rfl
lemma copy_code:CodeAt UniformTensorDiagonalBankMachine.program program 8 28:=by
 exact UniformAssembly.embed_code (setup.map Op.code) UniformTensorDiagonalBankMachine.program [.halt] 28
lemma halt_at:program[28]?=some .halt:=rfl
structure Args (r pool p c b d:ℕ) (lane:Fin 9) (s:State):Prop where
 radix:s.natReg 4380=r
 pool:s.natReg 4381=pool
 lane:s.natReg 4382=lane.val
 permutation:s.natReg 4383=p
 coefficient:s.natReg 4384=c
 row:s.natReg 4385=b
 depth:s.natReg 4386=d
lemma setup_header {r pool p c b d:ℕ} {lane:Fin 9} {s:State}
 (h:Args r pool p c b d lane s):
 UniformTensorDiagonalBankMachine.Header r (pool+lane.val*r) p c b d (applyBlock setup s):=by
 constructor <;> simp [setup,applyBlock,Op.apply,writeNat,next,h.radix,h.pool,h.lane,
  h.permutation,h.coefficient,h.row,h.depth]
lemma setup_bound {r pool p c b d B n:ℕ} {lane:Fin 9} {s:State}
 (h:Args r pool p c b d lane s) (bound:pool+9*r≤B) (code:29≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s):
 BoundedRuns program n x B s 8 (applyBlock setup s):=by
 have lm:lane.val*r≤8*r:=Nat.mul_le_mul_right r (by have:=lane.isLt;omega)
 have pp:p≤B:=by simpa only[h.permutation] using hs.2.1 4383
 have cc:c≤B:=by simpa only[h.coefficient] using hs.2.1 4384
 have bb:b≤B:=by simpa only[h.row] using hs.2.1 4385
 have dd:d≤B:=by simpa only[h.depth] using hs.2.1 4386
 apply block_runs setup program 0 n B x s setup_code pc hs (by rw[setup_length];omega)
 · simp [readable,setup,Op.readable]
 · simp [peak,setup,Op.peak,Op.apply,writeNat,next,h.radix,h.pool,h.lane,
    h.permutation,h.coefficient,h.row,h.depth]
   omega
structure Result (r pool p c b d:ℕ) (lane:Fin 9) (f:Fin r→ℂ) (s out:State):Prop where
 pc:out.pc=28
 permutation:∀j:Fin r,out.natHeap (p+j.val)=some j.val
 coefficient:∀j:Fin r,out.scalarHeap (c+j.val)=some (prepared (f j))
 rowWidth:out.natHeap (b+d*3)=some r
 rowPermutation:out.natHeap (b+d*3+1)=some p
 rowCoefficient:out.natHeap (b+d*3+2)=some c
 natFrame:∀a,(a<b+d*3 ∨ b+d*3+3≤a)→(a<p ∨ p+r≤a)→ out.natHeap a=s.natHeap a
 scalarFrame:∀a,a<c ∨ c+r≤a→ out.scalarHeap a=s.scalarHeap a
 outputs:out.outputs=s.outputs
 roots:out.rootOrders=s.rootOrders
lemma execution {r pool p c b d B n:ℕ} {lane:Fin 9} {s:State}
 (f:Fin r→ℂ) (h:Args r pool p c b d lane s)
 (coefficients:UniformTensorDiagonalBankMachine.Coefficients r (pool+lane.val*r) f s)
 (separate:pool+lane.val*r+r≤c ∨ c+r≤pool+lane.val*r)
 (rowSeparate:b+d*3+3≤p ∨ p+r≤b+d*3)
 (poolBound:pool+9*r≤B) (rowBound:b+d*3+2≤B) (permutationBound:p+r≤B)
 (coefficientBound:c+r≤B) (code:29≤B) (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s):
 ∃out,BoundedExecution program n x B s (9*r+21) out ∧
 Result r pool p c b d lane f s out:=by
 have start:=setup_bound h poolBound code x pc hs
 let e:State:=setPC (applyBlock setup s) 0
 have eb:WordBound B e:=changePC_bound B _ 0 start.final_bound (by omega)
 have head:=setup_header h
 have header:UniformTensorDiagonalBankMachine.Header r (pool+lane.val*r) p c b d e:=
  ⟨head.width,head.source,head.permutation,head.coefficient,head.row,head.depth⟩
 have source:UniformTensorDiagonalBankMachine.Coefficients r (pool+lane.val*r) f e:=coefficients
 obtain ⟨run,result⟩:=UniformTensorDiagonalBankMachine.complete_execution B n r
  (pool+lane.val*r) p c b d x f e header rfl source separate rowSeparate (by omega)
   rowBound permutationBound coefficientBound eb
 have tail:=UniformBoundedAssembly.boundedExecution_placed copy_code (by
   rw[UniformTensorDiagonalBankMachine.program_length];omega) (by omega) run
 have ep:(applyBlock setup s).pc=8:=by rw[applyBlock_pc,setup_length,pc]
 have input:placed 8 e=applyBlock setup s:=by
  change {applyBlock setup s with pc:=8+0}=applyBlock setup s
  simp only[Nat.add_zero]
  rw[←ep]
 rw[input] at tail
 let out:State:={UniformTensorDiagonalBankMachine.finalState r e with pc:=28}
 have finish:BoundedExecution program n x B out 1 out:=
  .halt tail.final_bound (by simp [UniformMachine.step,out,halt_at])
 refine ⟨out,?_,⟨rfl,result.permutation,result.coefficient,result.rowWidth,
  result.rowPermutation,result.rowCoefficient,result.natFrame,result.scalarFrame,
  result.frame.2.1,result.frame.1⟩⟩
 convert start.executes (tail.executes finish) using 1
 omega
end
end ExactFourierCircuits.UniformGlobalDiagonalPhasePreparation
