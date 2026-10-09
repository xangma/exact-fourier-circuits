import UniformRecursiveSavingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSmallPrologue
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
noncomputable section

def setupOps (count:ℕ):List Op := [.binary .mul 4900 4120 4153,.literal 4901 count,
 .binary .mul 4902 4121 4153,.binary .mul 4903 4122 4153]
lemma setup_length (count:ℕ):(setupOps count).length=4:=rfl

def Changed (j:ℕ):Prop := j=4177∨j=4900∨j=4901∨j=4902∨j=4903
structure Frame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j

/-- The actual small-branch test and four charged header writes. No batch
headers or branch outcome are supplied by the caller. -/
theorem execution (main:Program)(ready setup base large threshold count n B k A V:ℕ)
 (x:Fin n→ℂ)(s:State)
 (literalCode:main[ready]?=some (.natLiteral 4177 threshold))
 (branchCode:main[ready+1]?=some (.branchLT 4120 4177 setup large))
 (setupCode:BlockAt (setupOps count) main setup)(follow:setup+4=base)
 (pc:s.pc=ready)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(dataBase:s.natReg 4121=A)
 (volume:s.natReg 4122=V)(small:k<threshold)(bound:WordBound B s)
 (readyEnd:ready+2≤B)(setupEnd:setup+4≤B)(thresholdBound:threshold≤B)(countBound:count≤B):∃u,
 BoundedRuns main n x B s 6 u ∧u.pc=base ∧u.natReg 4900=k ∧u.natReg 4901=count ∧
 u.natReg 4902=A ∧u.natReg 4903=V ∧Frame s u:=by
 let tagged:=writeNat s 4177 threshold
 have tb:=writeNat_bound B s 4177 threshold bound (by omega) thresholdBound
 have tag:BoundedRuns main n x B s 1 tagged:=.next bound
  (by simp [step,pc,literalCode,tagged]) (.refl tb)
 let entered:=setPC tagged setup
 have eb:=changePC_bound B tagged setup tb (by omega)
 have branch:BoundedRuns main n x B tagged 1 entered:=.next tb
  (by simp [step,tagged,writeNat,next,pc,branchCode,bits,small,entered,setPC]) (.refl eb)
 have ek:entered.natReg 4120=k:=by simp [entered,tagged,setPC,writeNat,next,bits]
 have ea:entered.natReg 4121=A:=by simp [entered,tagged,setPC,writeNat,next,dataBase]
 have ev:entered.natReg 4122=V:=by simp [entered,tagged,setPC,writeNat,next,volume]
 have eo:entered.natReg 4153=1:=by simp [entered,tagged,setPC,writeNat,next,one]
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have ab:A≤B:=by have h:=bound.2.1 4121;rwa [dataBase] at h
 have vb:V≤B:=by have h:=bound.2.1 4122;rwa [volume] at h
 have safe:readable (setupOps count) entered∧peak (setupOps count) entered≤B:=by
  simp [setupOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,ek,ea,ev,eo,
   countBound,kb,ab,vb]
 have run:=block_runs (setupOps count) main setup n B x entered setupCode rfl eb
  (by rw [setup_length];exact setupEnd) safe.1 safe.2
 let u:=applyBlock (setupOps count) entered
 refine ⟨u,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only [setup_length] using tag.trans (branch.trans run)
 · simpa only [follow] using (show u.pc=setup+4 by simp [u,setupOps,applyBlock,Op.apply,writeNat,next,entered,setPC])
 · simp [u,setupOps,applyBlock,Op.apply,evalNat,writeNat,next,ek,eo]
 · simp [u,setupOps,applyBlock,Op.apply,evalNat,writeNat,next]
 · simp [u,setupOps,applyBlock,Op.apply,evalNat,writeNat,next,ea,eo]
 · simp [u,setupOps,applyBlock,Op.apply,evalNat,writeNat,next,ev,eo]
 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j hj
   unfold Changed at hj
   simp (disch:=omega) [u,setupOps,applyBlock,Op.apply,evalNat,entered,tagged,setPC,writeNat,next]

end
end ExactFourierCircuits.UniformRecursiveSmallPrologue
