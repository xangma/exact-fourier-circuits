import UniformAxisCacheInputs
import UniformAxisCacheAllocationExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheClockLookup
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformTensorMonomialMachine (setPC)

/-- The first clock axis physically resets both frontiers; later axes use the
preceding lookup's measured end addresses. -/
def boot:List Op:=[.literal 7098 0,.literal 7099 1]
def reset:List Op:=[.binary .add 6801 6909 7098,.binary .add 6802 6910 7098]
def select:List Op:=[.literal 7097 2,.binary .mul 7000 5922 7097,
 .binary .add 7000 6904 7000,.binary .add 7096 7000 7099,.load 6800 7096]
def program:Program:=boot.map Op.code++[.branchLT 5922 7099 3 5]++reset.map Op.code++
 select.map Op.code++UniformAxisCacheAllocationMachine.program.map (relocate 10 68)++[.halt]
lemma boot_length:boot.length=2:=rfl
lemma reset_length:reset.length=2:=rfl
lemma select_length:select.length=5:=rfl
lemma program_length:program.length=69:=rfl
lemma boot_code:BlockAt boot program 0:=by intro i hi;change i<2 at hi;interval_cases i<;>rfl
lemma branch_at:program[2]?=some (.branchLT 5922 7099 3 5):=rfl
lemma reset_code:BlockAt reset program 3:=by intro i hi;change i<2 at hi;interval_cases i<;>rfl
lemma select_code:BlockAt select program 5:=by intro i hi;change i<5 at hi;interval_cases i<;>rfl
lemma allocator_code:CodeAt UniformAxisCacheAllocationMachine.program program 10 68:=by
 change CodeAt UniformAxisCacheAllocationMachine.program
  ((boot.map Op.code++[.branchLT 5922 7099 3 5]++reset.map Op.code++select.map Op.code)++
    UniformAxisCacheAllocationMachine.program.map (relocate 10 68)++[.halt]) 10 68
 exact UniformRankCrossPreparationMachine.segment_code _ _ _ 10 68 rfl
lemma halt_at:program[68]?=some .halt:=rfl

noncomputable section
structure Header (c:A.Constants) (n j:ℕ) (s:State):Prop where
 axis:s.natReg 5922=j
 directory:s.natReg 6904=Seed.directoryBase n
 initialNat:s.natReg 6909=natAt c n 0
 initialScalar:s.natReg 6910=scalarAt c n 0

structure HeadFrame (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,q≠6800→q≠6801→q≠6802→q≠7000→q≠7096→q≠7097→q≠7098→q≠7099→u.natReg q=s.natReg q
lemma HeadFrame.refl (s:State):HeadFrame s s:=⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _ _ _ _ _ _ _=>rfl⟩
lemma HeadFrame.pc {s u:State} (h:HeadFrame s u) (pc:ℕ):HeadFrame s (setPC u pc):=
 ⟨h.natHeap,h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩
lemma HeadFrame.trans{s a u:State}(h:HeadFrame s a) (g:HeadFrame a u):HeadFrame s u:=
 ⟨g.natHeap.trans h.natHeap,g.scalarHeap.trans h.scalarHeap,g.scalarReg.trans h.scalarReg,
 g.outputs.trans h.outputs,g.roots.trans h.roots,fun q a b c d e f i j=>(g.natReg q a b c d e f i j).trans (h.natReg q a b c d e f i j)⟩
lemma boot_frame (s:State):HeadFrame s (applyBlock boot s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩;intro q a b c d e f g h
 simp[boot,applyBlock,Op.apply,writeNat,next,g,h]
lemma reset_frame (s:State):HeadFrame s (applyBlock reset s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩;intro q a b c d e f g h
 simp[reset,applyBlock,Op.apply,writeNat,next,b,c]
lemma select_frame (s:State):HeadFrame s (applyBlock select s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩;intro q a b c d e f g h
 simp[select,applyBlock,Op.apply,writeNat,next,a,d,e,f]
lemma head_safe (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (s:State)
 (head:Header c n j.val s) (one:s.natReg 7099=1)
 (width:s.natHeap (Seed.directoryBase n+2*j.val+1)=some (Seed.radix n j)):
 readable select s∧peak select s≤A.envelope c n:=by
 have width' : s.natHeap (Seed.directoryBase n+j.val*2+1)=some (Seed.radix n j):=by simpa only [Nat.mul_comm] using width
 have bounds:=arithmetic c n hn
 have dir:=bounds.2.2.2.1
 have rad:Seed.radix n j≤A.envelope c n:=
  (UniformGlobalLocalPreparation.radix_le_length n j).trans
   ((UniformWorkingLength.workingLength_upper hn).le.trans bounds.2.2.2.2)
 constructor
 · simp[select,readable,Op.readable,Op.apply,evalNat,writeNat,next,head.axis,head.directory,one,width']
 · simp[select,peak,Op.peak,Op.apply,evalNat,writeNat,next,head.axis,head.directory,one,width']
   omega

/-- The ten-cell prefix executes either eight or ten instructions. No ready
radix or current first-axis frontier is an input. -/
theorem head_execution (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (x:Fin n→ℂ) (s:State)
 (head:Header c n j.val s) (later:0<j.val→Frontiers c n j.val s)
 (input:Inputs n x s) (pc:s.pc=0) (wb:WordBound (A.envelope c n) s):
 ∃u,BoundedRuns program n x (A.envelope c n) s (if j.val=0 then 10 else 8) u∧u.pc=10∧
 UniformAxisCacheAllocationMachine.Arguments (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u∧
 u.natReg 7000=Seed.directoryBase n+2*j.val∧HeadFrame s u:=by
 have bounds:=arithmetic c n hn
 have bootSafe:readable boot s∧peak boot s≤A.envelope c n:=by
  constructor
  · simp[boot,readable,Op.readable]
  · simp[boot,peak,Op.peak];omega
 have first:=block_runs boot program 0 n (A.envelope c n) x s boot_code pc wb (by rw[boot_length];omega) bootSafe.1 bootSafe.2
 let a:=applyBlock boot s
 have ap:a.pc=2:=by simp[a,boot,applyBlock,Op.apply,writeNat,next,pc]
 have ax:a.natReg 5922=j.val:=by simp[a,boot,applyBlock,Op.apply,writeNat,next,head.axis]
 have one:a.natReg 7099=1:=by simp[a,boot,applyBlock,Op.apply,writeNat,next]
 have zero:a.natReg 7098=0:=by simp[a,boot,applyBlock,Op.apply,writeNat,next]
 let target:=if j.val=0 then 3 else 5
 let b:=setPC a target
 have bw:WordBound (A.envelope c n) b:=⟨by change target≤A.envelope c n;dsimp[target];split_ifs<;>omega,first.final_bound.2⟩
 have stepBranch:step program n x a=.running b:=by
  simp only [UniformMachine.step,ap,branch_at]
  rw [ax,one]
  simp only [Nat.lt_one_iff]
  rfl
 have branch:BoundedRuns program n x (A.envelope c n) a 1 b:=.next first.final_bound stepBranch (.refl bw)
 have bz:b.natReg 7098=0:=zero
 have bo:b.natReg 7099=1:=one
 have af:HeadFrame s b:=(boot_frame s).pc target
 have bh:Header c n j.val b:=⟨ax,(af.natReg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans head.directory,
  (af.natReg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans head.initialNat,
  (af.natReg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans head.initialScalar⟩
 have pre:∃d,BoundedRuns program n x (A.envelope c n) b (if j.val=0 then 2 else 0) d∧d.pc=5∧
   Frontiers c n j.val d∧Header c n j.val d∧d.natReg 7098=0∧d.natReg 7099=1∧HeadFrame b d:=by
  by_cases hj:j.val=0
  · have safe:readable reset b∧peak reset b≤A.envelope c n:=by
     have nfit:=bw.2.1 6909
     have sfit:=bw.2.1 6910
     constructor
     · simp[reset,readable,Op.readable,evalNat]
     · simp[reset,peak,Op.peak,Op.apply,evalNat,writeNat,next,bz];omega
    have run:=block_runs reset program 3 n (A.envelope c n) x b reset_code (by simp[b,target,hj,setPC]) bw
     (by rw[reset_length];omega) safe.1 safe.2
    let d:=applyBlock reset b
    have df:=reset_frame b
    refine⟨d,?_,?_,?_,?_,?_,?_,df⟩
    · simpa [hj,reset_length] using run
    · simp[d,reset,applyBlock,Op.apply,next,writeNat,b,target,hj,setPC]
    · constructor
      · simp[d,reset,applyBlock,Op.apply,evalNat,writeNat,next,bz,bh.initialNat,hj,natAt]
      · simp[d,reset,applyBlock,Op.apply,evalNat,writeNat,next,bz,bh.initialScalar,hj,scalarAt]
    · constructor<;>simp[d,reset,applyBlock,Op.apply,writeNat,next,bh.axis,bh.directory,bh.initialNat,bh.initialScalar]
    · exact bz
    · exact bo
  · have front:=later (by omega)
    refine⟨b,?_,?_,?_,bh,bz,bo,HeadFrame.refl b⟩
    · simpa [hj] using (BoundedRuns.refl bw : BoundedRuns program n x (A.envelope c n) b 0 b)
    · simp[b,target,hj,setPC]
    · constructor
      · simpa [b,setPC,a,boot,applyBlock,Op.apply,writeNat,next] using front.natFrontier
      · simpa [b,setPC,a,boot,applyBlock,Op.apply,writeNat,next] using front.scalarFrontier
 obtain⟨d,preRun,dp,front,dh,dz,do_,df⟩:=pre
 have totalFrame:=af.trans df
 have width:d.natHeap (Seed.directoryBase n+2*j.val+1)=some (Seed.radix n j):=by
  rw[totalFrame.natHeap]
  simpa only[Nat.mul_comm]using input.original.width j j.isLt
 have width' :d.natHeap (Seed.directoryBase n+j.val*2+1)=some (Seed.radix n j):=by simpa only [Nat.mul_comm] using width
 have safe:=head_safe c n hn j d dh do_ width
 have last:=block_runs select program 5 n (A.envelope c n) x d select_code dp preRun.final_bound
  (by rw[select_length];omega) safe.1 safe.2
 let u:=applyBlock select d
 refine⟨u,?_,?_,?_,?_,totalFrame.trans (select_frame d)⟩
 · have whole:=(first.trans branch).trans (preRun.trans last)
   convert whole using 1
   split_ifs <;> simp [boot_length,select_length]
 · rw[UniformAxisCacheAllocationMachine.block_pc,dp,select_length]
 · refine⟨?_,front.natFrontier,front.scalarFrontier⟩
   simp[u,select,applyBlock,Op.apply,evalNat,writeNat,next,dh.axis,dh.directory,do_,width']
 · simp[u,select,applyBlock,Op.apply,evalNat,writeNat,next,dh.axis,dh.directory,Nat.mul_comm]

end
end ExactFourierCircuits.UniformAxisCacheClockLookup
