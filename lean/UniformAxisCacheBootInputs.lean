import UniformAxisCacheBoot
import UniformAxisCacheInputs
import UniformFourierClockBounds
import UniformLocalRectangleWorkspaceHeaders
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheBootInputs
open UniformMachine UniformAssembly UniformNatBlockMachine UniformAxisCacheStartupMachine
open UniformAxisCacheSelectedPreparation UniformAxisCachePreparationRetention UniformAxisCacheInputs

/-- Preserve the actual initial allocation frontiers for later calendar
passes;6908 remains available as the axis-loop tail's next-index scratch. -/
def save:List Op:=[.binary .add 6909 6801 6900,.binary .add 6910 6802 6900]
lemma save_length:save.length=2:=rfl

theorem execution (c:A.Constants)(n:ℕ)(hn:0<n)(p:Program)(base:ℕ)
 (initCode:BlockAt UniformAxisCacheBoot.resetOps p base)
 (startupCode:CodeAt UniformAxisCacheStartupMachine.program p (base+1) (base+18))
 (saveCode:BlockAt save p (base+18))(codeBound:base+20≤A.envelope c n)
 (x:Fin n→ℂ)(s:State)(core:Core n x s)(slab:s.natReg 6020=A.slab c n)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)(pc:s.pc=base)
 (wb:WordBound (A.envelope c n) s):
 ∃u,BoundedRuns p n x (A.envelope c n) s 20 u∧u.pc=base+20∧
 Selected c n 0 u∧Inputs n x u∧UniformLocalRectangleWorkspaceHeaders.Bank n u∧
 u.natReg 5921=UniformFourierClockBounds.clockPrefix n 0∧
 u.natReg 6909=natAt c n 0∧u.natReg 6910=scalarAt c n 0∧
 u.natHeap=s.natHeap∧u.scalarHeap=s.scalarHeap∧u.scalarReg=s.scalarReg∧
 u.outputs=s.outputs∧u.rootOrders=s.rootOrders:=by
 obtain ⟨a,boot,ap,out,retained,clock,nh,sh,sr,outputs,roots,regs⟩:=
  UniformAxisCacheBoot.execution c n hn p base (base+18) initCode startupCode
   (by omega) (by omega) x s core slab pc wb
 have safe:readable save a∧peak save a≤A.envelope c n:=by
  constructor
  · simp [save,readable,Op.readable,evalNat]
  · have natBound:=boot.final_bound.2.1 6801
    have scalarBound:=boot.final_bound.2.1 6802
    simp [save,peak,Op.peak,Op.apply,evalNat,writeNat,next,out.control.zero]
    omega
 have last:=block_runs save p (base+18) n (A.envelope c n) x a saveCode ap boot.final_bound
  (by rw [save_length];omega) safe.1 safe.2
 let u:=applyBlock save a
 have frame:∀q,q≠6909→q≠6910→u.natReg q=a.natReg q:=by
  intro q hn hs
  simp [u,save,applyBlock,Op.apply,writeNat,next,hn,hs]
 have selected:Selected c n 0 u:=by
  refine ⟨?_,?_,(frame _ (by omega) (by omega)).trans out.radix,
   (frame _ (by omega) (by omega)).trans out.source,(frame _ (by omega) (by omega)).trans out.axisIndex⟩
  · exact ⟨(frame _ (by omega) (by omega)).trans out.control.zero,
    (frame _ (by omega) (by omega)).trans out.control.one,
    (frame _ (by omega) (by omega)).trans out.control.two,
    (frame _ (by omega) (by omega)).trans out.control.nine,
    (frame _ (by omega) (by omega)).trans out.control.source,
    (frame _ (by omega) (by omega)).trans out.control.count,
    (frame _ (by omega) (by omega)).trans out.control.index⟩
  · exact ⟨(frame _ (by omega) (by omega)).trans out.frontiers.natFrontier,
    (frame _ (by omega) (by omega)).trans out.frontiers.scalarFrontier⟩
 have finalInput:Inputs n x u:=UniformAxisCacheInputs.transport c n 0 hn x a u (of_core retained)
  ⟨rfl,rfl,rfl,rfl⟩ (fun _ _=>rfl) (fun q lo hi=>frame q (by omega) (by omega))
 refine ⟨u,?_,?_,selected,finalInput,?_,?_,?_,?_,nh,sh,sr,outputs,roots⟩
 · simpa only [save_length] using boot.trans last
 · simp [u,save,applyBlock,Op.apply,writeNat,next,ap]
 · intro f
   have hf:=f.isLt
   exact (frame _ (by omega) (by omega)).trans
    ((regs _ (by omega) (by
     simp only [UniformAxisCacheStartupMachine.changed,List.mem_cons,List.not_mem_nil,or_false]
     omega)).trans (bank f))
 · rw [frame _ (by omega) (by omega),clock,UniformFourierClockBounds.prefix_zero]
 · simp [u,save,applyBlock,Op.apply,evalNat,writeNat,next,out.control.zero,
    out.frontiers.natFrontier,natAt]
 · simp [u,save,applyBlock,Op.apply,evalNat,writeNat,next,out.control.zero,
    out.frontiers.scalarFrontier,scalarAt]

end ExactFourierCircuits.UniformAxisCacheBootInputs
