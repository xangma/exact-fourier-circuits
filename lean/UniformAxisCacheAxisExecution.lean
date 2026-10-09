import UniformAxisCacheWholePrefix
import UniformAxisCacheContents
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAxisExecution
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests UniformAxisCachePhysical
open UniformJointCacheAllocation
noncomputable section

def budget (c:A.Constants) (n:ℕ) (j:Fin (C.ell n)):ℕ:=
 4*Nat.clog 2 (4*Seed.radix n j)+66+
 ((2*Seed.radix n j+1)*UniformLocalCacheTreeExecution.nodeBudget (Seed.radix n j)+18)+6+
 UniformLocalCacheTimingExecution.printerBudget (Seed.radix n j) 0 (axis c n j).requests+7+8+
 (UniformLocalStoredRequestLoop.costPrefix n j (canonical c n j) (canonical c n j).length+23)+
 ((62*Seed.radix n j+246)*UniformDirectLeafForestModel.demand (visits c n j)+93*(visits c n j).length+40)

structure Result (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (x:Fin n→ℂ) (s u:State):Prop where
 contents:UniformAxisCacheContents.Contents c n hn j u
 input:Inputs n x u
 control:Control n j.val u
 allocation:UniformAxisCacheAllocationMachine.Result (Seed.radix n j) (natAt c n j.val) (scalarAt c n j.val) u
 bank:UniformLocalRectangleWorkspaceHeaders.Bank n u
 clock:u.natReg 5921=UniformFourierClockBounds.clockPrefix n (j.val+1)
 savedNat:u.natReg 6909=s.natReg 6909
 savedScalar:u.natReg 6910=s.natReg 6910
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 previous:∀i:Fin (C.ell n),i.val<j.val→Heaps c n i s u

/-- One concrete4654 controller iteration executes actual370, real horizon7,
eight header writes, all3776 requests and every461 leaf scan. -/
theorem execution (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (x:Fin n→ℂ) (s:State)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedRuns UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks≤budget c n j∧u.pc=4642∧Result c n hn j x s u:=by
 have fit:=UniformAxisCacheWholePrefix.code_fits c n
 obtain ⟨ta,t,tr,a,first,ap,treeCost,timeCost,requestCost,requests,ends,source,prepared,
  control,allocation,ai,ab,ac,an,as_,ao,ar,previous,radix⟩:=
  UniformAxisCacheWholePrefix.rectangle_axis c n hn j x s selected input bank clock pc wb
 obtain ⟨u,tf,last,leafCost,up,out⟩:=UniformAxisCacheForestExecution.execution c n hn j
  UniformAxisCacheWholeProgram.program 4181 4642 UniformAxisCacheWholeProgram.forestCode_at
  (by omega) (by omega) x a prepared ends source control allocation ai ab
  (fun i hi=>requests.completed i hi hi) radix ap first.final_bound
 refine ⟨u,4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7+8+tr+tf,first.trans last,?_,up,?_⟩
 · unfold budget
   omega
 · exact ⟨UniformAxisCacheContents.of_outcome out,out.input,out.control,out.result,out.bank,
    out.clock.trans ac,out.savedNat.trans an,out.savedScalar.trans as_,out.outputs.trans ao,
    out.roots.trans ar,fun i old=>(previous i old).trans (out.previous i old)⟩

end
end ExactFourierCircuits.UniformAxisCacheAxisExecution
