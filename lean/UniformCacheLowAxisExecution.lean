import UniformCacheLowWholePrefix
import UniformCacheLowForestExecution
import UniformAxisCacheAxisExecution
import UniformAxisCacheContents
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAxisExecution
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation UniformAxisCacheInputs
open UniformAxisCacheForestEntry UniformAxisCacheCanonicalRequests UniformAxisCachePhysical
open UniformJointCacheAllocation
noncomputable section

/-- One concrete4654 controller iteration executes actual370, real horizon7,
eight header writes, all3776 requests and every461 leaf scan. -/
theorem execution_low (c:A.Constants) (n:ℕ) (hn:0<n) (j:Fin (C.ell n)) (x:Fin n→ℂ) (s:State)
 (selected:Selected c n j.val s) (input:Inputs n x s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (clock:s.natReg 5921=UniformFourierClockBounds.clockPrefix n j.val)
 (pc:s.pc=20) (wb:WordBound (A.envelope c n) s):
 ∃u ticks,BoundedRuns UniformAxisCacheWholeProgram.program n x (A.envelope c n) s ticks u∧
 ticks≤budget c n j∧u.pc=4642∧Result c n hn j x s u ∧ UniformCacheLowRetention.Frame n s u:=by
 have fit:=UniformAxisCacheWholePrefix.code_fits c n
 obtain ⟨ta,t,tr,a,first,ap,treeCost,timeCost,requestCost,requests,ends,source,prepared,
  control,allocation,ai,ab,ac,an,as_,ao,ar,previous,radix,rectangleLow⟩:=
  UniformAxisCacheWholePrefix.rectangle_axis_low c n hn j x s selected input bank clock pc wb
 obtain ⟨u,tf,last,leafCost,up,out,forestLow⟩:=UniformAxisCacheForestExecution.execution_low c n hn j
  UniformAxisCacheWholeProgram.program 4181 4642 UniformAxisCacheWholeProgram.forestCode_at
  (by omega) (by omega) x a prepared ends source control allocation ai ab
  (fun i hi=>requests.completed i hi hi) radix ap first.final_bound
 refine ⟨u,4*Nat.clog 2 (4*Seed.radix n j)+66+ta+6+t+7+8+tr+tf,first.trans last,?_,up,?_,rectangleLow.trans forestLow⟩
 · unfold budget
   omega
 · exact ⟨UniformAxisCacheContents.of_outcome out,out.input,out.control,out.result,out.bank,
    out.clock.trans ac,out.savedNat.trans an,out.savedScalar.trans as_,out.outputs.trans ao,
    out.roots.trans ar,fun i old=>(previous i old).trans (out.previous i old)⟩

end
end ExactFourierCircuits.UniformAxisCacheAxisExecution
