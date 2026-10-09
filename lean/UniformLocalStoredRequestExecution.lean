import UniformLocalStoredRequestLoopExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalStoredRequestLoop
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformAllAxisSeedPreparation UniformJointAllocation
open UniformLocalRequestPlan UniformLocalRequestControl UniformLocalRequestGeometry
noncomputable section

/-- One fixed literal program derives its count from actual forest end
registers, prepares all requests, and returns the measured cumulative ends.
Physical source rows/times are supplied by the genuine370 forest/timing phase;
there is no cache, factor, action or per-request execution premise. -/
theorem execution {constants n j qs R T}(hn:0<n)
 (g:UniformLocalRequestGeometry.Geometry constants n j qs R T)(x:Fin n → ℂ)(s:State)
 (header:UniformLocalRequestCursorMachine.Header (radix n j) R qs.length T
  (UniformJointCacheAllocation.axis constants n j).control
  (UniformJointCacheAllocation.axis constants n j).pool (UniformJointCacheWorkspace.stride n) s)
 (bank:UniformLocalRectangleWorkspaceHeaders.Bank n s)
 (selected:s.natReg 6167=directoryBase n+2*j.val)(axis:s.natReg 6906=j.val)
 (source:Source R T qs s)(original:Retained n (axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)(operands:UniformInitialPreparation.Operands n x s)
 (code:3776 ≤ envelope constants n)(pc:s.pc=0)(wb:WordBound (envelope constants n) s):∃u ticks,
 BoundedExecution program n x (envelope constants n) s ticks u ∧
 ticks ≤ costPrefix n j qs qs.length+23 ∧u.pc=3775 ∧
 Ready constants n j qs R T g x qs.length u ∧LoopFrame constants n j s u:=by
 have persistent:=UniformCanonicalCacheSlotGeometry.persistent_bounds constants hn j 0 (Nat.zero_le _)
 have h3:3*slab constants n ≤ envelope constants n:=by unfold envelope;omega
 have room:(UniformJointCacheAllocation.axis constants n j).control+3*radix n j+4 ≤ envelope constants n:=by
  have row:=persistent.2.1
  rw[UniformJointCacheAllocation.slot_abi_end] at row
  simp only[Nat.zero_add,Nat.mul_one,UniformJointCacheAllocation.axis_radix] at row
  omega
 have temporary:22*UniformJointCacheWorkspace.stride n+1 ≤ envelope constants n:=
  (Nat.le_of_lt (low_before_cache constants n).2).trans (by unfold envelope;omega)
 obtain ⟨a,boot,ap,cursor,nh,sh,regs,out,roots⟩:=
  UniformLocalRequestCursorMachine.execution x s header room temporary (by omega) pc wb
 have first:=UniformBoundedAssembly.boundedExecution_placed cursor_code
  (by rw[UniformLocalRequestCursorMachine.program_length];omega) (by omega) boot
 have zero:placed 0 s=s:=by cases s;simp[placed]
 rw[zero] at first
 let start:=setPC a 21
 have startCursor:UniformLocalRequestCursorMachine.Cursor (radix n j) R qs.length T
   (UniformJointCacheAllocation.axis constants n j).control
   (UniformJointCacheAllocation.axis constants n j).pool (UniformJointCacheWorkspace.stride n) start:=
  ⟨cursor.pool,cursor.permutation,cursor.widths,cursor.markers,cursor.axis,cursor.abi,
   cursor.lowRow,cursor.control,cursor.inverse,cursor.mu,cursor.conjugateMu,
   cursor.pointer,cursor.timePointer,cursor.index,cursor.count⟩
 have control:Control constants n j qs R T 0 start:=by
  apply UniformLocalRequestControl.boot constants j qs R T start startCursor
  · intro f
    exact (UniformLocalRequestFrames.cursor_high boot _ (by have:=f.isLt;omega)).trans (bank f)
  · exact (UniformLocalRequestFrames.cursor_nat boot 6167 (by decide)).trans selected
  · exact (UniformLocalRequestFrames.cursor_high boot 6906 (by omega)).trans axis
 have frame:UniformSeedRankCrossPreparation.PreservedFrame n s start:=
  ⟨fun q _=>congrFun nh q,fun q _=>congrFun sh q,
   fun q lo hi=>UniformLocalRequestFrames.cursor_nat boot q (by simp[UniformLocalRequestFrames.cursorWrites];omega),out,roots⟩
 have startConjugate:UniformAllAxisConjugatePreparation.Retained n (axisCount n) start:=
  UniformLocalRectangleCoefficientMachine.conjugate_retained conjugate
   (fun q _=>congrFun sh q) (fun q _=>congrFun nh q)
 have ready:Ready constants n j qs R T g x 0 start:=
  ⟨control,source.transport (fun _ _ _=>congrFun nh _) (fun _ _=>congrFun nh _),
   frame.retained original,startConjugate,frame.protected.metadata metadata,
   frame.protected.operands operands,by intro k hk old;omega⟩
 obtain ⟨u,t,tail,cost,up,final,lastFrame⟩:=loop hn g x qs.length 0 (by omega) start ready code rfl first.final_bound
 have bootFrame:LoopFrame constants n j s start:=
  ⟨fun q _ _=>congrFun nh q,fun q _ _=>congrFun sh q,
   fun q lo=>UniformLocalRequestFrames.cursor_high boot q lo,out,roots⟩
 refine ⟨u,21+t,first.executes tail,?_,up,final,bootFrame.trans lastFrame⟩
 simp only[costPrefix] at cost
 omega

end
end ExactFourierCircuits.UniformLocalStoredRequestLoop
