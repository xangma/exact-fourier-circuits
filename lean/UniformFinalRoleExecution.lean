import UniformFinalRoleGeometry
import UniformSequentialExecution

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleExecution
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformAxisCachePreparationRetention UniformFinalStartupData
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
namespace H
export UniformFinalOuterHeaders (roleArgs Args Changed)
end H
namespace N
export UniformNatBlockMachine (applyBlock)
end N
namespace R
export UniformRoleInputMachine (Protected)
end R
structure Frame (n:ℕ) (s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalar:∀a,a<2*UniformJointAllocation.slab c n∨
  2*UniformJointAllocation.slab c n+W*V n≤a→u.scalarHeap a=s.scalarHeap a
 natReg:∀q,R.Protected q→¬H.Changed q→u.natReg q=s.natReg q
 scalarReg:∀q,q≠20→q≠32→q≠94→u.scalarReg q=s.scalarReg q
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
lemma args_transport {n:ℕ} {mode:Bool} {s u:State}
 (h:UniformRoleInputMachine.Frame s u) (args:H.Args c n W mode s):H.Args c n W mode u:=by
 constructor
 all_goals first
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.roles
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.volume
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.source
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.input
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.kernel
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.alpha
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.padded
 | exact (h.natReg _ (by unfold R.Protected;omega)).trans args.storage

lemma args_pc {n pc:ℕ} {mode:Bool} {s:State} (args:H.Args c n W mode s):
 H.Args c n W mode (setPC s pc):=
 ⟨args.roles,args.volume,args.source,args.input,args.kernel,args.alpha,args.padded,args.storage⟩

lemma entry_cells {n:ℕ} (x:Fin n→ℂ) (mode:Bool) (s a:State)
 (core:Core n x s) (data:Data n x s) (sh:a.scalarHeap=s.scalarHeap):
 (∀j:Fin (V n),a.scalarHeap ((if mode then UniformChirpKernelPreparation.kernelBase n
  else UniformInputPermutationPreparation.destination n)+j.val)=some (input x mode j))∧
 (∀j:Fin (V n),a.scalarHeap (UniformChirpKernelPreparation.kernelBase n+j.val)=some (kernel n j)):=by
 constructor
 · intro j
   rw[sh]
   cases mode
   · exact data.gathered j
   · exact core.operands.kernel j.val j.isLt
 · intro j
   rw[sh]
   exact core.operands.kernel j.val j.isLt

lemma compose_frame {n:ℕ} (s a u:State)
 (nh:a.natHeap=s.natHeap) (sh:a.scalarHeap=s.scalarHeap)
 (sr:a.scalarReg=s.scalarReg) (outputs:a.outputs=s.outputs) (roots:a.rootOrders=s.rootOrders)
 (regs:∀q,¬H.Changed q→a.natReg q=s.natReg q)
 (out:∀q,q<2*UniformJointAllocation.slab c n∨
  2*UniformJointAllocation.slab c n+W*V n≤q→u.scalarHeap q=a.scalarHeap q)
 (frame:UniformRoleInputMachine.Frame a u):Frame n s u:=
 ⟨frame.natHeap.trans nh,fun q h=>(out q h).trans (congrFun sh q),
  fun q hq unchanged=>(frame.natReg q hq).trans (regs q unchanged),
  fun q h20 h32 h94=>(frame.scalarReg q h20 h32 h94).trans (congrFun sr q),
  frame.outputs.trans outputs,frame.roots.trans roots⟩

/-- The actual fixed header followed by actual42. Its entry tables and operands
are earlier physical outputs; all-W role cells are constructed by literal runs. -/
theorem execution {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (mode:Bool)
 (AP:Fin (V n)≃Fin (V n)) (s:State)
 (core:Core n x s) (data:Data n x s)
 (source:s.natReg 6026=2*UniformJointAllocation.slab c n)
 (physical:s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n)
 (table:UniformGlobalNatPreparation.PermutationBank (V n) (UniformKernelSpectrumStorage.alphaBase c n) s.natHeap AP)
 (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 UniformSequentialExecution.LocalStages n (UniformJointAllocation.envelope c n) x
  [UniformSequentialAssembly.natProgram (H.roleArgs W mode),UniformRoleInputMachine.program] s
  ((if mode then 18 else 19)+(5*(W*V n)+16*V n+24)) u∧u.pc=41∧
 (∀i:Fin W,∀j:Fin (V n),u.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=
  some (values x mode AP i.val j))∧H.Args c n W mode u∧Frame n s u:=by
 obtain ⟨roles,code,extent,inputBefore,kernelBefore,tableFit,low⟩:=UniformFinalRoleGeometry.geometry hn
 let s0:=setPC s 0
 have core0:Core n x s0:=core.withPC
 have geo:UniformNatBlockMachine.readable (H.roleArgs W mode) s0∧
  UniformNatBlockMachine.peak (H.roleArgs W mode) s0≤UniformJointAllocation.envelope c n:=
  UniformFinalOuterHeaders.roleArgs_safe W mode s0 _ roles
   (by change s.natReg 6026≤_;rw[source];unfold UniformJointAllocation.envelope;omega)
   (by change s.natReg 7310≤_;rw[physical];have h:=tableFit;omega)
   (UniformFinalRoleGeometry.header_low hn s0 core0.metadata)
 have head:=UniformSequentialAssembly.nat_execution (H.roleArgs W mode) x s0 rfl
  (changePC_bound _ s 0 wb (by omega))
  (by rw[UniformFinalOuterHeaders.roleArgs_length];cases mode <;>simp only[Bool.false_eq_true,ite_false,ite_true] <;>omega) geo.1 geo.2
 let a:=N.applyBlock (H.roleArgs W mode) s0
 have args:H.Args c n W mode a:=UniformFinalOuterHeaders.roleArgs_values c n W mode s0 core0.metadata source physical
 obtain ⟨nh,sh,sr,outputs,roots,regs⟩:=UniformFinalOuterHeaders.roleArgs_frame W mode s0
 let a0:=setPC a 0
 obtain ⟨inputCells,kernelCells⟩:=entry_cells x mode s a0 core data sh
 have table0:UniformGlobalNatPreparation.PermutationBank (V n) (UniformKernelSpectrumStorage.alphaBase c n) a0.natHeap AP:=by
  intro j
  exact (congrFun nh _).trans (table j)
 obtain ⟨u,run,up,cells,out,frame⟩:=UniformRoleInputMachine.execution n (UniformJointAllocation.envelope c n)
  W (V n) (2*UniformJointAllocation.slab c n)
  (if mode then UniformChirpKernelPreparation.kernelBase n else UniformInputPermutationPreparation.destination n)
  (UniformChirpKernelPreparation.kernelBase n) (UniformKernelSpectrumStorage.alphaBase c n) x
  (input x mode) (kernel n) AP a0 rfl UniformFinalRoleGeometry.roles_two args.roles args.volume args.source
  args.input args.kernel args.alpha inputCells kernelCells table0
  (by cases mode;exact inputBefore;exact kernelBefore) kernelBefore extent tableFit code
  (changePC_bound _ a 0 head.final_bound (by omega))
 have stages:=UniformSequentialExecution.LocalStages.cons head
  (UniformSequentialExecution.LocalStages.cons run (.nil u run.final_bound))
 have ticks:(H.roleArgs W mode).length+1+(5*(W*V n)+16*V n+24+0)=
  (if mode then 18 else 19)+(5*(W*V n)+16*V n+24):=by
  rw[UniformFinalOuterHeaders.roleArgs_length]
  cases mode <;>simp only[Bool.false_eq_true,ite_false,ite_true,Nat.add_zero]
 refine ⟨u,?_,up,cells,args_transport frame (args_pc args),?_⟩
 · simpa only[ticks] using stages
 · exact compose_frame s a0 u nh sh sr outputs roots regs out frame
end
end ExactFourierCircuits.UniformFinalRoleExecution
