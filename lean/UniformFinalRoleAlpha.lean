import UniformFinalRoleRetention
import UniformPhysicalCRTConsumerMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2 (5.5)-(5.6), PDF p.22, and §5.3 three-transform chirp
construction, PDF pp.22-23 (`eq:crt-fourier`, `eq:working-transform`, `eq:chirp`).

Role-bank, prepared-spectrum and movement bookkeeping refines the actual
three-transform algorithm. The paper does not specify these cells or registers;
all desired values must be obtained from the same actual producing executions.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalRoleAlpha
open UniformMachine UniformTensorMonomialMachine UniformFinalRoleModel
open UniformAxisCachePreparationRetention UniformFinalRoleExecution
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
namespace C
export UniformPhysicalCRTConsumerMachine (alphaProgram)
end C
def standard {n:ℕ} (x:Fin n→ℂ) (j:Fin (V n)):Scalar:=
 UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x j.val
def physical {n:ℕ} (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (i:ℕ) (j:Fin (V n)):Scalar:=
 if i=0 then standard x (AP j) else values x false AP i j
lemma numeric_zero {n:ℕ} [NeZero (V n)] (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (j:Fin (V n)):
 (physical x AP 0 j).value=UniformFinalNumericJoin.data x (AP j):=
 UniformFinalNumericJoin.padded_input_value AP x j
lemma generic_cells (roles volume sourceBase:ℕ) (v:ℕ→Fin volume→Scalar)
 (first:Fin volume→Scalar) (s u:State)
 (old:∀i:Fin roles,∀j:Fin volume,s.scalarHeap (sourceBase+i.val*volume+j.val)=some (v i.val j))
 (gathered:∀j:Fin volume,u.scalarHeap (sourceBase+j.val)=some (first j))
 (outside:UniformPermutationMachine.Outside sourceBase volume s.scalarHeap u):
 ∀i:Fin roles,∀j:Fin volume,u.scalarHeap (sourceBase+i.val*volume+j.val)=
 some (if i.val=0 then first j else v i.val j):=by
 intro i j
 by_cases hi:i.val=0
 · simp only[hi,Nat.zero_mul,Nat.add_zero,ite_true]
   exact gathered j
 · rw[ite_eq_right hi]
   apply Eq.trans _ (old i j)
   apply outside
   apply Or.inr
   have bound:volume ≤ i.val*volume:=by
    simpa only[Nat.one_mul] using Nat.mul_le_mul_right volume (by omega:1 ≤ i.val)
   omega
lemma cells {n:ℕ} (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (s u:State)
 (old:∀i:Fin W,∀j:Fin (V n),s.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (values x false AP i.val j))
 (gathered:∀j:Fin (V n),u.scalarHeap (2*UniformJointAllocation.slab c n+j.val)=some (standard x (AP j)))
 (outside:UniformPermutationMachine.Outside (2*UniformJointAllocation.slab c n) (V n) s.scalarHeap u):
 ∀i:Fin W,∀j:Fin (V n),u.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (physical x AP i.val j):=
 generic_cells W (V n) (2*UniformJointAllocation.slab c n) (values x false AP)
  (fun j=>standard x (AP j)) s u old gathered outside
lemma frame {n:ℕ} (s u:State)
 (out:UniformPermutationMachine.Outside (2*UniformJointAllocation.slab c n) (V n) s.scalarHeap u)
 (h:UniformPhysicalCRTConsumerMachine.Frame s u):UniformFinalRoleExecution.Frame n s u:=by
 refine ⟨h.natHeap,?_,?_,fun q h20 _ _=>h.scalarReg q h20,h.outputs,h.roots⟩
 · intro a ha
   apply out
   rcases ha with ha|ha
   · exact Or.inl ha
   · have roles:1≤W:=by have:=UniformFinalRoleGeometry.roles_two;omega
     have bound:V n≤W*V n:=by simpa only[Nat.one_mul]using Nat.mul_le_mul_right (V n) roles
     exact Or.inr (by omega)
 · intro q hq hc
   exact h.natReg q ⟨hq.1,by unfold H.Changed at hc;omega⟩

/-- The actual18 AP gather replaces only role0 after the data loader. -/
theorem execution {n:ℕ} (hn:0<n) (x:Fin n→ℂ) (AP:Fin (V n)≃Fin (V n)) (s:State)
 (core:Core n x s) (args:H.Args c n W false s)
 (source:s.natReg 6026=2*UniformJointAllocation.slab c n)
 (tableAddress:s.natReg 7310=UniformKernelSpectrumStorage.alphaBase c n)
 (table:UniformGlobalNatPreparation.PermutationBank (V n) (UniformKernelSpectrumStorage.alphaBase c n) s.natHeap AP)
 (old:∀i:Fin W,∀j:Fin (V n),s.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (values x false AP i.val j))
 (pc:s.pc=0) (wb:WordBound (UniformJointAllocation.envelope c n) s):∃u,
 BoundedExecution C.alphaProgram n x (UniformJointAllocation.envelope c n) s (9*V n+10) u∧u.pc=17∧
 (∀i:Fin W,∀j:Fin (V n),u.scalarHeap (2*UniformJointAllocation.slab c n+i.val*V n+j.val)=some (physical x AP i.val j))∧
 UniformFinalRoleExecution.Frame n s u:=by
 obtain ⟨_,code,extent,_,kernelBefore,tableFit,_⟩:=UniformFinalRoleGeometry.geometry hn
 have oneRole:V n≤W*V n:=by
  have h:1≤W:=by have:=UniformFinalRoleGeometry.roles_two;omega
  simpa only[Nat.one_mul] using Nat.mul_le_mul_right (V n) h
 have inputBefore:UniformPaddedInputPreparation.dataBase n+V n≤2*UniformJointAllocation.slab c n:=by
  unfold UniformChirpKernelPreparation.kernelBase at kernelBefore
  omega
 obtain ⟨u,run,up,gathered,_kept,out,h⟩:=UniformPhysicalCRTConsumerMachine.alpha_execution n
  (UniformJointAllocation.envelope c n) (V n) (UniformPaddedInputPreparation.dataBase n)
  (2*UniformJointAllocation.slab c n) (UniformKernelSpectrumStorage.alphaBase c n) x (standard x) AP s pc
  core.metadata.saved.workingLength args.padded source tableAddress
  (fun j=>core.operands.input j.val j.isLt) table (Or.inl inputBefore)
  (by omega) (by omega) tableFit (by omega) wb
 exact ⟨u,run,up,cells x AP s u old gathered out,frame s u out h⟩
end
end ExactFourierCircuits.UniformFinalRoleAlpha
