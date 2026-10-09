import UniformDirectLeafHighExecution
import UniformDirectLeafCacheLoopChoice
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafHighComplete
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheLoopData UniformDirectLeafHighGeometry
open UniformDirectLeafCacheLoopGeometry (slot slot_zero Inputs)
open UniformDirectLeafHighExecution UniformDirectLeafCacheLoopBoot
open UniformDirectLeafCacheLoopChoice
open UniformTransposeDescriptorMachine (Record)
noncomputable section

/-- Raw ordinary headers enter; the actual boot reads width and radix,
computes the count and both strides, and chooses the physical orientation.
The selected descriptor bank is a physical entry here; actual82 removes that
entry premise in the continuous caller below. -/
theorem execution {c:Config} {r A C B n:ℕ} (v flip D E:ℕ) (qs:List Record)
 (x:Fin n→ℂ) (s:State) (call:Args c s)
 (flag:s.natReg 6611=flip) (forward:s.natReg 5602=D) (transpose:s.natReg 5603=E)
 (width:s.natHeap (s.natReg 5600)=some v)
 (layout:UniformDirectLeafHighGeometry.Layout {c with record:=bank flip D E} r A C B qs)
 (input:Inputs {c with record:=bank flip D E} r A C qs s)
 (valid:∀q∈qs,UniformDirectLeafCacheSource.InRange r (A+3*r) q ∧UniformDirectLeafCacheSource.Legal q)
 (positive:2≤r) (length:qs.length=size v)
 (quadratic:v*(v-1)≤B) (ss:9*r≤B) (ns:3*r+11≤B)
 (pc:s.pc=0) (wb:WordBound B s):∃u ticks,
 BoundedExecution UniformDirectLeafCacheLoopProgram.program n x B s ticks u ∧
 ticks≤(62*r+212)*qs.length+24 ∧
 Done {c with record:=bank flip D E} r A C qs 0 positive s u:=by
 have count:size v≤B:=by rw[←length];have:=layout.natEnd;nlinarith
 have boot:=boot_execution x s call width input.radix count quadratic ss ns layout.code pc wb
 let a:=UniformDirectLeafCacheLoopBoot.initialized s
 have ap:a.pc=19:=by
  simp only[a,UniformDirectLeafCacheLoopBoot.initialized,applyBlock_pc,divided,writeNat,next,left,pc]
  rfl
 have controls:=initialized_controls call width input.radix
 have choice:=UniformDirectLeafCacheLoopChoice.execution flip D E x a controls
  ((initialized_nat s 6611 (Or.inl (by omega))).trans flag)
  ((initialized_nat s 5602 (Or.inl (by omega))).trans forward)
  ((initialized_nat s 5603 (Or.inl (by omega))).trans transpose) ap layout.code boot.final_bound
 let z:=chosen a flip D E
 have args:Args {c with record:=bank flip D E} z:=chosen_args flip D E (initialized_args call)
 have controls':Controls r qs.length 0 z:=by rw[length];exact chosen_controls flip D E controls
 have input':Inputs {c with record:=bank flip D E} r A C qs z:=
  ⟨input.records,input.original,input.radix,input.conjugate,input.values,input.constants⟩
 have args':Args (slot {c with record:=bank flip D E} r qs 0) z:=by rw[slot_zero];exact args
 obtain ⟨u,ticks,run,cost,done⟩:=loop qs.length layout valid positive x z (by omega) args' controls' input' rfl choice.final_bound
 refine ⟨u,_,boot.executes (choice.executes run),?_,?_,⟩
 · by_cases zero:flip=0 <;>simp only[zero,ite_true,ite_false] <;>omega
 · refine ⟨done.pc,done.args,done.controls,done.inputs,done.events,?_,?_,?_,done.outputs,done.roots⟩
   · intro j h;exact done.scalarOutside j h
   · intro j h h';exact done.natPrefix j h h'
   · intro j h;exact done.natHigh j h
end
end ExactFourierCircuits.UniformDirectLeafHighComplete
