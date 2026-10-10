import DFTModelGlobalKernelSourceReturn
import DFTModelGlobalKernelSourcePreparationBounds
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open DFTModelAdmissibilityControl
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program UniformRecursiveSavingProgram.program

def program : Program := UniformConditionalKernelLayout.programFor child W

lemma place_return (p : Program) {F n ticks : ℕ} (c : Context F) (x : Fin n→ℂ) (s t z : State)
 (first : BoundedExecution (UniformSameProgramSectorLoop.assembly p) n x c.inverse.layout.B (setPC s 0) ticks t)
 (lastTicks : ℕ)
 (last : BoundedExecution (UniformGlobalInverseReturn.programFor W) n x c.inverse.layout.B
   (setPC t 0) lastTicks z)
 (code : p.length+614≤c.inverse.layout.B) :
 BoundedExecution (UniformConditionalSectorReturn.programFor p W) n x c.inverse.layout.B
   (setPC s 0) (ticks+(lastTicks+1)) (setPC z (p.length+240)) := by
 have first' : BoundedExecution (UniformSameProgramSectorLoop.assembly p) n x c.inverse.layout.B
  (setPC s 0) ticks t := first
 have f:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalSectorReturn.loop_code p W)
  (by rw[UniformSameProgramSectorLoop.assembly_length];omega) (by omega) first'
 rw[show placed 0 (setPC s 0)=setPC s 0 by cases s;rfl] at f
 have l:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalSectorReturn.return_code p W)
  (by rw[UniformGlobalInverseReturn.program_length];omega) (by omega) last
 rw[show placed (p.length+20) (setPC t 0)=setPC t (p.length+20) by cases t;rfl] at l
 have stop : BoundedExecution (UniformConditionalSectorReturn.programFor p W) n x c.inverse.layout.B
  (setPC z (p.length+240)) 1 (setPC z (p.length+240)) := .halt l.final_bound
   (by simp[step,setPC,UniformConditionalSectorReturn.halt_at])
 exact f.executes (l.executes stop)

lemma place_whole (p : Program) {F n prepTicks kernelTicks : ℕ} (c : Context F) (x : Fin n→ℂ) (s a z : State)
 (first : BoundedExecution (UniformGlobalPackingChildPreparation.programFor W) n x c.metadata.B s prepTicks a)
 (last : BoundedExecution (UniformConditionalSectorReturn.programFor p W) n x c.inverse.layout.B
   (setPC a 0) kernelTicks z)
 (code : p.length+614≤c.inverse.layout.B) :
 BoundedExecution (UniformConditionalKernelLayout.programFor p W) n x c.inverse.layout.B s (prepTicks+(kernelTicks+1))
  (setPC z (p.length+613)) := by
 have first' : BoundedExecution (UniformGlobalPackingChildPreparation.programFor W) n x c.inverse.layout.B
  s prepTicks a := by simpa only[c.inverseB] using first
 have f:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalKernelLayout.movement_code p W)
  (by rw[UniformGlobalPackingChildPreparation.program_length];omega) (by omega) first'
 rw[show placed 0 s=s by cases s;simp[placed]] at f
 have l:=UniformBoundedAssembly.boundedExecution_placed (UniformConditionalKernelLayout.kernel_code p W)
  (by rw[UniformConditionalSectorReturn.program_length];omega) (by omega) last
 rw[show placed 372 (setPC a 0)=setPC a 372 by cases a;rfl] at l
 have stop : BoundedExecution (UniformConditionalKernelLayout.programFor p W) n x c.inverse.layout.B
  (setPC z (p.length+613)) 1 (setPC z (p.length+613)) := .halt l.final_bound
   (by simp[step,setPC,UniformConditionalKernelLayout.halt_at])
 exact f.executes (l.executes stop)

structure Result {F n i : ℕ} (c : Context F) (v v0 : ℕ→Fin c.packing.volume→Scalar)
 (K : ℕ) (x : Fin n→ℂ) (s s0 a a0 t t0 z z0 : State)
 (prepTicks loopTicks returnTicks : ℕ) (trace : List ℕ) : Prop where
 preparation : Preparation (i:=i) c v v0 x s s0 a a0 prepTicks
 children : DFTModelGlobalSectorLoop.Result n c.inverse.layout.B F c.gather.buffer c.gather.directory K
  c.loop.volume (states c) (states c) (UniformConditionalKernelLayout.packed c v)
  (UniformConditionalKernelLayout.packed c v0) x (setPC a 0) (setPC a0 0) t t0 loopTicks 9 trace
 returned : Return c x t t0 z z0 returnTicks
 gathers : DFTModelGlobalKernelSourceLower.gatherCost W (states c)≤prepTicks
 actual : BoundedExecution program n x c.inverse.layout.B s (prepTicks+(loopTicks+(returnTicks+1)+1))
  (setPC z (child.length+613))
 baseline : BoundedExecution program n (fun _=>0) c.inverse.layout.B s0 (prepTicks+(loopTicks+(returnTicks+1)+1))
  (setPC z0 (child.length+613))

/-- Complete original packing372 → SAME closed sector loop → original220
all-scatter/inverse return, with the real helper halts relocated to charged
jumps at their original call sites. Every child is constructed, once/sector. -/
theorem execution {F n i K : ℕ} (c : Context F) (v v0 : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s s0 : State) (same : StateMatch s s0)
 (h : UniformConditionalKernelLayout.Ready c i v s)
 (source0 : UniformGlobalRolePackingMachine.Source c.packing v0 s0)
 (hi : i<(states c).length) (code : child.length+614≤c.inverse.layout.B)
 (cap : DFTModelSavingCost.nativeWorkFactor≤K) (pc : s.pc=0) (wb : WordBound c.metadata.B s) :
 ∃a a0 t t0 z z0 prepTicks loopTicks returnTicks trace,
 Result (i:=i) c v v0 K x s s0 a a0 t t0 z z0 prepTicks loopTicks returnTicks trace := by
 obtain ⟨a,a0,prepTicks,prep⟩:=preparation c v v0 x s s0 same h source0 hi
  (by rw[←c.inverseB];omega) pc wb
 have ab : WordBound c.inverse.layout.B (setPC a 0) := by
  apply changePC_bound _ _ _ _ (by omega)
  simpa only[c.inverseB] using prep.actual.actual.final_bound
 have constants : UniformBinaryCStageMachine.Constants (setPC a 0) := prep.actual.constants
 obtain ⟨t,t0,loopTicks,trace,loops⟩:=DFTModelGlobalSectorLoop.execution (loop_geometry c) x
  (UniformConditionalKernelLayout.packed c v) (UniformConditionalKernelLayout.packed c v0)
  (setPC a 0) (setPC a0 0) (prep.matched.withPC 0)
  (by rw[UniformSameProgramSectorLoop.program_length];exact (Nat.add_le_add_left (show 20≤614 by decide) _).trans code) cap prep.actual.table prep.pending prep.pending0
  constants prep.actual.count prep.actual.directory prep.actual.frontier rfl ab
 obtain ⟨z,z0,returnTicks,returned⟩:=return_execution c v v0 x s s0 a a0 t t0 prepTicks prep loops (by omega)
 have gathers := Prefix.gather_lower c v x s a h hi (by rw[←c.inverseB];omega) pc prep.actual
 have first:=place_return child c x a t z (by simpa only[UniformSameProgramSectorLoop.program] using loops.actual) returnTicks returned.actual code
 have first0:=place_return child c (fun _ : Fin n=>0) a0 t0 z0 (by simpa only[UniformSameProgramSectorLoop.program] using loops.baseline) returnTicks returned.baseline code
 have whole:=place_whole child c x s a (setPC z (child.length+240)) prep.actual.actual first code
 have whole0:=place_whole child c (fun _ : Fin n=>0) s0 a0 (setPC z0 (child.length+240)) prep.baseline.actual first0 code
 refine ⟨a,a0,t,t0,z,z0,prepTicks,loopTicks,returnTicks,trace,prep,loops,returned,gathers,?_,?_⟩
 · simpa only[program,setPC] using whole
 · simpa only[program,setPC] using whole0

end
end ExactFourierCircuits.DFTModelGlobalKernelSource
