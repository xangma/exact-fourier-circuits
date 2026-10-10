import DFTModelSavingNativeControl
import UniformRecursiveSmallEntry

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSavingNativeEntry
open UniformMachine DFTModelAdmissibilityControl DFTModelSavingNativeControl
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program

lemma constants_match {s s0 : State} (same : StateMatch s s0)
    (constants : UniformBinaryCStageMachine.Constants s) :
    UniformBinaryCStageMachine.Constants s0 := by
  constructor
  · obtain ⟨v,hv,hm⟩:=(same.scalarHeap 1).left constants.1
    rw [←hm.eq_of_prepared rfl] at hv
    exact hv
  · obtain ⟨v,hv,hm⟩:=(same.scalarHeap 2).left constants.2
    rw [←hm.eq_of_prepared rfl] at hv
    exact hv

structure Ready (k A V F depth : ℕ) (s t : State) : Prop where
  pc : t.pc=P.address .readyEntry
  nativeBits : t.natReg 5300=k
  nativeBase : t.natReg 3300=A
  bits : t.natReg 4120=k
  base : t.natReg 4121=A
  volume : t.natReg 4122=V
  depthReg : t.natReg 4151=depth
  one : t.natReg 4153=1
  frontier : t.natReg 4123=(if depth=0 then F+34*(k+1) else F)
  root_stack : depth=0→t.natReg 4150=F
  child_stack : depth≠0→t.natReg 4150=s.natReg 4150
  frame : UniformRecursiveSavingExecution.EntryFrame s t

theorem single (n B k A V F depth : ℕ) (x : Fin n→ℂ) (s : State)
    (pc : s.pc=0) (bits : s.natReg 4120=k) (base : s.natReg 4121=A)
    (volume : s.natReg 4122=V) (frontier : s.natReg 4123=F)
    (dp : s.natReg 4151=depth) (bound : WordBound B s)
    (code : P.program.length≤B) (stackEnd : F+34*(k+1)≤B) :
    ∃t,BoundedRuns P.program n x B s (if depth=0 then 10 else 4) t ∧
      Ready k A V F depth s t := by
  obtain ⟨t,actual,tp,tn,tA,tk,ta,tv,td,one,tf,root,frame⟩:=
    UniformRecursiveSavingExecution.entry_execution n B k A V F depth x s
      pc bits base volume frontier dp bound code stackEnd
  refine ⟨t,actual,⟨tp,tn,tA,tk,ta,tv,td,one,tf,root,?_,frame⟩⟩
  intro nonzero
  exact UniformRecursiveSmallEntry.nonroot_stack n B k A depth x s t
    pc bits base dp bound code nonzero (by simpa only [nonzero,ite_false] using actual)

/-- The real pc-zero entry is charged on both sources. Root stack allocation
and nonroot stack retention are established by the actual entry bytecode. -/
theorem paired (n B k A V F depth : ℕ) (x : Fin n→ℂ) (s s0 : State)
    (same : StateMatch s s0) (pc : s.pc=0) (bits : s.natReg 4120=k)
    (base : s.natReg 4121=A) (volume : s.natReg 4122=V)
    (frontier : s.natReg 4123=F) (dp : s.natReg 4151=depth)
    (bound : WordBound B s) (code : P.program.length≤B) (stackEnd : F+34*(k+1)≤B) :
    ∃t t0,
      BoundedRuns P.program n x B s (if depth=0 then 10 else 4) t ∧
      BoundedRuns P.program n (fun _=>0) B s0 (if depth=0 then 10 else 4) t0 ∧
      StateMatch t t0 ∧Ready k A V F depth s t ∧Ready k A V F depth s0 t0 := by
  obtain ⟨t,actual,ready⟩:=single n B k A V F depth x s
    pc bits base volume frontier dp bound code stackEnd
  obtain ⟨t0,zero,ready0⟩:=single n B k A V F depth (fun _=>0) s0
    (same.pc.trans pc) (by rw [same.natReg];exact bits)
    (by rw [same.natReg];exact base) (by rw [same.natReg];exact volume)
    (by rw [same.natReg];exact frontier) (by rw [same.natReg];exact dp)
    (same.wordBound bound) code stackEnd
  exact ⟨t,t0,actual,zero,paired_runs actual zero same,ready,ready0⟩

end
end ExactFourierCircuits.DFTModelSavingNativeEntry
