import DFTModelSavingNativeControl
import UniformRecursivePaddingActualFragments

set_option autoImplicit false

/-! Paper E (adc7f), §2.6, Theorem 2.6. These are the unchanged RAM
padding control blocks, with the parent and cursor metadata retained. -/
namespace ExactFourierCircuits.DFTModelSavingNativePaddingControl
open UniformMachine DFTModelAdmissibilityControl
open UniformRecursivePaddingFrames
open UniformFixedNetworkScheduleMachine (Printed)
noncomputable section

lemma parent_match {k q A F r stack depth : ℕ} {s s0 : State}
    (same : StateMatch s s0) (parent : Parent k q A F r stack depth s) :
    Parent k q A F r stack depth s0 := by
  rcases parent with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩
  constructor <;> rw [same.natReg] <;> assumption

lemma metadata_match {F U saved role last : ℕ} {s s0 : State}
    (same : StateMatch s s0) (metadata : Metadata F U saved role last s) :
    Metadata F U saved role last s0 := by
  rcases metadata with ⟨a,b,c,d,e⟩
  constructor <;> rw [same.natHeap] <;> assumption

lemma printed_match {U : ℕ} {words : List ℕ} {s s0 : State}
    (same : StateMatch s s0) (printed : Printed U words s) : Printed U words s0 := by
  intro j hj
  rw [same.natHeap]
  exact printed j hj

lemma metadata_frame {F U saved role last : ℕ} {s u : State}
    (metadata : Metadata F U saved role last s)
    (frame : UniformRecursivePaddingControl.Frame [] s u) :
    Metadata F U saved role last u :=
  metadata.transport (fun z _=>frame.natHeap z (by simp))

theorem test (n B k q A F r stack depth U saved role last : ℕ)
    (x : Fin n→ℂ) (s : State)
    (pc : s.pc=P.address .paddingTest)
    (parent : Parent k q A F r stack depth s)
    (metadata : Metadata F U saved role last s)
    (low : 6≤F) (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u, BoundedRuns P.program n x B s 6 u ∧
      u.pc=(if role<last then P.address .paddingPatch else P.address .paddingFinish) ∧
      Parent k q A F r stack depth u ∧ Metadata F U saved role last u ∧
      u.natReg 4175=role ∧ u.natReg 4176=last ∧
      UniformRecursivePaddingControl.Frame [] s u := by
  obtain ⟨u,run,up,dst,endpoint,frame⟩:=UniformRecursivePaddingControl.test_execution
    n B F role last x s pc parent.frontier parent.one low metadata.current metadata.endpoint bound code
  have bits:=UniformRecursivePaddingFragments.test_bits n B F role last x s u pc
    parent.frontier parent.one metadata.current metadata.endpoint low bound code run
  exact ⟨u,run,up,parent.padding frame (bits.trans parent.nativeBits),
    metadata_frame metadata frame,dst,endpoint,frame⟩

theorem finish (n B k q A F r stack depth U saved role last : ℕ)
    (x : Fin n→ℂ) (s : State)
    (pc : s.pc=P.address .paddingFinish)
    (parent : Parent k q A F r stack depth s)
    (metadata : Metadata F U saved role last s)
    (low : 6≤F) (bound : WordBound B s) (code : P.program.length≤B) :
    ∃u, BoundedRuns P.program n x B s 4 u ∧ u.pc=P.address .loop ∧
      u.natReg 2850=saved ∧ Parent k q A F r stack depth u ∧
      Metadata F U saved role last u ∧ UniformRecursivePaddingControl.Frame [] s u := by
  obtain ⟨u,run,up,cursor,frame⟩:=UniformRecursivePaddingControl.finish_execution
    n B F saved x s pc parent.frontier low metadata.saved bound code
  have bits:=UniformRecursivePaddingFragments.finish_bits n B F saved x s u pc
    parent.frontier metadata.saved low bound code run
  exact ⟨u,run,up,cursor,parent.padding frame (bits.trans parent.nativeBits),
    metadata_frame metadata frame,frame⟩

theorem next (n B k q A F r stack depth U saved role last : ℕ)
    (x : Fin n→ℂ) (s : State)
    (pc : s.pc=P.address .paddingNext)
    (parent : Parent k q A F r stack depth s)
    (metadata : Metadata F U saved role last s)
    (low : 6≤F) (bound : WordBound B s) (code : P.program.length≤B)
    (increment : role+1≤B) :
    ∃u, BoundedRuns P.program n x B s 6 u ∧ u.pc=P.address .paddingTest ∧
      Parent k q A F r stack depth u ∧ Metadata F U saved (role+1) last u ∧
      UniformRecursivePaddingControl.Frame [F-4] s u := by
  obtain ⟨u,run,up,current,frame⟩:=UniformRecursivePaddingControl.next_execution
    n B F role x s pc parent.frontier parent.one low metadata.current bound code increment
  have bits:=UniformRecursivePaddingFragments.next_bits n B F role x s u pc
    parent.frontier parent.one metadata.current low bound code increment run
  have mu : Metadata F U saved (role+1) last u := by
    refine ⟨?_,?_,current,?_,?_⟩
    all_goals first
    | exact (frame.natHeap _ (by simp only [List.mem_singleton];omega)).trans metadata.mode
    | exact (frame.natHeap _ (by simp only [List.mem_singleton];omega)).trans metadata.saved
    | exact (frame.natHeap _ (by simp only [List.mem_singleton];omega)).trans metadata.endpoint
    | exact (frame.natHeap _ (by simp only [List.mem_singleton];omega)).trans metadata.unit
  exact ⟨u,run,up,parent.padding frame (bits.trans parent.nativeBits),mu,frame⟩

theorem init (n B k q A F r stack depth U saved role count : ℕ)
    (x : Fin n→ℂ) (s : State)
    (pc : s.pc=P.address .paddingInit)
    (parent : Parent k q A F r stack depth s)
    (unit : s.natHeap (F-2)=some U)
    (finish : s.natReg 2865=saved) (dest : s.natReg 2854=role)
    (size : s.natReg 2855=count)
    (low : 6≤F) (bound : WordBound B s) (code : P.program.length≤B)
    (endBound : role+count≤B) :
    ∃u, BoundedRuns P.program n x B s 11 u ∧ u.pc=P.address .paddingTest ∧
      Parent k q A F r stack depth u ∧ Metadata F U saved role (role+count) u ∧
      UniformRecursivePaddingControl.Frame [F-6,F-5,F-4,F-3] s u := by
  obtain ⟨u,run,up,mode,stored,current,endpoint,frame⟩:=
    UniformRecursivePaddingControl.init_execution n B F saved role count x s pc parent.frontier
      parent.one finish dest size low bound code endBound
  have bits:=UniformRecursivePaddingFragments.init_bits n B F saved role count x s u pc
    parent.frontier parent.one finish dest size low bound code endBound run
  have ptr : u.natHeap (F-2)=some U := by
    rw [frame.natHeap _ (by simp only [List.mem_cons,List.mem_nil_iff,or_false];omega)]
    exact unit
  exact ⟨u,run,up,parent.padding frame (bits.trans parent.nativeBits),
    ⟨mode,stored,current,endpoint,ptr⟩,frame⟩

end
end ExactFourierCircuits.DFTModelSavingNativePaddingControl
