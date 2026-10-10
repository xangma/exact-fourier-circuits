import DFTModelSavingNativeScalar

set_option autoImplicit false

/-! Both actual marker opcodes traverse the original source record and retain
the complete scalar banks. Their concrete typed branches return that same bank. -/
namespace ExactFourierCircuits.DFTModelSavingNativeMarker
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl DFTModelAdmissibilityControl
open DFTModelSavingNativeControl
open DFTModelRecursiveScalarSource (paired)
open UniformFixedNetworkScheduleMachine (Printed Record)
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
noncomputable section

attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

lemma closed_value {s t : Ty} (f : Prog false s t) (h : Handler ChildPort) (x : s.T) :
    ((Code.importClosed f).run h x).val=(run f x).val := rfl

lemma test_value (j rest : ℕ) (raw : Tape ℕ) (node : Node.T) :
    (run (DFTModelSavingRecords.opcodeTest j) (rest,(raw,node))).val=raw.look 0 0-j := rfl

lemma dispatch_value (R rest : ℕ) (h : Handler ChildPort) (raw : Tape ℕ) (node : Node.T)
    (opcode : raw.look 0 0=2 ∨ raw.look 0 0=6) :
    ((DFTModelSavingRecords.dispatch R).run h (rest,(raw,node))).val=node := by
  unfold DFTModelSavingRecords.dispatch
  rw [DFTModelSavingNativeScalar.ifz_value]
  change (if raw.look 0 0=0 then _ else _)=_
  have nonzero : raw.look 0 0≠0 := by omega
  rw [ite_eq_right nonzero,DFTModelSavingNativeScalar.ifz_value]
  change (if raw.look 0 0-1=0 then _ else _)=_
  have one : raw.look 0 0-1≠0 := by omega
  rw [ite_eq_right one,DFTModelSavingNativeScalar.ifz_value]
  change (if raw.look 0 0-2=0 then _ else _)=_
  rcases opcode with opcode|opcode
  · rw [opcode,ite_eq_left (by decide)]
    rfl
  · rw [opcode,ite_eq_right (by decide),DFTModelSavingNativeScalar.ifz_value]
    change (if raw.look 0 0-3=0 then _ else _)=_
    rw [opcode,ite_eq_right (by decide),DFTModelSavingNativeScalar.ifz_value]
    change (if raw.look 0 0-4=0 then _ else _)=_
    rw [opcode,ite_eq_right (by decide),DFTModelSavingNativeScalar.ifz_value]
    change (if raw.look 0 0-5=0 then _ else _)=_
    rw [opcode,ite_eq_right (by decide)]
    rfl

theorem execution (q k A T F tapeEnd rest stack depth B n : ℕ) (x : Fin n→ℂ)
    (r : Record) (s s0 : State) (f f0 : Fin UniformFixedNetwork.W→Fin (2^k)→Scalar)
    (I : ℂ) (h : Handler ChildPort) (same : StateMatch s s0)
    (pc : s.pc=UniformRecursiveSavingProgram.address .loop)
    (parent : Parent k q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T r.data s) (marker : r.opcode=2∨r.opcode=6)
    (good : UniformFixedNetworkOpcodeMachine.WellFormed r)
    (data : Present A UniformFixedNetwork.W (2^k) f s)
    (baseline : Present A UniformFixedNetwork.W (2^k) f0 s0)
    (bound : WordBound B s) (code : UniformRecursiveSavingProgram.program.length≤B)
    (recordEnd : T+r.data.length≤B) (width : r.width+1≤B) :
    ∃u u0,
      BoundedRuns UniformRecursiveSavingProgram.program n x B s
        (6+2*UniformFixedNetworkOpcodeMachine.headCost r+
          UniformRecursiveRecordControl.dispatchCost r.opcode) u ∧
      BoundedRuns UniformRecursiveSavingProgram.program n (fun _=>0) B s0
        (6+2*UniformFixedNetworkOpcodeMachine.headCost r+
          UniformRecursiveRecordControl.dispatchCost r.opcode) u0 ∧
      StateMatch u u0 ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
      u0.pc=UniformRecursiveSavingProgram.address .loop ∧
      Parent k q A F (T+r.data.length) rest stack depth u ∧
      Parent k q A F (T+r.data.length) rest stack depth u0 ∧
      Present A UniformFixedNetwork.W (2^k) f u ∧
      Present A UniformFixedNetwork.W (2^k) f0 u0 ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^k) F s u ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^k) F s0 u0 ∧
      ((DFTModelSavingRecords.dispatch UniformFixedNetwork.W).run h
        (rest,(DFTModelCacheRecords.dataTape r.data,((k,I),paired f f0)))).val=
        ((k,I),paired f f0) := by
  obtain ⟨u,t,actual,up,cursor,control,frame⟩:=
    UniformRecursiveNativeRecords.marker_loop T F tapeEnd B n r x s pc parent.cursor parent.frontier
      parent.one metadata live printed marker good bound code recordEnd width
  have parent0 : Parent k q A F T rest stack depth s0 := by
    rcases parent with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩
    constructor <;> rw [same.natReg] <;> assumption
  have printed0 : Printed T r.data s0 := by
    intro j hj;rw [same.natHeap];exact printed j hj
  obtain ⟨u0,t0,actual0,up0,cursor0,control0,frame0⟩:=
    UniformRecursiveNativeRecords.marker_loop T F tapeEnd B n r (fun _=>0) s0
      (same.pc.trans pc) parent0.cursor parent0.frontier parent0.one
      (by rw [same.natHeap];exact metadata) live printed0 marker good (same.wordBound bound)
      code recordEnd width
  refine ⟨u,u0,actual,actual0,paired_runs actual actual0 same,up,up0,
    UniformRecursiveNativeParent.marker_parent parent cursor control frame,
    UniformRecursiveNativeParent.marker_parent parent0 cursor0 control0 frame0,?_,?_,
    UniformRecursiveNativeTypedRecords.marker_frame control frame,
    UniformRecursiveNativeTypedRecords.marker_frame control0 frame0,?_⟩
  · intro i j;rw [frame.scalarHeap,control.scalarHeap];exact data i j
  · intro i j;rw [frame0.scalarHeap,control0.scalarHeap];exact baseline i j
  · apply dispatch_value
    have opcode : (DFTModelCacheRecords.dataTape r.data).look 0 0=r.opcode := by
      rw [dataTape_lookup _ 0 (by simp [Record.data,Record.header])]
      rfl
    simpa only [opcode] using marker

end
end ExactFourierCircuits.DFTModelSavingNativeMarker
