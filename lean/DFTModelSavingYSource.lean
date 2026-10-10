import DFTModelSavingYBounds

set_option autoImplicit false

/-! Exact full-record correspondence to the actual native opcode3 program.
The single typed run carries both the actual and zero-source executions. -/
namespace ExactFourierCircuits.DFTModelSavingY
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelAdmissibilityControl
open UniformNativeYRecordMachine (Direction actions record)
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformResidualNativeTranslationMachine (volume)
open DFTModelRecursiveScalarSource (paired paired_lookup)
noncomputable section

theorem actual_execution {R : ℕ} (q m r k A E T P B n : ℕ) (x : Fin n → ℂ)
    (ds : List (Direction R m)) (f f0 : Fin R → Fin (volume k) → Scalar)
    (s s0 : State) (I : ℂ) (raw : Tape ℕ)
    (positive : 0<R) (same : StateMatch s s0)
    (pc : s.pc=0) (ptr : s.natReg 2850=P) (base : s.natReg 3300=A)
    (native : s.natReg 5300=k) (restHeader : s.natReg 5301=r)
    (shape : k=q*m+r) (qp : 1≤q) (padded : 2^(q*(m+r))≤B)
    (buffer : s.natReg 3364=E) (table : s.natReg 3389=T)
    (bank : Printed P (record q m ds).data s)
    (copied : ∀ j,j<(record q m ds).data.length →
      ∀ z,s.natHeap (P+j)=some z → raw.look j 0=z)
    (data : Present A R (volume k) f s) (baseline : Present A R (volume k) f0 s0)
    (wb : WordBound B s) (code : 197≤B)
    (sourceBeforeTable : P+(record q m ds).data.length≤T)
    (separate : A+R*volume k≤E) (tableEnd : T+2^q*2^q≤B)
    (extent : E+volume k≤B) (width : m+1≤B) :
    ∃ u u0,
      BoundedExecution UniformNativeYRecordMachine.program n x B s
        (UniformNativeYRecordMachine.runtime q m r k ds.length) u ∧
      BoundedExecution UniformNativeYRecordMachine.program n (fun _ => 0) B s0
        (UniformNativeYRecordMachine.runtime q m r k ds.length) u0 ∧
      StateMatch u u0 ∧
      UniformNativeYRecordMachine.FullFrame q A (R*volume k) E T m k s u ∧
      UniformNativeYRecordMachine.FullFrame q A (R*volume k) E T m k s0 u0 ∧
      u.natReg 2850=P+(record q m ds).data.length ∧
      u0.natReg 2850=P+(record q m ds).data.length ∧
      (run (program R) (input r k I raw (paired f f0))).val=
        ((k,I),paired (actions q m k ds f) (actions q m k ds f0)) ∧
      (∀ (b : Fin R) (j : Fin (volume k)),∃ a a0,
        u.scalarHeap (A+b.val*volume k+j.val)=some a ∧
        u0.scalarHeap (A+b.val*volume k+j.val)=some a0 ∧
        (run (program R) (input r k I raw (paired f f0))).val.2.look
          (b.val*volume k+j.val) Tagged.blank=encodePaired a a0) ∧
      (run (program R) (input r k I raw (paired f f0))).valid ∧
      (run (program R) (input r k I raw (paired f f0))).work≤
        32*(R+1)*UniformNativeYRecordMachine.runtime q m r k ds.length ∧
      (run (program R) (input r k I raw (paired f f0))).peak≤4*B+2 := by
  have source:=RecordSource.of_printed q P ds raw s bank copied
  obtain ⟨u,exec,out,cursor,frame⟩:=UniformNativeYRecordMachine.execution
    q m r k A E T P B n x ds f s pc ptr base native restHeader shape qp padded buffer table
    bank data wb code sourceBeforeTable separate tableEnd extent width
  have bank0 : Printed P (record q m ds).data s0 := by
    intro j hj
    rw [same.natHeap]
    exact bank j hj
  obtain ⟨u0,exec0,out0,cursor0,frame0⟩:=UniformNativeYRecordMachine.execution
    q m r k A E T P B n (fun _ => 0) ds f0 s0 (same.pc.trans pc)
    (by rw [same.natReg];exact ptr) (by rw [same.natReg];exact base)
    (by rw [same.natReg];exact native) (by rw [same.natReg];exact restHeader)
    shape qp padded (by rw [same.natReg];exact buffer) (by rw [same.natReg];exact table)
    bank0 baseline (same.wordBound wb) code sourceBeforeTable separate tableEnd extent width
  obtain ⟨u0',exec0',matched⟩:=boundedExecution_match (y:=fun _ => 0) exec same
  have eq : u0'=u0 := (exec0'.executes.deterministic exec0.executes).2
  subst u0'
  have value:=program_value q r k I raw ds source f f0 positive shape qp
  refine ⟨u,u0,exec,exec0,matched,frame,frame0,cursor,cursor0,value,?_,
    program_valid R _,program_work q r k I raw ds source f f0 positive shape qp,?_⟩
  · intro b j
    refine ⟨_,_,out b j,out0 b j,?_⟩
    rw [value]
    exact paired_lookup _ _ b j
  · apply program_peak q r k B I raw ds source f f0 positive shape qp
    · change R*volume k≤B
      omega
    · rw [←UniformNativeYRecordMachine.record_length q m ds]
      omega
    · exact padded
    · omega

end
end ExactFourierCircuits.DFTModelSavingY
