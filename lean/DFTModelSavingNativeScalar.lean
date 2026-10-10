import DFTModelSavingNativeControl
import DFTModelSavingShape
import UniformRecursiveNativeTypedRecords

set_option autoImplicit false

/-! The scalar record of the actual recursive RAM loop, including header
dispatch and return to that loop. Exact returned Scalar flags are retained. -/
namespace ExactFourierCircuits.DFTModelSavingNativeScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAffine DFTModelClockControl DFTModelAdmissibilityControl
open DFTModelSavingNativeControl
open DFTModelRecursiveScalarSource (paired)
open UniformFixedNetworkScheduleMachine (Printed Record)
open UniformFixedNetworkShearChildMachine (Present shearValues)
open UniformRecursiveResidualEdge (Parent)
noncomputable section

attribute [local irreducible] DFTModelSavingRecords.residual DFTModelSavingRecords.padding
  DFTModelSavingScalar.program DFTModelSavingY.program DFTModelRecursiveExchange.program

lemma ifz_value {s t : Ty} (test : Code false ChildPort s w)
    (f g : Code false ChildPort s t) (h : Handler ChildPort) (x : s.T) :
    ((Code.ifz test f g).run h x).val=
      if (test.run h x).val=0 then (f.run h x).val else (g.run h x).val := by
  change (if (test.run h x).val=0 then f.run h x else g.run h x).val=_
  split_ifs <;> rfl

lemma dispatch_value (R rest : ℕ) (h : Handler ChildPort) (raw : Tape ℕ) (node : Node.T)
    (opcode : raw.look 0 0=1) :
    ((DFTModelSavingRecords.dispatch R).run h (rest,(raw,node))).val=
      (run (DFTModelSavingScalar.program R) (raw,node)).val := by
  unfold DFTModelSavingRecords.dispatch
  rw [ifz_value]
  change (if raw.look 0 0=0 then _ else _)=_
  rw [opcode,ite_eq_right (by decide)]
  rw [ifz_value]
  change (if raw.look 0 0-1=0 then _ else _)=_
  rw [opcode,ite_eq_left (by decide),DFTModelClockBatch.code_comp_value]
  rfl

theorem execution (q w k A T F tapeEnd rest stack depth B n : ℕ) (x : Fin n→ℂ)
    (d src : Fin UniformFixedNetwork.W) (ne : d≠src) (c : Fin 5)
    (s s0 : State) (f f0 : Fin UniformFixedNetwork.W→Fin (2^k)→Scalar)
    (I : ℂ) (h : Handler ChildPort) (same : StateMatch s s0)
    (pc : s.pc=UniformRecursiveSavingProgram.address .loop)
    (parent : Parent k q A F T rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (live : T<tapeEnd)
    (printed : Printed T (UniformNativeScalarRecordMachine.shearRecord q w d src c).data s)
    (data : Present A UniformFixedNetwork.W (2^k) f s)
    (baseline : Present A UniformFixedNetwork.W (2^k) f0 s0)
    (bound : WordBound B s) (code : UniformRecursiveSavingProgram.program.length≤B)
    (tableEnd : T+8≤B) (width : w+1≤B) (extent : A+UniformFixedNetwork.W*2^k≤B) :
    ∃u u0,
      BoundedRuns UniformRecursiveSavingProgram.program n x B s (10*2^k+4*k+c.val+102) u ∧
      BoundedRuns UniformRecursiveSavingProgram.program n (fun _=>0) B s0
        (10*2^k+4*k+c.val+102) u0 ∧
      StateMatch u u0 ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
      u0.pc=UniformRecursiveSavingProgram.address .loop ∧
      Parent k q A F (T+8) rest stack depth u ∧
      Parent k q A F (T+8) rest stack depth u0 ∧
      Present A UniformFixedNetwork.W (2^k) (shearValues d src (UniformFixedCoefficientCodec.decode c) f) u ∧
      Present A UniformFixedNetwork.W (2^k) (shearValues d src (UniformFixedCoefficientCodec.decode c) f0) u0 ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^k) F s u ∧
      UniformRecursiveNativeTypedRecords.Frame A (2^k) F s0 u0 ∧
      (∀z,u.natHeap z=s.natHeap z ∧ u0.natHeap z=s0.natHeap z) ∧
      ((DFTModelSavingRecords.dispatch UniformFixedNetwork.W).run h
        (rest,(DFTModelCacheRecords.dataTape
          (UniformNativeScalarRecordMachine.shearRecord q w d src c).data,((k,I),paired f f0)))).val=
        ((k,I),paired (shearValues d src (UniformFixedCoefficientCodec.decode c) f)
          (shearValues d src (UniformFixedCoefficientCodec.decode c) f0)) := by
  obtain ⟨u,t,actual,up,out,cursor,control,frame⟩:=
    UniformRecursiveNativeRecords.scalar_loop q w k A T F tapeEnd B n x d src ne c f s
      pc parent.cursor parent.nativeBase parent.nativeBits parent.frontier parent.one metadata live
      printed data bound code tableEnd width extent
  have parent0 : Parent k q A F T rest stack depth s0 := by
    rcases parent with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o⟩
    constructor <;> rw [same.natReg] <;> assumption
  have printed0 : Printed T (UniformNativeScalarRecordMachine.shearRecord q w d src c).data s0 := by
    intro j hj;rw [same.natHeap];exact printed j hj
  obtain ⟨u0,t0,actual0,up0,out0,cursor0,control0,frame0⟩:=
    UniformRecursiveNativeRecords.scalar_loop q w k A T F tapeEnd B n (fun _=>0) d src ne c f0 s0
      (same.pc.trans pc) parent0.cursor parent0.nativeBase parent0.nativeBits parent0.frontier parent0.one
      (by rw [same.natHeap];exact metadata) live printed0 baseline (same.wordBound bound)
      code tableEnd width extent
  let raw:=DFTModelCacheRecords.dataTape (UniformNativeScalarRecordMachine.shearRecord q w d src c).data
  have word (j : ℕ) (hj : j<8) : raw.look j 0=
      (UniformNativeScalarRecordMachine.shearRecord q w d src c).data[j]'(by
        simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using hj) :=
    dataTape_lookup _ j (by simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using hj)
  have opcode : raw.look 0 0=1 := by simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using word 0 (by decide)
  have dest : raw.look 3 0=d.val := by simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using word 3 (by decide)
  have source : raw.look 4 0=src.val := by simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using word 4 (by decide)
  have coeff : raw.look 7 0=c.val := by simpa [UniformNativeScalarRecordMachine.shearRecord,Record.data,Record.header] using word 7 (by decide)
  refine ⟨u,u0,actual,actual0,paired_runs actual actual0 same,up,up0,
    UniformRecursiveNativeParent.scalar_parent parent cursor control frame,
    UniformRecursiveNativeParent.scalar_parent parent0 cursor0 control0 frame0,out,out0,
    UniformRecursiveNativeTypedRecords.scalar_frame control frame,
    UniformRecursiveNativeTypedRecords.scalar_frame control0 frame0,?_,?_⟩
  · intro z
    exact ⟨congrFun (frame.natHeap.trans control.natHeap) z,
      congrFun (frame0.natHeap.trans control0.natHeap) z⟩
  · change ((DFTModelSavingRecords.dispatch UniformFixedNetwork.W).run h
      (rest,(raw,((k,I),paired f f0)))).val=_
    rw [dispatch_value _ _ _ _ _ opcode]
    apply Prod.ext
    · exact (DFTModelSavingShape.scalar_preserves _ raw ((k,I),paired f f0)).1
    · apply DFTModelSavingY.paired_ext
      · exact (DFTModelSavingShape.scalar_preserves _ raw ((k,I),paired f f0)).2
      · intro i j
        exact DFTModelSavingScalar.program_lookup d src c (by positivity) f f0 k I raw dest source coeff i j

end
end ExactFourierCircuits.DFTModelSavingNativeScalar
