import DFTModelRecursiveYSource
import DFTModelRecursiveYPeak

set_option autoImplicit false

/-! Correspondence with one genuine opcode3 row of the actual 197-cell Y
machine. The baseline is a second source witness; the target executes once.
The finite descriptor/header loop is an explicit remaining caller boundary. -/
namespace ExactFourierCircuits.DFTModelRecursiveYDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
open UniformFixedNetworkScheduleMachine (Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformResidualNativeTranslationMachine (volume)
noncomputable section

attribute [local irreducible] program

theorem raw_row {R m : ℕ} (P : ℕ) (d : UniformNativeYRecordMachine.Direction R m)
    (raw : Tape ℕ) (s : State) (row : Printed P d.data s)
    (words : ∀a v,s.natHeap a=some v→ raw.look a 0=v) :
    raw.look P 0=d.role.val ∧
      ∀i:Fin m,raw.look (P+1+i.val) 0=(d.vector i).val := by
  refine ⟨words _ _ ?_,?_⟩
  · simpa [UniformNativeYRecordMachine.Direction.data] using row 0 (by
      simp [UniformNativeYRecordMachine.Direction.data])
  · intro i
    apply words
    have h:=row (i.val+1) (by
      rw [UniformNativeYRecordMachine.Direction.data_length];omega)
    simpa [UniformNativeYRecordMachine.Direction.data,
      UniformFixedNetworkScheduleMachine.bitWords,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using h

theorem header_match {q m r k A E T P i count : ℕ} {s s0 : State}
    (h : UniformNativeYRecordMachine.Header q m r k A E T P i count s)
    (same : StateMatch s s0) : UniformNativeYRecordMachine.Header q m r k A E T P i count s0 :=
  ⟨same.pc.trans h.pc,by rw [same.natReg];exact h.base,
    by rw [same.natReg];exact h.volume,by rw [same.natReg];exact h.q,
    by rw [same.natReg];exact h.width,by rw [same.natReg];exact h.buffer,
    by rw [same.natReg];exact h.table,by rw [same.natReg];exact h.cursor,
    by rw [same.natReg];exact h.index,by rw [same.natReg];exact h.count,
    by rw [same.natReg];exact h.one,by rw [same.natReg];exact h.stride,
    by rw [same.natReg];exact h.rest⟩

/-- No ready permutation or output is assumed: the raw printed row drives
the source iteration and the charged typed table/mask/gather computation. -/
theorem actual_round {R m : ℕ} (q r k A E T P i count B n : ℕ) (x : Fin n→ℂ)
    (I : ℂ) (d : UniformNativeYRecordMachine.Direction R m)
    (f f0 : Fin R→Fin (UniformResidualNativeTranslationMachine.volume k)→Scalar)
    (raw : Tape ℕ) (v : Tape DFTModelAffine.Tagged.T) (s s0 : State)
    (h : UniformNativeYRecordMachine.Header q m r k A E T P i count s)
    (same : StateMatch s s0)
    (shape : k=q*m+r) (qp : 1≤q) (padded : 2^(q*(m+r))≤B) (yes : i<count)
    (row : Printed P d.data s) (words : ∀a z,s.natHeap a=some z→ raw.look a 0=z)
    (source : Present A R (UniformResidualNativeTranslationMachine.volume k) f s)
    (baseline : Present A R (UniformResidualNativeTranslationMachine.volume k) f0 s0)
    (len : v.len=R*2^k)
    (encoded : ∀b j,v.look (b.val*2^k+j.val) (0,(0,0))=
      DFTModelAffine.encodePaired (f b j) (f0 b j))
    (bound : WordBound B s) (code : 197≤B) (rowEnd : P+m+1≤T)
    (separate : A+R*2^k≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+2^k≤B) :
    ∃u u0,
      BoundedRuns UniformNativeYRecordMachine.program n x B s
        (UniformNativePreparedYTranslationMachine.runtime q m r k+11) u ∧
      BoundedRuns UniformNativeYRecordMachine.program n (fun _=>0) B s0
        (UniformNativePreparedYTranslationMachine.runtime q m r k+11) u0 ∧
      UniformNativeYRecordMachine.Frame q A (R*2^k) E T m k s u ∧
      UniformNativeYRecordMachine.Frame q A (R*2^k) E T m k s0 u0 ∧
      (∀(b : Fin R) (j : Fin (UniformResidualNativeTranslationMachine.volume k)),∃z z0,u.scalarHeap (A+b.val*2^k+j.val)=some z ∧
        u0.scalarHeap (A+b.val*2^k+j.val)=some z0 ∧
        (run (program R) (input q m r P k I raw v)).val.2.look
          (b.val*2^k+j.val) (0,(0,0))=DFTModelAffine.encodePaired z z0 ∧
        ((run (program R) (input q m r P k I raw v)).val.2.look
          (b.val*2^k+j.val) (0,(0,0))).2.1=z0.value) ∧
      (run (program R) (input q m r P k I raw v)).valid ∧
      (run (program R) (input q m r P k I raw v)).work≤
        16*(R+1)*(UniformNativePreparedYTranslationMachine.runtime q m r k+11) ∧
      (run (program R) (input q m r P k I raw v)).peak≤4*B+2 := by
  have positive:0<R:=by have hh:=d.role.isLt;omega
  obtain ⟨roleSource,bits⟩:=raw_row P d raw s row words
  obtain ⟨u,runU,_,values,frame⟩:=UniformNativeYRecordMachine.round_execution q m r k A E T P i count B n x
    d f s h shape qp padded yes row source bound code rowEnd separate tableEnd extent
  have row0 : Printed P d.data s0 := by
    intro j hj;rw [same.natHeap];exact row j hj
  obtain ⟨u0,run0,_,values0,frame0⟩:=UniformNativeYRecordMachine.round_execution q m r k A E T P i count B n
    (fun _=>0) d f0 s0 (header_match h same) shape qp padded yes row0 baseline
    (same.wordBound bound) code rowEnd separate tableEnd extent
  refine ⟨u,u0,runU,run0,frame,frame0,?_,program_valid R _,?_,?_⟩
  · intro b j
    refine ⟨UniformNativeYRecordMachine.values q m k d f b j,
      UniformNativeYRecordMachine.values q m k d f0 b j,values b j,values0 b j,?_,?_⟩
    · exact lookup_paired q r P k I raw v d f f0 positive len shape qp roleSource bits encoded b j
    · rw [lookup_paired q r P k I raw v d f f0 positive len shape qp roleSource bits encoded b j]
      rfl
  · exact (work_source_bound R q m r P k I raw v len).trans
      (Nat.mul_le_mul_left _ (by omega))
  · have bankFit : R*2^k≤B :=
      (Nat.le_add_left (R*2^k) A).trans (separate.trans
        ((Nat.le_add_right E (2^k)).trans extent))
    have rowFit : P+m+1≤B := rowEnd.trans
      ((Nat.le_add_right T (2^q*2^q)).trans tableEnd)
    have tableFit : 2^q*2^q≤B :=
      (Nat.le_add_left (2^q*2^q) T).trans tableEnd
    exact program_peak q r P k B I raw v d positive len shape qp roleSource bits
      bankFit rowFit padded tableFit

end
end ExactFourierCircuits.DFTModelRecursiveYDirection
