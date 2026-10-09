import DFTModelRecursiveYDirection

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelRecursiveYDirection
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

attribute [local irreducible] program moved ready
  DFTModelRecursiveYMovement.program DFTModelRecursiveYMask.program DFTModelResidualTable.program

theorem lookup_paired {R m : ℕ} (q r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) (d : UniformNativeYRecordMachine.Direction R m)
    (f f0 : Fin R→Fin (UniformResidualNativeTranslationMachine.volume k)→Scalar)
    (positive : 0 < R) (len : v.len=R*2^k) (shape : k=q*m+r) (qp : 1 ≤ q)
    (roleSource : raw.look A 0=d.role.val)
    (bits : ∀i:Fin m,raw.look (A+1+i.val) 0=(d.vector i).val)
    (encoded : ∀ b j,v.look (b.val*2^k+j.val) (0,(0,0))=
      DFTModelAffine.encodePaired (f b j) (f0 b j))
    (b : Fin R) (j : Fin (UniformResidualNativeTranslationMachine.volume k)) :
    (run (program R) (input q m r A k I raw v)).val.2.look (b.val*2^k+j.val) (0,(0,0))=
      DFTModelAffine.encodePaired (UniformNativeYRecordMachine.values q m k d f b j)
        (UniformNativeYRecordMachine.values q m k d f0 b j) := by
  rw [program_value q r A k I raw v d positive len shape qp roleSource bits]
  have jbound:j.val<2^k:=j.isLt
  have addr:b.val*2^k+j.val<v.len := by
    rw [len]
    have h:=Nat.mul_le_mul_right (2^k) (Nat.succ_le_iff.mpr b.isLt)
    dsimp only [Nat.succ_eq_add_one] at h
    rw [Nat.add_mul,Nat.one_mul] at h
    omega
  have maskSmall : (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val<2^k :=
    (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  change (DFTModelRecursiveYMovement.data DFTModelAffine.Tagged (2^k) d.role.val
    (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val v).look
      (b.val*2^k+j.val) (0,(0,0))=_
  rw [Tape.look_of_lt _ _ (show b.val*2^k+j.val <
    (DFTModelRecursiveYMovement.data DFTModelAffine.Tagged (2^k) d.role.val
      (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val v).len from addr)]
  change v.look (DFTModelRecursiveYMovement.index (2^k) d.role.val
    (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val
    (b.val*2^k+j.val)) (0,(0,0))=_
  rw [DFTModelRecursiveYMovement.index_role _ _ _ _ _ (Nat.two_pow_pos _) jbound]
  by_cases eq:b=d.role
  · subst b
    simp only [ite_true]
    let partner : Fin (UniformResidualNativeTranslationMachine.volume k) :=
      ⟨j.val^^^(UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val,
        Nat.xor_lt_two_pow jbound maskSmall⟩
    rw [encoded d.role partner]
    have modEq : (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val %
        UniformResidualNativeTranslationMachine.volume k=
          (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q d.vector)).val :=
      Nat.mod_eq_of_lt maskSmall
    simp only [UniformNativeYRecordMachine.values,eq_self,ite_true,
      UniformResidualNativeTranslationMachine.translated,
      UniformResidualNativeTranslationMachine.partner,modEq,partner]
  · have ne:b.val≠d.role.val:=fun h=>eq (Fin.ext h)
    simp only [ite_eq_right ne,UniformNativeYRecordMachine.values,ite_eq_right eq]
    exact encoded b j

/-- The typed direction cost is bounded by a fixed role-dependent multiple
of the actual source child runtime, including its raw mask and table work. -/
theorem work_source_bound (R q m r A k : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape DFTModelAffine.Tagged.T) (len : v.len=R*2^k) :
    (run (program R) (input q m r A k I raw v)).work≤
      16*(R+1)*UniformNativePreparedYTranslationMachine.runtime q m r k := by
  have actual:=program_work R q m r A k I raw v
  rw [len] at actual
  have table:=DFTModelResidualTable.work_preserved q
  change (run DFTModelResidualTable.program q).work≤
    8*UniformNativePreparedYTranslationMachine.tableCost q at table
  have lower : 4*q≤UniformNativePreparedYTranslationMachine.tableCost q := by
    unfold UniformNativePreparedYTranslationMachine.tableCost
    omega
  have kernel : (120*(m+r)+154)*(R*2^k)≤
      10*R*((17*(m+r)+25)*2^k) := by nlinarith
  unfold UniformNativePreparedYTranslationMachine.runtime
  change (run (program R) (input q m r A k I raw v)).work≤
    16*(R+1)*(UniformNativePreparedYTranslationMachine.tableCost q+9*(q*m)+
      (17*(m+r)+25)*2^k+31)
  have tableCoe := Nat.mul_le_mul_right (UniformNativePreparedYTranslationMachine.tableCost q)
    (show 10≤16*(R+1) by omega)
  have maskCoe := Nat.mul_le_mul_right (q*m)
    (show 73≤16*(R+1)*9 by omega)
  have kernelCoe := Nat.mul_le_mul_right ((17*(m+r)+25)*2^k)
    (show 10*R≤16*(R+1) by omega)
  have constantCoe : 130≤16*(R+1)*31 := by omega
  nlinarith

end
end ExactFourierCircuits.DFTModelRecursiveYDirection
