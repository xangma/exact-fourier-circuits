import DFTModelSectorTransposeCore

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorTranspose
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem source_index_bound (W V a T j : ℕ) (positive : 0<T)
 (fit : a+T≤V) (small : j<W*T) : (j/T)*V+a+j%T<W*V := by
 have role : j/T<W := (Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.mul_comm] using small)
 have rem : j%T<T := Nat.mod_lt _ positive
 have order := Nat.mul_le_mul_right V (show j/T+1≤W by omega)
 nlinarith

theorem source_index_injective (V a T i j : ℕ) (positive : 0<T) (fit : a+T≤V)
 (same : (i/T)*V+a+i%T=(j/T)*V+a+j%T) : i=j := by
 have vp : 0<V := by omega
 have ir : a+i%T<V := by have := Nat.mod_lt i positive; omega
 have jr : a+j%T<V := by have := Nat.mod_lt j positive; omega
 have divi : ((i/T)*V+a+i%T)/V=i/T := by
  rw [Nat.add_assoc,Nat.mul_comm (i/T) V,Nat.mul_add_div vp,Nat.div_eq_of_lt ir,Nat.add_zero]
 have divj : ((j/T)*V+a+j%T)/V=j/T := by
  rw [Nat.add_assoc,Nat.mul_comm (j/T) V,Nat.mul_add_div vp,Nat.div_eq_of_lt jr,Nat.add_zero]
 have eqrole : i/T=j/T := by rw [←divi,←divj,same]
 have eqrem : i%T=j%T := by rw [eqrole] at same; omega
 have hi := Nat.mod_add_div i T
 have hj := Nat.mod_add_div j T
 rw [eqrole,eqrem] at hi
 exact hi.symm.trans hj

theorem gather_peak (t : Ty) (W V a T : ℕ) (v : Tape t.T)
 (positive : 0<T) (fit : a+T≤V) :
 (run (gather t) ((W,(V,(a,T))),v)).peak ≤ W*V := by
 simp only [gather,run,Code.run,Bill.pass,Bill.pay]
 change max (max (run (size t) ((W,(V,(a,T))),v)).peak
  (Bill.tab (run (size t) ((W,(V,(a,T))),v)).val t.blank
   (fun j => run (gatherCell t) (((W,(V,(a,T))),v),j))).peak) 0 ≤ _
 rw [size_run,ModelEquivalenceInterpreter.tab_peak]
 have sizeFit : W*T≤W*V := Nat.mul_le_mul_left W (by omega)
 simp only [max_le_iff]
 refine ⟨⟨sizeFit,⟨sizeFit,?_⟩⟩,Nat.zero_le _⟩
 apply Finset.sup_le
 intro j hj
 rw [gatherCell_run]
 have small := Finset.mem_range.mp hj
 have ix := source_index_bound W V a T j positive fit small
 have q := (Nat.div_le_self j T).trans (Nat.le_of_lt (small.trans_le sizeFit))
 dsimp only [Bill.peak]
 omega

theorem gather_native_work (t : Ty) (W V a T : ℕ) (v : Tape t.T)
 (_positive : 0<T) :
 (run (gather t) ((W,(V,(a,T))),v)).work ≤ 9*(W*(7*T+12)+17) := by
 rw [gather_work]
 nlinarith

theorem scatter_native_work (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).work ≤ 2*(W*(7*T+12)+17) := by
 rw [scatter_work]
 nlinarith

theorem scatter_length (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).val.2.len=W*T := by
 rw [scatter_value]; rfl

theorem scatter_retained (t : Ty) (W V a T : ℕ) (v b : Tape t.T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).val.1=((W,(V,(a,T))),v) := by
 rw [scatter_value]

theorem scatter_lookup (t : Ty) (W V a T j : ℕ) (v b : Tape t.T) (small : j<W*T) :
 (run (scatter t) (((W,(V,(a,T))),v),b)).val.2.look j t.blank=b.look j t.blank := by
 rw [scatter_value]
 simp [Tape.look,Tape.tab,small]

end
end ExactFourierCircuits.DFTModelSectorTranspose
