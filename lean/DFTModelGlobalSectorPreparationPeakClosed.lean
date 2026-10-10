import DFTModelGlobalSectorPreparationPeak
import DFTModelGlobalSectorPreparationSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheTraversal
noncomputable section
attribute [local irreducible] prepareAxis expand body base packing unpacking finalize program tables

theorem base_peak (i : ℕ) (axes : Tape Axis.T) : (run base (i,axes)).peak=1 := by
 simp [base,run,Code.run,Atom.run,Bill.word,Bill.one,Bill.pass,Bill.pay,
   ModelEquivalenceInterpreter.tab_peak]

theorem body_peak (h : Handler (some (Node,Tables))) (i H : ℕ) (axes : Tape Axis.T)
 (hp:(run prepareAxis (axes.look i Axis.blank)).peak≤H)
 (hc:(h (i+1,axes)).peak≤H)
 (he:(run expand ((run prepareAxis (axes.look i Axis.blank)).val,(h (i+1,axes)).val)).peak≤H)
 (hi:i+1≤H) : (body.run h (i,axes)).peak≤H := by
 simp only [body,current,next,nat,Code.run,Atom.run,NOp.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word]
 dsimp only [run] at hp he
 omega

theorem depth_peak (as : List UniformSectorPacking.Axis) (i : ℕ) (axes : Tape Axis.T)
 (read:∀l,l<as.length→axes.look (i+l) Axis.blank=(as.map encodeAxis)[l]?.getD Axis.blank) :
 (depthRun (run base) body.run as.length (i,axes)).peak≤
 6*(UniformSectorPacking.radices as).prod+i+as.length+1 := by
 induction as generalizing i with
 | nil=>simp only [List.length_nil];rw [depthRun];change max (run base (i,axes)).peak 0≤_;rw [base_peak];simp
 | cons a as ih=>
  have h0:=read 0 (by simp)
  simp only [Nat.add_zero,List.map_cons,List.getElem?_cons_zero,Option.getD_some] at h0
  have ht:∀l,l<as.length→axes.look ((i+1)+l) Axis.blank=(as.map encodeAxis)[l]?.getD Axis.blank := by
   intro l hl
   have hh:=read (l+1) (by simp;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have hc:=ih (i+1) ht
  have hp:=prepareAxis_peak a
  have he:=expand_peak _ _ _ _ (prepared_axis_bound a) (native_tables_bound as)
  have hv:=native_volume_pos as
  have hr:=a.radix_two
  have htvalue:(depthRun (run base) body.run as.length (i+1,axes)).val=nativeTables as := by
   rw [depth_value]
   have hlen:(as.map encodeAxis).length=as.length:=List.length_map encodeAxis
   rw [←hlen,tableValue_model (as.map encodeAxis) (i+1) axes (by simpa using ht),listTables_native]
  have hproduct:=Nat.mul_le_mul_right (UniformSectorPacking.radices as).prod hr
  have hlocal:a.widths.sum≤a.widths.sum*(UniformSectorPacking.radices as).prod:=by nlinarith
  have htail:(UniformSectorPacking.radices as).prod≤a.widths.sum*(UniformSectorPacking.radices as).prod:=by nlinarith
  change max (body.run _ (i,axes)).peak (as.length+1)≤_
  apply max_le
  · apply body_peak
    · rw [h0];exact le_trans hp (by change a.widths.sum+1≤6*(a.widths.sum*(UniformSectorPacking.radices as).prod)+i+(as.length+1)+1;omega)
    · exact le_trans hc (by change 6*(UniformSectorPacking.radices as).prod+(i+1)+as.length+1≤6*(a.widths.sum*(UniformSectorPacking.radices as).prod)+i+(as.length+1)+1;omega)
    · rw [h0,prepareAxis_value,htvalue]
      exact le_trans he (by change 3*(a.widths.sum*(UniformSectorPacking.radices as).prod)+a.widths.sum+(UniformSectorPacking.radices as).prod+1≤6*(a.widths.sum*(UniformSectorPacking.radices as).prod)+i+(as.length+1)+1;omega)
    · change i+1≤6*(a.widths.sum*(UniformSectorPacking.radices as).prod)+i+(as.length+1)+1
      omega
  · change as.length+1≤6*(a.widths.sum*(UniformSectorPacking.radices as).prod)+i+(as.length+1)+1
    omega

theorem tables_peak (as : List UniformSectorPacking.Axis) :
 (run tables (ofList (as.map encodeAxis))).peak≤6*(UniformSectorPacking.radices as).prod+as.length+1 := by
 have hd:=depth_peak as 0 (ofList (as.map encodeAxis)) (by intro l hl;rw [Nat.zero_add,ofList_look])
 have hlen:(ofList (as.map encodeAxis)).len=as.length:=by simp [ofList]
 simp only [tables,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 norm_num
 rw [hlen]
 constructor
 · exact (by simpa only [Nat.add_zero] using hd)
 · omega

theorem packing_peak (t : Tables.T) (V : ℕ) (bound:TablesBound t V) :
 (run packing t).peak≤2*V := by
 have hb:=bound.addresses
 have hv:=bound.volume
 have hs:(Bill.sow t.1 t.2.2.len 0 (fun j=>Code.run (.fork originalAddress packedAddress) () (t,j))).peak≤2*V := by
  rw [DFTModelCRT.sow_peak]
  refine max_le (le_trans hv (by omega)) (max_le (le_trans hb (by omega)) ?_)
  apply Finset.sup_le
  intro j _
  rw [emitPacking_run]
  rcases bound.address j with ⟨ha0,ha1,ha2,ha3⟩
  change (addressPair t j).1≤_
  dsimp only [addressPair]
  exact le_trans (Nat.add_le_add ha1 ha2) (by omega)
 simp only [packing,outputVolume,outputCount,run,Code.run,Atom.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank] at ⊢ hs
 norm_num at ⊢ hs
 omega

theorem unpacking_peak (t : Tables.T) (V : ℕ) (bound:TablesBound t V) :
 (run unpacking t).peak≤2*V := by
 have hb:=bound.addresses
 have hv:=bound.volume
 have hs:(Bill.sow t.1 t.2.2.len 0 (fun j=>Code.run (.fork packedAddress originalAddress) () (t,j))).peak≤2*V := by
  rw [DFTModelCRT.sow_peak]
  refine max_le (le_trans hv (by omega)) (max_le (le_trans hb (by omega)) ?_)
  apply Finset.sup_le
  intro j _
  rw [emitUnpacking_run]
  rcases bound.address j with ⟨ha0,ha1,ha2,ha3⟩
  change (addressPair t j).1≤_
  dsimp only [addressPair]
  exact le_trans (Nat.add_le_add ha1 ha2) (by omega)
 simp only [unpacking,outputVolume,outputCount,run,Code.run,Atom.run,
   Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank] at ⊢ hs
 norm_num at ⊢ hs
 omega

theorem finalize_peak (t : Tables.T) (V : ℕ) (bound:TablesBound t V) :
 (run finalize t).peak≤2*V := by
 have hp:=packing_peak t V bound
 have hu:=unpacking_peak t V bound
 have hb:=bound.blocks
 simp only [finalize,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
   max_le_iff,zero_le]
 dsimp only [run] at hp hu
 simpa only [true_and,and_true] using And.intro hp hu

theorem program_peak (as : List UniformSectorPacking.Axis) :
 (run program (ofList (as.map encodeAxis))).peak≤6*(UniformSectorPacking.radices as).prod+as.length+1 := by
 have ht:=tables_peak as
 have hf:=finalize_peak _ _ (native_tables_bound as)
 simp only [program,run,Code.run,Bill.pass,Bill.pay,max_zero]
 change max (run tables (ofList (as.map encodeAxis))).peak
   (run finalize (run tables (ofList (as.map encodeAxis))).val).peak≤_
 rw [tables_native]
 exact max_le ht (le_trans hf (by omega))

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
