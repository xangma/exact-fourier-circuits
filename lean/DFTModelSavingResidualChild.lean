import DFTModelSavingResidualGeometry
import UniformBinaryTensorCoordinates

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualChild
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup DFTModelSavingResidual
open DFTModelClockBatch (sliced)
open scoped BigOperators
noncomputable section
attribute [local irreducible] UniformBatching.width DFTModelSavingResidualBatch.program

/-- Internal smaller-child induction property. It covers both channels in one
actual child bill; it is not an input certificate of the final closed program. -/
def Channels (h:Handler Port) (q:ℕ) (I:ℂ) (G:ℕ) (bank:Tape Tagged.T) : Prop :=
  ∀g<G,∀j:Fin (UniformBatching.width*2^q),
    ((h ((q,I),sliced (UniformBatching.width*2^q) g bank Tagged.blank)).val.look j.val Tagged.blank).2=
      ((UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
        (fun s=>(sliced (UniformBatching.width*2^q) g bank Tagged.blank).look
          ((j.val/2^q)*2^q+s.val) Tagged.blank |>.2.1) ⟨j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
       (UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
        (fun s=>(sliced (UniformBatching.width*2^q) g bank Tagged.blank).look
          ((j.val/2^q)*2^q+s.val) Tagged.blank |>.2.2) ⟨j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩)

theorem block_base (W N j:ℕ) :
  (j/(W*N))*(W*N)+(j%(W*N)/N)*N=(j/N)*N := by
  have div:j/(W*N)=j/N/W:=by rw [Nat.div_div_eq_div_mul,Nat.mul_comm N W]
  rw [Nat.mod_mul_left_div_self,div]
  have decomp:=congrArg (fun z:ℕ=>z*N) (Nat.div_add_mod (j/N) W)
  nlinarith

theorem slice_lookup (q g j:ℕ) (bank:Tape Tagged.T) (live:j<UniformBatching.width*2^q) :
  (sliced (UniformBatching.width*2^q) g bank Tagged.blank).look j Tagged.blank=
    bank.look (g*(UniformBatching.width*2^q)+j) Tagged.blank := by
  simp only [sliced,Tape.look,Tape.tab,live,↓reduceDIte]

/-- Exact physical C^q action of all actual complete-W calls, for each of the
two affine channels. Group indexing is proved to retain the same native fiber. -/
theorem batch_channels (h:Handler Port) (q:ℕ) (I:ℂ) (G:ℕ) (bank:Tape Tagged.T)
  (ih:Channels h q I G bank) (j:Fin (G*(UniformBatching.width*2^q))) :
  ((Code.run (DFTModelSavingResidualBatch.program Params Tagged) h
      ((q,I),(G,(UniformBatching.width*2^q,bank)))).val.look j.val Tagged.blank).2=
    ((UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
      (fun s=>bank.look ((j.val/2^q)*2^q+s.val) Tagged.blank |>.2.1)
      ⟨j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
     (UniformBinaryTensorCoordinates.physicalMatrix q).mulVec
      (fun s=>bank.look ((j.val/2^q)*2^q+s.val) Tagged.blank |>.2.2)
      ⟨j.val%2^q,Nat.mod_lt _ (Nat.two_pow_pos _)⟩) := by
  let N:=2^q
  let T:=UniformBatching.width*N
  have np:0<N:=Nat.two_pow_pos _
  have wp:0<UniformBatching.width:=by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _
  have tp:0<T:=Nat.mul_pos wp np
  have group:j.val/T<G:=Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using j.isLt)
  have remainder:j.val%T<T:=Nat.mod_lt _ tp
  rw [DFTModelSavingResidualBatch.lookup]
  have child:=ih (j.val/T) group ⟨j.val%T,remainder⟩
  rw [child]
  have mod:(j.val%T)%N=j.val%N:=by
    apply Nat.mod_mod_of_dvd
    exact ⟨UniformBatching.width,Nat.mul_comm _ _⟩
  have bas:=block_base UniformBatching.width N j.val
  change j.val/T*T+(j.val%T)/N*N=j.val/N*N at bas
  have inputs:∀s:Fin N,(sliced T (j.val/T) bank Tagged.blank).look
      (((j.val%T)/N)*N+s.val) Tagged.blank=bank.look ((j.val/N)*N+s.val) Tagged.blank:=by
    intro s
    have within:((j.val%T)/N)*N+s.val<T:=by
      have div:(j.val%T)/N<UniformBatching.width:=Nat.div_lt_of_lt_mul
        (by simpa only [T,N,Nat.mul_comm] using remainder)
      have mult:=Nat.mul_le_mul_right N (show (j.val%T)/N+1≤UniformBatching.width by omega)
      have sl:=s.isLt
      change ((j.val%T)/N)*N+s.val<T
      change ((j.val%T)/N+1)*N≤T at mult
      nlinarith
    rw [slice_lookup q (j.val/T) _ bank within]
    congr 1
    change j.val/T*T+((j.val%T)/N*N+s.val)=_
    omega
  dsimp only [N,T] at inputs mod ⊢
  simp only [inputs,mod]

end
end ExactFourierCircuits.DFTModelSavingResidualChild
