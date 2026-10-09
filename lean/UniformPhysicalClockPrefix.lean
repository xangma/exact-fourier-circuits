import UniformPhysicalSynchronizedSchedule
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalClockPrefix
open UniformSynchronizedLayers
noncomputable section

def prefixProduct (n H:ℕ) (length:∀i,(localSchedules n i).length≤H) (t:ℕ):
 Matrix (Fin (UniformInitialPreparation.len n)) (Fin (UniformInitialPreparation.len n)) ℂ:=
 ((List.ofFn (UniformPhysicalSynchronizedSchedule.slot n H length)).take t).reverse.prod

lemma zero (n H:ℕ) (length:∀i,(localSchedules n i).length≤H):prefixProduct n H length 0=1:=by
 simp only[prefixProduct,List.take_zero,List.reverse_nil,List.prod_nil]

lemma step (n H:ℕ) (length:∀i,(localSchedules n i).length≤H) (t:Fin H):
 prefixProduct n H length (t.val+1)=UniformPhysicalSynchronizedSchedule.slot n H length t*prefixProduct n H length t.val:=by
 unfold prefixProduct
 rw[List.take_succ_eq_append_getElem (by simpa only[List.length_ofFn] using t.isLt)]
 rw[List.reverse_append,List.reverse_singleton,List.prod_append,List.prod_singleton,List.getElem_ofFn]

lemma final (n H:ℕ) (length:∀i,(localSchedules n i).length≤H):
 prefixProduct n H length H=UniformPhysicalSynchronizedSchedule.fourier n:=by
 unfold prefixProduct
 rw[List.take_of_length_le (by simp only[List.length_ofFn];exact le_rfl)]
 exact UniformPhysicalSynchronizedSchedule.product n H length

lemma step_values (n H:ℕ) (length:∀i,(localSchedules n i).length≤H) (t:Fin H)
 (v:Fin (UniformInitialPreparation.len n)→ℂ):
 (UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec ((prefixProduct n H length t.val).mulVec v)=
 (prefixProduct n H length (t.val+1)).mulVec v:=by
 rw[step,Matrix.mulVec_mulVec]

/-- The finite numerical invariant used by the actual clock loop has this
unique full physical Fourier endpoint, including actual identity padding. -/
theorem endpoint (n H:ℕ) (length:∀i,(localSchedules n i).length≤H)
 (v:Fin (UniformInitialPreparation.len n)→ℂ)
 (values:ℕ→Fin (UniformInitialPreparation.len n)→ℂ)
 (initial:values 0=v)
 (advance:∀t:Fin H,values (t.val+1)=
  (UniformPhysicalSynchronizedSchedule.slot n H length t).mulVec (values t.val)):
 values H=(UniformPhysicalSynchronizedSchedule.fourier n).mulVec v:=by
 have all:∀t,t≤H→values t=(prefixProduct n H length t).mulVec v:=by
  intro t bound
  induction t with
  | zero=>rw[zero,Matrix.one_mulVec];exact initial
  | succ t ih=>
    rw[advance ⟨t,by omega⟩,ih (by omega)]
    exact step_values n H length ⟨t,by omega⟩ v
 simpa only[final] using all H (le_refl _)
end
end ExactFourierCircuits.UniformPhysicalClockPrefix
