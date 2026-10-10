import DFTModelOuterAssemblyRoleProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelOuterAssemblyRole
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine DFTModelAdmissibilityControl
noncomputable section

theorem program_lookup (W V i j : ℕ) (a : Tape ℕ) (z : Tape Datum.T) (k : Tape ℂ)
    (hi : i<W) (hj : j<V) :
    (run program (input W V a z k)).val.look (i*V+j) (0,(0,0)) =
      if i=0 then z.look j (0,(0,0))
      else if i=1 then (0,(k.look (a.look j 0) 0,0))
      else (0,(0,0)) := by
  have vp : 0<V := by omega
  have small : i*V+j<W*V := by nlinarith
  have hd : (i*V+j)/V=i := by
    rw [Nat.add_comm,Nat.add_mul_div_right j i vp,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hm : (i*V+j)%V=j := by simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  rw [program_value]
  simp only [Tape.look,Tape.tab,small,↓reduceDIte,value,hd,hm]
  rfl

theorem role_match {V : ℕ} (v v₀ : Fin V → Scalar) (k : Fin V → ℂ)
    (a : Fin V ≃ Fin V) (same : ∀j, ScalarMatch (v j) (v₀ j)) (i : ℕ) (j : Fin V) :
    ScalarMatch
      (UniformRoleInputMachine.roleValue v (fun j => UniformPairMachine.prepared (k j)) a i j)
      (UniformRoleInputMachine.roleValue v₀ (fun j => UniformPairMachine.prepared (k j)) a i j) := by
  by_cases h0 : i=0
  · simpa [UniformRoleInputMachine.roleValue,h0] using same j
  · by_cases h1 : i=1
    · simpa [UniformRoleInputMachine.roleValue,h0,h1] using
        ScalarMatch.refl (UniformPairMachine.prepared (k (a j)))
    · simpa [UniformRoleInputMachine.roleValue,h0,h1] using ScalarMatch.refl Scalar.zero

theorem paired_lookup {W V : ℕ} (a : Fin V ≃ Fin V)
    (v v₀ : Fin V → Scalar) (k : Fin V → ℂ)
    (aT : Tape ℕ) (z : Tape Datum.T) (kT : Tape ℂ)
    (alphaSource : ∀j : Fin V, aT.look j.val 0=(a j).val)
    (dataSource : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (v j) (v₀ j))
    (kernelSource : ∀j : Fin V, kT.look j.val 0=k j)
    (i : Fin W) (j : Fin V) :
    (run program (input W V aT z kT)).val.look (i.val*V+j.val) (0,(0,0)) =
      DFTModelAffine.encodePaired
        (UniformRoleInputMachine.roleValue v (fun j => UniformPairMachine.prepared (k j)) a i.val j)
        (UniformRoleInputMachine.roleValue v₀ (fun j => UniformPairMachine.prepared (k j)) a i.val j) := by
  rw [program_lookup W V i.val j.val aT z kT i.isLt j.isLt]
  by_cases h0 : i.val=0
  · simpa [h0,UniformRoleInputMachine.roleValue] using dataSource j
  · by_cases h1 : i.val=1
    · simp [h1,UniformRoleInputMachine.roleValue,alphaSource j,kernelSource (a j),
        DFTModelAffine.encodePaired,DFTModelAffine.tagged,DFTModelAffine.flag,
        UniformPairMachine.prepared]
    · simp [h0,h1,UniformRoleInputMachine.roleValue,DFTModelAffine.encodePaired,
        DFTModelAffine.tagged,DFTModelAffine.flag,Scalar.zero]

/-- Only ordinary physical headers, entry bank contents, disjointness and
word bounds are assumed. The 42-instruction loader's action is derived. -/
structure Entry (W V S I K A B : ℕ) (v : Fin V → Scalar) (k : Fin V → ℂ)
    (a : Fin V ≃ Fin V) (s : State) : Prop where
  pc : s.pc=0
  roles : 2≤W
  roleHeader : s.natReg 6300=W
  volumeHeader : s.natReg 6301=V
  bankHeader : s.natReg 6302=S
  inputHeader : s.natReg 6303=I
  kernelHeader : s.natReg 6304=K
  alphaHeader : s.natReg 6305=A
  inputSource : ∀j : Fin V, s.scalarHeap (I+j.val)=some (v j)
  kernelSource : ∀j : Fin V, s.scalarHeap (K+j.val)=some (UniformPairMachine.prepared (k j))
  alphaSource : UniformGlobalNatPreparation.PermutationBank V A s.natHeap a
  inputBefore : I+V≤S
  kernelBefore : K+V≤S
  extent : S+W*V≤B
  tableFit : A+V≤B
  code : 42≤B
  wordBound : WordBound B s

theorem Entry.execution {n W V S I K A B : ℕ} (x : Fin n → ℂ)
    {v : Fin V → Scalar} {k : Fin V → ℂ} {a : Fin V ≃ Fin V} {s : State}
    (h : Entry W V S I K A B v k a s) :
    ∃u, BoundedExecution UniformRoleInputMachine.program n x B s (5*(W*V)+16*V+24) u ∧
      u.pc=41 ∧
      (∀i : Fin W, ∀j : Fin V, u.scalarHeap (S+i.val*V+j.val)=some
        (UniformRoleInputMachine.roleValue v (fun j => UniformPairMachine.prepared (k j)) a i.val j)) ∧
      (∀q, q<S ∨ S+W*V≤q → u.scalarHeap q=s.scalarHeap q) ∧
      UniformRoleInputMachine.Frame s u :=
  UniformRoleInputMachine.execution n B W V S I K A x v
    (fun j => UniformPairMachine.prepared (k j)) a s h.pc h.roles h.roleHeader
    h.volumeHeader h.bankHeader h.inputHeader h.kernelHeader h.alphaHeader
    h.inputSource h.kernelSource h.alphaSource h.inputBefore h.kernelBefore
    h.extent h.tableFit h.code h.wordBound

/-- One typed loader produces the exact affine encoding of both genuinely
executed source loaders, including prepared zero flags and the alpha direction.
The typed tables/banks retain their explicit entry provenance; no source
execution or role-output witness is supplied as an assumption. -/
theorem paired_execution {n W V S I K A B : ℕ} (x : Fin n → ℂ)
    (v v₀ : Fin V → Scalar) (k : Fin V → ℂ) (a : Fin V ≃ Fin V)
    (s s₀ : State) (actual : Entry W V S I K A B v k a s)
    (baseline : Entry W V S I K A B v₀ k a s₀)
    (same : ∀j, ScalarMatch (v j) (v₀ j))
    (aT : Tape ℕ) (z : Tape Datum.T) (kT : Tape ℂ)
    (alphaSource : ∀j : Fin V, aT.look j.val 0=(a j).val)
    (dataSource : ∀j : Fin V, z.look j.val (0,(0,0))=DFTModelAffine.encodePaired (v j) (v₀ j))
    (kernelSource : ∀j : Fin V, kT.look j.val 0=k j) :
    ∃u u₀,
      BoundedExecution UniformRoleInputMachine.program n x B s (5*(W*V)+16*V+24) u ∧
      BoundedExecution UniformRoleInputMachine.program n (fun _ => 0) B s₀ (5*(W*V)+16*V+24) u₀ ∧
      u.pc=41 ∧ u₀.pc=41 ∧
      UniformRoleInputMachine.Frame s u ∧ UniformRoleInputMachine.Frame s₀ u₀ ∧
      (∀q, q<S ∨ S+W*V≤q → u.scalarHeap q=s.scalarHeap q ∧ u₀.scalarHeap q=s₀.scalarHeap q) ∧
      (∀i : Fin W, ∀j : Fin V, ∃b b₀,
        u.scalarHeap (S+i.val*V+j.val)=some b ∧
        u₀.scalarHeap (S+i.val*V+j.val)=some b₀ ∧ ScalarMatch b b₀ ∧
        (run program (input W V aT z kT)).val.look (i.val*V+j.val) (0,(0,0))=
          DFTModelAffine.encodePaired b b₀) ∧
      (run program (input W V aT z kT)).valid ∧
      (run program (input W V aT z kT)).work≤13*(5*(W*V)+16*V+24) ∧
      (run program (input W V aT z kT)).peak≤B := by
  obtain ⟨u,hu,pcu,vu,ou,fu⟩ := actual.execution x
  obtain ⟨u₀,hu₀,pcu₀,vu₀,ou₀,fu₀⟩ := baseline.execution (fun _ => 0)
  refine ⟨u,u₀,hu,hu₀,pcu,pcu₀,fu,fu₀,?_,?_,program_valid _ _ _ _ _,
    work_preserved _ _ _ _ _,(program_peak _ _ _ _ _ actual.roles).trans ?_⟩
  · intro q hq
    exact ⟨ou q hq,ou₀ q hq⟩
  · intro i j
    exact ⟨_,_,vu i j,vu₀ i j,role_match v v₀ k a same i.val j,
      paired_lookup a v v₀ k aT z kT alphaSource dataSource kernelSource i j⟩
  · have h := actual.extent
    omega

end
end ExactFourierCircuits.DFTModelOuterAssemblyRole
