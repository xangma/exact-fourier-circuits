import UniformMatchingAxisFusion
import UniformGlobalMatchingScaleBankBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingPhysicalDiagonal
open UniformColoring UniformMatchingAxisTableMachine UniformMatchingPackingPreparation
open UniformMatchingAxisFusion UniformGlobalMatchingScaleBankBridge
noncomputable section

theorem nativeCoefficient_eq {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (hpos:2≤r) (mu:Fin M→ℂ) (lane:Fin 9)
    (z:Fin (geometry r E hm hr hpos).widths.sum) :
    nativeCoefficient (geometry r E hm hr hpos) (matchingCoefficients r E hm hr hpos mu) lane z=
      nativeFactor E mu lane z.val := by
  by_cases h:∃i,Incident (E i) z.val
  · obtain ⟨i,hi|hi⟩:=h
    · have eq:axisCoordinates (geometry r E hm hr hpos)
          (matchingPosition r E hm hr hpos i 0)=z:=by
        apply Fin.ext
        simpa only [Fin.val_zero,ite_true] using (pair_native_value r E hm hr hpos i 0).trans hi
      rw [←eq,nativeCoefficient_pair]
      have hv:=pair_native_value r E hm hr hpos i 0
      simp only [Fin.val_zero,ite_true] at hv
      rw [hv,nativeFactor_left E mu hm]
    · have eq:axisCoordinates (geometry r E hm hr hpos)
          (matchingPosition r E hm hr hpos i 1)=z:=by
        apply Fin.ext
        simpa only [Fin.val_one,one_ne_zero,ite_false] using (pair_native_value r E hm hr hpos i 1).trans hi
      rw [←eq,nativeCoefficient_pair]
      have hv:=pair_native_value r E hm hr hpos i 1
      simp only [Fin.val_one,one_ne_zero,ite_false] at hv
      rw [hv,nativeFactor_right E mu hm]
  · have un:z.val∉paired E:=by
      intro hz
      obtain ⟨i,hi|hi⟩:=(paired_mem E z.val).mp hz
      · exact h ⟨i,Or.inl hi.symm⟩
      · exact h ⟨i,Or.inr hi.symm⟩
    rw [nativeCoefficient_unused r E hm hr hpos mu lane z un,
      nativeFactor_unused E mu lane z.val (by intro i hi;exact h ⟨i,hi⟩)]

theorem nativePhase_actual_diagonal {M : ℕ} (r : ℕ) (E : Fin M→Edge)
    (hm:Matching E) (hr:InRange r E) (hpos:2≤r) (mu:Fin M→ℂ) (lane:Fin 9) :
    nativePhase (geometry r E hm hr hpos) (matchingCoefficients r E hm hr hpos mu) (.diagonal lane)=
      Matrix.diagonal (fun z=>nativeFactor E mu lane z.val) := by
  rw [nativePhase_diagonal]
  exact congrArg Matrix.diagonal (funext (nativeCoefficient_eq r E hm hr hpos mu lane))
end
end ExactFourierCircuits.UniformMatchingPhysicalDiagonal
