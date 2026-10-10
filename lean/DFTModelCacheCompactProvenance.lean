import DFTModelCacheCompactClosed

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheCompact
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

def actualAxis (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n)) :
    Fin (UniformAllAxisSeedPreparation.axisCount n) := i.castSucc

theorem actual_radix (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n)) :
    UniformAllAxisSeedPreparation.radix n (actualAxis n i)=UniformWorkingLength.oddPrime i.val := by
  simp only [actualAxis,UniformAllAxisSeedPreparation.radix,UniformGlobalLocalPreparation.radix,
    UniformSelectedCRT.radices,Fin.snoc_castSucc]

def NativeValues (n : ℕ) (i : Fin (UniformWorkingLength.axisCount n))
    (t : Tape ℂ) (s : UniformMachine.State) : Prop :=
  t.len=5*UniformWorkingLength.oddPrime i.val ∧
  ∀q : Fin 5,∀j : Fin (UniformWorkingLength.oddPrime i.val),
    s.scalarHeap (UniformAllAxisSeedPreparation.axisBase n i.val+
      q.val*UniformWorkingLength.oddPrime i.val+j.val)=
        some (UniformPairMachine.prepared (t.look (q.val*UniformWorkingLength.oddPrime i.val+j.val) 0))

/-- The closed raw producer's emitted scalar tape has the exact physical
original-bank values. Retained is used only to compare to the old native
preparer; it is not an entry premise of rawProgram or its specification. -/
theorem original_values (n : ℕ) (hn : 0<n) (i : Fin (UniformWorkingLength.axisCount n))
    (s : UniformMachine.State)
    (retained : UniformAllAxisSeedPreparation.Retained n
      (UniformAllAxisSeedPreparation.axisCount n) s) :
    NativeValues n i ((run rawProgram (n,OAI.ExactFourier.zeta
      (UniformMasterRootMachine.order n))).val.look i.val (Tape.empty ℂ)) s := by
  refine ⟨?_,?_⟩
  · rw [raw_value n hn,Tape.look_of_lt (values n) (Tape.empty ℂ) i.isLt]
    rfl
  · intro q j
    rw [raw_lane n hn i q j]
    have cell:=retained.coefficients (actualAxis n i) (actualAxis n i).isLt
    rw [actual_radix] at cell
    exact cell q j

/-- In particular the actual rank-kernel source is inverse H, compact lane3.
The supplied native bank is compared to the generated tape, never used as an
oracle to compute it. -/
theorem inverseH_lane (r : ℕ) (eta : ℂ) (j : Fin r) :
    (run localProgram (r,eta)).val.look (3*r+j.val) 0=
      PowerSeries.coeff j.val (OAI.ExactFourier.NewtonFourier.invH eta) := by
  have h:=lane_value r eta (3:Fin 5) j
  simpa [UniformLocalSeedTableMachine.seedValue,OAI.ExactFourier.NewtonFourier.invH] using h

theorem reciprocal_lane (r : ℕ) (eta : ℂ) (j : Fin r) :
    (run localProgram (r,eta)).val.look (4*r+j.val) 0=
      PowerSeries.coeff j.val (OAI.ExactFourier.NewtonFourier.invH eta)⁻¹ :=
  lane_value r eta (4:Fin 5) j

end
end ExactFourierCircuits.DFTModelCacheCompact
