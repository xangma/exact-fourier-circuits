import DFTModelCacheLeafCoefficientsProgram
import UniformDirectLeafCacheProducedSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheLeafCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier
open UniformTransposeDescriptorMachine
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelCacheForest.prepareInverseH
  DFTModelCacheDirectLeaf.orientations banks annotate

/-- Exactly the compact invH lane, not the H lane. -/
def inverseH (r : ℕ) (omega : ℂ) : Tape ℂ :=
  Tape.tab r (fun j=>(NewtonFourier.H omega j)⁻¹)
def encoded (qs : List Record) : Tape DFTModelCacheDirectLeaf.Record4.T :=
  DFTModelCacheTraversal.ofList (qs.map DFTModelCacheDirectLeaf.encode)
def coefficientPairs (omega : ℂ) (K : ℕ) (qs : List Record) : Pairs.T :=
  DFTModelCacheTraversal.ofList (qs.map (fun q=>
    ((NewtonFourier.H omega (q.coefficient-K))⁻¹,
      (NewtonFourier.H omega⁻¹ (q.coefficient-K))⁻¹)))

theorem banks_value (r : ℕ) (omega : ℂ) :
    (run banks (r,omega)).val=(inverseH r omega,inverseH r omega⁻¹) := by
  rw [banks_run]
  change ((run DFTModelCacheForest.prepareInverseH (r,omega)).val,
    (run DFTModelCacheForest.prepareInverseH (r,omega⁻¹)).val)=_
  rw [DFTModelCacheForest.prepareInverseH_value,DFTModelCacheForest.prepareInverseH_value]
  rfl

theorem banks_valid {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) : (run banks (r,omega)).valid := by
  rw [banks_run]
  exact ⟨DFTModelCacheForest.prepareInverseH_valid hr primitive,
    ⟨primitive.ne_zero (Nat.ne_of_gt hr),
      DFTModelCacheForest.prepareInverseH_valid hr primitive.inv⟩,trivial⟩

theorem setup_run (r v o K : ℕ) (omega : ℂ) :
    run setup ((r,omega),(v,(o,K)))=
      ⟨(((r,omega),(v,(o,K))),((run banks (r,omega)).val,
        (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).val)),
        (run banks (r,omega)).work+(run DFTModelCacheDirectLeaf.orientations (v,(o,K))).work+7,
        max (run banks (r,omega)).peak (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).peak,
        (run banks (r,omega)).valid ∧ (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).valid⟩ := by
  simp [setup,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem annotateArgument_run (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) (transposed : Bool) :
    run (annotateArgument transposed) (input,((h,hc),(f,t)))=
      ⟨((input.2.2.2,(h,hc)),if transposed then t else f),17,0,True⟩ := by
  cases transposed <;>
    simp [annotateArgument,seedBase,seedBanks,seedRecords,run,Code.run,Atom.run,
      Bill.one,Bill.pass,Bill.pay]

theorem body_run (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) :
    run body (input,((h,hc),(f,t)))=
      ((run annotate ((input.2.2.2,(h,hc)),f)).pass (fun fp=>
        (run annotate ((input.2.2.2,(h,hc)),t)).pass (fun tp=>
          Bill.one ((h,hc),((f,t),(fp,tp)))))).pay 44 0 := by
  rw [body,fork_run,fork_run,fork_run,comp_run,comp_run,
    annotateArgument_run,annotateArgument_run]
  simp [seedBanks,seedRecords,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem body_value (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run body (input,((h,hc),(f,t)))).val=
      ((h,hc),((f,t),((run annotate ((input.2.2.2,(h,hc)),f)).val,
        (run annotate ((input.2.2.2,(h,hc)),t)).val))) := by
  rw [body_run]
  rfl

theorem body_valid (input : Input.T) (h hc : Tape ℂ)
    (f t : Tape DFTModelCacheDirectLeaf.Record4.T) :
    (run body (input,((h,hc),(f,t)))).valid := by
  rw [body_run]
  exact ⟨annotate_valid _ _ _ _,annotate_valid _ _ _ _,trivial⟩

/-- The source range proof precedes lookup; no out-of-range blank is used as a coefficient. -/
theorem annotate_produced (r K : ℕ) (omega : ℂ) (qs : List Record)
    (range : ∀q∈qs,UniformDirectLeafCacheSource.InRange r K q) :
    (run annotate ((K,(inverseH r omega,inverseH r omega⁻¹)),encoded qs)).val=
      coefficientPairs omega K qs := by
  rw [annotate_value]
  apply DFTModelCacheTraversal.tape_ext _ _ (p sc sc).blank
  · simp [encoded,coefficientPairs,DFTModelCacheTraversal.ofList,Tape.tab]
  intro i hi
  have hi' : i<qs.length := by simpa [encoded,DFTModelCacheTraversal.ofList,Tape.tab] using hi
  have rng:=range qs[i] (List.getElem_mem hi')
  have ix : qs[i].coefficient-K<r := by rcases rng with ⟨_,_,lo,up⟩;omega
  have recLook : (encoded qs).look i DFTModelCacheDirectLeaf.Record4.blank=
      DFTModelCacheDirectLeaf.encode qs[i] := by
    rw [Tape.look_of_lt _ _ (by simpa [encoded,DFTModelCacheTraversal.ofList] using hi')]
    simp only [encoded,DFTModelCacheTraversal.ofList,List.getElem_map]
  rw [Tape.look_of_lt _ _ hi]
  change (_,_) = _
  rw [recLook]
  simp only [DFTModelCacheDirectLeaf.encode]
  rw [Tape.look_of_lt _ _ ix,Tape.look_of_lt _ _ ix]
  have out : i<(coefficientPairs omega K qs).len := by
    simpa [coefficientPairs,DFTModelCacheTraversal.ofList] using hi'
  rw [Tape.look_of_lt _ _ out]
  simp only [inverseH,coefficientPairs,DFTModelCacheTraversal.ofList,List.getElem_map]
  rfl

def values (r v o K : ℕ) (omega : ℂ) : Output.T :=
  let f:=leafRecords v o K
  let t:=f.reverse.map Record.transpose
  ((inverseH r omega,inverseH r omega⁻¹),((encoded f,encoded t),
    (coefficientPairs omega K f,coefficientPairs omega K t)))

theorem program_value (r v o K : ℕ) (omega : ℂ) (extent : o+v≤r) :
    (run program ((r,omega),(v,(o,K)))).val=values r v o K omega := by
  change (run body (run setup ((r,omega),(v,(o,K)))).val).val=_
  rw [setup_run]
  change (run body ((((r,omega),(v,(o,K))),((run banks (r,omega)).val,
    (run DFTModelCacheDirectLeaf.orientations (v,(o,K))).val)))).val=_
  rw [banks_value,DFTModelCacheDirectLeaf.orientations_value,body_value]
  unfold values
  congr 2
  apply Prod.ext
  · exact annotate_produced _ _ _ _ (fun q h=>
      (UniformDirectLeafCacheChronology.leaf_valid v o K r extent q h).1)
  · exact annotate_produced _ _ _ _ (fun q h=>by
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
      have good:=UniformDirectLeafCacheChronology.leaf_valid v o K r extent p (List.mem_reverse.mp hp)
      exact (UniformDirectLeafCacheChronology.transpose_valid r K p good.1 good.2).1)

theorem program_valid {r : ℕ} (hr : 0<r) {omega : ℂ}
    (primitive : IsPrimitiveRoot omega r) (v o K : ℕ) :
    (run program ((r,omega),(v,(o,K)))).valid := by
  change (run setup _).valid ∧ (run body (run setup _).val).valid
  constructor
  · rw [setup_run]
    exact ⟨banks_valid hr primitive,DFTModelCacheDirectLeaf.orientations_valid _ _ _⟩
  · rw [setup_run]
    exact body_valid _ _ _ _ _

/-- Canonical primitive root: the second produced coefficient is the genuine conjugate. -/
theorem canonical_pair (r K : ℕ) (hr : 0<r) (q : Record)
    (range : UniformDirectLeafCacheSource.InRange r K q) :
    ((NewtonFourier.H (zeta r) (q.coefficient-K))⁻¹,
      (NewtonFourier.H (zeta r)⁻¹ (q.coefficient-K))⁻¹)=
      (UniformDirectLeafCacheSource.mu r K q,
        starRingEnd ℂ (UniformDirectLeafCacheSource.mu r K q)) := by
  have ix : q.coefficient-K<r := by rcases range with ⟨_,_,lo,up⟩;omega
  have conj:=UniformSeedConjugatePreparation.seedValue_conjugate r hr (3:Fin 5) ⟨q.coefficient-K,ix⟩
  apply Prod.ext
  · rfl
  · simpa [UniformDirectLeafCacheSource.mu,UniformLocalSeedTableMachine.seedValue,
      UniformConjugateLocalPreparation.axisRoot] using conj

end
end ExactFourierCircuits.DFTModelCacheLeafCoefficients
