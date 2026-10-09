import UniformActualGlobalTickContext
import UniformPhysicalTensorFamily
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.2, Lemma 4.1, PDF p. 19; §4.3, Proposition 4.2, pp. 19–20 (`lem:sector-address`, `prop:tensor-fourier`).

Produced axis records determine the physical shape and allocation. These structures describe ordinary finite data and layout bounds; their cell contents are supplied later by producer executions, not by the geometry definition.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedAllAxisGeometry
open UniformSectorPackingMachine UniformAllAxisSeedPreparation
open UniformActualGlobalConstants (constants)
noncomputable section

/-- Only ordinary projections of the actual produced per-axis records. -/
structure Family (n:ℕ) where
 physical:Fin (axisCount n)→PhysicalAxis
 pool:Fin (axisCount n)→ℕ
 value:∀i:Fin (axisCount n),Fin 9→Fin (radix n i)→ℂ
 radix_eq:∀i,(physical i).geometry.widths.sum=radix n i
 widths:∀i,(physical i).widthsBase+(physical i).geometry.widths.length≤2*UniformJointAllocation.slab constants n
 permutations:∀i,(physical i).permutationBase+(physical i).geometry.widths.sum≤2*UniformJointAllocation.slab constants n
 pools:∀i,pool i+9*radix n i≤2*UniformJointAllocation.slab constants n

lemma volume {n:ℕ} (f:Family n):physicalVolume (List.ofFn f.physical)=UniformInitialPreparation.len n:=by
 change ((List.ofFn f.physical).map PhysicalAxis.geometry |>.map (fun a=>a.widths.sum)).prod=_
 rw[List.map_ofFn,List.map_ofFn]
 simp only[Function.comp_def]
 have shape:(fun i=>(f.physical i).geometry.widths.sum)=UniformSelectedCRT.radices n:=funext f.radix_eq
 rw[shape,List.prod_ofFn,UniformSelectedCRT.radices_product]

theorem placement {n:ℕ} (f:Family n):
 UniformJointDiagonalContext.PhysicalPlacement constants n (List.ofFn f.physical) where
 volume:=volume f
 length:=by simp only[List.length_ofFn]
 widths:=by
  intro a ha
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
  exact f.widths i
 permutations:=by
  intro a ha
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
  exact f.permutations i

def geometry {n:ℕ} (f:Family n):UniformActualGlobalTickContext.Geometry n where
 entries:=UniformJointDiagonalContext.entries n f.pool f.value
 selected:=UniformJointDiagonalContext.entries_radices n f.pool f.value
 poolFit:=by
  intro a ha
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
  exact f.pools i
 physical:=List.ofFn f.physical
 placement:=placement f

lemma axes_length {n:ℕ} (f:Family n):
 (physicalAxes (geometry f).physical).length=axisCount n:=by
 simp only[geometry,physicalAxes,List.length_map,List.length_ofFn]

def index {n:ℕ} (f:Family n):Fin (physicalAxes (geometry f).physical).length≃Fin (axisCount n):=
 finCongr (axes_length f)

lemma shape {n:ℕ} (f:Family n) (i:Fin (physicalAxes (geometry f).physical).length):
 ((physicalAxes (geometry f).physical).get i).widths.sum=radix n (index f i):=by
 dsimp only[geometry,physicalAxes] at i ⊢
 simp only[List.get_eq_getElem,List.getElem_map,List.getElem_ofFn]
 exact f.radix_eq (index f i)
end
end ExactFourierCircuits.UniformProducedAllAxisGeometry
