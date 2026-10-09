import UniformGenericPhysicalCoordinate
import UniformProducedAllAxisGeometry
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§4.1, mixed-radix traversal and (4.1), PDF p. 18; §5.2, CRT permutations and (5.5), p. 22 (`eq:prefix-nodes`, `eq:crt-fourier`).

The increasing printed axis order induces one fixed most-significant-digit physical coordinate map. This is codec bookkeeping; conversion to CRT input/output order requires the separate charged permutation stages.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedPhysicalCoordinate
open UniformSectorPacking
open UniformAllAxisSeedPreparation
open scoped BigOperators
noncomputable section

/-- This is equality with the generic MSB codec, requiring the actual printed
axis order. It makes no equality claim with the normal CRT LSB ordinal. -/
theorem family_eq {a:ℕ} (ps:List Axis) (idx:Fin ps.length≃Fin a)
 (r:Fin a→ℕ) (shape:∀i,(ps.get i).widths.sum=r (idx i))
 (ordered:∀i,(idx i).val=i.val) (rs:radices ps=List.ofFn r) (ds:∀i,Fin (r i)):
 finCongr ((congrArg List.prod rs).trans (by simp only[List.prod_ofFn]))
  (UniformPhysicalTensorFamily.coordinate ps idx r shape ds)=UniformGenericPhysicalCoordinate.physical r ds:=by
 apply Fin.ext
 change (UniformPhysicalTensorFamily.coordinate ps idx r shape ds).val=
  (UniformGenericPhysicalCoordinate.physical r ds).val
 rw[UniformPhysicalCoordinateValue.family_value,UniformGenericPhysicalCoordinate.physical_value,rs]
 exact Fintype.sum_equiv idx _ _ (fun i=>by rw[ordered i])

lemma radices {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n):
 UniformSectorPacking.radices (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)=
 List.ofFn (UniformSelectedCRT.radices n):=by
 change ((List.ofFn f.physical).map UniformSectorPackingMachine.PhysicalAxis.geometry |>.map (fun a=>a.widths.sum))=_
 rw[List.map_ofFn,List.map_ofFn]
 simp only[Function.comp_def]
 congr 1
 exact funext f.radix_eq

/-- The family produced in increasing axis order uses exactly the generic
physical MSB coordinate consumed by the charged AP/BI table converter. -/
theorem actual_family {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n)
 (ds:∀i:Fin (axisCount n),Fin (radix n i)):
 finCongr ((congrArg List.prod (radices f)).trans (by simp only[List.prod_ofFn]))
  (UniformPhysicalTensorFamily.coordinate
   (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical)
   (UniformProducedAllAxisGeometry.index f) (radix n) (UniformProducedAllAxisGeometry.shape f) ds)=
 UniformGenericPhysicalCoordinate.physical (radix n) ds:=
 family_eq _ (UniformProducedAllAxisGeometry.index f) (radix n) (UniformProducedAllAxisGeometry.shape f)
  (fun _=>rfl) (radices f) ds
end
end ExactFourierCircuits.UniformProducedPhysicalCoordinate
