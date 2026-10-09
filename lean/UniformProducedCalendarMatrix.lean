import UniformProducedCalendarFamily
import UniformProducedSynchronizedAction
/-!
Paper correspondence (audit): *An explicit power saving for the exact discrete Fourier transform*,
OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
§3.5, (3.12)–(3.14), PDF pp. 17–18; §4.3, Proposition 4.2 proof, p. 20 (`loc:three-kernel`, `loc:nonzero-shear`, `loc:nonzero-split`).

This matrix adapter identifies the actual ordered union of local C pairs and the lane-zero diagonal with the native slot. Cast and record-equality lemmas are implementation bookkeeping with no distinct paper theorem.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformProducedCalendarMatrix
open UniformAllAxisSeedPreparation UniformGlobalCalendarDispatch
open UniformMatchingAxisTableMachine UniformMatchingKernelAmbient
open OAI.ExactFourier
noncomputable section

lemma diagonal_reindex {m r:ℕ} (e:Fin m≃Fin r) (d:Fin r→ℂ):
 Matrix.reindex e e (Matrix.diagonal (fun j=>d (e j)))=Matrix.diagonal d:=by
 change (Matrix.diagonal (fun j=>d (e j))).submatrix e.symm e.symm=_
 rw[Matrix.submatrix_diagonal_equiv]
 simp only[Function.comp_def,Equiv.apply_symm_apply]

lemma local_matrix {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r) (hp:2≤r) (d:Fin r→ℂ):
 let c:=UniformMatchingKernelAmbient.coordinate r (edges p) (matching p) (UniformMatchingKernelAmbient.range p) hp
 Matrix.reindex c c (Matrix.diagonal (fun j=>d (c j))*
  UniformMatchingKernelGeometry.localKernel
   (geometry r (edges p) (matching p) (UniformMatchingKernelAmbient.range p) hp))=
 Matrix.diagonal d*Embedded.matrix p (Matrix.blockDiagonal' (fun _:Fin M=>C)):=by
 intro c
 change Matrix.reindexAlgEquiv ℂ ℂ c (_*_)=_
 rw[map_mul]
 change Matrix.reindex c c (Matrix.diagonal (fun j=>d (c j)))*
  Matrix.reindex c c (UniformMatchingKernelGeometry.localKernel
   (geometry r (edges p) (matching p) (UniformMatchingKernelAmbient.range p) hp))=_
 rw[diagonal_reindex,union_kernel]

lemma printed_axis {n:ℕ} (f:UniformProducedAllAxisGeometry.Family n)
 (i:Fin (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).length):
 (UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).get i=
 (f.physical (UniformProducedAllAxisGeometry.index f i)).geometry:=by
 have lt:i.val<axisCount n:=(UniformProducedAllAxisGeometry.index f i).isLt
 have len:((List.ofFn f.physical).map UniformSectorPackingMachine.PhysicalAxis.geometry).length=axisCount n:=by
  simp only[List.length_map,List.length_ofFn]
 have hi:i.val<((List.ofFn f.physical).map UniformSectorPackingMachine.PhysicalAxis.geometry).length:=lt.trans_eq len.symm
 have fnLength:(List.ofFn f.physical).length=axisCount n:=List.length_ofFn
 have hj:i.val<(List.ofFn f.physical).length:=lt.trans_eq fnLength.symm
 change (((List.ofFn f.physical).map UniformSectorPackingMachine.PhysicalAxis.geometry)[i.val]'hi)=_
 exact (List.getElem_map UniformSectorPackingMachine.PhysicalAxis.geometry).trans
  ((congrArg UniformSectorPackingMachine.PhysicalAxis.geometry (List.getElem_ofFn hj)).trans rfl)

lemma cast_matrix_congr {a b:UniformSectorPacking.Axis} {r:ℕ}
 (eq:a=b) (ha:a.widths.sum=r) (hb:b.widths.sum=r) (d:Fin r→ℂ):
 Matrix.reindex (finCongr ha) (finCongr ha)
  (Matrix.diagonal (fun j=>d (finCongr ha j))*UniformMatchingKernelGeometry.localKernel a)=
 Matrix.reindex (finCongr hb) (finCongr hb)
  (Matrix.diagonal (fun j=>d (finCongr hb j))*UniformMatchingKernelGeometry.localKernel b):=by
 cases eq
 rfl

/-- The real ordered union kernel and actual lane0 product are precisely the
per-axis matrix premise consumed by the fixed-coordinate physical action. -/
theorem local_matrices {n H:ℕ} (hn:0<n)
 (es:Fin (axisCount n)→List Event)
 (position:∀i,(Σ _:Fin (callTotal (radix n i) (es i)),Fin 2) ↪ Fin (radix n i))
 (length:∀i,(UniformSynchronizedLayers.localSchedules n i).length≤H) (t:Fin H)
 (native:∀i,Matrix.diagonal (fun j:Fin (radix n i)=>foldValues (es i) (fun _=>1) j.val)*
  Embedded.matrix (position i)
   (Matrix.blockDiagonal' (fun _:Fin (callTotal (radix n i) (es i))=>C))=
  (UniformSynchronizedLayers.slot (UniformSynchronizedLayers.localSchedules n i) (length i) t).matrix):
 let f:=UniformProducedCalendarFamily.family hn es position
 ∀i,Matrix.reindex (finCongr (UniformProducedAllAxisGeometry.shape f i))
  (finCongr (UniformProducedAllAxisGeometry.shape f i))
  (Matrix.diagonal (UniformProducedAllAxisAlignment.factors f i)*
   UniformMatchingKernelGeometry.localKernel
    ((UniformSectorPackingMachine.physicalAxes (UniformProducedAllAxisGeometry.geometry f).physical).get i))=
  (UniformSynchronizedLayers.slot
   (UniformSynchronizedLayers.localSchedules n (UniformProducedAllAxisGeometry.index f i))
   (length (UniformProducedAllAxisGeometry.index f i)) t).matrix:=by
 intro f i
 let k:=UniformProducedAllAxisGeometry.index f i
 have localEq:=local_matrix (position k)
  (UniformMultiAxisSectorMetadataPreparation.selected_radix_two hn k)
  (fun j:Fin (radix n k)=>foldValues (es k) (fun _=>1) j.val)
 have records:=printed_axis f i
 have same:=cast_matrix_congr records (UniformProducedAllAxisGeometry.shape f i)
  (UniformProducedCalendarFamily.physical_radix hn es position k)
  (fun j:Fin (radix n k)=>foldValues (es k) (fun _=>1) j.val)
 exact same.trans (localEq.trans (native k))
end
end ExactFourierCircuits.UniformProducedCalendarMatrix
