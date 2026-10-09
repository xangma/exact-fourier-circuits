import UniformGenericPhysicalCoordinate
import UniformSynchronizedLayers
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPhysicalSynchronizedSchedule
open OAI.ExactFourier UniformSynchronizedLayers UniformLocalFourierLayers
noncomputable section

def slot (n H:ℕ) (length:∀i,(localSchedules n i).length≤H) (t:Fin H):
 Matrix (Fin (UniformInitialPreparation.len n)) (Fin (UniformInitialPreparation.len n)) ℂ:=
 Matrix.reindex
  ((UniformGenericPhysicalCoordinate.physical (radix n)).trans (finCongr (UniformSelectedCRT.radices_product n)))
  ((UniformGenericPhysicalCoordinate.physical (radix n)).trans (finCongr (UniformSelectedCRT.radices_product n)))
  (tensorSlot (localSchedules n) length t)

def fourier (n:ℕ):Matrix (Fin (UniformInitialPreparation.len n)) (Fin (UniformInitialPreparation.len n)) ℂ:=
 Matrix.reindex
  ((UniformGenericPhysicalCoordinate.physical (radix n)).trans (finCongr (UniformSelectedCRT.radices_product n)))
  ((UniformGenericPhysicalCoordinate.physical (radix n)).trans (finCongr (UniformSelectedCRT.radices_product n)))
  (PiTensor.matrix (fun i:axes n=>fourierMatrix (radix n i)))

/-- Arbitrary synchronized horizon, including actual identity padding. The
result retains the physical MSB coordinate for the charged AP/BI correction. -/
theorem product (n H:ℕ) (length:∀i,(localSchedules n i).length≤H):
 (List.ofFn (slot n H length)).reverse.prod=fourier n:=by
 let e:((i:axes n)→Fin (radix n i))≃Fin (UniformInitialPreparation.len n):=
  (UniformGenericPhysicalCoordinate.physical (radix n)).trans (finCongr (UniformSelectedCRT.radices_product n))
 let hom:=Matrix.reindexAlgEquiv ℂ ℂ e
 change (List.ofFn (fun t:Fin H=>hom (tensorSlot (localSchedules n) length t))).reverse.prod=_
 rw[List.ofFn_comp',←List.map_reverse,←map_list_prod]
 have result:=tensorSchedule_product (localSchedules n) length
 change hom ((tensorSchedule (localSchedules n) length).reverse.prod)=_
 rw[result]
 change Matrix.reindex e e (PiTensor.matrix (fun i=>matrix (localSchedules n i)))=_
 have perAxis:(fun i:axes n=>matrix (localSchedules n i))=(fun i:axes n=>fourierMatrix (radix n i)):=by
  funext i
  exact specifiedSchedule_matrix _
 rw[perAxis]
 rfl
end
end ExactFourierCircuits.UniformPhysicalSynchronizedSchedule
