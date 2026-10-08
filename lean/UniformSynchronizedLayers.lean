import UniformLocalFourierLayers
import UniformCommonSlots
import OAI.Computability.FourierCircuit.PiTensor

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSynchronizedLayers
open OAI.ExactFourier UniformLocalFourierLayers
noncomputable section

/-- Chronological local layers, with actual identity layers appended. -/
def padded {r : ℕ} (T : ℕ) (L : List (Layer r)) : List (Layer r) :=
  L ++ List.replicate (T-L.length) (Layer.idle r)

theorem padded_length {r T : ℕ} (L : List (Layer r)) (h : L.length≤T) :
    (padded T L).length=T := by simp [padded];omega

theorem padded_matrix {r : ℕ} (T : ℕ) (L : List (Layer r)) :
    matrix (padded T L)=matrix L := by
  simp [padded,matrix,List.map_replicate,Layer.idle_matrix]

theorem padded_calls {r : ℕ} (T : ℕ) (L : List (Layer r)) :
    calls (padded T L)=calls L := by
  simp [padded,calls,List.map_replicate,Layer.idle_calls]

def slot {r T : ℕ} (L : List (Layer r)) (h : L.length≤T) (t : Fin T) : Layer r :=
  (padded T L).get (Fin.cast (padded_length L h).symm t)

theorem ofFn_slot {r T : ℕ} (L : List (Layer r)) (h : L.length≤T) :
    List.ofFn (slot L h)=padded T L := by
  unfold slot
  rw [←List.ofFn_congr (padded_length L h)]
  exact List.ofFn_get _

theorem slot_product {r T : ℕ} (L : List (Layer r)) (h : L.length≤T) :
    (List.ofFn (fun t=>(slot L h t).matrix)).reverse.prod=matrix L := by
  rw [List.ofFn_comp',ofFn_slot]
  exact padded_matrix T L

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι→ℕ} {T : ℕ}

/-- A slot tensors all axes together. It does not serialize full-array axis passes. -/
def tensorSlot (L : ∀i,List (Layer (r i))) (h : ∀i,(L i).length≤T) (t : Fin T) :
    Matrix (∀i,Fin (r i)) (∀i,Fin (r i)) ℂ :=
  PiTensor.matrix (fun i=>(slot (L i) (h i) t).matrix)

def tensorSchedule (L : ∀i,List (Layer (r i))) (h : ∀i,(L i).length≤T) :=
  List.ofFn (tensorSlot L h)

omit [DecidableEq ι] in
theorem tensorSchedule_length (L : ∀i,List (Layer (r i))) (h : ∀i,(L i).length≤T) :
    (tensorSchedule L h).length=T := by simp [tensorSchedule]

/-- Multiplicativity proves synchronization on arbitrary values, including all
borrowed coordinates; no intermediate restoration across other axes is assumed. -/
theorem tensorSchedule_product (L : ∀i,List (Layer (r i))) (h : ∀i,(L i).length≤T) :
    (tensorSchedule L h).reverse.prod=PiTensor.matrix (fun i=>matrix (L i)) := by
  let f := fun t : Fin T => fun i=>(slot (L i) (h i) t).matrix
  change (List.ofFn (fun t=>PiTensor.hom (f t))).reverse.prod=_
  rw [List.ofFn_comp',←List.map_reverse,←map_list_prod]
  change PiTensor.matrix ((List.ofFn f).reverse.prod)=_
  apply congrArg PiTensor.matrix
  funext i
  have he:=map_list_prod (Pi.evalMonoidHom (fun i=>Matrix (Fin (r i)) (Fin (r i)) ℂ) i)
    (List.ofFn f).reverse
  rw [List.map_reverse,List.map_ofFn] at he
  exact he.trans (slot_product (L i) (h i))

abbrev axes (n : ℕ) := Fin (UniformWorkingLength.axisCount n+1)
abbrev radix (n : ℕ) := UniformSelectedCRT.radices n
def localSchedules (n : ℕ) (i : axes n) := specifiedSchedule (radix n i)

theorem localSchedules_length {n : ℕ} (hn : 0<n) (i : axes n) :
    (localSchedules n i).length≤UniformCommonSlots.slotCount n :=
  (specifiedSchedule_length _).trans (UniformCommonSlots.localSlots_bound hn i)

def selectedSchedule (n : ℕ) (hn : 0<n) :=
  tensorSchedule (localSchedules n) (localSchedules_length hn)

theorem selectedSchedule_length (n : ℕ) (hn : 0<n) :
    (selectedSchedule n hn).length=UniformCommonSlots.slotCount n :=
  tensorSchedule_length _ _

theorem selectedSchedule_product (n : ℕ) (hn : 0<n) :
    (selectedSchedule n hn).reverse.prod=PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i)) := by
  rw [selectedSchedule,tensorSchedule_product]
  congr 1
  funext i
  exact specifiedSchedule_matrix _

theorem selectedSchedule_action (n : ℕ) (hn : 0<n) (x : (∀i : axes n,Fin (radix n i))→ℂ) :
    (selectedSchedule n hn).reverse.prod.mulVec x=
      (PiTensor.matrix (fun i : axes n=>fourierMatrix (radix n i))).mulVec x := by
  rw [selectedSchedule_product]

end
end ExactFourierCircuits.UniformSynchronizedLayers
