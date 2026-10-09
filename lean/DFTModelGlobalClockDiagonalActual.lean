import DFTModelGlobalClockDiagonal
import DFTModelAffinePaired

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelGlobalClockDiagonal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformTensorMonomialMachine
noncomputable section

attribute [local irreducible] program DFTModelGlobalClockTensor.program

theorem role_lookup (W : ℕ) (axes : List Axis) (v : Tape Datum.T)
    (roles : 0<W) (two : ∀a∈axes,2≤a.radix)
    (i : Fin W) (j : Fin (radices axes).prod) :
    (run program (W,(DFTModelGlobalClockTensor.axisTape axes,v))).val.look
      (i.val*(radices axes).prod+j.val) Datum.blank=
        DFTModelMemoryAffinePointwise.scaled
          (v.look (i.val*(radices axes).prod+j.val) Datum.blank)
          (tensorCoefficient axes j) := by
  rw [(program_contract W axes v roles two).1]
  have hj := j.isLt
  have hi := i.isLt
  have within : i.val*(radices axes).prod+j.val<W*(radices axes).prod := by nlinarith
  rw [Tape.look_of_lt _ _ within]
  have hm : (i.val*(radices axes).prod+j.val)%(radices axes).prod=j.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hj]
  simp [Tape.tab,DFTModelGlobalClockTensor.coefficientTape,hm,Tape.look,j.isLt]

theorem scaled_product (z : Datum.T) (v : Scalar) (c : ℂ)
    (h : DFTModelAffine.Represents z v) :
    DFTModelAffine.Represents (DFTModelMemoryAffinePointwise.scaled z c)
      (UniformPairMachine.product c v) := by
  rcases h with ⟨flag,value,prepared⟩
  refine ⟨flag,?_,?_⟩
  · change c*v.value=c*z.2.1+c*z.2.2
    rw [value,mul_add]
  · intro dep
    change c*z.2.2=0
    rw [prepared dep,mul_zero]

/-- The offset is the corresponding zero-input source scalar, not an
unspecified representation of the same numeric value. -/
theorem scaled_paired (c : ℂ) (a a₀ : Scalar) :
    DFTModelMemoryAffinePointwise.scaled (DFTModelAffine.encodePaired a a₀) c=
      DFTModelAffine.encodePaired (UniformPairMachine.product c a)
        (UniformPairMachine.product c a₀) := by
  simp [DFTModelMemoryAffinePointwise.scaled,DFTModelAffine.encodePaired,
    DFTModelAffine.tagged,UniformPairMachine.product,mul_sub]

theorem role_paired_lookup (W : ℕ) (axes : List Axis) (t : Tape Datum.T)
    (roles : 0<W) (two : ∀a∈axes,2≤a.radix)
    (i : Fin W) (j : Fin (radices axes).prod) (a a₀ : Scalar)
    (entry : t.look (i.val*(radices axes).prod+j.val) Datum.blank=
      DFTModelAffine.encodePaired a a₀) :
    (run program (W,(DFTModelGlobalClockTensor.axisTape axes,t))).val.look
      (i.val*(radices axes).prod+j.val) Datum.blank=
        DFTModelAffine.encodePaired
          (UniformPairMachine.product (tensorCoefficient axes j) a)
          (UniformPairMachine.product (tensorCoefficient axes j) a₀) := by
  rw [role_lookup W axes t roles two i j,entry,scaled_paired]

def SourceRepresentation {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (v : ℕ → ℕ → Scalar) (t : Tape Datum.T) : Prop :=
  t.len=W*g.volume ∧ ∀i : Fin W,∀j : Fin g.volume,
    DFTModelAffine.Represents (t.look (i.val*g.volume+j.val) Datum.blank) (v i.val j.val)

def OutputRepresentation {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (t : Tape Datum.T) (u : State) : Prop :=
  t.len=W*g.volume ∧ ∀i : Fin W,∀j : Fin g.volume,∃v,
    u.scalarHeap (g.destination+i.val*g.volume+j.val)=some v ∧
      DFTModelAffine.Represents (t.look (i.val*g.volume+j.val) Datum.blank) v

/-- Specialization of the actual131 output theorem to a single typed event.
The factor inputs are the real prepared lane values from its Entry records. -/
theorem filled_representation {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (as : List UniformGlobalDiagonalRowsMachine.Entry) (lane : Fin 9) (P C : ℕ)
    (v : ℕ → ℕ → Scalar) (t : Tape Datum.T) (u : State)
    (volume : g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
    (two : ∀a∈as,2≤a.radix) (represented : SourceRepresentation g v t)
    (done : UniformGlobalTensorDiagonalMachine.Filled g
      (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) v W u) :
    OutputRepresentation g
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),t))).val u := by
  let axes := UniformGlobalDiagonalRowsMachine.axes lane P C 0 as
  have av : g.volume=(radices axes).prod := by
    rw [UniformGlobalDiagonalRowsMachine.axes_radices]; exact volume
  have axisTwo : ∀a∈axes,2≤a.radix := by
    have hr := UniformGlobalDiagonalRowsMachine.axes_radices lane P C 0 as
    intro a ha
    have mem : a.radix∈radices axes := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hr] at mem
    obtain ⟨b,hb,equal⟩ := List.mem_map.mp mem
    rw [← equal]
    exact two b hb
  have out := UniformGlobalTensorDiagonalPreparation.diagonal_values done
  refine ⟨?_,?_⟩
  · rw [(program_contract W axes t g.positive axisTwo).1]
    change W*(radices axes).prod=W*g.volume
    rw [av]
  · intro i j
    let j' : Fin (radices axes).prod := ⟨j.val,by rw [← av];exact j.isLt⟩
    refine ⟨UniformPairMachine.product (tensorCoefficient axes j') (v i.val j.val),
      out i.val i.isLt j',?_⟩
    have lookup := role_lookup W axes t g.positive axisTwo i j'
    have entry := represented.2 i j
    change DFTModelAffine.Represents _ _
    have goalIndex : i.val*g.volume+j.val=i.val*(radices axes).prod+j'.val :=
      congrArg (fun V => i.val*V+j.val) av
    rw [goalIndex,lookup]
    apply scaled_product
    simpa only [← av] using entry

theorem volume_le_treeCost (rs : List ℕ) : rs.prod≤treeCost rs := by
  induction rs with
  | nil => simp [treeCost]
  | cons r rs ih =>
    simp only [List.prod_cons,treeCost]
    have hm := Nat.mul_le_mul_left r ih
    nlinarith

def SourceFrame {W : ℕ} (L : UniformGlobalDiagonalRowsMachine.Layout)
    (g : UniformGlobalTensorDiagonalMachine.Geometry W) (s u : State) : Prop :=
  (∀q,100≤q → q≤106 → u.natReg q=s.natReg q) ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀q,(q<L.rows ∨ L.rows+3*L.ell≤q) →
    (q<L.permutation ∨ L.permutation+L.total≤q) →
    (q<g.natStack ∨ g.natStack+3*g.ell≤q) → u.natHeap q=s.natHeap q) ∧
  (∀q,(q<L.coefficient ∨ L.coefficient+L.total≤q) →
    (q<g.scalarStack ∨ g.scalarStack+g.ell≤q) →
    (q<g.destination ∨ g.destination+W*g.volume≤q) → u.scalarHeap q=s.scalarHeap q)

/-- Concrete actual131 source execution paired with one closed typed event.
All input tables/pools are ordinary source entry contracts. No tensor output,
semantic callback, child action, or emitter is supplied. -/
theorem actual_execution {W n : ℕ} (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (L : UniformGlobalDiagonalRowsMachine.Layout) (lane : Fin 9)
    (g : UniformGlobalTensorDiagonalMachine.Geometry W) (v : ℕ → ℕ → Scalar)
    (t : Tape Datum.T) (x : Fin n → ℂ) (s : State)
    (sameB : g.B=L.B) (sameRows : g.row=L.rows) (length : as.length=L.ell)
    (sameAxes : g.ell=L.ell) (total : UniformGlobalDiagonalRowsMachine.amount as=L.total)
    (volume : g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
    (pBelow : L.permutation+L.total≤g.natStack)
    (cBelow : L.coefficient+L.total≤g.scalarStack)
    (sourceSeparate : g.source+W*g.volume≤L.coefficient ∨ L.coefficient+L.total≤g.source)
    (rowHeader : UniformGlobalDiagonalRowsMachine.Header L lane s)
    (directory : UniformGlobalDiagonalRowsMachine.Directory L.directory as 0 s)
    (pools : UniformGlobalDiagonalRowsMachine.Pools as s)
    (poolBound : ∀a∈as,a.pool+9*a.radix≤L.coefficient)
    (tensorHeader : UniformGlobalTensorDiagonalMachine.Header g s)
    (source : UniformGlobalTensorDiagonalMachine.Source g v s)
    (represented : SourceRepresentation g v t) (two : ∀a∈as,2≤a.radix)
    (code : 131≤L.B) (pc : s.pc=0) (wb : WordBound L.B s) :
    ∃u,BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x L.B s
        (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u ∧
      u.pc=130 ∧ SourceFrame L g s u ∧
      OutputRepresentation g (run program
        (W,(DFTModelGlobalClockTensor.axisTape
          (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).val u ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).valid ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).work≤
          200*(9*L.total+35*L.ell+
            W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).peak≤L.B := by
  obtain ⟨u,execution,upc,filled,saved,outputs,roots,natOutside,scalarOutside⟩ :=
    UniformGlobalTensorDiagonalPreparation.execution as L lane g v x s sameB sameRows length
      sameAxes total volume pBelow cBelow sourceSeparate rowHeader directory pools poolBound
      tensorHeader source code pc wb
  let axes := UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as
  have av : g.volume=(radices axes).prod := by
    rw [UniformGlobalDiagonalRowsMachine.axes_radices];exact volume
  have axisTwo : ∀a∈axes,2≤a.radix := by
    intro a ha
    have mem : a.radix∈radices axes := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at mem
    obtain ⟨b,hb,equal⟩ := List.mem_map.mp mem
    rw [← equal];exact two b hb
  have typed := program_contract W axes t g.positive axisTwo
  refine ⟨u,execution,upc,⟨saved,outputs,roots,natOutside,scalarOutside⟩,
    filled_representation g as lane L.permutation L.coefficient v t u volume two represented filled,
    typed.2.1,?_,?_⟩
  · have vc := volume_le_treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)
    have mul := Nat.mul_le_mul_left W vc
    have tw := typed.2.2.1
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at tw
    nlinarith
  · have pe := typed.2.2.2
    have nl := g.natStackBound
    have dl := g.destinationBound
    have al : axes.length=g.ell := by
      rw [UniformGlobalDiagonalRowsMachine.axes_length,length,sameAxes]
    rw [al,← av] at pe
    change (run program (W,(DFTModelGlobalClockTensor.axisTape axes,t))).peak≤L.B
    have bound : max g.ell (W*g.volume)≤L.B := by rw [← sameB];omega
    exact pe.trans bound

end
end ExactFourierCircuits.DFTModelGlobalClockDiagonal
