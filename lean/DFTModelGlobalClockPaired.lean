import DFTModelGlobalClockDiagonalActual

set_option autoImplicit false

/-! Paper correspondence: An explicit power saving for the exact discrete
Fourier transform, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§4.3, Proposition 4.2 proof, (4.5), PDF p.20 (eq:tensor-multiply): the tensor
monomial slot, specialized to diagonal factors. The actual131 source execution
and its zero-input counterpart are represented by one typed run. Every produced
output offset is exactly the second source value. Raw factor pools, a matched
source entry and its paired tape remain local entry conditions; cache/record
production and global entry provenance are separate obligations. -/
namespace ExactFourierCircuits.DFTModelGlobalClockPaired
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformTensorMonomialMachine
open DFTModelAdmissibilityControl DFTModelAffine
open DFTModelGlobalClockDiagonal
noncomputable section

def Source {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (v v0 : ℕ → ℕ → Scalar) (t : Tape Datum.T) : Prop :=
  t.len=W*g.volume ∧ ∀i : Fin W,∀j : Fin g.volume,
    t.look (i.val*g.volume+j.val) Datum.blank=encodePaired (v i.val j.val) (v0 i.val j.val)

def Output {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (t : Tape Datum.T) (u u0 : State) : Prop :=
  t.len=W*g.volume ∧ ∀i : Fin W,∀j : Fin g.volume,∃a a0,
    u.scalarHeap (g.destination+i.val*g.volume+j.val)=some a ∧
    u0.scalarHeap (g.destination+i.val*g.volume+j.val)=some a0 ∧
    t.look (i.val*g.volume+j.val) Datum.blank=encodePaired a a0

lemma source_representation {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (v v0 : ℕ → ℕ → Scalar) (t : Tape Datum.T) (s s0 : State)
    (same : StateMatch s s0) (h : Source g v v0 t)
    (actual : UniformGlobalTensorDiagonalMachine.Source g v s)
    (baseline : UniformGlobalTensorDiagonalMachine.Source g v0 s0) :
    SourceRepresentation g v t := by
  refine ⟨h.1,?_⟩
  intro i j
  rw [h.2 i j]
  obtain ⟨z,hz,matched⟩ := (same.scalarHeap _).left (actual i.val i.isLt j.val j.isLt)
  have equal : z=v0 i.val j.val := Option.some.inj
    (hz.symm.trans (baseline i.val i.isLt j.val j.isLt))
  subst z
  exact encodePaired_represents _ _ matched

lemma directory_transfer {D i : ℕ} {as : List UniformGlobalDiagonalRowsMachine.Entry}
    {s s0 : State} (same : StateMatch s s0)
    (h : UniformGlobalDiagonalRowsMachine.Directory D as i s) :
    UniformGlobalDiagonalRowsMachine.Directory D as i s0 := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    exact ⟨⟨by rw [same.natHeap];exact h.1.1,
      by rw [same.natHeap];exact h.1.2⟩,ih h.2⟩

lemma pools_transfer {as : List UniformGlobalDiagonalRowsMachine.Entry} {s s0 : State}
    (same : StateMatch s s0) (h : UniformGlobalDiagonalRowsMachine.Pools as s) :
    UniformGlobalDiagonalRowsMachine.Pools as s0 := by
  intro a ha lane j
  obtain ⟨z,hz,matched⟩ := (same.scalarHeap _).left (h a ha lane j)
  have equal := matched.eq_of_prepared rfl
  rw [hz,←equal]

lemma filled_paired {W : ℕ} (g : UniformGlobalTensorDiagonalMachine.Geometry W)
    (as : List UniformGlobalDiagonalRowsMachine.Entry) (lane : Fin 9) (P C : ℕ)
    (v v0 : ℕ → ℕ → Scalar) (t : Tape Datum.T) (u u0 : State)
    (volume : g.volume=(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)
    (two : ∀a∈as,2≤a.radix) (h : Source g v v0 t)
    (done : UniformGlobalTensorDiagonalMachine.Filled g
      (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) v W u)
    (done0 : UniformGlobalTensorDiagonalMachine.Filled g
      (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as) v0 W u0) :
    Output g (run program (W,(DFTModelGlobalClockTensor.axisTape
      (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),t))).val u u0 := by
  let axes := UniformGlobalDiagonalRowsMachine.axes lane P C 0 as
  have av : g.volume=(radices axes).prod := by
    rw [UniformGlobalDiagonalRowsMachine.axes_radices];exact volume
  have axisTwo : ∀a∈axes,2≤a.radix := by
    intro a ha
    have member : a.radix∈radices axes := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at member
    obtain ⟨b,hb,equal⟩ := List.mem_map.mp member
    rw [←equal];exact two b hb
  have out := UniformGlobalTensorDiagonalPreparation.diagonal_values done
  have out0 := UniformGlobalTensorDiagonalPreparation.diagonal_values done0
  refine ⟨?_,?_⟩
  · rw [(program_contract W axes t g.positive axisTwo).1]
    change W*(radices axes).prod=W*g.volume
    rw [av]
  · intro i j
    let j' : Fin (radices axes).prod := ⟨j.val,by rw [←av];exact j.isLt⟩
    refine ⟨_,_,out i.val i.isLt j',out0 i.val i.isLt j',?_⟩
    have entry : t.look (i.val*(radices axes).prod+j'.val) Datum.blank=
        encodePaired (v i.val j.val) (v0 i.val j.val) := by
      change t.look (i.val*(radices axes).prod+j.val) Datum.blank=_
      rw [←av];exact h.2 i j
    have result := role_paired_lookup W axes t g.positive axisTwo i j' _ _ entry
    simpa only [←av] using result

/-- Every entry condition describes raw source records, prepared scalar pools
or original paired data. Both complete source executions are genuine; only one
typed diagonal program is billed. No produced tensor bank is assumed. -/
theorem actual_execution {W n : ℕ} (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (L : UniformGlobalDiagonalRowsMachine.Layout) (lane : Fin 9)
    (g : UniformGlobalTensorDiagonalMachine.Geometry W) (v v0 : ℕ → ℕ → Scalar)
    (t : Tape Datum.T) (x : Fin n → ℂ) (s s0 : State)
    (same : StateMatch s s0)
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
    (baseline : UniformGlobalTensorDiagonalMachine.Source g v0 s0)
    (encoded : Source g v v0 t) (two : ∀a∈as,2≤a.radix)
    (code : 131≤L.B) (pc : s.pc=0) (wb : WordBound L.B s) :
    ∃u u0,
      BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n x L.B s
        (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u ∧
      BoundedExecution (UniformGlobalTensorDiagonalPreparation.programFor W) n (fun _ => 0) L.B s0
        (9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) u0 ∧
      StateMatch u u0 ∧ u.pc=130 ∧ SourceFrame L g s u ∧ SourceFrame L g s0 u0 ∧
      Output g (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).val u u0 ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).valid ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).work≤
          200*(9*L.total+35*L.ell+W*(treeCost (as.map UniformGlobalDiagonalRowsMachine.Entry.radix)+20)+14) ∧
      (run program (W,(DFTModelGlobalClockTensor.axisTape
        (UniformGlobalDiagonalRowsMachine.axes lane L.permutation L.coefficient 0 as),t))).peak≤L.B := by
  have rh0 : UniformGlobalDiagonalRowsMachine.Header L lane s0 := by
    exact ⟨by rw [same.natReg];exact rowHeader.count,
      by rw [same.natReg];exact rowHeader.directory,
      by rw [same.natReg];exact rowHeader.lane,
      by rw [same.natReg];exact rowHeader.rows,
      by rw [same.natReg];exact rowHeader.permutation,
      by rw [same.natReg];exact rowHeader.coefficient⟩
  have th0 : UniformGlobalTensorDiagonalMachine.Header g s0 := by
    exact ⟨by rw [same.natReg];exact tensorHeader.volume,
      by rw [same.natReg];exact tensorHeader.source,
      by rw [same.natReg];exact tensorHeader.destination,
      by rw [same.natReg];exact tensorHeader.axes,
      by rw [same.natReg];exact tensorHeader.rows,
      by rw [same.natReg];exact tensorHeader.natStack,
      by rw [same.natReg];exact tensorHeader.scalarStack⟩
  obtain ⟨u,run,up,frame,_,valid,work,peak⟩ := DFTModelGlobalClockDiagonal.actual_execution
    as L lane g v t x s sameB sameRows length sameAxes total volume pBelow cBelow
      sourceSeparate rowHeader directory pools poolBound tensorHeader source
      (source_representation g v v0 t s s0 same encoded source baseline) two code pc wb
  obtain ⟨z,run',_,filled,_,_,_,_,_⟩ := UniformGlobalTensorDiagonalPreparation.execution
    as L lane g v x s sameB sameRows length sameAxes total volume pBelow cBelow
      sourceSeparate rowHeader directory pools poolBound tensorHeader source code pc wb
  have zu : z=u := (run'.executes.deterministic run.executes).2
  subst z
  obtain ⟨u0,run0,_,filled0,saved0,out0,roots0,nat0,scalar0⟩ :=
    UniformGlobalTensorDiagonalPreparation.execution as L lane g v0 (fun _ => 0) s0
      sameB sameRows length sameAxes total volume pBelow cBelow sourceSeparate rh0
      (directory_transfer same directory) (pools_transfer same pools) poolBound th0 baseline
      code (same.pc.trans pc) (same.wordBound wb)
  obtain ⟨z0,rz0,matched⟩ := boundedExecution_match (y:=fun _ => 0) run same
  have equal : z0=u0 := (rz0.executes.deterministic run0.executes).2
  subst z0
  exact ⟨u,u0,run,run0,matched,up,frame,⟨saved0,out0,roots0,nat0,scalar0⟩,
    filled_paired g as lane L.permutation L.coefficient v v0 t u u0 volume two encoded
      filled filled0,valid,work,peak⟩

end
end ExactFourierCircuits.DFTModelGlobalClockPaired
