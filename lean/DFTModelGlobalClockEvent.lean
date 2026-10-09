import DFTModelGlobalClockRecords
import DFTModelGlobalClockDiagonalActual

set_option autoImplicit false

/-! Closed diagonal event from actual lane/pool records. This module does not
claim the remaining calendar printer, sector recursion, or whole clock has
been translated. -/
namespace ExactFourierCircuits.DFTModelGlobalClockEvent
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTensorMonomialMachine
noncomputable section

abbrev Input := p w (p DFTModelGlobalClockRecords.Input (Ty.a DFTModelAffine.Tagged))

def prepare : Prog false Input DFTModelGlobalClockDiagonal.Input :=
  .fork (.atom .fst) (.fork
    (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelGlobalClockRecords.program)
    (.comp (.atom .snd) (.atom .snd)))
def program : Prog false Input (Ty.a DFTModelAffine.Tagged) :=
  .comp prepare DFTModelGlobalClockDiagonal.program

attribute [local irreducible] DFTModelGlobalClockRecords.program DFTModelGlobalClockDiagonal.program

theorem prepare_run (W : ℕ) (x : DFTModelGlobalClockRecords.Input.T)
    (v : Tape DFTModelAffine.Tagged.T) :
    run prepare (W,(x,v))=
      ⟨(W,((run DFTModelGlobalClockRecords.program x).val,v)),
        (run DFTModelGlobalClockRecords.program x).work+10,
        (run DFTModelGlobalClockRecords.program x).peak,
        (run DFTModelGlobalClockRecords.program x).valid⟩ := by
  simp [prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem program_run (W : ℕ) (x : DFTModelGlobalClockRecords.Input.T)
    (v : Tape DFTModelAffine.Tagged.T) :
    run program (W,(x,v))=
      ((run DFTModelGlobalClockRecords.program x).pass
        (fun a => run DFTModelGlobalClockDiagonal.program (W,(a,v)))).pay 11 0 := by
  unfold program
  change ((run prepare (W,(x,v))).pass
    (fun x => run DFTModelGlobalClockDiagonal.program x)).pay 1 0=_
  rw [prepare_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem program_value (W : ℕ) (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (lane : Fin 9) (P C : ℕ) (heap : Tape ℂ) (v : Tape DFTModelAffine.Tagged.T)
    (pools : DFTModelGlobalClockRecords.PoolValues as heap) :
    (run program (W,((lane.val,(DFTModelGlobalClockRecords.directory as,heap)),v))).val=
      (run DFTModelGlobalClockDiagonal.program (W,
        (DFTModelGlobalClockTensor.axisTape
          (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),v))).val := by
  rw [program_run]
  change (run DFTModelGlobalClockDiagonal.program (W,
    ((run DFTModelGlobalClockRecords.program
      (lane.val,(DFTModelGlobalClockRecords.directory as,heap))).val,v))).val=_
  rw [DFTModelGlobalClockRecords.program_value as lane P C 0 heap pools]

/-- A genuine concrete event with charged record reads, one coefficient
descent, one whole-role publication and no array update of published storage. -/
theorem program_contract (W B : ℕ) (as : List UniformGlobalDiagonalRowsMachine.Entry)
    (lane : Fin 9) (P C : ℕ) (heap : Tape ℂ) (v : Tape DFTModelAffine.Tagged.T)
    (pools : DFTModelGlobalClockRecords.PoolValues as heap)
    (roles : 0<W) (two : ∀a∈as,2≤a.radix) (countFit : as.length≤B)
    (volumeFit : W*(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod≤B)
    (poolFit : ∀a∈as,a.pool+9*a.radix≤B) :
    (run program (W,((lane.val,(DFTModelGlobalClockRecords.directory as,heap)),v))).val=
      (run DFTModelGlobalClockDiagonal.program (W,
        (DFTModelGlobalClockTensor.axisTape
          (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),v))).val ∧
      (run program (W,((lane.val,(DFTModelGlobalClockRecords.directory as,heap)),v))).valid ∧
      (run program (W,((lane.val,(DFTModelGlobalClockRecords.directory as,heap)),v))).work≤
        169*(W*(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)+
          39*UniformGlobalDiagonalRowsMachine.amount as+38*as.length+49 ∧
      (run program (W,((lane.val,(DFTModelGlobalClockRecords.directory as,heap)),v))).peak≤B := by
  let axes := UniformGlobalDiagonalRowsMachine.axes lane P C 0 as
  have axisTwo : ∀a∈axes,2≤a.radix := by
    intro a ha
    have mem : a.radix∈radices axes := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at mem
    obtain ⟨b,hb,e⟩ := List.mem_map.mp mem
    rw [← e];exact two b hb
  have dc := DFTModelGlobalClockDiagonal.program_contract W axes v roles axisTwo
  let d := DFTModelGlobalClockRecords.directory as
  have rp : (run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).peak≤B := by
    apply DFTModelGlobalClockRecords.program_peak lane.val B d heap countFit
    · intro j hj
      change j<as.length at hj
      let i : Fin as.length := ⟨j,hj⟩
      have r : (d.look j DFTModelGlobalClockRecords.Record.blank).1=(as.get i).radix := by
        simp [d,DFTModelGlobalClockRecords.directory,Tape.look,hj,i]
      rw [r]
      change (as.get i).radix≤B
      have h := poolFit (as.get i) (List.get_mem as i)
      omega
    · intro j hj
      change j<as.length at hj
      let i : Fin as.length := ⟨j,hj⟩
      have r : d.look j DFTModelGlobalClockRecords.Record.blank=
          ((as.get i).radix,(as.get i).pool) := by
        simp [d,DFTModelGlobalClockRecords.directory,Tape.look,hj,i]
      rw [r]
      have h := poolFit (as.get i) (List.get_mem as i)
      have l := lane.isLt
      change (as.get i).pool+(lane.val+1)*(as.get i).radix≤B
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right (as.get i).radix
        (show lane.val+1≤9 by omega)) (as.get i).pool).trans h
  have dp : (run DFTModelGlobalClockDiagonal.program (W,
      (DFTModelGlobalClockTensor.axisTape axes,v))).peak≤B := by
    have h := dc.2.2.2
    rw [UniformGlobalDiagonalRowsMachine.axes_length,UniformGlobalDiagonalRowsMachine.axes_radices] at h
    exact h.trans (max_le countFit volumeFit)
  have rwk := DFTModelGlobalClockRecords.program_work lane.val d heap
  have sum : (∑j∈Finset.range d.len,(d.look j DFTModelGlobalClockRecords.Record.blank).1)=
      UniformGlobalDiagonalRowsMachine.amount as := by
    change (∑j∈Finset.range as.length,
      ((DFTModelGlobalClockRecords.directory as).look j DFTModelGlobalClockRecords.Record.blank).1)=_
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← List.sum_ofFn]
    simp [DFTModelGlobalClockRecords.directory,Tape.look,
      UniformGlobalDiagonalRowsMachine.amount]
  refine ⟨program_value W as lane P C heap v pools,?_,?_,?_⟩
  · rw [program_run]
    change (run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).valid ∧ _
    refine ⟨DFTModelGlobalClockRecords.program_valid _ _ _,?_⟩
    rw [DFTModelGlobalClockRecords.program_value as lane P C 0 heap pools]
    exact dc.2.1
  · rw [program_run]
    change (run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).work+
      (run DFTModelGlobalClockDiagonal.program (W,
        ((run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).val,v))).work+11≤_
    rw [DFTModelGlobalClockRecords.program_value as lane P C 0 heap pools,rwk,sum]
    have dw := dc.2.2.1
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at dw
    change 8+38*as.length+39*UniformGlobalDiagonalRowsMachine.amount as+
      (run DFTModelGlobalClockDiagonal.program
        (W,(DFTModelGlobalClockTensor.axisTape axes,v))).work+11≤_
    omega
  · rw [program_run]
    change max (max (run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).peak
      (run DFTModelGlobalClockDiagonal.program (W,
        ((run DFTModelGlobalClockRecords.program (lane.val,(d,heap))).val,v))).peak) 0≤_
    rw [DFTModelGlobalClockRecords.program_value as lane P C 0 heap pools]
    exact max_le (max_le rp dp) (Nat.zero_le B)

end
end ExactFourierCircuits.DFTModelGlobalClockEvent
