import DFTModelGlobalCompactPools
import DFTModelGlobalClockDiagonalActual

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalCompactPoolsEvent
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformTensorMonomialMachine
noncomputable section

abbrev Input := p w (p DFTModelGlobalCompactPools.Input (Ty.a DFTModelAffine.Tagged))
def prepare : Prog false Input DFTModelGlobalClockDiagonal.Input :=
  .fork (.atom .fst) (.fork
    (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelGlobalCompactPools.program)
    (.comp (.atom .snd) (.atom .snd)))
def program : Prog false Input (Ty.a DFTModelAffine.Tagged) :=
  .comp prepare DFTModelGlobalClockDiagonal.program
attribute [local irreducible] DFTModelGlobalCompactPools.program DFTModelGlobalClockDiagonal.program

private theorem radix_of_pool (r B : ℕ) (h : 9*r≤B) : r≤B := by omega

theorem prepare_run (W:ℕ) (x:DFTModelGlobalCompactPools.Input.T)
    (v:Tape DFTModelAffine.Tagged.T) :
    run prepare (W,(x,v))=
      ⟨(W,((run DFTModelGlobalCompactPools.program x).val,v)),
        (run DFTModelGlobalCompactPools.program x).work+10,
        (run DFTModelGlobalCompactPools.program x).peak,
        (run DFTModelGlobalCompactPools.program x).valid⟩ := by
  simp [prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

theorem program_run (W:ℕ) (x:DFTModelGlobalCompactPools.Input.T)
    (v:Tape DFTModelAffine.Tagged.T) :
    run program (W,(x,v))=
      ((run DFTModelGlobalCompactPools.program x).pass
        (fun a=>run DFTModelGlobalClockDiagonal.program (W,(a,v)))).pay 11 0 := by
  unfold program
  change ((run prepare (W,(x,v))).pass (fun x=>run DFTModelGlobalClockDiagonal.program x)).pay 1 0=_
  rw [prepare_run]
  simp [Bill.pass,Bill.pay]
  omega

theorem program_value (W:ℕ) (as:List UniformGlobalDiagonalRowsMachine.Entry)
    (lane:Fin 9) (P C:ℕ) (banks:Tape DFTModelGlobalCompactPools.Pool.T)
    (v:Tape DFTModelAffine.Tagged.T) (pools:DFTModelGlobalCompactPools.PoolValues as banks) :
    (run program (W,((lane.val,banks),v))).val=
      (run DFTModelGlobalClockDiagonal.program (W,
        (DFTModelGlobalClockTensor.axisTape (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),v))).val := by
  rw [program_run]
  change (run DFTModelGlobalClockDiagonal.program (W,
    ((run DFTModelGlobalCompactPools.program (lane.val,banks)).val,v))).val=_
  rw [DFTModelGlobalCompactPools.program_value as lane P C 0 banks pools]

/-- The only compact scalar inputs are the retained per-axis nine-lane banks.
Absolute native pool addresses never determine typed allocation or reader indices. -/
theorem program_contract (W B:ℕ) (as:List UniformGlobalDiagonalRowsMachine.Entry)
    (lane:Fin 9) (P C:ℕ) (banks:Tape DFTModelGlobalCompactPools.Pool.T)
    (v:Tape DFTModelAffine.Tagged.T) (pools:DFTModelGlobalCompactPools.PoolValues as banks)
    (roles:0<W) (two:∀a∈as,2≤a.radix) (countFit:as.length≤B)
    (volumeFit:W*(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod≤B)
    (poolFit:∀a∈as,9*a.radix≤B) :
    (run program (W,((lane.val,banks),v))).val=
      (run DFTModelGlobalClockDiagonal.program (W,
        (DFTModelGlobalClockTensor.axisTape (UniformGlobalDiagonalRowsMachine.axes lane P C 0 as),v))).val ∧
    (run program (W,((lane.val,banks),v))).valid ∧
    (run program (W,((lane.val,banks),v))).work≤
      169*(W*(as.map UniformGlobalDiagonalRowsMachine.Entry.radix).prod)+
        39*UniformGlobalDiagonalRowsMachine.amount as+42*as.length+47 ∧
    (run program (W,((lane.val,banks),v))).peak≤B := by
  let axes:=UniformGlobalDiagonalRowsMachine.axes lane P C 0 as
  have axisTwo:∀a∈axes,2≤a.radix:=by
    intro a ha
    have mem:a.radix∈radices axes:=List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at mem
    obtain ⟨b,hb,e⟩:=List.mem_map.mp mem
    rw [←e];exact two b hb
  have dc:=DFTModelGlobalClockDiagonal.program_contract W axes v roles axisTwo
  have rp:(run DFTModelGlobalCompactPools.program (lane.val,banks)).peak≤B:=by
    apply DFTModelGlobalCompactPools.program_peak lane.val B banks (by rw [pools.length];exact countFit)
    · intro j hj
      have ja:j<as.length:=by simpa only [pools.length] using hj
      rw [pools.radix ⟨j,ja⟩]
      exact radix_of_pool _ _ (poolFit (as.get ⟨j,ja⟩) (List.get_mem _ _))
    · intro j hj
      have ja:j<as.length:=by simpa only [pools.length] using hj
      rw [pools.radix ⟨j,ja⟩]
      exact (Nat.mul_le_mul_right _ (show lane.val+1≤9 by have:=lane.isLt;omega)).trans
        (poolFit (as.get ⟨j,ja⟩) (List.get_mem _ _))
  have dp:(run DFTModelGlobalClockDiagonal.program (W,
      (DFTModelGlobalClockTensor.axisTape axes,v))).peak≤B:=by
    have h:=dc.2.2.2
    rw [UniformGlobalDiagonalRowsMachine.axes_length,UniformGlobalDiagonalRowsMachine.axes_radices] at h
    exact h.trans (max_le countFit volumeFit)
  refine ⟨program_value W as lane P C banks v pools,?_,?_,?_⟩
  · rw [program_run]
    change (run DFTModelGlobalCompactPools.program (lane.val,banks)).valid ∧ _
    refine ⟨DFTModelGlobalCompactPools.program_valid _ _,?_⟩
    rw [DFTModelGlobalCompactPools.program_value as lane P C 0 banks pools]
    exact dc.2.1
  · rw [program_run]
    change (run DFTModelGlobalCompactPools.program (lane.val,banks)).work+
      (run DFTModelGlobalClockDiagonal.program (W,
        ((run DFTModelGlobalCompactPools.program (lane.val,banks)).val,v))).work+11≤_
    rw [DFTModelGlobalCompactPools.program_value as lane P C 0 banks pools,
      DFTModelGlobalCompactPools.program_work,DFTModelGlobalCompactPools.amount_eq as banks pools,pools.length]
    change 6+42*as.length+39*UniformGlobalDiagonalRowsMachine.amount as+
      (run DFTModelGlobalClockDiagonal.program (W,
        (DFTModelGlobalClockTensor.axisTape axes,v))).work+11≤_
    have dw:=dc.2.2.1
    rw [UniformGlobalDiagonalRowsMachine.axes_radices] at dw
    omega
  · rw [program_run]
    change max (max (run DFTModelGlobalCompactPools.program (lane.val,banks)).peak
      (run DFTModelGlobalClockDiagonal.program (W,
        ((run DFTModelGlobalCompactPools.program (lane.val,banks)).val,v))).peak) 0≤_
    rw [DFTModelGlobalCompactPools.program_value as lane P C 0 banks pools]
    exact max_le (max_le rp dp) (Nat.zero_le B)

end
end ExactFourierCircuits.DFTModelGlobalCompactPoolsEvent
