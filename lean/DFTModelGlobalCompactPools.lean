import DFTModelGlobalClockRecords

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalCompactPools
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Pool := p w (Ty.a sc)
abbrev Banks := Ty.a Pool
abbrev Input := p w Banks
abbrev AxisInput := p w Pool
abbrev DirectoryCell := p Input w

/-- The native absolute pool address is replaced only in the typed reader by
relative offset zero into its actual compact per-axis factor tape. -/
def axisArgument : Prog false AxisInput DFTModelGlobalClockRecords.AxisInput :=
  .fork (.atom .fst) (.fork
    (.fork (.comp (.atom .snd) (.atom .fst)) (.atom (.lit 0)))
    (.comp (.atom .snd) (.atom .snd)))
def axis : Prog false AxisInput DFTModelGlobalClockTensor.AxisRecord :=
  .comp axisArgument DFTModelGlobalClockRecords.axis

def entryArgument : Prog false DirectoryCell AxisInput :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.comp (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)) (.atom .look))
def entry : Prog false DirectoryCell DFTModelGlobalClockTensor.AxisRecord :=
  .comp entryArgument axis

def count : Prog false Input w := .comp (.atom .snd) (.atom .len)
def program : Prog false Input DFTModelGlobalClockTensor.Axes := .tab count entry

attribute [local irreducible] DFTModelGlobalClockRecords.axis
  DFTModelGlobalClockRecords.factors

theorem axisArgument_run (l r:ℕ) (f:Tape ℂ) :
    run axisArgument (l,(r,f))=⟨(l,((r,0),f)),11,0,True⟩ := by
  simp [axisArgument,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem axis_run (l r:ℕ) (f:Tape ℂ) :
    run axis (l,(r,f))=
      ⟨(r,(run DFTModelGlobalClockRecords.factors (l,((r,0),f))).val),39*r+26,
        (run DFTModelGlobalClockRecords.factors (l,((r,0),f))).peak,True⟩ := by
  unfold axis
  change ((run axisArgument (l,(r,f))).pass
    (fun x=>run DFTModelGlobalClockRecords.axis x)).pay 1 0=_
  rw [axisArgument_run]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelGlobalClockRecords.axis_run]
  simp only [zero_max,max_zero,true_and]
  congr 1
  omega

theorem entryArgument_run (l j:ℕ) (bs:Tape Pool.T) :
    run entryArgument ((l,bs),j)=⟨(l,bs.look j Pool.blank),11,0,True⟩ := by
  simp [entryArgument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

attribute [local irreducible] axis entryArgument

theorem entry_run (l j:ℕ) (bs:Tape Pool.T) :
    run entry ((l,bs),j)=
      ⟨((bs.look j Pool.blank).1,
        (run DFTModelGlobalClockRecords.factors (l,(((bs.look j Pool.blank).1,0),(bs.look j Pool.blank).2))).val),
        39*(bs.look j Pool.blank).1+38,
        (run DFTModelGlobalClockRecords.factors (l,(((bs.look j Pool.blank).1,0),(bs.look j Pool.blank).2))).peak,True⟩ := by
  unfold entry
  change ((run entryArgument ((l,bs),j)).pass (fun x=>run axis x)).pay 1 0=_
  rw [entryArgument_run]
  simp only [Bill.pass,Bill.pay]
  rw [axis_run]
  simp only [zero_max,max_zero,true_and]
  congr 1
  omega

/-- Explicit representation of already-produced local banks, with no dense
heap or fabricated scalar values. Native storage provenance stays separate. -/
structure PoolValues (as:List UniformGlobalDiagonalRowsMachine.Entry) (bs:Tape Pool.T) : Prop where
  length : bs.len=as.length
  radix : ∀i:Fin as.length,(bs.look i.val Pool.blank).1=(as.get i).radix
  extent : ∀i:Fin as.length,(bs.look i.val Pool.blank).2.len=9*(as.get i).radix
  value : ∀i:Fin as.length,∀l:Fin 9,∀j:Fin (as.get i).radix,
    (bs.look i.val Pool.blank).2.look (l.val*(as.get i).radix+j.val) 0=(as.get i).value l j

theorem actual_entry (as:List UniformGlobalDiagonalRowsMachine.Entry) (l:Fin 9)
    (bs:Tape Pool.T) (pools:PoolValues as bs) (i:Fin as.length) :
    (run entry ((l.val,bs),i.val)).val=
      DFTModelGlobalClockTensor.axisData
        (UniformGlobalDiagonalRowsMachine.axis l 0 0 0 (as.get i)) := by
  rw [entry_run,pools.radix i,DFTModelGlobalClockRecords.factors_value]
  change ((as.get i).radix,Tape.mk (as.get i).radix _)=
    ((as.get i).radix,Tape.mk (as.get i).radix _)
  congr 2
  funext j
  simpa only [Nat.zero_add,UniformGlobalDiagonalRowsMachine.axis] using pools.value i l j

theorem count_run (l:ℕ) (bs:Tape Pool.T) : run count (l,bs)=⟨bs.len,3,bs.len,True⟩ := by
  simp [count,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

attribute [local irreducible] entry count

theorem program_run (l:ℕ) (bs:Tape Pool.T) :
    run program (l,bs)=
      (Bill.tab bs.len DFTModelGlobalClockTensor.AxisRecord.blank
        (fun j=>run entry ((l,bs),j))).pay 4 bs.len := by
  unfold program
  change ((run count (l,bs)).pass (fun n=>
    Bill.tab n DFTModelGlobalClockTensor.AxisRecord.blank
      (fun j=>run entry ((l,bs),j)))).pay 1 0=_
  rw [count_run]
  simp only [Bill.pass,Bill.pay,true_and]
  congr 1 <;>omega

theorem program_value (as:List UniformGlobalDiagonalRowsMachine.Entry)
    (l:Fin 9) (P C o:ℕ) (bs:Tape Pool.T) (pools:PoolValues as bs) :
    (run program (l.val,bs)).val=DFTModelGlobalClockTensor.axisTape
      (UniformGlobalDiagonalRowsMachine.axes l P C o as) := by
  rw [program_run]
  change (Bill.tab bs.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j=>run entry ((l.val,bs),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value,
    DFTModelGlobalClockRecords.axisTape_listTape,DFTModelGlobalClockRecords.actual_axis_data]
  apply DFTModelGlobalClockRecords.tape_ext DFTModelGlobalClockTensor.AxisRecord.blank
  · simp [Tape.tab,DFTModelGlobalClockRecords.listTape,pools.length]
  · intro j hj
    change j<bs.len at hj
    have ja:j<as.length:=by simpa only [pools.length] using hj
    have e:=actual_entry as l bs pools ⟨j,ja⟩
    simpa [Tape.tab,Tape.look,DFTModelGlobalClockRecords.listTape,hj,ja] using e

def amount (bs:Tape Pool.T) : ℕ := ∑j∈Finset.range bs.len,(bs.look j Pool.blank).1

theorem program_work (l:ℕ) (bs:Tape Pool.T) :
    (run program (l,bs)).work=6+42*bs.len+39*amount bs := by
  rw [program_run]
  change (Bill.tab bs.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j=>run entry ((l,bs),j))).work+4=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have hw:(fun j=>(run entry ((l,bs),j)).work)=fun j=>39*(bs.look j Pool.blank).1+38:=by
    funext j;exact congrArg Bill.work (entry_run l j bs)
  rw [hw,Finset.sum_add_distrib,←Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  unfold amount
  omega

theorem program_valid (l:ℕ) (bs:Tape Pool.T) : (run program (l,bs)).valid := by
  rw [program_run]
  change (Bill.tab bs.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j=>run entry ((l,bs),j))).valid
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>by rw [entry_run];trivial)

theorem program_peak (l B:ℕ) (bs:Tape Pool.T) (countFit:bs.len≤B)
    (radixFit:∀j<bs.len,(bs.look j Pool.blank).1≤B)
    (poolFit:∀j<bs.len,(l+1)*(bs.look j Pool.blank).1≤B) :
    (run program (l,bs)).peak≤B := by
  rw [program_run]
  change max (Bill.tab bs.len DFTModelGlobalClockTensor.AxisRecord.blank
    (fun j=>run entry ((l,bs),j))).peak bs.len≤_
  rw [ModelEquivalenceInterpreter.tab_peak]
  have bound:(Finset.range bs.len).sup (fun j=>(run entry ((l,bs),j)).peak)≤B:=by
    apply Finset.sup_le
    intro j hj
    rw [entry_run]
    have h:=Finset.mem_range.mp hj
    exact DFTModelGlobalClockRecords.factors_peak l _ 0 B _ (radixFit j h)
      (by simpa only [Nat.zero_add] using poolFit j h)
  omega

theorem amount_eq (as:List UniformGlobalDiagonalRowsMachine.Entry) (bs:Tape Pool.T)
    (pools:PoolValues as bs) : amount bs=UniformGlobalDiagonalRowsMachine.amount as := by
  unfold amount
  rw [pools.length,←Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑i:Fin as.length,(as.get i).radix:=Finset.sum_congr rfl (fun i _=>pools.radix i)
    _ = _:=by rw [←List.sum_ofFn];simp [UniformGlobalDiagonalRowsMachine.amount]

end
end ExactFourierCircuits.DFTModelGlobalCompactPools
