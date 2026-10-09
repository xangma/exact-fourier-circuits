import UniformRepeatedMaskMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualPivotMachine
open UniformMachine
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
open BinaryFrames DirectionalWords
noncomputable section
/-- First nonzero binary coordinate is discovered by charged physical reads.
The failure branch is reached for an all-zero descriptor. -/
def boot : List Op := [.literal 4032 0,.literal 4033 1,.literal 4034 0]
def read : List Op := [.binary .add 4035 4031 4034,.load 4036 4035]
def program : Program := boot.map Op.code++[.branchLT 4034 4030 4 10]++
 read.map Op.code++[.branchLT 4036 4033 7 9,.natBinary .add 4034 4034 4033,
 .jump 3,.halt,.natBinary .div 4032 4032 4032]
theorem program_length : program.length=11 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
theorem read_code : BlockAt read program 4 := by intro i hi;change i<2 at hi;interval_cases i <;> rfl
theorem branch_at : program[3]?=some (.branchLT 4034 4030 4 10) := rfl
theorem found_at : program[6]?=some (.branchLT 4036 4033 7 9) := rfl
theorem increment_at : program[7]?=some (.natBinary .add 4034 4034 4033) := rfl
theorem jump_at : program[8]?=some (.jump 3) := rfl
theorem halt_at : program[9]?=some .halt := rfl

def Changed (r : ℕ) : Prop := 4032≤r∧r<4037
structure Frame (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r→u.natReg r=s.natReg r
lemma Frame.pc {s u : State} (f : Frame s u) (p : ℕ) : Frame s {u with pc:=p} :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Frame.trans {s u v : State} (f : Frame s u) (g : Frame u v) : Frame s v :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
 g.outputs.trans f.outputs,g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma frame_read (s : State) : Frame s (applyBlock read s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h;simp (disch:=omega) [Changed] at h
 simp (disch:=omega) [read,applyBlock,Op.apply,evalNat,writeNat,next]

structure Header (w U i : ℕ) (s : State) : Prop where
 pc : s.pc=3
 width : s.natReg 4030=w
 source : s.natReg 4031=U
 index : s.natReg 4034=i
 one : s.natReg 4033=1

lemma reads (n B w U i : ℕ) (v : Vec (Fin w)) (x : Fin n→ℂ) (s : State)
 (h : Header w U i s) (hi : i<w)
 (source : UniformRepeatedMaskMachine.Source U v s)
 (bound : WordBound B s) (code : 11≤B) (extent : U+w≤B) : ∃u,
 BoundedRuns program n x B s 3 u ∧ u.pc=6 ∧ u.natReg 4036=(v ⟨i,hi⟩).val ∧
 Frame s u ∧ Header w U i {u with pc:=3} := by
 let entry:State:={s with pc:=4}
 have eb:=changePC_bound B s 4 bound (by omega)
 have branch : BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,h.pc,branch_at,h.index,h.width,hi,entry]) (.refl eb)
 have physical : s.natHeap (U+i)=some (v ⟨i,hi⟩).val := source ⟨i,hi⟩
 have vb : (v ⟨i,hi⟩).val≤B := by have h:=ZMod.val_lt (v ⟨i,hi⟩);change (v ⟨i,hi⟩).val<2 at h;omega
 have safe : readable read entry ∧ peak read entry≤B := by
  simp [read,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   entry,h.source,h.index,physical]
  omega
 have rr:=block_runs read program 4 n B x entry read_code rfl eb (by change 6≤B;omega) safe.1 safe.2
 let u:=applyBlock read entry
 refine ⟨u,?_,?_,?_,(⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩:Frame s entry).trans (frame_read entry),?_⟩
 · convert branch.trans rr using 1
   simp [read]
 · simp [u,read,applyBlock,Op.apply,writeNat,next,entry]
 · simp [u,read,applyBlock,Op.apply,evalNat,writeNat,next,entry,h.source,h.index,physical]
 · constructor <;> simp [u,read,applyBlock,Op.apply,evalNat,writeNat,next,entry,h.width,h.source,h.index,h.one]

lemma scan (n B w U p : ℕ) (v : Vec (Fin w)) (x : Fin n→ℂ)
 (hp : p<w) (vp : v ⟨p,hp⟩=1) (before : ∀i (hi:i<p),v ⟨i,hi.trans hp⟩=0)
 (code : 11≤B) (extent : U+w≤B) :
 ∀remaining i s,i+remaining=p→Header w U i s→UniformRepeatedMaskMachine.Source U v s→WordBound B s→
 ∃u,BoundedExecution program n x B s (6*remaining+5) u ∧ u.pc=9 ∧
 u.natReg 4034=p ∧ Frame s u := by
 intro remaining
 induction remaining with
 | zero=>
  intro i s eq h source bound
  have ip : i=p := by omega
  obtain ⟨u,run,pc,value,frame,head⟩:=reads n B w U i v x s h (by omega) source bound code extent
  have one : u.natReg 4033=1 := head.one
  have index : u.natReg 4034=i := head.index
  have width : u.natReg 4030=w := head.width
  have base : u.natReg 4031=U := head.source
  have bit : u.natReg 4036=1 := by
   rw [value]
   have eqv : v ⟨i,by omega⟩=1 := by simpa [ip] using vp
   rw [eqv];rfl
  let ret:State:={u with pc:=9}
  have rb:=changePC_bound B u 9 run.final_bound (by omega)
  have stop : BoundedExecution program n x B u 2 ret:=.next run.final_bound
   (by simp [step,pc,found_at,bit,one,ret]) (.halt rb (by simp [step,ret,halt_at]))
  refine ⟨ret,?_,rfl,?_,frame.pc 9⟩
  · convert run.executes stop using 1
  · simpa [ret,ip] using head.index
 | succ remaining ih=>
  intro i s eq h source bound
  have low : i<p := by omega
  obtain ⟨u,run,pc,value,frame,head⟩:=reads n B w U i v x s h (by omega) source bound code extent
  have one : u.natReg 4033=1 := head.one
  have index : u.natReg 4034=i := head.index
  have width : u.natReg 4030=w := head.width
  have base : u.natReg 4031=U := head.source
  have bit : u.natReg 4036=0 := by rw [value];simpa using congrArg ZMod.val (before i low)
  let entry:State:={u with pc:=7}
  let incremented:=writeNat entry 4034 (i+1)
  let next:State:={incremented with pc:=3}
  have eb:=changePC_bound B u 7 run.final_bound (by omega)
  have nb : WordBound B incremented := writeNat_bound B entry 4034 (i+1) eb
   (by change 8≤B;omega) (by have wb:=bound.2.1 4030;rw [h.width] at wb;omega)
  have tail : BoundedRuns program n x B u 3 next:=.next run.final_bound
   (by simp [step,pc,found_at,bit,one])
   (.next eb (by simp [step,entry,increment_at,incremented,evalNat,index,one])
    (.next nb (by simp [step,incremented,entry,writeNat,next,UniformMachine.next,jump_at])
     (.refl (changePC_bound B incremented 3 nb (by omega)))))
  have hn : Header w U (i+1) next := by
   constructor <;> simp [next,incremented,entry,writeNat,UniformMachine.next,width,base,one]
  have sourceNext : UniformRepeatedMaskMachine.Source U v next := by
   intro j;change u.natHeap (U+j.val)=some (v j).val;rw [frame.natHeap];exact source j
  obtain ⟨out,rest,pcout,index,fr⟩:=ih (i+1) next (by omega) hn sourceNext tail.final_bound
  have tf : Frame u next := by
   refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro r h;have ne:r≠4034 := by unfold Changed at h;omega
   simp [next,incremented,entry,writeNat,UniformMachine.next,ne]
  refine ⟨out,?_,pcout,index,frame.trans (tf.trans fr)⟩
  convert run.executes (tail.executes rest) using 1
  omega

/-- Original descriptor presence and nonzeroness suffice: no pivot index or
produced coordinate/table is supplied to the caller. -/
theorem execution (n B w U : ℕ) (v : Vec (Fin w)) (x : Fin n→ℂ) (s : State)
 (nonzero : v≠0) (pc : s.pc=0) (width : s.natReg 4030=w) (base : s.natReg 4031=U)
 (source : UniformRepeatedMaskMachine.Source U v s)
 (bound : WordBound B s) (code : 11≤B) (extent : U+w≤B) : ∃p : Fin w,∃u,
 BoundedExecution program n x B s (6*p.val+8) u ∧ u.pc=9 ∧ u.natReg 4034=p.val ∧
 v p=1 ∧ (∀i:Fin w,i.val<p.val→v i=0) ∧ Frame s u := by
 have witness : ∃i:ℕ,∃hi:i<w,v ⟨i,hi⟩=1 := by
  obtain ⟨i,hi⟩:=DirectionalWords.exists_pivot v nonzero
  exact ⟨i.val,i.isLt,hi⟩
 let p:=Nat.find witness
 obtain ⟨hp,vp⟩:=Nat.find_spec witness
 have before : ∀i (hi:i<p),v ⟨i,hi.trans hp⟩=0 := by
  intro i hi
  rcases binary_values (v ⟨i,hi.trans hp⟩) with h|h
  · exact h
  · exact False.elim (Nat.find_min witness hi ⟨hi.trans hp,h⟩)
 have start:=block_runs boot program 0 n B x s boot_code pc bound
  (by change 3≤B;omega) (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let ready:=applyBlock boot s
 have head : Header w U 0 ready := by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc,width,base]
 obtain ⟨u,run,pcu,index,frame⟩:=scan n B w U p v x hp vp before code extent p 0 ready
  (by omega) head source start.final_bound
 have bf : Frame s ready := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r h;simp (disch:=omega) [Changed] at h
  simp (disch:=omega) [ready,boot,applyBlock,Op.apply,writeNat,next]
 refine ⟨⟨p,hp⟩,u,?_,pcu,index,vp,?_,bf.trans frame⟩
 · convert start.executes run using 1
   simp [boot]
   omega
 · intro i hi;exact before i.val hi
end
end ExactFourierCircuits.UniformResidualPivotMachine
