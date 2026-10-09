import UniformDirectLeafForestData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestBoot
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestProgram UniformDirectLeafForestData
open UniformDirectLeafForestModel
open UniformLocalCacheTreeMachine
noncomputable section

def left (s:State):State:=applyBlock UniformDirectLeafForestProgram.boot s
def initialized (s:State):State:=writeNat (left s) 6680 ((left s).natReg 6680/(left s).natReg 6681)

lemma left_values {p:Parameters}{visits:List Visit}{s:State}(h:Header p visits s):
 (left s).natReg 6680=p.start.pool-p.seedPool ∧
 (left s).natReg 6681=9*p.radix ∧(left s).pc=s.pc+24:=by
 simp [left,UniformDirectLeafForestProgram.boot,applyBlock,Op.apply,writeNat,next,h.pool,h.seedPool,h.radix]

lemma initialized_cursor {p:Parameters}{visits:List Visit}{s:State}(h:Header p visits s)
 (index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)(positive:0<p.radix):
 Cursor p visits 0 (initialized s):=by
 have div:(p.start.pool-p.seedPool)/(9*p.radix)=p.rectangles:=by
  rw[index,Nat.add_sub_cancel_left]
  exact Nat.mul_div_cancel_left _ (by omega)
 constructor
 · constructor <;>simp [initialized,left,UniformDirectLeafForestProgram.boot,applyBlock,Op.apply,writeNat,next,
   position,before_zero,h.original,h.conjugate,h.rows,h.pool,h.permutation,h.widths,h.markers,h.axis,h.entry]
 all_goals simp [initialized,left,UniformDirectLeafForestProgram.boot,applyBlock,Op.apply,writeNat,next,
  h.nodes,h.count,h.starts,h.durations,h.root,h.forward,h.transpose,h.radix,h.pool,h.seedPool,h.ranges,
  before_zero,div]

lemma initialized_frame (s:State):(initialized s).natHeap=s.natHeap ∧
 (initialized s).scalarHeap=s.scalarHeap ∧(initialized s).scalarReg=s.scalarReg ∧
 (initialized s).outputs=s.outputs ∧(initialized s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every pointer copy, root-duration load and measured ordinal division is
executed inside the fixed455 UniformDirectLeafForestProgram.program. -/
theorem execution {p:Parameters}{visits:List Visit}{n B:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Header p visits s)(stride:9*p.radix≤B)(positive:0<p.radix)
 (code:461≤B)(pc:s.pc=0)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 25 (initialized s):=by
 have duration:p.rootDuration≤B:=(wb.2.2.1 _ _ h.root).2
 have roots:s.natHeap (s.natReg 6665)=some p.rootDuration:=by rw[h.durations];exact h.root
 have lrun:BoundedRuns UniformDirectLeafForestProgram.program n x B s 24 (left s):=by
  apply block_runs UniformDirectLeafForestProgram.boot UniformDirectLeafForestProgram.program 0 n B x s boot_code pc wb (by change 24≤B;omega)
  · simp [UniformDirectLeafForestProgram.boot,readable,Op.readable,Op.apply,writeNat,next,roots]
  · simp [UniformDirectLeafForestProgram.boot,peak,Op.peak,Op.apply,writeNat,next,roots,h.radix]
    have r0:=wb.2.1 6660
    have r1:=wb.2.1 6690
    have r2:=wb.2.1 6691
    have r3:=wb.2.1 6692
    have r4:=wb.2.1 6160
    have r5:=wb.2.1 6162
    have r6:=wb.2.1 6163
    have r7:=wb.2.1 6164
    have r8:=wb.2.1 6165
    have r9:=wb.2.1 6166
    have r10:=wb.2.1 6814
    have r11:=wb.2.1 6815
    have r12:=wb.2.1 6810
    omega
 have lp:(left s).pc=24:=by rw[(left_values h).2.2,pc]
 have dw:WordBound B (initialized s):=writeNat_bound B (left s) 6680 _ lrun.final_bound
  (by rw[lp];omega) (Nat.div_le_self _ _|>.trans (lrun.final_bound.2.1 6680))
 have drun:BoundedRuns UniformDirectLeafForestProgram.program n x B (left s) 1 (initialized s):=
  .next lrun.final_bound (by simp [UniformMachine.step,lp,division_at,evalNat,initialized,
   (left_values h).2.1,show 9*p.radix≠0 by omega]) (.refl dw)
 simpa using lrun.trans drun

def completed(s:State):State:=applyBlock UniformDirectLeafForestProgram.durable (initialized s)
def countHeader(p:Parameters):ℕ:=p.ranges+4*p.radix+4
structure Counts(p:Parameters)(visits:List Visit)(s:State):Prop where
 rectangles:s.natHeap (countHeader p)=some p.rectangles
 nodes:s.natHeap (countHeader p+1)=some visits.length

lemma completed_heap {p:Parameters}{visits:List Visit}{s:State}(h:Header p visits s)
 (index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)(positive:0<p.radix):
 (completed s).natHeap=Function.update (Function.update s.natHeap (countHeader p)
 (some p.rectangles)) (countHeader p+1) (some visits.length):=by
 have cursor:=initialized_cursor h index positive
 have radix:(initialized s).natReg 6800=p.radix:=by
  simp [initialized,left,UniformDirectLeafForestProgram.boot,applyBlock,Op.apply,writeNat,next,h.radix]
 simp [completed,UniformDirectLeafForestProgram.durable,applyBlock,Op.apply,writeNat,next,
  cursor.four,cursor.ranges,cursor.one,cursor.ordinal,cursor.count,before_zero,radix,
  countHeader,Nat.add_assoc,(initialized_frame s).1]

lemma completed_counts {p:Parameters}{visits:List Visit}{s:State}(h:Header p visits s)
 (index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)(positive:0<p.radix):
 Counts p visits (completed s):=by
 constructor <;>rw[completed_heap h index positive] <;>simp

lemma completed_cursor {p:Parameters}{visits:List Visit}{s:State}(h:Header p visits s)
 (index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)(positive:0<p.radix):
 Cursor p visits 0 (completed s):=by
 have c:=initialized_cursor h index positive
 have keep(j:ℕ)(ne:j≠6684):(completed s).natReg j=(initialized s).natReg j:=by
  simp (disch:=omega) [completed,UniformDirectLeafForestProgram.durable,applyBlock,Op.apply,writeNat,next]
 exact ⟨⟨(keep _ (by omega)).trans c.originalDirectory,(keep _ (by omega)).trans c.conjugateDirectory,
  (keep _ (by omega)).trans c.pool,(keep _ (by omega)).trans c.rows,
  (keep _ (by omega)).trans c.permutation,(keep _ (by omega)).trans c.widths,
  (keep _ (by omega)).trans c.markers,(keep _ (by omega)).trans c.axis,(keep _ (by omega)).trans c.entry⟩,
  (keep _ (by omega)).trans c.nodes,(keep _ (by omega)).trans c.count,(keep _ (by omega)).trans c.index,
  (keep _ (by omega)).trans c.pointer,(keep _ (by omega)).trans c.starts,(keep _ (by omega)).trans c.durations,
  (keep _ (by omega)).trans c.root,(keep _ (by omega)).trans c.one,(keep _ (by omega)).trans c.two,
  (keep _ (by omega)).trans c.seven,(keep _ (by omega)).trans c.four,(keep _ (by omega)).trans c.fourteen,
  (keep _ (by omega)).trans c.zero,(keep _ (by omega)).trans c.ordinal,(keep _ (by omega)).trans c.divisor,
  (keep _ (by omega)).trans c.forward,(keep _ (by omega)).trans c.transpose,(keep _ (by omega)).trans c.ranges⟩

/-- The two durable counts are actual charged stores after the guarded
measured ordinal division. No count is installed by the host. -/
theorem complete_execution {p:Parameters}{visits:List Visit}{n B:ℕ}(x:Fin n→ℂ)(s:State)
 (h:Header p visits s)(index:p.start.pool=p.seedPool+9*p.radix*p.rectangles)
 (positive:0<p.radix)(stride:9*p.radix≤B)(space:countHeader p+2≤B)
 (code:461≤B)(pc:s.pc=0)(wb:WordBound B s):
 BoundedRuns UniformDirectLeafForestProgram.program n x B s 31 (completed s):=by
 have boot:=execution x s h stride positive code pc wb
 have cursor:=initialized_cursor h index positive
 have ip:(initialized s).pc=25:=by
  simp only[initialized,writeNat,next,(left_values h).2.2,pc]
 have radix:(initialized s).natReg 6800=p.radix:=by
  simp [initialized,left,UniformDirectLeafForestProgram.boot,applyBlock,Op.apply,writeNat,next,h.radix]
 have bound:=boot.final_bound.2.1 6661
 rw[cursor.count] at bound
 have rect:=boot.final_bound.2.1 6680
 rw[cursor.ordinal,before_zero,Nat.add_zero] at rect
 have tail:BoundedRuns UniformDirectLeafForestProgram.program n x B (initialized s) 6 (completed s):=by
  apply block_runs UniformDirectLeafForestProgram.durable UniformDirectLeafForestProgram.program 25 n B x
   (initialized s) UniformDirectLeafForestProgram.durable_code ip boot.final_bound (by change 31≤B;omega)
  · simp [UniformDirectLeafForestProgram.durable,readable,Op.readable]
  · simp [UniformDirectLeafForestProgram.durable,peak,Op.peak,Op.apply,writeNat,next,
    cursor.four,cursor.ranges,cursor.one,cursor.ordinal,cursor.count,before_zero,radix]
    unfold countHeader at space
    omega
 simpa using boot.trans tail
end
end ExactFourierCircuits.UniformDirectLeafForestBoot
