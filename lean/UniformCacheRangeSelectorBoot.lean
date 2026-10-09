import UniformCacheRangeSelectorFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine

lemma boot_result {r tasks control tick O rectangleCount qs rect s}
 (args:Args r tasks control tick O s)(source:RangeSource r tasks control rectangleCount rect qs s.natHeap):
 Control r tasks qs.length tick O 0 0 (applyBlock boot s) ∧
 UniformGlobalCalendarSelector.Args (control+3*r+4) (stride r) rectangleCount tick O 0 (applyBlock boot s):=by
 have rc:=source.rectangleCountCell
 have nc:=source.nodeCount
 have rc':s.natHeap (tasks+(4+r*4))=some rectangleCount:=by convert rc using 1; congr 1; omega
 have nc':s.natHeap (tasks+(1+(4+r*4)))=some qs.length:=by convert nc using 1; congr 1; omega
 constructor
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,args.radix,args.tasks,args.control,args.tick,args.output,
    stride,rc',nc',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]
 · constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,args.radix,args.tasks,args.control,args.tick,args.output,
    stride,rc',nc',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]
lemma boot_heap(s:State):(applyBlock boot s).natHeap=s.natHeap:=rfl

theorem boot_execution {n r tasks control tick O rectangleCount qs rect B}(x:Fin n → ℂ)(s:State)
 (args:Args r tasks control tick O s)(source:RangeSource r tasks control rectangleCount rect qs s.natHeap)
 (pc:s.pc=0)(wb:WordBound B s)(code:90 ≤ B)
 (layout:Layout r tasks control rectangleCount O B qs):
 BoundedRuns program n x B s 21 (applyBlock boot s):=by
 have rc:=source.rectangleCountCell
 have nc:=source.nodeCount
 have rc':s.natHeap (tasks+(4+r*4))=some rectangleCount:=by convert rc using 1; congr 1; omega
 have nc':s.natHeap (tasks+(1+(4+r*4)))=some qs.length:=by convert nc using 1; congr 1; omega
 have rcb:rectangleCount ≤ B:=(wb.2.2.1 _ _ rc).2
 have ncb:qs.length ≤ B:=(wb.2.2.1 _ _ nc).2
 have tickb:tick ≤ B:=by simpa only[args.tick] using wb.2.1 6703
 have ob:O ≤ B:=by have:=layout.output;omega
 have hb:tasks+4*r+6 ≤ B:=layout.header.trans ob
 have cb:control+3*r+4+stride r*rectangleCount+7 ≤ B:=layout.rectangle.trans ob
 apply block_runs boot program 0 n B x s boot_code pc wb (by change 21 ≤ B;omega)
 · simp [boot,readable,Op.readable,Op.apply,writeNat,next,args.radix,args.tasks,args.control,
    rc',nc',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,args.radix,args.tasks,args.control,args.output,
    rc',nc',Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
   unfold stride at *
   omega

/-- Opaque stage boundary avoids reducing the whole21-step state in later calls. -/
theorem boot_stage {n r tasks control tick O rectangleCount qs rect B}(x:Fin n → ℂ)(s:State)
 (args:Args r tasks control tick O s)(source:RangeSource r tasks control rectangleCount rect qs s.natHeap)
 (pc:s.pc=0)(wb:WordBound B s)(code:90 ≤ B)(layout:Layout r tasks control rectangleCount O B qs):
 ∃a,BoundedRuns program n x B s 21 a ∧a.pc=21 ∧
 Control r tasks qs.length tick O 0 0 a ∧
 UniformGlobalCalendarSelector.Args (control+3*r+4) (stride r) rectangleCount tick O 0 a ∧a.natHeap=s.natHeap:=by
 have run:=boot_execution x s args source pc wb code layout
 have result:=boot_result args source
 exact ⟨applyBlock boot s,run,by rw[applyBlock_pc,pc];rfl,result.1,result.2,rfl⟩
end ExactFourierCircuits.UniformCacheRangeSelector
