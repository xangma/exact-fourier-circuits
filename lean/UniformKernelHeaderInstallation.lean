import UniformInverseHeaderInstallation
import UniformConditionalKernelLayout
set_option autoImplicit false
namespace ExactFourierCircuits.UniformKernelHeaderInstallation
open UniformMachine UniformTensorMonomialMachine
open UniformConditionalKernelLayout (Context Ready)
noncomputable section

/-- All sources are actual saved startup or allocator cells. Zero/one and
the initial generated-sector ordinal are charged ordinary literals. -/
def head:List Op:=[.literal 5990 0,.literal 5991 1,
 .add 5820 103 5990,.add 5821 6026 5990,.add 5822 6028 5990,.add 5823 102 5991,
 .add 5824 6030 5990,.add 5825 6032 5990,.add 5826 6033 5990,.add 5827 6036 5990,
 .add 3201 6030 5990,.add 3202 6031 5990,.add 3213 6032 5990,.add 3214 6033 5990,
 .add 3215 6034 5990,.add 4441 6035 5990,.add 4442 6029 5990,
 .add 4530 103 5990,.add 4531 6028 5990,.literal 5800 0,.add 5801 6037 5990]
def block:List Op:=head++UniformInverseHeaderInstallation.block
lemma head_length:head.length=21:=rfl
lemma block_length:block.length=32:=rfl

/-- Ordinary address/size links only. In the concrete corollary they are
projections of the actual62 allocator and retained startup103/102 cells. -/
structure Input {W F R:ℕ} (g:Context W F R) (s:State):Prop where
 volume:s.natReg 103=g.packing.volume
 count:s.natReg 102+1=g.metadata.ell
 source:s.natReg 6026=g.packing.source
 packed:s.natReg 6028=g.packing.destination
 rows:s.natReg 6030=g.packing.rows
 suffix:s.natReg 6032=g.packing.suffix
 stack:s.natReg 6033=g.packing.stack
 inverse:s.natReg 6036=g.packing.inverse
 metadataRows:s.natReg 6031=g.metadata.rows
 metadataSuffix:s.natReg 6032=g.metadata.suffix
 metadataStack:s.natReg 6033=g.metadata.stack
 metadataDirectory:s.natReg 6034=g.metadata.directory
 batch:s.natReg 6035=g.gather.directory
 child:s.natReg 6029=g.gather.buffer
 frontier:s.natReg 6037=F
 inverseSource:s.natReg 6032=g.inverse.layout.source
 inverseStack:s.natReg 6033=g.inverse.layout.stack
 inverseInverse:s.natReg 6036=g.inverse.layout.inverse
 inverseTemporary:s.natReg 6033=g.inverse.layout.destination
 inverseFinal:s.natReg 6026=g.inverse.destination

lemma count_bound {W F R:ℕ} (g:Context W F R) (s:State) (h:Input g s):s.natReg 102+1 ≤ g.metadata.B:=by
 have axes:g.metadata.ell=g.packing.ell:=g.metadataLength.symm.trans g.physicalLength
 have a:=g.packing.suffixBelow
 have b:=g.packing.stackBelow
 have c:=g.packing.inverseFit
 rw[h.count,axes,g.packingB] at *
 omega
lemma safe (B:ℕ) (s:State) (count:s.natReg 102+1 ≤ B) (wb:WordBound B s) (_one:1 ≤ B):
 readable block s ∧peak block s ≤ B:=by
 have h103:=wb.2.1 103
 have h26:=wb.2.1 6026;have h28:=wb.2.1 6028;have h29:=wb.2.1 6029
 have h30:=wb.2.1 6030;have h31:=wb.2.1 6031;have h32:=wb.2.1 6032
 have h33:=wb.2.1 6033;have h34:=wb.2.1 6034;have h35:=wb.2.1 6035
 have h36:=wb.2.1 6036;have h37:=wb.2.1 6037
 simp[block,head,UniformInverseHeaderInstallation.block,readable,peak,Op.readable,Op.peak,
  Op.apply,writeNat,next]
 omega

def Changed (q:ℕ):Prop:=q=5990 ∨q=5991 ∨(5820 ≤ q ∧q ≤ 5827) ∨q=3201 ∨q=3202 ∨
 q=3213 ∨q=3214 ∨q=3215 ∨q=4441 ∨q=4442 ∨q=4530 ∨q=4531 ∨q=5800 ∨q=5801 ∨(5900 ≤ q ∧q ≤ 5911)
lemma apply_append (a b:List Op) (s:State):applyBlock (a++b) s=applyBlock b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>rfl
 | cons a rest ih=>exact ih (a.apply s)

lemma head_frame (s:State):(applyBlock head s).natHeap=s.natHeap ∧
 (applyBlock head s).scalarHeap=s.scalarHeap ∧(applyBlock head s).scalarReg=s.scalarReg ∧
 (applyBlock head s).outputs=s.outputs ∧(applyBlock head s).rootOrders=s.rootOrders ∧
 (∀q,¬Changed q→(applyBlock head s).natReg q=s.natReg q):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro q outside
 unfold Changed at outside
 simp (disch:=omega) [head,applyBlock,Op.apply,writeNat,next]
lemma frame (s:State):(applyBlock block s).natHeap=s.natHeap ∧
 (applyBlock block s).scalarHeap=s.scalarHeap ∧(applyBlock block s).scalarReg=s.scalarReg ∧
 (applyBlock block s).outputs=s.outputs ∧(applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,¬Changed q→(applyBlock block s).natReg q=s.natReg q):=by
 rw[block,apply_append]
 have a:=head_frame s
 have b:=UniformInverseHeaderInstallation.frame (applyBlock head s)
 exact ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,b.2.2.2.1.trans a.2.2.2.1,
  b.2.2.2.2.1.trans a.2.2.2.2.1,fun q outside=>
   (b.2.2.2.2.2 q (by unfold Changed at outside;omega)).trans (a.2.2.2.2.2 q outside)⟩
lemma kept (s:State) (q:ℕ) (low:q < 5900):(applyBlock block s).natReg q=(applyBlock head s).natReg q:=by
 rw[block,apply_append]
 exact (UniformInverseHeaderInstallation.frame (applyBlock head s)).2.2.2.2.2 q (Or.inl low)

lemma inverse_input {W F R:ℕ} (g:Context W F R) (s:State) (h:Input g s):
 UniformInverseHeaderInstallation.Input g.inverse g.scatter.directory (applyBlock head s):=by
 have axes:g.metadata.ell=g.packing.ell:=g.metadataLength.symm.trans g.physicalLength
 constructor <;>simp[head,applyBlock,Op.apply,writeNat,next]
 · exact h.volume.trans g.inverseVolume
 · exact h.count.trans axes |>.trans (g.physicalLength.symm.trans g.inverseLength)
 · exact h.inverseSource
 · exact h.suffix.trans g.inverseSuffix.symm
 · exact h.batch.trans g.scatterDirectory.symm
 · exact h.rows.trans g.inverseRows.symm
 · exact h.inverseStack
 · exact h.inverseInverse
 · exact h.inverseTemporary
 · exact h.inverseFinal

lemma ready {W F R:ℕ} (g:Context W F R) (v:ℕ→Fin g.packing.volume→Scalar) (s:State)
 (h:Input g s) (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s) (constants:UniformBinaryCStageMachine.Constants s):
 Ready g 0 v (applyBlock block s):=by
 have axes:g.metadata.ell=g.packing.ell:=g.metadataLength.symm.trans g.physicalLength
 have hn:=(frame s).1
 have hs:=(frame s).2.1
 have banksU:=UniformGlobalRolePackingMachine.banks_transfer g.packing g.physical g.physicalLength banks
  (fun q _ _ _=>congrFun hn q) g.widthsBelow g.permutationsBelow
 have sourceU:UniformGlobalRolePackingMachine.Source g.packing v (applyBlock block s):=by
  intro r hr j
  exact (congrFun hs _).trans (source r hr j)
 have constantsU:UniformBinaryCStageMachine.Constants (applyBlock block s):=
  ⟨(congrFun hs 1).trans constants.1,(congrFun hs 2).trans constants.2⟩
 refine ⟨?_,banksU,sourceU,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,constantsU⟩
 · constructor
   all_goals rw[kept s _ (by omega)]
   all_goals simp[head,applyBlock,Op.apply,writeNat,next]
   · exact h.volume
   · exact h.source
   · exact h.packed
   · exact h.count.trans axes
   · exact h.rows
   · exact h.suffix
   · exact h.stack
   · exact h.inverse
 · have keep:¬Changed 102:=by unfold Changed;omega
   rw[(frame s).2.2.2.2.2 102 keep]
   exact h.count
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.rows
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.metadataRows
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.metadataSuffix
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.metadataStack
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.metadataDirectory
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.batch
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.child
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.packed.trans g.gatherSource.symm
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using (h.volume.trans g.packingVolume).trans g.gatherVolume.symm
 · rw[kept s _ (by omega)]
   simp[head,applyBlock,Op.apply,writeNat,next]
 · rw[kept s _ (by omega)]
   simpa[head,applyBlock,Op.apply,writeNat,next] using h.frontier
 · rw[block,apply_append]
   exact UniformInverseHeaderInstallation.args g.inverse (applyBlock head s) (inverse_input g s h)

/-- The actual32 instructions install the entire kernel ABI in any placed
fixed program, retaining both produced banks and exact scalar tags. -/
theorem execution {W F R n start:ℕ} (g:Context W F R) (program:Program) (x:Fin n→ℂ)
 (v:ℕ→Fin g.packing.volume→Scalar) (s:State) (h:Input g s)
 (banks:UniformGlobalRolePackingMachine.Banks g.packing g.physical s)
 (source:UniformGlobalRolePackingMachine.Source g.packing v s) (constants:UniformBinaryCStageMachine.Constants s)
 (code:BlockAt block program start) (pc:s.pc=start) (room:start+32 ≤ g.metadata.B)
 (wb:WordBound g.metadata.B s):
 BoundedRuns program n x g.metadata.B s 32 (applyBlock block s) ∧Ready g 0 v (applyBlock block s) ∧
 (applyBlock block s).natHeap=s.natHeap ∧(applyBlock block s).scalarHeap=s.scalarHeap ∧
 (applyBlock block s).scalarReg=s.scalarReg ∧(applyBlock block s).outputs=s.outputs ∧
 (applyBlock block s).rootOrders=s.rootOrders ∧
 (∀q,¬Changed q→(applyBlock block s).natReg q=s.natReg q):=by
 have hs:=safe g.metadata.B s (count_bound g s h) wb (by omega)
 exact ⟨block_runs block program start n g.metadata.B x s code pc wb room hs.1 hs.2,
  ready g v s h banks source constants,frame s⟩
end
end ExactFourierCircuits.UniformKernelHeaderInstallation
