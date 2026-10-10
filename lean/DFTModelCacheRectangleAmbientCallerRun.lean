import DFTModelCacheRectangleAmbientCallerProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
attribute [local irreducible] DFTModelCacheRectangleCaller.program DFTModelCacheAmbientPool.program

theorem argument_run (x:Context.T) :
 run argument x=⟨argumentValue x,75,1,True⟩ := by
 simp only [argument,offset,original,coefficientHeader,localInput,spectrum,rows,
  DFTModelCacheMatchingProduced.rawRows,DFTModelCacheRectangleCaller.row,
  DFTModelCacheRectangleCaller.rows,run,Code.run,Atom.run,Bill.one,Bill.word,
  Bill.pass,Bill.pay,max_zero,zero_max,and_true,argumentValue,
  localInputValue,DFTModelCacheRectangleCaller.rowValue,Ty.blank]

theorem program_run (x:Input.T) :
 let first:=run DFTModelCacheRectangleCaller.program x.2
 let context:Context.T:=(x.1,first.val)
 let ambient:=run DFTModelCacheAmbientPool.program (argumentValue context)
 run program x=⟨(context,ambient.val),first.work+ambient.work+83,
  max first.peak (max 1 ambient.peak),first.valid∧ambient.valid⟩ := by
 dsimp only
 rw [program,comp_run]
 simp only [prepare,fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
  finish,argument_run,max_zero,zero_max,true_and,and_true]
 congr 1
 omega

/-- Pure composition boundary: every source fact is supplied by the two
actual producer theorems in the concrete specialization. -/
theorem composition {x:Input.T} {y:DFTModelCacheAmbientPool.Input.T}
 {aw bw ap bp:ℕ} {property:DFTModelCacheAmbientPool.Output.T→Prop}
 (args:argumentValue (x.1,(run DFTModelCacheRectangleCaller.program x.2).val)=y)
 (first:(run DFTModelCacheRectangleCaller.program x.2).valid ∧
  (run DFTModelCacheRectangleCaller.program x.2).work≤aw ∧
  (run DFTModelCacheRectangleCaller.program x.2).peak≤ap)
 (second:(run DFTModelCacheAmbientPool.program y).valid ∧
  (run DFTModelCacheAmbientPool.program y).work≤bw ∧
  (run DFTModelCacheAmbientPool.program y).peak≤bp ∧
  property (run DFTModelCacheAmbientPool.program y).val) :
 (run program x).valid ∧ (run program x).work≤aw+bw+83 ∧
 (run program x).peak≤ max ap (max 1 bp) ∧
 (run program x).val.1=(x.1,(run DFTModelCacheRectangleCaller.program x.2).val) ∧
 property (run program x).val.2 := by
 rw [program_run]
 dsimp only
 rw [args]
 exact ⟨⟨first.1,second.1⟩,Nat.add_le_add_right (Nat.add_le_add first.2.1 second.2.1) 83,
  max_le_max first.2.2 (max_le_max_left 1 second.2.2.1),rfl,second.2.2.2⟩

end
end ExactFourierCircuits.DFTModelCacheRectangleAmbientCaller
