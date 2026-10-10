import DFTModelCacheRectangleCallerProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

theorem row_run (x:Input.T) (j:ℕ) : run (row j) x=⟨rowValue x j,9,j,True⟩ := by
 simp [row,rows,rowValue,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem dimensions_run (x:Input.T) :
 run dimensions x=⟨(rowValue x 2,rowValue x 3),19,3,True⟩ := by
 rw [dimensions,fork_run,row_run,row_run]
 simp [Bill.one,Bill.pass]

theorem argument_value (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 (run argument (x,v)).val=argumentValue x v := by
 simp [argument,control,metadata,geometry,heightInput,seedRadix,master,C,P,depth,color,
  enabled,original,configuration,root,bases,slot,row,rows,dimensions,
  DFTModelCacheTopology.k,DFTModelCacheTopology.n,DFTModelCacheTopology.a,
  DFTModelCacheTopology.crossCount,DFTModelCacheTopology.gates,DFTModelCacheTopology.nat,
  argumentValue,controlValue,metadataValue,geometryValue,heightValue,gateValue,rowValue,
  run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem argument_work (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 (run argument (x,v)).work=265 := by
 simp [argument,control,metadata,geometry,heightInput,seedRadix,master,C,P,depth,color,
  enabled,original,configuration,root,bases,slot,row,rows,dimensions,
  DFTModelCacheTopology.k,DFTModelCacheTopology.n,DFTModelCacheTopology.a,
  DFTModelCacheTopology.crossCount,DFTModelCacheTopology.gates,DFTModelCacheTopology.nat,
  run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

theorem argument_valid (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 (run argument (x,v)).valid := by
 simp [argument,control,metadata,geometry,heightInput,seedRadix,master,C,P,depth,color,
  enabled,original,configuration,root,bases,slot,row,rows,dimensions,
  DFTModelCacheTopology.k,DFTModelCacheTopology.n,DFTModelCacheTopology.a,
  DFTModelCacheTopology.crossCount,DFTModelCacheTopology.gates,DFTModelCacheTopology.nat,
  run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]

attribute [local irreducible] Code.run argument prepare finish program DFTModelCacheTopology.prepare
 DFTModelCacheSelectedPhysicalRowsCaller.program

theorem prepare_run (x:Input.T) : run prepare x=
 let c:=run DFTModelCacheTopology.prepare (rowValue x 2,rowValue x 3)
 ⟨(x,c.val),c.work+22,max 3 c.peak,c.valid⟩ := by
 rw [prepare,fork_run,comp_run,atom_run,dimensions_run]
 simp only [Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,zero_max,max_zero,and_true]
 congr 1
 omega

private theorem finish_bill {s t u:Ty} (x:s.T) (a:Bill u.T) (f:Bill t.T)
 (hv:a.valid) :
 (⟨(x,f.val),265+f.work+3,max a.peak f.peak,a.valid ∧ f.valid⟩ : Bill (p s t).T)=
 ⟨(x,f.val),f.work+268,max a.peak f.peak,f.valid⟩ := by
 have hw:265+f.work+3=f.work+268:=by omega
 rw [hw]
 simp only [hv,true_and]

theorem finish_run (x:Input.T) (v:DFTModelCacheTopology.Config.T) : run finish (x,v)=
 let f:=run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x v)
 ⟨((x,v),f.val),f.work+268,max (run argument (x,v)).peak f.peak,f.valid⟩ := by
 have h:=DFTModelCacheColorRebase.retained_comp_run argument
  DFTModelCacheSelectedPhysicalRowsCaller.program (x,v)
 rw [argument_value,argument_work] at h
 rw [finish]
 exact h.trans (finish_bill (s:=Context) (t:=DFTModelCacheSelectedPhysicalRowsCaller.Output)
  (u:=DFTModelCacheSelectedPhysicalRowsCaller.Input) (x,v) (run argument (x,v))
  (run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x v)) (argument_valid x v))


private theorem composition_value {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
 (run (.comp f g) x).val=(run g (run f x).val).val := by rw [comp_run]; rfl
private theorem composition_work {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
 (run (.comp f g) x).work=(run f x).work+(run g (run f x).val).work+1 := by rw [comp_run]; rfl
private theorem composition_valid {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
 (run (.comp f g) x).valid ↔ (run f x).valid ∧ (run g (run f x).val).valid := by rw [comp_run]; rfl
private theorem composition_peak {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
 (run (.comp f g) x).peak=max (max (run f x).peak (run g (run f x).val).peak) 0 := by rw [comp_run]; rfl

theorem program_value (x:Input.T) :
 (run program x).val=
 let c:=run DFTModelCacheTopology.prepare (rowValue x 2,rowValue x 3)
 ((x,c.val),(run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x c.val)).val) := by
 rw [program,composition_value,prepare_run,finish_run]

theorem program_work (x:Input.T) :
 (run program x).work=
 let c:=run DFTModelCacheTopology.prepare (rowValue x 2,rowValue x 3)
 c.work+(run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x c.val)).work+291 := by
 rw [program,composition_work,prepare_run,finish_run]
 dsimp only
 omega

theorem program_valid (x:Input.T) :
 (run program x).valid ↔
 let c:=run DFTModelCacheTopology.prepare (rowValue x 2,rowValue x 3)
 c.valid ∧ (run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x c.val)).valid := by
 rw [program,composition_valid,prepare_run,finish_run]

theorem program_peak (x:Input.T) :
 (run program x).peak=
 let c:=run DFTModelCacheTopology.prepare (rowValue x 2,rowValue x 3)
 max (max 3 c.peak) (max (run argument (x,c.val)).peak
  (run DFTModelCacheSelectedPhysicalRowsCaller.program (argumentValue x c.val)).peak) := by
 rw [program,composition_peak,prepare_run,finish_run]
 dsimp only
 exact max_zero _


end
end ExactFourierCircuits.DFTModelCacheRectangleCaller
