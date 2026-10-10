import DFTModelGlobalKernelAssemblyProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelAssembly
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine
open scoped BigOperators
noncomputable section

attribute [local irreducible] move sectors DFTModelGlobalSectorPreparation.withDirectory
 DFTModelSectorMaterialization.joined gatherArgument sectorArgument mergeArgument scatterArgument

theorem preparation_run (x:Input.T) :
 run preparation x=(run DFTModelGlobalSectorPreparation.withDirectory x.1).pay 2 0 := by
 rw [preparation,DFTModelSectorMaterialization.comp_run]
 simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
 omega

theorem gather_run (x:Input.T) (p:Preparation.T) :
 run gather (x,p)=(run move (x.2.2.1,(p.1.1,(p.1.2.2.1,x.2.2.2)))).pay 32 0 := by
 rw [gather,DFTModelSectorMaterialization.comp_run,gatherArgument_run]
 simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
 congr 1; omega

theorem solve_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) :
 run solve ((x,p),v)=
 (run sectors (x.2.1,(x.2.2.1,(p.1.1,(p.1.2.2.2,v))))).pay 40 0 := by
 rw [solve,DFTModelSectorMaterialization.comp_run,sectorArgument_run]
 simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
 congr 1; omega

theorem merge_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) (ps:Tape (Tape Tagged.T)) :
 run merge (((x,p),v),ps)=
 (run (DFTModelSectorMaterialization.joined Tagged) (x.2.2.1,(p.2,(ps,v)))).pay 26 0 := by
 rw [merge,DFTModelSectorMaterialization.comp_run,mergeArgument_run]
 simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
 congr 1; omega

theorem scatter_run (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T)
 (ps:Tape (Tape Tagged.T)) (m:(Ty.p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged)).T) :
 run scatter ((((x,p),v),ps),m)=
 (run move (x.2.2.1,(p.1.1,(p.1.2.1,m.2)))).pay 44 0 := by
 rw [scatter,DFTModelSectorMaterialization.comp_run,scatterArgument_run]
 simp only [Bill.pass,Bill.pay,true_and,zero_max,max_zero]
 congr 1; omega

theorem retain_run {a b:Ty} (f:Prog false a b) (x:a.T) :
 run (.fork (.atom .id) f) x=
 ((run f x).pass (fun y=>Bill.one (x,y))).pay 1 0 := by
 simp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,
  true_and,and_true,zero_max,max_zero]
 congr 1;omega

attribute [local irreducible] preparation gather solve merge scatter

/-- Every stage is executed once; the continuation uses its produced value. -/
theorem program_run (x:Input.T) :
 run program x=
 ((run preparation x).pass (fun p=>
  ((run gather (x,p)).pass (fun v=>
   ((run solve ((x,p),v)).pass (fun ps=>
    ((run merge (((x,p),v),ps)).pass (fun m=>
      run (.fork (.atom .id) scatter) ((((x,p),v),ps),m))).pay 3 0)).pay 3 0)).pay 3 0)).pay 3 0 := by
 simp only [program,DFTModelSectorMaterialization.bind_run]

def prepared (x:Input.T) : Preparation.T :=
 (run DFTModelGlobalSectorPreparation.withDirectory x.1).val
def packed (x:Input.T) : Tape Tagged.T :=
 moved x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.1 x.2.2.2
def compactPatches (x:Input.T) : Tape (Tape Tagged.T) :=
 patches x.2.1 x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.2 (packed x)
def materialized (x:Input.T) :
 (Ty.p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged)).T :=
 (run (DFTModelSectorMaterialization.joined Tagged)
  (x.2.2.1,((prepared x).2,(compactPatches x,packed x)))).val
def returned (x:Input.T) : Tape Tagged.T :=
 moved x.2.2.1 (prepared x).1.1 (prepared x).1.2.1 (materialized x).2

theorem preparation_value (x:Input.T) : (run preparation x).val=prepared x := by
 rw [preparation_run];rfl
theorem gather_value (x:Input.T) (p:Preparation.T) :
 (run gather (x,p)).val=moved x.2.2.1 p.1.1 p.1.2.2.1 x.2.2.2 := by
 rw [gather_run];exact move_value _ _ _ _
theorem solve_value (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) :
 (run solve ((x,p),v)).val=patches x.2.1 x.2.2.1 p.1.1 p.1.2.2.2 v := by
 rw [solve_run];exact sectors_value _ _ _ _ _
theorem merge_value (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T) (ps:Tape (Tape Tagged.T)) :
 (run merge (((x,p),v),ps)).val=
 (run (DFTModelSectorMaterialization.joined Tagged) (x.2.2.1,(p.2,(ps,v)))).val := by
 rw [merge_run];rfl
theorem scatter_value (x:Input.T) (p:Preparation.T) (v:Tape Tagged.T)
 (ps:Tape (Tape Tagged.T)) (m:(Ty.p (DFTModelSectorMaterialization.JoinedInput Tagged) (Ty.a Tagged)).T) :
 (run scatter ((((x,p),v),ps),m)).val=moved x.2.2.1 p.1.1 p.1.2.1 m.2 := by
 rw [scatter_run];exact move_value _ _ _ _

theorem program_value (x:Input.T) :
 (run program x).val=(((((x,prepared x),packed x),compactPatches x),materialized x),returned x) := by
 rw [program_run]
 simp only [Bill.pass,Bill.pay,retain_run,Bill.one]
 rw [preparation_value]
 rw [gather_value]
 rw [solve_value]
 rw [merge_value]
 rw [scatter_value]
 rfl

/-- Exact work, including both movements and each real closed saving invocation. -/
theorem program_work (x:Input.T) :
 (run program x).work=
 (run DFTModelGlobalSectorPreparation.withDirectory x.1).work+
 106*(x.2.2.1*(prepared x).1.1)+68*(prepared x).1.2.2.2.len+
 (∑j∈Finset.range (prepared x).1.2.2.2.len,
   (run DFTModelSectorTranspose.saving
    (sectorArgs x.2.1 x.2.2.1 (prepared x).1.1 (prepared x).1.2.2.2 (packed x) j)).work)+
 (run (DFTModelSectorMaterialization.joined Tagged)
  (x.2.2.1,((prepared x).2,(compactPatches x,packed x)))).work+190 := by
 rw [program_run]
 simp only [Bill.pass,Bill.pay,retain_run,Bill.one]
 rw [preparation_value]
 rw [gather_value]
 rw [solve_value]
 rw [merge_value]
 rw [preparation_run,gather_run,solve_run,merge_run,scatter_run]
 simp only [Bill.pay]
 rw [move_work,sectors_work,move_work]
 dsimp only [prepared,packed,compactPatches]
 omega

end
end ExactFourierCircuits.DFTModelGlobalKernelAssembly
