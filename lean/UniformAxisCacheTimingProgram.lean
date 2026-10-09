import UniformAxisCacheTimingConductor
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheTimingProgram
open UniformMachine UniformAssembly UniformLocalCacheTimingPlacement
noncomputable section

def program:Program:=UniformAxisCachePrepareProgram.program.map (relocate 0 69)++
 UniformLocalCacheTimingConductor.program.map (terminalRelocate 69)
lemma program_length:program.length=370:=by
 simp only[program,List.length_append,List.length_map,UniformAxisCachePrepareProgram.program_length,
  UniformLocalCacheTimingConductor.program_length]
lemma prepare_code:CodeAt UniformAxisCachePrepareProgram.program program 0 69:=by
 have h:=embed_code [] UniformAxisCachePrepareProgram.program
  (UniformLocalCacheTimingConductor.program.map (terminalRelocate 69)) 69
 simpa only[embed,List.length_nil,List.nil_append,program] using h
lemma conductor_code:TerminalCodeAt UniformLocalCacheTimingConductor.program program 69:=by
 intro i hi
 rw[program,List.getElem?_append_right (by rw[List.length_map,UniformAxisCachePrepareProgram.program_length];omega)]
 rw[List.length_map,UniformAxisCachePrepareProgram.program_length,Nat.add_sub_cancel_left,List.getElem?_map]
lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have allowed:=UniformAxisCachePrepareProgram.program_natOnly a ha
   cases a <;>simp_all[relocate,UniformLocalRectangleDescriptors.NatOnly]
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have allowed:=UniformLocalCacheTimingConductor.program_natOnly a ha
   cases a <;>simp_all[terminalRelocate,relocate,UniformLocalRectangleDescriptors.NatOnly]

def changed(q:ℕ):Prop:= (290≤q∧q<4295)∨(6500≤q∧q<6600)∨
 (6803≤q∧q≤6830)∨(6175≤q∧q≤6177)∨q=6160
instance(q:ℕ):Decidable (changed q):=by unfold changed;infer_instance

def destinations(ins:Instruction):Prop:=match ins with
 | .natLiteral d _|.natBinary _ d _ _|.loadNat d _=>changed d
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by cases ins <;>simp[destinations] <;>infer_instance
lemma program_destinations:∀ins∈program,destinations ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have bounds:=UniformAxisCachePrepareProgram.program_destinations a ha
   cases a <;>simp_all[relocate,destinations,changed,UniformAxisCachePrepareProgram.destinations,
    UniformAxisCachePrepareProgram.destination]
   all_goals omega
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   have bounds:=UniformLocalCacheTimingConductor.program_destinations a ha
   cases a <;>simp_all[terminalRelocate,relocate,destinations,changed,UniformLocalCacheTimingConductor.destinations]
   all_goals omega
lemma program_keeps(q:ℕ)(hq:¬changed q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have bounds:=program_destinations ins hi
 have allowed:=program_natOnly ins hi
 cases ins <;>simp only[destinations] at bounds
 all_goals simp only[UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only[UniformNewtonTableMachine.KeepsNat]
 all_goals aesop

local instance(ins:Instruction):Decidable (UniformNewtonTableMachine.KeepsNat 4200 ins):=by
 cases ins <;>simp only[UniformNewtonTableMachine.KeepsNat] <;>infer_instance
lemma relocate_keeps (q base ret:ℕ)(ins:Instruction)(h:UniformNewtonTableMachine.KeepsNat q ins):
 UniformNewtonTableMachine.KeepsNat q (relocate base ret ins):=by
 cases ins <;>simp only[relocate,UniformNewtonTableMachine.KeepsNat] at h ⊢ <;>exact h
lemma terminal_keeps (q base:ℕ)(ins:Instruction)(h:UniformNewtonTableMachine.KeepsNat q ins):
 UniformNewtonTableMachine.KeepsNat q (terminalRelocate base ins):=by
 cases ins <;>simp only[terminalRelocate,relocate,UniformNewtonTableMachine.KeepsNat] at h ⊢ <;>exact h
lemma producer_keeps_axis_index:∀ins∈UniformLocalCacheTreeMachine.program,UniformNewtonTableMachine.KeepsNat 4200 ins:=by
 have checked:UniformLocalCacheTreeMachine.program.all
  (fun ins=>decide (UniformNewtonTableMachine.KeepsNat 4200 ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
lemma conductor_keeps_axis_index:∀ins∈UniformLocalCacheTimingConductor.program,UniformNewtonTableMachine.KeepsNat 4200 ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · rcases List.mem_append.mp hi with hi|hi
   · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
     exact relocate_keeps _ _ _ a (producer_keeps_axis_index a ha)
   · have checked:(UniformLocalCacheTimingConductor.installer.map UniformTensorMonomialMachine.Op.code).all
      (fun ins=>decide (UniformNewtonTableMachine.KeepsNat 4200 ins))=true:=by decide
     exact of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   exact terminal_keeps _ _ a (UniformCacheTimingControl.keeps_nat 4200 (Or.inl (by omega)) a ha)
lemma program_keeps_axis_index:∀ins∈program,UniformNewtonTableMachine.KeepsNat 4200 ins:=by
 intro ins hi
 rcases List.mem_append.mp hi with hi|hi
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   exact relocate_keeps _ _ _ a (UniformAxisCachePrepareProgram.program_keeps 4200
    (by unfold UniformAxisCachePrepareProgram.destination;omega) a ha)
 · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hi
   exact terminal_keeps _ _ a (conductor_keeps_axis_index a ha)
lemma axis_index_frame {n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s t u):u.natReg 4200=s.natReg 4200:=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes program_keeps_axis_index
end
end ExactFourierCircuits.UniformAxisCacheTimingProgram
