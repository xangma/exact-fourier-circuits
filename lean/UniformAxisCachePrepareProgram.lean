import UniformAxisCacheInstalledAddresses
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCachePrepareProgram
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace A
export UniformAxisCacheAllocationMachine (program)
end A
namespace I
export UniformAxisCachePoolInstaller (ops)
end I

noncomputable section
/-- Continuous58 allocator then ten charged caller-header copies. The final
halt is a diagnostic boundary; frontier advancement remains separate. -/
def program:Program:=A.program.map (relocate 0 58)++I.ops.map Op.code++[.halt]
lemma program_length:program.length=69:=rfl
lemma allocator_code:CodeAt A.program program 0 58:=by
 have h:=embed_code [] A.program (I.ops.map Op.code++[.halt]) 58
 simpa only [embed,List.length_nil,List.nil_append,List.append_assoc,program] using h
lemma installer_code:BlockAt I.ops program 58:=by
 intro i hi
 change i<10 at hi
 interval_cases i <;>rfl
lemma halt_at:program[68]?=some .halt:=rfl

lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 have checked:program.all (fun ins=>decide (UniformLocalRectangleDescriptors.NatOnly ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
def destination(q:ℕ):Prop:=
 (6540≤q∧q≤6551)∨(6803≤q∧q≤6830)∨(6175≤q∧q≤6177)∨(4270≤q∧q≤4274)∨q=6160
instance(q:ℕ):Decidable (destination q):=by unfold destination;infer_instance
def destinations(ins:Instruction):Prop:=match ins with
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>destination d
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by cases ins <;>simp [destinations] <;>infer_instance
lemma program_destinations:∀ins∈program,destinations ins:=by
 have checked:program.all (fun ins=>decide (destinations ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp checked) ins hi)
lemma program_keeps(q:ℕ)(hq:¬destination q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have bounds:=program_destinations ins hi
 have allowed:=program_natOnly ins hi
 cases ins <;>simp only [destinations] at bounds
 all_goals simp only [UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals aesop
end
end ExactFourierCircuits.UniformAxisCachePrepareProgram
