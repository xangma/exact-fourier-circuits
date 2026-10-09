import UniformForwardMatchingFactorHeaderCount
import UniformForwardMatchingFactorTensorBridge
import UniformInverseMatchingFactorReload
import UniformLocalCacheSlotHeaderMachine
import UniformReciprocalMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalFactorDispatchMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace FH
abbrev program := UniformForwardMatchingFactorHeaderPreparation.program
end FH
namespace BC
abbrev program := UniformLocalBroadcastPoolMachine.program
end BC
namespace IV
abbrev program := UniformInverseMatchingFactorPreparation.reloadProgram
end IV

/-- Reads the two stored control bits; the inverse destination is an ordinary
caller address. Neither branch selection nor a factor/count table is supplied. -/
def boot : List Op := [.literal 6210 0,.literal 6211 2,
 .add 4460 6200 6210,.add 6212 4421 6210,.getNat 6213 6212,
 .add 6212 6212 6211,.getNat 6214 6212]
def head : Program := boot.map Op.code ++
 [.branchLT 6210 6213 439 8,.branchLT 6210 6214 680 9]
def beforeBroadcast : Program := head ++ FH.program.map (relocate 9 1155)
def beforeInverse : Program := beforeBroadcast ++ BC.program.map (relocate 439 1155)
def inverseSetup:List Op:=[.add 5847 4460 6210]
def beforeInverseBody:Program:=beforeInverse++inverseSetup.map Op.code
def program : Program := beforeInverseBody ++ IV.program.map (relocate 681 1155) ++ [.halt]
lemma boot_length : boot.length=7 := rfl
lemma head_length : head.length=9 := by simp [head,boot_length]
lemma beforeBroadcast_length : beforeBroadcast.length=439 := by
 simp [beforeBroadcast,head_length,FH.program,UniformForwardMatchingFactorHeaderPreparation.program_length]
lemma beforeInverse_length : beforeInverse.length=680 := by
 simp [beforeInverse,beforeBroadcast_length,BC.program,UniformLocalBroadcastPoolMachine.program_length]
lemma beforeInverseBody_length:beforeInverseBody.length=681:=by
 simp [beforeInverseBody,beforeInverse_length,inverseSetup]
lemma program_length : program.length=1156 := by
 simp [program,beforeInverseBody_length,IV.program,UniformInverseMatchingFactorPreparation.reloadProgram_length]
section Code
attribute [local irreducible] UniformForwardMatchingFactorHeaderPreparation.program
 UniformLocalBroadcastPoolMachine.program UniformInverseMatchingFactorPreparation.reloadProgram
lemma boot_code : BlockAt boot program 0 := by
 intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma broadcast_branch : program[7]?=some (.branchLT 6210 6213 439 8) := rfl
lemma inverse_branch : program[8]?=some (.branchLT 6210 6214 680 9) := rfl
lemma forward_code : CodeAt FH.program program 9 1155 := by
 let rest:=BC.program.map (relocate 439 1155)++inverseSetup.map Op.code++IV.program.map (relocate 681 1155)++[.halt]
 have eq:program=head++FH.program.map (relocate 9 1155)++rest:=by
  simp only [program,beforeInverseBody,beforeInverse,beforeBroadcast,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code head rest _ 9 1155 head_length
lemma broadcast_code : CodeAt BC.program program 439 1155 := by
 let rest:=inverseSetup.map Op.code++IV.program.map (relocate 681 1155)++[.halt]
 have eq:program=beforeBroadcast++BC.program.map (relocate 439 1155)++rest:=by
  simp only [program,beforeInverseBody,beforeInverse,rest,List.append_assoc]
 rw [eq]
 exact UniformChunkRowTableMachine.segment_code beforeBroadcast rest _ 439 1155 beforeBroadcast_length
lemma inverseSetup_code:BlockAt inverseSetup program 680:=by
 let rest:=IV.program.map (relocate 681 1155)++[.halt]
 have eq:program=beforeInverse++inverseSetup.map Op.code++rest:=by
  simp only [program,beforeInverseBody,rest,List.append_assoc]
 rw [eq]
 exact UniformLocalBroadcastPoolMachine.segment_block beforeInverse rest inverseSetup 680 beforeInverse_length
lemma inverse_code : CodeAt IV.program program 681 1155 :=
 UniformChunkRowTableMachine.segment_code beforeInverseBody [.halt] _ 681 1155 beforeInverseBody_length
lemma halt_at : program[1155]?=some .halt := by
 rw [program,List.getElem?_append_right (by
  simp [beforeInverseBody_length,IV.program,UniformInverseMatchingFactorPreparation.reloadProgram_length])]
 simp only [List.length_append,List.length_map,beforeInverseBody_length,IV.program,
  UniformInverseMatchingFactorPreparation.reloadProgram_length];rfl

end Code

/-- A finite bytecode footprint, independent of any execution or input. -/
def protectedInstruction : Instruction → Bool
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ =>
   decide (d<100 ∨106<d) && decide (d<5100)
 | _ => true
lemma protected_relocate (base ret:ℕ) (i:Instruction):
 protectedInstruction (relocate base ret i)=protectedInstruction i := by cases i <;>rfl
lemma all_relocate (p:Program) (base ret:ℕ):
 (p.map (relocate base ret)).all protectedInstruction=p.all protectedInstruction := by
 simp only [List.all_map,Function.comp_def,protected_relocate]
lemma forward_footprint : FH.program.all protectedInstruction=true := by
 simp only [FH.program,UniformForwardMatchingFactorHeaderPreparation.program,
  UniformForwardMatchingFactorPreparation.program,UniformForwardMatchingFactorPreparation.beforeFactors,
  UniformForwardMatchingFactorPreparation.beforeTranslate,List.all_append,all_relocate,Bool.and_eq_true]
 repeat' first | apply And.intro | decide
lemma broadcast_footprint : BC.program.all protectedInstruction=true := by decide
lemma inverse_footprint : IV.program.all protectedInstruction=true := by
 simp only [IV.program,UniformInverseMatchingFactorPreparation.reloadProgram,
  UniformInverseMatchingFactorPreparation.wholeProgram,
  UniformInverseMatchingFactorPreparation.prefixProgram,
  UniformInverseMatchingFactorPreparation.program,
  UniformInverseMatchingFactorPreparation.beforeFactors,
  UniformForwardMatchingFactorPreparation.beforeTranslate,
  List.all_append,all_relocate,Bool.and_eq_true]
 repeat' first | apply And.intro | decide
lemma footprint_keeps {p:Program} (h:p.all protectedInstruction=true) (q:ℕ)
 (hq:(100≤q ∧q≤106) ∨5100≤q) : ∀ins∈p,UniformNewtonTableMachine.KeepsNat q ins := by
 intro ins member
 have hi:=List.all_eq_true.mp h ins member
 cases ins <;>simp only [protectedInstruction,UniformNewtonTableMachine.KeepsNat] at *
 all_goals simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
 all_goals omega
lemma program_keeps (q:ℕ) (hq:(100≤q ∧q≤106) ∨5100≤q)
 (hz:q≠4460) (hr:q≠5847) (hs:∀ (i : ℕ), 6210 ≤ i → i ≤ 6214 → q ≠ i) :
 ∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins := by
 have hb:∀ins∈head,UniformNewtonTableMachine.KeepsNat q ins:=by
  intro ins h
  change ins∈[.natLiteral 6210 0,.natLiteral 6211 2,.natBinary .add 4460 6200 6210,
   .natBinary .add 6212 4421 6210,.loadNat 6213 6212,.natBinary .add 6212 6212 6211,
   .loadNat 6214 6212,.branchLT 6210 6213 439 8,.branchLT 6210 6214 680 9] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h <;>subst ins
  all_goals simp only [UniformNewtonTableMachine.KeepsNat]
  all_goals first | trivial | exact Ne.symm hz | exact Ne.symm (hs _ (by omega) (by omega))
 have hf:=UniformReciprocalMachine.keeps_relocate q 9 1155 (footprint_keeps forward_footprint q hq)
 have hc:=UniformReciprocalMachine.keeps_relocate q 439 1155 (footprint_keeps broadcast_footprint q hq)
 have hi:=UniformReciprocalMachine.keeps_relocate q 681 1155 (footprint_keeps inverse_footprint q hq)
 have header:∀ins∈inverseSetup.map Op.code,UniformNewtonTableMachine.KeepsNat q ins:=by
  simp only [inverseSetup,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  intro ins eq;subst ins;exact Ne.symm hr
 have halt:∀ins∈([.halt]:Program),UniformNewtonTableMachine.KeepsNat q ins:=by
  simp [UniformNewtonTableMachine.KeepsNat]
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q (UniformReciprocalMachine.keeps_append q hb hf) hc) header) hi) halt
lemma execution_nat {n B t q:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u)
 (hq:(100≤q ∧q≤106) ∨5100≤q) (hz:q≠4460) (hr:q≠5847)
 (hs:∀ (i : ℕ), 6210 ≤ i → i ≤ 6214 → q ≠ i) : u.natReg q=s.natReg q :=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps q hq hz hr hs)
end ExactFourierCircuits.UniformLocalFactorDispatchMachine
