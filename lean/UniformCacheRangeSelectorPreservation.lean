import UniformCacheRangeSelectorExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRangeSelector
open UniformMachine UniformAssembly UniformTensorMonomialMachine UniformNewtonTableMachine

def instructionFootprint:Instruction → Bool
 | .natLiteral d _|.length d|.natBinary _ d _ _|.loadNat d _=>decide (6700 ≤ d ∧ d ≤ 6723 ∨ 7100 ≤ d ∧ d ≤ 7129)
 | _=>true
lemma footprint:program.all instructionFootprint=true:=by decide
lemma program_keeps(q:ℕ)(lo:q<6700 ∨ 6723<q)(hi:q<7100 ∨ 7129<q):∀ins∈program,KeepsNat q ins:=by
 intro ins mem
 have h:instructionFootprint ins=true:=List.all_eq_true.mp footprint ins mem
 cases ins <;>simp only[instructionFootprint,KeepsNat,decide_eq_true_eq] at * <;>try trivial
 all_goals omega
lemma execution_register {n B ticks}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u)(q:ℕ)(lo:q<6700 ∨ 6723<q)(hi:q<7100 ∨ 7129<q):
 u.natReg q=s.natReg q:=Executes.keeps_nat run.executes (program_keeps q lo hi)

def natInstruction:Instruction → Bool
 | .natLiteral ..|.natBinary ..|.loadNat ..|.storeNat ..|.branchLT ..|.jump ..|.halt=>true
 | _=>false
lemma onlyNat:program.all natInstruction=true:=by decide
structure Frame(s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
lemma Frame.trans {s u v:State}(a:Frame s u)(b:Frame u v):Frame s v:=
 ⟨b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,b.outputs.trans a.outputs,b.roots.trans a.roots⟩
lemma step_frame {p n}{x:Fin n → ℂ}{s u:State}(code:∀ins∈p,natInstruction ins=true)
 (run:step p n x s=.running u):Frame s u:=by
 cases hg:p[s.pc]? with
 | none=>simp[step,hg] at run
 | some ins=>
  obtain ⟨_,he⟩:=List.getElem?_eq_some_iff.1 hg
  have hi:=code ins (List.mem_of_getElem he)
  cases ins <;>simp only[natInstruction] at hi <;>try contradiction
  all_goals simp only[step,hg] at run
  all_goals try simp only[StepResult.running.injEq] at run
  all_goals repeat' (first | (subst u;exact ⟨rfl,rfl,rfl,rfl⟩) |
   (split at run <;>simp_all [StepResult.running.injEq,writeNat,next]))
  all_goals contradiction
lemma execution_frame {n B ticks}{x:Fin n → ℂ}{s u:State}
 (run:BoundedExecution program n x B s ticks u):Frame s u:=by
 have code:∀ins∈program,natInstruction ins=true:=List.all_eq_true.mp onlyNat
 have h:=run.executes
 clear run
 induction h with
 | halt _=>exact ⟨rfl,rfl,rfl,rfl⟩
 | next hs _ ih=>exact (step_frame code hs).trans ih
end ExactFourierCircuits.UniformCacheRangeSelector
