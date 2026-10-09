import UniformGlobalTensorDiagonalPreparation
import UniformGlobalRolePackingLoop
import UniformProducedSectorChildABI
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalMovementAssembly
open UniformMachine UniformAssembly UniformTensorMonomialMachine
noncomputable section

/-- A literal three-piece assembler, with every helper halt becoming a charged
jump. The final halt is the child-entry boundary, not a transform completion. -/
def assembly (p q r : Program) : Program :=
 p.map (relocate 0 p.length) ++ q.map (relocate p.length (p.length+q.length)) ++
 r.map (relocate (p.length+q.length) (p.length+q.length+r.length)) ++ [.halt]
lemma assembly_length (p q r : Program) : (assembly p q r).length=p.length+q.length+r.length+1 := by
 simp only [assembly,List.length_append,List.length_map,List.length_singleton]
lemma first_code (p q r : Program) : CodeAt p (assembly p q r) 0 p.length := by
 have link := UniformRankCrossPreparationMachine.segment_code []
  (q.map (relocate p.length (p.length+q.length)) ++
   r.map (relocate (p.length+q.length) (p.length+q.length+r.length)) ++ [.halt]) p 0 p.length rfl
 simpa only [assembly,List.nil_append,List.append_assoc] using link
lemma second_code (p q r : Program) : CodeAt q (assembly p q r) p.length (p.length+q.length) := by
 have link := UniformRankCrossPreparationMachine.segment_code (p.map (relocate 0 p.length))
  (r.map (relocate (p.length+q.length) (p.length+q.length+r.length)) ++ [.halt]) q p.length (p.length+q.length)
  (by rw [List.length_map])
 simpa only [assembly,List.append_assoc] using link
lemma third_code (p q r : Program) :
 CodeAt r (assembly p q r) (p.length+q.length) (p.length+q.length+r.length) := by
 exact UniformRankCrossPreparationMachine.segment_code
  (p.map (relocate 0 p.length) ++ q.map (relocate p.length (p.length+q.length))) [.halt]
  r (p.length+q.length) (p.length+q.length+r.length) (by simp only [List.length_append,List.length_map])
lemma halt_at (p q r : Program) : (assembly p q r)[p.length+q.length+r.length]?=some .halt := by
 unfold assembly
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map];omega)]
 simp only [List.length_append,List.length_map,Nat.sub_self,List.getElem?_cons_zero]

/-- One fixed physical prefix: the actual produced nine-factor diagonal131,
all-W physical forward packing153, and produced sector gather/child ABI218.
No runtime host rewiring or full child payload is part of this definition. -/
def programFor (W : ℕ) : Program := assembly
 (UniformGlobalTensorDiagonalPreparation.programFor W)
 (UniformGlobalRolePackingMachine.programFor W)
 (UniformProducedSectorChildABI.programFor W)
def program : Program := programFor ExplicitSeedBudget.paddedRoles
lemma program_length (W : ℕ) : (programFor W).length=503 := by
 simp only [programFor,assembly_length,UniformGlobalTensorDiagonalPreparation.program_length,
  UniformGlobalRolePackingMachine.program_length,UniformProducedSectorChildABI.program_length]

lemma diagonal_code (W : ℕ) :
 CodeAt (UniformGlobalTensorDiagonalPreparation.programFor W) (programFor W) 0 131 := by
 have link := first_code (UniformGlobalTensorDiagonalPreparation.programFor W)
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W)
 simpa only [programFor,UniformGlobalTensorDiagonalPreparation.program_length] using link
lemma packing_code (W : ℕ) :
 CodeAt (UniformGlobalRolePackingMachine.programFor W) (programFor W) 131 284 := by
 have link := second_code (UniformGlobalTensorDiagonalPreparation.programFor W)
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W)
 simpa only [programFor,UniformGlobalTensorDiagonalPreparation.program_length,UniformGlobalRolePackingMachine.program_length,show 131+153=284 by rfl] using link
lemma child_entry_code (W : ℕ) :
 CodeAt (UniformProducedSectorChildABI.programFor W) (programFor W) 284 502 := by
 have link := third_code (UniformGlobalTensorDiagonalPreparation.programFor W)
  (UniformGlobalRolePackingMachine.programFor W) (UniformProducedSectorChildABI.programFor W)
 simpa only [programFor,UniformGlobalTensorDiagonalPreparation.program_length,UniformGlobalRolePackingMachine.program_length,
  UniformProducedSectorChildABI.program_length,show 131+153=284 by rfl,show 284+218=502 by rfl] using link

/- Exact next obligations for the whole synchronized algorithm:
1. Executed cache and phase printing must produce every physical factor pool,
   four-word block row, width and forward permutation for the selected slot.
2. Link131 output/source and all raw ordinary headers to153, then its packed
   exact values and retained physical tables to218 in this very503 prefix.
3. Enter the same recursive C program for every generated sector, preserving
   its other complete W banks, and execute the true return/scatter/inverse
   packing path. A supplied child action is not a closed proof of this step.
4. Execute the nine local factor phases, their true inverse/permutation
   chronology, and all padded synchronized slots in one finite program.
5. Join selected CRT/output stores, allocation and full charged runtime.
These are recorded as prose obligations, not axioms or theorem hypotheses. -/

end
end ExactFourierCircuits.UniformGlobalMovementAssembly
