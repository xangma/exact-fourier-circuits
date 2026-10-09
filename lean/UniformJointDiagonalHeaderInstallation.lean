import UniformDiagonalHeaderInstallation
import UniformJointAllocationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointDiagonalHeaderInstallation
open UniformMachine UniformTensorMonomialMachine UniformJointAllocation
noncomputable section

/-- The coefficient row follows all W physical input arrays, so it cannot
 overwrite persistent prepared pools ending at2U. -/
def coefficient(c:Constants)(n:ℕ):ℕ:=(allocate c n).tensorSource+c.roles*UniformInitialPreparation.len n
lemma coefficient_stack(c:Constants){n:ℕ}(hn:0<n):
 coefficient c n+UniformAllAxisSeedPreparation.prefixSum n (UniformAllAxisSeedPreparation.axisCount n) ≤
 (allocate c n).tensorScalarStack:=by
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw [Nat.mul_assoc 2 c.roles] at h
 dsimp only [coefficient,allocate]
 omega

def rows(c:Constants)(n:ℕ)(hn:0<n):UniformGlobalDiagonalRowsMachine.Layout:=
 {rowLayout c n hn with
  coefficient:=coefficient c n
  coefficientBound:=by
   have fit:=coefficient_stack c hn
   dsimp only [rowLayout] at fit ⊢
   have big:3*slab c n ≤ envelope c n:=by unfold envelope;omega
   exact fit.trans (by simpa only [allocate] using big)}

lemma coefficient_fit(c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles):
 (rows c n hn).coefficient+(rows c n hn).total ≤ (tensorGeometry c n hn roles).scalarStack:=
 coefficient_stack c hn
lemma source_disjoint(c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles):
 (tensorGeometry c n hn roles).source+c.roles*(tensorGeometry c n hn roles).volume=
 (rows c n hn).coefficient:=rfl
lemma pools_before(c:Constants){n:ℕ}(hn:0<n)(poolEnd:ℕ)(kept:poolEnd ≤ 2*slab c n):
 poolEnd ≤ (rows c n hn).coefficient:=by
 change poolEnd ≤ coefficient c n
 dsimp only [coefficient,allocate]
 omega

/-- The input links come from the actual62 allocator, not a supplied Ready. -/
lemma input(c:Constants){n:ℕ}(hn:0<n)(roles:0<c.roles)(s:State)
 (saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
  (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) s)
 (allocated:UniformJointAllocationMachine.observed s=allocate c n):
 UniformDiagonalHeaderInstallation.Input (rows c n hn) (tensorGeometry c n hn roles) s:=by
 constructor
 · exact congrArg (fun q=>q+1) saved.count
 · exact congrArg (fun q=>q+1) saved.count
 · exact congrArg Addresses.factorDirectory allocated
 · exact congrArg Addresses.tensorRows allocated
 · exact congrArg Addresses.permutation allocated
 · have source:=congrArg Addresses.tensorSource allocated
   change s.natReg 6026=(allocate c n).tensorSource at source
   change s.natReg 6026+c.roles*s.natReg 103=coefficient c n
   rw [source,saved.workingLength]
   rfl
 · exact saved.workingLength
 · exact congrArg Addresses.tensorSource allocated
 · exact congrArg Addresses.native allocated
 · exact congrArg Addresses.tensorRows allocated
 · exact congrArg Addresses.tensorNatStack allocated
 · exact congrArg Addresses.tensorScalarStack allocated

theorem execution(c:Constants){n start:ℕ}(hn:0<n)(roles:0<c.roles)
 (program:Program)(x:Fin n → ℂ)(s:State)
 (saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n) n
  (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) s)
 (allocated:UniformJointAllocationMachine.observed s=allocate c n)
 (code:BlockAt (UniformDiagonalHeaderInstallation.block c.roles) program start)(pc:s.pc=start)
 (room:start+17 ≤ envelope c n)(wb:WordBound (envelope c n) s):
 BoundedRuns program n x (envelope c n) s 17 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s) ∧
 UniformGlobalDiagonalRowsMachine.Header (rows c n hn) (0:Fin 9)
  (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s) ∧
 UniformGlobalTensorDiagonalMachine.Header (tensorGeometry c n hn roles)
  (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s) ∧
 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).natHeap=s.natHeap ∧
 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).scalarReg=s.scalarReg ∧
 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).outputs=s.outputs ∧
 (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).rootOrders=s.rootOrders ∧
 (∀q,¬UniformDiagonalHeaderInstallation.Changed q →
  (applyBlock (UniformDiagonalHeaderInstallation.block c.roles) s).natReg q=s.natReg q):=
 UniformDiagonalHeaderInstallation.execution (rows c n hn) (tensorGeometry c n hn roles)
  program x s (input c hn roles s saved allocated) code pc room wb
end
end ExactFourierCircuits.UniformJointDiagonalHeaderInstallation
