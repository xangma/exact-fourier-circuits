import UniformDirectLeafCacheExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheRetained
open UniformMachine UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheExecution
open UniformTransposeDescriptorMachine
noncomputable section

lemma constants_of_operands {n:ℕ} {x:Fin n→ℂ} {s:State}
 (h:UniformInitialPreparation.Operands n x s) : UniformHadamardPairMachine.Constants s := by
 exact ⟨h.constants (1:Fin 6),h.constants (2:Fin 6),h.constants (3:Fin 6),
  h.constants (4:Fin 6),h.constants (5:Fin 6)⟩
lemma operation_scale_coefficient {v:ℕ} (o K:ℕ) (op:UniformDirectToeplitz.Operation v)
 (h:(ofOperation o K op).kind=0) : (ofOperation o K op).coefficient=K := by
 cases op with
 | scale i=>rfl
 | shear i j=>simp only[ofOperation] at h;omega
lemma leaf_scale_coefficient (v o K:ℕ) (q:Record) (member:q∈leafRecords v o K)
 (kind:q.kind=0) : q.coefficient=K := by
 obtain ⟨op,_h,rfl⟩:=List.mem_map.mp member
 exact operation_scale_coefficient o K op kind
lemma scale_value (r K:ℕ) (q:Record) (coefficient:q.coefficient=K) :
 UniformDirectLeafCacheSource.mu r K q=1 := by
 simp[UniformDirectLeafCacheSource.mu,coefficient,UniformLocalSeedTableMachine.seedValue]

/-- Actual original and conjugate retained lane3 produce both physical
coefficient reads. Actual82 descriptor membership supplies all endpoint and
opcode legality. The startup operands supply the five genuine C constants. -/
theorem execution {n B:ℕ} {c:Config} (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))
 (v o:ℕ) (q:Record) (x:Fin n→ℂ) (s:State)
 (original:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (operands:UniformInitialPreparation.Operands n x s)
 (args:Args c s) (record:UniformDirectLeafCacheSource.At c.record q s)
 (od:c.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:c.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (extent:o+v≤UniformAllAxisSeedPreparation.radix n axis)
 (member:q∈leafRecords v o (UniformAllAxisSeedPreparation.axisBase n axis.val+
  3*UniformAllAxisSeedPreparation.radix n axis))
 (positive:2≤UniformAllAxisSeedPreparation.radix n axis)
 (layout:Layout c (UniformAllAxisSeedPreparation.radix n axis) B)
 (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B)
 (originalBound:UniformAllAxisSeedPreparation.axisBase n axis.val+4*UniformAllAxisSeedPreparation.radix n axis≤B)
 (conjugateBound:UniformAllAxisConjugatePreparation.axisBase n axis.val+4*UniformAllAxisSeedPreparation.radix n axis≤B)
 (freshOriginal:UniformAllAxisSeedPreparation.axisBase n axis.val+4*UniformAllAxisSeedPreparation.radix n axis≤c.pool)
 (freshConjugate:UniformAllAxisConjugatePreparation.axisBase n axis.val+4*UniformAllAxisSeedPreparation.radix n axis≤c.pool)
 (code:264≤B) (pc:s.pc=0) (wb:WordBound B s) : ∃u,
 BoundedExecution UniformDirectLeafCacheProgram.program n x B s
  (62*UniformAllAxisSeedPreparation.radix n axis+(if q.kind=0 then 103 else 199)) u ∧u.pc=263 ∧
 Nonempty (Result c (UniformAllAxisSeedPreparation.radix n axis) q
  (UniformDirectLeafCacheSource.mu (UniformAllAxisSeedPreparation.radix n axis)
   (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) q) positive u) ∧
 (∀j,(j<c.pool∨c.pool+9*UniformAllAxisSeedPreparation.radix n axis≤j)→u.scalarHeap j=s.scalarHeap j) ∧
 (∀j,j<c.permutation→(j<c.rows∨c.rows+3≤j)→u.natHeap j=s.natHeap j) ∧
 (∀j,c.entry+7≤j→u.natHeap j=s.natHeap j) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 let r:=UniformAllAxisSeedPreparation.radix n axis
 let A:=UniformAllAxisSeedPreparation.axisBase n axis.val
 let C:=UniformAllAxisConjugatePreparation.axisBase n axis.val
 have legal:=UniformDirectLeafCacheChronology.leaf_valid v o (A+3*r) r extent q member
 obtain ⟨orig,width,conj⟩:=UniformDirectLeafCacheSource.retained_directories axis s original conjugate
 have source:Source c r A C q s:=⟨record,by rw[od];exact orig,by rw[od];exact width,by rw[cd];exact conj⟩
 have values:=UniformDirectLeafCacheSource.retained_sources axis s original conjugate q legal.1
 have hi:=legal.1.2.2
 exact UniformDirectLeafCacheExecution.execution _ x s args source values (constants_of_operands operands)
  legal.1 legal.2 positive layout descriptor directory conjugateDirectory originalBound conjugateBound
  (by omega) (by omega) code pc wb
end
end ExactFourierCircuits.UniformDirectLeafCacheRetained
