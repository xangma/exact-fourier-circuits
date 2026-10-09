import UniformGlobalRolePackingMachine
import UniformRecursiveBatchHeaderMachine
import UniformGlobalEnvelope
import UniformSeedChunkAllocation
import UniformGlobalTensorDiagonalPreparation
import UniformProducedSectorTransposePreparation
import UniformRecursiveNodePreparation

/-!
# A shared polynomial address envelope

*An explicit power saving for the exact discrete Fourier transform*, OpenAI
math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, §4.2, PDF pp. 19–20
(Lemma 4.1 and Proposition 4.2), and the final word-bound argument in §5.4,
PDF p. 24 (`thm:main`). The concrete slabs, bank headers, stack frames and
very conservative polynomial degree are machine bookkeeping, with no
one-to-one numbered paper lemma. These formulas alone do not assert execution;
actual callers prove the bounded transitions using the constructed layouts.
-/

set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointAllocation
open UniformMachine UniformAssembly
noncomputable section
structure Constants where
 code : ℕ
 seedTape : ℕ
 unitTape : ℕ
 roles : ℕ
/-- The actual held code, seed printer payload, unit table and native width. -/
/- §5.4, PDF p. 24: code, fixed network width and printer payloads are
absolute constants, fixed before n. Their sizes are kept symbolic here. -/
def actualConstants : Constants :=
 ⟨UniformRecursiveSavingProgram.program.length,UniformRecursiveSavingProgram.seedLength,
  UniformRecursiveSavingProgram.unitLength,ExplicitSeedBudget.paddedRoles⟩
variable (c:Constants)
def payload : ℕ := c.seedTape+c.unitTape+6
@[irreducible] def fixed : ℕ := c.code+payload c+c.roles+6000
lemma payload_le : payload c≤fixed c := by unfold fixed;omega
lemma program_le : c.code≤fixed c := by unfold fixed;omega
lemma roles_le : c.roles≤fixed c := by unfold fixed;omega
lemma fixed_large : 6000≤fixed c := by unfold fixed;omega

/-- Concrete shared slab, accounting for actual static printer code, both
actual record tapes and actual role multiplicity. Separate heaps reuse it. -/
def slab (n : ℕ) : ℕ := 100000*(fixed c+1)*(n+2)^19
/-- Raw addresses, to be installed by charged header operations. -/
structure Addresses where
 factorDirectory : ℕ
 tensorRows : ℕ
 permutation : ℕ
 coefficient : ℕ
 tensorNatStack : ℕ
 tensorScalarStack : ℕ
 tensorSource : ℕ
 native : ℕ
 packed : ℕ
 child : ℕ
 physicalRows : ℕ
 sectorRows : ℕ
 sectorSuffix : ℕ
 sectorStack : ℕ
 sectorDirectory : ℕ
 batchDirectory : ℕ
 inverse : ℕ
 fresh : ℕ

def allocate (n : ℕ) : Addresses :=
 let u:=slab c n
 ⟨u,2*u,3*u,u,4*u,3*u,2*u,4*u,5*u,6*u,5*u,6*u,7*u,8*u,9*u,10*u,11*u,12*u⟩

def envelope (n : ℕ) : ℕ := 40*slab c n+fixed c
/-- One fixed degree suffices at every positive n, including n=1. -/
/- §5.4, PDF p. 24: absorb the fixed multiplicative constants into a
single degree. This need not be the paper's sharpest space exponent. -/
def degree : ℕ := 2*(4000000*(fixed c+1)+fixed c)+19
lemma degree_pos : 0<degree c := by unfold degree;omega
lemma cover (C z:ℕ):
 40*(100000*(C+1)*z)+C≤(4000000*(C+1)+C)*z+(4000000*(C+1)+C):=by
 nlinarith
lemma polynomial {n : ℕ} (hn : 0<n) : envelope c n≤(n+2)^(degree c) := by
 have h:=UniformGlobalEnvelope.polynomial_envelope (4000000*(fixed c+1)+fixed c) 19 n hn
 have small:envelope c n≤(4000000*(fixed c+1)+fixed c)*(n+2)^19+
  (4000000*(fixed c+1)+fixed c):=by
  exact cover (fixed c) ((n+2)^19)
 exact small.trans h

/-- Every actual bank size used below is derived from ordinary geometry, not
from supplied desired envelopes or produced output. -/
lemma arithmetic (n ell V total : ℕ) (e:ell≤2*n+1) (v:V≤4*n)
 (t:total≤(2*n+1)*(4*n)) :
 10*ell+10*total+10*V+2*c.roles*V+
 34*(V+1)+(V+1)*(payload c+5*V)+V^2+6000+fixed c≤ slab c n := by
 have fw:=roles_le c
 have fp:=payload_le c
 have ev:10*ell≤10*(2*n+1):=Nat.mul_le_mul_left 10 e
 have tv:10*total≤10*((2*n+1)*(4*n)):=Nat.mul_le_mul_left 10 t
 have wv:c.roles*V≤fixed c*(4*n):=Nat.mul_le_mul fw v
 have pv:(V+1)*(payload c+5*V)≤(4*n+1)*(fixed c+20*n):=
  Nat.mul_le_mul (by omega) (by omega)
 have vv:V^2≤(4*n)^2:=Nat.pow_le_pow_left v 2
 have small:10*ell+10*total+10*V+2*c.roles*V+
  34*(V+1)+(V+1)*(payload c+5*V)+V^2+6000+fixed c≤100000*(fixed c+1)*(n+2)^2:=by
  nlinarith only [ev,tv,wv,pv,vv,v]
 exact small.trans (Nat.mul_le_mul_left _
  (Nat.pow_le_pow_right (by omega : 1≤n+2) (by decide : 2≤19)))

lemma actual_sizes (n : ℕ) (hn:0<n) :
 UniformAllAxisSeedPreparation.axisCount n≤2*n+1 ∧
 UniformInitialPreparation.len n≤4*n ∧
 UniformAllAxisSeedPreparation.prefixSum n (UniformAllAxisSeedPreparation.axisCount n)≤(2*n+1)*(4*n) := by
 have e:UniformInitialPreparation.ell n≤2*n:=by
  have h:=UniformWorkingLength.firstExceed_bound n
  unfold UniformInitialPreparation.ell UniformWorkingLength.axisCount
  omega
 have v:UniformInitialPreparation.len n≤4*n:=(UniformWorkingLength.workingLength_upper hn).le
 have axes:UniformAllAxisSeedPreparation.axisCount n≤2*n+1:=by
  unfold UniformAllAxisSeedPreparation.axisCount;omega
 have sum:=UniformAllAxisSeedPreparation.prefix_bound n (UniformAllAxisSeedPreparation.axisCount n) (le_refl _)
 exact ⟨axes,v,sum.trans (Nat.mul_le_mul axes v)⟩
lemma actual_arithmetic (n:ℕ) (hn:0<n) :
 let ell:=UniformAllAxisSeedPreparation.axisCount n
 let V:=UniformInitialPreparation.len n
 let total:=UniformAllAxisSeedPreparation.prefixSum n ell
 10*ell+10*total+10*V+2*c.roles*V+
 34*(V+1)+(V+1)*(payload c+5*V)+V^2+6000+fixed c≤ slab c n := by
 obtain ⟨e,v,t⟩:=actual_sizes n hn
 exact arithmetic c n _ _ _ e v t
lemma positive (n:ℕ):0<slab c n := by unfold slab;positivity
lemma program_bound (n:ℕ):c.code≤envelope c n:=(program_le c).trans (by unfold envelope;omega)
lemma roles_bound (n:ℕ):c.roles≤envelope c n:=(roles_le c).trans (by unfold envelope;omega)

/-- Actual49 row producer allocation, with totals of the selected real radices. -/
def rowLayout (n:ℕ) (hn:0<n) : UniformGlobalDiagonalRowsMachine.Layout where
 B:=envelope c n
 ell:=UniformAllAxisSeedPreparation.axisCount n
 directory:=(allocate c n).factorDirectory
 rows:=(allocate c n).tensorRows
 permutation:=(allocate c n).permutation
 coefficient:=(allocate c n).coefficient
 total:=UniformAllAxisSeedPreparation.prefixSum n (UniformAllAxisSeedPreparation.axisCount n)
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope] at *;omega
 directoryBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 rowsBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 permutationBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 coefficientBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega

/-- Same addresses as actual131 row/tensor composition, with every role read
and every output role reserved. No coefficient pool value is assumed here. -/
def tensorGeometry (n:ℕ) (hn:0<n) (rolePositive:0<c.roles):UniformGlobalTensorDiagonalMachine.Geometry c.roles where
 B:=envelope c n
 ell:=UniformAllAxisSeedPreparation.axisCount n
 row:=(allocate c n).tensorRows
 natStack:=(allocate c n).tensorNatStack
 scalarStack:=(allocate c n).tensorScalarStack
 source:=(allocate c n).tensorSource
 destination:=(allocate c n).native
 volume:=UniformInitialPreparation.len n
 positive:=rolePositive
 roles:=roles_bound c n
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope] at *;omega
 rowsBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 natStackBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 scalarStackBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 sourceBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 destinationAbove:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 destinationBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega

/-- Actual92 metadata generator uses a fresh slab c for each distinct region. -/
def sectorLayout (n:ℕ) (hn:0<n):UniformSectorMetadataMachine.Layout where
 ell:=UniformAllAxisSeedPreparation.axisCount n
 rows:=(allocate c n).sectorRows
 suffix:=(allocate c n).sectorSuffix
 stack:=(allocate c n).sectorStack
 directory:=(allocate c n).sectorDirectory
 total:=UniformInitialPreparation.len n
 B:=envelope c n
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope] at *;omega
 rowsBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 suffixBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 stackBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 directoryBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 volumeBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope] at *;omega

lemma sector_count_le_volume (axes:List UniformSectorPacking.Axis):
 (UniformSectorPacking.sectorStates axes).length≤(UniformSectorPacking.radices axes).prod:=by
 rw[UniformSectorBatchDirectoryMachine.sector_count]
 induction axes with
 | nil=>rfl
 | cons a axes ih=>
  have h:=UniformTraversal.block_count_le_sum a.widths (by
   intro q hq
   rcases a.widths_one_two q hq with h|h <;>omega)
  exact Nat.mul_le_mul h ih

/-- Every actual137 packing invocation gets the same retained metadata and
its own role slice of the real simultaneous scalar bank. -/
def packingLayout (n:ℕ) (hn:0<n) (i:ℕ) (hi:i<c.roles):UniformSectorPackingMachine.Layout where
 ell:=UniformAllAxisSeedPreparation.axisCount n
 rows:=(allocate c n).physicalRows
 suffix:=(allocate c n).sectorSuffix
 stack:=(allocate c n).sectorStack
 inverse:=(allocate c n).inverse
 source:=(allocate c n).native+i*UniformInitialPreparation.len n
 destination:=(allocate c n).packed+i*UniformInitialPreparation.len n
 total:=UniformInitialPreparation.len n
 B:=envelope c n
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope];omega
 rowsBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 suffixBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 stackBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 inverseBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope];omega
 sourceBelow:=by
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw[Nat.mul_assoc 2 c.roles] at h
  dsimp[allocate]
  omega
 destinationBound:=by
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw[Nat.mul_assoc 2 c.roles] at h
  have slice:(i+1)*UniformInitialPreparation.len n≤c.roles*UniformInitialPreparation.len n:=
   Nat.mul_le_mul_right _ (by omega)
  rw[Nat.add_mul,Nat.one_mul] at slice
  dsimp[allocate,envelope]
  omega
 volumeBound:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope];omega

/-- Construct the actual153 simultaneous packing geometry at the very same
4U→5U scalar banks and 7U/8U/11U retained metadata addresses. -/
def packingGeometry (n:ℕ) (hn:0<n):UniformGlobalRolePackingMachine.Geometry c.roles where
 B:=envelope c n
 ell:=UniformAllAxisSeedPreparation.axisCount n
 rows:=(allocate c n).physicalRows
 suffix:=(allocate c n).sectorSuffix
 stack:=(allocate c n).sectorStack
 inverse:=(allocate c n).inverse
 source:=(allocate c n).native
 destination:=(allocate c n).packed
 volume:=UniformInitialPreparation.len n
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope];omega
 roles:=roles_bound c n
 rowsBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 suffixBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 stackBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 inverseFit:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope];omega
 sourceBelow:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate];omega
 destinationFit:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope];omega
 volumeFit:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope];omega

/-- Construct geometry from the genuine mathematical sector partition. Fits
and ordering follow from that partition, rather than being Layout premises. -/
def transposeGeometry (n:ℕ) (hn:0<n) (axes:List UniformSectorPacking.Axis)
 (volume:(UniformSectorPacking.radices axes).prod=UniformInitialPreparation.len n):
 UniformAllSectorTransposeMachine.Geometry c.roles false (UniformSectorPacking.sectorStates axes) where
 B:=envelope c n
 volume:=UniformInitialPreparation.len n
 native:=(allocate c n).packed
 directory:=(allocate c n).batchDirectory
 buffer:=(allocate c n).child
 fits:=by simpa only[UniformAllSectorPaddingMachine.Fits,volume] using UniformSectorBatchDirectoryMachine.sector_fits axes
 ordered:=UniformSectorBatchDirectoryMachine.sector_before axes
 nativeFit:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 bufferFit:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate,envelope] at *;omega
 separation:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[allocate] at *;omega
 entry:=by
  have count:=sector_count_le_volume axes
  rw[volume] at count
  have h:=actual_arithmetic c n hn
  dsimp only at h
  rw[Nat.mul_assoc 2 c.roles] at h
  dsimp[allocate,envelope] at *;omega
 roles:=roles_bound c n
 code:=by have h:=actual_arithmetic c n hn;dsimp only at h;rw[Nat.mul_assoc 2 c.roles] at h;dsimp[envelope] at *;omega

/-- All producer/consumer separation premises for actual131 and actual202
programs, including the old three-word and new five-word directories. -/
lemma production_links (n:ℕ) (hn:0<n):
 let a:=allocate c n
 let ell:=UniformAllAxisSeedPreparation.axisCount n
 let V:=UniformInitialPreparation.len n
 let total:=UniformAllAxisSeedPreparation.prefixSum n ell
 a.permutation+total≤a.tensorNatStack ∧a.coefficient+total≤a.tensorScalarStack ∧
 a.coefficient+total≤a.tensorSource ∧a.physicalRows+4*ell≤a.sectorRows ∧
 a.sectorDirectory+3*V≤a.batchDirectory ∧a.batchDirectory+5*V≤a.fresh ∧
 a.child+c.roles*V≤a.fresh ∧
 a.native+c.roles*V≤a.packed ∧a.packed+c.roles*V≤a.child ∧
 a.sectorSuffix+ell+1≤a.sectorStack ∧a.sectorStack+9*ell≤a.inverse ∧a.inverse+V≤a.fresh := by
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw[Nat.mul_assoc 2 c.roles] at h
 dsimp[allocate]
 omega

/-- Actual generated five-word batch cells carry bounded recursive ABI
values. There is no assumed exponent, base, or word-bound output. -/
lemma sector_child_values (n:ℕ) (hn:0<n) (axes:List UniformSectorPacking.Axis)
 (volume:(UniformSectorPacking.radices axes).prod=UniformInitialPreparation.len n)
 (i:ℕ) (hi:i<(UniformSectorPacking.sectorStates axes).length):
 let st:=(UniformSectorPacking.sectorStates axes)[i]'hi
 st.pairs≤UniformInitialPreparation.len n ∧st.width≤UniformInitialPreparation.len n ∧
 (allocate c n).child+c.roles*st.start+c.roles*st.width≤(allocate c n).fresh ∧
 (allocate c n).batchDirectory+5*i+5≤(allocate c n).fresh:=by
 have fit:=UniformSectorBatchDirectoryMachine.sector_fits axes i hi
 rw[volume] at fit
 have width:=UniformSectorBatchDirectoryMachine.sector_width axes i hi
 have k:((UniformSectorPacking.sectorStates axes)[i]'hi).pairs≤((UniformSectorPacking.sectorStates axes)[i]'hi).width:=by
  rw[width];exact UniformRecursiveBatchHeaderMachine.index_le_power _
 have count:=sector_count_le_volume axes
 rw[volume] at count
 have mul:=Nat.mul_le_mul_left c.roles fit
 rw[Nat.mul_add] at mul
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw[Nat.mul_assoc 2 c.roles] at h
 dsimp[allocate]
 omega

/-- Genuine retained original/conjugate pools and both directories precede
all fresh banks; executed seed/chunk canonical allocation fits the same slab. -/
lemma canonical_below (n:ℕ): (n+2)^19≤ slab c n:=by
 have h:1≤100000*(fixed c+1):=by omega
 exact (by simpa only[slab,Nat.one_mul] using Nat.mul_le_mul_right ((n+2)^19) h)
lemma retained_below (n:ℕ) (hn:0<n):
 UniformAllAxisSeedPreparation.axisBase n (UniformAllAxisSeedPreparation.axisCount n)≤(allocate c n).coefficient ∧
 UniformAllAxisConjugatePreparation.axisBase n (UniformAllAxisSeedPreparation.axisCount n)≤(allocate c n).coefficient ∧
 UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤(allocate c n).factorDirectory ∧
 UniformAllAxisConjugatePreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤(allocate c n).factorDirectory:=by
 obtain ⟨_code,co,di⟩:=UniformAllAxisConjugatePreparation.word_setup hn
 obtain ⟨_originalCode,original,originalDir⟩:=UniformAllAxisSeedPreparation.word_setup hn
 exact ⟨original.trans (canonical_below c n),co.trans (canonical_below c n),
  originalDir.trans (canonical_below c n),di.trans (canonical_below c n)⟩

/-- This is the charged root allocator's actual 34-word-per-level slab. -/
def stackEnd (n k:ℕ):ℕ := (allocate c n).fresh+34*(k+1)
/-- Actual unit/seed setup followed by native five-volume gather. -/
def descendFrontier (F k:ℕ):ℕ :=
 UniformRecursiveNodePreparation.workBase F c.seedTape c.unitTape+5*2^k
lemma descend_formula (F k:ℕ):descendFrontier c F k=F+payload c+5*2^k:=by
 unfold descendFrontier UniformRecursiveNodePreparation.workBase UniformRecursiveNodePreparation.unitBase payload
 omega

/-- Literal same-child quotient chain, every step enabled by the actual large
branch. This predicate says nothing about whether the program has executed. -/
/- The quotient recursion in §2.5–§2.6, PDF pp. 10–12, and the
word bound in §5.4, p. 24. The descent/frontier proofs below bound live
child frames; they do not supply child executions or costs. -/
inductive Descent (k:ℕ):ℕ→ℕ→Prop
 | root:Descent k 0 k
 | child {d j:ℕ}:Descent k d j→UniformBatching.threshold≤j→
   Descent k (d+1) (UniformBatching.quotient j)
lemma Descent.depth_bound {k d j:ℕ} (h:Descent k d j):d+j≤k:=by
 induction h with
 | root=>omega
 | child old large ih=>have q:=UniformBatching.quotient_lt large;omega
lemma Descent.volume_bound {k d j:ℕ} (h:Descent k d j):2^j≤2^k:=
 Nat.pow_le_pow_right (by decide) (by have:=h.depth_bound;omega)

lemma Descent.chain {k d j:ℕ} (h:Descent k d j):j=UniformBatching.quotientChain k d:=by
 induction h with
 | root=>exact (UniformBatching.quotientChain_zero k).symm
 | child old large ih=>rw[UniformBatching.quotientChain_succ,←ih]
lemma frame_within_stack (n:ℕ) {k d j:ℕ} (h:Descent k d j):
 (allocate c n).fresh+34*(d+1)≤ stackEnd c n k:=by
 have depth:=h.depth_bound
 unfold stackEnd
 omega
/-- Actual quotient prevents the native XOR table from reaching the child
frontier: its square length is at most the parent volume, even for large q. -/
lemma twice_quotient (k:ℕ):2*UniformBatching.quotient k≤k:=by
 have qr:=UniformBatching.quotient_remainder k
 rw[UniformBatching.blockSize_eq] at qr
 omega
lemma xor_size (k:ℕ):2^UniformBatching.quotient k*2^UniformBatching.quotient k≤2^k:=by
 rw[←Nat.pow_add]
 exact Nat.pow_le_pow_right (by decide) (by have h:=twice_quotient k;omega)
lemma native_workspace_below_child (F k:ℕ):
 let work:=UniformRecursiveNodePreparation.workBase F c.seedTape c.unitTape
 work+3*2^k+2^UniformBatching.quotient k*2^UniformBatching.quotient k≤descendFrontier c F k ∧
 work+4*2^k+2^k≤descendFrontier c F k ∧F<descendFrontier c F k:=by
 have table:=xor_size k
 have pl:6≤payload c:=by unfold payload;omega
 dsimp[descendFrontier]
 unfold UniformRecursiveNodePreparation.workBase UniformRecursiveNodePreparation.unitBase at *
 unfold payload at pl
 omega

/-- Actual frontier after d simultaneously live preparations. Parent return
restores its fresh pointer, so sibling groups do not accumulate allocations. -/
def frontier (n k:ℕ):ℕ→ℕ
 | 0=>stackEnd c n k
 | d+1=>descendFrontier c (frontier n k d) (UniformBatching.quotientChain k d)
lemma frontier_upper (n k d:ℕ):
 frontier c n k d≤ stackEnd c n k+d*(payload c+5*2^k):=by
 induction d with
 | zero=>simp[frontier]
 | succ d ih=>
  have q:UniformBatching.quotientChain k d≤k:=Nat.div_le_self k _
  have p:2^UniformBatching.quotientChain k d≤2^k:=Nat.pow_le_pow_right (by decide) q
  rw[frontier,descend_formula]
  nlinarith

/-- A live root-to-child chain, its return stack and current workspace all fit
one additional slab. This is a bound on the actual formulas, not execution. -/
lemma recursion_bound (n k d:ℕ) (hn:0<n) (volume:2^k≤UniformInitialPreparation.len n)
 (depth:d≤k+1):frontier c n k d≤13*slab c n:=by
 have kV:k≤UniformInitialPreparation.len n:=
  (UniformRecursiveBatchHeaderMachine.index_le_power k).trans volume
 have mul:d*(payload c+5*2^k)≤(UniformInitialPreparation.len n+1)*
  (payload c+5*UniformInitialPreparation.len n):=Nat.mul_le_mul (by omega) (by omega)
 have h:=actual_arithmetic c n hn
 dsimp only at h
 rw[Nat.mul_assoc 2 c.roles] at h
 have f:=frontier_upper c n k d
 dsimp[stackEnd,allocate] at f
 nlinarith only[h,f,mul,kV]
lemma recursion_word_bound (n k d:ℕ) (hn:0<n) (volume:2^k≤UniformInitialPreparation.len n)
 (depth:d≤k+1):frontier c n k d≤(n+2)^(degree c):=
 (recursion_bound c n k d hn volume depth).trans
 ((show 13*slab c n≤envelope c n by unfold envelope;omega).trans (polynomial c hn))

/-- Fixed degree for the actual code and payloads, independent of input n. -/
theorem actual_polynomial (n:ℕ) (hn:0<n):
 envelope actualConstants n≤(n+2)^(degree actualConstants):=polynomial actualConstants hn
theorem actual_degree_pos:0<degree actualConstants:=degree_pos actualConstants
def actualRowLayout (n:ℕ) (hn:0<n):UniformGlobalDiagonalRowsMachine.Layout:=rowLayout actualConstants n hn
def actualSectorLayout (n:ℕ) (hn:0<n):UniformSectorMetadataMachine.Layout:=sectorLayout actualConstants n hn
theorem actual_recursion_word_bound (n k d:ℕ) (hn:0<n)
 (volume:2^k≤UniformInitialPreparation.len n) (depth:d≤k+1):
 frontier actualConstants n k d≤(n+2)^(degree actualConstants):=
 recursion_word_bound actualConstants n k d hn volume depth

def actualPackingGeometry (n:ℕ) (hn:0<n):UniformGlobalRolePackingMachine.Geometry actualConstants.roles:=
 packingGeometry actualConstants n hn

end
end ExactFourierCircuits.UniformJointAllocation
