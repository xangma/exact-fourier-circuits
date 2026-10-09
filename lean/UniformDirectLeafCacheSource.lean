import UniformStoredDirectLeafOrientations
import UniformAllAxisConjugatePreparation
import UniformGlobalMatchingScaleMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheSource
open UniformMachine UniformTransposeDescriptorMachine
open UniformPairMachine (prepared)
noncomputable section

/-- A four-word descriptor is actual physical input printed by fixed82. -/
def At (D : ℕ) (q : Record) (s : State) : Prop :=
 ∀j : Fin 4, s.natHeap (D+j.val)=some (q.words[j.val]'j.isLt)

/-- The printed coefficient refers to lane3, independently of subtree offset. -/
def InRange (r K : ℕ) (q : Record) : Prop :=
 q.dest<r ∧ q.source<r ∧ K≤q.coefficient ∧ q.coefficient<K+r

def Legal (q : Record) : Prop :=
 (q.kind=0 ∧ q.dest=q.source) ∨ (q.kind=1 ∧ q.dest≠q.source)

def mu (r K : ℕ) (q : Record) : ℂ :=
 UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta r) 3 (q.coefficient-K)

/-- Both values come from actual retained compact banks. No conjugate scalar
or coefficient action is supplied. -/
lemma retained_sources {n : ℕ} (axis : Fin (UniformAllAxisSeedPreparation.axisCount n))
 (s : State)
 (original : UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (conjugate : UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (q : Record)
 (range : InRange (UniformAllAxisSeedPreparation.radix n axis)
   (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) q) :
 s.scalarHeap q.coefficient=some (prepared (mu (UniformAllAxisSeedPreparation.radix n axis)
  (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) q)) ∧
 s.scalarHeap (UniformAllAxisConjugatePreparation.axisBase n axis.val+
  3*UniformAllAxisSeedPreparation.radix n axis+
  (q.coefficient-(UniformAllAxisSeedPreparation.axisBase n axis.val+
   3*UniformAllAxisSeedPreparation.radix n axis)))=
 some (prepared (starRingEnd ℂ (mu (UniformAllAxisSeedPreparation.radix n axis)
  (UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis) q))) := by
 rcases range with ⟨_hd,_he,hlo,hhi⟩
 let r:=UniformAllAxisSeedPreparation.radix n axis
 let K:=UniformAllAxisSeedPreparation.axisBase n axis.val+3*r
 have hi:q.coefficient-K<r:=by change q.coefficient-(UniformAllAxisSeedPreparation.axisBase n axis.val+3*UniformAllAxisSeedPreparation.radix n axis)<UniformAllAxisSeedPreparation.radix n axis;omega
 let i:Fin r:=⟨q.coefficient-K,hi⟩
 have a:=original.coefficients axis axis.isLt (3:Fin 5) i
 have b:=(UniformAllAxisConjugatePreparation.retained_complete conjugate axis).2.2 (3:Fin 5) i
 constructor
 · convert a using 1 <;>simp only [mu,i,K,r]
   congr 1; norm_num; omega
 · exact b

/-- Real width/offset and the two retained directories satisfy fixed82's
ordinary source cells, and the conjugate directory is measured physically. -/
lemma retained_directories {n : ℕ} (axis : Fin (UniformAllAxisSeedPreparation.axisCount n))
 (s : State)
 (original : UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (conjugate : UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s) :
 s.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)=
  some (UniformAllAxisSeedPreparation.axisBase n axis.val) ∧
 s.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*axis.val+1)=
  some (UniformAllAxisSeedPreparation.radix n axis) ∧
 s.natHeap (UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)=
  some (UniformAllAxisConjugatePreparation.axisBase n axis.val) :=
 ⟨original.address axis axis.isLt,original.width axis axis.isLt,conjugate.address axis axis.isLt⟩
end
end ExactFourierCircuits.UniformDirectLeafCacheSource
