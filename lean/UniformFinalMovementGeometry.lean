import UniformFinalMovementFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalMovementGeometry
open UniformMachine UniformFinalMovementFrame
noncomputable section
local notation "c" => UniformActualGlobalConstants.constants
abbrev V (n:ℕ):ℕ:=UniformInitialPreparation.len n
def S (n:ℕ):ℕ:=2*UniformJointAllocation.slab c n
def T (n:ℕ):ℕ:=3*UniformJointAllocation.slab c n
abbrev B (n:ℕ):ℕ:=UniformJointAllocation.envelope c n
def AP (n:ℕ):ℕ:=UniformKernelSpectrumStorage.alphaBase c n
def BI (n:ℕ):ℕ:=UniformKernelSpectrumStorage.betaInverseBase c n

structure Fits (n:ℕ):Prop where
 adjacent:Q n+V n=S n
 beforeSource:Q n≤S n
 beforeTarget:Q n≤T n
 disjoint:UniformPermutationMachine.Disjoint (S n) (T n) (V n)
 source:S n+V n+V n≤B n
 target:T n+V n≤B n
 alpha:AP n+V n≤B n
 inverse:BI n+V n≤B n
 code:64≤B n

lemma fits {n:ℕ}(hn:0<n):Fits n:=by
 have arithmetic:=UniformJointAllocation.actual_arithmetic c n hn
 dsimp only at arithmetic
 have end_eq:=UniformKernelSpectrumStorage.end_eq c hn
 have tables:=UniformKernelSpectrumStorage.tables_adjacent c hn
 have reserve:=UniformKernelSpectrumStorage.reserve c hn
 have large:=UniformJointAllocation.fixed_large c
 unfold UniformKernelSpectrumStorage.betaInverseBase at tables
 constructor <;> try dsimp only[V]
 · exact end_eq
 · unfold Q UniformKernelSpectrumStorage.base S;omega
 · unfold Q UniformKernelSpectrumStorage.base T;omega
 · apply Or.inl
   unfold S T;omega
 · unfold S B UniformJointAllocation.envelope;omega
 · unfold T B UniformJointAllocation.envelope;omega
 · unfold AP B UniformJointAllocation.envelope;omega
 · unfold BI B UniformJointAllocation.envelope UniformKernelSpectrumStorage.betaInverseBase;omega
 · unfold B UniformJointAllocation.envelope;omega

lemma roles_before_target {n:ℕ}(hn:0<n):
 S n+UniformRecursiveSelfCallMachine.W*V n≤T n:=by
 have h:=UniformJointAllocation.actual_arithmetic c n hn
 dsimp only at h
 rw[UniformActualGlobalConstants.roles_eq,Nat.mul_assoc] at h
 dsimp only[S,T,V]
 omega

end
end ExactFourierCircuits.UniformFinalMovementGeometry
