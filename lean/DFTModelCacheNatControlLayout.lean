import UniformCrossHeightPreparationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatControlLayout

def convG (K : ℕ) := 3*K*2^K+2*2^K
def gates (K a : ℕ) := 6*convG K+2*a
def heights (K : ℕ) := 8*K+7
def tape (K : ℕ) := 5*convG K
def depths (K a : ℕ) := tape K+5*gates K a
def order (K a e : ℕ) := depths K a+e+1+gates K a
def buckets (K a e : ℕ) := order K a e+gates K a*(gates K a+1)
def rows (K a e : ℕ) := buckets K a e+gates K a+2
def colors (K a e : ℕ) := rows K a e+6*gates K a*heights K
def palette (K a e : ℕ) := colors K a e+2*gates K a*heights K
def directory (K a e : ℕ) := palette K a e+12
def heapLength (K a e : ℕ) := directory K a e+3*heights K

/-- Coefficient addresses are local labels: 7N source slots and six constants.
This integer-only machine does not inspect the scalar bank they will name. -/
def parameters (K a e : ℕ) (enabled : Bool) : UniformCrossHeightPreparationMachine.Parameters where
  K:=K
  a:=a
  e:=e
  T:=tape K
  Q:=order K a e
  R:=buckets K a e
  D:=rows K a e
  F:=colors K a e
  U:=palette K a e
  J:=directory K a e
  C:=0
  P:=7*2^K
  enabled:=enabled

theorem topology_gate_count (K : ℕ) : UniformToeplitzCrossTopologyMachine.G K=convG K :=
  (UniformConvolutionDAG.records_length K).symm.trans (UniformConvolutionDAG.gate_count K)

theorem parameters_gates (K a e : ℕ) (enabled : Bool) :
    UniformCrossHeightPreparationMachine.gates (parameters K a e enabled)=gates K a := by
  simp only [UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.widthOf,
    parameters,UniformRadixTwoDAG.width_eq,gates,convG]

theorem layout (K a e : ℕ) (enabled : Bool) : UniformCrossHeightPreparationMachine.Layout (parameters K a e enabled) := by
  constructor <;>
    simp only [parameters,UniformCrossHeightPreparationMachine.rowBase,UniformCrossHeightPreparationMachine.colorBase,UniformCrossHeightPreparationMachine.widthOf,UniformRadixTwoDAG.width_eq,UniformCrossHeightPreparationMachine.gates,UniformCrossHeightPreparationMachine.height,
      tape,depths,order,buckets,rows,colors,palette,directory,gates,heights,convG] <;> omega

theorem topology_separation (K : ℕ) : 0+5*UniformToeplitzCrossTopologyMachine.G K≤tape K := by
  rw [topology_gate_count]
  simp only [tape,Nat.zero_add,le_refl]

theorem depth_separation (K a e : ℕ) : tape K+5*gates K a≤depths K a ∧
    depths K a+(e+1+gates K a)≤order K a e := by
  constructor <;> simp only [depths,order] <;> omega

theorem bucket_separation (K a e : ℕ) :
    depths K a+e+1+gates K a≤order K a e ∧
    order K a e+gates K a*(gates K a+1)≤buckets K a e ∧
    buckets K a e+gates K a+2≤rows K a e := ⟨le_rfl,le_rfl,le_rfl⟩

def size (K a e : ℕ) := gates K a+K+2^K+a+e+1

/-- All local heap addresses fit a fixed polynomial in the local gate count,
exponent, radix and rectangle extents. No global n-sized arena is allocated. -/
theorem local_heap_polynomial (K a e : ℕ) :
    heapLength K a e≤200*(size K a e+1)^2 := by
  have hpow:0≤2^K:=Nat.zero_le _
  let q:=size K a e+1
  have hq:1≤q:=by dsimp [q,size];omega
  have hg:gates K a≤q:=by dsimp [q,size];omega
  have hk:K≤q:=by dsimp [q,size];omega
  have he:e≤q:=by dsimp [q,size];omega
  have hc:convG K≤q:=by dsimp [q,size,gates];omega
  have hgg:gates K a*gates K a≤q*q:=Nat.mul_self_le_mul_self hg
  have hgh:gates K a*K≤q*q:=Nat.mul_le_mul hg hk
  change heapLength K a e≤200*q^2
  unfold heapLength directory palette colors rows buckets order depths tape heights
  nlinarith [Nat.zero_le (q*q)]

theorem size_radix_polynomial (K a e r : ℕ) (hN : 2^K≤8*r) (hK : K≤8*r)
    (ha : a≤r) (he : e≤r) : size K a e+1≤2000*(r+1)^2 := by
  have hKN:K*2^K≤64*(r*r):=by nlinarith [Nat.mul_le_mul hK hN]
  unfold size gates convG
  nlinarith

theorem heap_radix_polynomial (K a e r : ℕ) (hN : 2^K≤8*r) (hK : K≤8*r)
    (ha : a≤r) (he : e≤r) : heapLength K a e≤800000000*(r+1)^4 := by
  have h:=local_heap_polynomial K a e
  have hs:=Nat.mul_self_le_mul_self (size_radix_polynomial K a e r hN hK ha he)
  nlinarith

end ExactFourierCircuits.DFTModelCacheNatControlLayout
