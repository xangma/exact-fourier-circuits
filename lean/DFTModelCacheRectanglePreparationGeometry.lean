import DFTModelCacheSpectrumSource
import DFTModelCacheDescriptorRows
import UniformLocalRectangleBankMachine

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open UniformLocalRectangleDescriptors UniformWorkspacePlanner
noncomputable section

def height (q : Row) : ℕ := exponent q.a q.e
def width (q : Row) : ℕ := UniformRadixTwoDAG.width (height q)

/-- Only kernel geometry is represented here. Physical placement is retained
in the original row; its offset is deliberately not added to Newton indices. -/
def parameters (r : ℕ) (q : Row) : UniformRankKernelMachine.Parameters :=
  ⟨0,0,r,r,q.a,q.e,q.i0,q.j0,q.split,width q,0⟩

/-- Provenance from the actual nonempty node descriptor printer. -/
def ProducedRow (r : ℕ) (q : Row) : Prop :=
  ∃v o,v≤r ∧ q∈UniformLocalCacheTreeCoverage.currentRows
    (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)

theorem produced_geometry {r : ℕ} {q : Row} (source : ProducedRow r q) :
    0<q.a ∧ 0<q.e ∧ q.i0+q.a≤r ∧ q.split<r ∧
      q.split≤q.i0 ∧ q.j0+q.e≤q.split ∧ q.width≤r := by
  obtain ⟨v,o,vr,hq⟩:=source
  unfold UniformLocalCacheTreeCoverage.currentRows at hq
  dsimp only [UniformLocalCacheTreeMachine.Task.width] at hq
  split_ifs at hq with empty
  · simp only [List.not_mem_nil] at hq
  · have hv : 0<selected v := by omega
    have vn : 2≤v := by omega
    obtain ⟨ha,he,hi,hs,hsi,hj,_,hw,_⟩:=
      UniformLocalRectangleBankMachine.rows_geometry v o q vn hv hq
    exact ⟨ha,he,hi.trans vr,lt_of_lt_of_le hs vr,hsi,hj,hw.le.trans vr⟩

theorem produced_width {r : ℕ} {q : Row} (source : ProducedRow r q) :
    q.a≤width q ∧ q.e≤width q ∧ width q≤8*r := by
  obtain ⟨ha,he,hi,hs,hsi,hj,_⟩:=produced_geometry source
  have noAlias:=UniformWorkspacePlanner.no_alias q.a q.e
  have cap:=UniformWorkspacePlanner.width_bound (by omega : 0<q.a+q.e)
  change 2*(q.a+q.e)≤2^height q at noAlias
  change 2^height q≤4*(q.a+q.e) at cap
  rw [width,UniformRadixTwoDAG.width_eq]
  omega

theorem produced_shape {r : ℕ} {q : Row} (source : ProducedRow r q) :
    DFTModelCacheDisplacement.Shape (parameters r q) r := by
  obtain ⟨ha,he,hi,hs,hsi,hj,_⟩:=produced_geometry source
  obtain ⟨wa,we,_⟩:=produced_width source
  exact ⟨ha,he,hi,hs,hsi,hj,wa,we⟩

theorem produced_height {r : ℕ} {q : Row} (source : ProducedRow r q) :
    height q≤Nat.clog 2 r+2 := by
  obtain ⟨ha,he,hi,hs,hsi,hj,_⟩:=produced_geometry source
  exact UniformWorkspacePlanner.exponent_bound (by omega) (by omega)

/-- This ordinary master-order property discharges every descriptor width.
No width or root table is an entry value of the program. -/
structure Master (r D : ℕ) : Prop where
  positive : 0<D
  radixDiv : r∣D
  binaryDiv : 2^(Nat.clog 2 r+2)∣D

theorem produced_divisor {r D : ℕ} {q : Row}
    (source : ProducedRow r q) (master : Master r D) : width q∣D := by
  have lower : 2^height q∣2^(Nat.clog 2 r+2) :=
    pow_dvd_pow 2 (produced_height source)
  simpa only [width,UniformRadixTwoDAG.width_eq] using lower.trans master.binaryDiv

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
