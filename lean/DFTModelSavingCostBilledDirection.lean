import DFTModelSavingCostBilledAggregate
import DFTModelSavingDirectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl DFTModelSavingResidualSetup
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program UniformBatching.width

def residualChildrenWork (h : Handler DFTModelSavingResidual.Port) (x : Input.T) : ℕ :=
  ∑g∈Finset.range (DFTModelSavingResidual.arguments x).2.1,
    (h ((DFTModelSavingResidual.arguments x).1,
      DFTModelClockBatch.sliced (DFTModelSavingResidual.arguments x).2.2.1 g
        (DFTModelSavingResidual.arguments x).2.2.2 Tagged.blank)).work

/-- Actual row extraction and actual ascending-loop step, retaining the exact
sum of the same paired recursive child work. -/
theorem direction_row_actual_work {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (j : Fin edge.dimension) (k : ℕ) (I : ℂ) (bank : Tape Tagged.T) (initial : DFTModelClockControl.Node.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1≤q) (wide : 2≤w)
    (len : bank.len=UniformBatching.width*2^(q*(w+1)+r)) :
    (rowBill h r j.val raw initial ((k,I),bank)).work+1≤
      (363*(w+1)+240*r+1347+104*UniformBatching.width)*2^(q*(w+1)+r)+
        residualChildrenWork h (decoded r j.val raw ((k,I),bank)) := by
  have headers:=macro_headers q emb role edge raw source
  have bits:=row_source q emb role edge raw source j
  have nz : edgeVectors edge j≠0 := by
    intro eq
    have norm:=UniformResidualFibers.edgeVector_norm edge j
    rw [eq] at norm
    simp [BinaryFrames.dot] at norm
  let x : Input.T:=((q,(w+1,(r,row (w+1) j.val raw))),
    ((emb role).val,(raw.look 5 0,((k,I),bank))))
  have same : decoded r j.val raw ((k,I),bank)=x := by
    simp only [decoded]
    rw [headers.1,headers.2.1,headers.2.2.1]
  have cap:=residual_source_work h q w r (edgeVectors edge j)
    (row (w+1) j.val raw) (emb role).val (raw.look 5 0) k I bank qp wide bits nz
  change (Code.run DFTModelSavingResidual.program h x).work≤_ at cap
  rw [len] at cap
  have paid : (rowBill h r j.val raw initial ((k,I),bank)).work+1=
      (Code.run DFTModelSavingResidual.program h x).work+41*(w+1)+63 := by
    simp only [rowBill,Bill.pay,same,headers.2.1]
    omega
  rw [paid,same]
  change _≤_+residualChildrenWork h x
  have positive : 1≤2^(q*(w+1)+r) := Nat.two_pow_pos _
  have reserve:=Nat.le_mul_of_pos_right (41*(w+1)+63) positive
  unfold residualChildrenWork
  nlinarith only [cap,reserve]

/-- Operational callers may now substitute their aggregate actual child
elapsed time. A single K pays every depth. -/
theorem direction_row_billed_work {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (j : Fin edge.dimension) (k K localTicks childTicks : ℕ) (I : ℂ)
    (bank : Tape Tagged.T) (initial : DFTModelClockControl.Node.T) (h : Handler DFTModelSavingRecords.Port)
    (qp : 1≤q) (wide : 2≤w) (len : bank.len=UniformBatching.width*2^(q*(w+1)+r))
    (coefficient : 363*(w+1)+240*r+1347+104*UniformBatching.width≤K)
    (localBound : 2^(q*(w+1)+r)+
      (DFTModelSavingResidual.arguments (decoded r j.val raw ((k,I),bank))).2.1≤localTicks)
    (children : residualChildrenWork h (decoded r j.val raw ((k,I),bank))≤
      K*childTicks+K*(DFTModelSavingResidual.arguments (decoded r j.val raw ((k,I),bank))).2.1) :
    (rowBill h r j.val raw initial ((k,I),bank)).work+1≤K*(localTicks+childTicks) :=
  (direction_row_actual_work q r emb role edge raw source j k I bank initial h qp wide len).trans
    (absorb_billed_aggregate _ K _ _ localTicks _ childTicks coefficient localBound children)

end
end ExactFourierCircuits.DFTModelSavingCost
