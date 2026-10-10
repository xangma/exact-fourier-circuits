import DFTModelSavingCostResidualSource
import DFTModelSavingDirectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingCost
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelClockControl
open UniformFixedNetworkScheduleMachine BinaryFrames FramedScheduleWords UniformFixedNetwork
open DFTModelSavingDirection
noncomputable section
attribute [local irreducible] DFTModelSavingResidual.program DFTModelSavingRecords.residual

def directionAllowance (q m r L C : ℕ) : ℕ :=
  (322*m+240*r+1284)*2^(q*m+r)+104*L+
    2^(q*(m-1)+r-UniformBatching.roleBits)*C+41*m+63

/-- A genuine edge row supplies its actual nonzero vector. Child work is
assumed only on the actual smaller paired bank shape, once per complete batch. -/
theorem direction_row_work {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (i : Fin edge.dimension) (k C : ℕ) (I : ℂ) (bank : Tape Tagged.T) (initial : Node.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1≤q) (wide : 2≤w)
    (fits : UniformBatching.roleBits≤q*w+r)
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (rowBill h r i.val raw initial ((k,I),bank)).work≤
      directionAllowance q (w+1) r bank.len C-1 := by
  have headers:=macro_headers q emb role edge raw source
  have bits:=row_source q emb role edge raw source i
  have nz : edgeVectors edge i≠0 := by
    intro eq
    have norm:=UniformResidualFibers.edgeVector_norm edge i
    rw [eq] at norm
    simp [BinaryFrames.dot] at norm
  let ctx : DFTModelResidualClosedBasis.Meta.T:=(q,(w+1,(r,row (w+1) i.val raw)))
  let x : DFTModelSavingResidualSetup.Input.T:=
    (ctx,((emb role).val,(raw.look 5 0,((k,I),bank))))
  have args:=DFTModelSavingResidualGeometry.source_arguments q w r (edgeVectors edge i)
    (row (w+1) i.val raw) (emb role).val (raw.look 5 0) k I bank qp bits nz fits
  have child : ∀g<(DFTModelSavingResidual.arguments x).2.1,
      (h ((DFTModelSavingResidual.arguments x).1,
        DFTModelClockBatch.sliced (DFTModelSavingResidual.arguments x).2.2.1 g
          (DFTModelSavingResidual.arguments x).2.2.2 Tagged.blank)).work≤C := by
    intro g _
    have param : (DFTModelSavingResidual.arguments x).1=(q,I) := args.1
    have size : (DFTModelSavingResidual.arguments x).2.2.1=UniformBatching.width*2^q := args.2.2.1
    rw [param]
    apply children I
    change (DFTModelSavingResidual.arguments x).2.2.1=UniformBatching.width*2^q
    exact size
  have cost:=residual_source_child_work h q w r (edgeVectors edge i)
    (row (w+1) i.val raw) (emb role).val (raw.look 5 0) k C I bank qp wide bits nz fits child
  change (Code.run DFTModelSavingResidual.program h x).work≤_ at cost
  simp only [rowBill,decoded,Bill.pay]
  rw [headers.1,headers.2.1,headers.2.2.1]
  change (Code.run DFTModelSavingResidual.program h x).work+(41*(w+1)+62)≤_
  dsimp only [directionAllowance]
  simp only [Nat.add_sub_cancel]
  omega

/-- The actual ascending edge loop, including runtime row extraction and one
paired recursive call per complete batch. -/
theorem direction_work {R S w : ℕ} (q r : ℕ) (emb : Fin R ↪ Fin S)
    {old new : Label (w+1)} (role : Fin R) (edge : NestedEdge old new)
    (raw : Tape ℕ) (source : RawSource (macroRecord q emb (.edge old new role edge)) raw)
    (k C : ℕ) (I : ℂ) (bank : Tape Tagged.T)
    (h : Handler DFTModelSavingRecords.Port) (qp : 1≤q) (wide : 2≤w)
    (fits : UniformBatching.roleBits≤q*w+r)
    (children : ∀ J (v : Tape Tagged.T),v.len=UniformBatching.width*2^q→
      (h ((q,J),v)).work≤C) :
    (Code.run DFTModelSavingRecords.residual h (r,(raw,((k,I),bank)))).work≤
      14+directionAllowance q (w+1) r bank.len C*edge.dimension := by
  have stepsCost : ∀n,n≤edge.dimension→
      (steps h r raw ((k,I),bank) n).work≤1+directionAllowance q (w+1) r bank.len C*n := by
    intro n
    induction n with
    | zero => intro _;exact le_rfl
    | succ n ih =>
      intro cap
      have shape:=steps_preserved h r n k I raw bank
      have same : (steps h r raw ((k,I),bank) n).val=
        ((k,I),(steps h r raw ((k,I),bank) n).val.2) := Prod.ext shape.1 rfl
      have rowCost:=direction_row_work q r emb role edge raw source ⟨n,by omega⟩ k C I
        (steps h r raw ((k,I),bank) n).val.2 ((k,I),bank) h qp wide fits children
      dsimp only at rowCost
      rw [shape.2] at rowCost
      change (steps h r raw ((k,I),bank) n).work+
        (rowBill h r n raw ((k,I),bank) (steps h r raw ((k,I),bank) n).val).work+1≤_
      rw [same,Nat.mul_add,Nat.mul_one]
      have prior:=ih (by omega)
      have pos : 1≤directionAllowance q (w+1) r bank.len C := by
        unfold directionAllowance
        omega
      omega
  rw [residual_run]
  have count:raw.look 6 0=edge.dimension:=(macro_headers q emb role edge raw source).2.2.2.2
  rw [count]
  have cost:=stepsCost edge.dimension le_rfl
  change (steps h r raw ((k,I),bank) edge.dimension).work+13≤_
  omega

end
end ExactFourierCircuits.DFTModelSavingCost
