import DFTModelResidualClosedBasis
import DFTModelResidualPeakAddresses

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualClosedAddresses
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open DFTModelResidualClosedBasis (Meta)
noncomputable section

abbrev Prepared := p DFTModelResidualBasisImages.Params (Ty.a w)
abbrev WithTable := p Prepared (Ty.a w)

def basis : Prog false Meta Prepared := .comp DFTModelResidualClosedBasis.parameters
  (.fork (.atom .id) DFTModelResidualBasisImages.program)
def columns : Prog false Prepared w := .comp (.atom .fst) DFTModelResidualBasisImages.columns
def table : Prog false Meta WithTable := .comp basis
  (.fork (.atom .id) (.comp columns DFTModelResidualTable.program))
def params : Prog false WithTable DFTModelResidualBasisImages.Params :=
  .comp (.atom .fst) (.atom .fst)
def format : Prog false WithTable DFTModelResidualAddresses.Input := .fork
  (.comp params DFTModelResidualBasisImages.count) (.fork
    (binary .add (.comp params DFTModelResidualBasisImages.width)
      (.comp params DFTModelResidualBasisImages.spectators)) (.fork
      (.comp (.comp params DFTModelResidualBasisImages.columns) power)
      (.fork (.atom .snd) (.comp (.atom .fst) (.atom .snd)))))
/-- Actual direction scan, unit-image materialization, one q-XOR table,
and geometrically growing addresses. No preprinted metadata table is supplied. -/
def program : Prog false Meta (Ty.a w) := .comp table (.comp format DFTModelResidualAddresses.program)

attribute [local irreducible] DFTModelResidualClosedBasis.parameters DFTModelResidualBasisImages.program
  DFTModelResidualTable.program DFTModelResidualAddresses.program power

theorem format_value (q m r a p : ℕ) (images entries : Tape ℕ) :
    (run format (((q,(m,(r,(a,p)))),images),entries)).val=
      (q*m+r,(m+r,(2^q,(entries,images)))) := by
  simp [format,params,DFTModelResidualBasisImages.count,DFTModelResidualBasisImages.lowerCount,
    DFTModelResidualBasisImages.columns,DFTModelResidualBasisImages.width,
    DFTModelResidualBasisImages.spectators,binary,power_value,run,Code.run,Atom.run,
    NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem basis_value (z : Meta.T) :
    (run basis z).val=((run DFTModelResidualClosedBasis.parameters z).val,
      (run DFTModelResidualBasisImages.program (run DFTModelResidualClosedBasis.parameters z).val).val) := rfl

theorem table_value (z : Meta.T) :
    (run table z).val=((run basis z).val,
      (run DFTModelResidualTable.program (run basis z).val.1.1).val) := rfl

theorem program_value (q m r a p : ℕ) (raw : Tape ℕ)
    (prepared:(run DFTModelResidualClosedBasis.parameters (q,(m,(r,raw)))).val=(q,(m,(r,(a,p))))) :
    (run program (q,(m,(r,raw)))).val=
      (run DFTModelResidualAddresses.program
        (q*m+r,DFTModelResidualAddresses.parameters q (m+r)
          (run DFTModelResidualBasisImages.program (q,(m,(r,(a,p))))).val)).val := by
  change (run DFTModelResidualAddresses.program (run format (run table (q,(m,(r,raw)))).val).val).val=_
  rw [table_value,basis_value,prepared,format_value]
  rfl

/-- The emitted physical address tape is the actual native fiber permutation,
including spectator coordinates, from original raw direction values alone. -/
theorem source (q w r : ℕ) (v : BinaryFrames.Vec (Fin (w+1))) (raw : Tape ℕ)
    (qp:1 ≤ q) (data:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    ∃p:Fin (w+1),∃hp:v p=1,
      (run program (q,(w+1,(r,raw)))).val.len=2^(q*(w+1)+r) ∧
      ∀j:Fin (2^(q*(w+1)+r)),(run program (q,(w+1,(r,raw)))).val.look j.val 0=
        (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val := by
  obtain ⟨p,hp,prepared,images⟩:=DFTModelResidualClosedBasis.source_images q w r v raw data nonzero
  let imageTape:=(run DFTModelResidualBasisImages.program (q,(w+1,(r,((UniformBinaryXorCoordinates.encode v).val,p.val))))).val
  have imageBank:∀i:Fin (q*(w+1)+r),imageTape.look i.val 0=
      (DFTModelResidualBasisGeometry.permutation q w r v p hp
        (UniformBinaryXorCoordinates.encode (BinaryFrames.unit i))).val :=
    DFTModelResidualBasisGeometry.program_images q w r v p hp
  have cover:q*(w+1)+r ≤ q*((w+1)+r):=by nlinarith
  have small:∀i,i < q*(w+1)+r → imageTape.look i 0 < 2^(q*((w+1)+r)) := by
    intro i hi
    rw [imageBank ⟨i,hi⟩]
    exact (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) cover)
  have val:(run program (q,(w+1,(r,raw)))).val=
      DFTModelResidualAddresses.reference imageTape (q*(w+1)+r) := by
    rw [program_value q (w+1) r _ _ raw prepared,
      DFTModelResidualAddresses.program_value q ((w+1)+r) (q*(w+1)+r) imageTape small]
  refine ⟨p,hp,by rw [val];rfl,?_⟩
  intro j
  rw [val]
  have native:=UniformResidualPermutation.address_of_xor_equiv
    (DFTModelResidualBasisGeometry.permutation q w r v p hp)
    (DFTModelResidualBasisGeometry.zero q w r v p hp)
    (DFTModelResidualBasisGeometry.xor q w r v p hp)
    (fun i=>imageTape.look i 0) imageBank (q*(w+1)+r) 0 j.val le_rfl j.isLt
  simpa only [DFTModelResidualAddresses.reference,Tape.look,Tape.tab,j.isLt,↓reduceDIte,
    Nat.zero_xor] using native

end
end ExactFourierCircuits.DFTModelResidualClosedAddresses
