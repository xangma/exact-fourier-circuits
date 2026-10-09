import DFTModelResidualClosedMovement
import DFTModelResidualBasisBounds

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelResidualClosedBounds
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open DFTModelResidualClosedAddresses
noncomputable section

attribute [local irreducible] DFTModelResidualClosedBasis.parameters
  DFTModelResidualBasisImages.program DFTModelResidualTable.program
  DFTModelResidualAddresses.program power

theorem basis_work (z:DFTModelResidualClosedBasis.Meta.T) :
    (run basis z).work=(run DFTModelResidualClosedBasis.parameters z).work+
      (run DFTModelResidualBasisImages.program (run DFTModelResidualClosedBasis.parameters z).val).work+3 := by
  change (run DFTModelResidualClosedBasis.parameters z).work+
    (1+(run DFTModelResidualBasisImages.program (run DFTModelResidualClosedBasis.parameters z).val).work+1)+1=_
  omega

theorem table_work (z:DFTModelResidualClosedBasis.Meta.T) :
    (run table z).work=(run basis z).work+
      (run DFTModelResidualTable.program (run basis z).val.1.1).work+7 := by
  change (run basis z).work+(1+(3+(run DFTModelResidualTable.program (run basis z).val.1.1).work+1)+1)+1=_
  omega

theorem format_work (q m r a p:ℕ) (images entries:Tape ℕ) :
    (run format (((q,(m,(r,(a,p)))),images),entries)).work=8*q+56 := by
  have pw:=power_work q
  simp only [format,params,DFTModelResidualBasisImages.count,DFTModelResidualBasisImages.lowerCount,
    DFTModelResidualBasisImages.columns,DFTModelResidualBasisImages.width,
    DFTModelResidualBasisImages.spectators,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  change (Code.run power () q).work=8*q+4 at pw
  omega

theorem format_peak (q m r a p:ℕ) (images entries:Tape ℕ) :
    (run format (((q,(m,(r,(a,p)))),images),entries)).peak ≤ q*m+r+m+r+2^q+2 := by
  have pw:=power_peak q
  have pos:=Nat.two_pow_pos q
  simp only [format,params,DFTModelResidualBasisImages.count,DFTModelResidualBasisImages.lowerCount,
    DFTModelResidualBasisImages.columns,DFTModelResidualBasisImages.width,
    DFTModelResidualBasisImages.spectators,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,max_le_iff]
  change (Code.run power () q).peak ≤ 2^q at pw
  repeat' apply And.intro
  all_goals omega

theorem format_valid (q m r a p:ℕ) (images entries:Tape ℕ) :
    (run format (((q,(m,(r,(a,p)))),images),entries)).valid := by
  have pw:=power_valid q
  simpa only [format,params,DFTModelResidualBasisImages.count,DFTModelResidualBasisImages.lowerCount,
    DFTModelResidualBasisImages.columns,DFTModelResidualBasisImages.width,
    DFTModelResidualBasisImages.spectators,binary,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,and_true,true_and] using pw

/-- Explicit charged work: the quadratic bit-metadata preparation happens once,
then the table once, then a geometric whole-array address traversal. -/
def budget (q m r:ℕ) : ℕ :=
  60*m+(8*(q*m+r)+204)*(q*m+r)+(86*q+36)*(2^q*2^q)+16*q+
    (240*(m+r)+215)*2^(q*m+r)+200

theorem program_work (q w r a p:ℕ) (raw:Tape ℕ) (pivot:p<w+1)
    (prepared:(run DFTModelResidualClosedBasis.parameters (q,(w+1,(r,raw)))).val=
      (q,(w+1,(r,(a,p)))))
    (small:∀i,i<q*(w+1)+r → 
      (run DFTModelResidualBasisImages.program (q,(w+1,(r,(a,p))))).val.look i 0<2^(q*((w+1)+r))) :
    (run program (q,(w+1,(r,raw)))).work ≤ budget q (w+1) r := by
  let images:=(run DFTModelResidualBasisImages.program (q,(w+1,(r,(a,p))))).val
  have pc:=DFTModelResidualClosedBasis.parameters_work q (w+1) r raw
  have ic:=DFTModelResidualBasisBounds.program_work q w r a p pivot
  have ac:=DFTModelResidualAddresses.program_work q ((w+1)+r) (q*(w+1)+r) images small
  change (run program (q,(w+1,(r,raw)))).work ≤ _
  change (run table (q,(w+1,(r,raw)))).work+
    ((run format (run table (q,(w+1,(r,raw)))).val).work+
      (run DFTModelResidualAddresses.program
        (run format (run table (q,(w+1,(r,raw)))).val).val).work+1)+1 ≤ _
  rw [table_work,basis_work,table_value,basis_value,prepared,format_work,format_value,
    DFTModelResidualTable.program_work]
  dsimp only
  change (run DFTModelResidualAddresses.program
    (q*(w+1)+r,((w+1)+r,(2^q,((run DFTModelResidualTable.program q).val,images))))).work ≤ _ at ac
  dsimp only [images] at ac
  unfold budget
  omega

theorem program_valid (z:DFTModelResidualClosedBasis.Meta.T) : (run program z).valid := by
  rcases z with ⟨q,m,r,raw⟩
  have pc:=DFTModelResidualClosedBasis.parameters_valid q m r raw
  obtain ⟨cq,cm,cr,ca,cp,h⟩ : ∃cq cm cr ca cp,
      (run DFTModelResidualClosedBasis.parameters (q,(m,(r,raw)))).val=(cq,(cm,(cr,(ca,cp)))) := by
    rcases (run DFTModelResidualClosedBasis.parameters (q,(m,(r,raw)))).val with ⟨cq,cm,cr,ca,cp⟩
    exact ⟨cq,cm,cr,ca,cp,rfl⟩
  have bc:(run basis (q,(m,(r,raw)))).valid := by
    change (run DFTModelResidualClosedBasis.parameters (q,(m,(r,raw)))).valid ∧
      (True ∧ (run DFTModelResidualBasisImages.program
        (run DFTModelResidualClosedBasis.parameters (q,(m,(r,raw)))).val).valid ∧ True)
    rw [h]
    exact ⟨pc,trivial,DFTModelResidualBasisImages.program_valid cq cm cr ca cp,trivial⟩
  have tc:(run table (q,(m,(r,raw)))).valid := by
    change (run basis (q,(m,(r,raw)))).valid ∧
      (True ∧ ((True ∧ True) ∧ (run DFTModelResidualTable.program (run basis (q,(m,(r,raw)))).val.1.1).valid) ∧ True)
    exact ⟨bc,trivial,⟨⟨trivial,trivial⟩,DFTModelResidualTable.program_valid _⟩,trivial⟩
  have fv:(run format (run table (q,(m,(r,raw)))).val).valid := by
    rw [table_value,basis_value,h]
    exact format_valid _ _ _ _ _ _ _
  exact ⟨tc,fv,DFTModelResidualAddresses.program_valid _⟩

end
end ExactFourierCircuits.DFTModelResidualClosedBounds
