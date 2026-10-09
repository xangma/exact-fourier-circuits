import DFTModelResidualClosedPaired
import DFTModelResidualPeakPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def raw11:Tape ℕ:=Tape.tab 2 (fun _=>1)
def raw011:Tape ℕ:=Tape.tab 3 (fun i=>if i=0 then 0 else 1)
def ctx:DFTModelResidualClosedBasis.Meta.T:=(1,(2,(1,raw11)))
def addresses:Tape ℕ:=(run DFTModelResidualClosedAddresses.program ctx).val

theorem mask11:(run DFTModelResidualBasisMask.program (2,raw11)).val=3:=by rfl
theorem pivot11:(run DFTModelResidualBasisPivot.program (2,raw11)).val=0:=by rfl
theorem mask011:(run DFTModelResidualBasisMask.program (3,raw011)).val=6:=by rfl
theorem pivot011:(run DFTModelResidualBasisPivot.program (3,raw011)).val=1:=by rfl
theorem parameters:(run DFTModelResidualClosedBasis.parameters ctx).val=(1,(2,(1,(3,0)))):=by rfl
theorem basis0:(run DFTModelResidualClosedBasis.program (2,(2,(0,raw11)))).val.look 0 99=3:=by rfl
theorem basis1:(run DFTModelResidualClosedBasis.program (2,(2,(0,raw11)))).val.look 1 99=12:=by rfl
theorem basis2:(run DFTModelResidualClosedBasis.program (2,(2,(0,raw11)))).val.look 2 99=2:=by rfl
theorem basis3:(run DFTModelResidualClosedBasis.program (2,(2,(0,raw11)))).val.look 3 99=8:=by rfl

theorem addresses_length:addresses.len=8:=by rfl
theorem address0:addresses.look 0 99=0:=by rfl
theorem address1:addresses.look 1 99=3:=by rfl
theorem address2:addresses.look 2 99=2:=by rfl
theorem address3:addresses.look 3 99=1:=by rfl
theorem spectator4:addresses.look 4 99=4:=by rfl
theorem spectator7:addresses.look 7 99=5:=by rfl
theorem address_two_columns:(run DFTModelResidualClosedAddresses.program
    (2,(2,(0,raw11)))).val.look 2 99=12:=by rfl
theorem address_later_pivot:(run DFTModelResidualClosedAddresses.program
    (1,(3,(0,raw011)))).val.look 3 99=7:=by rfl

def bank:Tape ℕ:=Tape.tab 24 (fun j=>100+j)
def child:Tape ℕ:=Tape.tab 8 (fun j=>1000+j)
def gathered:(DFTModelResidualClosedRoleStages.Context w).T:=
  (run (DFTModelResidualClosedRole.gather w) (ctx,(1,bank))).val
def scattered:Tape ℕ:=(run (DFTModelResidualClosedRole.scatter w)
  ((ctx,(1,bank)),(gathered.2.1,child))).val

theorem retained_context:gathered.1=(ctx,(1,bank)):=by rfl
theorem gather_length:gathered.2.2.len=8:=by rfl
theorem gather_index0:gathered.2.2.look 0 0=108:=by rfl
theorem gather_index1:gathered.2.2.look 1 0=111:=by rfl
theorem gather_index7:gathered.2.2.look 7 0=113:=by rfl
theorem scatter_length:scattered.len=24:=by rfl
theorem scatter_native0:scattered.look 8 0=1000:=by rfl
theorem scatter_native1:scattered.look 11 0=1001:=by rfl
theorem scatter_native3:scattered.look 9 0=1003:=by rfl
theorem preceding_role:scattered.look 3 0=103:=by rfl
theorem following_role:scattered.look 22 0=122:=by rfl

def taggedBank:Tape DFTModelAffine.Tagged.T:=Tape.tab 24 (fun j=>
  if j%2=0 then DFTModelAffine.tagged false j 0 else DFTModelAffine.tagged true j Complex.I)
def taggedGathered:(DFTModelResidualClosedRoleStages.Context DFTModelAffine.Tagged).T:=
  (run (DFTModelResidualClosedRole.gather DFTModelAffine.Tagged) (ctx,(1,taggedBank))).val

theorem gather_exact_tag:(taggedGathered.2.2.look 1 DFTModelAffine.Tagged.blank).1=1:=by rfl
theorem gather_exact_baseline:(taggedGathered.2.2.look 1 DFTModelAffine.Tagged.blank).2.1=11:=by rfl
theorem gather_exact_difference:(taggedGathered.2.2.look 1 DFTModelAffine.Tagged.blank).2.2=Complex.I:=by rfl
theorem gather_prepared_tag:(taggedGathered.2.2.look 2 DFTModelAffine.Tagged.blank).1=0:=by rfl
theorem gather_prepared_difference:(taggedGathered.2.2.look 2 DFTModelAffine.Tagged.blank).2.2=0:=by rfl

/-- Negative source controls: zero/missing direction input does not satisfy the
nonzero raw-direction theorem; the total code does not fabricate that premise. -/
theorem zero_direction_duplicates:(run DFTModelResidualClosedAddresses.program
  (1,(2,(0,Tape.tab 2 (fun _=>0))))).val.look 1 99=0:=by rfl
theorem missing_direction_pivot:(run DFTModelResidualBasisPivot.program (2,Tape.empty ℕ)).val=2:=by rfl
theorem width_one:(run DFTModelResidualClosedAddresses.program
  (1,(1,(0,Tape.tab 1 (fun _=>1))))).val.look 1 99=1:=by rfl

theorem actual_gather_work:(run (DFTModelResidualClosedRole.gather w) (ctx,(1,bank))).work=
    (run DFTModelResidualClosedAddresses.program ctx).work+424:=by
  have h:=DFTModelResidualClosedRole.gather_work w ctx 1 bank
  have len:(run DFTModelResidualClosedAddresses.program ctx).val.len=8:=by rfl
  rw [len] at h
  exact h

theorem actual_scatter_work:(run (DFTModelResidualClosedRole.scatter w)
  ((ctx,(1,bank)),(addresses,child))).work ≤ 2664:=by
  have h:=DFTModelResidualClosedRole.scatter_work w ctx 1 bank addresses child
  rw [addresses_length,show bank.len=24 from rfl] at h
  exact h

end
end ExactFourierCircuits.DFTModelResidualClosedFixtures
