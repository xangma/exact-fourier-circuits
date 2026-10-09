import DFTModelResidualClosedRoleStages

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualClosedRole
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualClosedBasis (Meta)
open DFTModelResidualClosedRoleStages
noncomputable section

/-- Exactly one native role is extracted. The original complete role bank and
computed addresses remain in the context while the child changes the slice. -/
def prepare (t:Ty) : Prog false (Input t) (Addressed t) :=
  .fork (.atom .id) (.comp (.atom .fst) DFTModelResidualClosedAddresses.program)
def gather (t:Ty) : Prog false (Input t) (Context t) := .comp (prepare t)
  (.fork (.atom .fst) (.fork (.atom .snd)
    (.comp (.fork (.atom .snd) (slice t)) (DFTModelResidualMovement.gather t))))
/-- Scatter consumes the retained generated addresses, then one whole-bank tab
replaces the selected role; every unrelated role is copied as an entire element. -/
def scatter (t:Ty) : Prog false (Context t) (Ty.a t) := .comp
  (.fork (.atom .fst) (.comp (.atom .snd) (DFTModelResidualMovement.scatter t))) (replace t)

attribute [local irreducible] DFTModelResidualClosedAddresses.program
  DFTModelResidualMovement.gather DFTModelResidualMovement.scatter slice replace

theorem gather_value (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) :
    (run (gather t) (ctx,(a,bank))).val=
      ((ctx,(a,bank)),((run DFTModelResidualClosedAddresses.program ctx).val,
        (run (DFTModelResidualMovement.gather t)
          ((run DFTModelResidualClosedAddresses.program ctx).val,
            (run (slice t) ((ctx,(a,bank)),(run DFTModelResidualClosedAddresses.program ctx).val)).val)).val)) := rfl

theorem gather_work (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) :
    (run (gather t) (ctx,(a,bank))).work=
      (run DFTModelResidualClosedAddresses.program ctx).work+
        50*(run DFTModelResidualClosedAddresses.program ctx).val.len+24 := by
  have sw:=slice_work t ctx a bank (run DFTModelResidualClosedAddresses.program ctx).val
  have gw:=DFTModelResidualMovement.gather_work t
    (run DFTModelResidualClosedAddresses.program ctx).val
    (run (slice t) ((ctx,(a,bank)),(run DFTModelResidualClosedAddresses.program ctx).val)).val
  simp only [gather,prepare,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  change (Code.run (slice t) () ((ctx,(a,bank)),
    (Code.run DFTModelResidualClosedAddresses.program () ctx).val)).work=
      33*(Code.run DFTModelResidualClosedAddresses.program () ctx).val.len+6 at sw
  change (Code.run (DFTModelResidualMovement.gather t) ()
    ((Code.run DFTModelResidualClosedAddresses.program () ctx).val,
      (Code.run (slice t) () ((ctx,(a,bank)),
        (Code.run DFTModelResidualClosedAddresses.program () ctx).val)).val)).work=
      17*(Code.run DFTModelResidualClosedAddresses.program () ctx).val.len+6 at gw
  omega

theorem scatter_value (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ) (child:Tape t.T) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).val=
      (run (replace t) ((ctx,(a,old)),(run (DFTModelResidualMovement.scatter t) (p,child)).val)).val := rfl

theorem scatter_work (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ) (child:Tape t.T) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).work ≤ 18*p.len+104*old.len+24 := by
  have sw:=DFTModelResidualMovement.scatter_work t p child
  have rw:=replace_work t ctx a old (run (DFTModelResidualMovement.scatter t) (p,child)).val
  change 1+(1+(run (DFTModelResidualMovement.scatter t) (p,child)).work+1)+1+
    (run (replace t) ((ctx,(a,old)),(run (DFTModelResidualMovement.scatter t) (p,child)).val)).work+1 ≤ _
  omega

theorem gathered_lookup (t:Ty) (ctx:Meta.T) (a:ℕ) (bank:Tape t.T) (L:ℕ)
    (len:(run DFTModelResidualClosedAddresses.program ctx).val.len=L)
    (j:Fin L) (address:(run DFTModelResidualClosedAddresses.program ctx).val.look j.val 0<L) :
    (run (gather t) (ctx,(a,bank))).val.2.2.look j.val t.blank=
      bank.look (a*L+(run DFTModelResidualClosedAddresses.program ctx).val.look j.val 0) t.blank := by
  rw [gather_value,DFTModelResidualMovement.gather_value,slice_value]
  have jl:j.val < (run DFTModelResidualClosedAddresses.program ctx).val.len := by rw [len];exact j.isLt
  simp only [Tape.look,Tape.tab,jl,↓reduceDIte]
  simp only [Tape.look,jl,↓reduceDIte] at address
  simp only [len,address,↓reduceDIte]


theorem scatter_len (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ) (child:Tape t.T) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).val.len=old.len := by
  rw [scatter_value,replace_len]

theorem native_len (t:Ty) (p:Tape ℕ) (child:Tape t.T) :
    (run (DFTModelResidualMovement.scatter t) (p,child)).val.len=p.len := by
  unfold DFTModelResidualMovement.scatter
  exact DFTModelResidualMovement.scatterSteps_len t p child p.len

theorem scatter_permutation (t:Ty) (ctx:Meta.T) (a L:ℕ) (old:Tape t.T) (p:Tape ℕ)
    (child:Tape t.T) (phi:Fin L≃Fin L) (plen:p.len=L)
    (table:∀j:Fin L,p.look j.val 0=(phi j).val) (room:a*L+L ≤ old.len) (j:Fin L) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).val.look (a*L+(phi j).val) t.blank=
      child.look j.val t.blank := by
  let next:=(run (DFTModelResidualMovement.scatter t) (p,child)).val
  have nl:next.len=L:=(native_len t p child).trans plen
  have lookup:=DFTModelResidualMovement.scatter_value t phi p child plen table j
  have jj:(phi j).val<next.len:=by rw [nl];exact (phi j).isLt
  have fit:a*next.len+(phi j).val<old.len:=by rw [nl];have h:=(phi j).isLt;omega
  rw [scatter_value]
  have inside:=replace_inside t ctx a old next ⟨(phi j).val,jj⟩ fit
  simpa only [nl] using inside.trans lookup

theorem scatter_outside (t:Ty) (ctx:Meta.T) (a:ℕ) (old:Tape t.T) (p:Tape ℕ)
    (child:Tape t.T) (j:Fin old.len)
    (outside:¬(a*p.len ≤ j.val ∧ j.val<a*p.len+p.len)) :
    (run (scatter t) ((ctx,(a,old)),(p,child))).val.look j.val t.blank=old.look j.val t.blank := by
  rw [scatter_value]
  apply replace_outside t ctx a old (run (DFTModelResidualMovement.scatter t) (p,child)).val j
  rw [native_len]
  exact outside

/-- Concrete direction-generated gather, with no supplied pivot, unit images,
XOR table or address permutation. Entire tagged elements move unchanged. -/
theorem source_gather (t:Ty) (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1)))
    (raw:Tape ℕ) (a:ℕ) (bank:Tape t.T) (qp:1 ≤ q)
    (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0) :
    ∃p:Fin (w+1),∃hp:v p=1,
      (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).val.1=((q,(w+1,(r,raw))),(a,bank)) ∧
      (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).val.2.1.len=2^(q*(w+1)+r) ∧
      (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).val.2.2.len=2^(q*(w+1)+r) ∧
      ∀j:Fin (2^(q*(w+1)+r)),
        (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).val.2.1.look j.val 0=
          (DFTModelResidualBasisGeometry.permutation q w r v p hp j).val ∧
        (run (gather t) ((q,(w+1,(r,raw))),(a,bank))).val.2.2.look j.val t.blank=
          bank.look (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) t.blank := by
  obtain ⟨p,hp,len,table⟩:=DFTModelResidualClosedAddresses.source q w r v raw qp source nonzero
  refine ⟨p,hp,rfl,len,?_,?_⟩
  · rw [gather_value,DFTModelResidualMovement.gather_value]
    exact len
  · intro j
    refine ⟨table j,?_⟩
    have address:(run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val.look j.val 0<2^(q*(w+1)+r) := by
      rw [table j];exact Fin.isLt _
    rw [gathered_lookup t _ a bank _ len j address,table j]

/-- The literal scatter restores the native selected role coordinates and
retains all other addresses of the original full role bank. -/
theorem source_scatter (t:Ty) (q w r:ℕ) (v:BinaryFrames.Vec (Fin (w+1)))
    (raw:Tape ℕ) (a:ℕ) (old child:Tape t.T) (qp:1 ≤ q)
    (source:∀i:Fin (w+1),raw.look i.val 0=(v i).val) (nonzero:v≠0)
    (room:a*2^(q*(w+1)+r)+2^(q*(w+1)+r) ≤ old.len) :
    ∃p:Fin (w+1),∃hp:v p=1,
      (∀j:Fin (2^(q*(w+1)+r)),
        (run (scatter t) (((q,(w+1,(r,raw))),(a,old)),
          ((run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val,child))).val.look
          (a*2^(q*(w+1)+r)+(DFTModelResidualBasisGeometry.permutation q w r v p hp j).val) t.blank=
          child.look j.val t.blank) ∧
      (∀j:Fin old.len,¬(a*2^(q*(w+1)+r) ≤ j.val ∧ j.val<a*2^(q*(w+1)+r)+2^(q*(w+1)+r)) →
        (run (scatter t) (((q,(w+1,(r,raw))),(a,old)),
          ((run DFTModelResidualClosedAddresses.program (q,(w+1,(r,raw)))).val,child))).val.look j.val t.blank=
          old.look j.val t.blank) := by
  obtain ⟨p,hp,len,table⟩:=DFTModelResidualClosedAddresses.source q w r v raw qp source nonzero
  refine ⟨p,hp,?_,?_⟩
  · exact scatter_permutation t _ a _ old _ child
      (DFTModelResidualBasisGeometry.permutation q w r v p hp) len table room
  · intro j outside
    apply scatter_outside
    simpa only [len] using outside

end
end ExactFourierCircuits.DFTModelResidualClosedRole
