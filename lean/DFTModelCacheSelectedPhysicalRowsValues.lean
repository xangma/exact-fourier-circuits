import DFTModelCacheSelectedPhysicalRowsProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row nat)
open DFTModelCacheColorSelection (comp_value fork_value atom_value ifz_value nat_value)
open DFTModelCacheSelectedCoefficients (tab_lookup)
noncomputable section
attribute [local irreducible] borrowed DFTModelCacheColorSelection.program

private theorem outside_arithmetic (q s d:ℕ) :
 (if s-q=0 then (if s+d-q=0 then 1 else 0) else 1)=
 (if q<s ∨ s+d≤q then (1:ℕ) else 0) := by
 split_ifs <;>omega

private theorem eligible_arithmetic (j s e t a:ℕ) :
 (if j<s ∨ s+e≤j then (1:ℕ) else 0)*(if j<t ∨ t+a≤j then 1 else 0)=
 (if (j<s ∨ s+e≤j) ∧ (j<t ∨ t+a≤j) then 1 else 0) := by
 by_cases h:j<s ∨ s+e≤j <;>by_cases h':j<t ∨ t+a≤j <;>simp [h,h']

theorem outside_value {s:Ty} (q start width:Prog false s w) (x:s.T) :
 (run (outside q start width) x).val=
 if (run q x).val<(run start x).val ∨ (run start x).val+(run width x).val≤(run q x).val then 1 else 0 := by
 rw [outside,ifz_value,ifz_value,nat_value,nat_value,nat_value]
 exact outside_arithmetic _ _ _

theorem eligible_value (v s e t a g j:ℕ) :
 (run eligible (geom v s e t a g,j)).val=
 if UniformBorrowedCoordinateMachine.Eligible s e t a j then 1 else 0 := by
 rw [eligible,nat_value,outside_value,outside_value]
 exact eligible_arithmetic j s e t a

def candidateInput (v s e t a:ℕ) : DFTModelCacheColorSelection.Input.T :=
 (1,(Tape.tab v (fun j=>(j,(0,0))),Tape.tab v
  (fun j=>if UniformBorrowedCoordinateMachine.Eligible s e t a j then 1 else 0)))

theorem borrowedArgs_value (v s e t a g:ℕ) :
 (run borrowedArgs (geom v s e t a g)).val=candidateInput v s e t a := by
 rw [borrowedArgs,fork_value,fork_value,
  DFTModelCacheMatchingNat.tab_value_code,DFTModelCacheMatchingNat.tab_value_code]
 change (1,(Tape.tab v _,Tape.tab v _))=_
 have h:∀j,(run candidate (geom v s e t a g,j)).val=(j,(0,0)):=fun _=>rfl
 have heq:∀j,(run eligible (geom v s e t a g,j)).val=
  if UniformBorrowedCoordinateMachine.Eligible s e t a j then 1 else 0:=eligible_value v s e t a g
 simp only [h,heq]
 rfl

theorem candidate_accepts (v s e t a j:ℕ) (hj:j<v) :
 DFTModelCacheColorSelection.accepts (candidateInput v s e t a) j ↔
 UniformBorrowedCoordinateMachine.Eligible s e t a j := by
 unfold DFTModelCacheColorSelection.accepts candidateInput
 rw [tab_lookup v _ j 0 hj]
 split_ifs <;> simp_all

theorem candidate_row (v s e t a j:ℕ) (hj:j<v) :
 DFTModelCacheColorSelection.rowValue (candidateInput v s e t a) j=(j,(0,0)) := by
 unfold DFTModelCacheColorSelection.rowValue candidateInput
 exact tab_lookup v _ j Row.blank hj

theorem candidates_prefix (v s e t a:ℕ) :
 DFTModelCacheColorSelection.rowsPrefix (candidateInput v s e t a) v=availableRows v s e t a := by
 unfold DFTModelCacheColorSelection.rowsPrefix
 have h: (List.range v).filterMap (fun j=>if DFTModelCacheColorSelection.accepts
  (candidateInput v s e t a) j then some (DFTModelCacheColorSelection.rowValue
   (candidateInput v s e t a) j) else none)=
  (List.range v).filterMap (fun j=>if UniformBorrowedCoordinateMachine.Eligible s e t a j then some (j,(0,0)) else none) := by
  apply List.filterMap_congr
  intro j hj
  have lt: j<v:=List.mem_range.mp hj
  rw [candidate_row v s e t a j lt]
  exact if_congr (candidate_accepts v s e t a j lt) rfl rfl
 rw [h]
 unfold availableRows UniformBorrowedCoordinateMachine.available
 induction List.range v with
 | nil=>rfl
 | cons j js ih=>
  by_cases hj:UniformBorrowedCoordinateMachine.Eligible s e t a j <;>simp [hj,ih]

theorem borrowed_value (v s e t a g:ℕ) :
 (run borrowed (geom v s e t a g)).val=
 Tape.tab (availableRows v s e t a).length (fun j=>(availableRows v s e t a)[j]?.getD Row.blank) := by
 rw [borrowed,comp_value,borrowedArgs_value,DFTModelCacheColorSelection.program_value]
 change Tape.tab (DFTModelCacheColorSelection.rowsPrefix (candidateInput v s e t a) v).length
  (fun j=>(DFTModelCacheColorSelection.rowsPrefix (candidateInput v s e t a) v)[j]?.getD Row.blank)=_
 rw [candidates_prefix]

theorem borrowed_lookup (v s e t a g j:ℕ) (fit:g+e+a≤v) (hj:j<g) :
 ((run borrowed (geom v s e t a g)).val.look j Row.blank).1=
 UniformChunkPortMachine.borrowedCoordinate v s e t a g fit j := by
 have capacity:=UniformBorrowedCoordinateMachine.available_capacity v s e t a g fit
 have hi:j<(availableRows v s e t a).length:=by
  simp only [availableRows,List.length_map]
  omega
 rw [borrowed_value,tab_lookup _ _ j Row.blank hi]
 have nth:(availableRows v s e t a)[j]?=some ((availableRows v s e t a)[j]):=List.getElem?_eq_getElem hi
 rw [nth]
 simp only [Option.getD_some,availableRows,List.getElem_map]
 simp [UniformChunkPortMachine.borrowedCoordinate,hj,
  UniformBorrowedCoordinateMachine.embedding,UniformBorrowedCoordinateMachine.borrowed]

theorem coordinate_value (v s e t a g q:ℕ) (z:Tape Row.T) (fit:g+e+a≤v)
 (domain:UniformChunkPortMachine.Domain e g a q) :
 (run coordinate (((geom v s e t a g,z),(run borrowed (geom v s e t a g)).val),q)).val=
 UniformChunkPortMachine.mapped e g s t (UniformChunkPortMachine.borrowedCoordinate v s e t a g fit) q := by
 rw [coordinate,ifz_value]
 have first:(run (nat .sub (.comp (.atom .fst) (.comp geometry inputs)) (.atom .snd))
  (((geom v s e t a g,z),(run borrowed (geom v s e t a g)).val),q)).val=0 ↔ e≤q := by
  change e-q=0 ↔ e≤q
  omega
 by_cases he:q<e
 · rw [ite_eq_right (fun h=>by have :=first.mp h;omega)]
   simp only [UniformChunkPortMachine.mapped,he,ite_true]
   rfl
 · rw [ite_eq_left (first.mpr (by omega)),ifz_value]
   have hg:(run (nat .sub
     (nat .add (nat .add (.comp (.atom .fst) (.comp geometry inputs)) (.atom (.lit 1)))
      (.comp (.atom .fst) (.comp geometry gates))) (.atom .snd))
     (((geom v s e t a g,z),(run borrowed (geom v s e t a g)).val),q)).val=0 ↔ e+1+g≤q := by
    change e+1+g-q=0 ↔ e+1+g≤q
    omega
   by_cases hgate:q<e+1+g
   · rw [ite_eq_right (fun h=>by have :=hg.mp h;omega)]
     change ((run borrowed (geom v s e t a g)).val.look (q-(e+1)) Row.blank).1=_
     simp only [UniformChunkPortMachine.mapped,he,hgate,ite_false,ite_true]
     apply borrowed_lookup _ _ _ _ _ _ _ fit
     unfold UniformChunkPortMachine.Domain at domain
     omega
   · rw [ite_eq_left (hg.mpr (by omega))]
     simp only [UniformChunkPortMachine.mapped,he,hgate,ite_false]
     rfl

end
end ExactFourierCircuits.DFTModelCacheSelectedPhysicalRows
