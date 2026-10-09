import UniformLocalRequestDriver
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRequestPlan
open UniformMachine UniformLocalRectangleDescriptors UniformAllAxisSeedPreparation
open UniformCanonicalCacheSlotGeometry UniformLocalCacheSlotConductorMachine
noncomputable section

structure Request where
 row:Row
 time:ℕ

def slotCount (n:ℕ)(q:Row):ℕ:=352*(UniformJointCacheWorkspace.original n q).exponent+330
def slotPrefix (n:ℕ):List Request→ℕ→ℕ
 | _,0=>0
 | [],_+1=>0
 | q::qs,k+1=>slotCount n q.row+slotPrefix n qs k
lemma prefix_zero (n:ℕ)(qs:List Request):slotPrefix n qs 0=0:=by cases qs <;>rfl
lemma prefix_step (n:ℕ)(qs:List Request)(k:ℕ)(hk:k<qs.length):
 slotPrefix n qs (k+1)=slotPrefix n qs k+slotCount n (qs[k]'hk).row:=by
 induction qs generalizing k with
 | nil=>simp at hk
 | cons q qs ih=>
  cases k with
  | zero=>simp [slotPrefix]
  | succ k=>
   have bound:k<qs.length:=by simpa using hk
   simpa only [slotPrefix,List.getElem_cons_succ,Nat.add_assoc] using
    congrArg (slotCount n q.row+·) (ih k bound)
lemma prefix_mono (n:ℕ)(qs:List Request){i j:ℕ}(ij:i≤j)(bound:j≤qs.length):
 slotPrefix n qs i ≤ slotPrefix n qs j:=by
 induction j with
 | zero=>
  have eq:i=0:=by omega
  subst i
  exact le_rfl
 | succ j ih=>
  by_cases same:i=j+1
  · subst i;exact le_rfl
  · have b:j<qs.length:=by omega
    rw [prefix_step n qs j b]
    exact (ih (by omega) (by omega)).trans (Nat.le_add_right _ _)

def requestAt (qs:List Request)(i:ℕ):Request:=qs[i]?.getD ⟨⟨0,0,0,0,0,0,0⟩,0⟩
lemma requestAt_eq (qs:List Request)(i:ℕ)(hi:i<qs.length):requestAt qs i=qs[i]'hi:=by
 simp [requestAt,hi]
def controller (constants:UniformJointAllocation.Constants)(n:ℕ)(axis:Fin (axisCount n))
 (qs:List Request)(i:ℕ):UniformLocalCacheSlotHeaderMachine.Parameters:=
 context constants n axis (requestAt qs i).row (slotPrefix n qs i) (requestAt qs i).time
lemma controller_count (constants:UniformJointAllocation.Constants)(n:ℕ)(axis:Fin (axisCount n))
 (qs:List Request)(i:ℕ)(hi:i<qs.length):
 352*(controller constants n axis qs i).height.K+330=slotCount n (qs[i]'hi).row:=by
 rw [controller,requestAt_eq qs i hi];rfl

/-- Genuine stored rows and produced timing cells, with no factor or action
certificate. The forest/timing producer supplies these two physical banks. -/
structure Source (R T:ℕ)(qs:List Request)(s:State):Prop where
 rows:∀i (hi:i<qs.length),UniformLocalRectangleBankMachine.RowSource (R+7*i) (qs[i]'hi).row s
 times:∀i (hi:i<qs.length),s.natHeap (T+i)=some (qs[i]'hi).time

lemma Source.transport {R T qs s u}(h:Source R T qs s)
 (rows:∀i,i<qs.length→∀f:Fin 7,u.natHeap (R+7*i+f.val)=s.natHeap (R+7*i+f.val))
 (times:∀i,i<qs.length→u.natHeap (T+i)=s.natHeap (T+i)):
 Source R T qs u:=by
 refine ⟨?_,fun i hi=>(times i hi).trans (h.times i hi)⟩
 intro i hi f
 exact (rows i hi f).trans (h.rows i hi f)

end
end ExactFourierCircuits.UniformLocalRequestPlan
