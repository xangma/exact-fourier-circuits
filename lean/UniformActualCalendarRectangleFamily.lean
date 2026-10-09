import UniformActualCalendarRectangleRegistry
import UniformActualCalendarRegistryAppend

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleRegistry
open UniformMachine UniformActualCalendarRegistry UniformLocalRequestPlan
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestGeometry
noncomputable section

def entries (n:ℕ)(qs:List Request):List (ℕ×ℕ):=qs.flatMap (block n)

def assemble (n r O T B D stride:ℕ)(qs:List Request)(s:State)
 (h:∀i (hi:i<qs.length),Family r O T B (D+stride*slotPrefix n qs i) stride (block n qs[i]) s):
 Family r O T B D stride (entries n qs) s:=by
 induction qs generalizing D with
 | nil=>exact Family.nil _ _ _ _ _ _ _
 | cons q qs ih=>
  have first:Family r O T B D stride (block n q) s:=by
   exact h 0 (by simp)
  have rest:Family r O T B (D+stride*slotCount n q.row) stride (entries n qs) s:=by
   apply ih
   intro i hi
   have current:=h (i+1) (by simp;omega)
   change Family r O T B (D+stride*(slotCount n q.row+slotPrefix n qs i)) stride (block n qs[i]) s at current
   simpa only[Nat.mul_add,Nat.add_assoc] using current
  change Family r O T B D stride (block n q++entries n qs) s
  apply first.append
  simpa only[block,List.length_ofFn] using rest

variable {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R T:ℕ}
 (g:Geometry constants n axisIndex qs R T){s:State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R T g i hi s)

def wholeFamily (hn:0<n){O N:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤N)
 (radixRoom:radix n axisIndex≤envelope constants n):
 Family (radix n axisIndex) O N (envelope constants n) (base constants n axisIndex)
  (3*radix n axisIndex+11) (entries n qs) s:=
 assemble n _ _ _ _ _ _ qs s (fun i hi=>family g all hn scalarRoom natRoom radixRoom i hi)

end
end ExactFourierCircuits.UniformActualCalendarRectangleRegistry
