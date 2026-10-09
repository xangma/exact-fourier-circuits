import UniformActualCalendarAssembleEvents

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRectangleRegistry
open UniformMachine UniformActualCalendarRegistry UniformLocalRequestPlan
open UniformJointAllocation UniformAllAxisSeedPreparation UniformLocalRequestGeometry
noncomputable section

lemma wholeFamily_make {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R T:ℕ}
 (g:Geometry constants n axisIndex qs R T){s:State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R T g i hi s)
 (hn:0<n){O N:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤N)
 (radixRoom:radix n axisIndex≤envelope constants n)(i:ℕ)(hi:i<qs.length)(t elapsed:ℕ)
 (ht:t<slotCount n qs[i].row):
 (wholeFamily g all hn scalarRoom natRoom radixRoom).make (slotPrefix n qs i+t) elapsed=
 (data g all i hi t ht).event _ _ _ _ _ _ _ _ elapsed:=by
 have index:=assemble_make n (radix n axisIndex) O N (envelope constants n)
  (base constants n axisIndex) (3*radix n axisIndex+11) qs s
  (fun i hi=>family g all hn scalarRoom natRoom radixRoom i hi) i hi t elapsed ht
 exact index.trans (family_make g all hn scalarRoom natRoom radixRoom i hi t elapsed ht)

end
end ExactFourierCircuits.UniformActualCalendarRectangleRegistry
