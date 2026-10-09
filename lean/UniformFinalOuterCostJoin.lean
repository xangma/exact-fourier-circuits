import UniformFinalLinearTableCost
import UniformFinalOuterSuffix

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFinalOuterCostJoin
open UniformMachine UniformFinalOuterCost UniformFinalClockCost UniformFinalLinearTableCost
open UniformFinalCacheAsymptotics
noncomputable section
local notation "c"=>UniformActualGlobalConstants.constants
abbrev W:ℕ:=UniformRecursiveSelfCallMachine.W
abbrev V(n:ℕ):ℕ:=UniformInitialPreparation.len n

def prefixCost(_n ti tc tt:ℕ):ℕ:=ti+62+67+tc+20+tt
def suffixCost(n kernel data third:ℕ):ℕ:=
 (18+(5*(W*V n)+16*V n+24))+kernel+(7*V n+9)+
 (19+(5*(W*V n)+16*V n+24)+(9*V n+10))+data+
 ((9*V n+9)+(18*V n+18))+third+(18*V n+18)+(13*n+18)

/-- Actual charged counts from the prefix and fourteen-stage suffix fit the
closed paper majorant. Every helper halt and the final halt is included. -/
theorem bound {n ti tc tt kernel data third:ℕ}
 (initial:ti≤UniformAllAxisConjugatePreparation.fullBudget n)
 (cache:tc≤cacheBudget c n)
 (table:tt≤tableBudget n)
 (first:(kernel:ℝ)≤clockEnvelope W n)
 (second:(data:ℝ)≤clockEnvelope W n)
 (last:(third:ℝ)≤clockEnvelope W n):
 ((prefixCost n ti tc tt+suffixCost n kernel data third+1:ℕ):ℝ)≤finalBudget c W n:=by
 have a:(ti:ℝ)≤(UniformAllAxisConjugatePreparation.fullBudget n:ℝ):=by exact_mod_cast initial
 have b:(tc:ℝ)≤(cacheBudget c n:ℝ):=by exact_mod_cast cache
 have d:(tt:ℝ)≤(tableBudget n:ℝ):=by exact_mod_cast table
 simp only[prefixCost,suffixCost,finalBudget,overhead,V,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
 nlinarith only[a,b,d,first,second,last]

end
end ExactFourierCircuits.UniformFinalOuterCostJoin
