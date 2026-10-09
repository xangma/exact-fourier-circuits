import DFTModelResidualCore

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelResidualPeakSyntax
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem comp {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T) :
    (run (.comp f g) x).peak=max (run f x).peak (run g (run f x).val).peak := by
  simp [run,Code.run,Bill.pass,Bill.pay]

theorem fork {s t u:Ty} (f:Prog false s t) (g:Prog false s u) (x:s.T) :
    (run (.fork f g) x).peak=max (run f x).peak (run g x).peak := by
  simp [run,Code.run,Bill.pass,Bill.one]


theorem tab {s t:Ty} (f:Prog false s w) (g:Prog false (p s w) t) (x:s.T) :
    (run (.tab f g) x).peak=max (run f x).peak
      (max (run f x).val ((Finset.range (run f x).val).sup (fun j=>(run g (x,j)).peak))) := by
  change max (max (run f x).peak
    (Bill.tab (run f x).val t.blank (fun j=>run g (x,j))).peak) 0=_
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp

end
end ExactFourierCircuits.DFTModelResidualPeakSyntax
