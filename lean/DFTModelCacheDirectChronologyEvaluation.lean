import DFTModelCacheDirectChronologyFormula

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDirectLeaf
noncomputable section

theorem integer_value {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (integer op f g) x).val=(op.run ((run f x).val,(run g x).val)).val := by
  simp [integer,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem integer_work {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (integer op f g) x).work=(run f x).work+(run g x).work+3 := by
  cases op <;> simp [integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay] <;> omega
theorem integer_valid {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (integer op f g) x).valid↔(run f x).valid∧(run g x).valid := by
  cases op <;> simp [integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
theorem integer_peak {s : Ty} (op : NOp) (f g : Prog false s w) (x : s.T) :
    (run (integer op f g) x).peak=max (run f x).peak
      (max (run g x).peak (op.run ((run f x).val,(run g x).val)).val) := by
  cases op <;> simp [integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem ifz_value {s t : Ty} (f : Prog false s w) (g h : Prog false s t) (x : s.T) :
    (run (.ifz f g h) x).val=
      if (run f x).val=0 then (run g x).val else (run h x).val := by
  by_cases hx:(run f x).val=0 <;> simp [run,Code.run,Bill.pass,Bill.pay,hx]
theorem ifz_work {s t : Ty} (f : Prog false s w) (g h : Prog false s t) (x : s.T) :
    (run (.ifz f g h) x).work=(run f x).work+
      (if (run f x).val=0 then (run g x).work else (run h x).work)+1 := by
  by_cases hx:(run f x).val=0 <;> simp [run,Code.run,Bill.pass,Bill.pay,hx]
theorem ifz_valid {s t : Ty} (f : Prog false s w) (g h : Prog false s t) (x : s.T) :
    (run (.ifz f g h) x).valid↔(run f x).valid∧
      (if (run f x).val=0 then (run g x).valid else (run h x).valid) := by
  by_cases hx:(run f x).val=0 <;> simp [run,Code.run,Bill.pass,Bill.pay,hx]
theorem ifz_peak {s t : Ty} (f : Prog false s w) (g h : Prog false s t) (x : s.T) :
    (run (.ifz f g h) x).peak=max (run f x).peak
      (if (run f x).val=0 then (run g x).peak else (run h x).peak) := by
  by_cases hx:(run f x).val=0 <;> simp [run,Code.run,Bill.pass,Bill.pay,hx]

theorem fork_value {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).val=((run f x).val,(run g x).val) := by
  simp [run,Code.run,Bill.pass,Bill.one]
theorem fork_work {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).work=(run f x).work+(run g x).work+1 := by
  simp [run,Code.run,Bill.pass,Bill.one]
  omega
theorem fork_valid {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).valid↔(run f x).valid∧(run g x).valid := by
  simp [run,Code.run,Bill.pass,Bill.one]
theorem fork_peak {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).peak=max (run f x).peak (run g x).peak := by
  simp [run,Code.run,Bill.pass,Bill.one]

end
end ExactFourierCircuits.DFTModelCacheDirectChronology
