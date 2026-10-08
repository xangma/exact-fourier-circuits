import UniformXorWordBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformXorCallerInterface
open UniformMachine UniformXorTableMachine UniformXorWordBounds
noncomputable section

/-- The producer retains its physically computed radix after the final halt. -/
theorem table_loop_size (n q base k fuel : ℕ) (x : Fin n→ℂ) (s : State)
 (c : TableControl q base k s) (total : k+fuel=2^q*2^q) :
 ∃u,Executes tableProgram n x s ((12*q+15)*fuel+2) u ∧ u.natReg 3423=2^q := by
 induction fuel generalizing k s with
 | zero =>
   have same : k=2^q*2^q := by omega
   let u : State := {s with pc:=37}
   refine ⟨u,?_,c.size⟩
   refine .next (u:=u) ?_ (.halt ?_)
   · simp [step,tableProgram,tablePrefix,c.pc,c.index,c.total,same,u]
   · simp [step,tableProgram,tablePrefix,bitProgram,u]
 | succ fuel ih =>
   obtain ⟨v,first,cv,_,_⟩:=table_iteration n x q base k s c (by omega)
   obtain ⟨u,last,radix⟩:=ih (k+1) v cv (by omega)
   refine ⟨u,?_,radix⟩
   convert first.executes last using 1;ring

theorem table_execution_size (n q base : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3420=q) (hb : s.natReg 3421=base) :
 ∃u,Executes tableProgram n x s (4*q+10+(12*q+15)*(2^q*2^q)) u ∧ u.natReg 3423=2^q := by
 let start:=powerInitialized s
 have control : PowerControl q base 0 start := by
  constructor <;> simp [start,powerInitialized,writeNat,next,pc,hq,hb]
 obtain ⟨v,power,pv,cv,_⟩:=power_loop n x q base 0 q start control (by omega)
 have vl : v.natReg 3420=q := cv.length
 have vb : v.natReg 3421=base := cv.base
 have vv : v.natReg 3423=2^q := cv.value
 have vo : v.natReg 3424=1 := cv.one
 have vz : v.natReg 3426=0 := cv.zero
 let sized:=tableSized v
 have cs : TableControl q base 0 sized := by
  constructor <;> simp [sized,tableSized,writeNat,next,pv,vl,vb,vv,vo,vz]
 obtain ⟨u,last,radix⟩:=table_loop_size n q base 0 (2^q*2^q) x sized cs (by omega)
 refine ⟨u,?_,radix⟩
 convert ((power_initializes n x s pc).trans power).trans
  (table_size_runs n x v pv) |>.executes last using 1
 ring

/-- Caller-visible result with both generated entries and the actual radix;
no independently supplied size or table is needed by the next instruction. -/
theorem table_execution_bounded_size (n q base B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3420=q) (hb : s.natReg 3421=base)
 (bound : WordBound B s) (extent : 38≤B) (capacity : base+2^q*2^q≤B) :
 ∃u,BoundedExecution tableProgram n x B s (4*q+10+(12*q+15)*(2^q*2^q)) u ∧
 u.pc=37 ∧ u.natReg 3423=2^q ∧ Entries q base (2^q*2^q) u ∧
 Outside q base s.natHeap u ∧ TableFrame s u := by
 obtain ⟨u,run,pc',entries,outside,frame⟩:=
  table_execution_bounded n q base B x s pc hq hb bound extent capacity
 obtain ⟨v,rv,size⟩:=table_execution_size n q base x s pc hq hb
 have eq : u=v := (Executes.deterministic run.executes rv).2
 subst v
 exact ⟨u,run,pc',size,entries,outside,frame⟩

end
end ExactFourierCircuits.UniformXorCallerInterface
