import ModelEquivalenceInterpreter
import UniformBinaryCStageMachine

set_option autoImplicit false

/-! A whole packed binary-C layer in the upstream first-order model. The
coefficients are prepared input registers, and both scalar products use scale.
One tabulation constructs the complete output; no published tape is updated.
This is the packed essential kernel, not a compiler for the complete clock. -/
namespace ExactFourierCircuits.DFTModelClock
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine
noncomputable section

abbrev Datum := c .left
abbrev Input := p (p sc sc) (p w (Ty.a Datum))
abbrev CellInput := p Input w

def coefficientA : Prog false CellInput sc :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def coefficientB : Prog false CellInput sc :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def source : Prog false CellInput (Ty.a Datum) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def parity : Prog false CellInput w :=
  .comp (.fork (.atom .snd) (.atom (.lit 2))) (.atom (.int .mod))
def partner : Prog false CellInput w :=
  .ifz parity
    (.comp (.fork (.atom .snd) (.atom (.lit 1))) (.atom (.int .add)))
    (.comp (.fork (.atom .snd) (.atom (.lit 1))) (.atom (.int .sub)))
def currentRead : Prog false CellInput Datum :=
  .comp (.fork source (.atom .snd)) (.atom .look)
def partnerRead : Prog false CellInput Datum :=
  .comp (.fork source partner) (.atom .look)
def cell : Prog false CellInput Datum :=
  .comp (.fork
    (.comp (.fork coefficientA currentRead) (.atom (.scale .left)))
    (.comp (.fork coefficientB partnerRead) (.atom (.scale .left))))
    (.atom (.add .left))
def length : Prog false Input w :=
  .comp (.fork (.comp (.atom .snd) (.atom .fst)) (.atom (.lit 2)))
    (.atom (.int .mul))
def program : Prog false Input (Ty.a Datum) := .tab length cell

def mate (j : ℕ) : ℕ := if j%2=0 then j+1 else j-1

theorem mate_even (j : ℕ) : mate (2*j)=2*j+1 := by simp [mate]
theorem mate_odd (j : ℕ) : mate (2*j+1)=2*j := by simp [mate]

theorem cell_run (a b : ℂ) (N j : ℕ) (v : Tape ℂ) :
    run cell (((a,b),(N,v)),j) =
      ⟨a*v.look j 0+b*v.look (mate j) 0,47,max 2 (mate j),True⟩ := by
  by_cases h : j%2=0
  · simp [cell,currentRead,partnerRead,source,coefficientA,coefficientB,
      partner,parity,mate,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,h]
  · simp [cell,currentRead,partnerRead,source,coefficientA,coefficientB,
      partner,parity,mate,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,h]
    omega

theorem length_run (a b : ℂ) (N : ℕ) (v : Tape ℂ) :
    run length ((a,b),(N,v)) = ⟨N*2,7,max 2 (N*2),True⟩ := by
  simp [length,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem tab_peak {r : RAM.Port} {s t : Ty} (n : Code false r s w)
    (body : Code false r (p s w) t) (h : Handler r) (x : s.T) :
    (Code.run (.tab n body) h x).peak = max
      (max (Code.run n h x).peak
        (Bill.tab (Code.run n h x).val t.blank (fun j => Code.run body h (x,j))).peak) 0 := rfl

theorem program_value (a b : ℂ) (N : ℕ) (v : Tape ℂ) :
    (run program ((a,b),(N,v))).val =
      Tape.tab (2*N) (fun j => a*v.look j 0+b*v.look (mate j) 0) := by
  change (Bill.tab (N*2) Datum.blank (fun j => run cell (((a,b),(N,v)),j))).val = _
  rw [ModelEquivalenceInterpreter.tab_value]
  rw [Nat.mul_comm N 2]
  exact congrArg (Tape.tab (2*N)) (funext (fun j => congrArg Bill.val (cell_run a b N j v)))

theorem program_work (a b : ℂ) (N : ℕ) (v : Tape ℂ) :
    (run program ((a,b),(N,v))).work = 102*N+10 := by
  change 7+(Bill.tab (N*2) Datum.blank (fun j => run cell (((a,b),(N,v)),j))).work+1 = _
  rw [ModelEquivalenceInterpreter.tab_work]
  have h : (fun j => (run cell (((a,b),(N,v)),j)).work) = fun _ => 47 := by
    funext j; exact congrArg Bill.work (cell_run a b N j v)
  rw [h]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  omega

theorem program_valid (a b : ℂ) (N : ℕ) (v : Tape ℂ) :
    (run program ((a,b),(N,v))).valid := by
  simp only [program,length,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]
  simp only [true_and]
  apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
  intro j _
  change (run cell (((a,b),(N,v)),j)).valid
  rw [cell_run]; trivial

theorem program_peak (a b : ℂ) (N : ℕ) (v : Tape ℂ) :
    (run program ((a,b),(N,v))).peak ≤ max 2 (2*N) := by
  unfold program run
  rw [tab_peak]
  change max (max (run length ((a,b),(N,v))).peak
    (Bill.tab (run length ((a,b),(N,v))).val Datum.blank
      (fun j => run cell (((a,b),(N,v)),j))).peak) 0 ≤ _
  rw [length_run,ModelEquivalenceInterpreter.tab_peak]
  simp only [max_zero]
  refine max_le (by omega) (max_le (by omega) ?_)
  apply Finset.sup_le
  intro j hj
  rw [show (run cell (((a,b),(N,v)),j)).peak=max 2 (mate j) from
    congrArg Bill.peak (cell_run a b N j v)]
  have bound := Finset.mem_range.mp hj
  have hm : mate j ≤ j+1 := by unfold mate; split_ifs <;> omega
  omega

theorem even_value (a b : ℂ) (N : ℕ) (v : Tape ℂ) (j : ℕ) (hj : j<N) :
    (run program ((a,b),(N,v))).val.look (2*j) 0 =
      a*v.look (2*j) 0+b*v.look (2*j+1) 0 := by
  rw [program_value]
  simp [Tape.look,Tape.tab,mate_even,show 2*j<2*N by omega]

theorem odd_value (a b : ℂ) (N : ℕ) (v : Tape ℂ) (j : ℕ) (hj : j<N) :
    (run program ((a,b),(N,v))).val.look (2*j+1) 0 =
      b*v.look (2*j) 0+a*v.look (2*j+1) 0 := by
  rw [program_value]
  rw [Tape.look_of_lt _ _ (show 2*j+1<2*N by omega)]
  change a*v.look (2*j+1) 0+b*v.look (mate (2*j+1)) 0 = _
  rw [mate_odd,add_comm]

def data {N : ℕ} (v : Fin (1*N)→Fin 2→Scalar) : Tape ℂ :=
  ⟨2*N,fun z => (v ⟨z.val/2,by
    have h := z.isLt
    omega⟩ ⟨z.val%2,Nat.mod_lt _ (by omega)⟩).value⟩

theorem data_read {N : ℕ} (v : Fin (1*N)→Fin 2→Scalar)
    (j : Fin (1*N)) (t : Fin 2) :
    (data v).look (2*j.val+t.val) 0 = (v j t).value := by
  have hj := j.isLt
  have ht := t.isLt
  have range : 2*j.val+t.val<2*N := by omega
  have div : (2*j.val+t.val)/2=j.val := by omega
  have mod : (2*j.val+t.val)%2=t.val := by omega
  simp [data,Tape.look,range,div,mod]

/-- Exact numeric correspondence to the actual packed binary-C RAM stage.
The RAM stage retains complete Scalar flags; the upstream left-painted tape
here represents their values. Prepared coefficient literals are not added. -/
theorem actual_execution {n N A B : ℕ} (x : Fin n→ℂ)
    (v : Fin (1*N)→Fin 2→Scalar) (s : State)
    (pc : s.pc=0) (stride : s.natReg 2800=1) (base : s.natReg 2801=A)
    (count : s.natReg 2802=N) (aFit : 3≤A)
    (constants : UniformBinaryCStageMachine.Constants s)
    (source : ∀j t,s.scalarHeap (UniformBinaryCStageMachine.coordinate 1 A N j t)=some (v j t))
    (bound : WordBound B s) (code : 30≤B) (extent : A+1*2*N≤B) :
    ∃u,BoundedExecution UniformBinaryCStageMachine.program n x B s (25*(1*N)+6) u ∧
      (∀j t,u.scalarHeap (UniformBinaryCStageMachine.coordinate 1 A N j t)=
        some (UniformBinaryCStageMachine.transformed v j t)) ∧
      UniformBinaryCStageMachine.Frame A (1*2*N) s u ∧
      (∀j t,(run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).val.look
        (2*j.val+t.val) 0 = (UniformBinaryCStageMachine.transformed v j t).value) ∧
      (run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).valid ∧
      (run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).work≤5*(25*(1*N)+6) ∧
      (run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).peak≤B := by
  obtain ⟨u,runRAM,output,frame⟩ := UniformBinaryCStageMachine.execution n B x 1 A N v s
    pc stride base count (by omega) aFit constants source bound code extent
  refine ⟨u,runRAM,output,frame,?_,program_valid _ _ _ _,?_,?_⟩
  · intro j t
    have hj : j.val<N := by simpa only [Nat.one_mul] using j.isLt
    have d0 := data_read v j (0:Fin 2)
    have d1 := data_read v j (1:Fin 2)
    simp only [Fin.val_zero,Nat.add_zero] at d0
    simp only [Fin.val_one] at d1
    fin_cases t
    · change (run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).val.look
        (2*j.val) 0 = (UniformBinaryCStageMachine.transformed v j 0).value
      rw [even_value _ _ _ _ _ hj,d0,d1]
      rfl
    · change (run program ((ExactFourierCircuits.a,ExactFourierCircuits.b),(N,data v))).val.look
        (2*j.val+1) 0 = (UniformBinaryCStageMachine.transformed v j 1).value
      rw [odd_value _ _ _ _ _ hj,d0,d1]
      simp [UniformBinaryCStageMachine.transformed,UniformPairMachine.combine]
  · rw [program_work]
    omega
  · exact (program_peak _ _ _ _).trans (max_le (by omega) (by omega))

end
end ExactFourierCircuits.DFTModelClock
