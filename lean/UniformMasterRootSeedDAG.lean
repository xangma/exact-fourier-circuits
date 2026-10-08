import UniformLocalPreparationReferences
import UniformPowerMachine
import UniformBatching

set_option autoImplicit false

/-! One canonical master-root leaf supplies an axis root and all required
canonical dyadic roots. Typed arithmetic replay replaces Newton root leaves
with retained prepared references. RAM printing of this DAG is separate. -/
namespace ExactFourierCircuits.UniformMasterRootSeedDAG
open UniformScalarPreparation UniformLocalPreparationDAG UniformLocalPreparationReferences UniformShearPreparation
open OAI.ExactFourier
abbrev SProgram := UniformScalarPreparation.Program

/-- Repeated squaring appends shared register nodes and preserves the prefix. -/
structure Power (r l : ℕ) where
  length : ℕ
  program : SProgram r length
  old : Fin l → Fin length
  result : Fin length

def power {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ) : Power r l :=
  if _hz : e=0 then ⟨l,p,id,one⟩ else
    let q := power p one base (e/2)
    let square := UniformScalarPreparation.Program.step q.program (.mul q.result q.result)
    if e%2=0 then
      ⟨q.length+1,square,(fun j => (q.old j).castSucc),Fin.last q.length⟩
    else
      ⟨q.length+2,UniformScalarPreparation.Program.step square (.mul (Fin.last q.length) (q.old base).castSucc),
        (fun j => (q.old j).castSucc.castSucc),Fin.last (q.length+1)⟩
termination_by e
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem power_zero {r l : ℕ} (p : SProgram r l) (one base : Fin l) :
    power p one base 0=⟨l,p,id,one⟩ := by rw [power];rfl

theorem power_even {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ)
    (hz : e≠0) (hp : e%2=0) :
    power p one base e=
      let q := power p one base (e/2)
      ⟨q.length+1,UniformScalarPreparation.Program.step q.program (.mul q.result q.result),
        (fun j => (q.old j).castSucc),Fin.last q.length⟩ := by
  rw [power,dite_eq_right hz,ite_eq_left hp]

theorem power_odd {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ)
    (hz : e≠0) (hp : e%2≠0) :
    power p one base e=
      let q := power p one base (e/2)
      ⟨q.length+2,UniformScalarPreparation.Program.step
        (UniformScalarPreparation.Program.step q.program (.mul q.result q.result))
        (.mul (Fin.last q.length) (q.old base).castSucc),
        (fun j => (q.old j).castSucc.castSucc),Fin.last (q.length+1)⟩ := by
  rw [power,dite_eq_right hz,ite_eq_right hp]

def powerCost (e : ℕ) : ℕ :=
  if hz : e=0 then 0 else powerCost (e/2)+(if e%2=0 then 1 else 2)
termination_by e
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem power_length {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ) :
    (power p one base e).length=l+powerCost e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [power,powerCost]
    split_ifs with hz hp
    · rfl
    · have h := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
      dsimp only
      rw [h]
      omega
    · have h := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
      dsimp only
      rw [h]
      omega

theorem power_old {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ)
    (zs : Fin r → ℂ) (j : Fin l) :
    (power p one base e).program.eval zs ((power p one base e).old j)=p.eval zs j := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · subst e;rw [power_zero];rfl
    have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
    by_cases hp : e%2=0
    · rw [power_even p one base e hz hp]
      simpa only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc] using hh
    · rw [power_odd p one base e hz hp]
      simpa only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc] using hh

theorem power_old_val {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ) (j : Fin l) :
    ((power p one base e).old j).val=j.val := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · subst e;rw [power_zero];rfl
    have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
    by_cases hp : e%2=0
    · rw [power_even p one base e hz hp]
      simpa only [Fin.val_castSucc] using hh
    · rw [power_odd p one base e hz hp]
      simpa only [Fin.val_castSucc] using hh

theorem power_value {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ)
    (zs : Fin r → ℂ) (hone : p.eval zs one=1) :
    (power p one base e).program.eval zs (power p one base e).result=(p.eval zs base)^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · subst e;rw [power_zero];simpa using hone
    have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
    by_cases hp : e%2=0
    · rw [power_even p one base e hz hp]
      simp only [UniformScalarPreparation.Program.eval,Fin.snoc_last,Instruction.eval,hh]
      rw [←pow_add]
      congr 1
      omega
    · rw [power_odd p one base e hz hp]
      simp only [UniformScalarPreparation.Program.eval,
        Fin.snoc_last,Fin.snoc_castSucc,Instruction.eval,hh,power_old]
      rw [←pow_add,←pow_succ]
      congr 1
      have hm := Nat.mod_lt e (by decide : 0<2)
      omega

theorem power_admissible {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ)
    (zs : Fin r → ℂ) (hp : p.Admissible zs) : (power p one base e).program.Admissible zs := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · subst e;rw [power_zero];exact hp
    have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
    by_cases he : e%2=0
    · rw [power_even p one base e hz he]
      simpa only [UniformScalarPreparation.Program.Admissible,
        Instruction.Admissible,and_true] using hh
    · rw [power_odd p one base e hz he]
      simpa only [UniformScalarPreparation.Program.Admissible,
        Instruction.Admissible,and_true] using hh

theorem power_counts {r l : ℕ} (p : SProgram r l) (one base : Fin l) (e : ℕ) :
    (power p one base e).program.rootReads=p.rootReads ∧
      (power p one base e).program.divisions=p.divisions := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · subst e;rw [power_zero];exact ⟨rfl,rfl⟩
    have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
    by_cases he : e%2=0
    · rw [power_even p one base e hz he]
      simpa only [UniformScalarPreparation.Program.rootReads,
        UniformScalarPreparation.Program.divisions,Instruction.rootReads,Instruction.divisions,Nat.add_zero] using hh
    · rw [power_odd p one base e hz he]
      simpa only [UniformScalarPreparation.Program.rootReads,
        UniformScalarPreparation.Program.divisions,Instruction.rootReads,Instruction.divisions,Nat.add_zero] using hh

theorem powerCost_iterations (e : ℕ) : powerCost e≤2*UniformPowerMachine.iterations e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e=0
    · simp [hz,powerCost,UniformPowerMachine.iterations_zero]
    · rw [powerCost,dite_eq_right hz,UniformPowerMachine.iterations_step e hz]
      have hh := ih (e/2) (Nat.div_lt_self (by omega) (by decide))
      split_ifs <;> omega

theorem powerCost_log (e : ℕ) : powerCost e≤2*(Nat.log2 (e+1)+1) :=
  (powerCost_iterations e).trans (Nat.mul_le_mul_left 2 (UniformPowerMachine.iterations_log_succ_bound e))


def extractionCost (D : ℕ) : ℕ := 2*(Nat.log2 (D+1)+1)

theorem powerCost_div_bound (D d : ℕ) : powerCost (D/d)≤extractionCost D := by
  have hd := Nat.div_le_self D d
  have hm : Nat.log2 (D/d+1)≤Nat.log2 (D+1) :=
    (Nat.le_log2 (Nat.succ_ne_zero D)).2
      ((Nat.log2_self_le (Nat.succ_ne_zero (D/d))).trans (Nat.add_le_add_right hd 1))
  exact (powerCost_log _).trans (by unfold extractionCost;omega)

/-- Header refs are master root, zero, one, and minus one. -/
structure RootBank (N : ℕ) where
  length : ℕ
  program : SProgram 1 length
  header : Fin 4 → Fin length
  axis : Fin length
  omega : Fin (Nat.clog 2 N+3) → Fin length

def basic (N : ℕ) : RootBank N :=
  ⟨4,.step (.step (.step (.step .nil (.root 0)) (.rational 0)) (.rational 1)) (.rational (-1)),
    id,0,fun _=>0⟩

noncomputable def rootValues (D : ℕ) : Fin 1 → ℂ := fun _=>zeta D

def RootBank.Headers {N : ℕ} (b : RootBank N) (zs : Fin 1 → ℂ) : Prop :=
  b.program.eval zs (b.header 0)=zs 0 ∧ b.program.eval zs (b.header 1)=0 ∧
  b.program.eval zs (b.header 2)=1 ∧ b.program.eval zs (b.header 3)= -1

theorem basic_headers (N : ℕ) (zs : Fin 1 → ℂ) : (basic N).Headers zs := by
  simp [basic,RootBank.Headers,Instruction.eval,Fin.snoc]

def axisRoot (D N : ℕ) : RootBank N :=
  let b:=basic N
  let q:=power b.program (b.header 2) (b.header 0) (D/N)
  ⟨q.length,q.program,q.old ∘ b.header,q.result,q.old ∘ b.omega⟩

def dyadicRoot {N : ℕ} (b : RootBank N) (D : ℕ) (j : Fin (Nat.clog 2 N+3)) : RootBank N :=
  let q:=power b.program (b.header 2) (b.header 0) (D/(2^j.val))
  ⟨q.length,q.program,q.old ∘ b.header,q.old b.axis,
    Function.update (q.old ∘ b.omega) j q.result⟩

theorem axisRoot_headers (D N : ℕ) (zs : Fin 1 → ℂ) : (axisRoot D N).Headers zs := by
  rcases basic_headers N zs with ⟨hm,hz,ho,hn⟩
  exact ⟨(power_old _ _ _ _ _ _).trans hm,(power_old _ _ _ _ _ _).trans hz,
    (power_old _ _ _ _ _ _).trans ho,(power_old _ _ _ _ _ _).trans hn⟩

theorem axisRoot_value (D N : ℕ) (hD : 0<D) (hN : 0<N) (hd : N∣D) :
    (axisRoot D N).program.eval (rootValues D) (axisRoot D N).axis=zeta N := by
  change (power _ _ _ _).program.eval _ (power _ _ _ _).result=_
  rw [power_value _ _ _ _ _ (basic_headers N (rootValues D)).2.2.1]
  rw [(basic_headers N (rootValues D)).1]
  exact UniformRoots.specifiedRoot_divisor_power D N hD hN hd

theorem dyadicRoot_headers {N : ℕ} (b : RootBank N) (D : ℕ) (j : Fin (Nat.clog 2 N+3))
    (zs : Fin 1 → ℂ) (hb : b.Headers zs) : (dyadicRoot b D j).Headers zs := by
  exact ⟨(power_old _ _ _ _ _ _).trans hb.1,(power_old _ _ _ _ _ _).trans hb.2.1,
    (power_old _ _ _ _ _ _).trans hb.2.2.1,(power_old _ _ _ _ _ _).trans hb.2.2.2⟩

theorem dyadicRoot_axis {N : ℕ} (b : RootBank N) (D : ℕ) (j : Fin (Nat.clog 2 N+3))
    (zs : Fin 1 → ℂ) : (dyadicRoot b D j).program.eval zs (dyadicRoot b D j).axis=b.program.eval zs b.axis :=
  power_old _ _ _ _ _ _

theorem dyadicRoot_omega {N : ℕ} (b : RootBank N) (D : ℕ) (j l : Fin (Nat.clog 2 N+3))
    (hD : 0<D) (hd : 2^j.val∣D) (hb : b.Headers (rootValues D)) :
    (dyadicRoot b D j).program.eval (rootValues D) ((dyadicRoot b D j).omega l)=
      if l=j then zeta (2^l.val) else b.program.eval (rootValues D) (b.omega l) := by
  by_cases hl : l=j
  · subst l
    simp only [dyadicRoot,Function.update_self,ite_true]
    rw [power_value _ _ _ _ _ hb.2.2.1,hb.1]
    exact UniformRoots.specifiedRoot_divisor_power D (2^j.val) hD (by positivity) hd
  · simp only [dyadicRoot,Function.update_of_ne hl,ite_eq_right hl,Function.comp_def]
    exact power_old _ _ _ _ _ _

def dyadicRoots {N : ℕ} (D : ℕ) : RootBank N → List (Fin (Nat.clog 2 N+3)) → RootBank N
  | b,[] => b
  | b,j::js => dyadicRoots D (dyadicRoot b D j) js

theorem dyadicRoots_headers {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3)))
    (zs : Fin 1 → ℂ) (hb : b.Headers zs) : (dyadicRoots D b js).Headers zs := by
  induction js generalizing b with
  | nil => exact hb
  | cons j js ih => exact ih _ (dyadicRoot_headers b D j zs hb)

theorem dyadicRoots_axis {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3)))
    (zs : Fin 1 → ℂ) : (dyadicRoots D b js).program.eval zs (dyadicRoots D b js).axis=b.program.eval zs b.axis := by
  induction js generalizing b with
  | nil => rfl
  | cons j js ih => exact (ih _).trans (dyadicRoot_axis b D j zs)

theorem dyadicRoots_omega {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3)))
    (hD : 0<D) (hd : ∀ j∈js,2^j.val∣D) (hb : b.Headers (rootValues D)) (l : Fin (Nat.clog 2 N+3)) :
    (dyadicRoots D b js).program.eval (rootValues D) ((dyadicRoots D b js).omega l)=
      if l∈js then zeta (2^l.val) else b.program.eval (rootValues D) (b.omega l) := by
  induction js generalizing b with
  | nil => simp [dyadicRoots]
  | cons j js ih =>
    rw [dyadicRoots,ih _ (fun q hq=>hd q (by simp [hq])) (dyadicRoot_headers b D j _ hb)]
    by_cases hl : l∈js
    · simp only [hl,List.mem_cons,or_true,ite_true]
    · rw [ite_eq_right hl,dyadicRoot_omega b D j l hD (hd j (by simp)) hb]
      simp only [List.mem_cons,hl,or_false]

theorem root_headers_admissible (N : ℕ) (zs : Fin 1 → ℂ) : (basic N).program.Admissible zs := by
  trivial

theorem axisRoot_admissible (D N : ℕ) (zs : Fin 1 → ℂ) : (axisRoot D N).program.Admissible zs :=
  power_admissible _ _ _ _ _ (root_headers_admissible N zs)

theorem dyadicRoots_admissible {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3)))
    (zs : Fin 1 → ℂ) (hb : b.program.Admissible zs) : (dyadicRoots D b js).program.Admissible zs := by
  induction js generalizing b with
  | nil => exact hb
  | cons j js ih => exact ih _ (power_admissible _ _ _ _ _ hb)

theorem dyadicRoots_rootReads {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3))) :
    (dyadicRoots D b js).program.rootReads=b.program.rootReads := by
  induction js generalizing b with
  | nil => rfl
  | cons j js ih => exact (ih _).trans (power_counts _ _ _ _).1

theorem dyadicRoot_length {N : ℕ} (D : ℕ) (b : RootBank N) (j : Fin (Nat.clog 2 N+3)) :
    (dyadicRoot b D j).length≤b.length+extractionCost D := by
  change (power _ _ _ _).length≤_
  rw [power_length]
  exact Nat.add_le_add_left (powerCost_div_bound D _) b.length

theorem dyadicRoots_length {N : ℕ} (D : ℕ) (b : RootBank N) (js : List (Fin (Nat.clog 2 N+3))) :
    (dyadicRoots D b js).length≤b.length+js.length*extractionCost D := by
  induction js generalizing b with
  | nil => simp [dyadicRoots]
  | cons j js ih =>
    have h:=ih (dyadicRoot b D j)
    have h':=dyadicRoot_length D b j
    change (dyadicRoots D (dyadicRoot b D j) js).length≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def rootPrefix (D N : ℕ) : RootBank N := dyadicRoots D (axisRoot D N) (List.finRange (Nat.clog 2 N+3))

theorem rootPrefix_headers (D N : ℕ) : (rootPrefix D N).Headers (rootValues D) :=
  dyadicRoots_headers D _ _ _ (axisRoot_headers D N _)

theorem rootPrefix_axis (D N : ℕ) (hD : 0<D) (hN : 0<N) (hd : N∣D) :
    (rootPrefix D N).program.eval (rootValues D) (rootPrefix D N).axis=zeta N :=
  (dyadicRoots_axis _ _ _ _).trans (axisRoot_value D N hD hN hd)

theorem rootPrefix_omega (D N : ℕ) (hD : 0<D)
    (hd : ∀ j : Fin (Nat.clog 2 N+3),2^j.val∣D) (j : Fin (Nat.clog 2 N+3)) :
    (rootPrefix D N).program.eval (rootValues D) ((rootPrefix D N).omega j)=zeta (2^j.val) := by
  rw [rootPrefix,dyadicRoots_omega D _ _ hD (fun j _=>hd j) (axisRoot_headers D N _)]
  simp only [List.mem_finRange,ite_true]

theorem rootPrefix_admissible (D N : ℕ) : (rootPrefix D N).program.Admissible (rootValues D) :=
  dyadicRoots_admissible _ _ _ _ (axisRoot_admissible _ _ _)

theorem rootPrefix_rootReads (D N : ℕ) : (rootPrefix D N).program.rootReads=1 := by
  rw [rootPrefix,dyadicRoots_rootReads]
  exact (power_counts _ _ _ _).1

theorem rootPrefix_length (D N : ℕ) : (rootPrefix D N).length≤4+(Nat.clog 2 N+4)*extractionCost D := by
  have h:=dyadicRoots_length D (axisRoot D N) (List.finRange (Nat.clog 2 N+3))
  have ha : (axisRoot D N).length≤4+extractionCost D := by
    change (power _ _ _ _).length≤_
    rw [power_length]
    exact Nat.add_le_add_left (powerCost_div_bound D N) 4
  simp only [List.length_finRange] at h
  dsimp only [rootPrefix]
  nlinarith


/-! Typed root substitution, preserving the supplied destination prefix. -/
def substituteInstruction {r s k l : ℕ} (i : Instruction r k)
    (refs : Fin k → Fin l) (roots : Fin r → Fin l) (zero : Fin l) : Instruction s l :=
  match i with
  | .rational q => .rational q
  | .root j => .add (roots j) zero
  | .add j k => .add (refs j) (refs k)
  | .sub j k => .sub (refs j) (refs k)
  | .mul j k => .mul (refs j) (refs k)
  | .divide j k => .divide (refs j) (refs k)

theorem substituteInstruction_value {r s k l : ℕ} (i : Instruction r k)
    (refs : Fin k → Fin l) (rootRefs : Fin r → Fin l) (zero : Fin l)
    (zs : Fin s → ℂ) (values : Fin l → ℂ) (source : Fin r → ℂ) (old : Fin k → ℂ)
    (hr : ∀ j,values (rootRefs j)=source j) (hz : values zero=0)
    (hv : ∀ j,values (refs j)=old j) :
    (substituteInstruction i refs rootRefs zero).eval zs values=i.eval source old := by
  cases i <;> simp [substituteInstruction,Instruction.eval,hr,hz,hv]

theorem substituteInstruction_admissible {r s k l : ℕ} (i : Instruction r k)
    (refs : Fin k → Fin l) (rootRefs : Fin r → Fin l) (zero : Fin l)
    (values : Fin l → ℂ) (old : Fin k → ℂ) (hv : ∀ j,values (refs j)=old j) :
    (substituteInstruction (s:=s) i refs rootRefs zero).Admissible values↔i.Admissible old := by
  cases i <;> simp [substituteInstruction,Instruction.Admissible,hv]

structure Substitution (s l k : ℕ) where
  length : ℕ
  program : SProgram s length
  old : Fin l → Fin length
  refs : Fin k → Fin length

def substitute {r s l : ℕ} : {k : ℕ} → SProgram r k → SProgram s l →
    (Fin r → Fin l) → Fin l → Substitution s l k
  | _,.nil,q,_,_ => ⟨l,q,id,Fin.elim0⟩
  | _,.step p i,q,rs,z =>
    let t:=substitute p q rs z
    let out:=UniformScalarPreparation.Program.step t.program
      (substituteInstruction i t.refs (t.old ∘ rs) (t.old z))
    ⟨t.length+1,out,(fun j=>(t.old j).castSucc),
      Fin.snoc (fun j=>(t.refs j).castSucc) (Fin.last t.length)⟩

theorem substitute_length {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) : (substitute p q rs z).length=l+k := by
  induction p with
  | nil => rfl
  | step p i ih => change (substitute p q rs z).length+1=l+(_+1);rw [ih];omega

theorem substitute_old {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) (zs : Fin s → ℂ) (j : Fin l) :
    (substitute p q rs z).program.eval zs ((substitute p q rs z).old j)=q.eval zs j := by
  induction p with
  | nil => rfl
  | step p i ih =>
    rw [substitute.eq_2]
    simpa only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc] using ih

theorem substitute_old_val {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) (j : Fin l) : ((substitute p q rs z).old j).val=j.val := by
  induction p with
  | nil => rfl
  | step p i ih => simpa only [substitute,Fin.val_castSucc] using ih

theorem substitute_values {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) (zs : Fin s → ℂ) (source : Fin r → ℂ)
    (hr : ∀ j,q.eval zs (rs j)=source j) (hz : q.eval zs z=0) (j : Fin k) :
    (substitute p q rs z).program.eval zs ((substitute p q rs z).refs j)=p.eval source j := by
  induction p with
  | nil => exact Fin.elim0 j
  | step p i ih =>
    refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [substitute.eq_2]
      simp only [UniformScalarPreparation.Program.eval,Fin.snoc_last]
      exact substituteInstruction_value i _ _ _ zs _ source _
        (fun j=>(substitute_old p q rs z zs (rs j)).trans (hr j))
        ((substitute_old p q rs z zs z).trans hz) ih
    · rw [substitute.eq_2]
      simpa only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc] using ih j

theorem substitute_admissible {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) (zs : Fin s → ℂ) (source : Fin r → ℂ)
    (hr : ∀ j,q.eval zs (rs j)=source j) (hz : q.eval zs z=0)
    (hp : p.Admissible source) (hq : q.Admissible zs) : (substitute p q rs z).program.Admissible zs := by
  induction p with
  | nil => exact hq
  | step p i ih =>
    refine ⟨ih hp.1,?_⟩
    apply (substituteInstruction_admissible i _ _ _ _ _
      (substitute_values p q rs z zs source hr hz)).mpr
    exact hp.2

theorem substitute_rootReads {r s l k : ℕ} (p : SProgram r k) (q : SProgram s l)
    (rs : Fin r → Fin l) (z : Fin l) : (substitute p q rs z).program.rootReads=q.rootReads := by
  induction p with
  | nil => rfl
  | step p i ih =>
    rw [substitute.eq_2]
    cases i <;> simpa only [substituteInstruction,UniformScalarPreparation.Program.rootReads,
      Instruction.rootReads,Nat.add_zero] using ih

/-! Every Newton register survives the actual reciprocal recurrence. -/
structure Prefix {r l m : ℕ} (p : SProgram r l) (q : SProgram r m) : Prop where
  bound : l ≤ m
  value : ∀ zs j,q.eval zs (Fin.castLE bound j)=p.eval zs j

namespace Prefix

theorem refl {r l : ℕ} (p : SProgram r l) : Prefix p p := ⟨le_refl _,fun _ _=>rfl⟩

theorem trans {r l m k : ℕ} {p : SProgram r l} {q : SProgram r m} {u : SProgram r k}
    (hp : Prefix p q) (hq : Prefix q u) : Prefix p u := by
  refine ⟨hp.bound.trans hq.bound,fun zs j=>?_⟩
  exact (hq.value zs (Fin.castLE hp.bound j)).trans (hp.value zs j)

theorem step {r l : ℕ} (p : SProgram r l) (i : Instruction r l) :
    Prefix p (.step p i) := by
  refine ⟨Nat.le_succ _,?_⟩
  intro zs j
  change (UniformScalarPreparation.Program.step p i).eval zs j.castSucc=p.eval zs j
  simp only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc]

end Prefix

theorem reciprocal_term_prefix {r n k : ℕ} (b : UniformReciprocalPreparation.SumBank r n k)
    (hk : k<n) (j : Fin (k+1)) : Prefix b.bank.program (b.term hk j).bank.program :=
  (Prefix.step _ _).trans (Prefix.step _ _)

theorem reciprocal_terms_prefix {r n k : ℕ} (b : UniformReciprocalPreparation.SumBank r n k)
    (hk : k<n) (js : List (Fin (k+1))) : Prefix b.bank.program (b.terms hk js).bank.program := by
  induction js generalizing b with
  | nil => exact Prefix.refl _
  | cons j js ih => exact (reciprocal_term_prefix b hk j).trans (ih _)

theorem reciprocal_next_prefix {r n k : ℕ} (b : UniformReciprocalPreparation.Bank r n k) (hk : k<n) :
    Prefix b.program (UniformReciprocalPreparation.next b hk).program :=
  (reciprocal_terms_prefix ⟨b,b.zero⟩ hk _).trans ((Prefix.step _ _).trans (Prefix.step _ _))

theorem reciprocal_initial_prefix {r n : ℕ} (d : DAG r (n+1)) :
    Prefix d.program (UniformReciprocalPreparation.initial d).program :=
  (Prefix.step _ _).trans ((Prefix.step _ _).trans (Prefix.step _ _))

theorem reciprocal_build_prefix {r n : ℕ} (d : DAG r (n+1)) (k : ℕ) (hk : k≤n) :
    Prefix d.program (UniformReciprocalPreparation.build d k hk).program := by
  induction k with
  | zero => exact reciprocal_initial_prefix d
  | succ k ih => exact (ih (by omega)).trans (reciprocal_next_prefix _ _)


/-- Every radix-two root in the actual cache index range has order at most 8N. -/
theorem dyadic_width_bound {N : ℕ} (hN : 0<N) (j : Fin (Nat.clog 2 N+3)) : 2^j.val≤8*N := by
  have hp : 2^(Nat.clog 2 N)≤2*N := by
    by_cases h : N=1
    · subst N; norm_num
    · have hn : 1<N := by omega
      have hc := Nat.clog_pos (by omega : 1<2) hn
      have hpred := Nat.pow_pred_clog_lt_self (by omega : 1<2) hn
      simp only [Nat.pred_eq_sub_one] at hpred
      have he : 2^(Nat.clog 2 N)=2^(Nat.clog 2 N-1)*2 := by
        rw [←pow_succ];congr 1;omega
      rw [he];omega
  have he : j.val≤Nat.clog 2 N+2 := by have := j.isLt;omega
  have hm := Nat.pow_le_pow_right (by omega : 1≤2) he
  have hx : 2^(Nat.clog 2 N+2)=2^(Nat.clog 2 N)*4 := by rw [pow_add];norm_num
  rw [hx] at hm
  omega

theorem selected_axis_divides {ell L N : ℕ} (hd : N∣L) :
    N∣UniformBatching.masterRootOrder ell L := hd.trans (UniformBatching.workingOrder_dvd ell L)

theorem selected_dyadic_divides {ell L N : ℕ} (hN : 0<N) (hNL : N≤L)
    (j : Fin (Nat.clog 2 N+3)) : 2^j.val∣UniformBatching.masterRootOrder ell L :=
  UniformBatching.localPowerOrder_dvd hNL (dyadic_width_bound hN j)

/-- Actual Newton and series-reciprocal program, without any new root leaves. -/
def reciprocalBank (n : ℕ) :=
  UniformReciprocalPreparation.build (UniformReciprocalPreparation.newtonInput n) n (le_refl _)

def seedReplay (D n : ℕ) :=
  substitute (reciprocalBank n).program (rootPrefix D (n+1)).program
    (fun _ : Fin 1 => (rootPrefix D (n+1)).axis) ((rootPrefix D (n+1)).header 1)

/-- The original register domain covers the entire constructed seed. -/
def masterSeed (D n : ℕ) : State 1 (n+1) (seedReplay D n).length where
  length := (seedReplay D n).length
  program := (seedReplay D n).program
  original := id
  h := (seedReplay D n).refs ∘ (reciprocalBank n).h
  g := (seedReplay D n).refs ∘ (reciprocalBank n).g
  omega := (seedReplay D n).old ∘ (rootPrefix D (n+1)).omega
  cache := []

def masterReference (D n : ℕ) : Fin 1 → Fin (seedReplay D n).length :=
  fun _ => (seedReplay D n).old ((rootPrefix D (n+1)).header 0)

def headerReference (D n : ℕ) (j : Fin 4) : Fin (seedReplay D n).length :=
  (seedReplay D n).old ((rootPrefix D (n+1)).header j)

theorem root_source (D n : ℕ) (hD : 0<D) (hd : n+1∣D) (j : Fin 1) :
    (rootPrefix D (n+1)).program.eval (rootValues D) ((fun _ : Fin 1 => (rootPrefix D (n+1)).axis) j)=
      UniformNewton.Preparation.roots (zeta (n+1)) j :=
  rootPrefix_axis D (n+1) hD (by omega) hd

theorem root_zero (D n : ℕ) :
    (rootPrefix D (n+1)).program.eval (rootValues D) ((rootPrefix D (n+1)).header 1)=0 :=
  (rootPrefix_headers D (n+1)).2.1

theorem seedReplay_value (D n : ℕ) (hD : 0<D) (hd : n+1∣D) (j : Fin (reciprocalBank n).length) :
    (seedReplay D n).program.eval (rootValues D) ((seedReplay D n).refs j)=
      (reciprocalBank n).program.eval (UniformNewton.Preparation.roots (zeta (n+1))) j :=
  substitute_values _ _ _ _ _ _ (root_source D n hD hd) (root_zero D n) j

theorem masterSeed_admissible (D n : ℕ) (hD : 0<D) (hd : n+1∣D) :
    (masterSeed D n).program.Admissible (rootValues D) :=
  substitute_admissible _ _ _ _ _ _ (root_source D n hD hd) (root_zero D n)
    (UniformReciprocalPreparation.build_admissible _ _ _ _
      (UniformReciprocalPreparation.newtonInput_admissible (canonicalRoot (by omega)))
      (UniformReciprocalPreparation.newtonInput_zero n _)) (rootPrefix_admissible _ _)

theorem masterSeed_inputs (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    (masterSeed D n).Inputs (rootValues D) (PowerSeries.coeff · (NewtonFourier.invH (zeta (n+1))))
      (PowerSeries.coeff · (NewtonFourier.invH (zeta (n+1)))⁻¹) := by
  have hc := UniformReciprocalPreparation.build_correct (UniformReciprocalPreparation.newtonInput n)
    n (le_refl _) (UniformNewton.Preparation.roots (zeta (n+1))) _
    (UniformReciprocalPreparation.newtonInput_coeff n (zeta (n+1)))
  refine ⟨fun j => ?_,fun j => ?_,fun j => ?_⟩
  · exact (seedReplay_value D n hD hd _).trans (hc.1 j)
  · exact (seedReplay_value D n hD hd _).trans (hc.2.1 j)
  · change (seedReplay D n).program.eval (rootValues D)
      ((seedReplay D n).old ((rootPrefix D (n+1)).omega j))=_
    rw [UniformRadixTwoDAG.width_eq]
    exact (substitute_old _ _ _ _ _ _).trans (rootPrefix_omega D (n+1) hD hdyadic j)

theorem masterSeed_cachesGood (D n : ℕ) :
    (masterSeed D n).CachesGood (rootValues D) (PowerSeries.coeff · (NewtonFourier.invH (zeta (n+1))))
      (PowerSeries.coeff · (NewtonFourier.invH (zeta (n+1)))⁻¹) := by
  intro c hc;exact False.elim (List.not_mem_nil hc)

theorem masterSeed_rootReads (D n : ℕ) : (masterSeed D n).program.rootReads=1 := by
  change (seedReplay D n).program.rootReads=1
  rw [seedReplay,substitute_rootReads,rootPrefix_rootReads]

theorem masterSeed_length (D n : ℕ) :
    (masterSeed D n).length≤n*n+11*n+18+(Nat.clog 2 (n+1)+4)*extractionCost D := by
  change (seedReplay D n).length≤_
  rw [seedReplay,substitute_length]
  have hr := rootPrefix_length D (n+1)
  have hn : (reciprocalBank n).length=n*n+11*n+14 :=
    UniformReciprocalPreparation.newtonReciprocal_length n
  rw [hn];omega

theorem masterSeed_references (D n : ℕ) :
    referencesBound (n*n+11*n+18+(Nat.clog 2 (n+1)+4)*extractionCost D) (masterSeed D n).program :=
  referencesBound_of_length _ (by have := masterSeed_length D n;have := (masterSeed D n).h 0;omega)
    (masterSeed_length D n)

theorem masterReference_value (D n : ℕ) (j : Fin 1) :
    (masterSeed D n).program.eval (rootValues D) ((masterSeed D n).original (masterReference D n j))=
      rootValues D j := by
  exact (substitute_old _ _ _ _ _ _).trans (rootPrefix_headers D (n+1)).1

theorem headerReference_values (D n : ℕ) :
    (masterSeed D n).program.eval (rootValues D) (headerReference D n 1)=0 ∧
    (masterSeed D n).program.eval (rootValues D) (headerReference D n 2)=1 ∧
    (masterSeed D n).program.eval (rootValues D) (headerReference D n 3)=-1 := by
  exact ⟨(substitute_old _ _ _ _ _ _).trans (rootPrefix_headers D (n+1)).2.1,
    (substitute_old _ _ _ _ _ _).trans (rootPrefix_headers D (n+1)).2.2.1,
    (substitute_old _ _ _ _ _ _).trans (rootPrefix_headers D (n+1)).2.2.2⟩


/-- Reindex the original Newton table through the REAL reciprocal prefix. -/
def newtonRegister (D n : ℕ) (j : Fin (UniformReciprocalPreparation.newtonInput n).length) :
    Fin (seedReplay D n).length :=
  (seedReplay D n).refs (Fin.castLE (reciprocal_build_prefix _ n (le_refl _)).bound j)

theorem newtonRegister_value (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (j : Fin (UniformReciprocalPreparation.newtonInput n).length) :
    (masterSeed D n).program.eval (rootValues D) (newtonRegister D n j)=
      (UniformReciprocalPreparation.newtonInput n).program.eval
        (UniformNewton.Preparation.roots (zeta (n+1))) j :=
  (seedReplay_value D n hD hd _).trans ((reciprocal_build_prefix _ n (le_refl _)).value _ j)

def newtonReferences (D n : ℕ) (hD : 0<D) (hd : n+1∣D) :
    NewtonReferences (masterSeed D n) (rootValues D) (zeta (n+1)) where
  H := fun j => newtonRegister D n (UniformNewton.Preparation.finalH (n+1) j)
  scale := fun j => newtonRegister D n (UniformNewton.Preparation.finalScale (n+1) j)
  inverseDiagonal := fun j => newtonRegister D n (UniformNewton.Preparation.finalInvDiagonal (n+1) j)
  H_value := fun j => (newtonRegister_value D n hD hd _).trans
    (UniformNewton.Preparation.finalProgram_values _ (n+1) j).1
  scale_value := fun j => (newtonRegister_value D n hD hd _).trans
    (UniformNewton.Preparation.finalProgram_values _ (n+1) j).2.1
  inverseDiagonal_value := fun j => (newtonRegister_value D n hD hd _).trans
    (UniformNewton.Preparation.finalProgram_values _ (n+1) j).2.2.2.2

theorem master_unit (D : ℕ) (hD : 0<D) (j : Fin 1) : ‖rootValues D j‖=1 :=
  Complex.norm_eq_one_of_pow_eq_one (canonicalRoot hD).pow_eq_one hD.ne'

/-- A closed one-root Fourier schedule: no table-value, root-reference, bank
completeness, circuit-action or circuit-count assumptions occur. -/
noncomputable def localSchedule (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    List (UniformLocalFourierLayers.Layer (n+1)) :=
  fourierSchedule (masterSeed D n) (masterReference D n) (rootValues D) (master_unit D hD)
    (masterReference_value D n) (by omega) (canonicalRoot (by omega)) (newtonReferences D n hD hd)
    (masterSeed_inputs D n hD hd hdyadic)

theorem localSchedule_action (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) (x : Fin (n+1) → ℂ) :
    (UniformLocalFourierLayers.matrix (localSchedule D n hD hd hdyadic)).mulVec x=
      (fourierMatrix (n+1)).mulVec x :=
  canonical_fourier_action (masterSeed D n) (masterReference D n) (rootValues D) (master_unit D hD)
    (masterReference_value D n) (by omega) (newtonReferences D n hD hd)
    (masterSeed_inputs D n hD hd hdyadic) (masterSeed_cachesGood D n) (masterSeed_admissible D n hD hd) x

theorem localSchedule_calls (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    UniformLocalFourierLayers.calls (localSchedule D n hD hd hdyadic)≤32*(n+1)^3 :=
  fourierSchedule_call_bound (masterSeed D n) (masterReference D n) (rootValues D) (master_unit D hD)
    (masterReference_value D n) (by omega) (canonicalRoot (by omega)) (newtonReferences D n hD hd)
    (masterSeed_inputs D n hD hd hdyadic) (masterSeed_cachesGood D n) (masterSeed_admissible D n hD hd)

theorem localSchedule_slots (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    (localSchedule D n hD hd hdyadic).length≤UniformLocalFourierWord.sufficientSlots (n+1) :=
  fourierSchedule_length (masterSeed D n) (masterReference D n) (rootValues D) (master_unit D hD)
    (masterReference_value D n) (by omega) (canonicalRoot (by omega)) (newtonReferences D n hD hd)
    (masterSeed_inputs D n hD hd hdyadic) (masterSeed_cachesGood D n) (masterSeed_admissible D n hD hd)

/-- I is obtained from the dyadic root already in this one-root prefix. -/
def IReference (D n : ℕ) : Fin (seedReplay D n).length :=
  (seedReplay D n).old ((rootPrefix D (n+1)).omega ⟨2,by omega⟩)

theorem zeta_four : zeta 4=Complex.I := by
  unfold zeta
  norm_num only [Nat.cast_ofNat]
  have h : 2*(Real.pi : ℂ)*Complex.I/(4:ℂ)=(Real.pi : ℂ)/2*Complex.I := by ring
  rw [h]
  exact Complex.exp_pi_div_two_mul_I

theorem IReference_value (D n : ℕ) (hD : 0<D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    (masterSeed D n).program.eval (rootValues D) (IReference D n)=Complex.I := by
  exact ((substitute_old _ _ _ _ _ _).trans
    (rootPrefix_omega D (n+1) hD hdyadic ⟨2,by omega⟩)).trans zeta_four

/-- The paper's selected-axis order closes every divisibility obligation. -/
noncomputable def selectedSchedule (ell L n : ℕ) (hell : 0<ell) (hNL : n+1≤L) (hd : n+1∣L) :=
  localSchedule (UniformBatching.masterRootOrder ell L) n
    (UniformBatching.masterRootOrder_pos hell (by omega)) (selected_axis_divides hd)
    (selected_dyadic_divides (by omega) hNL)

theorem selectedSchedule_action (ell L n : ℕ) (hell : 0<ell) (hNL : n+1≤L) (hd : n+1∣L)
    (x : Fin (n+1) → ℂ) :
    (UniformLocalFourierLayers.matrix (selectedSchedule ell L n hell hNL hd)).mulVec x=
      (fourierMatrix (n+1)).mulVec x :=
  localSchedule_action _ _ _ _ _ x


/-- The ENTIRE balanced layer bank, including signed/conjugate replay scales. -/
def completeBank (D n : ℕ) :=
  planBank (masterSeed D n) (UniformBalancedToeplitz.plan (n+1)) (masterReference D n)

theorem completeBank_admissible (D n : ℕ) (hD : 0<D) (hd : n+1∣D) :
    (completeBank D n).env.program.Admissible (rootValues D) :=
  planBank_admissible _ _ _ _ (master_unit D hD) (masterSeed_admissible D n hD hd)
    (masterReference_value D n)

theorem completeBank_rootReads (D n : ℕ) : (completeBank D n).env.program.rootReads=1 := by
  rw [completeBank,planBank_rootReads,masterSeed_rootReads]

def bankBound (D n : ℕ) : ℕ :=
  20*(n*n+11*n+18+(Nat.clog 2 (n+1)+4)*extractionCost D)+20000*(n+2)^4+320*(n+1)^3+45

theorem completeBank_length (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    (completeBank D n).env.length≤bankBound D n := by
  have h := planBank_length (masterSeed D n) (UniformBalancedToeplitz.plan (n+1))
    (masterReference D n) (rootValues D) _ (masterSeed_inputs D n hD hd hdyadic)
    (masterSeed_cachesGood D n) (masterSeed_admissible D n hD hd) (by simp)
  change (completeBank D n).env.length≤20*(masterSeed D n).length+20000*(n+2)^4+320*(n+1)^3+1+44 at h
  have hs := masterSeed_length D n
  unfold bankBound
  change (completeBank D n).env.length≤_
  nlinarith

theorem completeBank_references (D n : ℕ) (hD : 0<D) (hd : n+1∣D)
    (hdyadic : ∀ j : Fin (Nat.clog 2 (n+1)+3),2^j.val∣D) :
    referencesBound (bankBound D n) (completeBank D n).env.program :=
  referencesBound_of_length _ (by unfold bankBound;omega) (completeBank_length D n hD hd hdyadic)

end ExactFourierCircuits.UniformMasterRootSeedDAG
