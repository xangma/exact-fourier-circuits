import DFTModelRecursiveScalarCore
import UniformGlobalMatchingScaleBankBridge

set_option autoImplicit false

/-! Charged prepared arithmetic for the nine actual matching-factor lanes.
The only supplied constants are the already-produced I and a inverse. -/
namespace ExactFourierCircuits.DFTModelCacheMatchingFactors
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Scalars := p (p sc sc) (p sc sc)
abbrev FactorInput := p (p w w) Scalars

def natural {s : Ty} : ℕ → Prog false s sc
  | 0 => .atom (.cz .scalar)
  | n+1 => .comp (.fork (.atom .cone) (natural n)) (.atom (.add .scalar))

theorem natural_run {s : Ty} (n : ℕ) (x : s.T) :
    run (natural n) x=⟨(n:ℂ),4*n+1,0,True⟩ := by
  induction n with
  | zero => simp [natural,run,Code.run,Atom.run,Bill.one]
  | succ n ih =>
    simp only [natural,comp_run,fork_run,atom_run,Atom.run,ih,
      Bill.one,Bill.pass,Bill.pay]
    congr 1
    · push_cast; ring
    · omega
    · simp

def ratio {s : Ty} (n d : ℕ) : Prog false s sc :=
  .comp (.fork (natural n) (.comp (natural d) (.atom .inv))) (.atom (.scale .scalar))

theorem ratio_run {s : Ty} (n d : ℕ) (x : s.T) :
    run (ratio n d) x=⟨(n:ℂ)/(d:ℂ),4*n+4*d+7,0,(d:ℂ)≠0⟩ := by
  simp only [ratio,comp_run,fork_run,atom_run,Atom.run,natural_run,
    Bill.one,Bill.pass,Bill.pay,div_eq_mul_inv]
  congr 1 <;> simp
  omega

def lane : Prog false FactorInput w := .comp (.atom .fst) (.atom .fst)
def side : Prog false FactorInput w := .comp (.atom .fst) (.atom .snd)
def constants : Prog false FactorInput (p sc sc) := .comp (.atom .snd) (.atom .snd)
def mu : Prog false FactorInput sc := .comp (.atom .snd) (.comp (.atom .fst) (.atom .fst))
def conjugate : Prog false FactorInput sc := .comp (.atom .snd) (.comp (.atom .fst) (.atom .snd))
def kappa : Prog false FactorInput sc :=
  .comp (.fork (.atom .cone)
    (.comp (.fork mu conjugate) (.atom (.scale .scalar)))) (.atom (.add .scalar))
def second : Prog false FactorInput sc :=
  .comp (.fork mu kappa) (.atom (.sub .scalar))
def multiply (f g : Prog false FactorInput sc) : Prog false FactorInput sc :=
  .comp (.fork f g) (.atom (.scale .scalar))
def divide (f g : Prog false FactorInput sc) : Prog false FactorInput sc :=
  multiply f (.comp g (.atom .inv))
def atMost (n : ℕ) : Prog false FactorInput w :=
  .comp (.fork lane (.atom (.lit n))) (.atom (.int .sub))

def left : Prog false FactorInput sc :=
  .ifz (atMost 0) (divide (ratio 5 4) kappa)
  (.ifz (atMost 1) (multiply (ratio 4 5) kappa)
  (.ifz (atMost 2) (divide (ratio 5 4) second)
  (.ifz (atMost 3) (multiply (ratio 4 5) second)
  (.ifz (atMost 4) (negative (natural 3))
  (.ifz (atMost 5) (natural 2)
  (.ifz (atMost 6) (negative (ratio 1 8))
  (.ifz (atMost 7) (.atom .cone) (.comp constants (.atom .snd)))))))))

def right : Prog false FactorInput sc :=
  .ifz (.comp (.fork lane (.atom (.lit 6))) (.atom (.int .lt)))
    (.ifz (atMost 6) (negative (ratio 1 6))
      (.ifz (atMost 7) (.comp constants (.atom .fst))
        (multiply (.comp constants (.atom .fst)) (.comp constants (.atom .snd)))))
    (.atom .cone)

def scalar : Prog false FactorInput sc := .ifz side left right

def input (l : Fin 9) (t : Fin 2) (z : ℂ) : FactorInput.T :=
  ((l.val,t.val),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))

theorem kappa_run (l t : ℕ) (z zc i ai : ℂ) :
    run kappa ((l,t),((z,zc),(i,ai)))=⟨1+z*zc,17,0,True⟩ := by
  simp [kappa,mu,conjugate,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem second_run (l t : ℕ) (z zc i ai : ℂ) :
    run second ((l,t),((z,zc),(i,ai)))=⟨z-(1+z*zc),25,0,True⟩ := by
  rw [second,comp_run,fork_run,kappa_run]
  simp [mu,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem atMost_run (n l t : ℕ) (z zc i ai : ℂ) :
    run (atMost n) ((l,t),((z,zc),(i,ai)))=⟨l-n,7,max n (l-n),True⟩ := by
  simp [atMost,lane,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem constants_run (l t : ℕ) (z zc i ai : ℂ) :
    run constants ((l,t),((z,zc),(i,ai)))=⟨(i,ai),3,0,True⟩ := by
  simp [constants,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem negative_run {s : Ty} (f : Prog false s sc) (x : s.T) :
    run (negative f) x=⟨-(run f x).val,(run f x).work+4,(run f x).peak,(run f x).valid⟩ := by
  simp [negative,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem multiply_run (f g : Prog false FactorInput sc) (x : FactorInput.T) :
    run (multiply f g) x=⟨(run f x).val*(run g x).val,
      (run f x).work+(run g x).work+3,max (run f x).peak (run g x).peak,
      (run f x).valid ∧ (run g x).valid⟩ := by
  simp [multiply,comp_run,fork_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

theorem divide_run (f g : Prog false FactorInput sc) (x : FactorInput.T) :
    run (divide f g) x=⟨(run f x).val/(run g x).val,
      (run f x).work+(run g x).work+5,max (run f x).peak (run g x).peak,
      (run f x).valid ∧ (run g x).valid ∧ (run g x).val≠0⟩ := by
  simp [divide,multiply_run,comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,
    div_eq_mul_inv]
  omega

theorem constant_first_run (l t : ℕ) (z zc i ai : ℂ) :
    run (.comp constants (.atom .fst)) ((l,t),((z,zc),(i,ai)))=⟨i,5,0,True⟩ := by
  rw [comp_run,constants_run]
  simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem constant_second_run (l t : ℕ) (z zc i ai : ℂ) :
    run (.comp constants (.atom .snd)) ((l,t),((z,zc),(i,ai)))=⟨ai,5,0,True⟩ := by
  rw [comp_run,constants_run]
  simp [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

def leftWork (l : Fin 9) : ℕ :=
  if l.val=0 then 73 else if l.val=1 then 79 else if l.val=2 then 97 else
  if l.val=3 then 103 else if l.val=4 then 57 else if l.val=5 then 57 else
  if l.val=6 then 103 else if l.val=7 then 65 else 69

theorem atMost_yes (n l t : ℕ) (z zc i ai : ℂ)
    (f g : Prog false FactorInput sc) (h : l≤n) :
    run (.ifz (atMost n) f g) ((l,t),((z,zc),(i,ai)))=
      (run f ((l,t),((z,zc),(i,ai)))).pay 8 n := by
  rw [ifz_run,atMost_run,Nat.sub_eq_zero_of_le h]
  simp [Bill.pass,Bill.pay]
  omega

theorem atMost_no (n l t : ℕ) (z zc i ai : ℂ)
    (f g : Prog false FactorInput sc) (h : n<l) :
    run (.ifz (atMost n) f g) ((l,t),((z,zc),(i,ai)))=
      (run g ((l,t),((z,zc),(i,ai)))).pay 8 (max n (l-n)) := by
  rw [ifz_run,atMost_run]
  simp [show l-n≠0 by omega,Bill.pass,Bill.pay]
  omega

theorem left_0 (t : ℕ) (z : ℂ) :
    run left ((0,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 0 0,leftWork 0,0,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢
  all_goals assumption

theorem left_1 (t : ℕ) (z : ℂ) :
    run left ((1,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 1 0,leftWork 1,1,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_2 (t : ℕ) (z : ℂ) :
    run left ((2,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 2 0,leftWork 2,2,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢
  all_goals assumption

theorem left_3 (t : ℕ) (z : ℂ) :
    run left ((3,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 3 0,leftWork 3,3,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_4 (t : ℕ) (z : ℂ) :
    run left ((4,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 4 0,leftWork 4,4,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_5 (t : ℕ) (z : ℂ) :
    run left ((5,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 5 0,leftWork 5,5,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_6 (t : ℕ) (z : ℂ) :
    run left ((6,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 6 0,leftWork 6,6,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_7 (t : ℕ) (z : ℂ) :
    run left ((7,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 7 0,leftWork 7,7,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_yes (h:=by decide)]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_8 (t : ℕ) (z : ℂ) :
    run left ((8,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z 8 0,leftWork 8,8,True⟩ := by
  have kn:=UniformLocalShear.kappa_ne_zero z
  have sn:=UniformLocalShear.second_ne_zero z
  rw [left]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  rw [atMost_no (h:=by decide)]
  repeat first
    | rw [divide_run]
    | rw [multiply_run]
    | rw [ratio_run]
    | rw [kappa_run]
    | rw [second_run]
    | rw [negative_run]
    | rw [natural_run]
    | rw [constant_second_run]
  norm_num [UniformGlobalMatchingScaleMachine.factor,UniformLocalShear.kappa,
    leftWork,atom_run,Atom.run,Bill.one,Bill.pay,div_eq_mul_inv] at kn sn ⊢

theorem left_spec (l : Fin 9) (t : ℕ) (z : ℂ) :
    run left ((l.val,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z l 0,leftWork l,l.val,True⟩ := by
  fin_cases l
  · exact left_0 t z
  · exact left_1 t z
  · exact left_2 t z
  · exact left_3 t z
  · exact left_4 t z
  · exact left_5 t z
  · exact left_6 t z
  · exact left_7 t z
  · exact left_8 t z

def belowSix : Prog false FactorInput w :=
  .comp (.fork lane (.atom (.lit 6))) (.atom (.int .lt))

theorem belowSix_run (l t : ℕ) (z zc i ai : ℂ) :
    run belowSix ((l,t),((z,zc),(i,ai)))=
      ⟨if l<6 then 1 else 0,7,6,True⟩ := by
  simp [belowSix,lane,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  split <;> simp

def rightWork (l : Fin 9) : ℕ :=
  if l.val<6 then 9 else if l.val=6 then 55 else if l.val=7 then 29 else 37

theorem right_spec (l : Fin 9) (t : ℕ) (z : ℂ) :
    run right ((l.val,t),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=
      ⟨UniformGlobalMatchingScaleMachine.factor z l 1,rightWork l,min 7 (max 6 l.val),True⟩ := by
  fin_cases l
  all_goals change run (.ifz belowSix _ _) _=_
  all_goals rw [ifz_run,belowSix_run]
  all_goals norm_num only [Bill.pass,Bill.pay]
  all_goals repeat first
    | rw [atMost_yes (h:=by decide)]
    | rw [atMost_no (h:=by decide)]
    | rw [negative_run]
    | rw [ratio_run]
    | rw [multiply_run]
    | rw [constant_first_run]
    | rw [constant_second_run]
  all_goals norm_num [rightWork,UniformGlobalMatchingScaleMachine.factor,atom_run,
    Atom.run,Bill.one,Bill.pay]

theorem side_run (l t : ℕ) (z zc i ai : ℂ) :
    run side ((l,t),((z,zc),(i,ai)))=⟨t,3,0,True⟩ := by
  simp [side,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem scalar_zero_spec (l : Fin 9) (z : ℂ) :
    run scalar (input l 0 z)=
      ⟨UniformGlobalMatchingScaleMachine.factor z l 0,leftWork l+4,l.val,True⟩ := by
  change run scalar ((l.val,0),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=_
  rw [scalar,ifz_run,side_run]
  simp only [Bill.pass,Bill.pay,ite_true]
  rw [left_spec]
  simp
  omega

theorem scalar_one_spec (l : Fin 9) (z : ℂ) :
    run scalar (input l 1 z)=
      ⟨UniformGlobalMatchingScaleMachine.factor z l 1,rightWork l+4,min 7 (max 6 l.val),True⟩ := by
  change run scalar ((l.val,1),((z,starRingEnd ℂ z),(Complex.I,ExactFourierCircuits.a⁻¹)))=_
  rw [scalar,ifz_run,side_run]
  norm_num only [Bill.pass,Bill.pay]
  rw [right_spec]
  simp
  omega

theorem scalar_correct (l : Fin 9) (t : Fin 2) (z : ℂ) :
    (run scalar (input l t z)).val=UniformGlobalMatchingScaleMachine.factor z l t ∧
    (run scalar (input l t z)).valid ∧
    (run scalar (input l t z)).work≤200 ∧
    (run scalar (input l t z)).peak≤9 := by
  have work : leftWork l≤190 ∧ rightWork l≤190 := by
    fin_cases l <;> norm_num [leftWork,rightWork]
  fin_cases t
  · have h:=scalar_zero_spec l z
    exact ⟨congrArg Bill.val h,(congrArg Bill.valid h).mpr trivial,
      (congrArg Bill.work h).le.trans (by dsimp only [Bill.work]; omega),
      (congrArg Bill.peak h).le.trans (by dsimp only [Bill.peak]; omega)⟩
  · have h:=scalar_one_spec l z
    exact ⟨congrArg Bill.val h,(congrArg Bill.valid h).mpr trivial,
      (congrArg Bill.work h).le.trans (by dsimp only [Bill.work]; omega),
      (congrArg Bill.peak h).le.trans (by dsimp only [Bill.peak]; omega)⟩

end
end ExactFourierCircuits.DFTModelCacheMatchingFactors
