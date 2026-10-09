import DFTModelWorkingHeadersCanonical
import DFTModelCRTMetadataSource

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelWorkingHeaders
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def select : Prog false w PrimeResult :=
  .comp DFTModelRoot.selectionSeed (.descend base body)

theorem descend_run (fuel n p R : ℕ) :
    run (.descend base body : Prog false (Ty.p w State) PrimeResult) (fuel,(n,(p,R)))=
      (aux fuel n p R).pay 1 fuel := rfl

attribute [local irreducible] aux body base DFTModelRoot.prime prepend

theorem select_run (n : ℕ) : run select n =
    (aux (UniformWorkingPreparation.candidateLimit n) n 3 1).pay 37
      (max 3 (UniformWorkingPreparation.candidateLimit n)) := by
  rw [select,DFTModelRoot.code_comp,DFTModelRoot.selectionSeed,DFTModelRoot.code_fork,
    DFTModelRoot.limit_run,DFTModelRoot.selectionInitial_run]
  dsimp only [Bill.pass,Bill.one,Bill.pay]
  rw [descend_run]
  simp [Bill.pay,Nat.add_comm,Nat.add_left_comm,max_assoc,max_comm,max_left_comm]
  omega

theorem initial_scan (n : ℕ) (hn : 0<n) :
    scan n 3 1 (UniformWorkingPreparation.candidateLimit n)=
      (UniformWorkingLength.oddProduct n,suffix (UniformWorkingLength.axisCount n) 0) := by
  have hj : UniformWorkingLength.axisCount n≤2*n := by
    have h := UniformWorkingLength.firstExceed_bound n
    unfold UniformWorkingLength.axisCount
    omega
  have hq : UniformWorkingLength.nextPrime n≤UniformWorkingPreparation.candidateLimit n := by
    have h := UniformWorkingLength.nextPrime_upper n
    have hm := Nat.pow_le_pow_left (Nat.add_le_add_right hj 2) 2
    unfold UniformWorkingPreparation.candidateLimit
    exact h.trans ((Nat.mul_le_mul_left 64 hm).trans (Nat.le_add_right _ 1))
  have hq3 : 3≤UniformWorkingLength.nextPrime n := by
    have h := UniformWorkingLength.oddPrime_lower (UniformWorkingLength.axisCount n)
    change UniformWorkingLength.axisCount n+3≤UniformWorkingLength.nextPrime n at h
    omega
  exact scan_canonical n hn 3 0 _ (by omega) hq3
    (by norm_num [Nat.primeCounting',Nat.count_succ]) (by omega)

theorem select_spec (n : ℕ) (hn : 0<n) :
    (run select n).val=(UniformWorkingLength.oddProduct n,suffix (UniformWorkingLength.axisCount n) 0) ∧
    (run select n).work≤8*UniformWorkingCompletion.preparationBudget n ∧
    (run select n).peak≤DFTModelRoot.selectionPeak n ∧ (run select n).valid := by
  obtain ⟨hv,hw,hp,hd⟩ := aux_spec n hn 3 0 1 (UniformWorkingPreparation.candidateLimit n)
    (DFTModelRoot.selectionPeak n) (by omega)
    (by unfold DFTModelRoot.selectionPeak; omega)
    (by unfold DFTModelRoot.selectionPeak; omega)
    (by unfold DFTModelRoot.selectionPeak; omega)
  rw [initial_scan n hn] at hv hw
  rw [select_run]
  dsimp only [Bill.pay]
  refine ⟨hv,?_,?_,hd⟩
  · have hc := UniformWorkingPreparation.selectPrefix_cost_polynomial hn
    change (UniformWorkingPreparation.selectLoop n 3 0 1
      (UniformWorkingPreparation.candidateLimit n)).cost+12≤_ at hc
    dsimp only [suffix,Tape.tab] at hw
    simp only [Nat.sub_zero] at hw
    have h2 : UniformWorkingLength.axisCount n^2≤(UniformWorkingLength.axisCount n+2)^4 := by
      have h := Nat.pow_le_pow_left (show UniformWorkingLength.axisCount n≤UniformWorkingLength.axisCount n+2 by omega) 2
      have h' := Nat.pow_le_pow_right (show 1≤UniformWorkingLength.axisCount n+2 by omega) (show 2≤4 by omega)
      exact h.trans h'
    have h1 : UniformWorkingLength.axisCount n≤(UniformWorkingLength.axisCount n+2)^4 := by
      have h := Nat.le_self_pow (by decide : 4≠0) (UniformWorkingLength.axisCount n+2)
      omega
    have h0 : 1≤(UniformWorkingLength.axisCount n+2)^4 := by
      have h : 0<(UniformWorkingLength.axisCount n+2)^4 := pow_pos (by omega) _
      omega
    unfold UniformWorkingCompletion.preparationBudget
    omega
  · exact max_le hp (max_le (by unfold DFTModelRoot.selectionPeak; omega)
      (by unfold DFTModelRoot.selectionPeak; omega))

abbrev Selected := p w PrimeResult
def volume : Prog false Selected w := .atom .fst
def product : Prog false Selected w := .comp (.atom .snd) (.atom .fst)
def primes : Prog false Selected (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def count : Prog false Selected w := .comp primes (.atom .len)
def binary : Prog false Selected w := nat .div volume product
def repack : Prog false Selected Input :=
  .fork count (.fork volume (.fork binary primes))

theorem repack_run (V R : ℕ) (v : Tape ℕ) :
    run repack (V,(R,v))=⟨(v.len,(V,(V/R,v))),19,max v.len (V/R),True⟩ := by
  simp [repack,count,primes,volume,binary,nat,product,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]

/-- Finite typed integer syntax, from n alone, producing all WorkingCompletion headers and primes. -/
def program : Prog false w Input :=
  .comp (.fork DFTModelRoot.workingLength select) repack

theorem program_bill (n : ℕ) : run program n =
    (((run DFTModelRoot.workingLength n).pass (fun V =>
      (run select n).pass (fun t => Bill.one (V,t)))).pass (run repack)).pay 1 0 := rfl

theorem binary_quotient (n : ℕ) :
    UniformWorkingLength.workingLength n/UniformWorkingLength.oddProduct n=
      UniformWorkingLength.binaryFactor n := by
  rw [UniformWorkingLength.workingLength]
  exact Nat.mul_div_right _ (UniformWorkingLength.primeProduct_pos _)

end
end ExactFourierCircuits.DFTModelWorkingHeaders
