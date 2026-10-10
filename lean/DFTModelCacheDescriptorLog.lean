import DFTModelCacheLiteral
import UniformWorkspaceSearchMachine

set_option autoImplicit false

/-! Charged integer doubling for the exact BalancedToeplitz cutoff search.
No logarithm or topology count is supplied by the caller.  Paper E, §3.1–3.5,
pp.13–18, especially Lemmas3.12–3.14, motivates the later cached descriptors. -/
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))

abbrev LogState := p w (p w w)
abbrev LogResult := p w w
abbrev LogPort : Port := some (LogState,LogResult)

def logTarget {p : Port} : Code false p LogState w := .atom .fst
def logIndex {p : Port} : Code false p LogState w := .comp (.atom .snd) (.atom .fst)
def logWidth {p : Port} : Code false p LogState w := .comp (.atom .snd) (.atom .snd)
def logResult {p : Port} : Code false p LogState LogResult := .atom .snd

def logNext {p : Port} : Code false p LogState LogState :=
  .fork logTarget (.fork
    (.comp (.fork logIndex (.atom (.lit 1))) (.atom (.int .add)))
    (.comp (.fork logWidth (.atom (.lit 2))) (.atom (.int .mul))))
def logTest : Code false LogPort LogState w :=
  .comp (.fork logWidth logTarget) (.atom (.int .lt))
def logBody : Code false LogPort LogState LogResult :=
  .ifz logTest logResult (.comp logNext .call)
def logBase : Prog false LogState LogResult := logResult

def logAux (fuel target k width : ℕ) : Bill LogResult.T :=
  depthRun (run logBase) (Code.run logBody) fuel (target,(k,width))

theorem logAux_stop (f t k W : ℕ) (h : ¬ W<t) :
    logAux (f+1) t k W=⟨(k,W),10,f+1,True⟩ := by
  change ((Code.run logBody (depthRun (run logBase) (Code.run logBody) f)
    (t,(k,W))).pay 1 (f+1))=_
  simp [logBody,logTest,logResult,logWidth,logTarget,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,h]

theorem logAux_go (f t k W : ℕ) (h : W<t) :
    logAux (f+1) t k W=(logAux f t (k+1) (W*2)).pay 28
      (max (max 1 (k+1)) (max (max 2 (W*2)) (f+1))) := by
  change ((Code.run logBody (depthRun (run logBase) (Code.run logBody) f)
    (t,(k,W))).pay 1 (f+1))=_
  simp [logBody,logTest,logResult,logWidth,logTarget,logNext,logIndex,Code.run,
    Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,h,logAux,
    Nat.add_assoc,max_assoc,max_comm,max_left_comm]
  omega

attribute [local irreducible] logAux

theorem logAux_spec (t fuel e : ℕ) (he : e≤Nat.clog 2 t)
    (hf : Nat.clog 2 t-e<fuel) :
    (logAux fuel t e (2^e)).val=(Nat.clog 2 t,2^Nat.clog 2 t) ∧
    (logAux fuel t e (2^e)).valid ∧
    (logAux fuel t e (2^e)).work=28*(Nat.clog 2 t-e)+10 ∧
    (logAux fuel t e (2^e)).peak ≤ max fuel (2*t+2) := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    by_cases hend : e=Nat.clog 2 t
    · have hs : ¬2^e<t := by rw [hend];exact Nat.not_lt.mpr (Nat.le_pow_clog (by decide) t)
      rw [logAux_stop _ _ _ _ hs]
      simp only [hend,Nat.sub_self,Nat.mul_zero,Nat.zero_add]
      exact ⟨trivial,trivial,trivial,le_max_left _ _⟩
    · have elt : e<Nat.clog 2 t := by omega
      have go:=Nat.pow_lt_of_lt_clog elt
      obtain ⟨iv,id,iw,ip⟩:=ih (e+1) (by omega) (by omega)
      rw [pow_succ] at iv id iw ip
      rw [logAux_go _ _ _ _ go]
      dsimp only [Bill.pay]
      refine ⟨iv,id,by omega,?_⟩
      have kb : e+1≤2*t+2 := by
        have h:=UniformWorkspaceSearchMachine.clog_bound t
        omega
      have wb : 2^e*2≤2*t+2 := by omega
      exact max_le (ip.trans (max_le_max (by omega) (le_refl _)))
        (max_le (max_le (by omega) (kb.trans (le_max_right _ _)))
          (max_le (max_le (by omega) (wb.trans (le_max_right _ _))) (le_max_left _ _)))

def logSeed : Prog false w (p w LogState) :=
  .fork (nat .add (.atom .id) (.atom (.lit 1)))
    (.fork (.atom .id) (.fork (.atom (.lit 0)) (.atom (.lit 1))))
def logarithm : Prog false w LogResult :=
  .comp logSeed (.descend logBase logBody)

theorem logarithm_run (t : ℕ) :
    run logarithm t=(logAux (t+1) t 0 1).pay 13 (t+1) := by
  change ((run logSeed t).pass (fun z =>
    (depthRun (run logBase) (Code.run logBody) z.1 z.2).pay 1 z.1)).pay 1 0=_
  simp [logSeed,nat,logAux,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,Nat.add_assoc,max_comm]
  omega

attribute [local irreducible] logarithm

theorem logarithm_spec (t : ℕ) :
    (run logarithm t).val=(Nat.clog 2 t,2^Nat.clog 2 t) ∧
    (run logarithm t).valid ∧
    (run logarithm t).work=28*Nat.clog 2 t+23 ∧
    (run logarithm t).peak≤2*t+2 := by
  have hf:=UniformWorkspaceSearchMachine.clog_bound t
  obtain ⟨hv,hd,hw,hp⟩:=logAux_spec t (t+1) 0 (by omega) (by omega)
  simp only [pow_zero,Nat.sub_zero] at hv hd hw hp
  rw [logarithm_run]
  dsimp only [Bill.pay]
  refine ⟨hv,hd,by omega,?_⟩
  have hp' : (logAux (t+1) t 0 1).peak ≤ 2*t+2 :=
    hp.trans (max_le (by omega) (le_refl _))
  exact max_le hp' (by omega)

end
end ExactFourierCircuits.DFTModelCacheDescriptor
