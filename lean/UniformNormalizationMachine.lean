import UniformIntegerScalarMachine
import UniformBoundedAssembly
import UniformPairMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformNormalizationMachine
open UniformMachine UniformAssembly UniformPairMachine
noncomputable section

/-- Nat17 supplies the transform length; Nat27 is the normalization destination.
The helper saves the working header, computes the rational 1/L by actual binary
integer conversion, writes the prepared scalar and restores Nat0. -/
def head : Program := [.natLiteral 41 0,.natBinary .add 42 0 41,
  .natLiteral 0 1,.natBinary .add 5 17 41]
def program : Program := embed head UniformIntegerScalarMachine.rationalProgram
  [.storeScalar 27 2,.natBinary .add 0 42 41,.halt] 33
theorem program_length : program.length=36 := rfl
theorem rational_code : CodeAt UniformIntegerScalarMachine.rationalProgram program 4 33 :=
  embed_code _ _ _ _

def zeroed (s : State) : State := writeNat s 41 0
def saved (s : State) : State := writeNat (zeroed s) 42 (s.natReg 0)
def numerator (s : State) : State := writeNat (saved s) 0 1
def entry (s : State) (L : ℕ) : State := writeNat (numerator s) 5 L

theorem startup_runs {n : ℕ} (x : Fin n→ℂ) (B L : ℕ) (s : State)
    (hp:s.pc=0) (hL:s.natReg 17=L) (hB:64≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 4 (entry s L) := by
  have h1:=writeNat_bound B s 41 0 hs (by omega) (by omega)
  have h2:=writeNat_bound B (zeroed s) 42 (s.natReg 0) h1
    (by simp [zeroed,writeNat,next,hp];omega) (hs.2.1 0)
  have h3:=writeNat_bound B (saved s) 0 1 h2
    (by simp [saved,zeroed,writeNat,next,hp];omega) (by omega)
  have h4:=writeNat_bound B (numerator s) 5 L h3
    (by simp [numerator,saved,zeroed,writeNat,next,hp];omega) (by rw [←hL];exact hs.2.1 17)
  refine .next hs (u:=zeroed s) ?_ (.next h1 (u:=saved s) ?_
    (.next h2 (u:=numerator s) ?_ (.next h3 (u:=entry s L) ?_ (.refl h4))))
  all_goals simp [step,program,embed,head,UniformIntegerScalarMachine.rationalProgram,
    UniformIntegerScalarMachine.block,entry,numerator,saved,zeroed,writeNat,next,hp,hL,evalNat]

def stored (s : State) (c : ℕ) : State :=
  {next s with scalarHeap:=Function.update s.scalarHeap c (some (s.scalarReg 2))}

theorem stored_bound (B c : ℕ) (s : State) (hs:WordBound B s)
    (hpc:s.pc+1≤B) (hc:c≤B) : WordBound B (stored s c) := by
  refine ⟨hpc,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2.1,hs.2.2.2.2.2⟩
  intro a v hv
  by_cases ha:a=c
  · subst a;exact hc
  · exact hs.2.2.2.1 a v (by simpa [stored,next,ha] using hv)

def Frame (c : ℕ) (s u : State) : Prop :=
  u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀a,a≠c → u.scalarHeap a=s.scalarHeap a) ∧ u.natReg 0=s.natReg 0 ∧
  (∀r,7≤r → r≠41 → r≠42 → u.natReg r=s.natReg r) ∧
  ∀r,4≤r → u.scalarReg r=s.scalarReg r

def runtime (L : ℕ) : ℕ :=
  20+UniformPowerMachine.loopCost 1+UniformPowerMachine.loopCost L

/-- Actual bounded execution, with no normalization-ready or scalar-action premise. -/
theorem normalization_execution {n : ℕ} (x : Fin n→ℂ) (B L c : ℕ) (s : State)
    (hp:s.pc=0) (h17:s.natReg 17=L) (h27:s.natReg 27=c)
    (hL:0<L) (hB:64≤B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (runtime L) u ∧
    u.scalarHeap c=some (prepared (L:ℂ)⁻¹) ∧ Frame c s u ∧ u.pc=35 := by
  have hstart:=startup_runs x B L s hp h17 hB hs
  let e:State:={entry s L with pc:=0}
  have he:WordBound B e:=changePC_bound B _ 0 hstart.final_bound (by omega)
  obtain ⟨w,hw,hval,hdep,hframe⟩:=UniformIntegerScalarMachine.bounded_rational_correct B
    (by omega) e he rfl (by simpa [e,entry,writeNat,next] using hL) n x
  have hentrypc:(entry s L).pc=4:=by simp [entry,numerator,saved,zeroed,writeNat,next,hp]
  have heq:placed 4 e=entry s L:=by
    change {entry s L with pc:=4}=entry s L
    rw [←hentrypc]
  have hbody:=UniformBoundedAssembly.boundedExecution_placed rational_code
    (by change 4+29≤B;omega) (by omega : 33≤B) hw
  rw [heq] at hbody
  have hw27:w.natReg 27=c:=by
    simpa [e,entry,numerator,saved,zeroed,writeNat,next] using
      (hframe.2.2.2.2.1 27 (by omega)).trans h27
  have hw41:w.natReg 41=0:=by
    simpa [e,entry,numerator,saved,zeroed,writeNat,next] using hframe.2.2.2.2.1 41 (by omega)
  have hw42:w.natReg 42=s.natReg 0:=by
    simpa [e,entry,numerator,saved,zeroed,writeNat,next] using hframe.2.2.2.2.1 42 (by omega)
  have hv:(w.scalarReg 2).value=(L:ℂ)⁻¹:=by
    simpa [e,entry,numerator,saved,zeroed,writeNat,next] using hval
  have hscalar:w.scalarReg 2=prepared (L:ℂ)⁻¹:=by
    cases h:w.scalarReg 2 with | mk value dependent => simp_all [prepared]
  let z:=stored {w with pc:=33} c
  have hz:WordBound B z:=stored_bound B c {w with pc:=33} hbody.final_bound
    (by change 33+1≤B;omega) (by rw [←h27];exact hs.2.1 27)
  let u:=writeNat z 0 (s.natReg 0)
  have hu:WordBound B u:=writeNat_bound B z 0 _ hz
    (by change 34+1≤B;omega) (hs.2.1 0)
  have hfinish:BoundedExecution program n x B {w with pc:=33} 3 u:=by
    refine .next hbody.final_bound (u:=z) ?_ (.next hz (u:=u) ?_ (.halt hu ?_))
    all_goals simp [step,program,embed,head,UniformIntegerScalarMachine.rationalProgram,
      UniformIntegerScalarMachine.block,z,u,stored,writeNat,next,evalNat,hw27,hw41,hw42]
  refine ⟨u,?_,?_,?_,rfl⟩
  · convert (hstart.trans hbody).executes hfinish using 1
    simp [runtime,e,entry,numerator,saved,zeroed,writeNat,next]
    omega
  · simp [u,z,stored,writeNat,next,hscalar]
  · refine ⟨hframe.1,hframe.2.2.1,hframe.2.2.2.1,?_,?_,?_,?_⟩
    · intro a ha
      simpa [u,z,stored,e,entry,numerator,saved,zeroed,writeNat,next,ha] using congrFun hframe.2.1 a
    · simp [u,writeNat,next]
    · intro r hr h41 h42
      simpa [u,z,stored,e,entry,numerator,saved,zeroed,writeNat,next,h41,h42,
        show r≠0 by omega,show r≠5 by omega] using hframe.2.2.2.2.1 r (by omega)
    · intro r hr
      exact hframe.2.2.2.2.2 r hr

theorem runtime_log_bound (L : ℕ) :
    runtime L≤7*(Nat.log2 (L+1)+1)+40 := by
  have h:=UniformPowerMachine.totalCost_log_bound L
  have h1:UniformPowerMachine.loopCost 1=9:=by
    rw [UniformPowerMachine.loopCost_step 1 (by decide)]
    norm_num [UniformPowerMachine.loopCost_zero,UniformPowerMachine.roundCost]
  simp only [runtime,h1]
  omega

end
end ExactFourierCircuits.UniformNormalizationMachine
