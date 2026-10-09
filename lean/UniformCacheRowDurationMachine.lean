import UniformLocalCacheTiming
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheRowDurationMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)

def boot : List Op := [.literal 6546 0,.literal 6547 1,.literal 6548 2,
 .literal 6549 352,.literal 6550 330,.literal 6551 28,
 .add 6543 6540 6541,.mul 6543 6543 6548,.literal 6544 1,.literal 6545 0]
def logStep : List Op := [.mul 6544 6544 6548,.add 6545 6545 6547]
def finish : List Op := [.mul 6542 6545 6549,.add 6542 6542 6550,.mul 6542 6542 6551]
def program : Program := boot.map Op.code++[.branchLT 6544 6543 11 14]++
 logStep.map Op.code++[.jump 10]++finish.map Op.code++[.halt]
lemma program_length : program.length=18 := rfl
lemma boot_code : BlockAt boot program 0 := by
 intro i hi;change i<10 at hi;interval_cases i <;>rfl
lemma log_code : BlockAt logStep program 11 := by
 intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma finish_code : BlockAt finish program 14 := by
 intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma branch_at : program[10]?=some (.branchLT 6544 6543 11 14) := rfl
lemma jump_at : program[13]?=some (.jump 10) := rfl
lemma halt_at : program[17]?=some .halt := rfl

def amount (a e : ℕ) : ℕ := 28*(352*Nat.clog 2 (2*(a+e))+330)
lemma amount_rectangle (q : UniformLocalRectangleDescriptors.Row) :
 amount q.a q.e=UniformLocalCacheTiming.rectangleDuration q := by
 unfold amount UniformLocalCacheTiming.rectangleDuration UniformWorkspacePlanner.exponent
 ring

def budget (a e : ℕ) : ℕ := 20000*(a+e+1)

noncomputable section
structure Frame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,r<6542∨6551<r→u.natReg r=s.natReg r
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.pc {s u : State} (f:Frame s u) (p : ℕ) : Frame s (setPC u p) :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Frame.trans {s u t : State} (f:Frame s u) (g:Frame u t) : Frame s t :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
  g.outputs.trans f.outputs,g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma boot_frame (s : State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma log_frame (s : State) : Frame s (applyBlock logStep s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h
 simp (disch:=omega) [logStep,applyBlock,Op.apply,writeNat,next]
lemma finish_frame (s : State) : Frame s (applyBlock finish s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h
 simp (disch:=omega) [finish,applyBlock,Op.apply,writeNat,next]
structure LogCounters (N j : ℕ) (s : State) : Prop where
 one:s.natReg 6547=1
 two:s.natReg 6548=2
 goal:s.natReg 6543=N
 power:s.natReg 6544=2^j
 exponent:s.natReg 6545=j
 c352:s.natReg 6549=352
 c330:s.natReg 6550=330
 c28:s.natReg 6551=28
lemma LogCounters.pc {N j : ℕ} {s : State} (h:LogCounters N j s) (p : ℕ) :
 LogCounters N j (setPC s p) := ⟨h.one,h.two,h.goal,h.power,h.exponent,h.c352,h.c330,h.c28⟩

/-- Four actual charged instructions per successful doubling, plus the exit branch. -/
theorem doubling_loop (n N j fuel B : ℕ) (x:Fin n→ℂ) (s:State)
 (hc:LogCounters N j s) (hj:j+fuel=Nat.clog 2 N) (hp:s.pc=10)
 (hs:WordBound B s) (hB:2*N+80≤B) : ∃u,
 BoundedRuns program n x B s (4*fuel+1) u ∧u.pc=14∧
 LogCounters N (Nat.clog 2 N) u∧Frame s u := by
 induction fuel generalizing j s with
 | zero=>
  have he:j=Nat.clog 2 N:=by omega
  have stop:¬2^j<N:=by rw [he];exact Nat.not_lt.mpr (Nat.le_pow_clog (by decide) N)
  have step:UniformMachine.step program n x s=.running (setPC s 14):=by
   simp [UniformMachine.step,hp,branch_at,hc.power,hc.goal,stop,setPC]
  refine ⟨setPC s 14,?_,rfl,?_,(Frame.refl s).pc 14⟩
  · exact control_run program n B 14 x s hs (by omega) step
  · simpa [he] using hc.pc 14
 | succ fuel ih=>
  have smaller:j<Nat.clog 2 N:=by omega
  have pow:2^j<N:=Nat.pow_lt_of_lt_clog smaller
  have step:UniformMachine.step program n x s=.running (setPC s 11):=by
   simp [UniformMachine.step,hp,branch_at,hc.power,hc.goal,pow,setPC]
  have entered:=control_run program n B 11 x s hs (by omega) step
  let a:=setPC s 11
  have safe:peak logStep a≤B:=by
   simp [logStep,peak,Op.peak,Op.apply,writeNat,next,a,setPC,hc.power,hc.two,hc.one,hc.exponent]
   have log:=UniformWorkspaceSearchMachine.clog_bound N
   omega
  have middle:=block_runs logStep program 11 n B x a log_code rfl entered.final_bound
   (by change 13≤B;omega) (by simp [logStep,readable,Op.readable]) safe
  have next:LogCounters N (j+1) (applyBlock logStep a):=by
   constructor <;>simp [logStep,applyBlock,Op.apply,writeNat,next,a,setPC,
    hc.one,hc.two,hc.goal,hc.power,hc.exponent,hc.c352,hc.c330,hc.c28,pow_succ]
  have pc:(applyBlock logStep a).pc=13:=by rw [applyBlock_pc];rfl
  have backstep:UniformMachine.step program n x (applyBlock logStep a)=
   .running (setPC (applyBlock logStep a) 10):=by simp [UniformMachine.step,pc,jump_at,setPC]
  have back:=control_run program n B 10 x (applyBlock logStep a) middle.final_bound (by omega) backstep
  obtain ⟨u,tail,up,out,frame⟩:=ih (j+1) (setPC (applyBlock logStep a) 10)
   (next.pc 10) (by omega) rfl back.final_bound
  refine ⟨u,?_,up,out,?_⟩
  · convert ((entered.trans middle).trans back).trans tail using 1
    change 4*(fuel+1)+1=1+2+1+(4*fuel+1)
    omega
  · exact ((Frame.refl s).pc 11 |>.trans (log_frame a) |>.pc 10).trans frame

theorem execution (n a e B : ℕ) (x:Fin n→ℂ) (s:State)
 (ha:s.natReg 6540=a) (he:s.natReg 6541=e) (hp:s.pc=0)
 (hs:WordBound B s) (hb:budget a e≤B) : ∃u,
 BoundedExecution program n x B s (4*Nat.clog 2 (2*(a+e))+15) u ∧u.pc=17∧
 u.natReg 6542=amount a e∧Frame s u := by
 have code:352≤B:=by unfold budget at hb;omega
 have goal:2*(a+e)≤B:=by unfold budget at hb;omega
 have first:=block_runs boot program 0 n B x s boot_code hp hs (by change 10≤B;omega)
  (by simp [boot,readable,Op.readable]) (by
   simp [boot,peak,Op.peak,Op.apply,writeNat,next,ha,he]
   omega)
 let t:=applyBlock boot s
 have counters:LogCounters (2*(a+e)) 0 t:=by
  constructor <;>simp [t,boot,applyBlock,Op.apply,writeNat,next,ha,he,Nat.mul_comm]
 have tp:t.pc=10:=by rw [applyBlock_pc,hp];rfl
 have hB:2*(2*(a+e))+80≤B:=by unfold budget at hb;omega
 obtain ⟨z,run,zp,zc,zf⟩:=doubling_loop n (2*(a+e)) 0 (Nat.clog 2 (2*(a+e))) B x t
  counters (by omega) tp first.final_bound hB
 have c352:z.natReg 6549=352:=zc.c352
 have c330:z.natReg 6550=330:=zc.c330
 have c28:z.natReg 6551=28:=zc.c28
 have log:=UniformWorkspaceSearchMachine.clog_bound (2*(a+e))
 have last:=block_runs finish program 14 n B x z finish_code zp run.final_bound (by change 17≤B;omega)
  (by simp [finish,readable,Op.readable]) (by
   simp [finish,peak,Op.peak,Op.apply,writeNat,next,zc.exponent,c352,c330,c28]
   unfold budget at hb
   omega)
 let u:=applyBlock finish z
 have up:u.pc=17:=by rw [applyBlock_pc,zp];rfl
 have halt:BoundedExecution program n x B u 1 u:=.halt last.final_bound
  (by simp [UniformMachine.step,up,halt_at])
 refine ⟨u,?_,up,?_,(boot_frame s |>.trans zf).trans (finish_frame z)⟩
 · convert first.executes (run.executes (last.executes halt)) using 1
   change 4*Nat.clog 2 (2*(a+e))+15=10+(4*Nat.clog 2 (2*(a+e))+1)+(3+1)
   omega
 · simp [u,finish,applyBlock,Op.apply,writeNat,next,zc.exponent,c352,c330,c28,amount,Nat.mul_comm]
end
end ExactFourierCircuits.UniformCacheRowDurationMachine
