import UniformCacheTimingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingControl
open UniformMachine UniformAssembly UniformCacheTimingProgram
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformPreparationRowTableMachine (control_run)

lemma program_natOnly:∀ins∈program,UniformLocalRectangleDescriptors.NatOnly ins:=by
 have top:program.all (fun ins=>decide (UniformLocalRectangleDescriptors.NatOnly ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp top) ins hi)
def destinations (ins:Instruction):Prop:=match ins with
 | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>6500≤d∧d<6600
 | _=>True
instance(ins:Instruction):Decidable (destinations ins):=by cases ins <;>simp [destinations] <;>infer_instance
lemma program_destinations:∀ins∈program,destinations ins:=by
 have top:program.all (fun ins=>decide (destinations ins))=true:=by decide
 exact fun ins hi=>of_decide_eq_true ((List.all_eq_true.mp top) ins hi)
lemma keeps_nat (q:ℕ)(hq:q<6500∨6600≤q):∀ins∈program,UniformNewtonTableMachine.KeepsNat q ins:=by
 intro ins hi
 have bounds:=program_destinations ins hi
 have allowed:=program_natOnly ins hi
 cases ins <;>simp only [destinations] at bounds
 all_goals simp only [UniformLocalRectangleDescriptors.NatOnly] at allowed
 all_goals simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals omega
lemma execution_natFrame {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u)(q:ℕ)(hq:q<6500∨6600≤q):u.natReg q=s.natReg q:=
 UniformNewtonTableMachine.Executes.keeps_nat h.executes (keeps_nat q hq)
lemma execution_scalarFrame {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:BoundedExecution program n x B s t u):UniformLocalRectangleDescriptors.ScalarFrame s u:=
 UniformLocalRectangleDescriptors.natOnly_execution program_natOnly h.executes

noncomputable section
structure Header (D R U V T N K:ℕ) (s:State):Prop where
 nodes:s.natReg 6500=D
 requests:s.natReg 6501=R
 durations:s.natReg 6502=U
 starts:s.natReg 6503=V
 requestStarts:s.natReg 6504=T
 rootStart:s.natReg 6505=0
 nodeCount:s.natReg 6506=N
 requestCount:s.natReg 6507=K
 zero:s.natReg 6508=0
 one:s.natReg 6509=1
 two:s.natReg 6510=2
 three:s.natReg 6511=3
 seven:s.natReg 6514=7
 fourteen:s.natReg 6515=14
lemma Header.pc {D R U V T N K:ℕ}{s:State}(h:Header D R U V T N K s)(p:ℕ):
 Header D R U V T N K (setPC s p):=
 ⟨h.nodes,h.requests,h.durations,h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,
 h.zero,h.one,h.two,h.three,h.seven,h.fourteen⟩
structure Init (D R U V T N K i:ℕ) (s:State):Prop extends Header D R U V T N K s where
 index:s.natReg 6516=i
lemma Init.pc {D R U V T N K i:ℕ}{s:State}(h:Init D R U V T N K i s)(p:ℕ):
 Init D R U V T N K i (setPC s p):=⟨h.toHeader.pc p,h.index⟩
def ZeroPrefix (U i:ℕ)(s:State):Prop := ∀ j : ℕ, j < i → s.natHeap (U+j)=some 0
lemma init_header {D R U V T N K i:ℕ}(s:State)(h:Init D R U V T N K i s):
 Init D R U V T N K (i+1) (applyBlock initCell s):=by
 constructor
 · constructor <;>simp [initCell,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
   h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 · simp [initCell,applyBlock,Op.apply,writeNat,next,h.index,h.one]
lemma init_prefix {D R U V T N K i:ℕ}(s:State)(h:Init D R U V T N K i s)(bank:ZeroPrefix U i s):
 ZeroPrefix U (i+1) (applyBlock initCell s):=by
 intro j hj
 by_cases eq:j=i
 · subst j
   simp [initCell,applyBlock,Op.apply,writeNat,next,h.index,h.durations,h.zero,h.one]
 · have hjlt : j < i := by omega
   simpa [initCell,applyBlock,Op.apply,writeNat,next,h.index,h.durations,h.zero,h.one,eq] using bank j hjlt
lemma init_outside {D R U V T N K i:ℕ}(s:State)(h:Init D R U V T N K i s)
 (a:ℕ)(outside:a<U∨U+i+1≤a):
 (applyBlock initCell s).natHeap a=s.natHeap a:=by
 simp (disch:=omega) [initCell,applyBlock,Op.apply,writeNat,next,h.index,h.durations,h.zero,h.one]

/-- Every duration cell is initialized by three physical instructions. -/
theorem initialize_loop (n D R U V T N K i fuel B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Init D R U V T N K i s)(bank:ZeroPrefix U i s)(endIndex:i+fuel=N)
 (hp:s.pc=13)(hs:WordBound B s)(code:122≤B)(extent:U+N≤B):∃u,
 BoundedRuns program n x B s (5*fuel+1) u∧u.pc=18∧
 Init D R U V T N K N u∧ZeroPrefix U N u∧
 (∀a,a<U∨U+N≤a→u.natHeap a=s.natHeap a):=by
 induction fuel generalizing i s with
 | zero=>
  have eq:i=N:=by omega
  have step:UniformMachine.step program n x s=.running (setPC s 18):=by
   simp [UniformMachine.step,hp,code_13,h.index,h.nodeCount,show ¬i<N by omega,setPC]
  refine ⟨setPC s 18,control_run program n B 18 x s hs (by omega) step,rfl,?_,?_,fun _ _=>rfl⟩
  · simpa [eq] using h.pc 18
  · simpa [ZeroPrefix,eq,setPC] using bank
 | succ fuel ih=>
  have hi:i<N:=by omega
  have step:UniformMachine.step program n x s=.running (setPC s 14):=by
   simp [UniformMachine.step,hp,code_13,h.index,h.nodeCount,hi,setPC]
  have enter:=control_run program n B 14 x s hs (by omega) step
  let a:=setPC s 14
  have next:=block_runs initCell program 14 n B x a initCell_code rfl enter.final_bound
   (by change 17≤B;omega) (by simp [initCell,readable,Op.readable]) (by
    simp [initCell,peak,Op.peak,Op.apply,writeNat,next,a,setPC,h.durations,h.index,h.zero,h.one]
    omega)
  have pc:(applyBlock initCell a).pc=17:=by rw [applyBlock_pc];rfl
  have stepBack:UniformMachine.step program n x (applyBlock initCell a)=
   .running (setPC (applyBlock initCell a) 13):=by simp [UniformMachine.step,pc,code_17,setPC]
  have back:=control_run program n B 13 x (applyBlock initCell a) next.final_bound (by omega) stepBack
  obtain ⟨u,tail,up,out,zero,frame⟩:=ih (i+1) (setPC (applyBlock initCell a) 13)
   ((init_header a (h.pc 14)).pc 13) (init_prefix a (h.pc 14) bank) (by omega) rfl back.final_bound
  refine ⟨u,?_,up,out,zero,?_⟩
  · convert ((enter.trans next).trans back).trans tail using 1
    change 5*(fuel+1)+1=1+3+1+(5*fuel+1)
    omega
  · intro z hz
    rw [frame z hz]
    exact init_outside a (h.pc 14) z (by rcases hz with hz|hz <;>omega)
end
end ExactFourierCircuits.UniformCacheTimingControl
