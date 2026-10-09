import UniformCacheTimingControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingStartup
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)

structure Input (D R U V T N K:ℕ)(s:State):Prop where
 nodes:s.natReg 6500=D
 requests:s.natReg 6501=R
 durations:s.natReg 6502=U
 starts:s.natReg 6503=V
 requestStarts:s.natReg 6504=T
 nodeCount:s.natReg 4281=N
 requestEnd:s.natReg 4282=R+7*K

noncomputable section
lemma boot_header {D R U V T N K:ℕ}(s:State)(h:Input D R U V T N K s):
 Header D R U V T N K (writeNat (applyBlock boot s) 6507 K):=by
 constructor <;>simp [boot,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
 h.starts,h.requestStarts,h.nodeCount,h.requestEnd]
lemma boot_heap (s:State):(applyBlock boot s).natHeap=s.natHeap:=rfl
lemma setup_header {D R U V T N K:ℕ}(s:State)(h:Header D R U V T N K s):
 Init D R U V T N K 0 (applyBlock initSetup s):=by
 constructor
 · constructor <;>simp [initSetup,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
   h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 · simp [initSetup,applyBlock,Op.apply,writeNat,next]
lemma reverse_header {D R U V T N K:ℕ}(s:State)(h:Init D R U V T N K N s):
 Init D R U V T N K N (applyBlock reverseSetup s):=by
 constructor
 · constructor <;>simp [reverseSetup,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
   h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 · simp [reverseSetup,applyBlock,Op.apply,writeNat,next,h.nodeCount,h.zero]

/-- Header values and actual173 counters are read by charged instructions;
no duration or ready-time input is supplied. -/
theorem startup (n D R U V T N K B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Input D R U V T N K s)(hp:s.pc=0)(hs:WordBound B s)
 (code:122≤B)(extent:U+N≤B):∃u,
 BoundedRuns program n x B s (5*N+15) u∧u.pc=19∧
 Init D R U V T N K N u∧ZeroPrefix U N u∧
 (∀a,a<U∨U+N≤a→u.natHeap a=s.natHeap a):=by
 have count:N≤B:=by have hh:=hs.2.1 4281;omega
 have request:R+7*K≤B:=by have hh:=hs.2.1 4282; rw [h.requestEnd] at hh; exact hh
 have first:=block_runs boot program 0 n B x s boot_code hp hs
  (by change 11≤B;omega) (by simp [boot,readable,Op.readable]) (by
   simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.nodeCount,h.requestEnd,h.requests]
   omega)
 let t:=applyBlock boot s
 have tp:t.pc=11:=by rw [applyBlock_pc,hp];rfl
 have tk:t.natReg 6507=7*K:=by simp [t,boot,applyBlock,Op.apply,writeNat,next,h.requests,h.requestEnd]
 have t7:t.natReg 6514=7:=by simp [t,boot,applyBlock,Op.apply,writeNat,next]
 have divstep:UniformMachine.step program n x t=.running (writeNat t 6507 K):=by
  simp [UniformMachine.step,tp,code_11,evalNat,tk,t7]
 have divbound:=writeNat_bound B t 6507 K first.final_bound (by omega) (by omega)
 have divrun:BoundedRuns program n x B t 1 (writeNat t 6507 K):=
  .next first.final_bound divstep (.refl divbound)
 let z:=writeNat t 6507 K
 have zp:z.pc=12:=by simp [z,writeNat,next,tp]
 have zh:Header D R U V T N K z:=boot_header s h
 have setup:=block_runs initSetup program 12 n B x z initSetup_code zp divrun.final_bound
  (by change 13≤B;omega) (by simp [initSetup,readable,Op.readable]) (by simp [initSetup,peak,Op.peak])
 let a:=applyBlock initSetup z
 have ap:a.pc=13:=by rw [applyBlock_pc,zp];rfl
 obtain ⟨b,loop,bp,bh,bank,frame⟩:=initialize_loop n D R U V T N K 0 N B x a
  (setup_header z zh) (by simp [ZeroPrefix]) (by omega) ap setup.final_bound code extent
 have last:=block_runs reverseSetup program 18 n B x b reverseSetup_code bp loop.final_bound
  (by change 19≤B;omega) (by simp [reverseSetup,readable,Op.readable]) (by
   simp [reverseSetup,peak,Op.peak,bh.nodeCount,bh.zero]
   omega)
 let u:=applyBlock reverseSetup b
 have up:u.pc=19:=by rw [applyBlock_pc,bp];rfl
 refine ⟨u,?_,up,reverse_header b bh,bank,?_⟩
 · convert ((first.trans divrun).trans setup).trans (loop.trans last) using 1
   change 5*N+15=11+1+1+(5*N+1+1)
   omega
 · intro q hq
   exact frame q hq
end
end ExactFourierCircuits.UniformCacheTimingStartup
