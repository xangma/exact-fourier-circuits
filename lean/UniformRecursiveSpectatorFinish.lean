import UniformRecursiveRecordControl
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSpectatorFinish
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (program address size)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace S
export UniformBinarySpectatorCMachine (program execution arrayCost transformed Frame Changed arrayBase)
end S
noncomputable section

def setupOps (count:ℕ):List Op := [.binary .mul 5200 4120 4153,.literal 5201 count,
 .binary .mul 5202 4121 4153,.binary .mul 5203 4122 4153,.binary .mul 5204 4060 4061]
lemma setup_length (count:ℕ):(setupOps count).length=5:=rfl
def SetupChanged (j:ℕ):Prop := j=5200∨j=5201∨j=5202∨j=5203∨j=5204
structure SetupFrame (s t:State):Prop where
 natHeap:t.natHeap=s.natHeap
 scalarHeap:t.scalarHeap=s.scalarHeap
 scalarReg:t.scalarReg=s.scalarReg
 outputs:t.outputs=s.outputs
 roots:t.rootOrders=s.rootOrders
 natReg:∀j,¬SetupChanged j→t.natReg j=s.natReg j
lemma setup_frame (count:ℕ)(s:State):SetupFrame s (applyBlock (setupOps count) s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j hj
 unfold SetupChanged at hj
 simp (disch:=omega) [setupOps,applyBlock,Op.apply,evalNat,writeNat,next]

/-- Five charged header operations and the actual jump. The start axis is
computed as q*m; no preinstalled spectator headers are assumed. -/
theorem setup_generic (main:Program)(start exit count n B k q m A V:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt (setupOps count) main start)(atJump:main[start+5]?=some (.jump exit))
 (pc:s.pc=start)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (volume:s.natReg 4122=V)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)
 (bound:WordBound B s)(extent:start+6≤B)(ret:exit≤B)(countBound:count≤B)(axes:q*m≤k):∃t,
 BoundedRuns main n x B s 6 t ∧ t.pc=exit ∧
 t.natReg 5200=k ∧ t.natReg 5201=count ∧ t.natReg 5202=A ∧ t.natReg 5203=V ∧ t.natReg 5204=q*m ∧ SetupFrame s t:=by
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have ab:A≤B:=by have h:=bound.2.1 4121;rwa [base] at h
 have vb:V≤B:=by have h:=bound.2.1 4122;rwa [volume] at h
 have qb:q*m≤B:=axes.trans kb
 have safe:readable (setupOps count) s∧peak (setupOps count) s≤B:=by
  simp [setupOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   one,bits,base,volume,columns,width,countBound,kb,ab,vb,qb]
 have run:=block_runs (setupOps count) main start n B x s atCode pc bound
  (by rw [setup_length];omega) safe.1 safe.2
 let u:=applyBlock (setupOps count) s
 let t:=setPC u exit
 have up:u.pc=start+5:=by rw [UniformRecursiveNodePreparation.block_pc,pc,setup_length]
 have tb:=changePC_bound B u exit run.final_bound ret
 have jump:BoundedRuns main n x B u 1 t:=.next run.final_bound
  (by simp only [step,up,atJump];rfl) (.refl tb)
 have fr:=setup_frame count s
 refine ⟨t,?_,rfl,?_,?_,?_,?_,?_,⟨fr.natHeap,fr.scalarHeap,fr.scalarReg,fr.outputs,fr.roots,fr.natReg⟩⟩
 · simpa only [setup_length] using run.trans jump
 all_goals simp [t,u,setPC,setupOps,applyBlock,Op.apply,evalNat,writeNat,next,one,bits,base,volume,columns,width]

lemma setup_code:BlockAt (setupOps UniformRecursiveSelfCallMachine.W) P.program (P.address .spectatorSetup):=
 UniformRecursiveSavingExecution.part_block .spectatorSetup _ _ rfl
lemma setup_jump:P.program[P.address .spectatorSetup+5]?=some (.jump (P.address .spectator)):=
 UniformRecursiveSavingExecution.part_at .spectatorSetup 5 (by decide)
theorem setup_execution (n B k q m A V:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .spectatorSetup)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (volume:s.natReg 4122=V)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)
 (bound:WordBound B s)(code:P.program.length≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)(axes:q*m≤k):∃t,
 BoundedRuns P.program n x B s 6 t ∧ t.pc=P.address .spectator ∧
 t.natReg 5200=k ∧ t.natReg 5201=UniformRecursiveSelfCallMachine.W ∧ t.natReg 5202=A ∧
 t.natReg 5203=V ∧ t.natReg 5204=q*m ∧ SetupFrame s t:=
 setup_generic P.program (P.address .spectatorSetup) (P.address .spectator) UniformRecursiveSelfCallMachine.W
 n B k q m A V x s setup_code setup_jump pc one bits base volume columns width bound
 (R.code_bound .spectatorSetup 6 B rfl code) (R.start_bound .spectator B code) countBound axes

/-- The same69-cell spectator bytecode executes on every stored role and
returns to the fixed finish branch, with its complete data/control frame. -/
theorem spectator_embedded (main:Program)(start exit n B k b count A:ℕ)(x:Fin n→ℂ)
 (link:CodeAt S.program main start exit)(s:State)(v:Fin count→Fin (2^k)→Scalar)
 (pc:s.pc=start)(bits:s.natReg 5200=k)(arrays:s.natReg 5201=count)(base:s.natReg 5202=A)
 (size:s.natReg 5203=2^k)(axis:s.natReg 5204=b)
 (data:∀w z,s.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z))
 (axes:b≤k)(heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:start+S.program.length≤B)(ret:exit≤B)
 (extent:A+count*2^k≤B)(stride:2^b*2≤B):∃u,
 BoundedRuns main n x B s (4*b+count*S.arrayCost k b+9) u ∧ u.pc=exit ∧
 (∀w z,u.scalarHeap (S.arrayBase A k w.val+z.val)=some (S.transformed k b (v w) z)) ∧
 S.Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u:=by
 have localCode:S.program.length≤B:=(Nat.le_add_left _ _).trans code
 have small:69≤B:=by simpa only [UniformBinarySpectatorCMachine.program_length] using localCode
 obtain ⟨u,run,out,frame,con,_⟩:=S.execution n B k b count A x (setPC s 0) v rfl bits arrays base size axis
  data axes heapBase constants small extent stride (changePC_bound B s 0 bound (by omega))
 have placed:=UniformBoundedAssembly.boundedExecution_placed link code ret run
 have begin:UniformAssembly.placed start (setPC s 0)=s:=by
  change setPC s start=s;rw [←pc];cases s;rfl
 rw [begin] at placed
 exact ⟨setPC u exit,placed,rfl,out,⟨frame.natHeap,frame.outputs,frame.roots,frame.natReg,frame.scalarReg,frame.scalarHeap⟩,con⟩

/-- The final branch reads the actual stack depth: root goes to halt,
descendant goes to the real saved-frame return site. All data is retained. -/
theorem finish_generic (main:Program)(loc root child n B depth:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:main[loc]?=some (.branchLT 4151 4153 root child))
 (pc:s.pc=loc)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (bound:WordBound B s)(rootBound:root≤B)(childBound:child≤B):
 BoundedRuns main n x B s 1 (setPC s (if depth=0 then root else child)):=by
 have eq:(depth<1)=(depth=0):=propext (by omega)
 exact .next bound (by simp only [step,pc,atCode,dp,one,eq];rfl)
  (.refl (changePC_bound B s _ bound (by split <;> assumption)))
lemma zero_cell (main:Program)(loc:ℕ)(i:Instruction)(h:main[loc+0]?=some i):main[loc]?=some i:=by simpa only [Nat.add_zero] using h
lemma finish_code:P.program[P.address .finish]?=some (.branchLT 4151 4153 (P.address .halt) (P.address .returnSite)):=
 zero_cell P.program (P.address .finish) _ (UniformRecursiveSavingExecution.part_at .finish 0 (by decide))
theorem finish_execution (n B depth:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .finish)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (bound:WordBound B s)(code:P.program.length≤B):
 BoundedRuns P.program n x B s 1 (setPC s (if depth=0 then P.address .halt else P.address .returnSite)):=
 finish_generic P.program (P.address .finish) (P.address .halt) (P.address .returnSite) n B depth x s finish_code
 pc dp one bound (R.start_bound .halt B code) (R.start_bound .returnSite B code)

def Changed (j:ℕ):Prop := SetupChanged j∨S.Changed j
structure Frame (A volume:ℕ)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,¬Changed j→u.natReg j=s.natReg j
 scalarReg:∀j,8≤j→u.scalarReg j=s.scalarReg j
 scalarHeap:∀a,a<A∨A+volume≤a→u.scalarHeap a=s.scalarHeap a
lemma compose_frame {A volume:ℕ}{s t u:State}(a:SetupFrame s t)(b:S.Frame A volume t u)(pc:ℕ):
 Frame A volume s (setPC u pc):=by
 refine ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,?_,?_,?_⟩
 · intro j hj
   exact (b.natReg j (by exact fun h=>hj (Or.inr h))).trans
    (a.natReg j (by exact fun h=>hj (Or.inl h)))
 · intro j hj;exact (b.scalarReg j hj).trans (congrFun a.scalarReg j)
 · intro adr h;exact (b.scalarHeap adr h).trans (congrFun a.scalarHeap adr)

/-- Continuous setup, spectator transform, and finish branch. Only raw parent
headers, the stored data and ordinary bounds enter the proof. -/
theorem suffix_generic (main:Program)(setup spectator finish root child count n B k q m A depth:ℕ)
 (x:Fin n→ℂ)(s:State)(v:Fin count→Fin (2^k)→Scalar)
 (setupCode:BlockAt (setupOps count) main setup)(setupJump:main[setup+5]?=some (.jump spectator))
 (spectatorLink:CodeAt S.program main spectator finish)
 (finishCode:main[finish]?=some (.branchLT 4151 4153 root child))
 (pc:s.pc=setup)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)(dp:s.natReg 4151=depth)
 (data:∀w z,s.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z))
 (axes:q*m≤k)(heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(setupEnd:setup+6≤B)(spectatorEnd:spectator+S.program.length≤B)
 (finishBound:finish≤B)(rootBound:root≤B)(childBound:child≤B)(countBound:count≤B)
 (extent:A+count*2^k≤B)(stride:2^(q*m)*2≤B):∃u,
 BoundedRuns main n x B s (4*(q*m)+count*S.arrayCost k (q*m)+16) u ∧
 u.pc=(if depth=0 then root else child) ∧
 (∀w z,u.scalarHeap (S.arrayBase A k w.val+z.val)=some (S.transformed k (q*m) (v w) z)) ∧
 Frame A (count*2^k) s u ∧ UniformBinaryCStageMachine.Constants u:=by
 have spectatorBound:spectator≤B:=(Nat.le_add_right _ _).trans spectatorEnd
 obtain ⟨t,setupRun,tp,tk,tw,ta,tv,tb,sf⟩:=setup_generic main setup spectator count n B k q m A (2^k)
  x s setupCode setupJump pc one bits base size columns width bound setupEnd spectatorBound countBound axes
 have td:∀w z,t.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z):=by
  intro w z;rw [sf.scalarHeap];exact data w z
 have tc:UniformBinaryCStageMachine.Constants t:=by
  rcases constants with ⟨a,b⟩;exact ⟨by rw [sf.scalarHeap];exact a,by rw [sf.scalarHeap];exact b⟩
 obtain ⟨u,run,up,out,fr,con⟩:=spectator_embedded main spectator finish n B k (q*m) count A x spectatorLink
  t v tp tk tw ta tv tb td axes heapBase tc setupRun.final_bound spectatorEnd finishBound extent stride
 have depthKeep:u.natReg 4151=depth:=
  (fr.natReg _ (by unfold S.Changed UniformBinaryTensorCMachine.Changed;omega)).trans
   ((sf.natReg _ (by unfold SetupChanged;omega)).trans dp)
 have oneKeep:u.natReg 4153=1:=
  (fr.natReg _ (by unfold S.Changed UniformBinaryTensorCMachine.Changed;omega)).trans
   ((sf.natReg _ (by unfold SetupChanged;omega)).trans one)
 have last:=finish_generic main finish root child n B depth x u finishCode up depthKeep oneKeep run.final_bound rootBound childBound
 refine ⟨setPC u (if depth=0 then root else child),?_,rfl,out,compose_frame sf fr _,con⟩
 convert (setupRun.trans run).trans last using 1
 omega

theorem suffix_execution (n B k q m A depth:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=P.address .spectatorSetup)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)(dp:s.natReg 4151=depth)
 (data:∀w z,s.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z))
 (axes:q*m≤k)(heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:P.program.length≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B)(stride:2^(q*m)*2≤B):∃u,
 BoundedRuns P.program n x B s (4*(q*m)+UniformRecursiveSelfCallMachine.W*S.arrayCost k (q*m)+16) u ∧
 u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
 (∀w z,u.scalarHeap (S.arrayBase A k w.val+z.val)=some (S.transformed k (q*m) (v w) z)) ∧
 Frame A (UniformRecursiveSelfCallMachine.W*2^k) s u ∧ UniformBinaryCStageMachine.Constants u:=
 suffix_generic P.program (P.address .spectatorSetup) (P.address .spectator) (P.address .finish)
 (P.address .halt) (P.address .returnSite) UniformRecursiveSelfCallMachine.W n B k q m A depth x s v
 setup_code setup_jump UniformRecursiveSavingProgram.spectator_code finish_code pc one bits base size columns width dp
 data axes heapBase constants bound (R.code_bound .spectatorSetup 6 B rfl code)
 (R.code_bound .spectator S.program.length B (UniformBinarySpectatorCMachine.program_length.symm) code)
 (R.start_bound .finish B code) (R.start_bound .halt B code) (R.start_bound .returnSite B code)
 countBound extent stride

/-- The actual exhausted-tape comparison precedes the suffix. The tape end
is loaded from work-1; no decoded end-register or branch result is assumed. -/
theorem terminal_execution (n B k q m A depth work cursor tapeEnd:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=cursor)(workHeader:s.natReg 4123=work)
 (metadata:s.natHeap (work-1)=some tapeEnd)(expired:tapeEnd≤cursor)
 (one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)(dp:s.natReg 4151=depth)
 (data:∀w z,s.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z))
 (axes:q*m≤k)(heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:P.program.length≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B)(stride:2^(q*m)*2≤B):∃u t,
 BoundedRuns P.program n x B s (4*(q*m)+UniformRecursiveSelfCallMachine.W*S.arrayCost k (q*m)+20) u ∧
 u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
 (∀w z,u.scalarHeap (S.arrayBase A k w.val+z.val)=some (S.transformed k (q*m) (v w) z)) ∧
 UniformRecursiveRecordControl.LoopFrame s t ∧ Frame A (UniformRecursiveSelfCallMachine.W*2^k) t u ∧
 UniformBinaryCStageMachine.Constants u:=by
 obtain ⟨t,head,tp,_,_,lf⟩:=UniformRecursiveRecordControl.loop_execution n B work cursor tapeEnd x s
  pc workHeader ptr metadata bound code
 have entered:t.pc=P.address .spectatorSetup:=by
  simpa only [not_lt.mpr expired,ite_false] using tp
 have keep:∀j,j≠3301→j≠4178→j≠4179→t.natReg j=s.natReg j:=lf.natReg
 have td:∀w z,t.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z):=by
  intro w z;rw [lf.scalarHeap];exact data w z
 have tc:UniformBinaryCStageMachine.Constants t:=by
  rcases constants with ⟨a,b⟩;exact ⟨by rw [lf.scalarHeap];exact a,by rw [lf.scalarHeap];exact b⟩
 obtain ⟨u,last,up,out,fr,con⟩:=suffix_execution n B k q m A depth x t v entered
  ((keep _ (by omega) (by omega) (by omega)).trans one)
  ((keep _ (by omega) (by omega) (by omega)).trans bits)
  ((keep _ (by omega) (by omega) (by omega)).trans base)
  ((keep _ (by omega) (by omega) (by omega)).trans size)
  ((keep _ (by omega) (by omega) (by omega)).trans columns)
  ((keep _ (by omega) (by omega) (by omega)).trans width)
  ((keep _ (by omega) (by omega) (by omega)).trans dp)
  td axes heapBase tc head.final_bound code countBound extent stride
 refine ⟨u,t,?_,up,out,lf,fr,con⟩
 convert head.trans last using 1
 omega

lemma halt_code:P.program[P.address .halt]?=some .halt:=
 zero_cell P.program (P.address .halt) _ (UniformRecursiveSavingExecution.part_at .halt 0 (by decide))
lemma halt_generic (main:Program)(loc n B:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:main[loc]?=some .halt)(pc:s.pc=loc)(bound:WordBound B s):BoundedExecution main n x B s 1 s:=
 .halt bound (by simp only [step,pc,atCode])

lemma execution_plus_one (main:Program)(n B a b:ℕ)(x:Fin n→ℂ)(s u:State)
 (run:BoundedRuns main n x B s (a+b+20) u)(halt:BoundedExecution main n x B u 1 u):
 BoundedExecution main n x B s (a+b+21) u:=by
 convert run.executes halt using 1

/-- The root terminal path includes the actual halt instruction and all
earlier integer, branch and spectator operations. -/
theorem root_terminal_execution (n B k q m A work cursor tapeEnd:ℕ)(x:Fin n→ℂ)(s:State)
 (v:Fin UniformRecursiveSelfCallMachine.W→Fin (2^k)→Scalar)
 (pc:s.pc=P.address .loop)(ptr:s.natReg 2850=cursor)(workHeader:s.natReg 4123=work)
 (metadata:s.natHeap (work-1)=some tapeEnd)(expired:tapeEnd≤cursor)
 (one:s.natReg 4153=1)(bits:s.natReg 4120=k)(base:s.natReg 4121=A)
 (size:s.natReg 4122=2^k)(columns:s.natReg 4060=q)(width:s.natReg 4061=m)(dp:s.natReg 4151=0)
 (data:∀w z,s.scalarHeap (S.arrayBase A k w.val+z.val)=some (v w z))
 (axes:q*m≤k)(heapBase:3≤A)(constants:UniformBinaryCStageMachine.Constants s)
 (bound:WordBound B s)(code:P.program.length≤B)(countBound:UniformRecursiveSelfCallMachine.W≤B)
 (extent:A+UniformRecursiveSelfCallMachine.W*2^k≤B)(stride:2^(q*m)*2≤B):∃u t,
 BoundedExecution P.program n x B s (4*(q*m)+UniformRecursiveSelfCallMachine.W*S.arrayCost k (q*m)+21) u ∧
 u.pc=P.address .halt ∧
 (∀w z,u.scalarHeap (S.arrayBase A k w.val+z.val)=some (S.transformed k (q*m) (v w) z)) ∧
 UniformRecursiveRecordControl.LoopFrame s t ∧ Frame A (UniformRecursiveSelfCallMachine.W*2^k) t u ∧
 UniformBinaryCStageMachine.Constants u:=by
 obtain ⟨u,t,run,up,out,lf,fr,con⟩:=terminal_execution n B k q m A 0 work cursor tapeEnd x s v
  pc ptr workHeader metadata expired one bits base size columns width dp data axes heapBase constants bound code countBound extent stride
 have stop:u.pc=P.address .halt:=by simpa only [ite_true] using up
 have halt:=halt_generic P.program (P.address .halt) n B x u halt_code stop run.final_bound
 refine ⟨u,t,?_,stop,out,lf,fr,con⟩
 exact execution_plus_one P.program n B (4*(q*m)) (UniformRecursiveSelfCallMachine.W*S.arrayCost k (q*m)) x s u run halt

end
end ExactFourierCircuits.UniformRecursiveSpectatorFinish
