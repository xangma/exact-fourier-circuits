import UniformBlockXorMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualAddressToggleMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

/-- One actual image-bank toggle. It reads the image from the physical heap;
XOR is implemented by the frozen table lookup loop, never by a new opcode. -/
def head : List Op := [.literal 4006 1,.binary .add 4007 4001 4002,
 .load 3351 4007,.binary .mul 3350 4000 4006,.binary .mul 3352 4003 4006,
 .binary .mul 3353 4004 4006,.binary .mul 3354 4005 4006]
def tail : List Op := [.binary .mul 4000 3357 4006]
def program : Program := head.map Op.code++
 UniformBlockXorMachine.program.map (relocate 7 29)++tail.map Op.code++[.halt]
theorem program_length : program.length=31 := rfl
theorem head_code : BlockAt head program 0 := by
 intro i hi;change i<7 at hi;interval_cases i <;> rfl
theorem xor_code : CodeAt UniformBlockXorMachine.program program 7 29 := by
 intro i hi;change i<22 at hi;interval_cases i <;> rfl
theorem tail_code : BlockAt tail program 29 := by
 intro i hi;change i<1 at hi;interval_cases i;rfl
theorem halt_at : program[30]?=some .halt := rfl

def Changed (r : ℕ) : Prop := UniformBlockXorMachine.Changed r ∨
 r=3352 ∨ r=3353 ∨ r=3354 ∨ r=4000 ∨ r=4006 ∨ r=4007
structure Frame (s u : State) : Prop where
 natHeap : u.natHeap=s.natHeap
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r→u.natReg r=s.natReg r

theorem execution (n B q w a imageBase axis image table : ℕ)
 (x : Fin n→ℂ) (s : State) (pc : s.pc=0)
 (ha : s.natReg 4000=a) (hb : s.natReg 4001=imageBase)
 (hi : s.natReg 4002=axis) (hw : s.natReg 4003=w)
 (hn : s.natReg 4004=2^q) (ht : s.natReg 4005=table)
 (physicalImage : s.natHeap (imageBase+axis)=some image)
 (entries : UniformXorTableMachine.Entries q table (2^q*2^q) s)
 (smallA : a<2^(q*w)) (smallImage : image<2^(q*w))
 (bound : WordBound B s) (code : 31≤B)
 (imageExtent : imageBase+axis≤B) (tableExtent : table+2^q*2^q≤B)
 (volume : 2^(q*w)≤B) : ∃u,
 BoundedExecution program n x B s (17*w+15) u ∧
 u.pc=30 ∧ u.natReg 4000=a^^^image ∧ Frame s u := by
 have wb : w≤B := by have h:=bound.2.1 4003;rw [hw] at h;exact h
 have nb : 2^q≤B := by
  have pos:=Nat.two_pow_pos q
  have le:2^q≤2^q*2^q:=Nat.le_mul_of_pos_right _ pos
  omega
 have safe : readable head s ∧ peak head s≤B := by
  simp [head,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   ha,hb,hi,hw,hn,ht,physicalImage]
  omega
 have hr:=block_runs head program 0 n B x s head_code pc bound
  (by change 7≤B;omega) safe.1 safe.2
 let ready:=applyBlock head s
 let child:State:={ready with pc:=0}
 have cb : WordBound B child:=changePC_bound B ready 0 hr.final_bound (by omega)
 have readyPC : ready.pc=7 := by
  simp [ready,head,applyBlock,Op.apply,writeNat,next,pc]
 have inputA : child.natReg 3350=a := by
  simp [child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,ha,hb,hi,physicalImage]
 have inputImage : child.natReg 3351=image := by
  simp [child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,hb,hi,physicalImage]
 have inputWidth : child.natReg 3352=w := by
  simp [child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,hw]
 have inputSize : child.natReg 3353=2^q := by
  simp [child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,hn]
 have inputTable : child.natReg 3354=table := by
  simp [child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,ht]
 obtain ⟨v,run,pv,val,fv⟩:=UniformBlockXorMachine.execution q w table a image B n x child
  rfl inputA inputImage inputWidth inputSize inputTable smallA smallImage entries cb
  (by omega) tableExtent volume
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed xor_code
  (by change 29≤B;omega) (by omega) run
 have placedEntry : UniformAssembly.placed 7 child=ready := by
  change {ready with pc:=7}=ready
  rw [←readyPC]
 rw [placedEntry] at placedRun
 let ret:State:={v with pc:=29}
 have one : ret.natReg 4006=1 := by
  have k:=fv.natReg 4006 (by simp [UniformBlockXorMachine.Changed])
  simpa [ret,child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next] using k
 have value : ret.natReg 3357=a^^^image := val
 have safeTail : readable tail ret ∧ peak tail ret≤B := by
  simp [tail,readable,peak,Op.readable,Op.peak,evalNat,one,value]
  exact (Nat.xor_lt_two_pow smallA smallImage).le.trans volume
 have tr:=block_runs tail program 29 n B x ret tail_code rfl placedRun.final_bound
  (by change 30≤B;omega) safeTail.1 safeTail.2
 let u:=applyBlock tail ret
 have up : u.pc=30 := by simp [u,tail,applyBlock,Op.apply,writeNat,next,ret]
 have halt : BoundedExecution program n x B u 1 u:=.halt tr.final_bound
  (by simp [step,up,halt_at])
 refine ⟨u,?_,up,?_,?_⟩
 · convert hr.executes (placedRun.trans tr |>.executes halt) using 1
   change 17*w+15=7+(17*w+6+1)+1
   omega
 · simp [u,tail,applyBlock,Op.apply,evalNat,writeNat,next,one,value]
 · refine ⟨fv.natHeap,fv.scalarHeap,fv.scalarReg,fv.outputs,fv.roots,?_⟩
   intro r keep
   have hk : ¬UniformBlockXorMachine.Changed r := by unfold Changed at keep;tauto
   have h0 : r≠4000 := by unfold Changed at keep;tauto
   have h6 : r≠4006 := by unfold Changed at keep;tauto
   have h7 : r≠4007 := by unfold Changed at keep;tauto
   have h2 : r≠3352 := by unfold Changed at keep;tauto
   have h3 : r≠3353 := by unfold Changed at keep;tauto
   have h4 : r≠3354 := by unfold Changed at keep;tauto
   have outside:=fv.natReg r hk
   simpa [u,ret,tail,child,ready,head,applyBlock,Op.apply,evalNat,writeNat,next,
    h0,h6,h7,h2,h3,h4,show r≠3350 by unfold UniformBlockXorMachine.Changed at hk;omega,
    show r≠3351 by unfold UniformBlockXorMachine.Changed at hk;omega] using outside
end
end ExactFourierCircuits.UniformResidualAddressToggleMachine
