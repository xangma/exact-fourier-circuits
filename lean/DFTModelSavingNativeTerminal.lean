import DFTModelSavingNativeSequence
import DFTModelSavingBinarySuffixSemantics
import UniformRecursiveSpectatorFinish

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingNativeTerminal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformBinaryTensorCoordinates
open UniformFixedNetworkShearChildMachine (Present)
open UniformRecursiveResidualEdge (Parent)
open DFTModelClockControl DFTModelAffine DFTModelAdmissibilityControl
open DFTModelRecursiveScalarSource (paired)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
noncomputable section
attribute [local irreducible] P.program DFTModelSavingBinarySuffix.program

structure Frame (A V : ℕ) (s u : State) : Prop where
  natHeap : u.natHeap=s.natHeap
  scalarHeap : ∀z,z<A∨A+W*V≤z→u.scalarHeap z=s.scalarHeap z
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  stack : u.natReg 4150=s.natReg 4150
  depth : u.natReg 4151=s.natReg 4151

lemma frame {A k : ℕ}{s t u : State}
    (head : UniformRecursiveRecordControl.LoopFrame s t)
    (tail : UniformRecursiveSpectatorFinish.Frame A (W*2^k) t u) : Frame A (2^k) s u := by
  refine ⟨tail.natHeap.trans head.natHeap,?_,tail.outputs.trans head.outputs,tail.roots.trans head.roots,?_,?_⟩
  · intro z away
    exact (tail.scalarHeap z away).trans (congrFun head.scalarHeap z)
  · exact (tail.natReg _ (by
      unfold UniformRecursiveSpectatorFinish.Changed UniformRecursiveSpectatorFinish.SetupChanged
        UniformBinarySpectatorCMachine.Changed UniformBinaryTensorCMachine.Changed
      omega)).trans (head.natReg _ (by omega) (by omega) (by omega))
  · exact (tail.natReg _ (by
      unfold UniformRecursiveSpectatorFinish.Changed UniformRecursiveSpectatorFinish.SetupChanged
        UniformBinarySpectatorCMachine.Changed UniformBinaryTensorCMachine.Changed
      omega)).trans (head.natReg _ (by omega) (by omega) (by omega))

/-- After the last real printed record, both source states execute the actual
exhausted-loop comparison, charged spectator setup, native69 and depth branch.
The one typed suffix returns exactly their paired physical Scalars. -/
theorem execution (n B q rest A F cursor tapeEnd stack depth : ℕ) (x : Fin n→ℂ)
    (s s0 : State) (f f0 : Fin W→Fin (2^(q*m+rest))→Scalar)
    (same : StateMatch s s0) (pc : s.pc=P.address .loop)
    (parent : Parent (q*m+rest) q A F cursor rest stack depth s)
    (metadata : s.natHeap (F-1)=some tapeEnd) (expired : tapeEnd≤cursor)
    (data : Present A W (2^(q*m+rest)) f s) (data0 : Present A W (2^(q*m+rest)) f0 s0)
    (positive : 1≤q) (base : 3≤A) (extent : A+W*2^(q*m+rest)≤B)
    (constants : UniformBinaryCStageMachine.Constants s) (bound : WordBound B s)
    (code : P.program.length≤B) :
    ∃u u0,
      BoundedRuns P.program n x B s
        (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) u ∧
      BoundedRuns P.program n (fun _=>0) B s0
        (4*(q*m)+W*UniformBinarySpectatorCMachine.arrayCost (q*m+rest) (q*m)+20) u0 ∧
      StateMatch u u0 ∧
      u.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
      u0.pc=(if depth=0 then P.address .halt else P.address .returnSite) ∧
      Present A W (2^(q*m+rest))
        (fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (f i)) u ∧
      Present A W (2^(q*m+rest))
        (fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (f0 i)) u0 ∧
      Frame A (2^(q*m+rest)) s u ∧Frame A (2^(q*m+rest)) s0 u0 ∧
      UniformBinaryCStageMachine.Constants u ∧UniformBinaryCStageMachine.Constants u0 ∧
      (run DFTModelSavingBinarySuffix.program
        (q*m,((q*m+rest,Complex.I),paired f f0))).val=
        ((q*m+rest,Complex.I),paired
          (fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (f i))
          (fun i=>UniformBinarySpectatorCMachine.transformed (q*m+rest) (q*m) (f0 i))) := by
  have width:s.natReg 4061=m:=by
    rw [parent.width,Nat.add_sub_cancel_right]
    exact Nat.mul_div_right m (by omega)
  have countBound:W≤B:=by
    have h:=Nat.mul_le_mul_left W (show 1≤2^(q*m+rest) from Nat.two_pow_pos _)
    simp only [Nat.mul_one] at h
    omega
  have countTwo:2≤W:=by
    change 2≤2^ExplicitSeedBudget.roleBits
    exact Nat.le_trans (by decide : 2≤2^1)
      (Nat.pow_le_pow_right (by decide) (by norm_num [ExplicitSeedBudget.roleBits]))
  have stride:2^(q*m)*2≤B:=UniformBinarySpectatorCMachine.stride_bound (by omega) countTwo extent
  obtain ⟨u,t,run,up,out,lf,fr,con⟩:=UniformRecursiveSpectatorFinish.terminal_execution n B
    (q*m+rest) q m A depth F cursor tapeEnd x s f pc parent.cursor parent.frontier metadata expired
    parent.one parent.bits parent.original parent.volume parent.columns width parent.depth data
    (by omega) base constants bound code countBound extent stride
  have parent0:=DFTModelSavingNativeExchange.parent_match same parent
  obtain ⟨u0,t0,run0,up0,out0,lf0,fr0,con0⟩:=UniformRecursiveSpectatorFinish.terminal_execution n B
    (q*m+rest) q m A depth F cursor tapeEnd (fun _=>0) s0 f0 (same.pc.trans pc)
    parent0.cursor parent0.frontier (by rw [same.natHeap];exact metadata) expired
    parent0.one parent0.bits parent0.original parent0.volume parent0.columns
    (by rw [same.natReg];exact width) parent0.depth data0
    (by omega) base (DFTModelSavingNativeExchange.constants_match same constants) (same.wordBound bound)
    code countBound extent stride
  exact ⟨u,u0,run,run0,DFTModelSavingNativeControl.paired_runs run run0 same,up,up0,out,out0,
    frame lf fr,frame lf0 fr0,con,con0,
    DFTModelSavingBinarySuffix.program_paired f f0 (q*m) (by omega)⟩

end
end ExactFourierCircuits.DFTModelSavingNativeTerminal
