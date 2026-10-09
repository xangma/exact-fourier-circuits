import UniformRecursivePaddingUnitEdge
import UniformRecursiveResidualControlJoin
import UniformFixedNetworkShearChildMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingFrames
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
namespace P
export UniformRecursiveSavingProgram (program address)
end P
namespace C
export UniformRecursivePaddingControl (Frame Changed)
end C
noncomputable section

structure Parent (k q A F r stack depth:ℕ)(s:State):Prop where
 nativeBase:s.natReg 3300=A
 original:s.natReg 4121=A
 bits:s.natReg 4120=k
 volume:s.natReg 4122=2^k
 frontier:s.natReg 4123=F
 rest:s.natReg 4127=r
 stack:s.natReg 4150=stack
 depth:s.natReg 4151=depth
 one:s.natReg 4153=1
 nativeBits:s.natReg 5300=k
 nativeRest:s.natReg 5301=r
 table:s.natReg 3389=F+3*2^k
 columns:s.natReg 4060=q
 width:s.natReg 4061=(k-r)/q

structure Metadata (F U saved role last:ℕ)(s:State):Prop where
 mode:s.natHeap (F-6)=some 1
 saved:s.natHeap (F-5)=some saved
 current:s.natHeap (F-4)=some role
 endpoint:s.natHeap (F-3)=some last
 unit:s.natHeap (F-2)=some U

lemma Metadata.transport {F U saved role last:ℕ}{s u:State}
 (h:Metadata F U saved role last s)
 (same:∀z,z∈[F-6,F-5,F-4,F-3,F-2]→u.natHeap z=s.natHeap z):Metadata F U saved role last u:=
 ⟨(same _ (by simp)).trans h.mode,(same _ (by simp)).trans h.saved,
  (same _ (by simp)).trans h.current,(same _ (by simp)).trans h.endpoint,(same _ (by simp)).trans h.unit⟩

lemma Parent.of_control {k q A F T r stack depth index dimension finish flag:ℕ}{s:State}
 (h:UniformRecursiveResidualDirection.Control k q A F T r stack depth index dimension finish flag s):
 Parent k q A F r stack depth s:=
 ⟨h.nativeBase,h.original,h.bits,h.volume,h.frontier,h.rest,h.stack,h.depth,h.one,
  h.nativeBits,h.nativeRest,h.table,h.columns,h.width⟩

lemma Parent.padding {k q A F r stack depth:ℕ}{s u:State}{cells:List ℕ}
 (h:Parent k q A F r stack depth s)(f:C.Frame cells s u)
 (bits:u.natReg 5300=k):Parent k q A F r stack depth u:=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,bits,?_,?_,?_,?_⟩
 all_goals first
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.nativeBase
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.original
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.bits
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.volume
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.frontier
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.rest
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.stack
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.depth
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.one
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.nativeRest
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.table
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.columns
 | exact (f.natReg _ (by unfold C.Changed;omega)).trans h.width

lemma Parent.residual {k q A F r stack depth:ℕ}{s u:State}
 (h:Parent k q A F r stack depth s)
 (f:UniformRecursiveResidualControl.Frame F s u):Parent k q A F r stack depth u:=by
 constructor
 all_goals first
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.nativeBase
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.original
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.bits
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.volume
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.frontier
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.rest
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.stack
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.depth
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.one
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.nativeBits
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.nativeRest
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.table
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.columns
 | exact (f.natReg _ (by unfold UniformRecursiveResidualControl.Changed;omega)).trans h.width

lemma runs_unique {main:Program}{n B t:ℕ}{x:Fin n→ℂ}{s u v:State}
 (a:BoundedRuns main n x B s t u)(b:BoundedRuns main n x B s t v):u=v:=by
 induction a generalizing v with
 | refl=>cases b;rfl
 | next hb hs tail ih=>
  cases b with
  | next _ hs' tail'=>
   rw [hs] at hs'
   cases hs'
   exact ih tail'

def keeps (j:ℕ):Op→Prop
 | .literal d _=>d≠j
 | .binary _ d _ _=>d≠j
 | .load d _=>d≠j
 | .store _ _=>True
lemma block_register (ops:List Op)(s:State)(j:ℕ)(h:∀o∈ops,keeps j o):
 (applyBlock ops s).natReg j=s.natReg j:=by
 induction ops generalizing s with
 | nil=>rfl
 | cons o ops ih=>
  rw [show applyBlock (o::ops) s=applyBlock ops (o.apply s) from rfl,
   ih _ (fun a ha=>h a (by simp [ha]))]
  have ho:=h o (by simp)
  cases o <;> simp_all [keeps,Op.apply,writeNat,next,evalNat,ne_comm]

lemma block_jump_register (main:Program)(start ret n B j:ℕ)(ops:List Op)(x:Fin n→ℂ)
 (s u:State)(link:BlockAt ops main start)(jump:main[start+ops.length]?=some (.jump ret))
 (pc:s.pc=start)(bound:WordBound B s)(extent:start+ops.length+1≤B)(returnBound:ret≤B)
 (safe:readable ops s∧peak ops s≤B)(keep:∀o∈ops,keeps j o)
 (run:BoundedRuns main n x B s (ops.length+1) u):u.natReg j=s.natReg j:=by
 have exactRun:=UniformRecursivePaddingControl.run_jump main start ret n B ops x s link jump pc bound extent returnBound safe
 have eq:=runs_unique run exactRun
 rw [eq]
 exact block_register ops s j keep

lemma block_branch_register (main:Program)(start yes no left right n B j:ℕ)(ops:List Op)(x:Fin n→ℂ)
 (s u:State)(link:BlockAt ops main start)
 (branch:main[start+ops.length]?=some (.branchLT left right yes no))
 (pc:s.pc=start)(bound:WordBound B s)(extent:start+ops.length+1≤B)(yb:yes≤B)(nb:no≤B)
 (safe:readable ops s∧peak ops s≤B)(keep:∀o∈ops,keeps j o)
 (run:BoundedRuns main n x B s (ops.length+1) u):u.natReg j=s.natReg j:=by
 have first:=block_runs ops main start n B x s link pc bound (by omega) safe.1 safe.2
 have tp:(applyBlock ops s).pc=start+ops.length:=by rw [UniformRecursiveNodePreparation.block_pc,pc]
 have last:=UniformRecursiveRecordControl.branch_control main (start+ops.length) yes no n B left right x
  (applyBlock ops s) branch tp first.final_bound yb nb
 have eq:=runs_unique run (first.trans last)
 rw [eq]
 exact block_register ops s j keep

lemma block_jump_register_len (main:Program)(start ret n B j len:ℕ)(ops:List Op)(length:ops.length=len)(x:Fin n→ℂ)
 (s u:State)(link:BlockAt ops main start)(jump:main[start+len]?=some (.jump ret))
 (pc:s.pc=start)(bound:WordBound B s)(extent:start+(len+1)≤B)(returnBound:ret≤B)
 (safe:readable ops s∧peak ops s≤B)(keep:∀o∈ops,keeps j o)
 (run:BoundedRuns main n x B s (len+1) u):u.natReg j=s.natReg j:=by
 subst len
 exact block_jump_register main start ret n B j ops x s u link jump pc bound (by omega) returnBound safe keep run

lemma block_branch_register_len (main:Program)(start yes no left right n B j len:ℕ)(ops:List Op)(length:ops.length=len)(x:Fin n→ℂ)
 (s u:State)(link:BlockAt ops main start)(branch:main[start+len]?=some (.branchLT left right yes no))
 (pc:s.pc=start)(bound:WordBound B s)(extent:start+(len+1)≤B)(yb:yes≤B)(nb:no≤B)
 (safe:readable ops s∧peak ops s≤B)(keep:∀o∈ops,keeps j o)
 (run:BoundedRuns main n x B s (len+1) u):u.natReg j=s.natReg j:=by
 subst len
 exact block_branch_register main start yes no left right n B j ops x s u link branch pc bound (by omega) yb nb safe keep run
end
end ExactFourierCircuits.UniformRecursivePaddingFrames
