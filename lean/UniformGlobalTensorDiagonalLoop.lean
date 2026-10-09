import UniformGlobalTensorDiagonalMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalTensorDiagonalMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (product)
noncomputable section
lemma Banks.transfer {W i:ℕ} {g:Geometry W} {axes:List Axis} {s u:State}
 (length:g.ell=axes.length) (h:Banks g axes s)
 (nat:∀q,q < g.natStack ∨g.natStack+3*g.ell ≤ q→u.natHeap q=s.natHeap q)
 (scalar:∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination+i*g.volume ∨g.destination+(i+1)*g.volume ≤ q)→
  u.scalarHeap q=s.scalarHeap q):Banks g axes u:=by
 let zero:Fin W:=⟨0,g.positive⟩
 have old:=h.forRole zero
 have next:=banks_transfer axes 0 (g.layout zero) s u (by simp[Geometry.layout,length]) old
  (fun q hq=>nat q (Or.inl hq))
  (fun q hq=>by
   change q < g.scalarStack at hq
   exact scalar q (Or.inl hq) (Or.inl (by have:=g.destinationAbove;omega)))
 exact ⟨next.rows,next.permutation,next.coefficient,next.permutationBelow,next.coefficientBelow⟩
lemma Source.transfer {W i:ℕ} {g:Geometry W} {v:ℕ→ℕ→Scalar} {s u:State}
 (h:Source g v s)
 (scalar:∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination+i*g.volume ∨g.destination+(i+1)*g.volume ≤ q)→
  u.scalarHeap q=s.scalarHeap q):Source g v u:=by
 intro r hr j hj
 have source:g.source+r*g.volume+j < g.scalarStack:=by have:=g.sourceBelow;nlinarith
 have destination:g.source+r*g.volume+j < g.destination+i*g.volume:=by
  have:=g.destinationAbove;omega
 exact (scalar _ (Or.inl source) (Or.inl destination)).trans (h r hr j hj)
def Filled {W:ℕ} (g:Geometry W) (axes:List Axis) (v:ℕ→ℕ→Scalar) (done:ℕ) (s:State):Prop:=
 ∀i,i < done→RoleOutput g axes v i s
lemma Filled.step {W i:ℕ} {g:Geometry W} {axes:List Axis} {v:ℕ→ℕ→Scalar} {s u:State}
 (volume:g.volume=(radices axes).prod) (old:Filled g axes v i s)
 (fresh:RoleOutput g axes v i u)
 (scalar:∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination+i*g.volume ∨g.destination+(i+1)*g.volume ≤ q)→
  u.scalarHeap q=s.scalarHeap q):Filled g axes v (i+1) u:=by
 intro r hr
 by_cases equal:r=i
 · subst r;exact fresh
 · have before:r < i:=by omega
   intro j
   have jj:(tensorPermutation axes j).val < g.volume:=by rw[volume];exact (tensorPermutation axes j).isLt
   have outside:g.destination+r*g.volume+(tensorPermutation axes j).val < g.destination+i*g.volume:=by nlinarith
   exact (scalar _ (Or.inr (by have:=g.destinationAbove;omega)) (Or.inl outside)).trans (old r before j)

/-- Induction is over actual remaining role visits, not a callback evaluator.
The same81 instructions execute every recursive proof case. -/
lemma loop (remaining:ℕ) {W n:ℕ} (g:Geometry W) (axes:List Axis) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ)
 (length:g.ell=axes.length) (volume:g.volume=(radices axes).prod):
 ∀i s,W=i+remaining→s.pc=4→WordBound g.B s→Cursor g i s→Banks g axes s→Source g v s→
 Filled g axes v i s→
 ∃u,BoundedExecution (programFor W) n x g.B s (remaining*(treeCost (radices axes)+20)+2) u ∧
 u.pc=80 ∧Filled g axes v W u ∧Frame s u ∧
 (∀q,q < g.natStack ∨g.natStack+3*g.ell ≤ q→u.natHeap q=s.natHeap q) ∧
 (∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination ∨g.destination+W*g.volume ≤ q)→u.scalarHeap q=s.scalarHeap q):=by
 induction remaining with
 | zero=>
   intro i s last pc wb cursor banks source filled
   have equal:i=W:=by omega
   let u:=setPC s 80
   have ub:=changePC_bound g.B s 80 wb (by have:=g.code;omega)
   have branch:BoundedRuns (programFor W) n x g.B s 1 u:=
    .next wb (by simp[step,pc,branch_at,cursor.index,cursor.roles,equal,u,setPC]) (.refl ub)
   have stop:BoundedExecution (programFor W) n x g.B u 1 u:=
    .halt ub (by simp[step,u,setPC,halt_at])
   refine ⟨u,by simpa using branch.executes stop,rfl,?_,Frame.refl s,fun _ _=>rfl,fun _ _ _=>rfl⟩
   simpa only[Filled,RoleOutput,u,setPC,equal] using filled
 | succ remaining ih=>
   intro i s count pc wb cursor banks source filled
   have hi:i < W:=by omega
   obtain ⟨t,first,tp,result,next,frame,nat,scalar⟩:=iteration g axes v x s ⟨i,hi⟩ cursor length volume banks source pc wb
   have bt:Banks g axes t:=banks.transfer length nat scalar
   have st:Source g v t:=source.transfer scalar
   have ft:Filled g axes v (i+1) t:=filled.step volume result scalar
   obtain ⟨u,rest,up,done,frameU,natU,scalarU⟩:=ih (i+1) t (by omega) tp first.final_bound next bt st ft
   refine ⟨u,?_,up,done,frame.trans frameU,fun q hq=>(natU q hq).trans (nat q hq),?_⟩
   · convert first.executes rest using 1
     simp only[Nat.succ_mul]
     omega
   · intro q hs hd
     have current:q < g.destination+i*g.volume ∨g.destination+(i+1)*g.volume ≤ q:=by
      rcases hd with before|after
      · exact Or.inl (by omega)
      · exact Or.inr (by nlinarith)
     exact (scalarU q hs hd).trans (scalar q hs current)

lemma boot_cursor {W:ℕ} {g:Geometry W} {s:State} (h:Header g s):Cursor g 0 (applyBlock (boot W) s):=by
 constructor
 · constructor <;>simp[boot,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,
    h.axes,h.rows,h.natStack,h.scalarStack]
 · simp[boot,applyBlock,Op.apply,writeNat,next]
 · simp[boot,applyBlock,Op.apply,writeNat,next]
 · simp[boot,applyBlock,Op.apply,writeNat,next]
 · simp[boot,applyBlock,Op.apply,writeNat,next]
lemma boot_frame (W:ℕ) (s:State):Frame s (applyBlock (boot W) s):=by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_⟩
 intro q h0 h1 h2
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]

/-- Fully charged simultaneous role traversal from physical prepared axis
banks and arbitrary present tagged input. It is a monomial/diagonal stage,
not an implementation of the six recursive C-transform calls. -/
theorem execution {W n:ℕ} (g:Geometry W) (axes:List Axis) (v:ℕ→ℕ→Scalar) (x:Fin n→ℂ) (s:State)
 (length:g.ell=axes.length) (volume:g.volume=(radices axes).prod)
 (h:Header g s) (banks:Banks g axes s) (source:Source g v s) (pc:s.pc=0) (wb:WordBound g.B s):
 ∃u,BoundedExecution (programFor W) n x g.B s (W*(treeCost (radices axes)+20)+6) u ∧
 u.pc=80 ∧Filled g axes v W u ∧Frame s u ∧
 (∀q,q < g.natStack ∨g.natStack+3*g.ell ≤ q→u.natHeap q=s.natHeap q) ∧
 (∀q,(q < g.scalarStack ∨g.scalarStack+g.ell ≤ q)→
  (q < g.destination ∨g.destination+W*g.volume ≤ q)→u.scalarHeap q=s.scalarHeap q):=by
 have safe:readable (boot W) s ∧peak (boot W) s ≤ g.B:=by
  simp[boot,readable,peak,Op.readable,Op.peak]
  have:=g.roles;have:=g.code;omega
 have start:=block_runs (boot W) (programFor W) 0 n g.B x s (boot_code W) pc wb
  (by have:=g.code;change 0+4 ≤ g.B;omega) safe.1 safe.2
 let b:=applyBlock (boot W) s
 have bp:b.pc=4:=by rw[applyBlock_pc,pc];rfl
 have bn:Banks g axes b:=banks.transfer (i:=0) length (fun _ _=>rfl) (fun _ _ _=>rfl)
 have bs:Source g v b:=source.transfer (i:=0) (fun _ _ _=>rfl)
 have empty:Filled g axes v 0 b:=by intro i hi;omega
 obtain ⟨u,rest,up,done,frame,nat,scalar⟩:=loop W g axes v x length volume 0 b (by omega) bp start.final_bound
  (boot_cursor h) bn bs empty
 refine ⟨u,?_,up,done,(boot_frame W s).trans frame,nat,scalar⟩
 convert start.executes rest using 1
 change W*(treeCost (radices axes)+20)+6=4+(W*(treeCost (radices axes)+20)+2)
 omega

lemma tensorPermutation_identity (axes:List Axis)
 (h:∀a∈axes,∀j,a.permutation j=j):∀j,tensorPermutation axes j=j:=by
 induction axes with
 | nil=>intro j;rfl
 | cons a axes ih=>
   intro j
   let pair:Fin a.radix×Fin (radices axes).prod:=finProdFinEquiv.symm j
   have first:a.permutation pair.1=pair.1:=h a (by simp) pair.1
   have second:tensorPermutation axes pair.2=pair.2:=ih
    (by intro b hb;exact h b (by simp[hb])) pair.2
   have equal:(a.permutation pair.1,tensorPermutation axes pair.2)=pair:=Prod.ext first second
   exact (congrArg finProdFinEquiv equal).trans (finProdFinEquiv.apply_symm_apply j)

theorem diagonal_values {W:ℕ} {g:Geometry W} {axes:List Axis} {v:ℕ→ℕ→Scalar} {u:State}
 (identity:∀a∈axes,∀j,a.permutation j=j) (done:Filled g axes v W u):
 ∀i,i < W→∀j:Fin (radices axes).prod,
 u.scalarHeap (g.destination+i*g.volume+j.val)=some (product (tensorCoefficient axes j) (v i j.val)):=by
 intro i hi j
 simpa only[tensorPermutation_identity axes identity j] using done i hi j
lemma instruction_bound_radices_two (W:ℕ) (axes:List Axis) (h:∀a∈axes,2 ≤ a.radix):
 W*(treeCost (radices axes)+20)+6 ≤ 122*W*(radices axes).prod+6:=by
 have b:=UniformTensorMonomialMachine.instruction_bound_radices_two axes h
 have positive:=UniformTensorMonomialMachine.volume_positive axes
 nlinarith
end
end ExactFourierCircuits.UniformGlobalTensorDiagonalMachine
