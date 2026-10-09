import UniformDirectLeafCacheExecution
import UniformDirectLeafCalendarSemanticBranch
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheSemanticExecution
open UniformMachine UniformTensorMonomialMachine
open UniformDirectLeafCacheReader UniformDirectLeafCacheSetup
open UniformTransposeDescriptorMachine (Record)
noncomputable section

open UniformDirectLeafCacheExecution (Layout Result)
/-- Semantic refinement of the frozen produced result. The singleton pair
is the actual descriptor destination/source, rather than an arbitrary pair. -/
structure SemanticResult (c:Config) (r:ℕ) (q:Record) (mu:ℂ) (positive:2≤r) (s:State)
 extends Result c r q mu positive s where
 endpoints : ∀i, (edges i).left=q.dest ∧(edges i).right=q.source
 unused : q.kind=1→∀(lane:Fin 9)(i:Fin r),i.val≠q.dest→i.val≠q.source→
  s.scalarHeap (c.pool+lane.val*r+i.val)=some (UniformPairMachine.prepared 1)

/-- One actual82 descriptor → actual pool, permutation, block widths and
mixed-duration event. The genuine retained-source specialization follows below.
There is no supplied generated edge table, factor pool, or helper header. -/
theorem execution {c:Config} {r A C n B:ℕ} {q:Record} (mu:ℂ) (x:Fin n→ℂ) (s:State)
 (args:Args c s) (src:Source c r A C q s)
 (values:UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) s)
 (constants:UniformHadamardPairMachine.Constants s)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q) (legal:UniformDirectLeafCacheSource.Legal q)
 (positive:2≤r) (layout:Layout c r B)
 (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (coefficient:q.coefficient<c.pool)
 (conjugateCoefficient:C+3*r+(q.coefficient-(A+3*r))<c.pool)
 (code:264≤B) (pc:s.pc=0) (wb:WordBound B s) : ∃u,
 BoundedExecution UniformDirectLeafCacheProgram.program n x B s
  (62*r+(if q.kind=0 then 103 else 199)) u ∧u.pc=263 ∧
 Nonempty (SemanticResult c r q mu positive u) ∧
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) ∧
 (∀j,j<c.permutation→(j<c.rows∨c.rows+3≤j)→u.natHeap j=s.natHeap j) ∧
 (∀j,c.entry+7≤j→u.natHeap j=s.natHeap j) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders := by
 have lRows:=layout.rows
 have lP:=layout.permutation
 have lW:=layout.widths
 have lU:=layout.markers
 have lA:=layout.axis
 have lD:=layout.entry
 have lPool:=layout.pool
 have rowBound:c.rows+3≤B:=by
  have:=layout.rows
  have:=layout.permutation
  have:=layout.widths
  have:=layout.markers
  have:=layout.axis
  have:=layout.entry
  omega
 obtain ⟨b,boot,bp,ready,ones,source,cc,out0,nh0,outs0,roots0⟩:=UniformDirectLeafCacheBootstrap.execution
  mu x s args src values constants range descriptor directory conjugateDirectory original conjugate
  rowBound layout.pool layout.constants coefficient conjugateCoefficient code pc wb
 rcases legal with ⟨kind,_eq⟩|⟨kind,neq⟩
 · obtain ⟨v,branch,vp,table,head,nh1,outs1,roots1,out1⟩:=UniformDirectLeafCacheBranches.scale_execution
    mu x b ready source.1 ones kind range.1 layout.pool (by omega) code bp boot.final_bound
   let E:Fin 0→UniformColoring.Edge:=Fin.elim0
   have hm:UniformMatchingAxisTableMachine.Matching E:=by intro i;exact Fin.elim0 i
   have hr:UniformMatchingAxisTableMachine.InRange r E:=by intro i;exact Fin.elim0 i
   have edges:UniformMatchingAxisTableMachine.Edges E c.rows v:=by intro i;exact Fin.elim0 i
   obtain ⟨u,finish,up,entry,rows,widths,perm,sh,outs2,roots2,nh2,high2⟩:=
    UniformDirectLeafCacheFinish.execution x E v head edges hm hr positive (by have:=layout.rows;omega)
     layout.permutation layout.widths layout.markers layout.axis layout.entry code vp branch.final_bound
   have table':UniformDirectLeafCacheScale.Table c.pool r q.dest mu u:=by
    intro lane j;rw[sh];exact table lane j
   let result:Result c r q mu positive u:=⟨0,1,E,hm,hr,by simp[kind],
    by simp[UniformDirectLeafCacheChronology.cacheKind,kind],entry,rows,widths,perm,
    fun _=>table',fun impossible=>by omega⟩
   refine ⟨u,?_,up,⟨⟨result,by intro i;exact Fin.elim0 i,by intro impossible;omega⟩⟩,?_,?_,?_,outs2.trans (outs1.trans outs0),roots2.trans (roots1.trans roots0)⟩
   · convert (boot.trans branch).executes finish using 1
     simp only[kind,ite_true,UniformMatchingAxisTableMachine.runtime];omega
   · intro j hj;exact (congrFun sh j).trans ((out1 j hj).trans (out0 j hj))
   · intro j hj outside;exact (nh2 j hj).trans ((congrFun nh1 j).trans (nh0 j outside))
   · intro j hj
     exact (high2 j hj).trans ((congrFun nh1 j).trans (nh0 j (Or.inr (by omega))))
 · obtain ⟨v,branch,vp,table,head,nh1,outs1,roots1,out1,unused⟩:=UniformDirectLeafCalendarSemanticBranch.shear_execution
    mu x b ready source cc ones kind range.1 range.2.1 neq (by omega) layout.pool code bp boot.final_bound
   let E:Fin 1→UniformColoring.Edge:=fun _=>⟨q.dest,q.source,neq⟩
   have hm:UniformMatchingAxisTableMachine.Matching E:=by
    intro i j ne
    have h:i=j:=Fin.ext (by have:=i.isLt;have:=j.isLt;omega)
    exact False.elim (ne h)
   have hr:UniformMatchingAxisTableMachine.InRange r E:=fun _=>⟨range.1,range.2.1⟩
   have edges:UniformMatchingAxisTableMachine.Edges E c.rows v:=by
    intro i
    have iz:i=0:=by have:=i.isLt;omega
    subst i
    constructor
    · simpa [E] using (congrFun nh1 c.rows).trans ready.dest
    · simpa [E] using (congrFun nh1 (c.rows+1)).trans ready.source
   obtain ⟨u,finish,up,entry,rows,widths,perm,sh,outs2,roots2,nh2,high2⟩:=
    UniformDirectLeafCacheFinish.execution x E v head edges hm hr positive layout.rows
     layout.permutation layout.widths layout.markers layout.axis layout.entry code vp branch.final_bound
   have table':UniformGlobalMatchingScaleMachine.FullFactorTable c.pool r q.dest q.source mu u:=by
    intro lane side;rw[sh];exact table lane side
   let result:Result c r q mu positive u:=⟨1,0,E,hm,hr,by simp[kind],
    by simp[UniformDirectLeafCacheChronology.cacheKind,kind],entry,rows,widths,perm,
    fun impossible=>by omega,fun _=>table'⟩
   refine ⟨u,?_,up,⟨⟨result,by intro i;exact ⟨rfl,rfl⟩,by
    intro _ lane i nd ne
    rw[sh]
    exact unused lane i nd ne⟩⟩,?_,?_,?_,outs2.trans (outs1.trans outs0),roots2.trans (roots1.trans roots0)⟩
   · convert (boot.trans branch).executes finish using 1
     simp only[kind,show ¬(1:ℕ)=0 by omega,ite_false,UniformMatchingAxisTableMachine.runtime];omega
   · intro j hj;exact (congrFun sh j).trans ((out1 j hj).trans (out0 j hj))
   · intro j hj outside;exact (nh2 j hj).trans ((congrFun nh1 j).trans (nh0 j outside))
   · intro j hj
     exact (high2 j hj).trans ((congrFun nh1 j).trans (nh0 j (Or.inr (by omega))))
end
end ExactFourierCircuits.UniformDirectLeafCacheSemanticExecution
