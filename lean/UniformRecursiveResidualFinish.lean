import UniformRecursiveGroupLoop
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualFinish
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace P
export UniformRecursiveSavingProgram (Part program piece address size part_child)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace Copy
export UniformResidualArrayCopyMachine (program Header Frame Outside finiteIndex finiteIndex_small finiteIndex_injective)
end Copy
noncomputable section

def scatterOps:List Op:=[.binary .mul 4072 4091 4153,.binary .mul 4073 4090 4153,
 .binary .mul 4070 4122 4153,.binary .mul 4071 4067 4153,
 .literal 4074 1,.binary .mul 4069 4153 4153]
lemma scatterOps_length:scatterOps.length=6:=rfl
lemma scatter_setup_code:BlockAt scatterOps P.program (P.address .scatterSetup):=
 UniformRecursiveSavingExecution.part_block .scatterSetup _ _ rfl
lemma scatter_jump:P.program[P.address .scatterSetup+6]?=some (.jump (P.address .scatter)):=
 UniformRecursiveSavingExecution.part_at .scatterSetup 6 (by decide)
lemma scatter_code:CodeAt Copy.program P.program (P.address .scatter) (P.address .directionNext):=
 P.part_child rfl

def SetupChanged(i:ℕ):Prop:=i=4072∨i=4073∨i=4070∨i=4071∨i=4074∨i=4069
structure SetupFrame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬SetupChanged i→u.natReg i=s.natReg i
lemma scatter_frame(s:State):SetupFrame s (applyBlock scatterOps s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 unfold SetupChanged at hi
 simp (disch:=omega) [scatterOps,applyBlock,Op.apply,evalNat,writeNat,next]

lemma place_setPC(main:Program)(start n B:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=start)(_run:BoundedRuns main n x B s 0 s):placed start {s with pc:=0}=s:=by
 change {s with pc:=start}=s
 rw [←pc]

/-- The actual six header writes and continuation jump, over symbolic PCs. -/
theorem scatter_setup_generic(main:Program)(start target n B V table source dest:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt scatterOps main start)(jump:main[start+6]?=some (.jump target))
 (pc:s.pc=start)(one:s.natReg 4153=1)(length:s.natReg 4122=V)(src:s.natReg 4091=source)
 (dst:s.natReg 4090=dest)(permutation:s.natReg 4067=table)
 (bound:WordBound B s)(extent:start+7 ≤ B)(ret:target ≤ B):∃u,
 BoundedRuns main n x B s 7 u ∧ u.pc=target ∧ Copy.Header V table source dest false u ∧ SetupFrame s u:=by
 have vb:V ≤ B:=by have h:=bound.2.1 4122;rwa [length] at h
 have sb:source ≤ B:=by have h:=bound.2.1 4091;rwa [src] at h
 have db:dest ≤ B:=by have h:=bound.2.1 4090;rwa [dst] at h
 have tb:table ≤ B:=by have h:=bound.2.1 4067;rwa [permutation] at h
 have ob:1 ≤ B:=by have h:=bound.2.1 4153;rwa [one] at h
 have safe:readable scatterOps s∧peak scatterOps s ≤ B:=by
  simp [scatterOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,one,length,src,dst,permutation,vb,sb,db,tb,ob]
 have run:=block_runs scatterOps main start n B x s atCode pc bound (by rw [scatterOps_length];omega) safe.1 safe.2
 let a:=applyBlock scatterOps s
 let u:State:={a with pc:=target}
 have ap:a.pc=start+6:=by rw [UniformRecursiveNodePreparation.block_pc,pc,scatterOps_length]
 have ub:=changePC_bound B a target run.final_bound ret
 have finish:BoundedRuns main n x B a 1 u:=.next run.final_bound (by simp [step,ap,jump,u]) (.refl ub)
 have header:Copy.Header V table source dest false u:=by
  constructor <;> simp [u,a,scatterOps,applyBlock,Op.apply,evalNat,writeNat,next,one,length,src,dst,permutation]
 have fr:=scatter_frame s
 exact ⟨u,by simpa only [scatterOps_length] using run.trans finish,rfl,header,
  ⟨fr.natHeap,fr.scalarHeap,fr.scalarReg,fr.outputs,fr.roots,fr.natReg⟩⟩

/-- Literal copy16 embedded inside the held recursive Program. The physical
permutation and source presence come from the earlier native gather/groups. -/
theorem scatter_embedded(main:Program)(start exit n B V table source dest:ℕ)(x:Fin n→ℂ)(s:State)
 (link:CodeAt Copy.program main start exit)(pc:s.pc=start)(header:Copy.Header V table source dest false s)
 (permutation:Fin V≃Fin V)(bank:∀j:Fin V,s.natHeap (table+j.val)=some (permutation j).val)
 (data:∀j:Fin V,(s.scalarHeap (source+j.val)).isSome=true)
 (separate:source+V ≤ dest∨dest+V ≤ source)(sourceEnd:source+V ≤ B)(destEnd:dest+V ≤ B)
 (tableEnd:table+V ≤ B)(bound:WordBound B s)(extent:start+Copy.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s (10*V+4) u ∧ u.pc=exit ∧
 (∀j:Fin V,u.scalarHeap (dest+(permutation j).val)=s.scalarHeap (source+j.val)) ∧
 Copy.Outside V dest s.scalarHeap u ∧ Copy.Frame s u:=by
 let caller:State:={s with pc:=0}
 have cb:=changePC_bound B s 0 bound (by omega)
 have h:Copy.Header V table source dest false caller:=
  ⟨header.length,header.table,header.source,header.destination,header.mode⟩
 have src:∀j,j < V→∃v,caller.scalarHeap (source+j)=some v:=by
  intro j hj
  have present:=data ⟨j,hj⟩
  cases e:s.scalarHeap (source+j) with
  | none=>simp only [e,Option.isSome_none,Bool.false_eq_true] at present
  | some v=>exact ⟨v,rfl⟩
 have atBank:∀j,j < V→caller.natHeap (table+j)=some (Copy.finiteIndex permutation j):=by
  intro j hj
  simpa only [UniformResidualArrayCopyMachine.finiteIndex,dite_eq_left hj] using bank ⟨j,hj⟩
 have small:16 ≤ B:=by
  have h:Copy.program.length ≤ B:=(Nat.le_add_left _ _).trans extent
  simpa only [UniformResidualArrayCopyMachine.program_length] using h
 obtain ⟨a,run,ap,values,outside,fr⟩:=UniformResidualArrayCopyMachine.execution n B V table source dest false
  (Copy.finiteIndex permutation) x caller h (Copy.finiteIndex_small permutation)
  (fun i hi j hj eq=>Copy.finiteIndex_injective permutation i j hi hj eq) atBank src separate sourceEnd destEnd tableEnd small rfl cb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed link extent ret run
 have same:placed start caller=s:=by
  change {s with pc:=start}=s
  rw [←pc]
 rw [same] at placedRun
 let u:State:={a with pc:=exit}
 have vals:∀j:Fin V,u.scalarHeap (dest+(permutation j).val)=s.scalarHeap (source+j.val):=by
  intro j
  have v:=values j.val j.isLt
  simpa only [UniformResidualArrayCopyMachine.targetIndex,UniformResidualArrayCopyMachine.sourceIndex,
   Bool.false_eq_true,ite_false,UniformResidualArrayCopyMachine.finiteIndex_value] using v
 exact ⟨u,by simpa only [Bool.false_eq_true,ite_false] using placedRun,rfl,vals,outside,
  ⟨fr.natHeap,fr.outputs,fr.roots,fr.natReg,fr.scalarReg⟩⟩
def ScatterChanged(i:ℕ):Prop:=SetupChanged i∨(4075 ≤ i∧i ≤ 4081)
structure ScatterFrame(dest V:ℕ)(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬ScatterChanged i→u.natReg i=s.natReg i
 scalarReg:∀i,i ≠ 120→u.scalarReg i=s.scalarReg i
 scalarHeap:∀z,(z < dest∨dest+V ≤ z)→u.scalarHeap z=s.scalarHeap z

/-- Physical setup7 followed by literal scatter16, from the raw controls
retained by the complete group loop. Coefficient/array values are never
installed by host action or a callback. -/
theorem scatter_execution(n B V table source dest:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .scatterSetup)(one:s.natReg 4153=1)(length:s.natReg 4122=V)
 (src:s.natReg 4091=source)(dst:s.natReg 4090=dest)(perm:s.natReg 4067=table)
 (permutation:Fin V≃Fin V)(bank:∀j:Fin V,s.natHeap (table+j.val)=some (permutation j).val)
 (data:∀j:Fin V,(s.scalarHeap (source+j.val)).isSome=true)
 (separate:source+V ≤ dest∨dest+V ≤ source)(sourceEnd:source+V ≤ B)(destEnd:dest+V ≤ B)
 (tableEnd:table+V ≤ B)(bound:WordBound B s)(code:P.program.length ≤ B):∃u,
 BoundedRuns P.program n x B s (10*V+11) u ∧ u.pc=P.address .directionNext ∧
 (∀j:Fin V,u.scalarHeap (dest+(permutation j).val)=s.scalarHeap (source+j.val)) ∧ ScatterFrame dest V s u:=by
 obtain ⟨a,prep,ap,header,fr⟩:=scatter_setup_generic P.program (P.address .scatterSetup) (P.address .scatter)
  n B V table source dest x s scatter_setup_code scatter_jump pc one length src dst perm bound
  (R.code_bound .scatterSetup 7 B rfl code) (R.start_bound .scatter B code)
 have atBank:∀j:Fin V,a.natHeap (table+j.val)=some (permutation j).val:=by intro j;rw [fr.natHeap];exact bank j
 have atData:∀j:Fin V,(a.scalarHeap (source+j.val)).isSome=true:=by intro j;rw [fr.scalarHeap];exact data j
 obtain ⟨u,run,up,values,outside,cf⟩:=scatter_embedded P.program (P.address .scatter) (P.address .directionNext)
  n B V table source dest x a scatter_code ap header permutation atBank atData separate sourceEnd destEnd tableEnd
  prep.final_bound (R.code_bound .scatter Copy.program.length B rfl code) (R.start_bound .directionNext B code)
 have total:BoundedRuns P.program n x B s (10*V+11) u:=by
  convert prep.trans run using 1
  omega
 have frame:ScatterFrame dest V s u:=by
  refine ⟨cf.natHeap.trans fr.natHeap,cf.outputs.trans fr.outputs,cf.roots.trans fr.roots,?_,?_,?_⟩
  · intro i hi
    have hs:¬SetupChanged i:=fun h=>hi (Or.inl h)
    have hc:i < 4075∨4081 < i:=by
     have h:¬(4075 ≤ i∧i ≤ 4081):=fun h=>hi (Or.inr h)
     omega
    exact (cf.natReg i hc).trans (fr.natReg i hs)
  · intro i hi;exact (cf.scalarReg i hi).trans (congrFun fr.scalarReg i)
  · intro z hz
    exact (outside z hz).trans (congrFun fr.scalarHeap z)
 exact ⟨u,total,up,fun j=>(values j).trans (congrFun fr.scalarHeap _),frame⟩


theorem scatter_generic(main:Program)(start next exit n B V table source dest:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=start)(one:s.natReg 4153=1)(length:s.natReg 4122=V)
 (src:s.natReg 4091=source)(dst:s.natReg 4090=dest)(perm:s.natReg 4067=table)
 (permutation:Fin V≃Fin V)(bank:∀j:Fin V,s.natHeap (table+j.val)=some (permutation j).val)
 (data:∀j:Fin V,(s.scalarHeap (source+j.val)).isSome=true)
 (separate:source+V ≤ dest∨dest+V ≤ source)(sourceEnd:source+V ≤ B)(destEnd:dest+V ≤ B)
 (tableEnd:table+V ≤ B)(bound:WordBound B s)(atCode:BlockAt scatterOps main start)
 (jump:main[start+6]?=some (.jump next))(link:CodeAt Copy.program main next exit)
 (setupExtent:start+7 ≤ B)(nextBound:next ≤ B)(extent:next+Copy.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s (10*V+11) u ∧ u.pc=exit ∧
 (∀j:Fin V,u.scalarHeap (dest+(permutation j).val)=s.scalarHeap (source+j.val)) ∧ ScatterFrame dest V s u:=by
 obtain ⟨a,prep,ap,header,fr⟩:=scatter_setup_generic main (start) (next)
  n B V table source dest x s atCode jump pc one length src dst perm bound
  setupExtent nextBound
 have atBank:∀j:Fin V,a.natHeap (table+j.val)=some (permutation j).val:=by intro j;rw [fr.natHeap];exact bank j
 have atData:∀j:Fin V,(a.scalarHeap (source+j.val)).isSome=true:=by intro j;rw [fr.scalarHeap];exact data j
 obtain ⟨u,run,up,values,outside,cf⟩:=scatter_embedded main (next) (exit)
  n B V table source dest x a link ap header permutation atBank atData separate sourceEnd destEnd tableEnd
  prep.final_bound extent ret
 have total:BoundedRuns main n x B s (10*V+11) u:=by
  convert prep.trans run using 1
  omega
 have frame:ScatterFrame dest V s u:=by
  refine ⟨cf.natHeap.trans fr.natHeap,cf.outputs.trans fr.outputs,cf.roots.trans fr.roots,?_,?_,?_⟩
  · intro i hi
    have hs:¬SetupChanged i:=fun h=>hi (Or.inl h)
    have hc:i < 4075∨4081 < i:=by
     have h:¬(4075 ≤ i∧i ≤ 4081):=fun h=>hi (Or.inr h)
     omega
    exact (cf.natReg i hc).trans (fr.natReg i hs)
  · intro i hi;exact (cf.scalarReg i hi).trans (congrFun fr.scalarReg i)
  · intro z hz
    exact (outside z hz).trans (congrFun fr.scalarHeap z)
 exact ⟨u,total,up,fun j=>(values j).trans (congrFun fr.scalarHeap _),frame⟩

end
end ExactFourierCircuits.UniformRecursiveResidualFinish
