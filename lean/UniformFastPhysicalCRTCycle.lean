import UniformFastPhysicalCRTProgress
import UniformFastPhysicalCRTCarryLoop

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, linear CRT index enumeration after (5.5), PDF p.22
(`eq:crt-fourier`), and prefix bound (4.1), PDF p.18.

Mixed-radix carry enumeration is an implementation refinement of the paper's
linear traversal. Initialization, carry visits, frames and instruction counts
have no one-to-one paper lemma; the final caller charges this actual producer.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFastPhysicalCRTCycle
open UniformMachine UniformNatBlockMachine UniformFastPhysicalCRTMachine UniformCRTTraversalCycle
open UniformFastPhysicalCRTArithmetic UniformFastPhysicalCRTInitialization UniformFastPhysicalCRTProgress
open scoped BigOperators
noncomputable section

lemma enter_carry{a V n B:ℕ}(L:Addresses)(x:Fin n→ℂ)(s:State)(args:Args a V L s)
 (c:Constants s)(pc:s.pc=28)(index:s.natReg 7803<V)(code:53≤B)(wb:WordBound B s):∃u,
 BoundedRuns program n x B s 3 u∧u.pc=31∧u.natReg 7804=a∧
 Args a V L u∧Constants u∧Frame s u∧u.natHeap=s.natHeap∧
 u.natReg 7803=s.natReg 7803∧u.natReg 7806=s.natReg 7806:=by
 let b:State:={s with pc:=29}
 have branch:BoundedRuns program n x B s 1 b:=.next wb
  (by simp[step,pc,emit_test,args.volume,index,b]) (.refl (changePC_bound B s 29 wb (by omega)))
 have block:=block_runs carryInit program 29 n B x b carry_init_code rfl branch.final_bound
  (by change 29+1≤B;omega) (by simp[carryInit,readable,Op.readable,evalNat])
  (by simp[carryInit,peak,Op.peak,evalNat,b,c.zero];exact wb.2.1 7790)
 let t:=applyBlock carryInit b
 have tp:t.pc=30:=by rw[block_pc];rfl
 let u:State:={t with pc:=31}
 have jump:BoundedRuns program n x B t 1 u:=.next block.final_bound
  (by simp[step,tp,carry_init_jump,u]) (.refl (changePC_bound B t 31 block.final_bound (by omega)))
 have frame:Frame s u:=by
  constructor <;>try rfl
  intro q hq;simp (disch:=omega) [u,t,b,carryInit,applyBlock,Op.apply,writeNat,next]
 refine ⟨u,?_,rfl,?_,frame.args args,?_,frame,rfl,?_,?_⟩
 · exact (branch.trans block).trans jump
 · simp[u,t,b,carryInit,applyBlock,Op.apply,writeNat,next,evalNat,args.axes,c.zero]
 · constructor <;>simp[u,t,b,carryInit,applyBlock,Op.apply,writeNat,next,c.zero,c.one,c.two]
 · simp[u,t,b,carryInit,applyBlock,Op.apply,writeNat,next]
 · simp[u,t,b,carryInit,applyBlock,Op.apply,writeNat,next]

/-- Every actual emission is followed by the necessary physical carry only.
The potential is the exact sum of odometer visit counts. -/
/- Paper stage: §5.2, linear digit traversal, PDF p.22 and (4.1), PDF p.18: actual odometer carries are amortized by the exact visit potential. -/
theorem loop{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,0<r i)(L:Addresses)
 (rho alpha beta:Fin (∏i,r i)≃Fin (∏i,r i))
 (normalEq:∀j:Fin (∏i,r i),normal r j.val=(rho j).val)
 (x:Fin n→ℂ)(heap:ℕ→Option ℕ)
 (reads:∀i:Fin a,heap (L.directory+2*i.val+1)=some (r i))
 (alphaTable:UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.alpha heap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.beta heap beta)
 (df:L.directory+2*a≤L.physicalAlpha)(af:L.alpha+(∏i,r i)≤L.physicalAlpha)
 (bf:L.beta+(∏i,r i)≤L.physicalAlpha)(separate:L.physicalAlpha+(∏i,r i)≤L.inverseBeta)
 (before:L.inverseBeta+(∏i,r i)≤L.work)(fit:L.work+2*a≤B)(volume:(∏i,r i)≤B)(code:53≤B)
 (p fuel:ℕ)(s:State)(eq:p+fuel=∏i,r i)(hp:p<∏i,r i)(pc:s.pc=19)
 (index:s.natReg 7803=p)(normalized:s.natReg 7806=normal r p)
 (args:Args a (∏i,r i) L s)(c:Constants s)(work:Work r L (digits r p) s)
 (progress:Progress a (∏i,r i) L rho alpha beta p heap s)(wb:WordBound B s):∃ticks u,
 BoundedRuns program n x B s ticks u∧
 ticks+18*totalVisits (reverse r) p≤12*fuel+18*totalVisits (reverse r) (∏i,r i)∧
 u.pc=52∧Args a (∏i,r i) L u∧Constants u∧Frame s u∧
 Progress a (∏i,r i) L rho alpha beta (∏i,r i) heap u:=by
 induction fuel generalizing p s with
 | zero=>omega
 | succ fuel ih=>
   have ats:=progress.source af separate before alphaTable
   have bts:=progress.source bf separate before bt
   obtain ⟨e,emit,ep,ei,en,ea,ec,ef,eo,eh⟩:=UniformFastPhysicalCRTEmission.execution L x s pc wb args c
    index (rho ⟨p,hp⟩) (normalized.trans (normalEq ⟨p,hp⟩)) alpha beta ats bts hp
    (by omega) (by omega) (by omega) (by omega) bf code
   have pe:=progress.step hp separate eh
   have ew:Work r L (digits r p) e:=by
    intro i
    constructor
    · rw[eo _ (Or.inr (by omega)) (Or.inr (by omega))];exact (work i).1
    · rw[eo _ (Or.inr (by omega)) (Or.inr (by omega))];exact (work i).2
   by_cases next:p+1<∏i,r i
   · obtain ⟨b,enter,bp,bi,ba,bc,bf0,bh,bindex,bnormal⟩:=enter_carry L x e ea ec ep
      (by rw[ei];exact next) code emit.final_bound
     have pb:=pe.heap bh
     have bw:Work r L (front r (p+1) 0) b:=by
      rw[UniformFastPhysicalCRTArithmetic.front_initial];simpa only[Nat.add_sub_cancel] using (show Work r L (digits r p) b from fun i=>by rw[bh];exact ew i)
     have readsB:∀i:Fin a,b.natHeap (L.directory+2*i.val+1)=some (r i):=by
      intro i
      rw[pb.outside _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact reads i
     obtain ⟨ct,u,carry,cb,up,un,ua,uc,uf,uw,uo,ui⟩:=UniformFastPhysicalCRTCarryLoop.execution r hr L x
      (p+1) 0 a (by omega) next (by omega) (by simp[place_zero]) b bp
      (by simpa using bi) (by rw[bnormal,en,←normalEq];simp[UniformFastPhysicalCRTArithmetic.front_initial,normal])
      ba bc bw readsB (by omega) fit volume code enter.final_bound
     have pu:=pb.work separate before uo
     obtain ⟨ticks,v,tail,bound,vp,va,vc,vf,pv⟩:=ih (p+1) u (by omega) next up
      (ui.trans (bindex.trans ei)) un ua uc uw pu carry.final_bound
     refine ⟨12+ct+ticks,v,?_,?_,vp,va,vc,(ef.trans (bf0.trans uf)).trans vf,pv⟩
     · convert ((emit.trans enter).trans carry).trans tail using 1
     · have step:=totalVisits_succ (reverse r) p
       omega
   · have endEq:p+1=∏i,r i:=by omega
     let u:State:={e with pc:=52}
     have branch:BoundedRuns program n x B e 1 u:=.next emit.final_bound
      (by simp[step,ep,emit_test,ei,ea.volume,next,u])
      (.refl (changePC_bound B e 52 emit.final_bound (by omega)))
     have mono:=totalVisits_mono (reverse r) (reverse_positive r hr) (Nat.le_of_lt hp)
     refine ⟨10,u,emit.trans branch,?_,rfl,args_pc ea 52,constants_pc ec 52,ef.trans (Frame.pc (.refl e) 52),?_⟩
     · omega
     · have h:=pe.heap (show u.natHeap=e.natHeap from rfl)
       simpa only[endEq] using h

/-- The literal53 produces the two complete physical CRT tables from the real
normal tables, deriving all prefix weights/digits internally. -/
/- Paper stage: §5.2, PDF p.22: literal complete table production with linear total cost; directory/source readability is an explicit discharged caller obligation. -/
theorem execution{a n B:ℕ}(r:Fin a→ℕ)(hr:∀i,2≤r i)(L:Addresses)
 (rho alpha beta:Fin (∏i,r i)≃Fin (∏i,r i))
 (normalEq:∀j:Fin (∏i,r i),normal r j.val=(rho j).val)
 (x:Fin n→ℂ)(s:State)(pc:s.pc=0)(args:Args a (∏i,r i) L s)
 (reads:∀i:Fin a,s.natHeap (L.directory+2*i.val+1)=some (r i))
 (alphaTable:UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.alpha s.natHeap alpha)
 (bt:UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.beta s.natHeap beta)
 (df:L.directory+2*a≤L.physicalAlpha)(af:L.alpha+(∏i,r i)≤L.physicalAlpha)
 (bf:L.beta+(∏i,r i)≤L.physicalAlpha)(separate:L.physicalAlpha+(∏i,r i)≤L.inverseBeta)
 (before:L.inverseBeta+(∏i,r i)≤L.work)(fit:L.work+2*a≤B)(volume:(∏i,r i)≤B)
 (code:53≤B)(wb:WordBound B s):∃ticks u,
 BoundedExecution program n x B s ticks u∧ticks≤60*((∏i,r i)+a+1)∧u.pc=52∧
 Args a (∏i,r i) L u∧Constants u∧Frame s u∧Outside a (∏i,r i) L s.natHeap u∧
 UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.physicalAlpha u.natHeap (rho.trans alpha)∧
 UniformGlobalNatPreparation.PermutationBank (∏i,r i) L.inverseBeta u.natHeap (rho.trans beta).symm:=by
 have positive:∀i,0<r i:=fun i=>by have h:=hr i;omega
 obtain ⟨b,init,bp,ba,bc,bf0,bo,bi,bn,bw⟩:=UniformFastPhysicalCRTInitialization.execution r positive L x s args
  reads (by omega) fit volume code pc wb
 have bwork:Work r L (digits r 0) b:=by simpa only[digits_zero] using bw
 have bnormal:b.natReg 7806=normal r 0:=by rw[bn];simp[normal,digits_zero,value]
 have pr:=Progress.initialized L rho alpha beta s b bo
 obtain ⟨ticks,u,run,cost,up,ua,uc,uf,pu⟩:=loop r positive L rho alpha beta normalEq x s.natHeap
  reads alphaTable bt df af bf separate before fit volume code 0 (∏i,r i) b (by omega)
  (Finset.prod_pos (fun i _=>positive i)) bp bi bnormal ba bc bwork pr init.final_bound
 have halt:BoundedExecution program n x B u 1 u:=.halt run.final_bound (by simp[step,up,halt_code])
 refine ⟨12*a+8+ticks+1,u,?_,?_,up,ua,uc,bf0.trans uf,pu.outside,pu.banks⟩
 · convert init.executes (run.executes halt) using 1
 · have visits:=reverse_totalVisits r hr
   simp only[totalVisits_zero,Nat.mul_zero,Nat.add_zero] at cost
   omega
end
end ExactFourierCircuits.UniformFastPhysicalCRTCycle
