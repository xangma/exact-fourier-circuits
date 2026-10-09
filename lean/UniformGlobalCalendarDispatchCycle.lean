import UniformGlobalCalendarDispatchRouting

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine UniformAssembly
open UniformGlobalMatchingScaleMachine (Phase)
open UniformTensorMonomialMachine (applyBlock)
noncomputable section

def phaseCalls : Phase→ℕ→ℕ
 | .diagonal _,_=>0
 | .kernel,m=>m
def phaseFactor : Phase→(ℕ→ℂ)→ℕ→ℂ
 | .diagonal _,f=>f
 | .kernel,_=>fun _=>1

def Source (r : ℕ) (d : Descriptor) (p : Phase) (f : ℕ→ℂ) (records : ℕ→ℕ×ℕ) (s : State) : Prop := match p with
 | .diagonal lane=>UniformGlobalCalendarFactorMerge.Factors (d.pool+lane.val*r) r f s.scalarHeap
 | .kernel=>UniformGlobalCalendarUnionRows.Rows d.permutation (r-d.widthCount) records s.natHeap

def rowAction (T used count : ℕ) (p : Phase) (records : ℕ→ℕ×ℕ) (heap : ℕ→Option ℕ) : ℕ→Option ℕ := match p with
 | .diagonal _=>heap
 | .kernel=>UniformGlobalCalendarUnionRows.writeRows T used records 0 count heap

/-- One complete genuine selected entry through the actual281 instruction
loop. The two physical actions merge real scalar cells or copy real ordered
endpoints; the row count and both persistent cache prefixes are retained. -/
theorem cycle_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (p : Phase) (f g : ℕ→ℂ) (records : ℕ→ℕ×ℕ)
 (h : Header A N r O T used phaseBank j s) (selected : Selected A j d s) (stored : Stored d s)
 (decoded : Decoded d p) (pc : s.pc=10) (wb : WordBound B s) (code : 281 ≤ B) (index : j<N)
 (selectionFit : A+2*N ≤ B) (entryFit : d.address+7 ≤ B)
 (printed : UniformFixedNetworkScheduleMachine.Printed phaseBank UniformGlobalCalendarPhaseDirectory.words s)
 (phaseFit : phaseBank+56 ≤ B) (source : Source r d p f records s)
 (target : UniformGlobalCalendarFactorMerge.Factors O r g s.scalarHeap)
 (sourcePoolFit : d.pool+9*r ≤ B) (freshPool : d.pool+9*r ≤ O) (outputPoolFit : O+r ≤ B)
 (sourceRowsFit : d.permutation+2*(r-d.widthCount) ≤ B) (freshRows : d.permutation+2*(r-d.widthCount) ≤ T)
 (values : ∀i,i<r-d.widthCount→(records i).1 ≤ B∧(records i).2 ≤ B)
 (outputRowsFit : T+3*(used+phaseCalls p (r-d.widthCount)) ≤ B) (matching : 2*(r-d.widthCount) ≤ r) :
 ∃u time, BoundedRuns program n x B s time u∧time ≤ 9*r+48∧u.pc=10∧
 Header A N r O T (used+phaseCalls p (r-d.widthCount)) phaseBank (j+1) u∧
 UniformGlobalCalendarFactorMerge.Factors O r (fun i=>phaseFactor p f i*g i) u.scalarHeap∧
 u.natHeap=rowAction T used (r-d.widthCount) p records s.natHeap∧
 (∀z,z<T→u.natHeap z=s.natHeap z)∧
 (∀z,z<O∨O+r ≤ z→u.scalarHeap z=s.scalarHeap z)∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs := by
 obtain ⟨a,first,ap,ah,al,anh,ash,ar,ao⟩:=prefix_execution x s d h selected stored pc wb code index selectionFit entryFit
 obtain ⟨b,t,route,cap,entry,bh,bl,bnh,bsh,br,bo⟩:=route_execution x a d p ah al decoded ap first.final_bound code
  (by intro i hi;exact (congrFun anh _).trans (printed i hi)) phaseFit
 have heaps : b.natHeap=s.natHeap:=bnh.trans anh
 have scalars : b.scalarHeap=s.scalarHeap:=bsh.trans ash
 have roots : b.rootOrders=s.rootOrders:=br.trans ar
 have outputs : b.outputs=s.outputs:=bo.trans ao
 cases p with
 | diagonal lane=>
   have so : UniformGlobalCalendarFactorMerge.Factors (d.pool+lane.val*r) r f b.scalarHeap:=by
    rw [scalars];exact source
   have tg : UniformGlobalCalendarFactorMerge.Factors O r g b.scalarHeap:=by rw [scalars];exact target
   obtain ⟨c,merge,cp,ch,out,sf,nh,cr,co⟩:=factor_execution x b d f g bh bl entry.2 lane.isLt entry.1
    route.final_bound code so tg sourcePoolFit freshPool outputPoolFit
   have jump : BoundedRuns program n x B c 1 {c with pc:=49}:=control x c merge.final_bound (by omega)
    (by simp [step,cp,code_41])
   obtain ⟨advance,dh⟩:=advance_execution x {c with pc:=49} (ch.atPC 49) rfl jump.final_bound code index
   refine ⟨{applyBlock UniformGlobalCalendarDispatch.advance {c with pc:=49} with pc:=10},18+t+(9*r+12)+1+2,
    (((first.trans route).trans merge).trans jump).trans advance,by omega,rfl,?_,out,?_,?_,?_,?_,?_⟩
   · simpa only [phaseCalls,Nat.add_zero] using dh
   · exact nh.trans heaps
   · intro z _;exact congrFun (nh.trans heaps) z
   · intro z outside;exact (sf z outside).trans (congrFun scalars z)
   · exact cr.trans roots
   · exact co.trans outputs
 | kernel=>
   have so : UniformGlobalCalendarUnionRows.Rows d.permutation (r-d.widthCount) records b.natHeap:=by
    rw [heaps];exact source
   obtain ⟨c,rows,cp,ch,heap,sh,cr,co⟩:=rows_execution x b d records bh bl entry route.final_bound code
    so sourceRowsFit freshRows values outputRowsFit
   obtain ⟨advance,dh⟩:=advance_execution x c ch cp rows.final_bound code index
   refine ⟨{applyBlock UniformGlobalCalendarDispatch.advance c with pc:=10},18+t+(16*(r-d.widthCount)+15)+2,
    ((first.trans route).trans rows).trans advance,by omega,rfl,dh,?_,?_,?_,?_,?_,?_⟩
   · intro i hi
     change c.scalarHeap (O+i)=some (UniformPairMachine.prepared (1*g i))
     rw [sh,scalars,one_mul];exact target i hi
   · exact heap.trans (congrArg (UniformGlobalCalendarUnionRows.writeRows T used records 0 (r-d.widthCount)) heaps)
   · intro z below
     change c.natHeap z=s.natHeap z
     rw [heap,UniformGlobalCalendarUnionRows.writeRows_low T used records 0 (r-d.widthCount) b.natHeap z (by omega),heaps]
   · intro z _;exact (congrFun sh z).trans (congrFun scalars z)
   · exact cr.trans roots
   · exact co.trans outputs

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
