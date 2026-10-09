import UniformActualCalendarMatchingSource
import UniformDirectLeafCacheSemanticExecution
import UniformGlobalCalendarMatchingPhase
set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarDirectEvent
open UniformMachine UniformGlobalCalendarDispatch
open UniformGlobalMatchingScaleMachine (Phase)
open UniformDirectLeafCacheReader UniformDirectLeafCacheSemanticExecution
open UniformActualCalendarMatchingSource UniformGlobalMatchingScaleBankBridge
noncomputable section

variable {c : Config} {r : ℕ} {q : UniformTransposeDescriptorMachine.Record}
 {mu : ℂ} {positive : 2≤r} {s : State}

def values (res : SemanticResult c r q mu positive s) (lane : Fin 9) (i : Fin r) : ℂ:=
 if q.kind=0 then UniformDirectLeafCacheScale.Value mu q.dest lane.val i.val
 else nativeFactor res.edges (fun _=>mu) lane i.val

lemma grid (res : SemanticResult c r q mu positive s) (legal : UniformDirectLeafCacheSource.Legal q) :
 ∀lane (i:Fin r),s.scalarHeap (c.pool+lane.val*r+i.val)=some (UniformPairMachine.prepared (values res lane i)):=by
 intro lane i
 rcases legal with ⟨scale,_⟩|⟨shear,_⟩
 · simpa only[values,scale,ite_true] using res.scale scale lane i
 · have count:res.count=1:=by rw[res.count_eq,shear];rfl
   let first:Fin res.count:=⟨0,by omega⟩
   have pair:=res.endpoints first
   have matching:=res.matching
   have coefficient:values res lane i=nativeFactor res.edges (fun _=>mu) lane i.val:=by
    simp only[values,shear,show ¬(1:ℕ)=0 by omega,ite_false]
   rw[coefficient]
   by_cases left:i.val=q.dest
   · rw[left,←pair.1,nativeFactor_left res.edges (fun _=>mu) matching lane first]
     simpa only[UniformGlobalMatchingScaleMachine.FullFactorTable,
      UniformGlobalMatchingScaleMachine.address,ite_true,pair.1] using res.shear shear lane 0
   · by_cases right:i.val=q.source
     · rw[right,←pair.2,nativeFactor_right res.edges (fun _=>mu) matching lane first]
       simpa [UniformGlobalMatchingScaleMachine.address,pair.2] using res.shear shear lane 1
     · rw[nativeFactor_unused res.edges (fun _=>mu) lane i.val (by
        intro j incident
        rcases incident with eq|eq
        · exact left (eq.symm.trans (res.endpoints j).1)
        · exact right (eq.symm.trans (res.endpoints j).2))]
       exact res.unused shear lane i left right

def actualEvent (res : SemanticResult c r q mu positive s) (elapsed : ℕ) (phase : Phase) : Event:=
 event c.entry elapsed c.pool c.permutation res.kind phase (values res) res.edges

/-- Actual direct-cache execution, with its generated partition and all nine
source lanes, supplies the281 dispatcher without a ready-action premise. -/
theorem cached {O T B : ℕ} (res : SemanticResult c r q mu positive s)
 (legal : UniformDirectLeafCacheSource.Legal q) (elapsed : ℕ) (phase : Phase)
 (decoded : Decoded (actualEvent res elapsed phase).descriptor phase)
 (entryFit : c.entry+7≤T) (poolFit : c.pool+9*r≤O)
 (permutationFit : c.permutation+r≤T) (radixBound : r≤B) :
 CachedEvent r O T B (actualEvent res elapsed phase) s:=
 cached_event res.edges res.matching res.inRange positive phase (values res) s decoded res.entry
  (grid res legal) res.permutations entryFit poolFit permutationFit radixBound

end
end ExactFourierCircuits.UniformActualCalendarDirectEvent
