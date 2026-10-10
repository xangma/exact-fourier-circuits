import DFTModelCacheHeightNative
import DFTModelCacheHeightBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightRaw
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def wordBound (a e A C P d:ℕ):ℕ :=
 DFTModelCacheTopology.B (DFTModelCacheTopology.exponent a e) a e+
 e+A+C+P+d+5*(dag a e).size+((dag a e).size+2)*(dag a e).size+10

theorem source_input_words (a e A C P d:ℕ) (enabled:Bool)
 (u:UniformMachine.State) (ticks:ℕ) (source:DFTModelCacheTopology.Result a e u ticks):
 DFTModelCacheHeight.Words DFTModelCacheHeight.Input (wordBound a e A C P d)
  (selectedInput (A,(C,(P,(d,if enabled then 1 else 0)))) e
   (run DFTModelCacheBucketRaw.program (a,e)).val) := by
 let G:=(dag a e).size
 let M:=wordBound a e A C P d
 have size:G=DFTModelCacheBucketRaw.count a e:=DFTModelCacheTopology.typed_count _ _ _
  (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
 have len:(run DFTModelCacheTopology.program (a,e)).val.2.2.len=5*G:=by
  simpa only [size,DFTModelCacheBucketRaw.count,DFTModelCacheTopologyDepth.count] using source.length
 have base:DFTModelCacheTopology.B (DFTModelCacheTopology.exponent a e) a e≤M:=by
  unfold M wordBound;omega
 have par:e≤M ∧ A≤M ∧ C≤M ∧ P≤M ∧ d≤M ∧ 1≤M ∧ 5*G≤M ∧ G+2≤M ∧ (G+2)*G≤M:=by
  dsimp only [M,wordBound,G]
  omega
 rw [DFTModelCacheBucketRaw.program_value]
 change (e≤M ∧ A≤M ∧ C≤M ∧ P≤M ∧ d≤M ∧ (if enabled then 1 else 0)≤M) ∧
  ((run DFTModelCacheTopology.program (a,e)).val.2.2.len≤M ∧
    ∀i, (run DFTModelCacheTopology.program (a,e)).val.2.2.pos i≤M) ∧
  (G≤M ∧ ∀i:Fin G,(UniformDAGBucketMachine.order G
    (UniformDAGBucketMachine.typedDepth (dag a e).program))[i.val]?.getD 0≤M) ∧
  (G+2≤M ∧ ∀i:Fin (G+2),UniformDAGBucketMachine.offset G i.val
    (UniformDAGBucketMachine.typedDepth (dag a e).program)≤M)
 refine ⟨⟨par.1,par.2.1,par.2.2.1,par.2.2.2.1,par.2.2.2.2.1,?_⟩,
   ⟨by rw [len];exact par.2.2.2.2.2.2.1,?_⟩,⟨by omega,?_⟩,
   ⟨par.2.2.2.2.2.2.2.1,?_⟩⟩
 · split <;>omega
 · intro i
   have hi:i.val<5*DFTModelCacheBucketRaw.count a e:=by
     have hlt:=i.isLt
     omega
   have copied:=source.copied.2 i.val hi
   have bound:=source.actual.final_bound.2.2.1 _ _ copied |>.2
   have read:(run DFTModelCacheTopology.program (a,e)).val.2.2.look i.val 0=
       (run DFTModelCacheTopology.program (a,e)).val.2.2.pos i:=by
     unfold Tape.look
     split
     · rfl
     · exact False.elim (by have:=i.isLt;contradiction)
   rw [read] at bound
   exact bound.trans base
 · intro i
   cases h:(UniformDAGBucketMachine.order G (UniformDAGBucketMachine.typedDepth (dag a e).program))[i.val]? with
   | none=>simp only [Option.getD_none];omega
   | some j=>
     have hj: j<G:=(UniformDAGBucketMachine.order_mem G _ j).mp (List.mem_of_getElem? h) |>.1
     simp only [Option.getD_some]
     omega
 · intro i
   exact (UniformDAGBucketMachine.offset_bound G i.val _).trans
    ((Nat.mul_le_mul_right G (by have:=i.isLt;omega)).trans par.2.2.2.2.2.2.2.2)

def workBudget (a e A C P d:ℕ) : ℕ :=
 DFTModelCacheBucketRaw.workBudget a e+DFTModelCacheHeight.workBudget (2*wordBound a e A C P d)+25

def peakBudget (a e A C P d:ℕ) : ℕ :=
 max (DFTModelCacheBucketRaw.peakBudget a e) (DFTModelCacheHeight.peakBudget (wordBound a e A C P d))

theorem height_work_mono {S T:ℕ} (h:S≤T):
 DFTModelCacheHeight.workBudget S≤DFTModelCacheHeight.workBudget T := by
 unfold DFTModelCacheHeight.workBudget DFTModelCacheHeight.selectBudget
 have square:=Nat.mul_le_mul h h
 nlinarith

/-- All metadata and their integer bounds are derived internally from the raw
producer. The selected-height scan has an explicit quadratic work envelope. -/
theorem execution (a e A C P d:ℕ) (enabled:Bool):
 ∃u ticks,DFTModelCacheTopology.Result a e u ticks ∧
 DFTModelCacheMatchingNat.Budget
  (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e)))
  (workBudget a e A C P d) (peakBudget a e A C P d) := by
 obtain ⟨u,ticks,source,bucket⟩:=DFTModelCacheBucketRaw.execution a e
 have words:=source_input_words a e A C P d enabled u ticks source
 have five:5≤wordBound a e A C P d:=by unfold wordBound;omega
 have h:=DFTModelCacheHeight.program_bound _ _ five words
 have slots:=DFTModelCacheHeight.slotCount_bound _ _ words
 have cost:=h.2.1.trans (height_work_mono slots)
 have bucketCost:=bucket.2.1
 refine ⟨u,ticks,source,?_⟩
 rw [program_run]
 change (_ ∧ _) ∧ _ ∧ _
 exact ⟨⟨bucket.1,h.1⟩,by unfold workBudget;dsimp only;omega,
  max_le (bucket.2.2.trans (le_max_left _ _)) (h.2.2.trans (le_max_right _ _))⟩

end
end ExactFourierCircuits.DFTModelCacheHeightRaw
