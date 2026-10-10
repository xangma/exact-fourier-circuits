import DFTModelCacheBucketBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- The genuine topology-depth producer precedes bucket generation. -/
def fromTopology : Prog false Input (p (Ty.a w) (Ty.a w)) :=
  .comp (.fork (.atom .fst) (.fork count DFTModelCacheDAGDepth.fromTopology)) program

attribute [local irreducible] program DFTModelCacheDAGDepth.fromTopology

theorem fromTopology_run (N G:ℕ) (t:Tape ℕ):
    run fromTopology (N,(G,t))=
      ⟨(run program (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val))).val,
       (run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).work+
         (run program (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val))).work+7,
       max (run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).peak
         (run program (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val))).peak,
       (run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).valid ∧
         (run program (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val))).valid⟩ := by
  rw [fromTopology]
  simp only [count,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,and_true,zero_max,max_zero]
  congr 1
  omega

theorem selected_congr (G l:ℕ) (d e:ℕ→ℕ) (h:∀i,i<G→d i=e i):
    UniformDAGBucketMachine.selected G l d=UniformDAGBucketMachine.selected G l e := by
  unfold UniformDAGBucketMachine.selected
  apply List.filter_congr
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem order_congr (G:ℕ) (d e:ℕ→ℕ) (h:∀i,i<G→d i=e i):
    UniformDAGBucketMachine.order G d=UniformDAGBucketMachine.order G e := by
  unfold UniformDAGBucketMachine.order
  exact congrArg (fun f=>(List.range (G+1)).flatMap f) (funext (fun l=>selected_congr G l d e h))

theorem offset_congr (G l:ℕ) (d e:ℕ→ℕ) (h:∀i,i<G→d i=e i):
    UniformDAGBucketMachine.offset G l d=UniformDAGBucketMachine.offset G l e := by
  unfold UniformDAGBucketMachine.offset
  congr 1
  exact congrArg (fun f=>(List.range l).flatMap f) (funext (fun j=>selected_congr G j d e h))

theorem topology_depth {r N G:ℕ} (p:UniformReplayPrint.Program r N G) (t:Tape ℕ)
    (fields:DFTModelCacheDAGDepth.TopologyFields (UniformDAGDepthMachine.rows p) t)
    (i:ℕ) (hi:i<G):
    depthValue (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val)) i=
      UniformDAGBucketMachine.typedDepth p i := by
  have h:=DFTModelCacheDAGDepth.fromTopology_typed p t fields ⟨N+1+i,by omega⟩
  simpa only [depthValue,UniformDAGBucketMachine.typedDepth,UniformDAGLayers.natLevel,
    dite_eq_left (show N+1+i<N+1+G by omega)] using h

/-- Exact stable typed gate chronology from the original five-field tape.
The only input condition is genuine topology fields, not depth or order output. -/
theorem fromTopology_value {r N G:ℕ} (p:UniformReplayPrint.Program r N G) (t:Tape ℕ)
    (fields:DFTModelCacheDAGDepth.TopologyFields (UniformDAGDepthMachine.rows p) t):
    (run fromTopology (N,(G,t))).val=
      (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G (UniformDAGBucketMachine.typedDepth p))[j]?.getD 0),
       Tape.tab (G+2) (fun l=>UniformDAGBucketMachine.offset G l (UniformDAGBucketMachine.typedDepth p))) := by
  rw [fromTopology_run,program_value]
  have h:=topology_depth p t fields
  rw [order_congr G _ _ h]
  rw [UniformDAGBucketMachine.order_length G _ (UniformDAGBucketMachine.typedDepth_bound p)]
  congr 1
  exact congrArg (Tape.tab (G+2)) (funext (fun l=>offset_congr G l _ _ h))

theorem fromTopology_bound {r N G:ℕ} (p:UniformReplayPrint.Program r N G) (t:Tape ℕ)
    (fields:DFTModelCacheDAGDepth.TopologyFields (UniformDAGDepthMachine.rows p) t):
    (run fromTopology (N,(G,t))).valid ∧
    (run fromTopology (N,(G,t))).work ≤
      DFTModelCacheDAGDepth.workBudget N G+57*G+9+workBudget G+7 ∧
    (run fromTopology (N,(G,t))).peak ≤
      max (N+5*G+5) (selectPeak N G) := by
  have hd:=DFTModelCacheDAGDepth.fromTopology_specification N
    (UniformDAGDepthMachine.rows p) t fields (UniformDAGDepthMachine.rows_topological p)
  rw [UniformDAGDepthMachine.rows_length] at hd
  have hb:=program_bound (N,(G,(run DFTModelCacheDAGDepth.fromTopology (N,(G,t))).val))
  rw [fromTopology_run]
  exact ⟨⟨hd.2.1,hb.1⟩,Nat.add_le_add_right (Nat.add_le_add hd.2.2.1 hb.2.1) 7,
    max_le_max hd.2.2.2 hb.2.2⟩

theorem tab_look (n:ℕ) (f:ℕ→ℕ) (i:ℕ) (hi:i<n):
    (Tape.tab n f).look i 0=f i := by
  exact Tape.look_of_lt (Tape.tab n f) 0 hi

/-- The native source execution computes exactly the same output cells as the
charged typed producer on the same actual full-depth bank. -/
theorem native_execution (N G P Q R B n:ℕ) (x:Fin n→ℂ) (s:UniformMachine.State)
    (t:Tape ℕ) (h:UniformDAGBucketMachine.Header G (P+N+1) Q R s)
    (hpc:s.pc=0)
    (copied:∀i,i<G→s.natHeap (P+(N+1+i))=some (t.look (N+1+i) 0))
    (hP:P+N+1+G ≤ Q) (hQ:Q+G*(G+1) ≤ R) (hR:R+G+2 ≤ B)
    (hB:24 ≤ B) (hs:UniformMachine.WordBound B s):
    ∃u ticks,UniformMachine.BoundedExecution UniformDAGBucketMachine.program n x B s ticks u ∧
      ticks ≤ UniformDAGBucketMachine.runtimeBudget G ∧ u.pc=23 ∧
      (∀j,j<(run program (N,(G,t))).val.1.len→
        u.natHeap (Q+j)=some ((run program (N,(G,t))).val.1.look j 0)) ∧
      (∀l,l<G+2→u.natHeap (R+l)=some ((run program (N,(G,t))).val.2.look l 0)) := by
  have dep:UniformDAGBucketMachine.Depths (P+N+1) G (depthValue (N,(G,t))) s:=by
    intro i hi
    simpa only [Nat.add_assoc,depthValue] using copied i hi
  obtain ⟨u,ticks,exe,cost,pc,_header,bank,dir,_dep,_outside,_frame⟩:=
    UniformDAGBucketMachine.execution G (P+N+1) Q R B n x (depthValue (N,(G,t))) s
      h hpc dep hP hQ hR hB hs
  refine ⟨u,ticks,exe,cost,pc,?_,?_⟩
  · rw [program_value]
    intro j hj
    change j<(UniformDAGBucketMachine.order G (depthValue (N,(G,t)))).length at hj
    simpa only [Tape.tab,Tape.look,dite_eq_left hj,List.getElem?_eq_getElem hj,Option.getD_some] using bank j hj
  · rw [program_value]
    intro l hl
    change l<G+2 at hl
    rw [tab_look (G+2) (fun l=>UniformDAGBucketMachine.offset G l (depthValue (N,(G,t)))) l hl]
    exact dir l hl

end
end ExactFourierCircuits.DFTModelCacheBucket
