import DFTModelCacheTopologyDepth
import DFTModelCacheBucketSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucketRaw
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section

abbrev Topology := p w (p w (Ty.a w))
abbrev Input := p (p w w) Topology
abbrev Output := p Topology (p (Ty.a w) (Ty.a w))

/-- Keep the actual K/count/flat5 output while invoking charged depth+bucket code. -/
def argument : Prog false Input DFTModelCacheBucket.Input :=
  .fork (.comp (.atom .fst) (.atom .snd)) (.comp (.atom .snd) (.atom .snd))
def adapter : Prog false Input Output :=
  .fork (.atom .snd) (.comp argument DFTModelCacheBucket.fromTopology)
attribute [local irreducible] DFTModelCacheBucket.fromTopology

theorem adapter_run (a e K G:ℕ) (t:Tape ℕ):
    run adapter ((a,e),(K,(G,t)))=
      let b:=run DFTModelCacheBucket.fromTopology (e,(G,t))
      ⟨((K,(G,t)),b.val),b.work+10,b.peak,b.valid⟩ := by
  simp only [adapter,argument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,
    true_and,and_true,zero_max,max_zero]
  congr 1
  omega

/-- Raw extents only. Topology, depth and stable order are generated internally. -/
def program : Prog false DFTModelCacheTopology.Input Output :=
  .comp (.fork (.atom .id) DFTModelCacheTopology.program) adapter
attribute [local irreducible] DFTModelCacheTopology.program adapter

theorem program_run (a e:ℕ):
    run program (a,e)=
      let top:=run DFTModelCacheTopology.program (a,e)
      let b:=run DFTModelCacheBucket.fromTopology (e,top.val.2)
      ⟨(top.val,b.val),top.work+b.work+13,max top.peak b.peak,top.valid ∧ b.valid⟩ := by
  rw [program,comp_run,fork_run,atom_run]
  simp only [Atom.run,Bill.one,Bill.pass,Bill.pay,true_and,zero_max,max_zero]
  generalize hv:(run DFTModelCacheTopology.program (a,e)).val=v
  rcases v with ⟨K,G,t⟩
  rw [adapter_run]
  simp only [and_true]
  congr 1
  omega

abbrev dag:=DFTModelCacheTopologyDepth.dag
abbrev count:=DFTModelCacheTopologyDepth.count

theorem argument_eq (a e:ℕ) (u:UniformMachine.State) (ticks:ℕ)
    (source:DFTModelCacheTopology.Result a e u ticks):
    (e,(run DFTModelCacheTopology.program (a,e)).val.2)=
      (e,((dag a e).size,(run DFTModelCacheTopology.program (a,e)).val.2.2)) := by
  have size:(dag a e).size=count a e:=DFTModelCacheTopology.typed_count _ _ _
    (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
  congr 1
  exact Prod.ext (source.count.trans size.symm) rfl

theorem topology_fields (a e:ℕ) (u:UniformMachine.State) (ticks:ℕ)
    (source:DFTModelCacheTopology.Result a e u ticks):
    DFTModelCacheDAGDepth.TopologyFields (UniformDAGDepthMachine.rows (dag a e).program)
      (run DFTModelCacheTopology.program (a,e)).val.2.2 := by
  have size:(dag a e).size=count a e:=DFTModelCacheTopology.typed_count _ _ _
    (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
  have copied:DFTModelCacheDAGDepth.CopiedTopology (dag a e).size
      (DFTModelCacheTopology.D (DFTModelCacheTopology.exponent a e))
      (run DFTModelCacheTopology.program (a,e)).val.2.2 u:=by
    simpa only [size,count,DFTModelCacheTopologyDepth.count] using source.copied
  exact DFTModelCacheDAGDepth.fields_of_encoded (dag a e).program _ u source.encoded copied

/-- Exact native typed stable order and directory, without an output-table premise. -/
theorem source_value (a e:ℕ) (u:UniformMachine.State) (ticks:ℕ)
    (source:DFTModelCacheTopology.Result a e u ticks):
    (run program (a,e)).val=
      ((run DFTModelCacheTopology.program (a,e)).val,
       Tape.tab (dag a e).size
         (fun j=>(UniformDAGBucketMachine.order (dag a e).size
           (UniformDAGBucketMachine.typedDepth (dag a e).program))[j]?.getD 0),
       Tape.tab ((dag a e).size+2)
         (fun l=>UniformDAGBucketMachine.offset (dag a e).size l
           (UniformDAGBucketMachine.typedDepth (dag a e).program))) := by
  rw [program_run]
  change ((run DFTModelCacheTopology.program (a,e)).val,
    (run DFTModelCacheBucket.fromTopology (e,(run DFTModelCacheTopology.program (a,e)).val.2)).val)=_
  rw [argument_eq a e u ticks source,
    DFTModelCacheBucket.fromTopology_value (dag a e).program _ (topology_fields a e u ticks source)]

theorem program_value (a e:ℕ):
    (run program (a,e)).val=
      ((run DFTModelCacheTopology.program (a,e)).val,
       Tape.tab (dag a e).size
         (fun j=>(UniformDAGBucketMachine.order (dag a e).size
           (UniformDAGBucketMachine.typedDepth (dag a e).program))[j]?.getD 0),
       Tape.tab ((dag a e).size+2)
         (fun l=>UniformDAGBucketMachine.offset (dag a e).size l
           (UniformDAGBucketMachine.typedDepth (dag a e).program))) := by
  obtain ⟨u,ticks,source⟩:=DFTModelCacheTopology.execution_values a e
  exact source_value a e u ticks source

def workBudget (a e:ℕ):ℕ:=DFTModelCacheTopology.workBudget a e+
  DFTModelCacheDAGDepth.workBudget e (count a e)+57*count a e+
  DFTModelCacheBucket.workBudget (count a e)+29
def peakBudget (a e:ℕ):ℕ:=max (DFTModelCacheTopology.peakBudget a e)
  (max (e+5*count a e+5) (DFTModelCacheBucket.selectPeak e (count a e)))

theorem bucket_budget (a e:ℕ) (u:UniformMachine.State) (ticks:ℕ)
    (source:DFTModelCacheTopology.Result a e u ticks):
    DFTModelCacheMatchingNat.Budget
      (run DFTModelCacheBucket.fromTopology (e,(run DFTModelCacheTopology.program (a,e)).val.2))
      (DFTModelCacheDAGDepth.workBudget e (count a e)+57*count a e+9+
        DFTModelCacheBucket.workBudget (count a e)+7)
      (max (e+5*count a e+5) (DFTModelCacheBucket.selectPeak e (count a e))) := by
  have size:(dag a e).size=count a e:=DFTModelCacheTopology.typed_count _ _ _
    (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
  have h:=DFTModelCacheBucket.fromTopology_bound (dag a e).program _ (topology_fields a e u ticks source)
  rw [←argument_eq a e u ticks source] at h
  rw [size] at h
  exact h

/-- One closed raw producer, retaining the genuine native source execution and
charging topology once, depth once, stable bucketing once. -/
theorem execution (a e:ℕ):∃u ticks,
    DFTModelCacheTopology.Result a e u ticks ∧
    DFTModelCacheMatchingNat.Budget (run program (a,e)) (workBudget a e) (peakBudget a e) := by
  obtain ⟨u,ticks,source,top⟩:=DFTModelCacheTopology.execution a e
  have b:=bucket_budget a e u ticks source
  refine ⟨u,ticks,source,?_⟩
  rw [program_run]
  change (_ ∧ _) ∧ _ ∧ _
  refine ⟨⟨top.1,b.1⟩,?_,?_⟩
  · dsimp only
    unfold workBudget
    have ht:=top.2.1
    have hb:=b.2.1
    omega
  · dsimp only
    exact max_le (top.2.2.trans (le_max_left _ _))
      (b.2.2.trans (le_max_right _ _))

end
end ExactFourierCircuits.DFTModelCacheBucketRaw
