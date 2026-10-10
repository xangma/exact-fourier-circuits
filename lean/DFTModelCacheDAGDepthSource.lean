import DFTModelCacheDAGDepthTopology

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDAGDepth
open OAI.PowerSaving OAI.PowerSaving.RAM
noncomputable section

/-- The typed input is the same ordinary integer tape produced by the source
machine; this condition concerns its input fields, never its depth output. -/
def CopiedTopology (G d : ℕ) (t : Tape ℕ) (s : UniformMachine.State) : Prop :=
  5*G≤t.len ∧ ∀i,i<5*G→s.natHeap (d+i)=some (t.look i 0)

theorem fields_of_encoded {r N G d : ℕ} (p : UniformReplayPrint.Program r N G)
    (t : Tape ℕ) (s : UniformMachine.State)
    (encoded : UniformDAGDepthMachine.EncodedTape p d s)
    (copied : CopiedTopology G d t s) :
    TopologyFields (UniformDAGDepthMachine.rows p) t := by
  have ht:=UniformDAGDepthMachine.tape_of_encoded encoded
  refine ⟨?_,?_⟩
  · simpa only [UniformDAGDepthMachine.rows_length] using copied.1
  · intro j
    have hj:j.val<G:=by simpa only [UniformDAGDepthMachine.rows_length] using j.isLt
    have hs:=ht j
    refine ⟨?_,?_,?_⟩
    · exact Option.some.inj ((copied.2 (5*j.val) (by omega)).symm.trans hs.1)
    · exact Option.some.inj ((copied.2 (5*j.val+1) (by omega)).symm.trans hs.2.1)
    · exact Option.some.inj ((copied.2 (5*j.val+2) (by omega)).symm.trans hs.2.2)

/-- Exact correspondence to the native typed DAG, from its genuine five-field
input tape. Earlier-reference bounds follow from the typed constructors. -/
theorem fromTopology_typed {r N G : ℕ} (p : UniformReplayPrint.Program r N G)
    (t : Tape ℕ) (fields : TopologyFields (UniformDAGDepthMachine.rows p) t)
    (i : Fin (N+1+G)) :
    (run fromTopology (N,(G,t))).val.look i.val 0=
      UniformToeplitzCrossDAG.runDepth p (fun _=>0) i := by
  rw [fromTopology_run]
  have hd:=decodedTopology_eq (UniformDAGDepthMachine.rows p) t fields
  rw [UniformDAGDepthMachine.rows_length] at hd
  rw [hd]
  exact typed_value p i

theorem fromTopology_native {r N G d : ℕ} (p : UniformReplayPrint.Program r N G)
    (t : Tape ℕ) (s : UniformMachine.State)
    (encoded : UniformDAGDepthMachine.EncodedTape p d s)
    (copied : CopiedTopology G d t s) :
    (run fromTopology (N,(G,t))).valid ∧
    (run fromTopology (N,(G,t))).work≤workBudget N G+57*G+9 ∧
    (run fromTopology (N,(G,t))).peak≤N+5*G+5 ∧
    ∀i:Fin (N+1+G),(run fromTopology (N,(G,t))).val.look i.val 0=
      UniformToeplitzCrossDAG.runDepth p (fun _=>0) i := by
  have fields:=fields_of_encoded p t s encoded copied
  have h:=fromTopology_specification N (UniformDAGDepthMachine.rows p) t fields
    (UniformDAGDepthMachine.rows_topological p)
  rw [UniformDAGDepthMachine.rows_length] at h
  exact ⟨h.2.1,h.2.2.1,h.2.2.2,fromTopology_typed p t fields⟩

theorem fromTopology_cross_depth (K a e : ℕ)
    (ha:a≤UniformRadixTwoDAG.width K) (he:e≤UniformRadixTwoDAG.width K)
    (t : Tape ℕ)
    (fields : TopologyFields
      (UniformDAGDepthMachine.rows (UniformToeplitzCrossDAG.crossDAG K a e ha he).program) t)
    (i : Fin (e+1+(UniformToeplitzCrossDAG.crossDAG K a e ha he).size)) :
    (run fromTopology (e,((UniformToeplitzCrossDAG.crossDAG K a e ha he).size,t))).val.look i.val 0≤8*K+6 := by
  rw [fromTopology_typed _ t fields]
  exact UniformToeplitzCrossDAG.crossDAG_depth K a e ha he i

end
end ExactFourierCircuits.DFTModelCacheDAGDepth
