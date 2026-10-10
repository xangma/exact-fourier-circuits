import DFTModelCacheDAGDepthProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDAGDepth
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformDAGDepthMachine (Row Topological evaluate)
noncomputable section
attribute [local irreducible] step program

theorem initialTape_run (N : ℕ) (qs : Tape Row3.T) :
    run initialTape (N,qs)=⟨Tape.tab (N+1+qs.len) (fun _=>0),
      5*(N+1+qs.len)+14,N+1+qs.len,True⟩ := by
  have hs : run span (N,qs)=⟨N+1+qs.len,11,N+1+qs.len,True⟩ := by
    simp [span,nat,inputCount,gateCount,run,Code.run,Atom.run,NOp.run,
      Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [initialTape]
  change ((run span (N,qs)).pass (fun n=>Bill.tab n (0:ℕ)
    (fun _=>Bill.word 0))).pay 1 0 = _
  rw [hs]
  simp only [Bill.word,Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_value,ModelEquivalenceInterpreter.tab_work,
    ModelEquivalenceInterpreter.tab_peak]
  simp [ModelEquivalenceInterpreter.tab_valid]
  omega

def iterations (N : ℕ) (qs : Tape Row3.T) (j : ℕ) : Bill (Tape ℕ) :=
  Bill.steps (Tape.tab (N+1+qs.len) (fun _=>0))
    (fun i d=>run step ((N,qs),(i,d))) j

theorem iterations_length (N : ℕ) (qs : Tape Row3.T) (j : ℕ) :
    (iterations N qs j).val.len=N+1+qs.len := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    change (run step ((N,qs),(j,(iterations N qs j).val))).val.len=_
    rw [step_run]
    exact ih

theorem loop_billing (N G : ℕ) (b : Bill (Tape ℕ)) :
    (((⟨G,3,G,True⟩ : Bill ℕ).pass (fun _=>
      (⟨Tape.tab (N+1+G) (fun _=>0),5*(N+1+G)+14,N+1+G,True⟩ : Bill (Tape ℕ)).pass
        (fun _=>b))).pay 1 0)=
      ⟨b.val,b.work+5*(N+1+G)+18,max (N+1+G) b.peak,b.valid⟩ := by
  simp only [Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;>omega

theorem program_run (N : ℕ) (qs : Tape Row3.T) : run program (N,qs)=
    ⟨(iterations N qs qs.len).val,(iterations N qs qs.len).work+5*(N+1+qs.len)+18,
      max (N+1+qs.len) (iterations N qs qs.len).peak,(iterations N qs qs.len).valid⟩ := by
  rw [program]
  change ((run gateCount (N,qs)).pass (fun n=>(run initialTape (N,qs)).pass
    (fun d=>Bill.steps d (fun i d=>run step ((N,qs),(i,d))) n))).pay 1 0 = _
  have hc : run gateCount (N,qs)=⟨qs.len,3,qs.len,True⟩ := by
    simp [gateCount,run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  rw [hc,initialTape_run]
  exact loop_billing N qs.len (iterations N qs qs.len)

theorem rowsTape_get (qs : List Row) (j : ℕ) (hj:j<qs.length) :
    (rowsTape qs).look j (0,(0,0))=encode qs[j] := by
  simp [rowsTape,Tape.look,hj]

theorem rowValue_encode (q : Row) (d : Tape ℕ) :
    rowValue (encode q) d=q.depth (fun i=>d.look i 0) := by
  cases q <;>simp [rowValue,encode,Row.opcode,Row.left,Row.right,Row.depth]

theorem tab_update (M i v : ℕ) (f : ℕ→ℕ) :
    (Tape.tab M f).set i v=Tape.tab M (Function.update f i v) := by
  unfold Tape.tab Tape.set
  congr 1
  funext j
  simp [Function.update]

/-- Every operand read by this recurrence is a genuine earlier port, inside
the allocated table. Scale rows do not read their unused right field. -/
theorem refs_inBounds {N : ℕ} {qs : List Row} (ht : Topological N qs)
    (j : ℕ) (hj:j<qs.length) (a : ℕ) (ha:a∈qs[j].refs) :
    a<N+1+qs.length := (ht ⟨j,hj⟩ a ha).trans_le (by omega)

theorem row_depth_tab {N : ℕ} {qs : List Row} (ht : Topological N qs)
    (j : ℕ) (hj:j<qs.length) (f : ℕ→ℕ) :
    qs[j].depth (fun a=>(Tape.tab (N+1+qs.length) f).look a 0)=qs[j].depth f := by
  have h:=refs_inBounds ht j hj
  generalize he:qs[j]=q at h ⊢
  cases q with
  | add a b | sub a b=>
    have ha:=h a (by simp [Row.refs])
    have hb:=h b (by simp [Row.refs])
    simp [Row.depth,Tape.look,Tape.tab,ha,hb]
  | scale a=>
    have ha:=h a (by simp [Row.refs])
    simp [Row.depth,Tape.look,Tape.tab,ha]

theorem iterations_value (N : ℕ) (qs : List Row) (ht : Topological N qs)
    (j : ℕ) (hj:j≤qs.length) :
    (iterations N (rowsTape qs) j).val=
      Tape.tab (N+1+qs.length) (evaluate (N+1) (qs.take j) (fun _=>0)) := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    have hlt:j<qs.length:=by omega
    have ih:=ih (by omega)
    change (run step ((N,rowsTape qs),(j,(iterations N (rowsTape qs) j).val))).val=_
    rw [step_run,ih,rowsTape_get qs j hlt,rowValue_encode,row_depth_tab ht j hlt,
      tab_update,List.take_succ_eq_append_getElem hlt,UniformDAGDepthMachine.evaluate_append]
    have hl:(qs.take j).length=j:=by simp [List.length_take,min_eq_left (by omega:j≤qs.length)]
    rw [hl]
    rfl

theorem program_value (N : ℕ) (qs : List Row) (ht : Topological N qs) :
    (run program (N,rowsTape qs)).val=
      Tape.tab (N+1+qs.length) (evaluate (N+1) qs (fun _=>0)) := by
  rw [program_run]
  simpa only [rowsTape,List.take_length] using iterations_value N qs ht qs.length (le_refl _)

theorem typed_value {r N G : ℕ} (p : UniformReplayPrint.Program r N G)
    (i : Fin (N+1+G)) :
    (run program (N,rowsTape (UniformDAGDepthMachine.rows p))).val.look i.val 0=
      UniformToeplitzCrossDAG.runDepth p (fun _=>0) i := by
  rw [program_value N _ (UniformDAGDepthMachine.rows_topological p)]
  have hi:i.val<N+1+(UniformDAGDepthMachine.rows p).length:=by
    simpa only [UniformDAGDepthMachine.rows_length] using i.isLt
  rw [Tape.look_of_lt _ _ hi]
  exact UniformDAGDepthMachine.evaluate_typed p i

end
end ExactFourierCircuits.DFTModelCacheDAGDepth
