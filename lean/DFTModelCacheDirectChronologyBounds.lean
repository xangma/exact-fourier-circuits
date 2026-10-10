import DFTModelCacheDirectChronologyCorrect

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectChronology
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDirectLeaf
open UniformTransposeDescriptorMachine UniformDirectLeafCacheChronology
open scoped BigOperators
noncomputable section

theorem argV_run (v o t K : ℕ) (q : Record) :
    run argV ((v,(o,(t,K))),encode q)=⟨v,3,0,True⟩ := by
  simp [argV,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem argO_run (v o t K : ℕ) (q : Record) :
    run argO ((v,(o,(t,K))),encode q)=⟨o,5,0,True⟩ := by
  simp [argO,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem argT_run (v o t K : ℕ) (q : Record) :
    run argT ((v,(o,(t,K))),encode q)=⟨t,7,0,True⟩ := by
  simp [argT,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem targetIndex_run (v o t K : ℕ) (q : Record) :
    run targetIndex ((v,(o,(t,K))),encode q)=⟨q.dest-o,13,q.dest-o,True⟩ := by
  simp [targetIndex,dest,argO,integer,encode,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
theorem kind_run (v o t K : ℕ) (q : Record) :
    run kind ((v,(o,(t,K))),encode q)=⟨q.kind,3,0,True⟩ := by
  simp [kind,encode,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem source_run (v o t K : ℕ) (q : Record) :
    run source ((v,(o,(t,K))),encode q)=⟨q.source,7,0,True⟩ := by
  simp [source,encode,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem literal_run {s : Ty} (c : ℕ) (x : s.T) :
    run (.atom (.lit c) : Prog false s w) x=⟨c,1,c,True⟩ := rfl
theorem snd_run {s t : Ty} (x : s.T) (y : t.T) :
    run (.atom .snd : Prog false (p s t) t) (x,y)=⟨y,1,0,True⟩ := rfl

attribute [local irreducible] argV argO argT kind source targetIndex

theorem rowTime_value (v o t K : ℕ) (q : Record) :
    (run rowTime ((v,(o,(t,K))),encode q)).val=t+rowOffset v (q.dest-o) := by
  simp only [rowTime,integer_value,targetIndex_run v o t K q,
    argV_run v o t K q,argT_run v o t K q,literal_run,NOp.run,Bill.word]
  rfl

theorem rowTime_peak (v o t K : ℕ) (q : Record) (hd:q.dest-o≤v) :
    (run rowTime ((v,(o,(t,K))),encode q)).peak≤t+100*(v+1)^2 := by
  have hsub:=Nat.sub_le v 1
  have hm : v*(v-1)≤(v+1)^2 := by nlinarith
  have hm' : (q.dest-o)*(q.dest-o+1)≤(v+1)^2 := by nlinarith
  have hm'' := Nat.sub_le (v*(v-1)) ((q.dest-o)*(q.dest-o+1))
  have hl := Nat.sub_le (v-1) (q.dest-o)
  have large : 100*v+100≤100*(v+1)^2 := by nlinarith
  simp only [rowTime,integer_peak,integer_value,targetIndex_run v o t K q,
    argV_run v o t K q,argT_run v o t K q,
    literal_run,NOp.run,Bill.word,max_le_iff]
  omega

attribute [local irreducible] rowTime

theorem stamp_peak (v o t K : ℕ) (q : Record)
    (hd:q.dest-o≤v) (hs:q.source-o≤v) :
    (run stamp ((v,(o,(t,K))),encode q)).peak≤t+100*(v+1)^2 := by
  have rp:=rowTime_peak v o t K q hd
  have sp : (run (.atom .snd : Prog false StampInput Record4)
      ((v,(o,(t,K))),encode q)).peak=0 := rfl
  have hsub:=Nat.sub_le v 1
  have hm : v*(v-1)≤(v+1)^2 := by nlinarith
  have hm' : (q.dest-o)*(q.dest-o+1)≤(v+1)^2 := by nlinarith
  have hm'' := Nat.sub_le (v*(v-1)) ((q.dest-o)*(q.dest-o+1))
  have hl := Nat.sub_le (v-1) (q.dest-o)
  have large : 100*v+100≤100*(v+1)^2 := by nlinarith
  simp only [stamp,fork_peak,stampTime,ifz_peak,integer_peak,
    nativeKind,integer_value,rowTime_value v o t K q,kind_run v o t K q,
    source_run v o t K q,argO_run v o t K q,literal_run,NOp.run,Bill.word,rowOffset]
  by_cases h:q.kind=0 <;>
    simp only [h,↓reduceIte,max_le_iff] <;>
    omega

theorem record_fields (v o K : ℕ) (q : Record) (hq:q∈records o K v) :
    q.dest-o≤v ∧ q.source-o≤v := by
  induction v with
  | zero=>simp [records] at hq
  | succ v ih=>
    rcases List.mem_append.mp hq with hq|hq
    · simp only [rowRecords,List.mem_cons,List.mem_ofFn] at hq
      rcases hq with rfl|⟨j,rfl⟩
      · simp
      · have hj:=j.isLt
        simp only [Nat.add_sub_cancel_left]
        omega
    · have h:=ih hq
      exact ⟨Nat.le_trans h.1 (Nat.le_succ _),Nat.le_trans h.2 (Nat.le_succ _)⟩

theorem annotate_work (v o t K : ℕ) (qs : List Record) :
    (run annotate ((v,(o,(t,K))),DFTModelCacheTraversal.ofList (qs.map encode))).work≤
      316*qs.length+6 := by
  rw [annotate_run]
  simp only [DFTModelCacheTraversal.ofList,List.length_map,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_work]
  have sum : (∑j∈Finset.range qs.length,
      (run cell (((v,(o,(t,K))),DFTModelCacheTraversal.ofList (qs.map encode)),j)).work)≤312*qs.length := by
    calc
      _≤∑_j∈Finset.range qs.length,312 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [cell_run]
        have h:j<(qs.map encode).length := by simpa using Finset.mem_range.mp hj
        change (run stamp ((v,(o,(t,K))),_)).work+12≤_
        simp only [DFTModelCacheTraversal.ofList]
        rw [Tape.look_of_lt _ _ h]
        dsimp only
        rw [List.getElem_map]
        exact Nat.add_le_add_right (stamp_work _ _ _ _ _) 12
      _=_ := by simp [Nat.mul_comm]
  dsimp only [DFTModelCacheTraversal.ofList] at sum
  omega

theorem program_work (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).work≤600*(v+1)^3+27 := by
  rw [program_run]
  change (run forward (v,(o,K))).work+
    (run annotate ((v,(o,(t,K))),(run forward (v,(o,K))).val)).work+15≤_
  have h:=forward_work v o K
  rw [forward_value]
  have a:=annotate_work v o t K (leafRecords v o K)
  have l:=records_length_bound v o K
  rw [records_native] at l
  have cube : (v+1)^2≤(v+1)^3 := by nlinarith [Nat.zero_le (v*v*v)]
  nlinarith

theorem annotate_peak (v o t K : ℕ) :
    (run annotate ((v,(o,(t,K))),DFTModelCacheTraversal.ofList
      ((leafRecords v o K).map encode))).peak≤t+100*(v+1)^2 := by
  rw [annotate_run]
  simp only [DFTModelCacheTraversal.ofList,List.length_map,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_peak]
  have l:=records_length_bound v o K
  rw [records_native] at l
  apply max_le
  · apply max_le (by omega)
    apply Finset.sup_le
    intro j hj
    rw [cell_run]
    have h:j<((leafRecords v o K).map encode).length := by simpa using Finset.mem_range.mp hj
    change max (run stamp ((v,(o,(t,K))),_)).peak 0≤_
    rw [max_zero]
    rw [Tape.look_of_lt _ _ h]
    dsimp only
    rw [List.getElem_map]
    have hj' : j<(leafRecords v o K).length := Finset.mem_range.mp hj
    have q:=record_fields v o K ((leafRecords v o K)[j]'hj')
      (by rw [records_native];exact List.getElem_mem _)
    exact stamp_peak _ _ _ _ _ q.1 q.2
  · omega

theorem program_peak (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).peak≤o+K+t+100*(v+1)^2 := by
  rw [program_run]
  change max (max (run forward (v,(o,K))).peak
    (run annotate ((v,(o,(t,K))),(run forward (v,(o,K))).val)).peak) 0≤_
  rw [max_zero,forward_value]
  have f:=forward_peak v o K
  have a:=annotate_peak v o t K
  exact max_le (by omega) (by omega)

theorem specification (v o t K : ℕ) :
    (run program (v,(o,(t,K)))).val=values v o t K ∧
    (run program (v,(o,(t,K)))).valid ∧
    (run program (v,(o,(t,K)))).work≤600*(v+1)^3+27 ∧
    (run program (v,(o,(t,K)))).peak≤o+K+t+100*(v+1)^2 :=
  ⟨program_value _ _ _ _,program_valid _ _ _ _,program_work _ _ _ _,program_peak _ _ _ _⟩

end
end ExactFourierCircuits.DFTModelCacheDirectChronology
