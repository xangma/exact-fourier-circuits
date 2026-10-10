import DFTModelCacheDirectLeafProgram

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDirectLeaf
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Orientations := p (Ty.a Record4) (Ty.a Record4)
def swap : Prog false Record4 Record4 :=
  .fork (.atom .fst) (.fork (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
    (.fork (.comp (.atom .snd) (.atom .fst))
      (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
def reverseIndex : Prog false (p (Ty.a Record4) w) w :=
  integer .sub (integer .sub (.comp (.atom .fst) (.atom .len)) (.atom (.lit 1))) (.atom .snd)
def reverseCell : Prog false (p (Ty.a Record4) w) Record4 :=
  .comp (.comp (.fork (.atom .fst) reverseIndex) (.atom .look)) swap
def transpose : Prog false (Ty.a Record4) (Ty.a Record4) := .tab (.atom .len) reverseCell
def orientationSeed : Prog false Input (p Input (Ty.a Record4)) :=
  .fork (.atom .id) forward
def orientationBody : Prog false (p Input (Ty.a Record4)) Orientations :=
  .fork (.atom .snd) (.comp (.atom .snd) transpose)
/-- Both record orientations are materialized by charged loops; no descriptor
tape is an input to this closed width/offset/coefficient-base producer. -/
def orientations : Prog false Input Orientations := .comp orientationSeed orientationBody

attribute [local irreducible] forward transpose

theorem swap_run (q : UniformTransposeDescriptorMachine.Record) :
    run swap (encode q)=⟨encode q.transpose,17,0,True⟩ := by
  simp [swap,encode,UniformTransposeDescriptorMachine.Record.transpose,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem reverseCell_run (t : Tape Record4.T) (j : ℕ) :
    run reverseCell (t,j)=⟨((t.look (t.len-1-j) Record4.blank).1,
      ((t.look (t.len-1-j) Record4.blank).2.2.1,
        ((t.look (t.len-1-j) Record4.blank).2.1,
          (t.look (t.len-1-j) Record4.blank).2.2.2))),33,max t.len 1,True⟩ := by
  simp [reverseCell,reverseIndex,integer,swap,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  omega

theorem transpose_run (t : Tape Record4.T) :
    run transpose t=(Bill.tab t.len Record4.blank (fun j=>run reverseCell (t,j))).pay 2 t.len := by
  simp [transpose,run,Code.run,Atom.run,Bill.word,Bill.pass,Bill.pay]
  omega

theorem transpose_value (qs : List UniformTransposeDescriptorMachine.Record) :
    (run transpose (DFTModelCacheTraversal.ofList (qs.map encode))).val=
      DFTModelCacheTraversal.ofList ((qs.reverse.map UniformTransposeDescriptorMachine.Record.transpose).map encode) := by
  rw[transpose_run]
  change (Bill.tab _ Record4.blank _).val=_
  rw[ModelEquivalenceInterpreter.tab_value]
  apply DFTModelCacheTraversal.tape_ext _ _ Record4.blank (by simp[DFTModelCacheTraversal.ofList,Tape.tab])
  intro j hj
  have hj' : j < qs.length := by simpa[DFTModelCacheTraversal.ofList,Tape.tab] using hj
  rw[Tape.look_of_lt _ _ hj]
  change (run reverseCell (DFTModelCacheTraversal.ofList (qs.map encode),j)).val=_
  rw[reverseCell_run]
  have ix : qs.length-1-j < (qs.map encode).length := by simp;omega
  have out : j < ((qs.reverse.map UniformTransposeDescriptorMachine.Record.transpose).map encode).length := by simpa using hj'
  simp only [DFTModelCacheTraversal.ofList,List.length_map]
  rw[Tape.look_of_lt _ _ ix]
  rw[Tape.look_of_lt _ _ out]
  simp only [List.getElem_map,List.getElem_reverse]
  rfl

theorem transpose_valid (t : Tape Record4.T) : (run transpose t).valid := by
  rw[transpose_run]
  exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun j _=>by rw[reverseCell_run];trivial)

theorem transpose_work (t : Tape Record4.T) : (run transpose t).work=37*t.len+4 := by
  rw[transpose_run]
  change (Bill.tab t.len Record4.blank _).work+2=_
  rw[ModelEquivalenceInterpreter.tab_work]
  have sum : (∑j∈Finset.range t.len,(run reverseCell (t,j)).work)=33*t.len := by
    trans ∑_j∈Finset.range t.len,33
    · apply Finset.sum_congr rfl;intro j _;exact congrArg Bill.work (reverseCell_run t j)
    · simp [Nat.mul_comm]
  rw[sum]
  omega

theorem transpose_peak (t : Tape Record4.T) : (run transpose t).peak≤ max t.len 1 := by
  rw[transpose_run]
  change max (Bill.tab t.len Record4.blank _).peak t.len≤_
  rw[ModelEquivalenceInterpreter.tab_peak]
  apply max_le
  · apply max_le (le_max_left _ _)
    apply Finset.sup_le
    intro j _;rw[reverseCell_run]
  · exact le_max_left _ _

theorem orientations_run (v o K : ℕ) :
    run orientations (v,(o,K))=
      ((run forward (v,(o,K))).pass (fun f=>(run transpose f).pass
        (fun t=>Bill.one (f,t)))).pay 6 0 := by
  simp [orientations,orientationSeed,orientationBody,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  omega

theorem orientations_value (v o K : ℕ) :
    (run orientations (v,(o,K))).val=
      (DFTModelCacheTraversal.ofList ((UniformTransposeDescriptorMachine.leafRecords v o K).map encode),
        DFTModelCacheTraversal.ofList (((UniformTransposeDescriptorMachine.leafRecords v o K).reverse.map
          UniformTransposeDescriptorMachine.Record.transpose).map encode)) := by
  rw[orientations_run]
  change ((run forward (v,(o,K))).val,(run transpose (run forward (v,(o,K))).val).val)=_
  rw[forward_value,transpose_value]

theorem orientations_valid (v o K : ℕ) : (run orientations (v,(o,K))).valid := by
  rw[orientations_run]
  exact ⟨forward_valid _ _ _,transpose_valid _,trivial⟩

theorem orientations_work (v o K : ℕ) :
    (run orientations (v,(o,K))).work≤1000*(v+1)^3 := by
  rw[orientations_run]
  change (run forward (v,(o,K))).work+
    ((run transpose (run forward (v,(o,K))).val).work+1)+6≤_
  rw[transpose_work]
  have fw:=forward_work v o K
  have len:(run forward (v,(o,K))).val.len≤(v+1)^2 := by
    rw[forward_value]
    simpa[DFTModelCacheTraversal.ofList,←records_native] using records_length_bound v o K
  have cube : (v+1)^2≤(v+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have positive : 0<(v+1)^3 := pow_pos (by omega) 3
  nlinarith

theorem orientations_peak (v o K : ℕ) :
    (run orientations (v,(o,K))).peak≤o+K+2*(v+1)^2 := by
  rw[orientations_run]
  change max (max (run forward (v,(o,K))).peak
    (max (run transpose (run forward (v,(o,K))).val).peak 0)) 0≤_
  simp only [max_zero]
  apply max_le (forward_peak _ _ _)
  have tp:=transpose_peak (run forward (v,(o,K))).val
  have len:(run forward (v,(o,K))).val.len≤(v+1)^2 := by
    rw[forward_value]
    simpa[DFTModelCacheTraversal.ofList,←records_native] using records_length_bound v o K
  have positive : 0<(v+1)^2 := pow_pos (by omega) 2
  exact tp.trans (max_le (by nlinarith) (by nlinarith))

end
end ExactFourierCircuits.DFTModelCacheDirectLeaf
