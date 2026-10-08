import UniformCrossShearTableMachine
import UniformGreedyColorMachine
import UniformBoundedAssembly

set_option autoImplicit false

/-! Actual depth slices of the printed cross DAG.  Degrees count indexed
occurrences, including repeated operands and zero coefficients.  The active
schedule is bounded by constructor depth, independently of its gate count. -/
namespace ExactFourierCircuits.UniformCrossDepthReplayPreparation
open UniformReplayPrint UniformDAGLayers UniformLayeredReplay UniformColoring
open UniformToeplitzCrossDAG OAI.ExactFourier UniformMachine

variable {r n t : ℕ}

def bucket (p : UniformReplayPrint.Program r n t) (enabled : Bool) (d : ℕ) :
    List (ShearCode ℕ r) :=
  (natSweep p enabled).filter (fun s => decide (natLevel p s.dst=d))

def activeBuckets (p : UniformReplayPrint.Program r n t) (enabled : Bool) (H : ℕ) :
    List (List (ShearCode ℕ r)) :=
  List.ofFn (fun d : Fin (H+1) => bucket p enabled d.val)

lemma filter_later (W : List (ShearCode ℕ r)) (level : ℕ→ℕ) (a d : ℕ)
    (h : a<d) :
    (W.filter (fun s => decide (a<level s.dst))).filter
      (fun s => decide (level s.dst=d)) =
      W.filter (fun s => decide (level s.dst=d)) := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    by_cases hd : level s.dst=d
    · simp [hd,h,ih]
    · by_cases ha : a<level s.dst <;> simp [hd,ha,ih]

lemma bucketsFrom_ofFn (start count : ℕ) (level : ℕ→ℕ)
    (W : List (ShearCode ℕ r)) :
    bucketsFrom start count level W =
      List.ofFn (fun i : Fin count =>
        W.filter (fun s => decide (level s.dst=start+i.val))) := by
  induction count generalizing start W with
  | zero => simp [bucketsFrom]
  | succ c ih =>
    rw [bucketsFrom,List.ofFn_succ]
    simp only [Fin.val_zero,Nat.add_zero]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    rw [filter_later _ _ start (start+1+i.val) (by omega)]
    simp only [Fin.val_succ]
    congr 2
    funext s
    congr 1
    congr 1
    omega

lemma depthBuckets_ofFn (p : UniformReplayPrint.Program r n t) (enabled : Bool) (H : ℕ) :
    depthBuckets (natSweep p enabled) (natLevel p) H =
      List.ofFn (fun d : Fin (H+1) =>
        (depthOrdered (natSweep p enabled) (natLevel p)).filter
          (fun s => decide (natLevel p s.dst=d.val))) := by
  simpa [depthBuckets] using bucketsFrom_ofFn 0 (H+1) (natLevel p)
    (depthOrdered (natSweep p enabled) (natLevel p))

lemma bucket_onLevel (p : UniformReplayPrint.Program r n t) (enabled : Bool) (d : ℕ) :
    OnLevel (bucket p enabled d) (natLevel p) d := by
  intro s hs
  have hm := List.mem_filter.mp hs
  have he := of_decide_eq_true hm.2
  exact ⟨he,by simpa only [← he] using natSweep_depth p enabled s hm.1⟩

lemma bucket_degree {a : ℕ} (D : DAG r n a) (enabled : Bool) (d delta : ℕ)
    (hdelta : 2≤delta) (huse : ∀ v,physicalUseCount D v≤delta) :
    DegreeBound (printedEdges (bucket D.program enabled d)) delta := by
  have hc (P : ShearCode ℕ r→Bool) :
      (bucket D.program enabled d).countP P≤(natSweep D.program enabled).countP P :=
    List.filter_sublist.countP_le
  apply degree_of_level _ (natLevel D.program) (bucket_onLevel D.program enabled d)
  · intro v
    change (Finset.univ.filter (fun i : Fin (bucket D.program enabled d).length =>
      ((bucket D.program enabled d).get i).dst=v)).card≤delta
    rw [uses_card]
    exact (hc _).trans ((natSweep_dst_count D.program enabled v).trans hdelta)
  · intro v
    change (Finset.univ.filter (fun i : Fin (bucket D.program enabled d).length =>
      ((bucket D.program enabled d).get i).src=v)).card≤delta
    rw [uses_card]
    exact (hc _).trans ((natSweep_physical_src_count D enabled v).trans (huse v))

lemma ofFn_nat {α : Type} (c : ℕ) (f : ℕ→α) :
    List.ofFn (fun i : Fin c=>f i.val)=(List.range c).map f := by
  apply List.ext_getElem <;> simp

lemma activeBuckets_length (p : UniformReplayPrint.Program r n t) (enabled : Bool) (H : ℕ) :
    (activeBuckets p enabled H).length=H+1 := by simp [activeBuckets]

noncomputable section

lemma ofFn_action_congr {c : ℕ} (bank : Fin r→ℂ)
    (F G : Fin c→List (ShearCode ℕ r))
    (h : ∀ i v,runShears ((F i).map (ShearCode.eval bank)) v=
      runShears ((G i).map (ShearCode.eval bank)) v) (v : ℕ→ℂ) :
    runShears ((List.ofFn F).flatten.map (ShearCode.eval bank)) v=
      runShears ((List.ofFn G).flatten.map (ShearCode.eval bank)) v := by
  induction c generalizing v with
  | zero => simp
  | succ c ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.flatten_cons,List.flatten_cons,
      List.map_append,List.map_append,runShears_append,runShears_append,h 0]
    exact ih (fun i=>F i.succ) (fun i=>G i.succ) (fun i=>h i.succ) _

theorem activeBuckets_action (p : UniformReplayPrint.Program r n t)
    (bank : Fin r→ℂ) (enabled : Bool) (H : ℕ)
    (hb : ∀ s∈natSweep p enabled,natLevel p s.dst≤H) (v : ℕ→ℂ) :
    runShears ((activeBuckets p enabled H).flatten.map (ShearCode.eval bank)) v=
      runShears ((natSweep p enabled).map (ShearCode.eval bank)) v := by
  have hs (d : Fin (H+1)) :
      (bucket p enabled d.val).Perm
        ((depthOrdered (natSweep p enabled) (natLevel p)).filter
          (fun s=>decide (natLevel p s.dst=d.val))) :=
    (depthOrdered_perm _ _).symm.filter _
  have he := ofFn_action_congr bank
    (fun d : Fin (H+1)=>bucket p enabled d.val)
    (fun d : Fin (H+1)=>(depthOrdered (natSweep p enabled) (natLevel p)).filter
      (fun s=>decide (natLevel p s.dst=d.val)))
    (fun d w=>run_perm bank (hs d) (bucket_onLevel p enabled d.val).safe w) v
  change runShears ((activeBuckets p enabled H).flatten.map (ShearCode.eval bank)) v=_ at he
  rw [← depthBuckets_ofFn,depthBuckets_flatten _ _ H hb] at he
  exact he.trans (sorted_natSweep_action p bank enabled v)

theorem orderedSweep_action (p : UniformReplayPrint.Program r n t)
    (bank : Fin r→ℂ) (enabled : Bool) (v : ℕ→ℂ) :
    runShears ((UniformCrossShearTableMachine.orderedSweep p enabled).map
      (ShearCode.eval bank)) v=
      runShears ((natSweep p enabled).map (ShearCode.eval bank)) v := by
  rw [UniformCrossShearTableMachine.orderedSweep_buckets]
  have hf : (List.range (t+1)).flatMap (fun d=>bucket p enabled d)=
      (activeBuckets p enabled t).flatten := by
    rw [activeBuckets,ofFn_nat]
    rfl
  change runShears (((List.range (t+1)).flatMap (fun d=>bucket p enabled d)).map _) v=_
  rw [hf]
  apply activeBuckets_action p bank enabled t
  intro s hs
  have hn := natSweep_bounds p enabled s hs
  have eq : n+1+(s.dst-(n+1))=s.dst := by omega
  have bound := UniformDAGBucketMachine.typedDepth_bound p
    (s.dst-(n+1)) (by omega)
  simpa only [UniformDAGBucketMachine.typedDepth,eq] using bound

end

/-- Eleven indexed colors for each actual constructor depth. -/
def activeLayers (p : UniformReplayPrint.Program r n t) (enabled : Bool) (H : ℕ) :
    List (List (ShearCode ℕ r)) := coloredBuckets (activeBuckets p enabled H) 6

lemma activeLayers_length (p : UniformReplayPrint.Program r n t) (enabled : Bool) (H : ℕ) :
    (activeLayers p enabled H).length=11*(H+1) := by
  rw [activeLayers,coloredBuckets_length,activeBuckets_length]
  omega

lemma active_bucket_degree {a H : ℕ} (D : DAG r n a) (enabled : Bool)
    (huse : ∀v,physicalUseCount D v≤6) :
    ∀W∈activeBuckets D.program enabled H,DegreeBound (printedEdges W) 6 ∧ LevelSafe W := by
  intro W hW
  obtain ⟨d,rfl⟩ := List.mem_ofFn.mp hW
  exact ⟨bucket_degree D enabled d.val 6 (by omega) huse,
    (bucket_onLevel D.program enabled d.val).safe⟩

lemma activeLayers_matching {a H : ℕ} (D : DAG r n a) (enabled : Bool)
    (huse : ∀v,physicalUseCount D v≤6) :
    ∀W∈activeLayers D.program enabled H,Matching W := by
  intro W hW
  obtain ⟨V,hV,hW⟩ := List.mem_flatMap.mp hW
  exact colorBlocks_matching V 6 (active_bucket_degree D enabled huse V hV).1
    (by omega) W hW

noncomputable section

theorem activeLayers_action {a H : ℕ} (D : DAG r n a) (bank : Fin r→ℂ)
    (enabled : Bool) (hD : DepthBound D H) (huse : ∀v,physicalUseCount D v≤6) (v : ℕ→ℂ) :
    runShears ((activeLayers D.program enabled H).flatten.map (ShearCode.eval bank)) v=
      runShears ((natSweep D.program enabled).map (ShearCode.eval bank)) v := by
  rw [activeLayers,coloredBuckets_action bank _ 6 (by omega)
    (active_bucket_degree D enabled huse)]
  exact activeBuckets_action D.program bank enabled H (natSweep_depthBound D enabled hD) v

end

/-- The six exact dirty-replay phases, using the actual stable depth slices. -/
def activeReplay {a : ℕ} (D : DAG r n a) (H : ℕ) : List (List (ShearCode ℕ r)) :=
  let W := activeLayers D.program true H
  let V := activeLayers D.program false H
  let B := colorBlocks (natBroadcast D true) 6
  let Z := colorBlocks (natBroadcast D false) 6
  W ++ B ++ reverseLayers W ++ V ++ reverseLayers Z ++ reverseLayers V

lemma activeReplay_length {a : ℕ} (D : DAG r n a) (H : ℕ) :
    (activeReplay D H).length=11*(4*(H+1)+2) := by
  simp only [activeReplay,List.length_append,reverseLayers_length,
    activeLayers_length,colorBlocks_length]
  omega

lemma activeReplay_matching {a H : ℕ} (D : DAG r n a) (huse : ∀v,physicalUseCount D v≤6) :
    ∀W∈activeReplay D H,Matching W := by
  have hs (enabled : Bool) := activeLayers_matching (H:=H) D enabled huse
  have hb (enabled : Bool) := colorBlocks_matching (natBroadcast D enabled) 6
    (natBroadcast_degree D enabled (by omega) huse) (by omega)
  intro W hW
  simp only [activeReplay,List.mem_append] at hW
  rcases hW with ((((h|h)|h)|h)|h)|h
  · exact hs true W h
  · exact hb true W h
  · exact reverseLayers_matching _ (hs true) W h
  · exact hs false W h
  · exact reverseLayers_matching _ (hb false) W h
  · exact reverseLayers_matching _ (hs false) W h

noncomputable section

theorem activeReplay_action {a H : ℕ} (D : DAG r n a) (bank : Fin r→ℂ)
    (hD : DepthBound D H) (huse : ∀v,physicalUseCount D v≤6) (v : ℕ→ℂ) :
    runShears ((activeReplay D H).flatten.map (ShearCode.eval bank)) v=
      runShears ((natReplayCode D).map (ShearCode.eval bank)) v := by
  have hs (enabled : Bool) := activeLayers_action D bank enabled hD huse
  have hb (enabled : Bool) := colorOrdered_action bank (natBroadcast D enabled)
    (natBroadcast_degree D enabled (by omega) huse) (by omega)
    (natBroadcast_onLevel D enabled).safe
  have hrs (enabled : Bool) := reverseCode_action_congr bank
    (activeLayers D.program enabled H).flatten (natSweep D.program enabled) (hs enabled)
  have hrb (enabled : Bool) := reverseCode_action_congr bank
    (colorOrdered (natBroadcast D enabled) 6) (natBroadcast D enabled) (hb enabled)
  rw [natReplayCode_phases]
  simp only [activeReplay,List.flatten_append,reverseLayers_flatten,colorBlocks_flatten,
    List.map_append,runShears_append]
  rw [hs true,hb true,hrs true,hs false,hrb false,hrs false]

theorem cross_activeReplay_spec (K a e : ℕ) (ha : a≤UniformRadixTwoDAG.width K)
    (he : e≤UniformRadixTwoDAG.width K) (bank : Fin (bankSize K)→ℂ) (v : ℕ→ℂ) :
    runShears ((activeReplay (crossDAG K a e ha he) (8*K+6)).flatten.map
      (ShearCode.eval bank)) v ∘ replayEmbedding e (crossDAG K a e ha he).size a=
      Sum.elim (Sum.elim (fun i : Fin e=>v i.val)
        (fun j : Fin (crossDAG K a e ha he).size=>v (e+1+j.val)))
        (fun j : Fin a=>v (e+1+(crossDAG K a e ha he).size+j.val)+
          ((crossDAG K a e ha he).program.eval bank).eval (fun i=>v i.val)
            ((crossDAG K a e ha he).outputs j)) := by
  rw [activeReplay_action _ bank (crossDAG_depth K a e ha he)
    (crossDAG_physicalFanout K a e ha he),natReplayCode_spec]

end

lemma cross_bucket_degree (K a e d : ℕ) (ha : a≤UniformRadixTwoDAG.width K)
    (he : e≤UniformRadixTwoDAG.width K) (enabled : Bool) :
    DegreeBound (printedEdges (bucket (crossDAG K a e ha he).program enabled d)) 6 :=
  bucket_degree _ enabled d 6 (by omega) (crossDAG_physicalFanout K a e ha he)

lemma cross_activeReplay_bound (K a e : ℕ) (ha : a≤UniformRadixTwoDAG.width K)
    (he : e≤UniformRadixTwoDAG.width K) :
    (activeReplay (crossDAG K a e ha he) (8*K+6)).length≤66*(8*K+7) := by
  rw [activeReplay_length]
  omega

/-- A physical selected gate slice expands to the exact chronological level word. -/
lemma selected_expansion (p : UniformReplayPrint.Program r n t) (enabled : Bool) (d : ℕ) :
    (UniformDAGBucketMachine.selected t d (UniformDAGBucketMachine.typedDepth p)).flatMap
      (UniformCrossShearTableMachine.gateSweep p enabled)=bucket p enabled d := by
  rw [UniformDAGBucketMachine.selected,UniformCrossShearTableMachine.selected_gateSweeps,
    UniformCrossShearTableMachine.gateSweep_all]
  rfl

lemma order_decomposition (G d : ℕ) (depth : ℕ→ℕ) (hd : d≤G) :
    ∃tail,UniformDAGBucketMachine.order G depth=
      ((List.range d).flatMap (fun j=>UniformDAGBucketMachine.selected G j depth)) ++
      UniformDAGBucketMachine.selected G d depth ++ tail := by
  have hr : List.range (G+1)=List.range d ++
      d::(List.range (G-d)).map (fun j=>d+1+j) := by
    have he : G+1=d+((G-d)+1) := by omega
    rw [he,List.range_add,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map]
    congr 2
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply,Nat.succ_eq_add_one]
    omega
  refine ⟨((List.range (G-d)).map (fun j=>d+1+j)).flatMap
    (fun j=>UniformDAGBucketMachine.selected G j depth),?_⟩
  rw [UniformDAGBucketMachine.order,hr,List.flatMap_append,List.flatMap_cons]
  exact List.append_assoc _ _ _ |>.symm

lemma order_slice (G d : ℕ) (depth : ℕ→ℕ) (hd : d≤G) :
    ((UniformDAGBucketMachine.order G depth).drop (UniformDAGBucketMachine.offset G d depth)).take
      (UniformDAGBucketMachine.selected G d depth).length=
        UniformDAGBucketMachine.selected G d depth := by
  obtain ⟨tail,he⟩ := order_decomposition G d depth hd
  rw [he]
  rw [List.append_assoc]
  change ((_ ++ (_ ++ tail)).drop (List.length _)).take _=_
  simp

noncomputable section

lemma order_slice_bank (G d Q : ℕ) (depth : ℕ→ℕ) (hd : d≤G) (s : State)
    (bank : UniformDAGBucketMachine.Bank Q (UniformDAGBucketMachine.order G depth) s) :
    UniformDAGBucketMachine.Bank (Q+UniformDAGBucketMachine.offset G d depth)
      (UniformDAGBucketMachine.selected G d depth) s := by
  have slice := order_slice G d depth hd
  intro i hi
  have valid : i < (((UniformDAGBucketMachine.order G depth).drop
      (UniformDAGBucketMachine.offset G d depth)).take
      (UniformDAGBucketMachine.selected G d depth).length).length := by rw [slice];exact hi
  have bound : UniformDAGBucketMachine.offset G d depth+i<
      (UniformDAGBucketMachine.order G depth).length := by
    simp only [List.length_take,List.length_drop] at valid
    omega
  have eq : (UniformDAGBucketMachine.selected G d depth)[i]'hi=
      (UniformDAGBucketMachine.order G depth)[UniformDAGBucketMachine.offset G d depth+i]'bound := by
    have he := congrArg (fun l : List ℕ=>l[i]?) slice
    simpa only [List.getElem?_take,hi,decide_true,ite_true,List.getElem?_drop,
      List.getElem?_eq_getElem bound,List.getElem?_eq_getElem hi,Option.some.injEq] using he.symm
  simpa only [Nat.add_assoc,eq] using bank (UniformDAGBucketMachine.offset G d depth+i) bound

end

/-- Adding a physical data-base offset changes no indexed incidences. -/
def shiftedEdges (A : ℕ) (W : List (ShearCode ℕ r)) : Fin W.length→Edge :=
  fun i=>⟨A+(W.get i).dst,A+(W.get i).src,by
    intro h;exact (W.get i).different (Nat.add_left_cancel h)⟩

lemma shiftedEdges_degree (A delta : ℕ) (W : List (ShearCode ℕ r))
    (hd : DegreeBound (printedEdges W) delta) : DegreeBound (shiftedEdges A W) delta := by
  intro v
  by_cases hv : A≤v
  · have he : incidentEdges (shiftedEdges A W) v=incidentEdges (printedEdges W) (v-A) := by
      ext i
      simp only [incidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
      change (A+(W.get i).dst=v ∨ A+(W.get i).src=v) ↔
        ((W.get i).dst=v-A ∨ (W.get i).src=v-A)
      omega
    rw [he]
    exact hd (v-A)
  · have he : incidentEdges (shiftedEdges A W) v=∅ := by
      ext i
      simp only [incidentEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty]
      change (A+(W.get i).dst=v ∨ A+(W.get i).src=v) ↔ False
      constructor
      · rintro (he|he) <;> omega
      · exact False.elim
    rw [he]
    simp

lemma power_ge_successor (K : ℕ) : K+1≤2^K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ]
    have h : 1≤2^K := Nat.one_le_pow K 2 (by omega)
    nlinarith

lemma cross_height_le_size (K a e : ℕ) (ha : a≤UniformRadixTwoDAG.width K)
    (he : e≤UniformRadixTwoDAG.width K) : 8*K+6≤(crossDAG K a e ha he).size := by
  rw [crossDAG_size]
  have := power_ge_successor K
  nlinarith [Nat.zero_le (K*2^K)]

/-- The height driver uses 8K+7 depths; empty slots are retained, not G+1. -/
def activeDepths (K : ℕ) : List ℕ := List.range (8*K+7)
lemma activeDepths_length (K : ℕ) : (activeDepths K).length=8*K+7 := by simp [activeDepths]

open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformAssembly

/-- Read two real Bucket24 directory cells and install the Shear60 header. -/
def directoryOps : List Op := [.literal 920 0,.literal 921 1,
  .add 922 904 901,.getNat 923 922,.add 922 922 921,.getNat 924 922,
  .sub 720 924 923]
def shearOps : List Op := [.add 721 902 920,.add 722 903 923,.add 723 905 920,
  .add 724 906 920,.add 725 907 920,.add 726 908 920,.add 727 912 920,
  .add 728 909 920,.add 729 911 920]
def colorOps : List Op := [.add 800 736 920,.add 801 905 920,
  .add 802 913 920,.add 803 914 920]
def program : UniformMachine.Program := directoryOps.map Op.code ++ shearOps.map Op.code ++
  UniformCrossShearTableMachine.program.map (relocate 16 76) ++ colorOps.map Op.code ++
  UniformGreedyColorMachine.program.map (relocate 80 131) ++ [.halt]
lemma program_length : program.length=132 := by
  simp only [program,List.length_append,List.length_map,
    UniformCrossShearTableMachine.program_length,UniformGreedyColorMachine.program_length]
  rfl
lemma directory_code : BlockAt directoryOps program 0 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma shear_header_code : BlockAt shearOps program 7 := by
  intro i hi;change i<9 at hi;interval_cases i <;> rfl
lemma shear_code : CodeAt UniformCrossShearTableMachine.program program 16 76 := by
  intro i hi;rw [UniformCrossShearTableMachine.program_length] at hi
  interval_cases i <;> rfl
lemma color_header_code : BlockAt colorOps program 76 := by
  intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma color_code : CodeAt UniformGreedyColorMachine.program program 80 131 := by
  intro i hi;rw [UniformGreedyColorMachine.program_length] at hi
  interval_cases i <;> rfl
lemma halt_at : program[131]?=some .halt := rfl

noncomputable section

/-- Persistent header900..914. Header910 is unused and preserved. -/
structure Header (G d T Q R D A C P n N F U : ℕ) (enabled : Bool) (s : State) : Prop where
  gates : s.natReg 900=G
  depth : s.natReg 901=d
  tape : s.natReg 902=T
  order : s.natReg 903=Q
  directory : s.natReg 904=R
  destination : s.natReg 905=D
  dataBase : s.natReg 906=A
  coefficients : s.natReg 907=C
  constants : s.natReg 908=P
  inputs : s.natReg 909=n
  width : s.natReg 911=N
  enabled : s.natReg 912=if enabled then 1 else 0
  colors : s.natReg 913=F
  palette : s.natReg 914=U

def Protected (j : ℕ) : Prop := (j<720 ∨ 750≤j) ∧ (j<800 ∨ 824≤j) ∧ (j<920 ∨ 925≤j)
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ∀j,Protected j→u.natReg j=s.natReg j
lemma Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun j hj=>(h'.2.2.2.2 j hj).trans (h.2.2.2.2 j hj)⟩

def natOnly : Op→Prop
  | .literal _ _ | .add _ _ _ | .sub _ _ _ | .getNat _ _=>True
  | _=>False
def natDest : Op→ℕ
  | .literal d _ | .add d _ _ | .sub d _ _ | .getNat d _=>d
  | _=>0
lemma natOp_frame (o : Op) (s : State) (hn : natOnly o) (hd : ¬Protected (natDest o)) :
    Frame s (o.apply s) := by
  cases o <;> simp only [natOnly] at hn
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals
    intro j hj
    simp only [Op.apply,writeNat,next]
    apply Function.update_of_ne
    intro he
    subst j
    exact hd hj
lemma natBlock_frame (b : List Op) (s : State)
    (h : ∀o∈b,natOnly o ∧ ¬Protected (natDest o)) : Frame s (applyBlock b s) := by
  induction b generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
  | cons o b ih =>
    exact (natOp_frame o s (h o (by simp)).1 (h o (by simp)).2).trans
      (ih _ (fun v hv=>h v (by simp [hv])))
lemma natBlock_heap (b : List Op) (s : State) (h : ∀o∈b,natOnly o) :
    (applyBlock b s).natHeap=s.natHeap := by
  induction b generalizing s with
  | nil => rfl
  | cons o b ih =>
    rw [applyBlock,ih _ (fun v hv=>h v (by simp [hv]))]
    have hn := h o (by simp)
    cases o <;> simp only [natOnly] at hn
    all_goals rfl
lemma directory_frame (s : State) : Frame s (applyBlock directoryOps s) := by
  apply natBlock_frame
  simp [directoryOps,natOnly,natDest,Protected]
lemma shear_header_frame (s : State) : Frame s (applyBlock shearOps s) := by
  apply natBlock_frame
  simp [shearOps,natOnly,natDest,Protected]
lemma color_header_frame (s : State) : Frame s (applyBlock colorOps s) := by
  apply natBlock_frame
  simp [colorOps,natOnly,natDest,Protected]
lemma directory_heap (s : State) : (applyBlock directoryOps s).natHeap=s.natHeap := by
  apply natBlock_heap;simp [directoryOps,natOnly]
lemma shear_header_heap (s : State) : (applyBlock shearOps s).natHeap=s.natHeap := by
  apply natBlock_heap;simp [shearOps,natOnly]
lemma color_header_heap (s : State) : (applyBlock colorOps s).natHeap=s.natHeap := by
  apply natBlock_heap;simp [colorOps,natOnly]
lemma Header.transport {G d T Q R D A C P n N F U : ℕ} {enabled : Bool} {s u : State}
    (h : Header G d T Q R D A C P n N F U enabled s) (hf : Frame s u) :
    Header G d T Q R D A C P n N F U enabled u := by
  constructor
  all_goals first
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.gates
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.depth
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.tape
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.order
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.directory
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.destination
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.dataBase
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.coefficients
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.constants
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.inputs
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.width
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.enabled
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.colors
  | exact (hf.2.2.2.2 _ (by simp [Protected])).trans h.palette

lemma directory_spec (s : State) {G d T Q R D A C P n N F U : ℕ} {enabled : Bool}
    (h : Header G d T Q R D A C P n N F U enabled s) (start finish : ℕ)
    (hstart : s.natHeap (R+d)=some start) (hfinish : s.natHeap (R+d+1)=some finish) :
    (applyBlock directoryOps s).natReg 720=finish-start ∧
    (applyBlock directoryOps s).natReg 923=start ∧
    (applyBlock directoryOps s).natReg 920=0 := by
  simp [directoryOps,applyBlock,Op.apply,writeNat,next,h.directory,h.depth,hstart,hfinish]

lemma offset_span {G d : ℕ} (depth : ℕ→ℕ) (hd : d≤G)
    (bounds : ∀i,i<G→depth i≤G) :
    UniformDAGBucketMachine.offset G d depth+
      (UniformDAGBucketMachine.selected G d depth).length≤G := by
  obtain ⟨tail,he⟩ := order_decomposition G d depth hd
  have hl := congrArg List.length he
  rw [UniformDAGBucketMachine.order_length G depth bounds] at hl
  simp only [List.length_append] at hl
  change G=UniformDAGBucketMachine.offset G d depth+_+_ at hl
  omega

lemma bucket_rows {u : ℕ} (K A C Z P : ℕ)
    (p : UniformReplayPrint.Program (bankSize K) n u) (enabled : Bool) (d : ℕ)
    (good : ∀g∈programRecords p,UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K) g) :
    UniformCrossShearTableMachine.orderedRows n A C P enabled
      (UniformCrossShearTableMachine.rowAt p)
      (UniformDAGBucketMachine.selected u d (UniformDAGBucketMachine.typedDepth p))=
      (bucket p enabled d).map
        (UniformCrossShearTableMachine.shiftedRow A (UniformCrossShearTableMachine.locations (bankSize K) C Z P)) := by
  rw [← selected_expansion, List.map_flatMap]
  unfold UniformCrossShearTableMachine.orderedRows
  apply List.flatMap_congr
  intro j hj
  have valid := (UniformDAGBucketMachine.selected_mem u d _ j).mp hj |>.1
  rw [UniformCrossShearTableMachine.gateSweep_rows p j A _ enabled valid]
  exact UniformCrossShearTableMachine.expansion_typed K n A C Z P j enabled
    (UniformCrossShearTableMachine.exprAt p j)
    (good _ (UniformCrossShearTableMachine.exprAt_mem p j valid))

lemma table_edges (A D : ℕ) (W : List (ShearCode ℕ r))
    (loc : UniformInPlaceMachine.Locations r) (s : State)
    (table : UniformCrossShearTableMachine.Table D
      (W.map (UniformCrossShearTableMachine.shiftedRow A loc)) s) :
    UniformGreedyColorMachine.Edges (shiftedEdges A W) D s := by
  intro i
  have ht := table i.val (by simp only [List.length_map];exact i.isLt)
  simp only [List.getElem_map] at ht
  exact ⟨ht.1,ht.2.1⟩

lemma directory_runs {G d T Q R D A C P n N F U B m : ℕ} {enabled : Bool}
    (x : Fin m→ℂ) (s : State) (h : Header G d T Q R D A C P n N F U enabled s)
    (pc : s.pc=0) (hs : WordBound B s) (start finish : ℕ)
    (hstart : s.natHeap (R+d)=some start) (hfinish : s.natHeap (R+d+1)=some finish)
    (hbound : start≤G ∧ finish≤G) (hb : 132+R+d+G≤B) :
    BoundedRuns program m x B s 7 (applyBlock directoryOps s) := by
  apply block_runs directoryOps program 0 m B x s directory_code pc hs (by change 0+7≤B;omega)
  · simp [readable,directoryOps,Op.readable,Op.apply,writeNat,next,h.directory,h.depth,hstart,hfinish]
  · simp [peak,directoryOps,Op.peak,Op.apply,writeNat,next,h.directory,h.depth,hstart,hfinish]
    omega

lemma shear_header_spec {G d T Q R D A C P n N F U M start : ℕ} {enabled : Bool} (s : State)
    (h : Header G d T Q R D A C P n N F U enabled s)
    (hM : s.natReg 720=M) (hstart : s.natReg 923=start) (hz : s.natReg 920=0) :
    UniformCrossShearTableMachine.Header M T (Q+start) D A C P n N enabled (applyBlock shearOps s) := by
  constructor
  all_goals simp [shearOps,applyBlock,Op.apply,writeNat,next,hM,hstart,hz,
    h.tape,h.order,h.destination,h.dataBase,h.coefficients,h.constants,h.enabled,h.inputs,h.width]

lemma shear_header_changePC {M T Q D A C P n N pc : ℕ} {enabled : Bool} {s : State}
    (h : UniformCrossShearTableMachine.Header M T Q D A C P n N enabled s) :
    UniformCrossShearTableMachine.Header M T Q D A C P n N enabled {s with pc:=pc} :=
  ⟨h.count,h.tape,h.order,h.output,h.dataBase,h.coefficients,h.constants,h.enabled,h.inputs,h.width⟩

def OutsideNat (D F U G : ℕ) (s u : State) : Prop :=
  ∀j,(j<D ∨ D+6*G≤j)→(j<F ∨ F+2*G≤j)→(j<U ∨ U+12≤j)→u.natHeap j=s.natHeap j

def wordBudget (G T Q R D A C P n N F U : ℕ) : ℕ :=
    132+T+5*G+Q+G+R+G+2+D+6*G+A+n+1+G+C+7*N+P+2+F+2*G+U+12

lemma reset_placed (base : ℕ) (s : State) (h : s.pc=base) : placed base {s with pc:=0}=s := by
  cases s
  change _=base at h
  subst h
  rfl

lemma color_frame {s u : State} (h : UniformGreedyColorMachine.Frame s u) : Frame s u :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun j hj=>h.2.2.2.2 j (by unfold Protected at hj;omega)⟩
lemma shear_frame {s u : State} (h : UniformCrossShearTableMachine.Frame s u) : Frame s u :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun j hj=>h.2.2.2.2 j (by unfold Protected at hj;omega)⟩

/-- One actual depth call: directory reads, header installation, literal Shear60,
    color header installation, literal Greedy51 and halt.  No coloring or
    complete shear table is supplied.  The source bank/directory are the exact
    outputs of Bucket24; scalar coefficient production remains separate. -/
theorem bucket_execution {G : ℕ} (K d T Q R D A C Z P F U B m : ℕ)
    (p : UniformReplayPrint.Program (bankSize K) n G) (x : Fin m→ℂ)
    (enabled : Bool) (s : State)
    (good : ∀g∈programRecords p,UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K) g)
    (degree : DegreeBound (printedEdges (bucket p enabled d)) 6)
    (header : Header G d T Q R D A C P n (UniformRadixTwoDAG.width K) F U enabled s)
    (pc : s.pc=0) (hs : WordBound B s) (hd : d≤G)
    (bank : UniformDAGBucketMachine.Bank Q
      (UniformDAGBucketMachine.order G (UniformDAGBucketMachine.typedDepth p)) s)
    (directory : UniformDAGBucketMachine.Directory R G (G+2) (UniformDAGBucketMachine.typedDepth p) s)
    (tape : UniformToeplitzCrossTopologyMachine.RowTable
      ((programRecords p).map UniformConvolutionTopologyMachine.encode) T s)
    (hT : T+5*G≤D) (hQ : Q+G≤D) (hR : R+G+2≤D)
    (hD : D+6*G≤F) (hF : F+2*G≤U)
    (hb : wordBudget G T Q R D A C P n (UniformRadixTwoDAG.width K) F U≤B) :
    ∃u ticks,BoundedExecution program m x B s ticks u ∧
      ticks≤64*G+200*(2*G+1)^2+31 ∧ u.pc=131 ∧
      UniformCrossShearTableMachine.Table D
        ((bucket p enabled d).map (UniformCrossShearTableMachine.shiftedRow A
          (UniformCrossShearTableMachine.locations (bankSize K) C Z P))) u ∧
      u.natReg 800=(bucket p enabled d).length ∧
      (∀i:Fin (bucket p enabled d).length,u.natHeap (F+i.val)=
        some (coloring (shiftedEdges A (bucket p enabled d)) 6 i)) ∧
      (∀i:Fin (bucket p enabled d).length,coloring (shiftedEdges A (bucket p enabled d)) 6 i<11) ∧
      (∀i j:Fin (bucket p enabled d).length,i≠j→
        coloring (shiftedEdges A (bucket p enabled d)) 6 i=
        coloring (shiftedEdges A (bucket p enabled d)) 6 j→
          ¬Conflict (shiftedEdges A (bucket p enabled d) i) (shiftedEdges A (bucket p enabled d) j)) ∧
      OutsideNat D F U G s u ∧
      UniformDAGBucketMachine.Directory R G (G+2) (UniformDAGBucketMachine.typedDepth p) u ∧
      Frame s u ∧ Header G d T Q R D A C P n (UniformRadixTwoDAG.width K) F U enabled u := by
  let js := UniformDAGBucketMachine.selected G d (UniformDAGBucketMachine.typedDepth p)
  let start := UniformDAGBucketMachine.offset G d (UniformDAGBucketMachine.typedDepth p)
  let finish := UniformDAGBucketMachine.offset G (d+1) (UniformDAGBucketMachine.typedDepth p)
  have span : start+js.length≤G := offset_span _ hd (UniformDAGBucketMachine.typedDepth_bound p)
  have endeq : finish=start+js.length := UniformDAGBucketMachine.offset_succ G d _
  have hstart := directory d (by omega)
  have hfinish := directory (d+1) (by omega)
  change s.natHeap (R+d)=some start at hstart
  change s.natHeap (R+d+1)=some finish at hfinish
  have bounds : start≤G ∧ finish≤G := by omega
  have budget := hb
  unfold wordBudget at budget
  have boot := directory_runs x s header pc hs start finish hstart hfinish bounds (by omega)
  let a := applyBlock directoryOps s
  obtain ⟨h720,h923,h920⟩ := directory_spec s header start finish hstart hfinish
  have count : a.natReg 720=js.length := by dsimp only [a];rw [h720,endeq];omega
  have ha : Header G d T Q R D A C P n (UniformRadixTwoDAG.width K) F U enabled a :=
    header.transport (directory_frame s)
  change a.natReg 923=start at h923
  change a.natReg 920=0 at h920
  have apc : a.pc=7 := by simp only [a,UniformTensorMonomialMachine.applyBlock_pc,pc];rfl
  have setup : BoundedRuns program m x B a 9 (applyBlock shearOps a) := by
    apply block_runs shearOps program 7 m B x a shear_header_code apc boot.final_bound (by change 7+9≤B;omega)
    · simp [readable,shearOps,Op.readable]
    · simp [peak,shearOps,Op.peak,Op.apply,writeNat,next,h920,h923,
        ha.tape,ha.order,ha.destination,ha.dataBase,ha.coefficients,ha.constants,ha.enabled,ha.inputs,ha.width]
      cases enabled <;> simp_all only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  let b := applyBlock shearOps a
  have bpc : b.pc=16 := by simp only [b,UniformTensorMonomialMachine.applyBlock_pc,apc];rfl
  have bframe : Frame s b := (directory_frame s).trans (shear_header_frame a)
  have bheader : UniformCrossShearTableMachine.Header js.length T (Q+start) D A C P n
      (UniformRadixTwoDAG.width K) enabled b := shear_header_spec a ha count h923 h920
  have bheap : b.natHeap=s.natHeap := (shear_header_heap a).trans (directory_heap s)
  have bbank := order_slice_bank G d Q _ hd s bank
  have bbank' : UniformCrossShearTableMachine.OrderBank (Q+start) js {b with pc:=0} := by
    simpa only [UniformCrossShearTableMachine.OrderBank,UniformDAGBucketMachine.Bank,bheap] using bbank
  have btape : UniformCrossShearTableMachine.Tape G T (UniformCrossShearTableMachine.rowAt p) {b with pc:=0} := by
    simpa only [UniformCrossShearTableMachine.Tape,UniformCrossShearTableMachine.Fields,bheap] using
      UniformCrossShearTableMachine.tape_of_typed p s tape
  obtain ⟨v,ticks,run,cost,vpc,vheader,table,countRows,outside,vframe⟩ :=
    UniformCrossShearTableMachine.execution B m G T (Q+start) D A C P n
      (UniformRadixTwoDAG.width K) x (UniformCrossShearTableMachine.rowAt p) js enabled {b with pc:=0}
      (shear_header_changePC bheader) rfl (changePC_bound B b 0 setup.final_bound (by omega)) bbank' btape
      (UniformCrossShearTableMachine.rowAt_bounds K p good)
      (fun j hj=>(UniformDAGBucketMachine.selected_mem G d _ j).mp hj |>.1)
      (by omega) hT (by omega) (by omega) (by omega) (by omega) (by omega)
  have rows := bucket_rows K A C Z P p enabled d good
  change UniformCrossShearTableMachine.orderedRows n A C P enabled
    (UniformCrossShearTableMachine.rowAt p) js=_ at rows
  rw [rows] at table countRows
  simp only [List.length_map] at countRows
  have size : (bucket p enabled d).length≤2*js.length := by
    have h := UniformCrossShearTableMachine.orderedRows_length n A C P enabled
      (UniformCrossShearTableMachine.rowAt p) js
    rw [rows,List.length_map] at h
    exact h
  have placedRun := UniformBoundedAssembly.boundedExecution_placed shear_code
    (by rw [UniformCrossShearTableMachine.program_length];omega) (by omega) run
  have reset : placed 16 {b with pc:=0}=b := reset_placed 16 b bpc
  rw [reset] at placedRun
  let c : State := {v with pc:=76}
  have cf : Frame s c := bframe.trans (shear_frame vframe)
  have ch := header.transport cf
  have ccount : c.natReg 736=(bucket p enabled d).length := countRows
  have zero : c.natReg 920=0 := (vframe.2.2.2.2 920 (by omega)).trans
    (by simpa [b,shearOps,applyBlock,Op.apply,writeNat,next] using h920)
  have colorBoot : BoundedRuns program m x B c 4 (applyBlock colorOps c) := by
    apply block_runs colorOps program 76 m B x c color_header_code rfl placedRun.final_bound
      (by change 76+4≤B;omega)
    · simp [readable,colorOps,Op.readable]
    · simp [peak,colorOps,Op.peak,Op.apply,writeNat,next,zero,ccount,ch.destination,ch.colors,ch.palette]
      omega
  let e := applyBlock colorOps c
  have eh : UniformGreedyColorMachine.Header (bucket p enabled d).length D F U {e with pc:=0} := by
    constructor
    all_goals simp [e,colorOps,applyBlock,Op.apply,writeNat,next,zero,ccount,
      ch.destination,ch.colors,ch.palette]
  have ehp : e.natHeap=c.natHeap := color_header_heap c
  have etable : UniformCrossShearTableMachine.Table D
      ((bucket p enabled d).map (UniformCrossShearTableMachine.shiftedRow A
        (UniformCrossShearTableMachine.locations (bankSize K) C Z P))) {e with pc:=0} := by
    simpa only [UniformCrossShearTableMachine.Table,ehp] using table
  obtain ⟨ct,u,ccost,crun,upc,uh,colors,colorBound,matching,_,cout,uframe⟩ :=
    UniformGreedyColorMachine.execution_degree_six (bucket p enabled d).length D F U B m x
      {e with pc:=0} (shiftedEdges A (bucket p enabled d)) (shiftedEdges_degree A 6 _ degree)
      eh rfl (table_edges A D _ _ _ etable) (by omega) (by omega) (by omega) (by omega)
      (changePC_bound B e 0 colorBoot.final_bound (by omega))
  have colorRun := UniformBoundedAssembly.boundedExecution_placed color_code
    (by rw [UniformGreedyColorMachine.program_length];omega) (by omega) crun
  have epc : e.pc=80 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have reset : placed 80 {e with pc:=0}=e := reset_placed 80 e epc
  rw [reset] at colorRun
  let final : State := {u with pc:=131}
  have halt : BoundedExecution program m x B final 1 final := .halt colorRun.final_bound
    (by simp [final,UniformMachine.step,halt_at])
  have ff : Frame s final := cf.trans ((color_header_frame c).trans (color_frame uframe))
  have out : OutsideNat D F U G s final := by
    intro j hjD hjF hjU
    rw [cout j (by omega) hjU]
    change e.natHeap j=s.natHeap j
    rw [ehp]
    change v.natHeap j=s.natHeap j
    rw [outside j (by omega)]
    exact congrFun bheap j
  have dirFinal : UniformDAGBucketMachine.Directory R G (G+2)
      (UniformDAGBucketMachine.typedDepth p) final := by
    intro j hj
    rw [out (R+j) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact directory j hj
  refine ⟨final,7+9+ticks+4+ct+1,?_,?_,rfl,?_,uh.count,colors,colorBound,matching,out,dirFinal,ff,
    header.transport ff⟩
  · simpa only [Nat.add_assoc] using (boot.trans (setup.trans (placedRun.trans (colorBoot.trans colorRun)))).executes halt
  · unfold UniformGreedyColorMachine.runtimeBudget at ccost
    have monotone : ((bucket p enabled d).length+1)^2≤(2*G+1)^2 := by
      apply Nat.pow_le_pow_left;omega
    omega
  · intro j hj
    have ht := etable j hj
    have hj' : j<(bucket p enabled d).length := by simpa only [List.length_map] using hj
    unfold UniformCrossShearTableMachine.RowFields at *
    refine ⟨?_,?_,?_⟩
    · rw [cout _ (Or.inl (by omega)) (Or.inl (by omega))]
      exact ht.1
    · rw [cout _ (Or.inl (by omega)) (Or.inl (by omega))]
      exact ht.2.1
    · rw [cout _ (Or.inl (by omega)) (Or.inl (by omega))]
      exact ht.2.2

/-- Actual Cross271 specialization. The final caller has no coefficient-subset,
    sort, degree, complete shear-table or coloring certificate in its entry. -/
theorem cross_bucket_execution (K a e d T Q R D A C Z P F U B m : ℕ)
    (ha : a≤UniformRadixTwoDAG.width K) (he : e≤UniformRadixTwoDAG.width K)
    (enabled : Bool) (x : Fin m→ℂ) (s : State)
    (header : Header (crossDAG K a e ha he).size d T Q R D A C P e
      (UniformRadixTwoDAG.width K) F U enabled s)
    (pc : s.pc=0) (hs : WordBound B s) (hd : d≤8*K+6)
    (bank : UniformDAGBucketMachine.Bank Q
      (UniformDAGBucketMachine.order (crossDAG K a e ha he).size
        (UniformDAGBucketMachine.typedDepth (crossDAG K a e ha he).program)) s)
    (directory : UniformDAGBucketMachine.Directory R (crossDAG K a e ha he).size
      ((crossDAG K a e ha he).size+2)
      (UniformDAGBucketMachine.typedDepth (crossDAG K a e ha he).program) s)
    (tape : UniformToeplitzCrossTopologyMachine.RowTable
      (UniformToeplitzCrossTopologyMachine.crossRows K a e) T s)
    (hT : T+5*(crossDAG K a e ha he).size≤D)
    (hQ : Q+(crossDAG K a e ha he).size≤D)
    (hR : R+(crossDAG K a e ha he).size+2≤D)
    (hD : D+6*(crossDAG K a e ha he).size≤F)
    (hF : F+2*(crossDAG K a e ha he).size≤U)
    (hb : wordBudget (crossDAG K a e ha he).size T Q R D A C P e
      (UniformRadixTwoDAG.width K) F U≤B) :
    ∃u ticks,BoundedExecution program m x B s ticks u ∧
      ticks≤64*(crossDAG K a e ha he).size+200*(2*(crossDAG K a e ha he).size+1)^2+31 ∧
      u.pc=131 ∧
      UniformCrossShearTableMachine.Table D
        ((bucket (crossDAG K a e ha he).program enabled d).map
          (UniformCrossShearTableMachine.shiftedRow A
            (UniformCrossShearTableMachine.locations (bankSize K) C Z P))) u ∧
      u.natReg 800=(bucket (crossDAG K a e ha he).program enabled d).length ∧
      (∀i:Fin (bucket (crossDAG K a e ha he).program enabled d).length,
        u.natHeap (F+i.val)=some (coloring
          (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d)) 6 i)) ∧
      (∀i:Fin (bucket (crossDAG K a e ha he).program enabled d).length,
        coloring (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d)) 6 i<11) ∧
      (∀i j:Fin (bucket (crossDAG K a e ha he).program enabled d).length,i≠j→
        coloring (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d)) 6 i=
        coloring (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d)) 6 j→
          ¬Conflict (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d) i)
            (shiftedEdges A (bucket (crossDAG K a e ha he).program enabled d) j)) ∧
      OutsideNat D F U (crossDAG K a e ha he).size s u ∧
      Frame s u := by
  have actual : UniformToeplitzCrossTopologyMachine.RowTable
      ((programRecords (crossDAG K a e ha he).program).map UniformConvolutionTopologyMachine.encode) T s := by
    rw [← UniformToeplitzCrossTopologyMachine.crossRows_typed K a e ha he]
    exact tape
  obtain ⟨u,ticks,run,cost,pc',rows,count,colors,bounds,matching,outside,_,frame,_⟩ :=
    bucket_execution K d T Q R D A C Z P F U B m (crossDAG K a e ha he).program x enabled s
      (UniformCrossShearTableMachine.cross_good K a e ha he)
      (cross_bucket_degree K a e d ha he enabled) header pc hs
      (hd.trans (cross_height_le_size K a e ha he)) bank directory actual hT hQ hR hD hF hb
  exact ⟨u,ticks,run,cost,pc',rows,count,colors,bounds,matching,outside,frame⟩

lemma saved_headers {s u : State} (frame : Frame s u) (j : ℕ) (h : 100≤j ∧ j≤106) :
    u.natReg j=s.natReg j := frame.2.2.2.2 j (by unfold Protected;omega)

lemma master_retained {s u : State} (frame : Frame s u) : u.scalarHeap 0=s.scalarHeap 0 :=
  congrFun frame.1 0

end
end ExactFourierCircuits.UniformCrossDepthReplayPreparation
