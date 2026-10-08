import UniformTensorMonomialMachine
import UniformDAGLayers
import UniformDAGDepthMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDAGBucketMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Header: Nat700=gate count,701=actual gate-depth bank,702=output,
703=bucket directory. Only Nat704..711 are scratch. No scalar is read. -/
def boot : List Op := [.literal 704 0,.literal 705 1,.literal 706 0,
  .literal 707 0,.add 708 700 705]
def head : List Op := [.add 709 703 706,.putNat 709 707,.literal 710 0]
def read : List Op := [.add 709 701 710,.getNat 711 709]
def write : List Op := [.add 709 702 707,.putNat 709 710,.add 707 707 705]
def tick : List Op := [.add 710 710 705]
def close : List Op := [.add 706 706 705]
def finish : List Op := [.add 709 703 706,.putNat 709 707]
def program : Program := boot.map Op.code ++ [.branchLT 706 708 6 21] ++
  head.map Op.code ++ [.branchLT 710 700 10 19] ++ read.map Op.code ++
  [.branchLT 711 706 17 13,.branchLT 706 711 17 14] ++ write.map Op.code ++
  tick.map Op.code ++ [.jump 9] ++ close.map Op.code ++ [.jump 5] ++
  finish.map Op.code ++ [.halt]
theorem program_length : program.length=24 := rfl
theorem boot_code : BlockAt boot program 0 := by
  intro i hi; change i<5 at hi; interval_cases i <;> rfl
theorem head_code : BlockAt head program 6 := by
  intro i hi; change i<3 at hi; interval_cases i <;> rfl
theorem read_code : BlockAt read program 10 := by
  intro i hi; change i<2 at hi; interval_cases i <;> rfl
theorem write_code : BlockAt write program 14 := by
  intro i hi; change i<3 at hi; interval_cases i <;> rfl
theorem tick_code : BlockAt tick program 17 := by
  intro i hi; change i<1 at hi; interval_cases i; rfl
theorem close_code : BlockAt close program 19 := by
  intro i hi; change i<1 at hi; interval_cases i; rfl
theorem finish_code : BlockAt finish program 21 := by
  intro i hi; change i<2 at hi; interval_cases i <;> rfl
theorem outer_at : program[5]?=some (.branchLT 706 708 6 21) := rfl
theorem inner_at : program[9]?=some (.branchLT 710 700 10 19) := rfl
theorem less_at : program[12]?=some (.branchLT 711 706 17 13) := rfl
theorem greater_at : program[13]?=some (.branchLT 706 711 17 14) := rfl
theorem tick_at : program[18]?=some (.jump 9) := rfl
theorem close_at : program[20]?=some (.jump 5) := rfl
theorem halt_at : program[23]?=some .halt := rfl

/-- Stable order of gate ordinals; even zero-depth occurrences are retained. -/
def selected (G level : ℕ) (depth : ℕ→ℕ) : List ℕ :=
  (List.range G).filter (fun i=>decide (depth i=level))
def order (G : ℕ) (depth : ℕ→ℕ) : List ℕ :=
  (List.range (G+1)).flatMap (fun d=>selected G d depth)
def offset (G level : ℕ) (depth : ℕ→ℕ) : ℕ :=
  ((List.range level).flatMap (fun d=>selected G d depth)).length
theorem selected_length (G level : ℕ) (depth : ℕ→ℕ) :
    (selected G level depth).length≤G := by
  exact (List.length_filter_le _ _).trans (by simp)
theorem selected_mem (G level : ℕ) (depth : ℕ→ℕ) (i : ℕ) :
    i∈selected G level depth ↔ i<G ∧ depth i=level := by simp [selected]
theorem selected_nodup (G level : ℕ) (depth : ℕ→ℕ) :
    (selected G level depth).Nodup := (List.nodup_range).filter _
theorem offset_bound (G level : ℕ) (depth : ℕ→ℕ) : offset G level depth≤level*G := by
  induction level with
  | zero => simp [offset]
  | succ d ih =>
    have h:=selected_length G d depth
    simp only [offset,List.range_succ,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_append] at *
    simpa [Nat.add_mul] using Nat.add_le_add ih h

noncomputable section
structure Header (G P Q R : ℕ) (s : State) : Prop where
  count : s.natReg 700=G
  source : s.natReg 701=P
  output : s.natReg 702=Q
  directory : s.natReg 703=R
structure Fixed (G P Q R : ℕ) (s : State) : Prop where
  header : Header G P Q R s
  zero : s.natReg 704=0
  one : s.natReg 705=1
  limit : s.natReg 708=G+1
structure Cursor (G P Q R level i count : ℕ) (s : State) : Prop where
  fixed : Fixed G P Q R s
  pc : s.pc=9
  level : s.natReg 706=level
  index : s.natReg 710=i
  count : s.natReg 707=count
def Depths (P G : ℕ) (depth : ℕ→ℕ) (s : State) : Prop :=
  ∀i,i<G→s.natHeap (P+i)=some (depth i)
def Bank (Q : ℕ) (values : List ℕ) (s : State) : Prop :=
  ∀i,(hi:i<values.length)→s.natHeap (Q+i)=some (values[i]'hi)
def Outside (Q length R count : ℕ) (s u : State) : Prop :=
  ∀j,(j<Q ∨ Q+length≤j)→(j<R ∨ R+count≤j)→u.natHeap j=s.natHeap j
def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,(r<704 ∨ 712≤r)→u.natReg r=s.natReg r)
theorem frame_refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem frame_trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr=>(h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩
def runtimeBudget (G : ℕ) := 10*G*(G+1)+7*(G+1)+9

def readState (s : State) := applyBlock read (setPC s 10)
def writeState (s : State) := applyBlock write (setPC s 14)
def tickState (s : State) := setPC (applyBlock tick (setPC s 17)) 9
def iteration (level value : ℕ) (s : State) :=
  let v:=readState s
  tickState (if value=level then writeState v else v)
def rowCost (level value : ℕ) := if value<level then 6 else if level<value then 7 else 10

theorem read_spec {G P Q R level i count value : ℕ} {s : State}
    (h:Cursor G P Q R level i count s) (hv:s.natHeap (P+i)=some value) :
    (readState s).pc=12 ∧ (readState s).natReg 711=value ∧
    Cursor G P Q R level i count (setPC (readState s) 9) := by
  refine ⟨?_,?_,⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_,?_⟩⟩
  all_goals simp [readState,read,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.output,h.fixed.header.directory,
    h.fixed.zero,h.fixed.one,h.fixed.limit,h.level,h.index,h.count,hv]
theorem read_heap (s : State) : (readState s).natHeap=s.natHeap := rfl
theorem read_frame (s : State) : Frame s (readState s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr; simp (disch:=omega) [readState,read,applyBlock,Op.apply,setPC,writeNat,next]

theorem iteration_heap {G P Q R level i count value : ℕ} {s : State}
    (h:Cursor G P Q R level i count s) :
    (iteration level value s).natHeap=if value=level then
      Function.update s.natHeap (Q+count) (some i) else s.natHeap := by
  by_cases he:value=level <;> simp [iteration,he,tickState,tick,writeState,write,
    readState,read,applyBlock,Op.apply,setPC,writeNat,next,h.fixed.header.output,
    h.index,h.count]
theorem iteration_cursor {G P Q R level i count value : ℕ} {s : State}
    (h:Cursor G P Q R level i count s) :
    Cursor G P Q R level (i+1) (count+if value=level then 1 else 0)
      (iteration level value s) := by
  by_cases he:value=level
  all_goals refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_,?_⟩
  all_goals simp [iteration,he,tickState,tick,writeState,write,readState,read,
    applyBlock,Op.apply,setPC,writeNat,next,h.fixed.header.count,
    h.fixed.header.source,h.fixed.header.output,h.fixed.header.directory,
    h.fixed.zero,h.fixed.one,h.fixed.limit,h.level,h.index,h.count]
theorem iteration_frame (level value : ℕ) (s : State) : Frame s (iteration level value s) := by
  by_cases he:value=level
  all_goals simp only [iteration,he,ite_true,ite_false]
  all_goals refine ⟨rfl,rfl,rfl,rfl,?_⟩
  all_goals intro r hr
  all_goals simp (disch:=omega) [tickState,tick,writeState,write,
    readState,read,applyBlock,Op.apply,setPC,writeNat,next]

theorem read_bounded {G P Q R level i count value : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor G P Q R level i count s) (hi:i<G)
    (hv:s.natHeap (P+i)=some value) (hB:24≤B) (hP:P+G≤B)
    (hs:WordBound B s) : BoundedRuns program n x B s 3 (readState s) := by
  let e:=setPC s 10
  have he:WordBound B e:=changePC_bound B s 10 hs (by omega)
  have vB:value≤B:=(hs.2.2.1 (P+i) value hv).2
  have hr:readable read e:=by
    simp [readable,read,Op.readable,Op.apply,setPC,e,writeNat,next,
      h.fixed.header.source,h.index,hv]
  have pk:peak read e≤B:=by
    simp [peak,read,Op.peak,Op.apply,setPC,e,writeNat,next,
      h.fixed.header.source,h.index,hv]
    omega
  have enter:BoundedRuns program n x B s 1 e:=.next hs
    (by simp [step,h.pc,inner_at,h.index,h.fixed.header.count,hi,e,setPC]) (.refl he)
  have run:=block_runs read program 10 n B x e read_code rfl he (by change 10+2≤B;omega) hr pk
  simpa [readState,e,read] using enter.trans run

theorem tick_bounded {G P Q R level i count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor G P Q R level i count (setPC s 9)) (hp:s.pc=17)
    (hi:i<G) (hB:24≤B) (hG:G≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 2 (tickState s) := by
  have index:s.natReg 710=i:=h.index
  have one:s.natReg 705=1:=h.fixed.one
  have eqPC:setPC s 17=s:=by cases s; simp_all [setPC]
  have hr:readable tick s:=by simp [tick,readable,Op.readable]
  have pk:peak tick s≤B:=by
    simp [tick,peak,Op.peak,index,one]
    omega
  have run:=block_runs tick program 17 n B x s tick_code hp hs
    (by change 17+1≤B;omega) hr pk
  have ipc:(applyBlock tick s).pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  have jump:BoundedRuns program n x B (applyBlock tick s) 1 (tickState s):=
    .next run.final_bound (by rw [step,ipc,tick_at];rfl)
      (.refl (by change WordBound B (setPC (applyBlock tick (setPC s 17)) 9)
                 rw [eqPC]; exact changePC_bound B _ 9 run.final_bound (by omega)))
  simpa [tick] using run.trans jump

theorem write_bounded {G P Q R level i count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor G P Q R level i count (setPC s 9)) (hp:s.pc=14)
    (hi:i<G) (hB:24≤B) (hG:G≤B) (hQ:Q+count+1≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 3 (writeState s) := by
  have index:s.natReg 710=i:=h.index
  have count:s.natReg 707=count:=h.count
  have output:s.natReg 702=Q:=h.fixed.header.output
  have one:s.natReg 705=1:=h.fixed.one
  have eqPC:setPC s 14=s:=by cases s; simp_all [setPC]
  have hr:readable write s:=by simp [write,readable,Op.readable]
  have pk:peak write s≤B:=by
    simp [write,peak,Op.peak,Op.apply,writeNat,next,count,index,output,one]
    omega
  have run:=block_runs write program 14 n B x s write_code hp hs
    (by change 14+3≤B;omega) hr pk
  simpa [writeState,eqPC,write] using run

theorem branch_runs (p : Program) (B n a b yes no : ℕ) (x : Fin n→ℂ)
    (s : State) (hc:p[s.pc]?=some (.branchLT a b yes no)) (hs:WordBound B s)
    (hy:yes≤B) (hn:no≤B) :
    BoundedRuns p n x B s 1 (setPC s (if s.natReg a<s.natReg b then yes else no)) := by
  refine .next hs ?_ (.refl ?_)
  · simp only [step,hc];split <;> rfl
  · apply changePC_bound B _ _ hs
    split <;> assumption

theorem iteration_bounded {G P Q R level i count value : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor G P Q R level i count s) (hi:i<G)
    (hv:s.natHeap (P+i)=some value) (hB:24≤B) (hP:P+G≤B)
    (hQ:Q+count+1≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s (rowCost level value) (iteration level value s) := by
  have rd:=read_bounded B n x s h hi hv hB hP hs
  let v:=readState s
  have spec:=read_spec h hv
  have vc:Cursor G P Q R level i count (setPC v 9):=spec.2.2
  have vl:v.natReg 706=level:=vc.level
  have vv:v.natReg 711=value:=spec.2.1
  have vg:G≤B:=by omega
  have b1:=branch_runs program B n 711 706 17 13 x v
    (by rw [spec.1];exact less_at) rd.final_bound (by omega) (by omega)
  by_cases less:value<level
  · have run1:BoundedRuns program n x B v 1 (setPC v 17):=by
      simpa [vv,vl,less] using b1
    have tc:Cursor G P Q R level i count (setPC (setPC v 17) 9):=by
      simpa [setPC] using vc
    have run2:=tick_bounded B n x (setPC v 17) tc rfl hi hB vg run1.final_bound
    have ne:value≠level:=by omega
    simpa [rowCost,less,iteration,ne,v,tickState,setPC] using rd.trans (run1.trans run2)
  · have run1:BoundedRuns program n x B v 1 (setPC v 13):=by
      simpa [vv,vl,less] using b1
    let w:=setPC v 13
    have wc:Cursor G P Q R level i count (setPC w 9):=by simpa [w,setPC] using vc
    have b2:=branch_runs program B n 706 711 17 14 x w greater_at
      run1.final_bound (by omega) (by omega)
    by_cases greater:level<value
    · have run2:BoundedRuns program n x B w 1 (setPC w 17):=by
        simpa [w,setPC,vv,vl,greater] using b2
      have tc:Cursor G P Q R level i count (setPC (setPC w 17) 9):=by
        simpa [setPC] using wc
      have run3:=tick_bounded B n x (setPC w 17) tc rfl hi hB vg run2.final_bound
      have ne:value≠level:=by omega
      simpa [rowCost,less,greater,iteration,ne,v,w,tickState,setPC] using
        rd.trans (run1.trans (run2.trans run3))
    · have equal:value=level:=by omega
      have run2:BoundedRuns program n x B w 1 (setPC w 14):=by
        simpa [w,setPC,vv,vl,greater] using b2
      have wc':Cursor G P Q R level i count (setPC (setPC w 14) 9):=by
        simpa [setPC] using wc
      have wr:=write_bounded B n x (setPC w 14) wc' rfl hi hB vg hQ run2.final_bound
      let z:=writeState (setPC w 14)
      have tc:Cursor G P Q R level i (count+1) (setPC z 9):=by
        have e700:v.natReg 700=G:=vc.fixed.header.count
        have e701:v.natReg 701=P:=vc.fixed.header.source
        have e702:v.natReg 702=Q:=vc.fixed.header.output
        have e703:v.natReg 703=R:=vc.fixed.header.directory
        have e704:v.natReg 704=0:=vc.fixed.zero
        have e705:v.natReg 705=1:=vc.fixed.one
        have e708:v.natReg 708=G+1:=vc.fixed.limit
        have e710:v.natReg 710=i:=vc.index
        have e707:v.natReg 707=count:=vc.count
        refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_,?_⟩
        all_goals simp [z,writeState,write,applyBlock,Op.apply,setPC,writeNat,next,
          w,e700,e701,e702,e703,e704,e705,e708,e710,e707,vl]
      have zpc:z.pc=17:=by simp [z,writeState,write,UniformTensorMonomialMachine.applyBlock_pc,setPC]
      have run3:=tick_bounded B n x z tc zpc hi hB vg wr.final_bound
      simpa [rowCost,less,greater,iteration,equal,v,w,z,writeState,tickState,setPC] using
        rd.trans (run1.trans (run2.trans (wr.trans run3)))

theorem rowCost_bound (level value : ℕ) : rowCost level value≤10 := by
  simp only [rowCost];split <;> (try split) <;> omega

def selection (depth : ℕ→ℕ) (level i : ℕ) : ℕ→List ℕ
  | 0=>[]
  | r+1=>if depth i=level then i::selection depth level (i+1) r
      else selection depth level (i+1) r
theorem selection_length (depth : ℕ→ℕ) (level i remaining : ℕ) :
    (selection depth level i remaining).length≤remaining := by
  induction remaining generalizing i with
  | zero => rfl
  | succ r ih =>
    simp only [selection];split
    · simp only [List.length_cons];have h:=ih (i+1);omega
    · exact (ih (i+1)).trans (by omega)
theorem selection_filter (depth : ℕ→ℕ) (level i remaining : ℕ) :
    selection depth level i remaining=
      (List.range' i remaining).filter (fun j=>decide (depth j=level)) := by
  induction remaining generalizing i with
  | zero => simp [selection]
  | succ r ih => simp [selection,List.range'_succ,ih,List.filter_cons]
theorem selection_zero (depth : ℕ→ℕ) (level G : ℕ) :
    selection depth level 0 G=selected G level depth := by
  simp [selection_filter,selected,List.range_eq_range']

theorem iteration_outside {G P Q R level i count value : ℕ} {s : State}
    (h:Cursor G P Q R level i count s) (j : ℕ)
    (hj:j<Q+count ∨ Q+count+1≤j) : (iteration level value s).natHeap j=s.natHeap j := by
  rw [iteration_heap h]
  split
  · apply Function.update_of_ne;omega
  · rfl
theorem iteration_depths {G P Q R level i count value : ℕ} {s : State}
    (h:Cursor G P Q R level i count s) (depth : ℕ→ℕ) (hd:Depths P G depth s)
    (hP:P+G≤Q) : Depths P G depth (iteration level value s) := by
  intro j hj
  rw [iteration_outside h (P+j) (Or.inl (by omega))]
  exact hd j hj
theorem iteration_bank {G P Q R level i value : ℕ} {s : State}
    (prior : List ℕ) (h:Cursor G P Q R level i prior.length s)
    (hb:Bank Q prior s) : Bank Q
      (prior++if value=level then [i] else []) (iteration level value s) := by
  intro j hj
  by_cases equal:value=level
  · simp only [ite_eq_left equal] at hj ⊢
    rw [iteration_heap h,ite_eq_left equal]
    by_cases old:j<prior.length
    · rw [Function.update_of_ne (by omega),List.getElem_append_left old]
      exact hb j old
    · have he:j=prior.length:=by
        simp only [List.length_append,List.length_singleton] at hj;omega
      subst j
      simp
  · simp only [ite_eq_right equal,List.append_nil] at hj ⊢
    rw [iteration_heap h,ite_eq_right equal]
    exact hb j hj

/-- The recursive invariant allows only an already-written prior. The public
entry theorem will start with the empty prior, without a supplied order bank. -/
theorem row_loop {G P Q R level i : ℕ} (remaining B n : ℕ) (x : Fin n→ℂ)
    (depth : ℕ→ℕ) (prior : List ℕ) (s : State)
    (h:Cursor G P Q R level i prior.length s) (hi:i+remaining=G)
    (hd:Depths P G depth s) (hb:Bank Q prior s) (hB:24≤B)
    (hP:P+G≤Q) (hQ:Q+prior.length+remaining≤B) (hs:WordBound B s) : ∃u t,
    BoundedRuns program n x B s t u ∧ t≤10*remaining ∧
    Cursor G P Q R level G (prior++selection depth level i remaining).length u ∧
    Bank Q (prior++selection depth level i remaining) u ∧ Depths P G depth u ∧
    (∀j,(j<Q+prior.length ∨ Q+prior.length+remaining≤j)→u.natHeap j=s.natHeap j) ∧
    Frame s u := by
  induction remaining generalizing i prior s with
  | zero =>
    have he:i=G:=by omega
    subst i
    refine ⟨s,0,.refl hs,by omega,?_,?_,hd,fun _ _=>rfl,frame_refl s⟩
    · simpa [selection] using h
    · simpa [selection] using hb
  | succ r ih =>
    have ilt:i<G:=by omega
    have hPB:P+G≤B:=by omega
    have run:=iteration_bounded B n x s h ilt (hd i ilt) hB hPB (by omega) hs
    let nextPrefix:=prior++if depth i=level then [i] else []
    have cur:Cursor G P Q R level (i+1) nextPrefix.length (iteration level (depth i) s):=by
      by_cases he:depth i=level
      all_goals simpa [nextPrefix,he,List.length_append] using (iteration_cursor (value:=depth i) h)
    have bank:Bank Q nextPrefix (iteration level (depth i) s):=iteration_bank prior h hb
    have dep:=iteration_depths (value:=depth i) h depth hd hP
    have cap:Q+nextPrefix.length+r≤B:=by
      dsimp [nextPrefix];split <;> simp only [List.length_append,List.length_singleton,List.length_nil] <;> omega
    obtain ⟨u,t,ru,tc,uc,ub,ud,uo,uf⟩:=ih (i:=i+1) nextPrefix
      (iteration level (depth i) s) cur (by omega) dep bank cap run.final_bound
    have same:nextPrefix++selection depth level (i+1) r=
        prior++selection depth level i (r+1):=by
      by_cases he:depth i=level <;> simp [nextPrefix,selection,he,List.append_assoc]
    refine ⟨u,rowCost level (depth i)+t,run.trans ru,?_,?_,?_,ud,?_,
      frame_trans (iteration_frame _ _ s) uf⟩
    · have hcost:=rowCost_bound level (depth i);omega
    · simpa [same] using uc
    · simpa [same] using ub
    · intro j hj
      have small:prior.length≤nextPrefix.length:=by simp [nextPrefix]
      have large:nextPrefix.length≤prior.length+1:=by
        dsimp [nextPrefix];split <;> simp
      rw [uo j (by omega)]
      exact iteration_outside h j (by omega)

structure LevelCursor (G P Q R level count : ℕ) (s : State) : Prop where
  fixed : Fixed G P Q R s
  pc : s.pc=5
  level : s.natReg 706=level
  count : s.natReg 707=count
def opened (s : State) := applyBlock head (setPC s 6)
def closed (s : State) := setPC (applyBlock close (setPC s 19)) 5
theorem opened_cursor {G P Q R level count : ℕ} {s : State}
    (h:LevelCursor G P Q R level count s) :
    Cursor G P Q R level 0 count (opened s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_,?_⟩
  all_goals simp [opened,head,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.output,h.fixed.header.directory,
    h.fixed.zero,h.fixed.one,h.fixed.limit,h.level,h.count]
theorem opened_heap {G P Q R level count : ℕ} {s : State}
    (h:LevelCursor G P Q R level count s) :
    (opened s).natHeap=Function.update s.natHeap (R+level) (some count) := by
  simp [opened,head,applyBlock,Op.apply,setPC,writeNat,next,h.fixed.header.directory,h.level,h.count]
theorem opened_frame (s : State) : Frame s (opened s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr; simp (disch:=omega) [opened,head,applyBlock,Op.apply,setPC,writeNat,next]
theorem opened_run {G P Q R level count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:LevelCursor G P Q R level count s) (hl:level<G+1)
    (hB:24≤B) (hR:R+G+2≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 4 (opened s) := by
  let v:=setPC s 6
  have hb:WordBound B v:=changePC_bound B s 6 hs (by omega)
  have enter:BoundedRuns program n x B s 1 v:=by
    have run:=branch_runs program B n 706 708 6 21 x s
      (by rw [h.pc];exact outer_at) hs (by omega) (by omega)
    simpa [h.level,h.fixed.limit,hl,v] using run
  have hr:readable head v:=by simp [head,readable,Op.readable]
  have countB:count≤B:=by rw [←h.count];exact hs.2.1 707
  have pk:peak head v≤B:=by
    simp [head,peak,Op.peak,Op.apply,setPC,v,writeNat,next,h.fixed.header.directory,
      h.level,h.count];omega
  have run:=block_runs head program 6 n B x v head_code rfl hb
    (by change 6+3≤B;omega) hr pk
  simpa [opened,v,head] using enter.trans run

theorem closed_cursor {G P Q R level count : ℕ} {s : State}
    (h:Cursor G P Q R level G count s) : LevelCursor G P Q R (level+1) count (closed s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,rfl,?_,?_⟩
  all_goals simp [closed,close,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.count,h.fixed.header.source,h.fixed.header.output,h.fixed.header.directory,
    h.fixed.zero,h.fixed.one,h.fixed.limit,h.level,h.count]
theorem closed_heap (s : State) : (closed s).natHeap=s.natHeap := rfl
theorem closed_frame (s : State) : Frame s (closed s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr;simp (disch:=omega) [closed,close,applyBlock,Op.apply,setPC,writeNat,next]
theorem closed_run {G P Q R level count : ℕ} (B n : ℕ) (x : Fin n→ℂ)
    (s : State) (h:Cursor G P Q R level G count s) (hl:level<G+1)
    (hB:24≤B) (hG:G+1≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 3 (closed s) := by
  let v:=setPC s 19
  have hb:WordBound B v:=changePC_bound B s 19 hs (by omega)
  have enter:BoundedRuns program n x B s 1 v:=by
    have run:=branch_runs program B n 710 700 10 19 x s
      (by rw [h.pc];exact inner_at) hs (by omega) (by omega)
    simpa [h.index,h.fixed.header.count,v] using run
  have hr:readable close v:=by simp [close,readable,Op.readable]
  have pk:peak close v≤B:=by simp [close,peak,Op.peak,v,setPC,h.level,h.fixed.one];omega
  have run:=block_runs close program 19 n B x v close_code rfl hb
    (by change 19+1≤B;omega) hr pk
  have ipc:(applyBlock close v).pc=20:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have jump:BoundedRuns program n x B (applyBlock close v) 1 (closed s):=
    .next run.final_bound (by rw [step,ipc,close_at];rfl)
      (.refl (changePC_bound B _ 5 run.final_bound (by omega)))
  simpa [close] using enter.trans (run.trans jump)

def levels (G level remaining : ℕ) (depth : ℕ→ℕ) : List ℕ :=
  (List.range' level remaining).flatMap (fun d=>selected G d depth)
theorem levels_succ (G level remaining : ℕ) (depth : ℕ→ℕ) :
    levels G level (remaining+1) depth=selected G level depth++levels G (level+1) remaining depth := by
  simp [levels,List.range'_succ]
theorem levels_length (G level remaining : ℕ) (depth : ℕ→ℕ) :
    (levels G level remaining depth).length≤remaining*G := by
  induction remaining generalizing level with
  | zero => simp [levels]
  | succ r ih =>
    rw [levels_succ,List.length_append]
    have h:=selected_length G level depth
    have h':=ih (level+1)
    nlinarith

def processed (G level : ℕ) (depth : ℕ → ℕ) : List ℕ :=
  (List.range level).flatMap (fun d => selected G d depth)

theorem processed_length (G level : ℕ) (depth : ℕ → ℕ) :
    (processed G level depth).length = offset G level depth := rfl

theorem processed_zero (G : ℕ) (depth : ℕ → ℕ) : processed G 0 depth = [] := rfl

theorem processed_succ (G level : ℕ) (depth : ℕ → ℕ) :
    processed G (level+1) depth = processed G level depth ++ selected G level depth := by
  simp [processed,List.range_succ]

theorem processed_order (G : ℕ) (depth : ℕ → ℕ) : processed G (G+1) depth = order G depth := rfl

def Directory (R G level : ℕ) (depth : ℕ → ℕ) (s : State) : Prop :=
  ∀ j,j < level → s.natHeap (R+j) = some (offset G j depth)

theorem opened_bank {G P Q R level : ℕ} {depth : ℕ → ℕ} {s : State}
    (h : LevelCursor G P Q R level (offset G level depth) s)
    (hb : Bank Q (processed G level depth) s) (hcap : Q+offset G level depth ≤ R) :
    Bank Q (processed G level depth) (opened s) := by
  intro j hj
  have hl : j < offset G level depth := hj
  rw [opened_heap h,Function.update_of_ne (by omega)]
  exact hb j hj

theorem opened_depths {G P Q R level count : ℕ} {s : State}
    (h : LevelCursor G P Q R level count s) (depth : ℕ → ℕ)
    (hd : Depths P G depth s) (hP : P+G ≤ R) : Depths P G depth (opened s) := by
  intro j hj
  rw [opened_heap h,Function.update_of_ne (by omega)]
  exact hd j hj

theorem opened_directory {G P Q R level : ℕ} {depth : ℕ → ℕ} {s : State}
    (h : LevelCursor G P Q R level (offset G level depth) s)
    (hd : Directory R G level depth s) : Directory R G (level+1) depth (opened s) := by
  intro j hj
  rw [opened_heap h]
  by_cases he : j=level
  · simp [he,Function.update]
  · rw [Function.update_of_ne (by omega)]
    exact hd j (by omega)

/-- Every level stores its actual initial output offset and scans each gate once. -/
theorem one_level {G P Q R level : ℕ} (B n : ℕ) (x : Fin n → ℂ)
    (depth : ℕ → ℕ) (s : State)
    (h : LevelCursor G P Q R level (offset G level depth) s) (hl : level < G+1)
    (hd : Depths P G depth s) (hb : Bank Q (processed G level depth) s)
    (dir : Directory R G level depth s)
    (hP : P+G ≤ Q) (hQ : Q+G*(G+1) ≤ R) (hR : R+G+2 ≤ B)
    (hB : 24 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedRuns program n x B s t u ∧ t ≤ 10*G+7 ∧
      LevelCursor G P Q R (level+1) (offset G (level+1) depth) u ∧
      Bank Q (processed G (level+1) depth) u ∧ Directory R G (level+1) depth u ∧
      Depths P G depth u ∧ Outside Q (G*(G+1)) R (G+2) s u ∧ Frame s u := by
  have off := offset_bound G level depth
  have capG : offset G level depth+G ≤ G*(G+1) := by nlinarith
  have cap : Q+offset G level depth+G ≤ R := by omega
  have openRun := opened_run B n x s h hl hB hR hs
  have cur := opened_cursor h
  have bank := opened_bank h hb (by omega)
  have depths := opened_depths h depth hd (by omega)
  have directory := opened_directory h dir
  obtain ⟨v,t,run,cost,vc,vb,vd,vo,vf⟩ := row_loop G B n x depth (processed G level depth) (opened s)
    (by simpa only [processed_length] using cur) (by simp) depths bank hB hP
    (by rw [processed_length]; omega) openRun.final_bound
  have closeRun := closed_run B n x v vc hl hB (by omega) run.final_bound
  have exactList : processed G level depth ++ selection depth level 0 G =
      processed G (level+1) depth := by rw [selection_zero,processed_succ]
  have uc : LevelCursor G P Q R (level+1) (offset G (level+1) depth) (closed v) := by
    have out := closed_cursor vc
    rw [exactList,processed_length] at out
    exact out
  refine ⟨closed v,4+t+3,openRun.trans (run.trans closeRun),by omega,uc,?_,?_,vd,?_,?_⟩
  · intro j hj
    rw [closed_heap]
    simpa only [exactList] using vb j (by simpa only [exactList] using hj)
  · intro j hj
    rw [closed_heap,vo (R+j) (Or.inr (by rw [processed_length]; omega))]
    exact directory j hj
  · intro j hjQ hjR
    rw [closed_heap,vo j (by rw [processed_length]; omega),opened_heap h,
      Function.update_of_ne (by omega)]
  · exact frame_trans (opened_frame s) (frame_trans vf (closed_frame v))

/-- Consecutive physical level scans start with the already emitted prefix. -/
theorem outer_loop {G P Q R level : ℕ} (remaining B n : ℕ) (x : Fin n → ℂ)
    (depth : ℕ → ℕ) (s : State)
    (h : LevelCursor G P Q R level (offset G level depth) s) (hl : level+remaining=G+1)
    (hd : Depths P G depth s) (hb : Bank Q (processed G level depth) s)
    (dir : Directory R G level depth s)
    (hP : P+G ≤ Q) (hQ : Q+G*(G+1) ≤ R) (hR : R+G+2 ≤ B)
    (hB : 24 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedRuns program n x B s t u ∧ t ≤ (10*G+7)*remaining ∧
      LevelCursor G P Q R (G+1) (offset G (G+1) depth) u ∧
      Bank Q (order G depth) u ∧ Directory R G (G+1) depth u ∧
      Depths P G depth u ∧ Outside Q (G*(G+1)) R (G+2) s u ∧ Frame s u := by
  induction remaining generalizing level s with
  | zero =>
    have he : level=G+1 := by omega
    subst level
    exact ⟨s,0,.refl hs,by simp,h,hb,dir,hd,fun _ _ _ => rfl,frame_refl s⟩
  | succ remaining ih =>
    obtain ⟨v,t,run,cost,vc,vb,vd,vdep,vo,vf⟩ := one_level B n x depth s h (by omega)
      hd hb dir hP hQ hR hB hs
    obtain ⟨u,t',run',cost',uc,ub,ud,udep,uo,uf⟩ := ih v vc (by omega) vdep vb vd run.final_bound
    refine ⟨u,t+t',run.trans run',?_,uc,ub,ud,udep,?_,frame_trans vf uf⟩
    · nlinarith
    · intro j hjQ hjR
      exact (uo j hjQ hjR).trans (vo j hjQ hjR)

theorem boot_fixed {G P Q R : ℕ} {s : State} (h : Header G P Q R s) :
    Fixed G P Q R (applyBlock boot s) := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next,
    h.count,h.source,h.output,h.directory]

theorem boot_cursor {G P Q R : ℕ} {s : State} (h : Header G P Q R s) (hp : s.pc=0) :
    LevelCursor G P Q R 0 0 (applyBlock boot s) := by
  refine ⟨boot_fixed h,?_,?_,?_⟩
  · rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
  all_goals simp [boot,applyBlock,Op.apply,writeNat,next]

theorem boot_frame (s : State) : Frame s (applyBlock boot s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [boot,applyBlock,Op.apply,writeNat,next]

def finalized (s : State) := applyBlock finish (setPC s 21)

theorem finalized_heap {G P Q R level count : ℕ} {s : State}
    (h : LevelCursor G P Q R level count s) :
    (finalized s).natHeap = Function.update s.natHeap (R+level) (some count) := by
  simp [finalized,finish,applyBlock,Op.apply,setPC,writeNat,next,
    h.fixed.header.directory,h.level,h.count]

theorem finalized_frame (s : State) : Frame s (finalized s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp (disch := omega) [finalized,finish,applyBlock,Op.apply,setPC,writeNat,next]

/-- Universal initialized execution. No output order or directory is supplied. -/
theorem execution (G P Q R B n : ℕ) (x : Fin n → ℂ) (depth : ℕ → ℕ) (s : State)
    (h : Header G P Q R s) (hpc : s.pc=0) (hd : Depths P G depth s)
    (hP : P+G ≤ Q) (hQ : Q+G*(G+1) ≤ R) (hR : R+G+2 ≤ B)
    (hB : 24 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget G ∧ u.pc=23 ∧
      Header G P Q R u ∧ Bank Q (order G depth) u ∧ Directory R G (G+2) depth u ∧
      Depths P G depth u ∧ Outside Q (G*(G+1)) R (G+2) s u ∧ Frame s u := by
  have bootReadable : readable boot s := by simp [readable,boot,Op.readable]
  have pk : peak boot s ≤ B := by
    simp [peak,boot,Op.peak,Op.apply,writeNat,next,h.count]
    omega
  have start := block_runs boot program 0 n B x s boot_code hpc hs
    (by change 0+5 ≤ B; omega) bootReadable pk
  obtain ⟨v,t,run,cost,vc,vb,vd,vdep,vo,vf⟩ := outer_loop (G+1) B n x depth (applyBlock boot s)
    (by change LevelCursor G P Q R 0 0 (applyBlock boot s); exact boot_cursor h hpc) (by simp) hd
    (by intro j hj; simp [processed] at hj) (by intro j hj; omega)
    hP hQ hR hB start.final_bound
  have stop := branch_runs program B n 706 708 6 21 x v
    (by rw [vc.pc]; exact outer_at) run.final_bound (by omega) (by omega)
  have cmp : ¬ v.natReg 706 < v.natReg 708 := by rw [vc.level,vc.fixed.limit]; omega
  simp only [cmp,ite_false] at stop
  let w := setPC v 21
  have finishReadable : readable finish w := by simp [readable,finish,Op.readable]
  have countBound : offset G (G+1) depth ≤ B := by
    rw [←vc.count]; exact run.final_bound.2.1 707
  have finishPeak : peak finish w ≤ B := by
    simp [peak,finish,Op.peak,Op.apply,w,setPC,writeNat,next,
      vc.fixed.header.directory,vc.level,vc.count]
    omega
  have last := block_runs finish program 21 n B x w finish_code rfl stop.final_bound
    (by change 21+2 ≤ B; omega) finishReadable finishPeak
  let u := finalized v
  have pc : u.pc=23 := by
    change (applyBlock finish (setPC v 21)).pc=23
    rw [UniformTensorMonomialMachine.applyBlock_pc]; rfl
  have halt : BoundedExecution program n x B u 1 u := .halt last.final_bound
    (by rw [step,pc,halt_at])
  refine ⟨u,5+t+1+2+1,?_,?_,pc,?_,?_,?_,?_,?_,?_⟩
  · simpa only [show boot.length=5 from rfl,show finish.length=2 from rfl,Nat.add_assoc] using
      (start.trans (run.trans (stop.trans last))).executes halt
  · unfold runtimeBudget
    nlinarith
  · refine ⟨?_,?_,?_,?_⟩
    all_goals simp [u,finalized,finish,applyBlock,Op.apply,setPC,writeNat,next,
      vc.fixed.header.count,vc.fixed.header.source,vc.fixed.header.output,vc.fixed.header.directory]
  · have length : (order G depth).length ≤ (G+1)*G := by
      have hh := offset_bound G (G+1) depth
      exact hh
    intro j hj
    rw [finalized_heap vc,Function.update_of_ne (by nlinarith)]
    exact vb j hj
  · intro j hj
    rw [finalized_heap vc]
    by_cases he : j=G+1
    · simp [he,Function.update]
    · rw [Function.update_of_ne (by omega)]
      exact vd j (by omega)
  · intro j hj
    rw [finalized_heap vc,Function.update_of_ne (by omega)]
    exact vdep j hj
  · intro j hjQ hjR
    rw [finalized_heap vc,Function.update_of_ne (by omega)]
    exact vo j hjQ hjR
  · exact frame_trans (boot_frame s) (frame_trans vf (finalized_frame v))

/-- Every ordinal occurs only in its own depth bucket. -/
theorem order_mem (G : ℕ) (depth : ℕ → ℕ) (i : ℕ) :
    i ∈ order G depth ↔ i < G ∧ depth i ≤ G := by
  constructor
  · intro hi
    obtain ⟨level,hl,hm⟩ := List.mem_flatMap.mp hi
    have hl' : level < G+1 := List.mem_range.mp hl
    have hs := (selected_mem G level depth i).mp hm
    exact ⟨hs.1,by omega⟩
  · rintro ⟨hi,hd⟩
    exact List.mem_flatMap.mpr ⟨depth i,List.mem_range.mpr (by omega),
      (selected_mem G (depth i) depth i).mpr ⟨hi,rfl⟩⟩

theorem order_nodup (G : ℕ) (depth : ℕ → ℕ) : (order G depth).Nodup := by
  unfold order
  apply List.nodup_flatMap.mpr
  refine ⟨fun level _ => selected_nodup G level depth,?_⟩
  have hn : (List.range (G+1)).Nodup := List.nodup_range
  apply hn.imp
  intro a b hab i hi hj
  have ha := (selected_mem G a depth i).mp hi
  have hb := (selected_mem G b depth i).mp hj
  exact hab (ha.2.symm.trans hb.2)

/-- The internally printed order is a full permutation for actual depth labels. -/
theorem order_perm (G : ℕ) (depth : ℕ → ℕ) (hd : ∀ i,i<G → depth i ≤ G) :
    (order G depth).Perm (List.range G) := by
  apply (List.perm_ext_iff_of_nodup (order_nodup G depth) List.nodup_range).mpr
  intro i
  rw [order_mem,List.mem_range]
  exact ⟨And.left,fun hi => ⟨hi,hd i hi⟩⟩

theorem order_length (G : ℕ) (depth : ℕ → ℕ) (hd : ∀ i,i<G → depth i ≤ G) :
    (order G depth).length=G := by
  simpa using (order_perm G depth hd).length_eq

theorem range_increasing (n : ℕ) : (List.range n).Pairwise (fun a b => a<b) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [List.getElem_range] using hij

/-- The stable order within a bucket is the original gate chronology. -/
theorem selected_increasing (G level : ℕ) (depth : ℕ → ℕ) :
    (selected G level depth).Pairwise (fun a b => a<b) :=
  (range_increasing G).filter (fun i => decide (depth i=level))

/-- Earlier buckets have smaller depths; ties retain strictly increasing ordinals. -/
theorem order_stable (G : ℕ) (depth : ℕ → ℕ) :
    (order G depth).Pairwise (fun a b => depth a < depth b ∨ (depth a=depth b ∧ a<b)) := by
  unfold order
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro level _
    apply (selected_increasing G level depth).imp_of_mem
    intro a b ha hb hab
    have hda := (selected_mem G level depth a).mp ha
    have hdb := (selected_mem G level depth b).mp hb
    exact Or.inr ⟨hda.2.trans hdb.2.symm,hab⟩
  · apply (range_increasing (G+1)).imp
    intro a b hab i hi j hj
    have hdi := (selected_mem G a depth i).mp hi
    have hdj := (selected_mem G b depth j).mp hj
    exact Or.inl (by rw [hdi.2,hdj.2]; exact hab)

theorem order_monotone (G : ℕ) (depth : ℕ → ℕ) :
    (order G depth).Pairwise (fun a b => depth a ≤ depth b) := by
  apply (order_stable G depth).imp
  intro a b hab
  exact hab.elim Nat.le_of_lt (fun he => Nat.le_of_eq he.1)

/-- The directory's terminal offset equals the actual emitted width. -/
theorem terminal_offset (G : ℕ) (depth : ℕ → ℕ) :
    offset G (G+1) depth=(order G depth).length := rfl

theorem offset_succ (G level : ℕ) (depth : ℕ → ℕ) :
    offset G (level+1) depth = offset G level depth + (selected G level depth).length := by
  change (processed G (level+1) depth).length = _
  rw [processed_succ,List.length_append,processed_length]

theorem offset_zero (G : ℕ) (depth : ℕ → ℕ) : offset G 0 depth = 0 := rfl

/-- Gate labels use the real typed runDepth, at the literal physical node ports. -/
def typedDepth {r N G : ℕ} (p : UniformReplayPrint.Program r N G) (i : ℕ) : ℕ :=
  UniformDAGLayers.natLevel p (N+1+i)

theorem natLevel_evaluate {r N G : ℕ} (p : UniformReplayPrint.Program r N G)
    (a : ℕ) (ha : a < N+1+G) :
    UniformDAGLayers.natLevel p a =
      UniformDAGDepthMachine.evaluate (N+1) (UniformDAGDepthMachine.rows p) (fun _ => 0) a := by
  simpa only [UniformDAGLayers.natLevel,dite_eq_left ha] using
    (UniformDAGDepthMachine.evaluate_typed p ⟨a,ha⟩).symm

theorem typedDepth_bound {r N G : ℕ} (p : UniformReplayPrint.Program r N G) :
    ∀ i,i<G → typedDepth p i ≤ G := by
  intro i hi
  rw [typedDepth,natLevel_evaluate p _ (by omega)]
  have h := UniformDAGDepthMachine.evaluate_bound (N+1) 0
    (UniformDAGDepthMachine.rows p) (fun _ => 0) (by simp) (N+1+i)
  simpa only [Nat.zero_add,UniformDAGDepthMachine.rows_length] using h

/-- This is exactly the physically generated bank returned by Depth35. -/
theorem depths_of_typed_bank {r N G P : ℕ} (p : UniformReplayPrint.Program r N G)
    (s : State)
    (hb : ∀ a : Fin (N+1+G),s.natHeap (P+a.val) =
      some (UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a)) :
    Depths (P+N+1) G (typedDepth p) s := by
  intro i hi
  have ha : N+1+i < N+1+G := by omega
  rw [typedDepth,UniformDAGLayers.natLevel,dite_eq_left ha]
  convert hb ⟨N+1+i,ha⟩ using 1
  simp only [Nat.add_assoc]

/-- Actual typed labels yield a complete stable gate permutation, with no
    preprinted ordering or directory entry premise. Header setting is explicit. -/
theorem typed_execution {r N G : ℕ} (p : UniformReplayPrint.Program r N G)
    (P Q R B n : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Header G (P+N+1) Q R s) (hpc : s.pc=0)
    (hb : ∀ a : Fin (N+1+G),s.natHeap (P+a.val) =
      some (UniformToeplitzCrossDAG.runDepth p (fun _ => 0) a))
    (hP : P+N+1+G ≤ Q) (hQ : Q+G*(G+1) ≤ R) (hR : R+G+2 ≤ B)
    (hB : 24 ≤ B) (hs : WordBound B s) :
    ∃ u t, BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget G ∧ u.pc=23 ∧
      Header G (P+N+1) Q R u ∧ Bank Q (order G (typedDepth p)) u ∧
      Directory R G (G+2) (typedDepth p) u ∧ Depths (P+N+1) G (typedDepth p) u ∧
      (order G (typedDepth p)).Perm (List.range G) ∧
      (order G (typedDepth p)).length=G ∧
      (order G (typedDepth p)).Pairwise
        (fun a b => typedDepth p a < typedDepth p b ∨ (typedDepth p a=typedDepth p b ∧ a<b)) ∧
      Outside Q (G*(G+1)) R (G+2) s u ∧ Frame s u := by
  obtain ⟨u,t,run,cost,pc,header,bank,dir,dep,outside,frame⟩ :=
    execution G (P+N+1) Q R B n x (typedDepth p) s h hpc (depths_of_typed_bank p s hb)
      hP hQ hR hB hs
  exact ⟨u,t,run,cost,pc,header,bank,dir,dep,order_perm G _ (typedDepth_bound p),
    order_length G _ (typedDepth_bound p),order_stable G _,outside,frame⟩

/-- Saved global preparation headers are disjoint from scratch704..711. -/
theorem Frame.saved {s u : State} (h : Frame s u) :
    ∀ r,100 ≤ r → r ≤ 106 → u.natReg r = s.natReg r := by
  intro r _ hr
  exact h.2.2.2.2 r (Or.inl (by omega))

/-- Ties keep original ordinals; out-of-range diagnostic labels are not selected. -/
theorem stable_fixture : order 5 (fun i => [2,1,2,0,1][i]?.getD 0) = [3,1,4,0,2] := by decide

theorem empty_fixture : order 0 (fun _ => 0) = [] := rfl

theorem out_of_range_fixture : order 3 (fun i => [0,4,1][i]?.getD 0) = [0,2] := by decide

end
end ExactFourierCircuits.UniformDAGBucketMachine
