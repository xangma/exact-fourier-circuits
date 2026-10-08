import UniformChunkPortMachine
import UniformColorLayerTableMachine
import UniformToeplitzCrossDAG
import UniformCrossShearTableMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCrossBroadcastTableMachine
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/- Actual output-broadcast rows: target+j, borrowed[gates-a+j], +1.
Nat3100..3105=a,gates,target,borrowed-table,row-table,positive coefficient
address. The physical borrowed coordinates are read, never enumerated by
the host. Nat894 is the generated matching count. -/
def boot : List Op := [.literal 3110 0,.literal 3111 1,.literal 3112 3,
 .sub 3113 3101 3100,.add 894 3100 3110]
def body : List Op := [.add 3114 3113 3110,.add 3114 3103 3114,.getNat 3115 3114,
 .add 3116 3102 3110,.mul 3117 3112 3110,.add 3117 3104 3117,
 .putNat 3117 3116,.add 3117 3117 3111,.putNat 3117 3115,
 .add 3117 3117 3111,.putNat 3117 3105,.add 3110 3110 3111]
def program : Program := boot.map Op.code ++ [.branchLT 3110 3100 6 19] ++
 body.map Op.code ++ [.jump 5,.halt]
theorem program_length : program.length=20 := rfl
theorem boot_code : BlockAt boot program 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl
theorem body_code : BlockAt body program 6 := by
 intro i hi;change i<12 at hi;interval_cases i <;> rfl
theorem branch_at : program[5]?=some (.branchLT 3110 3100 6 19) := rfl
theorem jump_at : program[18]?=some (.jump 5) := rfl
theorem halt_at : program[19]?=some .halt := rfl

noncomputable section

structure Header (a g T Q D P : ℕ) (s : State) : Prop where
 count : s.natReg 3100=a
 gates : s.natReg 3101=g
 target : s.natReg 3102=T
 borrowed : s.natReg 3103=Q
 output : s.natReg 3104=D
 coefficient : s.natReg 3105=P
structure Cursor (a g T Q D P i : ℕ) (s : State) : Prop where
 header : Header a g T Q D P s
 pc : s.pc=5
 index : s.natReg 3110=i
 one : s.natReg 3111=1
 three : s.natReg 3112=3
 offset : s.natReg 3113=g-a
 generated : s.natReg 894=a
def Borrowed (Q g : ℕ) (b : ℕ→ℕ) (s : State) : Prop :=
 ∀j,j<g→s.natHeap (Q+j)=some (b j)
def Rows (D T P g a i : ℕ) (b : ℕ→ℕ) (s : State) : Prop :=
 ∀j,j < i → s.natHeap (D+3*j)=some (T+j) ∧
  s.natHeap (D+3*j+1)=some (b (g-a+j)) ∧ s.natHeap (D+3*j+2)=some P
def Outside (D a : ℕ) (s u : State) : Prop :=
 ∀z,z<D∨D+3*a≤z→u.natHeap z=s.natHeap z
def Frame (s u : State) : Prop :=
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧
 u.rootOrders=s.rootOrders ∧ ∀r,r≠894→(r<3110∨3117<r)→u.natReg r=s.natReg r
def round (s : State) : State := setPC (applyBlock body (setPC s 6)) 5

theorem boot_cursor {a g T Q D P : ℕ} {s : State} (h : Header a g T Q D P s)
 (pc : s.pc=0) : Cursor a g T Q D P 0 (applyBlock boot s) := by
 refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,pc,h.count,h.gates,h.target,
  h.borrowed,h.output,h.coefficient]

theorem round_cursor {a g T Q D P i : ℕ} {s : State} (h : Cursor a g T Q D P i s) :
 Cursor a g T Q D P (i+1) (round s) := by
 refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,rfl,?_,?_,?_,?_,?_⟩
 all_goals simp [round,body,applyBlock,Op.apply,setPC,writeNat,next,h.index,h.one,h.three,h.offset,
  h.generated,h.header.count,h.header.gates,h.header.target,h.header.borrowed,h.header.output,h.header.coefficient]

theorem frame_boot (s : State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r h h'
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
theorem frame_round (s : State) : Frame s (round s) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r h h'
 simp (disch:=omega) [round,body,applyBlock,Op.apply,setPC,writeNat,next]
theorem Frame.trans {s u v : State} (f : Frame s u) (h : Frame u v) : Frame s v :=
 ⟨h.1.trans f.1,h.2.1.trans f.2.1,h.2.2.1.trans f.2.2.1,h.2.2.2.1.trans f.2.2.2.1,
  fun r hr hr'=>(h.2.2.2.2 r hr hr').trans (f.2.2.2.2 r hr hr')⟩
theorem Outside.trans {D a : ℕ} {s u v : State} (f : Outside D a s u) (h : Outside D a u v) :
 Outside D a s v := fun z hz=>(h z hz).trans (f z hz)

theorem round_heap {a g T Q D P i : ℕ} {b : ℕ→ℕ} {s : State}
 (h : Cursor a g T Q D P i s) (hi : i<a) (ag : a≤g) (bank : Borrowed Q g b s) :
 (round s).natHeap=Function.update (Function.update (Function.update s.natHeap
  (D+3*i) (some (T+i))) (D+3*i+1) (some (b (g-a+i)))) (D+3*i+2) (some P) := by
 have read:=bank (g-a+i) (by omega)
 simp [round,body,applyBlock,Op.apply,setPC,writeNat,next,h.index,h.one,h.three,h.offset,
  h.header.target,h.header.borrowed,h.header.output,h.header.coefficient,read,Nat.add_assoc]

theorem round_outside {a g T Q D P i : ℕ} {b : ℕ→ℕ} {s : State}
 (h : Cursor a g T Q D P i s) (hi : i<a) (ag : a≤g) (bank : Borrowed Q g b s) :
 Outside D a s (round s) := by
 intro z hz
 rw [round_heap h hi ag bank]
 simp (disch:=omega)

theorem round_rows {a g T Q D P i : ℕ} {b : ℕ→ℕ} {s : State}
 (h : Cursor a g T Q D P i s) (hi : i<a) (ag : a≤g) (bank : Borrowed Q g b s)
 (rows : Rows D T P g a i b s) : Rows D T P g a (i+1) b (round s) := by
 intro j hj
 rw [round_heap h hi ag bank]
 by_cases eq:j=i
 · subst j
   simp (disch:=omega)
 · have old:=rows j (by omega)
   simp (disch:=omega) [old.1,old.2.1,old.2.2]

theorem borrowed_transport {D a Q g : ℕ} {b : ℕ→ℕ} {s u : State}
 (bank : Borrowed Q g b s) (out : Outside D a s u) (sep : Q+g≤D) : Borrowed Q g b u := by
 intro j hj
 rw [out (Q+j) (Or.inl (by omega))]
 exact bank j hj

theorem boot_runs (n B a g T Q D P : ℕ) (x : Fin n→ℂ) (s : State)
 (h : Header a g T Q D P s) (pc : s.pc=0) (bound : WordBound B s) (code : 20≤B) :
 BoundedRuns program n x B s 5 (applyBlock boot s) := by
 have ac:a≤B:=by rw [←h.count];exact bound.2.1 _
 have gc:g≤B:=by rw [←h.gates];exact bound.2.1 _
 have cap:peak boot s≤B := by
  simp [boot,peak,Op.peak,Op.apply,writeNat,next,h.count,h.gates,ac,
   show g-a≤B from (Nat.sub_le g a).trans gc,show 3≤B by omega]
 exact block_runs boot program 0 n B x s boot_code pc bound (by simp [boot];omega)
  (by simp [boot,readable,Op.readable]) cap

theorem round_runs (n B a g T Q D P i : ℕ) (x : Fin n→ℂ) (b : ℕ→ℕ) (s : State)
 (h : Cursor a g T Q D P i s) (hi : i<a) (ag : a≤g) (bank : Borrowed Q g b s)
 (sep : Q+g≤D) (rowsEnd : D+3*a≤B) (targetEnd : T+a≤B)
 (bound : WordBound B s) (code : 20≤B) :
 BoundedRuns program n x B s 14 (round s) := by
 have read:=bank (g-a+i) (by omega)
 have vb: b (g-a+i)≤B:=(bound.2.2.1 _ _ read).2
 have cb:P≤B:=by rw [←h.header.coefficient];exact bound.2.1 _
 have startBound:=changePC_bound B s 6 bound (by omega)
 have first : BoundedRuns program n x B s 1 (setPC s 6) := by
  refine .next bound ?_ (.refl startBound)
  simp [step,branch_at,h.pc,h.index,h.header.count,hi,setPC]
 have ready:readable body (setPC s 6) := by
  simp [body,readable,Op.readable,Op.apply,setPC,writeNat,next,h.index,h.offset,
   h.header.borrowed,read]
 have cap:peak body (setPC s 6)≤B := by
  simp [body,peak,Op.peak,Op.apply,setPC,writeNat,next,h.index,h.one,h.three,h.offset,
   h.header.target,h.header.borrowed,h.header.output,h.header.coefficient,read,Nat.add_assoc]
  omega
 have middle:=block_runs body program 6 n B x (setPC s 6) body_code rfl startBound
  (by simp [body];omega) ready cap
 have endBound:=changePC_bound B _ 5 middle.final_bound (by omega)
 have last : BoundedRuns program n x B (applyBlock body (setPC s 6)) 1 (round s) := by
  refine .next middle.final_bound ?_ (.refl endBound)
  simp [step,jump_at,round,body,applyBlock,Op.apply,setPC,writeNat,next]
 exact (first.trans middle).trans last

theorem loop_execution (n B a g T Q D P count : ℕ) (x : Fin n→ℂ) (b : ℕ→ℕ) :
 ∀i s,i+count=a→Cursor a g T Q D P i s→a≤g→Borrowed Q g b s→
 Rows D T P g a i b s→Q+g≤D→D+3*a≤B→T+a≤B→WordBound B s→20≤B→
 ∃u,BoundedExecution program n x B s (14*count+2) u ∧ Rows D T P g a a b u ∧
 Borrowed Q g b u ∧ Outside D a s u ∧ Frame s u ∧ u.natReg 894=a ∧ u.pc=19 := by
 induction count with
 | zero =>
  intro i s eq h ag bank rows sep endRows endTarget bound code
  have ia:i=a:=by omega
  let u:=setPC s 19
  have ub:=changePC_bound B s 19 bound (by omega)
  refine ⟨u,.next bound (u:=u) ?_ (.halt ub ?_),?_,bank,fun _ _=>rfl,
   ⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩,h.generated,rfl⟩
  · simp [step,branch_at,h.pc,h.index,h.header.count,ia,u,setPC]
  · simp [step,halt_at,u,setPC]
  · simpa [ia,Rows,u,setPC] using rows
 | succ count ih =>
  intro i s eq h ag bank rows sep endRows endTarget bound code
  have hi:i<a:=by omega
  have first:=round_runs n B a g T Q D P i x b s h hi ag bank sep endRows endTarget bound code
  have out:=round_outside h hi ag bank
  have newBank:=borrowed_transport bank out sep
  have newRows:=round_rows h hi ag bank rows
  obtain ⟨u,last,result,bu,ou,fu,cu,pcu⟩:=ih (i+1) (round s) (by omega)
   (round_cursor h) ag newBank newRows sep endRows endTarget first.final_bound code
  refine ⟨u,?_,result,bu,out.trans ou,(frame_round s).trans fu,cu,pcu⟩
  convert first.executes last using 1
  omega

/-- Every actual output-broadcast row is produced by physical Nat loads and
stores; the count and entire triple table are outputs, not entry certificates. -/
theorem execution (n B a g T Q D P : ℕ) (x : Fin n→ℂ) (b : ℕ→ℕ) (s : State)
 (h : Header a g T Q D P s) (pc : s.pc=0) (ag : a≤g) (bank : Borrowed Q g b s)
 (sep : Q+g≤D) (rowsEnd : D+3*a≤B) (targetEnd : T+a≤B)
 (bound : WordBound B s) (code : 20≤B) :
 ∃u,BoundedExecution program n x B s (14*a+7) u ∧ Rows D T P g a a b u ∧
 Borrowed Q g b u ∧ Outside D a s u ∧ Frame s u ∧ u.natReg 894=a ∧ u.pc=19 := by
 have first:=boot_runs n B a g T Q D P x s h pc bound code
 obtain ⟨u,last,result,bu,out,frame,cu,pcu⟩:=loop_execution n B a g T Q D P a x b 0
  (applyBlock boot s) (by omega) (boot_cursor h pc) ag bank (by intro j hj;omega)
  sep rowsEnd targetEnd first.final_bound code
 refine ⟨u,?_,result,bu,out,(frame_boot s).trans frame,cu,pcu⟩
 convert first.executes last using 1
 omega

def rowList (a g T P : ℕ) (b : ℕ→ℕ) : List UniformInPlaceMachine.Row :=
 (List.finRange a).map (fun j=>⟨T+j.val,b (g-a+j.val),P⟩)
theorem rowList_length (a g T P : ℕ) (b : ℕ→ℕ) : (rowList a g T P b).length=a := by
 simp [rowList]
theorem rows_table {a g T D P : ℕ} {b : ℕ→ℕ} {s : State}
 (h : Rows D T P g a a b s) : UniformCrossShearTableMachine.Table D (rowList a g T P b) s := by
 intro j hj
 have ja:j<a:=by simpa [rowList] using hj
 simpa [rowList,UniformCrossShearTableMachine.RowFields] using h j ja

/-- A sum-of-three cross graph outputs exactly its last a internal nodes. -/
theorem sumThree_output_index {r e a : ℕ} (A B D : UniformToeplitzCrossDAG.DAG r e a) (j : Fin a) :
 ((A.sumThree B D).outputs j).val=e+1+((A.sumThree B D).size-a)+j.val := by
 simp only [UniformToeplitzCrossDAG.DAG.sumThree,OAI.ExactFourier.gateIndex]
 omega

theorem cross_output_index (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
 (he : e≤UniformRadixTwoDAG.width k) (j : Fin a) :
 ((UniformToeplitzCrossDAG.crossDAG k a e ha he).outputs j).val=
 e+1+((UniformToeplitzCrossDAG.crossDAG k a e ha he).size-a)+j.val :=
 sumThree_output_index _ _ _ j

/-- The producer's source index is the actual ChunkPort image of the typed
cross output, for either enabled sweep. No host-generated output list enters. -/
theorem cross_source (k a e source target : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
 (he : e≤UniformRadixTwoDAG.width k) (b : ℕ→ℕ) (j : Fin a) :
 UniformChunkPortMachine.mapped e (UniformToeplitzCrossDAG.crossDAG k a e ha he).size
  source target b ((UniformToeplitzCrossDAG.crossDAG k a e ha he).outputs j).val=
 b ((UniformToeplitzCrossDAG.crossDAG k a e ha he).size-a+j.val) := by
 rw [cross_output_index]
 rw [Nat.add_assoc]
 apply UniformChunkPortMachine.mapped_gate
 have bound:a≤(UniformToeplitzCrossDAG.crossDAG k a e ha he).size:=by
  rw [UniformToeplitzCrossDAG.crossDAG_size]
  omega
 have:=j.isLt
 omega

def outputBorrowed (v source e target a g : ℕ) (fit : g+e+a≤v) (ag : a≤g)
 (j : Fin a) : Fin v := UniformBorrowedCoordinateMachine.embedding v source e target a g fit
  ⟨g-a+j.val,by have:=j.isLt;omega⟩
theorem outputBorrowed_eligible (v source e target a g : ℕ) (fit : g+e+a≤v) (ag : a≤g)
 (j : Fin a) : UniformBorrowedCoordinateMachine.Eligible source e target a
 (outputBorrowed v source e target a g fit ag j).val :=
 UniformBorrowedCoordinateMachine.embedding_eligible _ _ _ _ _ _ fit _

def actualEdges (v source e target a g : ℕ) (fit : g+e+a≤v) (ag : a≤g) :
 Fin a→UniformColoring.Edge := fun j=>
 ⟨target+j.val,(outputBorrowed v source e target a g fit ag j).val,by
  have h:=outputBorrowed_eligible v source e target a g fit ag j
  unfold UniformBorrowedCoordinateMachine.Eligible at h
  have:=j.isLt
  omega⟩

/-- Actual Borrowed17 coordinates make the complete output broadcast one
disjoint matching; a supplied coloring or matching certificate is unnecessary. -/
theorem actual_matching (v source e target a g : ℕ) (fit : g+e+a≤v) (ag : a≤g) :
 UniformMatchingAxisTableMachine.Matching (actualEdges v source e target a g fit ag) := by
 intro i j different
 have ei:=outputBorrowed_eligible v source e target a g fit ag i
 have ej:=outputBorrowed_eligible v source e target a g fit ag j
 unfold UniformBorrowedCoordinateMachine.Eligible at ei ej
 have il:=i.isLt
 have jl:=j.isLt
 have ij:i.val≠j.val:=by intro eq;exact different (Fin.ext eq)
 have right:(outputBorrowed v source e target a g fit ag i).val≠
  (outputBorrowed v source e target a g fit ag j).val := by
  intro eq
  have same:=(UniformBorrowedCoordinateMachine.embedding v source e target a g fit).injective (Fin.ext eq)
  have vals:=congrArg Fin.val same
  dsimp only [outputBorrowed] at vals
  omega
 unfold UniformColoring.Conflict UniformColoring.Incident actualEdges
 dsimp only
 omega

theorem actual_inRange (v source e target a g : ℕ) (fit : g+e+a≤v) (ag : a≤g)
 (targetEnd : target+a≤v) :
 UniformMatchingAxisTableMachine.InRange v (actualEdges v source e target a g fit ag) := by
 intro j
 exact ⟨by have:=j.isLt;change target+j.val<v;omega,
  (outputBorrowed v source e target a g fit ag j).isLt⟩

theorem canonical_execution (n a g T Q D P : ℕ) (hn : 0<n) (x : Fin n→ℂ)
 (b : ℕ→ℕ) (s : State) (h : Header a g T Q D P s) (pc : s.pc=0) (ag : a≤g)
 (bank : Borrowed Q g b s) (sep : Q+g≤D) (rowsEnd : D+3*a≤(n+2)^19)
 (targetEnd : T+a≤(n+2)^19) (bound : WordBound ((n+2)^19) s) :
 ∃u,BoundedExecution program n x ((n+2)^19) s (14*a+7) u ∧
 UniformCrossShearTableMachine.Table D (rowList a g T P b) u ∧ Borrowed Q g b u ∧
 Outside D a s u ∧ Frame s u ∧ u.natReg 894=(rowList a g T P b).length ∧ u.pc=19 := by
 have small:20≤3^19:=by norm_num
 obtain ⟨u,run,rows,bank,out,frame,count,pcu⟩:=execution n _ a g T Q D P x b s h pc ag bank sep
  rowsEnd targetEnd bound (small.trans (Nat.pow_le_pow_left (by omega) 19))
 exact ⟨u,run,rows_table rows,bank,out,frame,by simpa only [rowList_length] using count,pcu⟩

end
end ExactFourierCircuits.UniformCrossBroadcastTableMachine
