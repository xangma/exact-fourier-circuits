import UniformAxisCacheAllocationBounds
import UniformAxisCacheAllocationValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheAllocationMachine
open UniformMachine UniformAssembly UniformNatBlockMachine
open UniformTensorMonomialMachine (setPC)
noncomputable section
attribute [local irreducible] Nat.mul

lemma peak_append (a b : List Op) (s : State) :
 peak (a++b) s=max (peak a s) (peak b (applyBlock a s)) := by
 induction a generalizing s with
 | nil=>simp only [List.nil_append,peak,applyBlock,Nat.zero_max]
 | cons o a ih=>simp only [List.cons_append,peak,applyBlock,ih,max_assoc]
lemma readable_append (a b : List Op) (s : State) :
 readable (a++b) s ↔ readable a s ∧readable b (applyBlock a s) := by
 induction a generalizing s with
 | nil=>simp only [List.nil_append,readable,applyBlock,true_and]
 | cons o a ih=>simp only [List.cons_append,readable,applyBlock,ih,and_assoc]

lemma boot_safe {r N S B : ℕ} (s : State) (args : Arguments r N S s) (num : NumericBounds r N S B) :
 readable boot s ∧peak boot s≤B := by
 have code:=num.code
 have twice:=num.twice
 constructor
 · simp [boot,readable,Op.readable,evalNat]
 · simp [boot,peak,Op.peak,Op.apply,evalNat,writeNat,next,args.radix]
   omega

lemma capacity_safe {r N S B : ℕ} (s : State) (h : BaseValues r N S s) (num : NumericBounds r N S B) :
 readable capacityOps s ∧peak capacityOps s≤B := by
 have code:=num.code
 have quotient:=num.quotient
 have slots:=num.slots
 have square:=num.square
 have capacity:=num.capacity
 rw [←computed_capacity] at capacity
 constructor
 · simp [capacityOps,readable,Op.readable,evalNat,Op.apply,writeNat,next]
 · simp [capacityOps,peak,Op.peak,Op.apply,evalNat,writeNat,next,h.v6542,h.v6800]
   omega

lemma front_safe {r N S B : ℕ} (s : State) (h : CapacityValues r N S s) (num : NumericBounds r N S B) :
 readable frontOps s ∧peak frontOps s≤B := by
 have code:=num.code
 have nodeCount:=num.nodeCount
 have stack:=num.stack
 have directory:=num.directory
 have frontier:=num.natFrontier
 have nodes:=num.endpoints _ (show (C.axisBank r N S).nodes∈_ by simp)
 have requests:=num.endpoints _ (show (C.axisBank r N S).requests∈_ by simp)
 dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank] at nodes requests
 constructor
 · simp [frontOps,readable,Op.readable,evalNat]
 · simp [frontOps,peak,Op.peak,Op.apply,evalNat,writeNat,next,
    h.v6540,h.v6804,h.v6823,h.v6801,h.v6803,Nat.mul_comm]
   omega

lemma control_safe {r N S B : ℕ} (s : State) (h : FrontValues r N S s) (num : NumericBounds r N S B) :
 readable controlOps s ∧peak controlOps s≤B := by
 have code:=num.code
 have rectangles:=num.rectangles
 have triple:=num.triple
 have stride:=num.stride
 have cache:=num.cache
 have control:=num.endpoints _ (show (C.axisBank r N S).control∈_ by simp)
 have leaf:=num.endpoints _ (show (C.axisBank r N S).leafForward∈_ by simp)
 dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank] at control leaf
 constructor
 · simp [controlOps,readable,Op.readable,evalNat]
 · simp [controlOps,peak,Op.peak,Op.apply,evalNat,writeNat,next,
    h.v6809,h.v6806,h.v6812,h.v6800,h.v6807,
    C.axisBank,UniformJointCacheAllocation.axisBank,pow_two,Nat.mul_comm,Nat.mul_assoc]
   simp only [pow_two,Nat.mul_comm,Nat.mul_assoc] at rectangles triple stride cache control leaf
   omega

lemma time_safe {r N S B : ℕ} (s : State) (h : ControlValues r N S s) (num : NumericBounds r N S B) :
 readable timeOps s ∧peak timeOps s≤B := by
 have code:=num.code
 have four:=num.fourSquare
 have eight:=num.eightSquare
 have twoCount:=num.twoCount
 have leafT:=num.endpoints _ (show (C.axisBank r N S).leafTranspose∈_ by simp)
 have duration:=num.endpoints _ (show (C.axisBank r N S).durations∈_ by simp)
 have start:=num.endpoints _ (show (C.axisBank r N S).nodeStarts∈_ by simp)
 have request:=num.endpoints _ (show (C.axisBank r N S).requestStarts∈_ by simp)
 have endNat:=num.endpoints _ (show (C.axisBank r N S).endNat∈_ by simp)
 dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank] at leafT duration start request endNat
 constructor
 · simp [timeOps,readable,Op.readable,evalNat]
 · simp [timeOps,peak,Op.peak,Op.apply,evalNat,writeNat,next,
    h.v6823,h.v6806,h.v6814,h.v6808,h.v6804,
    C.axisBank,UniformJointCacheAllocation.axisBank,pow_two,Nat.mul_comm,Nat.mul_assoc]
   simp only [pow_two,Nat.mul_comm,Nat.mul_assoc] at four eight twoCount leafT duration start request endNat
   omega

lemma scalar_safe {r N S B : ℕ} (s : State) (h : TimeValues r N S s) (num : NumericBounds r N S B) :
 readable scalarOps s ∧peak scalarOps s≤B := by
 have code:=num.code
 have frontier:=num.scalarFrontier
 have nine:=num.nineRadix
 have factors:=num.factors
 have endScalar:=num.endpoints _ (show (C.axisBank r N S).endScalar∈_ by simp)
 dsimp only [C.axisBank,UniformJointCacheAllocation.axisBank] at endScalar
 constructor
 · simp [scalarOps,readable,Op.readable,evalNat]
 · simp [scalarOps,peak,Op.peak,Op.apply,evalNat,writeNat,next,h.v6802,h.v6803,h.v6800,h.v6807,
    Nat.mul_comm,Nat.mul_assoc]
   simp only [Nat.mul_comm,Nat.mul_assoc] at nine factors endScalar
   omega

lemma post_safe {r N S B : ℕ} (s : State) (h : BaseValues r N S s) (num : NumericBounds r N S B) :
 readable post s ∧peak post s≤B := by
 have c:=capacity_values r N S s h
 have f:=front_values r N S _ c
 have d:=control_values r N S _ f
 have t:=time_values r N S _ d
 have sc:=capacity_safe s h num
 have sf:=front_safe _ c num
 have sd:=control_safe _ f num
 have st:=time_safe _ d num
 have ss:=scalar_safe _ t num
 simp only [post,readable_append,peak_append,applyBlock_append,max_le_iff]
 constructor
 · exact ⟨⟨⟨⟨sc.1,sf.1⟩,sd.1⟩,st.1⟩,ss.1⟩
 · exact ⟨⟨⟨⟨sc.2,sf.2⟩,sd.2⟩,st.2⟩,ss.2⟩


structure Frame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀q,(q<6540∨6551<q)→(q<6803∨6828<q)→u.natReg q=s.natReg q
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩
lemma Frame.pc {s u : State} (f : Frame s u) (pc : ℕ) : Frame s (setPC u pc) :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Frame.trans {s u t : State} (f : Frame s u) (g : Frame u t) : Frame s t :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
  g.outputs.trans f.outputs,g.roots.trans f.roots,fun q h k=>(g.natReg q h k).trans (f.natReg q h k)⟩
lemma duration_frame {s u : State} (f : UniformCacheRowDurationMachine.Frame s u) : Frame s u :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,fun q h _=>f.natReg q (by omega)⟩

def allowed (q : ℕ) : Prop := (6540≤q∧q≤6551)∨(6803≤q∧q≤6828)
def ordinary : Op→Prop
 | .literal d _=>allowed d
 | .binary _ d _ _=>allowed d
 | _=>False
lemma op_frame (o : Op) (s : State) (h : ordinary o) : Frame s (o.apply s) := by
 cases o with
 | literal d v | binary op d left right=>
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q first second
  have ne:q≠d:=by change allowed d at h;unfold allowed at h;omega
  simp [Op.apply,writeNat,next,ne]
 | load d a=>exact False.elim h
 | store a r=>exact False.elim h
lemma block_frame (os : List Op) (s : State) (h : ∀o∈os,ordinary o) : Frame s (applyBlock os s) := by
 induction os generalizing s with
 | nil=>exact Frame.refl s
 | cons o os ih=>
  exact (op_frame o s (h o (by simp))).trans (ih (o.apply s) (fun z hz=>h z (by simp[hz])))
lemma boot_frame (s : State) : Frame s (applyBlock boot s) :=
 block_frame boot s (by simp [boot,ordinary,allowed])
lemma post_frame (s : State) : Frame s (applyBlock post s) :=
 block_frame post s (by simp [post,capacityOps,frontOps,controlOps,timeOps,scalarOps,ordinary,allowed])
lemma block_pc (os : List Op) (s : State) : (applyBlock os s).pc=s.pc+os.length := by
 induction os generalizing s with
 | nil=>simp only [applyBlock,List.length_nil,Nat.add_zero]
 | cons o os ih=>simp only [applyBlock,ih,Op.apply_pc,List.length_cons,Nat.add_assoc,Nat.add_comm 1]

/-- The actual58 allocator computes every address from ordinary input frontiers.
Every arithmetic instruction and the real logarithm loop is charged. -/
theorem execution (r N S B n : ℕ) (x : Fin n→ℂ) (s : State)
 (args : Arguments r N S s) (pc : s.pc=0) (wb : WordBound B s) (budget : wordBudget r N S≤B) :
 ∃u,BoundedExecution program n x B s (4*Nat.clog 2 (4*r)+55) u ∧
 u.pc=57 ∧Result r N S u ∧Frame s u := by
 have num:NumericBounds r N S B:=(numeric_bounds r N S).mono budget
 have safe:=boot_safe s args num
 have code:=num.code
 have first:=block_runs boot program 0 n B x s boot_code pc wb (by rw [boot_length];omega) safe.1 safe.2
 let a:=applyBlock boot s
 have values:=boot_values r N S s args
 have ap:a.pc=4:=by rw [block_pc,pc,boot_length]
 let start:=setPC a 0
 have swb:WordBound B start:=changePC_bound B a 0 first.final_bound (by omega)
 obtain ⟨b,drun,bp,amount,df⟩:=UniformCacheRowDurationMachine.execution n (2*r) 0 B x start
  values.1 values.2.1 rfl swb num.rowBudget
 have middle:=UniformBoundedAssembly.boundedExecution_placed duration_code
  (by rw [UniformCacheRowDurationMachine.program_length];omega) (by omega) drun
 change BoundedRuns program n x B (placed 4 (setPC a 0)) _ (setPC b 22) at middle
 rw [UniformSeedRankCrossPreparation.placed_zero a 4 ap] at middle
 let u:=setPC b 22
 have af:Frame a u:=((Frame.refl a).pc 0 |>.trans (duration_frame df)).pc 22
 have ua:Arguments r N S u:=⟨(af.natReg 6800 (by omega) (by omega)).trans values.2.2.2.2.radix,
  (af.natReg 6801 (by omega) (by omega)).trans values.2.2.2.2.natFrontier,
  (af.natReg 6802 (by omega) (by omega)).trans values.2.2.2.2.scalarFrontier⟩
 have zero:u.natReg 6803=0:=(df.natReg 6803 (by omega)).trans values.2.2.1
 have two:u.natReg 6804=2:=(df.natReg 6804 (by omega)).trans values.2.2.2.1
 have twice:u.natReg 6540=2*r:=(df.natReg 6540 (by omega)).trans values.1
 have base:BaseValues r N S u:=⟨ua.radix,ua.natFrontier,ua.scalarFrontier,zero,two,twice,amount⟩
 have postSafe:=post_safe u base num
 have last:=block_runs post program 22 n B x u post_code rfl middle.final_bound
  (by rw [post_length];omega) postSafe.1 postSafe.2
 let final:=applyBlock post u
 have finalPc:final.pc=57:=by rw [block_pc,post_length];rfl
 have halted:BoundedExecution program n x B final 1 final:=.halt last.final_bound
  (by simp only [UniformMachine.step,finalPc,halt_at])
 refine ⟨final,?_,finalPc,post_result r N S u ua zero two twice amount,
  ((boot_frame s).trans af).trans (post_frame u)⟩
 convert first.executes (middle.executes (last.executes halted)) using 1
 rw [show 2*(2*r+0)=4*r by omega]
 change 4*Nat.clog 2 (4*r)+55=4+(4*Nat.clog 2 (4*r)+15)+(35+1)
 omega
end
end ExactFourierCircuits.UniformAxisCacheAllocationMachine
