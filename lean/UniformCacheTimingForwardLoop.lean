import UniformCacheTimingForwardNode
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheTimingForwardLoop
open UniformMachine UniformAssembly UniformCacheTimingProgram UniformCacheTimingControl
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs setPC)
open UniformPreparationRowTableMachine (control_run)
open UniformCacheTimingForwardRows (Values writeStarts writeStarts_value writeStarts_outside)

structure Data where
 parent : ℕ
 ordinal : ℕ
 duration : ℕ
 correction : ℕ
 prefixes : List ℕ
structure Layout (D U V T N K B : ℕ) : Prop where
 directory : D+7*N ≤ U
 durations : U+N ≤ V
 starts : V+N ≤ T
 requests : T+K ≤ B
 code : 122 ≤ B
structure Ordered (N K B : ℕ) (a : ℕ→Data) : Prop where
 parents : ∀k,k < N→k=0∨(a k).parent < k
 ordinals : ∀i j,i < j→j < N→(a i).ordinal+(a i).prefixes.length ≤ (a j).ordinal
 requests : ∀k,k < N→(a k).ordinal+(a k).prefixes.length ≤ K
 values : ∀k,k < N→∀v∈(a k).prefixes,(a k).duration-(a k).correction+v ≤ B
structure Bank (D R U V T N : ℕ) (a : ℕ→Data) (i : ℕ) (s : State) : Prop where
 directory : ∀k,k < N→s.natHeap (D+7*k+3)=some (a k).parent ∧
  s.natHeap (D+7*k+5)=some (R+7*(a k).ordinal) ∧
  s.natHeap (D+7*k+6)=some (a k).prefixes.length
 durations : ∀k,k < N→s.natHeap (U+k)=some (a k).duration
 starts : ∀k,k < N→s.natHeap (V+k)=some (if k < i then 0 else (a k).correction)
 prefixes : ∀k,k < N→∀j,(hj:j < (a k).prefixes.length)→
  s.natHeap (T+(a k).ordinal+j)=some
   (if k < i then (a k).duration-(a k).correction+(a k).prefixes[j] else (a k).prefixes[j])
noncomputable section
lemma Bank.pc {D R U V T N i : ℕ} {a : ℕ→Data} {s : State}
 (h : Bank D R U V T N a i s) (p : ℕ) : Bank D R U V T N a i (setPC s p) := ⟨h.directory,h.durations,h.starts,h.prefixes⟩

def converted (V T i : ℕ) (a : ℕ→Data) (heap : ℕ→Option ℕ) : ℕ→Option ℕ :=
 Function.update (writeStarts T (a i).ordinal ((a i).duration-(a i).correction) (a i).prefixes heap)
  (V+i) (some 0)
lemma converted_below {D U V T N K B : ℕ} (g : Layout D U V T N K B)
 (a : ℕ→Data) (i : ℕ) (heap : ℕ→Option ℕ) (z : ℕ) (hz : z < V) :
 converted V T i a heap z=heap z := by
 rw [converted,Function.update_of_ne (by omega),writeStarts_outside]
 left;have:=g.starts;omega
lemma converted_outside {D U V T N K B : ℕ} (_g : Layout D U V T N K B)
 (a : ℕ→Data) (ord : Ordered N K B a) (i : ℕ) (hi : i < N)
 (heap : ℕ→Option ℕ) (z : ℕ)
 (hv : z < V∨V+N ≤ z) (ht : z < T∨T+K ≤ z) : converted V T i a heap z=heap z := by
 rw [converted,Function.update_of_ne (by omega),writeStarts_outside]
 have := ord.requests i hi
 rcases ht with ht|ht
 · left;omega
 · right;omega
lemma bank_step {D R U V T N K B i : ℕ} (g : Layout D U V T N K B)
 (a : ℕ→Data) (ord : Ordered N K B a) (s u : State) (h : Bank D R U V T N a i s)
 (hi : i < N) (heap : u.natHeap=converted V T i a s.natHeap) : Bank D R U V T N a (i+1) u := by
 constructor
 · intro k hk
   have old:=h.directory k hk
   have dv:=g.directory
   have uv:=g.durations
   rw [heap,converted_below g a i s.natHeap _ (by omega),
    converted_below g a i s.natHeap _ (by omega),converted_below g a i s.natHeap _ (by omega)]
   exact old
 · intro k hk
   rw [heap,converted_below g a i s.natHeap _ (by have:=g.durations;omega)]
   exact h.durations k hk
 · intro k hk
   rw [heap,converted]
   by_cases eq : k=i
   · subst k;simp
   · have ne : V+k≠V+i := by omega
     rw [Function.update_of_ne ne,writeStarts_outside]
     · rw [h.starts k hk]
       congr 2
       apply propext;omega
     · left;have:=g.starts;omega
 · intro k hk j hj
   rw [heap,converted,Function.update_of_ne (by have:=g.starts;omega)]
   by_cases eq : k=i
   · subst k
     rw [writeStarts_value _ _ _ _ _ j hj]
     simp
   · rw [writeStarts_outside]
     · rw [h.prefixes k hk j hj]
       congr 2
       apply propext;omega
     · by_cases before : k < i
       · have:=ord.ordinals k i before hi
         left;omega
       · have:=ord.ordinals i k (by omega) hk
         right;omega

def ticks (a : ℕ→Data) : ℕ→ℕ→ℕ
 | _,0=>1
 | i,fuel+1=>UniformCacheTimingForwardNode.ticks i (a i).prefixes.length+ticks a (i+1) fuel

/-- The literal forward loop converts all remaining nodes and returns at the
actual halt address. Its invariant retains the unprocessed physical values. -/
theorem loop (n D R U V T N K B i fuel : ℕ) (a : ℕ→Data) (x : Fin n→ℂ) (s : State)
 (g : Layout D U V T N K B) (ord : Ordered N K B a) (h : Init D R U V T N K i s)
 (bank : Bank D R U V T N a i s) (endIndex : i+fuel=N) (hp : s.pc=87) (hs : WordBound B s) : ∃u,
 BoundedRuns program n x B s (ticks a i fuel) u ∧ u.pc=121 ∧
 Init D R U V T N K N u ∧ Bank D R U V T N a N u ∧
 (∀z,(z < V∨V+N ≤ z)→(z < T∨T+K ≤ z)→u.natHeap z=s.natHeap z) := by
 induction fuel generalizing i s with
 | zero =>
  have eq : i=N := by omega
  have step : UniformMachine.step program n x s=.running (setPC s 121) := by
   simp [UniformMachine.step,hp,code_87,h.index,h.nodeCount,eq,setPC]
  refine ⟨setPC s 121,control_run program n B 121 x s hs (by have:=g.code;omega) step,rfl,?_,?_,fun _ _ _=>rfl⟩
  · simpa only [eq] using h.pc 121
  · simpa only [eq] using bank.pc 121
 | succ fuel ih =>
  have hi : i < N := by omega
  have stored:=bank.directory i hi
  have d:=bank.durations i hi
  have correction : s.natHeap (V+i)=some (a i).correction := by simpa using bank.starts i hi
  have vals : Values T (a i).ordinal (a i).prefixes s := by
   intro j hj
   simpa using bank.prefixes i hi j hj
  have pf : 0 < i→s.natHeap (V+(a i).parent)=some 0 := by
   intro positive
   have pp : (a i).parent < i := by rcases ord.parents i hi with eq|lt;omega;exact lt
   simpa only [ite_eq_left pp] using bank.starts (a i).parent (by omega)
  have du:=g.directory
  have uv:=g.durations
  have vt:=g.starts
  have tk:=g.requests
  have requestFit:=ord.requests i hi
  obtain ⟨u,one,up,uh,uheap⟩:=UniformCacheTimingForwardNode.node n D R U V T N K i (a i).parent
   (R+7*(a i).ordinal) (a i).duration (a i).correction (a i).ordinal B (a i).prefixes x s h hp hs g.code hi
   (by omega) (by omega) (by omega) stored.1 stored.2.1 stored.2.2 d correction rfl
   (ord.parents i hi) pf vals (by omega) (ord.values i hi)
  have newbank:=bank_step g a ord s u bank hi uheap
  obtain ⟨v,tail,vp,vh,vbank,frame⟩:=ih (i+1) u uh newbank (by omega) up one.final_bound
  refine ⟨v,one.trans tail,vp,vh,vbank,?_⟩
  intro z hz ht
  rw [frame z hz ht,uheap]
  exact converted_outside g a ord i hi s.natHeap z hz ht

lemma forwardSetup_header {D R U V T N K : ℕ} (s : State) (h : Header D R U V T N K s) :
 Init D R U V T N K 0 (applyBlock forwardSetup s) := by
 constructor
 · constructor <;>simp [forwardSetup,applyBlock,Op.apply,writeNat,next,h.nodes,h.requests,h.durations,
      h.starts,h.requestStarts,h.rootStart,h.nodeCount,h.requestCount,h.zero,h.one,h.two,h.three,h.seven,h.fourteen]
 · simp [forwardSetup,applyBlock,Op.apply,writeNat,next]

/-- Includes the charged forward index reset and the actual halt. -/
theorem execution (n D R U V T N K B : ℕ) (a : ℕ→Data) (x : Fin n→ℂ) (s : State)
 (g : Layout D U V T N K B) (ord : Ordered N K B a) (h : Header D R U V T N K s)
 (bank : Bank D R U V T N a 0 s) (hp : s.pc=86) (hs : WordBound B s) : ∃u,
 BoundedExecution program n x B s (ticks a 0 N+2) u ∧ u.pc=121 ∧
 Bank D R U V T N a N u ∧
 (∀z,(z < V∨V+N ≤ z)→(z < T∨T+K ≤ z)→u.natHeap z=s.natHeap z) := by
 have setup:=block_runs forwardSetup program 86 n B x s forwardSetup_code hp hs
  (by change 87 ≤ B;have:=g.code;omega) (by simp [forwardSetup,readable,Op.readable]) (by simp [forwardSetup,peak,Op.peak])
 let t:=applyBlock forwardSetup s
 have tp : t.pc=87 := by rw [applyBlock_pc,hp];rfl
 have th:=forwardSetup_header s h
 obtain ⟨u,run,up,uh,ubank,frame⟩:=loop n D R U V T N K B 0 N a x t g ord th ⟨bank.directory,bank.durations,bank.starts,bank.prefixes⟩ (by omega) tp setup.final_bound
 have halt : UniformMachine.step program n x u=.halted u := by simp [UniformMachine.step,up,code_121]
 have done:=((setup.trans run).executes (.halt run.final_bound halt))
 refine ⟨u,?_,up,ubank,frame⟩
 convert done using 1
 change ticks a 0 N+2=1+ticks a 0 N+1
 omega
end
end ExactFourierCircuits.UniformCacheTimingForwardLoop
