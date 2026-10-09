import UniformRecursiveSavingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveSavingExecution
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace P
export UniformRecursiveSavingProgram (Part piece program address size order part_slice piece_size)
end P
noncomputable section

lemma offset_bound {α : Type*} [DecidableEq α] (size : α→ℕ) (ls : List α) (a : α) (mem : a∈ls) :
 UniformRecursiveSavingProgram.offset size ls a+size a≤(ls.map size).sum:=by
 induction ls with
 | nil=>simp at mem
 | cons b bs ih=>
  by_cases eq:b=a
  · subst b;simp [UniformRecursiveSavingProgram.offset]
  · have tail:a∈bs:=by rcases List.mem_cons.mp mem with h|h;exact False.elim (eq h.symm);exact h
    have h:=ih tail
    simp only [UniformRecursiveSavingProgram.offset,eq,ite_false,List.map_cons,List.sum_cons]
    omega
lemma part_bound (a : P.Part) : P.address a+P.size a≤P.program.length:=by
 have mem:a∈P.order:=by cases a <;> simp [UniformRecursiveSavingProgram.order]
 have h:=offset_bound P.size P.order a mem
 have len:P.program.length=(P.order.map P.size).sum:=by
  simp only [UniformRecursiveSavingProgram.program,List.length_flatMap]
  simp_rw [P.piece_size]
 rw [len]
 exact h
lemma part_block (a : P.Part) (ops : List Op) (tail : Program)
 (eq : P.piece a=ops.map Op.code++tail) : BlockAt ops P.program (P.address a):=by
 intro i hi
 have hi':i<(P.piece a).length:=by rw [eq,List.length_append,List.length_map];omega
 rw [P.part_slice a i hi',eq,List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma part_at (a : P.Part) (i : ℕ) (hi:i<P.size a) :
 P.program[P.address a+i]?=(P.piece a)[i]?:=P.part_slice a i (by rwa [P.piece_size])

def entryOps : List Op := [.literal 4153 1,.binary .mul 5300 4120 4153,.binary .mul 3300 4121 4153]
lemma entry_code : BlockAt entryOps P.program (P.address .entry):=part_block _ entryOps _ rfl
lemma entry_address : P.address .entry=0:=rfl
lemma entry_branch : P.program[3]?=some (.branchLT 4151 4153 (P.address .rootAllocate) (P.address .readyEntry)):=by
 exact part_at .entry 3 (by decide)

def rootOps : List Op := [.binary .mul 4150 4123 4153,.binary .add 4177 4120 4153,
 .literal 4178 34,.binary .mul 4177 4177 4178,.binary .add 4123 4123 4177]
lemma root_code : BlockAt rootOps P.program (P.address .rootAllocate):=part_block _ rootOps _ rfl
lemma root_jump : P.program[P.address .rootAllocate+5]?=some (.jump (P.address .readyEntry)):=by
 exact part_at .rootAllocate 5 (by decide)

def EntryChanged (i : ℕ) : Prop := i=4153∨i=5300∨i=3300∨i=4150∨i=4177∨i=4178∨i=4123
structure EntryFrame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬EntryChanged i→u.natReg i=s.natReg i
lemma EntryFrame.refl (s : State) : EntryFrame s s:=⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma EntryFrame.pc {s u : State} (h : EntryFrame s u) (pc : ℕ) : EntryFrame s {u with pc:=pc}:=
 ⟨h.natHeap,h.scalarHeap,h.scalarReg,h.outputs,h.roots,h.natReg⟩
lemma EntryFrame.trans {s u v : State} (h : EntryFrame s u) (g : EntryFrame u v) : EntryFrame s v:=
 ⟨g.natHeap.trans h.natHeap,g.scalarHeap.trans h.scalarHeap,g.scalarReg.trans h.scalarReg,
 g.outputs.trans h.outputs,g.roots.trans h.roots,fun i hi=>(g.natReg i hi).trans (h.natReg i hi)⟩
lemma entry_frame (s : State) : EntryFrame s (applyBlock entryOps s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 unfold EntryChanged at hi
 simp (disch:=omega) [entryOps,applyBlock,Op.apply,evalNat,writeNat,next]
lemma root_frame (s : State) : EntryFrame s (applyBlock rootOps s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 unfold EntryChanged at hi
 simp (disch:=omega) [rootOps,applyBlock,Op.apply,evalNat,writeNat,next]

/-- Actual common entry. Only raw k/base/volume/frontier and the physical
stack depth are read. The root stack is allocated by charged Nat operations. -/
theorem entry_execution (n B k A V F depth : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=0) (bits:s.natReg 4120=k) (base:s.natReg 4121=A) (volume:s.natReg 4122=V)
 (frontier:s.natReg 4123=F) (stackDepth:s.natReg 4151=depth) (bound:WordBound B s)
 (code:P.program.length≤B) (stackEnd:F+34*(k+1)≤B) : ∃u,
 BoundedRuns P.program n x B s (if depth=0 then 10 else 4) u ∧ u.pc=P.address .readyEntry ∧
 u.natReg 5300=k ∧ u.natReg 3300=A ∧ u.natReg 4120=k ∧ u.natReg 4121=A ∧ u.natReg 4122=V ∧
 u.natReg 4151=depth ∧ u.natReg 4153=1 ∧
 u.natReg 4123=(if depth=0 then F+34*(k+1) else F) ∧
 (depth=0→u.natReg 4150=F) ∧ EntryFrame s u:=by
 have codeEntry:4≤B:=by have h:=part_bound .entry;rw [entry_address] at h;change 0+4≤P.program.length at h;omega
 have rootEnd:P.address .rootAllocate+6≤B:=(part_bound .rootAllocate).trans code
 have readyBound:P.address .readyEntry≤B:=by have h:=(part_bound .readyEntry).trans code;omega
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have ab:A≤B:=by have h:=bound.2.1 4121;rwa [base] at h
 have safe:readable entryOps s ∧ peak entryOps s≤B:=by
  simp [entryOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,bits,base];omega
 have run:=block_runs entryOps P.program 0 n B x s (by simpa only [entry_address] using entry_code) pc bound
  (by change 0+3≤B;omega) safe.1 safe.2
 let boot:=applyBlock entryOps s
 have bpc:boot.pc=3:=by simp [boot,entryOps,applyBlock,Op.apply,writeNat,next,pc]
 have dp:boot.natReg 4151=depth:=by simp [boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next,stackDepth]
 have one:boot.natReg 4153=1:=by simp [boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next]
 by_cases zero:depth=0
 · let go:State:={boot with pc:=P.address .rootAllocate}
   have gb:=changePC_bound B boot (P.address .rootAllocate) run.final_bound (by omega)
   have branch:BoundedRuns P.program n x B boot 1 go:=.next run.final_bound
    (by simp [step,bpc,entry_branch,dp,one,zero,go]) (.refl gb)
   have keep (i:ℕ)(hi:i≠4153 ∧ i≠5300 ∧ i≠3300):go.natReg i=s.natReg i:=by
    simp [go,boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next,hi.1,hi.2.1,hi.2.2]
   have f:go.natReg 4123=F:=(keep _ (by omega)).trans frontier
   have k':go.natReg 4120=k:=(keep _ (by omega)).trans bits
   have kp:k+1≤B:=by nlinarith only [stackEnd]
   have prod:34*(k+1)≤B:=by omega
   have rootSafe:readable rootOps go ∧ peak rootOps go≤B:=by
    simp [rootOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,f,k',one,
     show go.natReg 4153=1 from one,Nat.mul_comm]
    omega
   have rr:=block_runs rootOps P.program (P.address .rootAllocate) n B x go root_code rfl gb
    (by change P.address .rootAllocate+5≤B;omega) rootSafe.1 rootSafe.2
   let prepared:=applyBlock rootOps go
   let u:State:={prepared with pc:=P.address .readyEntry}
   have preparedPC:prepared.pc=P.address .rootAllocate+5:=by simp [prepared,rootOps,applyBlock,Op.apply,writeNat,next,go]
   have ub:=changePC_bound B prepared (P.address .readyEntry) rr.final_bound readyBound
   have jump:BoundedRuns P.program n x B prepared 1 u:=.next rr.final_bound
    (by simp [step,preparedPC,root_jump,u]) (.refl ub)
   have fr:EntryFrame s u:=((entry_frame s).pc _).trans (root_frame go) |>.pc _
   refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,fr⟩
   · simpa only [zero,ite_true,entryOps,rootOps,List.length_cons,List.length_nil] using run.trans (branch.trans (rr.trans jump))
   · simp [u,prepared,rootOps,applyBlock,Op.apply,evalNat,writeNat,next,go,boot,entryOps,bits]
   · simp [u,prepared,rootOps,applyBlock,Op.apply,evalNat,writeNat,next,go,boot,entryOps,base]
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans bits
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans base
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans volume
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans stackDepth
   · simp [u,prepared,rootOps,applyBlock,Op.apply,evalNat,writeNat,next,go,boot,entryOps]
   · simp [u,prepared,rootOps,applyBlock,Op.apply,evalNat,writeNat,next,go,boot,entryOps,frontier,bits,zero,Nat.mul_comm]
   · intro _;simp [u,prepared,rootOps,applyBlock,Op.apply,evalNat,writeNat,next,go,boot,entryOps,frontier]
 · let u:State:={boot with pc:=P.address .readyEntry}
   have ub:=changePC_bound B boot (P.address .readyEntry) run.final_bound readyBound
   have branch:BoundedRuns P.program n x B boot 1 u:=.next run.final_bound
    (by simp [step,bpc,entry_branch,dp,one,show ¬depth<1 by omega,u]) (.refl ub)
   have fr:EntryFrame s u:=(entry_frame s).pc _
   refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,fr⟩
   · simpa only [zero,ite_false,entryOps,List.length_cons,List.length_nil] using run.trans branch
   · simp [u,boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next,bits]
   · simp [u,boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next,base]
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans bits
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans base
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans volume
   · exact fr.natReg _ (by unfold EntryChanged;omega) |>.trans stackDepth
   · exact one
   · simp [u,boot,entryOps,applyBlock,Op.apply,evalNat,writeNat,next,zero,frontier]
   · intro h;exact False.elim (zero h)

lemma radix_positive : 0<ExplicitSeedBudget.m:=by norm_num [ExplicitSeedBudget.m]
lemma radix_two : 2≤ExplicitSeedBudget.m:=by norm_num [ExplicitSeedBudget.m]
lemma threshold_radix : ExplicitSeedBudget.m≤UniformRecursiveSavingProgram.threshold:=by
 rw [UniformRecursiveSavingProgram.threshold,ExplicitSeedBudget.bits_value]
 norm_num [ExplicitSeedBudget.m]
lemma recursive_geometry (k : ℕ) (large:UniformRecursiveSavingProgram.threshold≤k) :
 1≤k/ExplicitSeedBudget.m ∧ k/ExplicitSeedBudget.m<k ∧ k%ExplicitSeedBudget.m<ExplicitSeedBudget.m ∧
 k=(k/ExplicitSeedBudget.m)*ExplicitSeedBudget.m+k%ExplicitSeedBudget.m:=by
 have mk:ExplicitSeedBudget.m≤k:=threshold_radix.trans large
 refine ⟨(Nat.one_le_div_iff radix_positive).mpr mk,?_,Nat.mod_lt _ radix_positive,?_⟩
 · exact Nat.div_lt_self (radix_positive.trans_le mk) (by have h:=radix_two;omega)
 · simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div k ExplicitSeedBudget.m).symm

lemma ready_at (i : ℕ) (hi:i<2) : P.program[P.address .readyEntry+i]?=
 ([.natLiteral 4177 UniformRecursiveSavingProgram.threshold,
  .branchLT 4120 4177 (P.address .smallSetup) (P.address .largeSetup)] : Program)[i]?:=
 part_at .readyEntry i hi
lemma large_follow : P.address .largeSetup+7=P.address .seedPrinter:=by
 change 77=77
 rfl

def largeOps : List Op := [.literal 4061 ExplicitSeedBudget.m,.binary .div 4060 4120 4061,
 .binary .mod 4127 4120 4061,.binary .mul 5301 4127 4153,
 .binary .mul 2599 4060 4153,.binary .mul 2600 4123 4153,.binary .mul 3304 4122 4153]
lemma large_code : BlockAt largeOps P.program (P.address .largeSetup):=by
 simpa only [List.append_nil] using part_block .largeSetup largeOps [] rfl

def GeometryChanged (i : ℕ) : Prop := i=4060∨i=4061∨i=4127∨i=5301∨i=2599∨i=2600∨i=3304∨i=4177
structure GeometryFrame (s u : State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬GeometryChanged i→u.natReg i=s.natReg i
lemma large_frame (s : State) : GeometryFrame s (applyBlock largeOps s):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 unfold GeometryChanged at hi
 simp (disch:=omega) [largeOps,applyBlock,Op.apply,evalNat,writeNat,next]

/-- The real large-branch prologue computes q=floor(k/m) and r=k mod m.
In particular, its next self-call has the strictly smaller exponent q. -/
theorem geometry_execution (n B k V F : ℕ) (x : Fin n→ℂ) (s : State)
 (pc:s.pc=P.address .readyEntry) (bits:s.natReg 4120=k) (volume:s.natReg 4122=V)
 (frontier:s.natReg 4123=F) (one:s.natReg 4153=1) (large:UniformRecursiveSavingProgram.threshold≤k)
 (bound:WordBound B s) (code:P.program.length≤B) (literal:UniformRecursiveSavingProgram.threshold≤B) : ∃u,
 BoundedRuns P.program n x B s 9 u ∧ u.pc=P.address .seedPrinter ∧
 u.natReg 4060=k/ExplicitSeedBudget.m ∧ u.natReg 4061=ExplicitSeedBudget.m ∧
 u.natReg 4127=k%ExplicitSeedBudget.m ∧ u.natReg 5301=k%ExplicitSeedBudget.m ∧
 u.natReg 2599=k/ExplicitSeedBudget.m ∧ u.natReg 2600=F ∧ u.natReg 3304=V ∧
 GeometryFrame s u:=by
 have readyEnd:P.address .readyEntry+2≤B:=(part_bound .readyEntry).trans code
 have largeEnd:P.address .largeSetup+7≤B:=(part_bound .largeSetup).trans code
 let tagged:=writeNat s 4177 UniformRecursiveSavingProgram.threshold
 have tb:=writeNat_bound B s 4177 _ bound (by omega) literal
 have literalAt:P.program[P.address .readyEntry]?=some (.natLiteral 4177 UniformRecursiveSavingProgram.threshold):=by
  exact ready_at 0 (by omega)
 have tag:BoundedRuns P.program n x B s 1 tagged:=.next bound
  (by simp [step,pc,literalAt,tagged]) (.refl tb)
 let entered:State:={tagged with pc:=P.address .largeSetup}
 have eb:=changePC_bound B tagged (P.address .largeSetup) tb (by omega)
 have branch:BoundedRuns P.program n x B tagged 1 entered:=.next tb
  (by simp [step,tagged,writeNat,next,pc,ready_at 1 (by omega),bits,show ¬k<UniformRecursiveSavingProgram.threshold by omega,entered]) (.refl eb)
 have k':entered.natReg 4120=k:=by simp [entered,tagged,writeNat,next,bits]
 have v':entered.natReg 4122=V:=by simp [entered,tagged,writeNat,next,volume]
 have f':entered.natReg 4123=F:=by simp [entered,tagged,writeNat,next,frontier]
 have o':entered.natReg 4153=1:=by simp [entered,tagged,writeNat,next,one]
 have kb:k≤B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have vb:V≤B:=by have h:=bound.2.1 4122;rwa [volume] at h
 have fb:F≤B:=by have h:=bound.2.1 4123;rwa [frontier] at h
 have qb:k/ExplicitSeedBudget.m≤B:=(Nat.div_le_self _ _).trans kb
 have rb:k%ExplicitSeedBudget.m≤B:=(Nat.mod_le _ _).trans kb
 have mb:ExplicitSeedBudget.m≤B:=threshold_radix.trans literal
 have safe:readable largeOps entered ∧ peak largeOps entered≤B:=by
  simp [largeOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,k',v',f',o',
   Nat.ne_of_gt radix_positive]
  omega
 have run:=block_runs largeOps P.program (P.address .largeSetup) n B x entered large_code rfl eb
  (by change P.address .largeSetup+7≤B;exact largeEnd) safe.1 safe.2
 let u:=applyBlock largeOps entered
 have frame:GeometryFrame s u:=by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  rw [(large_frame entered).natReg i hi]
  unfold GeometryChanged at hi
  simp (disch:=omega) [entered,tagged,writeNat,next]
 refine ⟨u,?_,?_,?_,?_,?_,?_,?_,?_,?_,frame⟩
 · convert tag.trans (branch.trans run) using 1
   norm_num [largeOps]
 · simpa [u,largeOps,applyBlock,Op.apply,writeNat,next,entered] using large_follow
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,k',o',Nat.ne_of_gt radix_positive]
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next]
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,k',Nat.ne_of_gt radix_positive]
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,k',o',Nat.ne_of_gt radix_positive]
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,k',o',Nat.ne_of_gt radix_positive]
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,f',o']
 · simp [u,largeOps,applyBlock,Op.apply,evalNat,writeNat,next,v',o']
end
end ExactFourierCircuits.UniformRecursiveSavingExecution
