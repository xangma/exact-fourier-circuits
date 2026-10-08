import UniformSixCDepthColorController
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSixCTraversal
open UniformMachine UniformAssembly
open UniformSixCDepthColorController
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

def layerOrdinal (backwards:Bool) (total i:ℕ) := if backwards then total-1-i else i
def layerDepth (backwards:Bool) (total i:ℕ) := layerOrdinal backwards total i/11
def layerColor (backwards:Bool) (total i:ℕ) := layerOrdinal backwards total i%11
lemma ordinal_bound (backwards:Bool) (total i:ℕ) (hi:i<total) : layerOrdinal backwards total i<total:=by
 cases backwards <;> simp [layerOrdinal] <;> omega
lemma depth_bound (backwards:Bool) (H i:ℕ) (hi:i<H*11) : layerDepth backwards (H*11) i<H:=by
 exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (ordinal_bound backwards _ _ hi)
lemma color_bound (backwards:Bool) (total i:ℕ) : layerColor backwards total i<11:=
 Nat.mod_lt _ (by decide)
lemma descending_ordinal (total:ℕ) (i:Fin total) : layerOrdinal true total i.val=i.rev.val:=by
 simp only [layerOrdinal,ite_true,Fin.val_rev];omega
lemma ascending_encode (H i:ℕ) (_hi:i<H*11) :
 11*layerDepth false (H*11) i+layerColor false (H*11) i=i:=by
 simp only [layerDepth,layerColor,layerOrdinal,Bool.false_eq_true,ite_false]
 omega
lemma descending_encode (H i:ℕ) (_hi:i<H*11) :
 11*layerDepth true (H*11) i+layerColor true (H*11) i=H*11-1-i:=by
 simp only [layerDepth,layerColor,layerOrdinal,ite_true]
 omega

def reversePrefix (backwards:Bool) : List Op :=
 if backwards then [.sub 3028 3027 3022,.sub 3028 3028 3021] else []
def ordinalRegister (backwards:Bool) := if backwards then 3028 else 3021
lemma reversePrefix_length (backwards:Bool) : (reversePrefix backwards).length=if backwards then 2 else 0:=by
 cases backwards <;> rfl
lemma head_code (backwards:Bool) : ∀i,(hi:i<(cursorHead backwards).length)→
 (traversalProgram backwards)[10+i]?=some ((cursorHead backwards)[i]'hi):=by
 intro i hi
 have h:=UniformAllAxisSeedPreparation.lookup_segment
  (traversalBoot.map Op.code++[.branchLT 3021 3027 10 (traversalHaltPC backwards)])
  (cursorHead backwards)
  ((traversalBody backwards).map (relocate (traversalBodyBase backwards) (traversalTickPC backwards))++
   [.natBinary .add 3021 3021 3022,.jump 9,.halt]) i hi
 have len:(traversalBoot.map Op.code++[Instruction.branchLT 3021 3027 10 (traversalHaltPC backwards)]).length=10:=by
  simp [traversalBoot_length]
 simpa only [traversalProgram,List.append_assoc,len,List.getElem?_eq_getElem hi] using h
lemma reverse_prefix_code (backwards:Bool) :
 BlockAt (reversePrefix backwards) (traversalProgram backwards) 10:=by
 cases backwards with
 | false=>intro i hi;change i<0 at hi;omega
 | true=>
  intro i hi;change i<2 at hi
  have h:=head_code true i (by change i<4;omega)
  interval_cases i <;> exact h
lemma division_at (backwards:Bool) :
 (traversalProgram backwards)[10+(reversePrefix backwards).length]?=
 some (.natBinary .div 1191 (ordinalRegister backwards) 3023):=by
 cases backwards with
 | false=>exact head_code false 0 (by decide)
 | true=>exact head_code true 2 (by decide)
lemma remainder_at (backwards:Bool) :
 (traversalProgram backwards)[10+(reversePrefix backwards).length+1]?=
 some (.natBinary .mod 1192 (ordinalRegister backwards) 3023):=by
 cases backwards with
 | false=>exact head_code false 1 (by decide)
 | true=>exact head_code true 3 (by decide)

noncomputable section
structure Cursor (K i:ℕ) (s:State) : Prop where
 index:s.natReg 3021=i
 one:s.natReg 3022=1
 eleven:s.natReg 3023=11
 total:s.natReg 3027=(8*K+7)*11
 zero:s.natReg 3026=0

def decoded (backwards:Bool) (s:State) : State :=
 let p:=applyBlock (reversePrefix backwards) s
 let index:=p.natReg (ordinalRegister backwards)
 writeNat (writeNat p 1191 (index/p.natReg 3023)) 1192 (index%p.natReg 3023)
lemma reversePrefix_heap (backwards:Bool) (s:State) :
 (applyBlock (reversePrefix backwards) s).natHeap=s.natHeap ∧
 (applyBlock (reversePrefix backwards) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (reversePrefix backwards) s).outputs=s.outputs ∧
 (applyBlock (reversePrefix backwards) s).rootOrders=s.rootOrders:=by
 cases backwards <;> exact ⟨rfl,rfl,rfl,rfl⟩
lemma reversePrefix_register (backwards:Bool) (s:State) (q:ℕ) (hq:q≠3028) :
 (applyBlock (reversePrefix backwards) s).natReg q=s.natReg q:=by
 cases backwards <;> simp [reversePrefix,applyBlock,Op.apply,writeNat,next,hq]
lemma reversePrefix_ordinal (backwards:Bool) {K i:ℕ} {s:State} (cur:Cursor K i s) :
 (applyBlock (reversePrefix backwards) s).natReg (ordinalRegister backwards)=
 layerOrdinal backwards ((8*K+7)*11) i:=by
 cases backwards <;> simp [reversePrefix,ordinalRegister,applyBlock,Op.apply,writeNat,next,
  layerOrdinal,cur.index,cur.total,cur.one]
lemma decoded_registers (backwards:Bool) {K i:ℕ} {s:State} (cur:Cursor K i s) :
 (decoded backwards s).natReg 1191=layerDepth backwards ((8*K+7)*11) i ∧
 (decoded backwards s).natReg 1192=layerColor backwards ((8*K+7)*11) i:=by
 have k: (applyBlock (reversePrefix backwards) s).natReg 3023=11:=
  (reversePrefix_register backwards s 3023 (by decide)).trans cur.eleven
 simp [decoded,writeNat,next,layerDepth,layerColor,k,reversePrefix_ordinal backwards cur]
lemma decoded_high (backwards:Bool) (s:State) (q:ℕ) (lo:3001≤q) (ne:q≠3028) :
 (decoded backwards s).natReg q=s.natReg q:=by
 simp [decoded,writeNat,next,show q≠1191 by omega,show q≠1192 by omega,
  reversePrefix_register backwards s q ne]
lemma decoded_cursor (backwards:Bool) {K i:ℕ} {s:State} (cur:Cursor K i s) :
 Cursor K i (decoded backwards s):=by
 constructor
 · exact (decoded_high backwards s 3021 (by decide) (by decide)).trans cur.index
 · exact (decoded_high backwards s 3022 (by decide) (by decide)).trans cur.one
 · exact (decoded_high backwards s 3023 (by decide) (by decide)).trans cur.eleven
 · exact (decoded_high backwards s 3027 (by decide) (by decide)).trans cur.total
 · exact (decoded_high backwards s 3026 (by decide) (by decide)).trans cur.zero
lemma decoded_heap (backwards:Bool) (s:State) :
 (decoded backwards s).natHeap=s.natHeap ∧ (decoded backwards s).scalarHeap=s.scalarHeap ∧
 (decoded backwards s).outputs=s.outputs ∧ (decoded backwards s).rootOrders=s.rootOrders:=by
 unfold decoded
 exact reversePrefix_heap backwards s
lemma decoded_readonly (backwards:Bool) (s:State) (q:ℕ) (h:readonly q=true) (nd:q≠1191) (nc:q≠1192) :
 (decoded backwards s).natReg q=s.natReg q:=by
 have range:=h
 simp only [readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
 simp [decoded,writeNat,next,nd,nc,reversePrefix_register backwards s q (by omega)]

/-- Both quotient and remainder are literal Nat operations with a checked
nonzero divisor. The source ordinal is computed internally in descending mode. -/
theorem decode_execution (backwards:Bool) {K i n B:ℕ} (x:Fin n→ℂ) (s:State)
 (cur:Cursor K i s) (_hi:i<(8*K+7)*11) (pc:s.pc=10) (bound:WordBound B s)
 (code:(traversalProgram backwards).length≤B) :
 BoundedRuns (traversalProgram backwards) n x B s (cursorHead backwards).length (decoded backwards s) ∧
 (decoded backwards s).pc=traversalBodyBase backwards := by
 have safe:readable (reversePrefix backwards) s ∧ peak (reversePrefix backwards) s≤B:=by
  cases backwards with
  | false=>exact ⟨trivial,Nat.zero_le _⟩
  | true=>
   simp [reversePrefix,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
    cur.total,cur.one,cur.index]
   have limit:=bound.2.1 3027;rw [cur.total] at limit;omega
 have prefRun:=block_runs (reversePrefix backwards) (traversalProgram backwards) 10 n B x s
  (reverse_prefix_code backwards) pc bound
  (by rw [traversalProgram_length] at code;cases backwards <;> simp_all only [reversePrefix_length,Bool.false_eq_true,ite_false,ite_true] <;> omega)
  safe.1 safe.2
 let p:=applyBlock (reversePrefix backwards) s
 have pp:p.pc=10+(reversePrefix backwards).length:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc]
 have den:p.natReg 3023=11:=(reversePrefix_register backwards s 3023 (by decide)).trans cur.eleven
 let a:=writeNat p 1191 (p.natReg (ordinalRegister backwards)/11)
 have ab:WordBound B a:=writeNat_bound B p 1191 _ prefRun.final_bound
  (by rw [pp];rw [traversalProgram_length] at code;cases backwards <;> simp_all only [reversePrefix_length,Bool.false_eq_true,ite_false,ite_true] <;> omega)
  ((Nat.div_le_self _ _).trans (prefRun.final_bound.2.1 _))
 have div:step (traversalProgram backwards) n x p=.running a:=by
  simp [step,pp,division_at,evalNat,den,a]
 let u:=writeNat a 1192 (p.natReg (ordinalRegister backwards)%11)
 have ub:WordBound B u:=writeNat_bound B a 1192 _ ab
  (by simp [a,writeNat,next,pp];rw [traversalProgram_length] at code;cases backwards <;> simp_all only [reversePrefix_length,Bool.false_eq_true,ite_false,ite_true] <;> omega)
  (Nat.le_trans (Nat.mod_le _ _) (prefRun.final_bound.2.1 _))
 have rem:step (traversalProgram backwards) n x a=.running u:=by
  have ap:a.pc=10+(reversePrefix backwards).length+1:=by simp [a,writeNat,next,pp]
  have ind:a.natReg (ordinalRegister backwards)=p.natReg (ordinalRegister backwards):=by
   cases backwards <;> simp [a,writeNat,next,ordinalRegister]
  have de:a.natReg 3023=11:=by simp [a,writeNat,next,den]
  simp [step,ap,remainder_at,evalNat,de,ind,u]
 have tail:BoundedRuns (traversalProgram backwards) n x B p 2 u:=
  .next prefRun.final_bound div (.next ab rem (.refl ub))
 have ud:u=decoded backwards s:=by simp [u,a,decoded,p,den]
 rw [ud] at tail
 constructor
 · convert prefRun.trans tail using 1
   cases backwards <;> rfl
 · rw [←ud]
   simp [u,a,writeNat,next,pp,traversalBodyBase,cursorHead_length,reversePrefix_length]
   cases backwards <;> rfl
lemma traversal_boot_cursor {K:ℕ} (s:State) (hk:s.natReg 1050=K) :
 Cursor K 0 (applyBlock traversalBoot s):=by
 constructor <;> simp [traversalBoot,applyBlock,Op.apply,writeNat,next,hk,Nat.mul_comm K 8]
lemma traversal_boot_readonly (s:State) (q:ℕ) (h:readonly q=true) :
 (applyBlock traversalBoot s).natReg q=s.natReg q:=by
 have range:=h
 simp only [readonly,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
 simp (disch:=omega) [traversalBoot,applyBlock,Op.apply,writeNat,next]
lemma traversal_boot_high (s:State) (q:ℕ) (h:3001≤q) (stop:q≤3020) :
 (applyBlock traversalBoot s).natReg q=s.natReg q:=by
 simp (disch:=omega) [traversalBoot,applyBlock,Op.apply,writeNat,next]
lemma traversal_boot_heap (s:State) :
 (applyBlock traversalBoot s).natHeap=s.natHeap ∧
 (applyBlock traversalBoot s).scalarHeap=s.scalarHeap ∧
 (applyBlock traversalBoot s).outputs=s.outputs ∧
 (applyBlock traversalBoot s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
theorem traversal_boot_execution (backwards:Bool) {K n B:ℕ} (x:Fin n→ℂ) (s:State)
 (hk:s.natReg 1050=K) (count:(8*K+7)*11≤B) (pc:s.pc=0) (bound:WordBound B s)
 (code:(traversalProgram backwards).length≤B) :
 BoundedRuns (traversalProgram backwards) n x B s 9 (applyBlock traversalBoot s) ∧
 (applyBlock traversalBoot s).pc=9 ∧ Cursor K 0 (applyBlock traversalBoot s):=by
 have min:11≤B:=by rw [traversalProgram_length] at code;cases backwards <;> simp_all <;> omega
 have safe:peak traversalBoot s≤B:=by
  simp [peak,traversalBoot,Op.peak,Op.apply,writeNat,next,hk]
  omega
 have run:=block_runs traversalBoot (traversalProgram backwards) 0 n B x s
  (traversal_boot_code backwards) pc bound (by rw [traversalBoot_length];omega)
  (by simp [traversalBoot,readable,Op.readable]) safe
 exact ⟨by simpa only [traversalBoot_length] using run,by rw [UniformTensorMonomialMachine.applyBlock_pc,pc];rfl,
  traversal_boot_cursor s hk⟩

def tickState (_backwards:Bool) (s:State) := setPC (writeNat s 3021 (s.natReg 3021+s.natReg 3022)) 9
lemma tick_cursor (backwards:Bool) {K i:ℕ} {s:State} (h:Cursor K i s) :
 Cursor K (i+1) (tickState backwards s):=by
 constructor <;> simp [tickState,setPC,writeNat,next,h.index,h.one,h.eleven,h.total,h.zero]
lemma tick_high (backwards:Bool) (s:State) (q:ℕ) (ne:q≠3021) :
 (tickState backwards s).natReg q=s.natReg q:=by simp [tickState,setPC,writeNat,next,ne]
lemma tick_heap (backwards:Bool) (s:State) :
 (tickState backwards s).natHeap=s.natHeap ∧ (tickState backwards s).scalarHeap=s.scalarHeap ∧
 (tickState backwards s).outputs=s.outputs ∧ (tickState backwards s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl⟩
theorem tick_execution (backwards:Bool) {K i n B:ℕ} (x:Fin n→ℂ) (s:State)
 (cur:Cursor K i s) (hi:i<(8*K+7)*11) (pc:s.pc=traversalTickPC backwards)
 (bound:WordBound B s) (code:(traversalProgram backwards).length≤B) :
 BoundedRuns (traversalProgram backwards) n x B s 2 (tickState backwards s):=by
 have count:=bound.2.1 3027;rw [cur.total] at count
 let a:=writeNat s 3021 (i+1)
 have ap:a.pc=traversalTickPC backwards+1:=by simp [a,writeNat,next,pc]
 have bp:traversalTickPC backwards+2≤B:=by
  rw [traversalProgram_length] at code
  cases backwards <;> simp_all [traversalTickPC,traversalBodyBase,cursorHead_length,traversalBody_length] <;> omega
 have ab:WordBound B a:=writeNat_bound B s 3021 _ bound (by omega) (by omega)
 have first:step (traversalProgram backwards) n x s=.running a:=by
  simp [step,pc,traversal_tick_at,evalNat,a,cur.index,cur.one]
 have ub:WordBound B (tickState backwards s):=by
  simpa [tickState,a,setPC,cur.index,cur.one] using changePC_bound B a 9 ab (by omega)
 have second:step (traversalProgram backwards) n x a=.running (tickState backwards s):=by
  simp [step,ap,traversal_jump_at,tickState,a,setPC,cur.index,cur.one]
 exact .next bound first (.next ab second (.refl ub))
theorem enter_iteration (backwards:Bool) {K i n B:ℕ} (x:Fin n→ℂ) (s:State)
 (cur:Cursor K i s) (hi:i<(8*K+7)*11) (pc:s.pc=9) (bound:WordBound B s)
 (code:(traversalProgram backwards).length≤B) :
 BoundedRuns (traversalProgram backwards) n x B s (1+(cursorHead backwards).length)
  (decoded backwards (setPC s 10)) ∧
 (decoded backwards (setPC s 10)).pc=traversalBodyBase backwards ∧
 Cursor K i (decoded backwards (setPC s 10)):=by
 have bp:10≤B:=by rw [traversalProgram_length] at code;cases backwards <;> simp_all <;> omega
 have enter:BoundedRuns (traversalProgram backwards) n x B s 1 (setPC s 10):=
  .next bound (by simp [step,pc,traversal_branch_at,cur.index,cur.total,hi,setPC])
   (.refl (changePC_bound B s 10 bound bp))
 have shifted:Cursor K i (setPC s 10):=⟨cur.index,cur.one,cur.eleven,cur.total,cur.zero⟩
 have head:=decode_execution backwards x (setPC s 10) shifted hi rfl enter.final_bound code
 exact ⟨enter.trans head.1,head.2,decoded_cursor backwards shifted⟩
theorem finish_iteration (backwards:Bool) {K n B:ℕ} (x:Fin n→ℂ) (s:State)
 (cur:Cursor K ((8*K+7)*11) s) (pc:s.pc=9) (bound:WordBound B s)
 (code:(traversalProgram backwards).length≤B) :
 BoundedExecution (traversalProgram backwards) n x B s 2 (setPC s (traversalHaltPC backwards)):=by
 have hp:traversalHaltPC backwards≤B:=by
  rw [traversalProgram_length] at code
  cases backwards <;> simp_all [traversalHaltPC,traversalTickPC,traversalBodyBase,cursorHead_length,traversalBody_length] <;> omega
 have last:step (traversalProgram backwards) n x s=.running (setPC s (traversalHaltPC backwards)):=by
  simp [step,pc,traversal_branch_at,cur.index,cur.total,setPC]
 exact .next bound last (.halt (changePC_bound B s _ bound hp)
  (by simp [step,setPC,traversal_halt_at]))

end
end ExactFourierCircuits.UniformSixCTraversal
