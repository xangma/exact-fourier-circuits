import UniformJointCacheWorkspace
set_option autoImplicit false
namespace ExactFourierCircuits.UniformJointCacheWorkspaceMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
namespace W
abbrev stride:=UniformJointCacheWorkspace.stride
abbrev original:=UniformJointCacheWorkspace.original
abbrev work:=UniformJointCacheWorkspace.work
end W
noncomputable section
def headerOps (r:ℕ)(fs:List ℕ):List Op:=match fs with
 | []=>[]
 | f::rest=>[.literal 6309 f,.mul r 6309 6308]++headerOps (r+1) rest
lemma headers_length (r:ℕ)(fs:List ℕ):(headerOps r fs).length=2*fs.length:=by
 induction fs generalizing r with
 | nil=>rfl
 | cons f fs ih=>simp [headerOps,ih];omega
lemma headers_slab (r u:ℕ)(fs:List ℕ)(s:State)(high:6309<r)(sl:s.natReg 6308=u):
 (applyBlock (headerOps r fs) s).natReg 6308=u:=by
 induction fs generalizing r s with
 | nil=>exact sl
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  apply ih (r+1) _ (by omega)
  simp (disch:=omega) [Op.apply,writeNat,next,sl]
lemma headers_natReg (r:ℕ)(fs:List ℕ)(s:State)(j:ℕ)(temp:j≠6309)(outside:j<r∨r+fs.length≤ j):
 (applyBlock (headerOps r fs) s).natReg j=s.natReg j:=by
 induction fs generalizing r s with
 | nil=>rfl
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  rw [ih (r+1) _ (by simp only [List.length_cons] at outside;omega)]
  have ne:j≠r:=by simp only [List.length_cons] at outside;omega
  simp [Op.apply,writeNat,next,temp,ne]
lemma headers_value (r u:ℕ)(fs:List ℕ)(s:State)(high:6309<r)(sl:s.natReg 6308=u)
 (i:ℕ)(hi:i<fs.length):
 (applyBlock (headerOps r fs) s).natReg (r+i)=fs[i]*u:=by
 induction fs generalizing r s i with
 | nil=>simp at hi
 | cons f fs ih=>
  simp only [headerOps,List.cons_append,List.nil_append,applyBlock]
  let t:=Op.apply (.mul r 6309 6308) (Op.apply (.literal 6309 f) s)
  have ts:t.natReg 6308=u:=by simp (disch:=omega) [t,Op.apply,writeNat,next,sl]
  cases i with
  | zero=>
   have keep:=headers_natReg (r+1) fs t r (by omega) (Or.inl (by omega))
   simp only [Nat.add_zero,List.getElem_cons_zero]
   change (applyBlock (headerOps (r+1) fs) t).natReg r=f*u
   rw [keep];simp [t,Op.apply,writeNat,next,sl]
  | succ i=>
   have h:=ih (r+1) t (by omega) ts i (by simp only [List.length_cons] at hi;omega)
   simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
lemma headers_safe (r u:ℕ)(fs:List ℕ)(s:State)(high:6309<r)(sl:s.natReg 6308=u)
 (positive:1≤ u)(small:∀f∈fs,f≤32):
 readable (headerOps r fs) s ∧ peak (headerOps r fs) s≤32*u:=by
 induction fs generalizing r s with
 | nil=>simp [headerOps,readable,peak]
 | cons f fs ih=>
  have fsmall:f≤32:=small f (by simp)
  let t:=Op.apply (.mul r 6309 6308) (Op.apply (.literal 6309 f) s)
  have ts:t.natReg 6308=u:=by simp (disch:=omega) [t,Op.apply,writeNat,next,sl]
  have tail:=ih (r+1) t (by omega) ts (by intro a ha;exact small a (by simp [ha]))
  have lit:f≤32*u:=(fsmall.trans (Nat.le_mul_of_pos_right _ positive))
  have prod:f*u≤32*u:=Nat.mul_le_mul_right u fsmall
  simpa (disch:=omega) [headerOps,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,sl,t] using
   And.intro tail.1 (max_le lit (max_le prod tail.2))
lemma headers_frame (r:ℕ)(fs:List ℕ)(s:State):
 (applyBlock (headerOps r fs) s).natHeap=s.natHeap ∧
 (applyBlock (headerOps r fs) s).scalarHeap=s.scalarHeap ∧
 (applyBlock (headerOps r fs) s).scalarReg=s.scalarReg ∧
 (applyBlock (headerOps r fs) s).outputs=s.outputs ∧
 (applyBlock (headerOps r fs) s).rootOrders=s.rootOrders:=by
 induction fs generalizing r s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons f fs ih=>
  have h:=ih (r+1) (Op.apply (.mul r 6309 6308) (Op.apply (.literal 6309 f) s))
  simpa [headerOps,applyBlock,Op.apply,writeNat,next] using h


/-- Actual root allocator leaves Nat6002=(n+2)^19; other allocated banks are retained. -/
def boot : List Op := [.literal 6309 0,.add 6308 6002 6309]
def factors : List ℕ := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
def program : Program := boot.map Op.code++(headerOps 6400 factors).map Op.code++[.halt]
lemma boot_length : boot.length=2 := rfl
lemma factors_length : factors.length=32 := rfl
lemma program_length : program.length=67 := by
 simp only [program,List.length_append,List.length_map,boot_length,headers_length,factors_length,List.length_singleton]
lemma boot_code : BlockAt boot program 0 := by
 intro i hi
 change i < 2 at hi
 interval_cases i <;> rfl
lemma header_code : BlockAt (headerOps 6400 factors) program 2 := by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment (boot.map Op.code)
  ((headerOps 6400 factors).map Op.code) [.halt] i (by simpa using hi)
 simpa only [program,List.length_map,boot_length,List.getElem?_map,
  List.getElem?_eq_getElem hi,Option.map_some] using lookup
lemma halt_at : program[66]?=some .halt := rfl
lemma factors_small : ∀f∈factors,f ≤ 32 := by
 intro f hf
 simp only [factors,List.mem_cons,List.not_mem_nil,or_false] at hf
 omega
lemma factors_value (i : Fin 32) : factors[i.val]'(by rw [factors_length];exact i.isLt)=i.val+1 := by
 fin_cases i <;> rfl
lemma boot_value (n : ℕ) (s : State) (h : s.natReg 6002=W.stride n) :
 (applyBlock boot s).natReg 6308=W.stride n := by
 simp [boot,applyBlock,Op.apply,writeNat,next,h]
def result (s : State) := applyBlock (headerOps 6400 factors) (applyBlock boot s)
lemma exact_banks (n : ℕ) (s : State) (h : s.natReg 6002=W.stride n) (i : Fin 32) :
 (result s).natReg (6400+i.val)=(i.val+1)*W.stride n := by
 have v:=headers_value 6400 (W.stride n) factors (applyBlock boot s) (by decide) (boot_value n s h)
  i.val (by rw [factors_length];exact i.isLt)
 rw [factors_value i] at v
 exact v
lemma result_frame (s : State) :
 (result s).natHeap=s.natHeap ∧ (result s).scalarHeap=s.scalarHeap ∧
 (result s).scalarReg=s.scalarReg ∧ (result s).outputs=s.outputs ∧ (result s).rootOrders=s.rootOrders ∧
 (∀r,r ≠ 6308 → r ≠ 6309 → (r < 6400 ∨ 6432 ≤ r) → (result s).natReg r=s.natReg r) := by
 have f:=headers_frame 6400 factors (applyBlock boot s)
 refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2,?_⟩
 intro r h8 h9 hr
 have k:=headers_natReg 6400 factors (applyBlock boot s) r h9 (by rw [factors_length];exact hr)
 rw [result,k]
 simp [boot,applyBlock,Op.apply,writeNat,next,h8,h9]
theorem execution (n B : ℕ) (x : Fin n → ℂ) (s : State)
 (h : s.natReg 6002=W.stride n) (codeBound : 67 ≤ B) (bankBound : 32*W.stride n ≤ B)
 (pc : s.pc=0) (hs : WordBound B s) :
 BoundedExecution program n x B s 67 (result s) ∧ (result s).pc=66 ∧
 (∀i : Fin 32,(result s).natReg (6400+i.val)=(i.val+1)*W.stride n) := by
 have small : W.stride n ≤ B := by omega
 have first:=block_runs boot program 0 n B x s boot_code pc hs (by rw [boot_length];omega)
  (by simp [boot,readable,Op.readable])
  (by simp [boot,peak,Op.peak,Op.apply,writeNat,next,h];exact small)
 let t:=applyBlock boot s
 have tp:t.pc=2 := by rw [applyBlock_pc,pc,boot_length]
 have value:t.natReg 6308=W.stride n := boot_value n s h
 have positive : 1 ≤ W.stride n := Nat.one_le_pow _ _ (by omega)
 obtain ⟨rd,pk⟩:=headers_safe 6400 (W.stride n) factors t (by decide) value positive factors_small
 have second:=block_runs (headerOps 6400 factors) program 2 n B x t header_code tp first.final_bound
  (by rw [headers_length,factors_length];omega) rd (pk.trans bankBound)
 have rp : (result s).pc=66 := by
  change (applyBlock (headerOps 6400 factors) t).pc=66
  rw [applyBlock_pc,tp,headers_length,factors_length]
 have halt : BoundedExecution program n x B (result s) 1 (result s) :=
  .halt second.final_bound (by rw [step,rp];rfl)
 refine ⟨?_,rp,exact_banks n s h⟩
 convert first.executes (second.executes halt) using 1
 rw [headers_length,factors_length,boot_length]
attribute [irreducible] result
end
end ExactFourierCircuits.UniformJointCacheWorkspaceMachine
