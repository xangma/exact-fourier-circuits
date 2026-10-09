import UniformRecursiveSelfCallMachine
import UniformResidualExtendedPermutation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveBatchGroupMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section
abbrev W := UniformRecursiveSelfCallMachine.W

def bootGroups : List Op := [.literal 4164 W,.binary .mul 4165 4164 4015,
 .binary .div 4126 4023 4165,.literal 4125 0,.binary .mul 4124 4015 4069]
lemma initialize_length : bootGroups.length=5:=rfl

def groupCount (q w r:ℕ) := 2^(q*w+r-ExplicitSeedBudget.roleBits)
lemma W_eq : W=2^ExplicitSeedBudget.roleBits:=by
 change ExplicitSeedBudget.paddedRoles=2^ExplicitSeedBudget.roleBits
 rfl
lemma partition (q w r:ℕ) (fits:ExplicitSeedBudget.roleBits ≤ q*w+r) :
 groupCount q w r*(W*2^q)=2^(q*(w+1)+r):=by
 rw [W_eq]
 exact UniformResidualExtendedPermutation.complete_batches q w r ExplicitSeedBudget.roleBits fits
lemma groupCount_positive (q w r:ℕ) : 0 < groupCount q w r:=Nat.two_pow_pos _
lemma division (q w r:ℕ) (fits:ExplicitSeedBudget.roleBits ≤ q*w+r) :
 2^(q*(w+1)+r)/(W*2^q)=groupCount q w r:=by
 rw [←partition q w r fits]
 exact Nat.mul_div_left _ (Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos _))

/-- Compute the exact complete-W group count from the produced native sizes.
No group directory, divisibility answer or child action is an entry premise. -/
theorem initialize_execution (p:Program) (start n B q w r D:ℕ) (x:Fin n→ℂ) (s:State)
 (code:BlockAt bootGroups p start) (pc:s.pc=start)
 (size:s.natReg 4015=2^q) (volume:s.natReg 4023=2^(q*(w+1)+r)) (one:s.natReg 4069=1)
 (fits:ExplicitSeedBudget.roleBits ≤ q*w+r) (bound:WordBound B s)
 (extent:start+5 ≤ B) (dataEnd:D+2^(q*(w+1)+r) ≤ B) :
 BoundedRuns p n x B s 5 (applyBlock bootGroups s)  ∧ 
 (applyBlock bootGroups s).natReg 4126=groupCount q w r  ∧ 
 (applyBlock bootGroups s).natReg 4125=0  ∧  (applyBlock bootGroups s).natReg 4124=2^q  ∧ 
 (applyBlock bootGroups s).natHeap=s.natHeap  ∧  (applyBlock bootGroups s).scalarHeap=s.scalarHeap :=by
 have part:=partition q w r fits
 have positive:=groupCount_positive q w r
 have gb:=UniformRecursiveSelfCallMachine.group_bounds D (2^(q*(w+1)+r)) (2^q) 0 (groupCount q w r) B
  part positive dataEnd (Nat.two_pow_pos _)
 have countBound:groupCount q w r ≤ B:=by
  have h:groupCount q w r ≤ groupCount q w r*(W*2^q):=Nat.le_mul_of_pos_right _
   (Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos _))
  rw [part] at h
  omega
 have sizeB:2^q ≤ B:=by have h:=bound.2.1 4015;rwa [size] at h
 have safe:readable bootGroups s  ∧  peak bootGroups s ≤ B:=by
  simp [bootGroups,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,size,volume,one,
   division q w r fits,Nat.ne_of_gt (Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos q)),
   gb.1,gb.2.1,countBound,sizeB]
 have run:=block_runs bootGroups p start n B x s code pc bound (by rw [initialize_length];exact extent) safe.1 safe.2
 refine ⟨run,?_,?_,?_,rfl,rfl⟩
 all_goals simp [bootGroups,applyBlock,Op.apply,evalNat,writeNat,next,size,volume,one,
  division q w r fits,Nat.ne_of_gt (Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos q))]

/-- The loop is a real Nat comparison. Its positive branch reaches the fixed
save/setup/self-call fragment; its final branch reaches the native inverse/scatter. -/
theorem branch_execution (p:Program) (loop call finish n B i count:ℕ) (x:Fin n→ℂ) (s:State)
 (code:p[loop]?=some (.branchLT 4125 4126 call finish)) (pc:s.pc=loop)
 (index:s.natReg 4125=i) (total:s.natReg 4126=count) (bound:WordBound B s)
 (callBound:call ≤ B) (finishBound:finish ≤ B) :
 BoundedRuns p n x B s 1 {s with pc:=if i < count then call else finish}:=by
 exact .next bound (by simp [step,pc,code,index,total])
  (.refl (changePC_bound B s _ bound (by split_ifs  <;> assumption)))

/-- Physical data produced by the native gather is already in exact complete
W-array order. Spectator coordinates are in this one full grouping. -/
lemma group_data_generic {q w r b D:ℕ} {v:BinaryFrames.Vec (Fin (w+1))} {pivot:Fin (w+1)} {hp:v pivot=1}
 (fits:b ≤ q*w+r) (X:Fin (2^(q*(w+1)+r))→Scalar) (s:State)
 (data:∀c:Fin (2^(q*w+r)),∀t:Fin (2^q),s.scalarHeap (D+c.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.fibers q w r v pivot hp (c,t))))
 (g:Fin (2^(q*w+r-b))) (role:Fin (2^b)) (t:Fin (2^q)) :
 s.scalarHeap (D+g.val*(2^b*2^q)+role.val*2^q+t.val)=
  some (X (UniformResidualExtendedPermutation.groups q w r b fits v pivot hp (g,(role,t)))):=by
 rw [UniformResidualExtendedPermutation.groups_fibers]
 have h:=data (finCongr (by rw [←Nat.pow_add];congr 1;omega)
   (finProdFinEquiv (g,role))) t
 rw [show D+g.val*(2^b*2^q)+role.val*2^q+t.val=
  D+(role.val*2^q+(g.val*(2^q*2^b)+t.val)) by ring]
 simpa only [finProdFinEquiv,Equiv.coe_fn_mk,finCongr_apply,Fin.coe_cast,
  Nat.mul_add,Nat.add_mul,Nat.add_assoc,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
end
end ExactFourierCircuits.UniformRecursiveBatchGroupMachine
