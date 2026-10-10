import DFTModelCacheDescriptorAmount
import DFTModelCacheDescriptorFold

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targetWidth sourceWidth targets sources targetSize sourceSize pairAmount)
noncomputable section

abbrev ChunkPair := p Pair Pair
abbrev SourceInput := p Pair w

def minimum {s : Ty} (f g : Prog false s w) : Prog false s w :=
  nat .sub f (nat .sub f g)

def split : Prog false w w := nat .div (.atom .id) (.atom (.lit 2))
def target : Prog false w w := nat .sub (.atom .id) split

def chunks (width : Prog false w w) : Prog false Pair w :=
  nat .div (nat .sub (nat .add (.comp (.atom .fst) width) (.atom .snd))
    (.atom (.lit 1))) (.atom .snd)
def targetCount : Prog false Pair w := chunks target
def sourceCount : Prog false Pair w := chunks split

def pairV : Prog false ChunkPair w := .comp (.atom .fst) (.atom .fst)
def pairB : Prog false ChunkPair w := .comp (.atom .fst) (.atom .snd)
def pairI : Prog false ChunkPair w := .comp (.atom .snd) (.atom .fst)
def pairJ : Prog false ChunkPair w := .comp (.atom .snd) (.atom .snd)
def targetPart : Prog false ChunkPair w :=
  minimum pairB (nat .sub (.comp pairV target) (nat .mul pairI pairB))
def sourcePart : Prog false ChunkPair w :=
  minimum pairB (nat .sub (.comp pairV split) (nat .mul pairJ pairB))
def pairSizes : Prog false ChunkPair Pair := .fork targetPart sourcePart
/-- One is a failed pair, zero is a fitting pair. -/
def badPair : Prog false ChunkPair w :=
  nat .lt pairV (.comp pairSizes amount)
def sourceRepack : Prog false (p SourceInput w) ChunkPair :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd))
def sourceTerm : Prog false (p SourceInput w) w := .comp sourceRepack badPair
def sourceBad : Prog false SourceInput w :=
  sumProgram (.comp (.atom .fst) sourceCount) sourceTerm
def allBad : Prog false Pair w := sumProgram targetCount sourceBad

theorem minimum_value {s : Ty} (f g : Prog false s w) (x : s.T) :
    (run (minimum f g) x).val=min (run f x).val (run g x).val := by
  dsimp only [minimum,nat,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]
  exact Nat.sub_sub_eq_min _ _

theorem split_value (v : ℕ) : (run split v).val=sourceWidth v := by
  simp [split,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,sourceWidth]
theorem target_value (v : ℕ) : (run target v).val=targetWidth v := by
  change v-(run split v).val=_
  rw [split_value]
  rfl

theorem chunks_value (width : Prog false w w) (v b : ℕ) :
    (run (chunks width) (v,b)).val=UniformWorkspacePlanner.chunkCount (run width v).val b := by
  simp [chunks,nat,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,
    UniformWorkspacePlanner.chunkCount]
theorem targetCount_value (v b : ℕ) : (run targetCount (v,b)).val=targets v b := by
  rw [targetCount,chunks_value,target_value];rfl
theorem sourceCount_value (v b : ℕ) : (run sourceCount (v,b)).val=sources v b := by
  rw [sourceCount,chunks_value,split_value];rfl

attribute [local irreducible] minimum target split amount

theorem pairSizes_value (v b i j : ℕ) :
    (run pairSizes ((v,b),(i,j))).val=(targetSize v b i,sourceSize v b j) := by
  change ((run targetPart ((v,b),(i,j))).val,(run sourcePart ((v,b),(i,j))).val)=_
  rw [targetPart,sourcePart,minimum_value,minimum_value]
  change (min b ((run target v).val-i*b),min b ((run split v).val-j*b))=_
  rw [target_value,split_value]
  rfl

attribute [local irreducible] pairSizes badPair sourceTerm sourceBad allBad

theorem badPair_value (v b i j : ℕ) :
    (run badPair ((v,b),(i,j))).val=if v<pairAmount v b i j then 1 else 0 := by
  rw [badPair]
  change (if (run pairV ((v,b),(i,j))).val<
    (run amount (run pairSizes ((v,b),(i,j))).val).val then 1 else 0)=_
  rw [pairSizes_value,amount_value]
  rfl

theorem sourceTerm_value (v b i j : ℕ) :
    (run sourceTerm (((v,b),i),j)).val=if v<pairAmount v b i j then 1 else 0 := by
  rw [sourceTerm]
  change (run badPair (run sourceRepack (((v,b),i),j)).val).val=_
  have h : (run sourceRepack (((v,b),i),j)).val=((v,b),(i,j)) := rfl
  rw [h,badPair_value]

theorem sourceBad_value (v b i : ℕ) :
    (run sourceBad ((v,b),i)).val=
      ∑j∈Finset.range (sources v b),if v<pairAmount v b i j then 1 else 0 := by
  rw [sourceBad,sumProgram_value]
  have count : (run (.comp (.atom .fst) sourceCount : Prog false SourceInput w) ((v,b),i)).val=sources v b :=
    by
      change (run sourceCount (v,b)).val=_
      exact sourceCount_value v b
  rw [count]
  apply Finset.sum_congr rfl
  intro j _
  exact sourceTerm_value v b i j

theorem allBad_value (v b : ℕ) :
    (run allBad (v,b)).val=
      ∑i∈Finset.range (targets v b),∑j∈Finset.range (sources v b),
        if v<pairAmount v b i j then 1 else 0 := by
  rw [allBad,sumProgram_value,targetCount_value]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceBad_value v b i

theorem allBad_zero (v b : ℕ) :
    (run allBad (v,b)).val=0 ↔ UniformWorkspacePlanner.allFits v b=true := by
  rw [allBad_value,UniformWorkspaceSearchMachine.allFits_indices]
  have zero (k : ℕ) : (if v<k then 1 else 0)=0 ↔ k≤v := by
    by_cases h : v<k
    · simp only [h,ite_true,one_ne_zero,false_iff,not_le]
    · simp only [h,ite_false,true_iff]
      exact Nat.le_of_not_gt h
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _),
    Finset.mem_range,zero,UniformWorkspaceSearchMachine.pairFit,decide_eq_true_eq]

end
end ExactFourierCircuits.DFTModelCacheDescriptor
