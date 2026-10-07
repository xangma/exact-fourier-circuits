import UniformNewton
import UniformDAGLowering
import UniformBoundedAssembly

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ExactFourierCircuits.UniformNewtonTableMachine
open UniformMachine UniformAssembly UniformPreparationMachine UniformDAGLowering

/-- The operands below are Nat formulas, independent of all complex values. -/
def powerIndex (j : ℕ) : ℕ := if j = 0 then 1 else 5*j-2
def HIndex (j : ℕ) : ℕ := if j = 0 then 1 else 5*j
def scaleIndex (j : ℕ) : ℕ := if j = 0 then 1 else 5*j+2

def baseRows : List Row := [⟨.add,1,0⟩,⟨.add,3,0⟩,⟨.add,4,0⟩]

def productRows (a j : ℕ) : List Row := [
  ⟨.mul,a+powerIndex j,a⟩,
  ⟨.sub,a+1,a+(5*j+3)⟩,
  ⟨.mul,a+HIndex j,a+(5*j+4)⟩,
  ⟨.mul,a+scaleIndex j,a+powerIndex j⟩,
  ⟨.mul,a+2,a+(5*j+6)⟩]

def inverseRows (r a j : ℕ) : List Row := [
  ⟨.div,a+1,a+HIndex j⟩,
  ⟨.mul,a+HIndex j,a+scaleIndex j⟩,
  ⟨.div,a+1,a+(5*r+3*j+4)⟩]

def rows (r a : ℕ) : List Row := baseRows ++
  (List.range r).flatMap (productRows a) ++ (List.range r).flatMap (inverseRows r a)

theorem powerRef_val (j : ℕ) : (UniformNewton.Preparation.powerRef j).val=powerIndex j := by
  cases j with
  | zero =>  rfl
  | succ j =>  simp [UniformNewton.Preparation.powerRef,powerIndex,
      UniformNewton.Preparation.productCount_formula];omega

theorem HRef_val (j : ℕ) : (UniformNewton.Preparation.HRef j).val=HIndex j := by
  cases j with
  | zero =>  rfl
  | succ j =>  simp [UniformNewton.Preparation.HRef,HIndex,
      UniformNewton.Preparation.productCount_formula];omega

theorem scaleRef_val (j : ℕ) : (UniformNewton.Preparation.scaleRef j).val=scaleIndex j := by
  cases j with
  | zero =>  rfl
  | succ j =>  simp [UniformNewton.Preparation.scaleRef,scaleIndex,
      UniformNewton.Preparation.productCount_formula];omega

theorem compile_product (r a : ℕ) :
    compile (UniformNewton.Preparation.productProgram r) a =
      baseRows ++ (List.range r).flatMap (productRows a) := by
  induction r with
  | zero =>  rfl
  | succ r ih => 
    simp only [UniformNewton.Preparation.productProgram,compile,List.range_succ,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
    simp only [lowerInstruction,Fin.val_castSucc,Fin.val_last,
      UniformNewton.Preparation.rootRef,UniformNewton.Preparation.oneRef,
      UniformNewton.Preparation.minusRef,powerRef_val,HRef_val,scaleRef_val,
      UniformNewton.Preparation.productCount_formula]
    simp [productRows,List.append_assoc]

theorem compile_inverse (r j a : ℕ) (hj : j ≤ r) :
    compile (UniformNewton.Preparation.inverseProgram r j hj) a =
      baseRows ++ (List.range r).flatMap (productRows a) ++
        (List.range j).flatMap (inverseRows r a) := by
  induction j with
  | zero =>  simpa [UniformNewton.Preparation.inverseProgram] using compile_product r a
  | succ j ih => 
    simp only [UniformNewton.Preparation.inverseProgram,compile,ih (by omega),
      List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil]
    simp only [lowerInstruction,Fin.val_castSucc,Fin.val_last,
      UniformNewton.Preparation.inverseOne,UniformNewton.Preparation.inverseH,
      UniformNewton.Preparation.inverseScale,UniformNewton.Preparation.tableRef,
      UniformNewton.Preparation.baseLift,UniformNewton.Preparation.productLift,
      UniformNewton.Preparation.oneRef,Fin.val_castLE,HRef_val,scaleRef_val,
      UniformNewton.Preparation.inverseCount_formula]
    simp [inverseRows,List.append_assoc]

theorem rows_eq_compile (r a : ℕ) : rows r a =
    compile (UniformNewton.Preparation.finalProgram r) a := by
  exact (compile_inverse r r a le_rfl).symm

theorem rows_length (r a : ℕ) : (rows r a).length=8*r+3 := by
  rw [rows_eq_compile,compile_length,UniformNewton.Preparation.inverseCount_formula]
  omega

/- The small straight-line assembler below expands only a fixed number of
instructions. Its final loop code never depends on r or on a complex value. -/
inductive Op where
  | literal (dst value : ℕ)
  | add (dst left right : ℕ)
  | sub (dst left right : ℕ)
  | mul (dst left right : ℕ)
  | putNat (address src : ℕ)
  | literalScalar (dst : ℕ) (value : ℚ)
  | getScalar (dst address : ℕ)
  | putScalar (address src : ℕ)
  deriving DecidableEq

def Op.code : Op → UniformMachine.Instruction
  | .literal d v =>  .natLiteral d v
  | .add d l r =>  .natBinary .add d l r
  | .sub d l r =>  .natBinary .sub d l r
  | .mul d l r =>  .natBinary .mul d l r
  | .putNat a r =>  .storeNat a r
  | .literalScalar d q =>  .scalarLiteral d q
  | .getScalar d a =>  .loadScalar d a
  | .putScalar a r =>  .storeScalar a r

noncomputable section

def Op.apply (o : Op) (s : State) : State := match o with
  | .literal d v =>  writeNat s d v
  | .add d l r =>  writeNat s d (s.natReg l+s.natReg r)
  | .sub d l r =>  writeNat s d (s.natReg l-s.natReg r)
  | .mul d l r =>  writeNat s d (s.natReg l*s.natReg r)
  | .putNat a r =>  {next s with natHeap:=(Function.update s.natHeap
      (s.natReg a) (some (s.natReg r)))}
  | .literalScalar d q =>  writeScalar s d ⟨q,false⟩
  | .getScalar d a =>  writeScalar s d ((s.scalarHeap (s.natReg a)).getD Scalar.zero)
  | .putScalar a r =>  {next s with scalarHeap:=(Function.update s.scalarHeap
      (s.natReg a) (some (s.scalarReg r)))}

def Op.readable (o : Op) (s : State) : Prop := match o with
  | .getScalar _ a =>  (s.scalarHeap (s.natReg a)).isSome=true
  | _ =>  True

def Op.peak (o : Op) (s : State) : ℕ := match o with
  | .literal _ v =>  v
  | .add _ l r =>  s.natReg l+s.natReg r
  | .sub _ l r =>  s.natReg l-s.natReg r
  | .mul _ l r =>  s.natReg l*s.natReg r
  | .putNat a r =>  max (s.natReg a) (s.natReg r)
  | .putScalar a _ =>  s.natReg a
  | _ =>  0

def applyBlock : List Op → State → State
  | [],s =>  s
  | o::b,s =>  applyBlock b (o.apply s)

def readable : List Op → State → Prop
  | [],_ =>  True
  | o::b,s =>  o.readable s ∧ readable b (o.apply s)

def peak : List Op → State → ℕ
  | [],_ =>  0
  | o::b,s =>  max (o.peak s) (peak b (o.apply s))

theorem Op.apply_pc (o : Op) (s : State) : (o.apply s).pc=s.pc+1 := by
  cases o  <;>  rfl

theorem Op.step (o : Op) (p : Program) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hcode:p[s.pc]?=some o.code) (hread:o.readable s) :
    UniformMachine.step p n x s = .running (o.apply s) := by
  cases o  <;>  simp [UniformMachine.step,hcode,Op.code,Op.apply,evalNat]
  case getScalar d a => 
    cases hh:s.scalarHeap (s.natReg a) with
    | none =>  simp [Op.readable,hh] at hread
    | some v =>  simp

theorem Op.apply_bound (o : Op) (B : ℕ) (s : State) (hs:WordBound B s)
    (hp:s.pc+1 ≤ B) (hpeak:o.peak s ≤ B) : WordBound B (o.apply s) := by
  cases o with
  | literal d v =>  exact writeNat_bound B s d v hs hp hpeak
  | add d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | sub d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | mul d l r =>  exact writeNat_bound B s d _ hs hp hpeak
  | putNat a r => 
    refine ⟨hp,hs.2.1,?_,hs.2.2.2⟩
    intro j v hj
    by_cases he:j=s.natReg a
    · simp [Op.apply,next,he] at hj
      subst v
      exact ⟨by simpa [he,Op.peak] using (le_max_left (s.natReg a) (s.natReg r)).trans hpeak,
        by simpa [Op.peak] using (le_max_right (s.natReg a) (s.natReg r)).trans hpeak⟩
    · exact hs.2.2.1 j v (by simpa [Op.apply,next,he] using hj)
  | literalScalar d q =>  exact writeScalar_bound B s d _ hs hp
  | getScalar d a =>  exact writeScalar_bound B s d _ hs hp
  | putScalar a r => 
    refine ⟨hp,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
    intro j v hj
    by_cases he:j=s.natReg a
    · simpa [he,Op.peak] using hpeak
    · exact hs.2.2.2.1 j v (by simpa [Op.apply,next,he] using hj)

def BlockAt (b : List Op) (p : Program) (base : ℕ) : Prop :=
  ∀i,(hi:i < b.length)→p[base+i]?=some (b[i]'hi).code

/-- Every store and every operand calculation is one real charged instruction. -/
theorem block_runs (b : List Op) (p : Program) (base n B : ℕ) (x : Fin n → ℂ)
    (s : State) (hc:BlockAt b p base) (hpc:s.pc=base) (hs:WordBound B s)
    (hcode:base+b.length ≤ B) (hread:readable b s) (hpeak:peak b s ≤ B) :
    BoundedRuns p n x B s b.length (applyBlock b s) := by
  induction b generalizing base s with
  | nil =>  exact .refl hs
  | cons o b ih => 
    have hp:s.pc+1 ≤ B:=by
      simp only [List.length_cons] at hcode
      omega
    have hpk:o.peak s ≤ B:=(le_max_left _ _).trans hpeak
    have hb:=o.apply_bound B s hs hp hpk
    have htail:BlockAt b p (base+1):=by
      intro i hi
      have h:=hc (i+1) (by simpa using hi)
      change p[base+(i+1)]?=some (b[i]'hi).code at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have hr:=ih (base+1) (o.apply s) htail (by rw [Op.apply_pc,hpc]) hb
      (by simp only [List.length_cons] at hcode;omega) hread.2
      ((le_max_right _ _).trans hpeak)
    have hfirst:=hc 0 (by simp)
    change p[base]?=some o.code at hfirst
    exact .next hs (o.step p n x s (by simpa [hpc] using hfirst) hread.1) hr

theorem applyBlock_pc (b : List Op) (s : State) : (applyBlock b s).pc=s.pc+b.length := by
  induction b generalizing s with
  | nil =>  simp [applyBlock]
  | cons o b ih =>  simp [applyBlock,ih,Op.apply_pc];omega

theorem applyBlock_append (b c : List Op) (s : State) :
    applyBlock (b++c) s=applyBlock c (applyBlock b s) := by
  induction b generalizing s with
  | nil =>  rfl
  | cons o b ih =>  exact ih (o.apply s)

theorem applyBlock_outputs (b : List Op) (s : State) :
    (applyBlock b s).outputs=s.outputs ∧ (applyBlock b s).rootOrders=s.rootOrders := by
  induction b generalizing s with
  | nil =>  exact ⟨rfl,rfl⟩
  | cons o b ih => 
    have h:=ih (o.apply s)
    cases o  <;>  exact h

def NatHeapFree : Op → Bool
  | .putNat _ _ =>  false
  | _ =>  true
theorem applyBlock_natHeap (b : List Op) (s : State) (h:∀o∈b,NatHeapFree o=true) :
    (applyBlock b s).natHeap=s.natHeap := by
  induction b generalizing s with
  | nil =>  rfl
  | cons o b ih => 
    have ho:=h o (by simp)
    have hb:∀p∈b,NatHeapFree p=true:=fun p hp=> h p (by simp [hp])
    rw [applyBlock,ih _ hb]
    cases o  <;>  first | rfl | simp [NatHeapFree] at ho

def putWords : ℕ → List ℕ → (ℕ→Option ℕ) → (ℕ→Option ℕ)
  | _,[],heap =>  heap
  | ptr,v::vs,heap =>  putWords (ptr+1) vs (Function.update heap ptr (some v))

theorem putWords_append (ptr : ℕ) (xs ys : List ℕ) (heap : ℕ→Option ℕ) :
    putWords ptr (xs++ys) heap=putWords (ptr+xs.length) ys (putWords ptr xs heap) := by
  induction xs generalizing ptr heap with
  | nil =>  simp [putWords]
  | cons v xs ih => 
    simpa [putWords,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (ptr+1) (Function.update heap ptr (some v))

theorem putWords_before (ptr : ℕ) (xs : List ℕ) (heap : ℕ→Option ℕ) (i : ℕ) (hi:i < ptr) :
    putWords ptr xs heap i=heap i := by
  induction xs generalizing ptr heap with
  | nil =>  rfl
  | cons v xs ih => 
    rw [putWords,ih (ptr+1) _ (by omega)]
    simp [show i≠ptr by omega]

theorem putWords_after (ptr : ℕ) (xs : List ℕ) (heap : ℕ→Option ℕ) (i : ℕ)
    (hi:ptr+xs.length  ≤  i) : putWords ptr xs heap i=heap i := by
  induction xs generalizing ptr heap with
  | nil =>  rfl
  | cons v xs ih => 
    rw [putWords,ih (ptr+1) _ (by
      simp only [List.length_cons] at hi
      omega)]
    simp [show i≠ptr by
      simp only [List.length_cons] at hi
      omega]

theorem putWords_get (ptr : ℕ) (xs : List ℕ) (heap : ℕ→Option ℕ) (i : ℕ) (hi:i < xs.length) :
    putWords ptr xs heap (ptr+i)=xs[i]? := by
  induction xs generalizing ptr heap i with
  | nil =>  simp at hi
  | cons v xs ih => 
    cases i with
    | zero => 
      simp only [putWords,Nat.add_zero,List.getElem?_cons_zero]
      rw [putWords_before _ xs _ ptr (by omega)]
      simp
    | succ i => 
      have hj:i < xs.length:=by simpa using hi
      simpa [putWords,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (ptr+1) (Function.update heap ptr (some v)) i hj

/-- Nat23 is the write pointer; Nat24 is one. All three fields are charged. -/
def emitRow : List Op := [.putNat 23 20,.add 23 23 24,
  .putNat 23 21,.add 23 23 24,.putNat 23 22,.add 23 23 24]

structure Recipe where
  op : FieldOp
  left : ℕ×ℕ
  right : ℕ×ℕ
  deriving DecidableEq

def Recipe.row (q : Recipe) (s : State) : Row :=
  ⟨q.op,s.natReg q.left.1+s.natReg q.left.2,s.natReg q.right.1+s.natReg q.right.2⟩

def Recipe.block (q : Recipe) : List Op := [
  .literal 20 (opcode q.op),.add 21 q.left.1 q.left.2,.add 22 q.right.1 q.right.2]++emitRow

def Recipe.valid (q : Recipe) : Prop :=
  (∀i∈[q.left.1,q.left.2,q.right.1,q.right.2],i≠20∧i≠21∧i≠22∧i≠23)

theorem Recipe.block_length (q : Recipe) : q.block.length=9 := rfl

theorem emitRow_heap (s : State) (h1:s.natReg 24=1) :
    (applyBlock emitRow s).natHeap=putWords (s.natReg 23)
      [s.natReg 20,s.natReg 21,s.natReg 22] s.natHeap := by
  simp [applyBlock,emitRow,Op.apply,writeNat,next,h1,putWords,Nat.add_assoc]

theorem Recipe.block_heap (q : Recipe) (s : State) (h1:s.natReg 24=1) (hq:q.valid) :
    (applyBlock q.block s).natHeap=putWords (s.natReg 23) (bytecode [q.row s]) s.natHeap := by
  have h20:q.right.1≠20∧q.right.2≠20∧q.left.1≠20∧q.left.2≠20 := by
    exact ⟨(hq _ (by simp)).1,(hq _ (by simp)).1,(hq _ (by simp)).1,(hq _ (by simp)).1⟩
  have h21:q.right.1≠21∧q.right.2≠21 :=
    ⟨(hq _ (by simp)).2.1,(hq _ (by simp)).2.1⟩
  simp [Recipe.block,applyBlock,emitRow,Op.apply,writeNat,next,h1,h20.1,h20.2.1,
    h20.2.2.1,h20.2.2.2,h21.1,h21.2,Recipe.row,bytecode,putWords,Nat.add_assoc]

theorem Recipe.block_regs (q : Recipe) (s : State) (i : ℕ)
    (hi:i≠20∧i≠21∧i≠22∧i≠23) : (applyBlock q.block s).natReg i=s.natReg i := by
  simp [Recipe.block,applyBlock,emitRow,Op.apply,writeNat,next,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

theorem Recipe.block_pointer (q : Recipe) (s : State) (h1:s.natReg 24=1) :
    (applyBlock q.block s).natReg 23=s.natReg 23+3 := by
  simp [Recipe.block,applyBlock,emitRow,Op.apply,writeNat,next,h1]

def recipesBlock (qs : List Recipe) : List Op := qs.flatMap Recipe.block

def baseRecipes : List Recipe := [⟨.add,(24,30),(30,30)⟩,
  ⟨.add,(31,30),(30,30)⟩,⟨.add,(26,30),(30,30)⟩]

def productRecipes : List Recipe := [⟨.mul,(35,30),(17,30)⟩,
  ⟨.sub,(17,24),(34,30)⟩,⟨.mul,(36,30),(34,24)⟩,
  ⟨.mul,(37,30),(35,30)⟩,⟨.mul,(17,25),(34,31)⟩]

def inverseRecipes : List Recipe := [⟨.div,(17,24),(36,30)⟩,
  ⟨.mul,(36,30),(37,30)⟩,⟨.div,(17,24),(34,24)⟩]

theorem recipesBlock_length (qs : List Recipe) : (recipesBlock qs).length=9*qs.length := by
  induction qs with
  | nil =>  rfl
  | cons q qs ih =>  simp [recipesBlock,Recipe.block_length];omega

@[simp] theorem recipesBlock_regs (qs : List Recipe) (s : State) (i : ℕ)
    (hi:i≠20∧i≠21∧i≠22∧i≠23) :
    (applyBlock (recipesBlock qs) s).natReg i=s.natReg i := by
  induction qs generalizing s with
  | nil =>  rfl
  | cons q qs ih => 
    change (applyBlock (q.block++recipesBlock qs) s).natReg i=s.natReg i
    rw [applyBlock_append,ih,Recipe.block_regs _ _ _ hi]

theorem recipesBlock_pointer (qs : List Recipe) (s : State) (h1:s.natReg 24=1) :
    (applyBlock (recipesBlock qs) s).natReg 23=s.natReg 23+3*qs.length := by
  induction qs generalizing s with
  | nil =>  simp [recipesBlock,applyBlock]
  | cons q qs ih => 
    change (applyBlock (q.block++recipesBlock qs) s).natReg 23=_
    rw [applyBlock_append,ih _
      (by rw [Recipe.block_regs q s 24 (by decide)];exact h1),Recipe.block_pointer q s h1]
    simp only [List.length_cons];omega

theorem recipesBlock_heap (qs : List Recipe) (s : State) (h1:s.natReg 24=1)
    (hqs:∀q∈qs,q.valid) :
    (applyBlock (recipesBlock qs) s).natHeap=
      putWords (s.natReg 23) (bytecode (qs.map (fun q=> q.row s))) s.natHeap := by
  induction qs generalizing s with
  | nil =>  rfl
  | cons q qs ih => 
    have hq:=hqs q (by simp)
    have ht:∀p∈qs,p.valid:=fun p hp=> hqs p (by simp [hp])
    have hrow:qs.map (fun p=> p.row (applyBlock q.block s))=qs.map (fun p=> p.row s) := by
      apply List.map_congr_left
      intro p hp
      have hv:=ht p hp
      have hr (i:ℕ) (hi:i∈[p.left.1,p.left.2,p.right.1,p.right.2]) :=
        Recipe.block_regs q s i (hv i hi)
      simp [Recipe.row,hr p.left.1 (by simp),hr p.left.2 (by simp),
        hr p.right.1 (by simp),hr p.right.2 (by simp)]
    change (applyBlock (q.block++recipesBlock qs) s).natHeap=_
    rw [applyBlock_append,
      ih _ (by rw [Recipe.block_regs q s 24 (by decide)];exact h1) ht,hrow,
      Recipe.block_heap q s h1 hq,Recipe.block_pointer q s h1]
    exact (putWords_append (s.natReg 23)
      [opcode q.op,(q.row s).left,(q.row s).right]
      (bytecode (qs.map (fun p=> p.row s))) s.natHeap).symm

/-- Five printed product rows, then maintained shared prior-node addresses. -/
def productBlock : List Op := recipesBlock productRecipes ++ [
  .add 35 34 30,.add 36 34 25,.add 37 34 26,.add 34 34 27,.add 28 28 24]

/-- Three inverse rows. The new old-H/scale addresses are computed from j. -/
def inverseBlock : List Op := recipesBlock inverseRecipes ++ [
  .add 28 28 24,.mul 36 28 27,.add 36 36 17,.add 37 36 25,.add 34 34 31]

def startBlock : List Op := [.literal 24 1,.literal 25 2,.literal 26 4,
  .literal 27 5,.literal 30 0,.literal 31 3,.literal 23 0,.literal 28 0,
  .add 34 17 31,.add 35 17 24,.add 36 17 24,.add 37 17 24] ++ recipesBlock baseRecipes

def switchBlock : List Op := [.literal 28 0,.add 35 17 24,.add 36 17 24,
  .add 37 17 24,.mul 34 16 27,.add 34 34 31,.add 34 34 17]

def productPC : ℕ := startBlock.length
def switchPC : ℕ := productPC+1+productBlock.length+1
def inversePC : ℕ := switchPC+switchBlock.length
def exitPC : ℕ := inversePC+1+inverseBlock.length+1

/-- One literal program, independent of r and of all field values. Nat16=r,
Nat17=result base a. Only Nat heap [0,3*(8*r+3)) is allocated here. -/
def tableProgram : Program := startBlock.map Op.code ++
  [.branchLT 28 16 (productPC+1) switchPC] ++ productBlock.map Op.code ++ [.jump productPC] ++
  switchBlock.map Op.code ++ [.branchLT 28 16 (inversePC+1) exitPC] ++
  inverseBlock.map Op.code ++ [.jump inversePC,.halt]

theorem tableProgram_length : tableProgram.length=133 := rfl
theorem productPC_val : productPC=39 := rfl
theorem switchPC_val : switchPC=91 := rfl
theorem inversePC_val : inversePC=98 := rfl
theorem exitPC_val : exitPC=132 := rfl

structure Constants (r a : ℕ) (s : State) : Prop where
  order : s.natReg 16=r
  base : s.natReg 17=a
  one : s.natReg 24=1
  two : s.natReg 25=2
  four : s.natReg 26=4
  five : s.natReg 27=5
  zero : s.natReg 30=0
  three : s.natReg 31=3

structure ProductData (a j : ℕ) (s : State) : Prop where
  index : s.natReg 28=j
  pointer : s.natReg 23=9+15*j
  next : s.natReg 34=a+(5*j+3)
  power : s.natReg 35=a+powerIndex j
  H : s.natReg 36=a+HIndex j
  scale : s.natReg 37=a+scaleIndex j

structure InverseData (r a j : ℕ) (s : State) : Prop where
  index : s.natReg 28=j
  pointer : s.natReg 23=9+15*r+9*j
  next : s.natReg 34=a+(5*r+3*j+3)
  H : s.natReg 36=a+HIndex j
  scale : s.natReg 37=a+scaleIndex j

theorem start_heap (s : State) :
    (applyBlock startBlock s).natHeap=putWords 0 (bytecode baseRows) s.natHeap := by
  rw [startBlock,applyBlock_append,recipesBlock_heap _ _ (by
    simp [applyBlock,Op.apply,writeNat,next]) (by simp [baseRecipes,Recipe.valid])]
  simp [baseRecipes,Recipe.row,applyBlock,Op.apply,writeNat,next,bytecode,baseRows]

theorem start_data (r a : ℕ) (s : State) (hr:s.natReg 16=r) (ha:s.natReg 17=a) :
    Constants r a (applyBlock startBlock s) ∧ ProductData a 0 (applyBlock startBlock s) := by
  constructor
  · constructor  <;>  simp [startBlock,recipesBlock_regs,
      applyBlock,Op.apply,writeNat,next,hr,ha]
  · constructor
    · rw [startBlock,applyBlock_append,recipesBlock_regs _ _ 28 (by decide)]
      simp [applyBlock,Op.apply,writeNat,next]
    · rw [startBlock,applyBlock_append,recipesBlock_pointer _ _ (by
        simp [applyBlock,Op.apply,writeNat,next])]
      simp [applyBlock,Op.apply,writeNat,next,baseRecipes]
    all_goals
      rw [startBlock,applyBlock_append,recipesBlock_regs]
      first | decide | simp [applyBlock,Op.apply,writeNat,next,ha,powerIndex,HIndex,scaleIndex]
    all_goals decide

theorem product_heap (r a j : ℕ) (s : State) (hc:Constants r a s) (hd:ProductData a j s) :
    (applyBlock productBlock s).natHeap=putWords (9+15*j) (bytecode (productRows a j)) s.natHeap := by
  rw [productBlock,applyBlock_append]
  rw [applyBlock_natHeap _ _ (by simp [NatHeapFree])]
  rw [recipesBlock_heap _ _ hc.one (by simp [productRecipes,Recipe.valid])]
  simp [productRecipes,Recipe.row,productRows,hc.base,hc.one,hc.two,hc.three,hc.zero,
    hd.power,hd.H,hd.scale,hd.next,hd.pointer,Nat.add_assoc]

theorem product_constants (r a : ℕ) (s : State) (hc:Constants r a s) :
    Constants r a (applyBlock productBlock s) := by
  constructor  <;>  simp [productBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
    recipesBlock_regs,hc.order,hc.base,hc.one,hc.two,hc.four,
    hc.five,hc.zero,hc.three]

theorem product_data (r a j : ℕ) (s : State) (hc:Constants r a s) (hd:ProductData a j s) :
    ProductData a (j+1) (applyBlock productBlock s) := by
  constructor
  · simp [productBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
      recipesBlock_regs,hd.index,hc.one]
  · rw [productBlock,applyBlock_append]
    change (applyBlock (recipesBlock productRecipes) s).natReg 23=_
    rw [recipesBlock_pointer _ _ hc.one,hd.pointer]
    simp [productRecipes];omega
  all_goals
    simp [productBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
      recipesBlock_regs,hd.next,hc.one,hc.two,hc.four,hc.five,
      hc.zero,powerIndex,HIndex,scaleIndex]
    omega

theorem switch_data (r a : ℕ) (s : State) (hc:Constants r a s) (hp:s.natReg 23=9+15*r) :
    Constants r a (applyBlock switchBlock s) ∧ InverseData r a 0 (applyBlock switchBlock s) := by
  constructor
  · constructor  <;>  simp [switchBlock,applyBlock,Op.apply,writeNat,next,
      hc.order,hc.base,hc.one,hc.two,hc.four,hc.five,hc.zero,hc.three]
  · constructor  <;>  simp [switchBlock,applyBlock,Op.apply,writeNat,next,
      hc.order,hc.base,hc.one,hc.five,hc.three,hp,HIndex,scaleIndex]
    all_goals omega

theorem inverse_heap (r a j : ℕ) (s : State) (hc:Constants r a s) (hd:InverseData r a j s) :
    (applyBlock inverseBlock s).natHeap=putWords (9+15*r+9*j)
      (bytecode (inverseRows r a j)) s.natHeap := by
  rw [inverseBlock,applyBlock_append]
  rw [applyBlock_natHeap _ _ (by simp [NatHeapFree])]
  rw [recipesBlock_heap _ _ hc.one (by simp [inverseRecipes,Recipe.valid])]
  simp [inverseRecipes,Recipe.row,inverseRows,hc.base,hc.one,hc.zero,
    hd.H,hd.scale,hd.next,hd.pointer,Nat.add_assoc]

theorem inverse_constants (r a : ℕ) (s : State) (hc:Constants r a s) :
    Constants r a (applyBlock inverseBlock s) := by
  constructor  <;>  simp [inverseBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
    recipesBlock_regs,hc.order,hc.base,hc.one,hc.two,hc.four,
    hc.five,hc.zero,hc.three]

theorem inverse_data (r a j : ℕ) (s : State) (hc:Constants r a s) (hd:InverseData r a j s) :
    InverseData r a (j+1) (applyBlock inverseBlock s) := by
  constructor
  · simp [inverseBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
      recipesBlock_regs,hd.index,hc.one]
  · rw [inverseBlock,applyBlock_append]
    change (applyBlock (recipesBlock inverseRecipes) s).natReg 23=_
    rw [recipesBlock_pointer _ _ hc.one,hd.pointer]
    simp [inverseRecipes];omega
  all_goals
    simp [inverseBlock,applyBlock_append,applyBlock,Op.apply,writeNat,next,
      recipesBlock_regs,hd.next,hd.index,hc.base,hc.one,hc.two,
      hc.five,hc.three,HIndex,scaleIndex]
    omega

theorem start_at : BlockAt startBlock tableProgram 0 := by
  intro i hi
  change i < 39 at hi
  interval_cases i  <;>  rfl
theorem product_at : BlockAt productBlock tableProgram (productPC+1) := by
  intro i hi
  change i < 50 at hi
  interval_cases i  <;>  rfl
theorem switch_at : BlockAt switchBlock tableProgram switchPC := by
  intro i hi
  change i < 7 at hi
  interval_cases i  <;>  rfl
theorem inverse_at : BlockAt inverseBlock tableProgram (inversePC+1) := by
  intro i hi
  change i < 32 at hi
  interval_cases i  <;>  rfl

theorem index_bounds (j : ℕ) :
    powerIndex j ≤ 5*j+1 ∧ HIndex j ≤ 5*j+1 ∧ scaleIndex j ≤ 5*j+2 := by
  simp only [powerIndex,HIndex,scaleIndex]
  split_ifs  <;>  omega

theorem start_peak (r a B : ℕ) (s : State) (hr:s.natReg 16=r) (ha:s.natReg 17=a)
    (hB:a+24*r+200 ≤ B) : peak startBlock s ≤ B := by
  simp [peak,startBlock,recipesBlock,baseRecipes,Recipe.block,emitRow,Op.peak,Op.apply,
    writeNat,next,ha,opcode]
  omega

theorem product_peak (r a j B : ℕ) (s : State) (hc:Constants r a s) (hd:ProductData a j s)
    (hj:j < r) (hB:a+24*r+200 ≤ B) : peak productBlock s ≤ B := by
  have hb:=index_bounds j
  simp [peak,productBlock,recipesBlock,productRecipes,Recipe.block,emitRow,Op.peak,Op.apply,
    writeNat,next,hc.base,hc.one,hc.two,hc.four,hc.five,hc.zero,hc.three,
    hd.index,hd.pointer,hd.next,hd.power,hd.H,hd.scale,opcode]
  omega

theorem switch_peak (r a B : ℕ) (s : State) (hc:Constants r a s)
    (hB:a+24*r+200 ≤ B) : peak switchBlock s ≤ B := by
  simp [peak,switchBlock,Op.peak,Op.apply,writeNat,next,hc.order,hc.base,hc.one,
    hc.five,hc.three]
  omega

theorem inverse_peak (r a j B : ℕ) (s : State) (hc:Constants r a s) (hd:InverseData r a j s)
    (hj:j < r) (hB:a+24*r+200 ≤ B) : peak inverseBlock s ≤ B := by
  have hb:=index_bounds j
  simp [peak,inverseBlock,recipesBlock,inverseRecipes,Recipe.block,emitRow,Op.peak,Op.apply,
    writeNat,next,hc.base,hc.one,hc.two,hc.five,hc.zero,hc.three,
    hd.index,hd.pointer,hd.next,hd.H,hd.scale,opcode]
  omega

theorem Constants.withPC {r a pc : ℕ} {s : State} (h:Constants r a s) :
    Constants r a {s with pc:=pc} := by cases h;constructor  <;>  assumption
theorem ProductData.withPC {a j pc : ℕ} {s : State} (h:ProductData a j s) :
    ProductData a j {s with pc:=pc} := by cases h;constructor  <;>  assumption
theorem InverseData.withPC {r a j pc : ℕ} {s : State} (h:InverseData r a j s) :
    InverseData r a j {s with pc:=pc} := by cases h;constructor  <;>  assumption

theorem table_product_branch : tableProgram[39]?=some (.branchLT 28 16 40 91) := rfl
theorem table_product_jump : tableProgram[90]?=some (.jump 39) := rfl
theorem table_inverse_branch : tableProgram[98]?=some (.branchLT 28 16 99 132) := rfl
theorem table_inverse_jump : tableProgram[131]?=some (.jump 98) := rfl
theorem table_halt : tableProgram[132]?=some .halt := rfl

def productEnd (s : State) : State :=
  {applyBlock productBlock {s with pc:=productPC+1} with pc:=productPC}
def inverseEnd (s : State) : State :=
  {applyBlock inverseBlock {s with pc:=inversePC+1} with pc:=inversePC}

theorem product_iteration (n : ℕ) (x : Fin n → ℂ) (r a j B : ℕ) (s : State)
    (hc:Constants r a s) (hd:ProductData a j s) (hp:s.pc=productPC)
    (hj:j < r) (hB:a+24*r+200 ≤ B) (hs:WordBound B s) :
    BoundedRuns tableProgram n x B s 52 (productEnd s) ∧
    Constants r a (productEnd s) ∧ ProductData a (j+1) (productEnd s) ∧
    (productEnd s).natHeap=putWords (9+15*j) (bytecode (productRows a j)) s.natHeap := by
  let e:State:={s with pc:=productPC+1}
  have he:WordBound B e:=changePC_bound B s _ hs (by rw [productPC_val];omega)
  have hrun:=block_runs productBlock tableProgram (productPC+1) n B x e product_at rfl he
    (by change 40+50 ≤ B;omega) (by simp [readable,productBlock,recipesBlock,
      productRecipes,Recipe.block,emitRow,Op.readable])
    (product_peak r a j B e hc.withPC hd.withPC hj hB)
  have hfinal:WordBound B (productEnd s):=changePC_bound B _ _ hrun.final_bound
    (by rw [productPC_val];omega)
  have hg:BoundedRuns tableProgram n x B (applyBlock productBlock e) 1 (productEnd s) := by
    refine .next hrun.final_bound ?_ (.refl hfinal)
    have hpc:(applyBlock productBlock e).pc=90:=by
      rw [applyBlock_pc]
      rfl
    rw [step,hpc,table_product_jump]
    rfl
  have hb:BoundedRuns tableProgram n x B s 1 e := by
    refine .next hs ?_ (.refl he)
    rw [step,hp,productPC_val,table_product_branch]
    simp [hc.order,hd.index,hj,e,productPC_val]
  refine ⟨?_,(product_constants r a e hc.withPC).withPC,
    (product_data r a j e hc.withPC hd.withPC).withPC,
    product_heap r a j e hc.withPC hd.withPC⟩
  convert hb.trans (hrun.trans hg) using 1; rfl

theorem inverse_iteration (n : ℕ) (x : Fin n → ℂ) (r a j B : ℕ) (s : State)
    (hc:Constants r a s) (hd:InverseData r a j s) (hp:s.pc=inversePC)
    (hj:j < r) (hB:a+24*r+200 ≤ B) (hs:WordBound B s) :
    BoundedRuns tableProgram n x B s 34 (inverseEnd s) ∧
    Constants r a (inverseEnd s) ∧ InverseData r a (j+1) (inverseEnd s) ∧
    (inverseEnd s).natHeap=putWords (9+15*r+9*j) (bytecode (inverseRows r a j)) s.natHeap := by
  let e:State:={s with pc:=inversePC+1}
  have he:WordBound B e:=changePC_bound B s _ hs (by rw [inversePC_val];omega)
  have hrun:=block_runs inverseBlock tableProgram (inversePC+1) n B x e inverse_at rfl he
    (by change 99+32 ≤ B;omega) (by simp [readable,inverseBlock,recipesBlock,
      inverseRecipes,Recipe.block,emitRow,Op.readable])
    (inverse_peak r a j B e hc.withPC hd.withPC hj hB)
  have hfinal:WordBound B (inverseEnd s):=changePC_bound B _ _ hrun.final_bound
    (by rw [inversePC_val];omega)
  have hg:BoundedRuns tableProgram n x B (applyBlock inverseBlock e) 1 (inverseEnd s) := by
    refine .next hrun.final_bound ?_ (.refl hfinal)
    have hpc:(applyBlock inverseBlock e).pc=131:=by rw [applyBlock_pc];rfl
    rw [step,hpc,table_inverse_jump]
    rfl
  have hb:BoundedRuns tableProgram n x B s 1 e := by
    refine .next hs ?_ (.refl he)
    rw [step,hp,inversePC_val,table_inverse_branch]
    simp [hc.order,hd.index,hj,e,inversePC_val]
  refine ⟨?_,(inverse_constants r a e hc.withPC).withPC,
    (inverse_data r a j e hc.withPC hd.withPC).withPC,
    inverse_heap r a j e hc.withPC hd.withPC⟩
  convert hb.trans (hrun.trans hg) using 1; rfl

theorem bytecode_append (xs ys : List Row) : bytecode (xs++ys)=bytecode xs++bytecode ys := by
  induction xs with
  | nil =>  rfl
  | cons q xs ih =>  simp [bytecode,ih]

def productBytes (a j : ℕ) : List ℕ := bytecode
  (baseRows++(List.range j).flatMap (productRows a))
def inverseBytes (r a j : ℕ) : List ℕ := bytecode
  (baseRows++(List.range r).flatMap (productRows a)++
    (List.range j).flatMap (inverseRows r a))

theorem productBytes_length (a j : ℕ) : (productBytes a j).length=9+15*j := by
  rw [productBytes,bytecode_length]
  have h : ((List.range j).flatMap (productRows a)).length=5*j := by
    induction j with
    | zero =>  rfl
    | succ j ih =>  simp [List.range_succ,List.flatMap_append,productRows,ih];omega
  simp [h,baseRows];omega

theorem inverseBytes_length (r a j : ℕ) : (inverseBytes r a j).length=9+15*r+9*j := by
  have h : ((List.range j).flatMap (inverseRows r a)).length=3*j := by
    induction j with
    | zero =>  rfl
    | succ j ih =>  simp [List.range_succ,List.flatMap_append,inverseRows,ih];omega
  change (bytecode ((baseRows++(List.range r).flatMap (productRows a))++_)).length=_
  rw [bytecode_append,List.length_append,bytecode_length ((List.range j).flatMap (inverseRows r a))]
  rw [h]
  change (productBytes a r).length+3*(3*j)=_
  rw [productBytes_length];omega

theorem productBytes_succ (a j : ℕ) : productBytes a (j+1)=
    productBytes a j++bytecode (productRows a j) := by
  simp [productBytes,List.range_succ,List.flatMap_append,List.append_assoc,bytecode_append]

theorem inverseBytes_succ (r a j : ℕ) : inverseBytes r a (j+1)=
    inverseBytes r a j++bytecode (inverseRows r a j) := by
  simp [inverseBytes,List.range_succ,List.flatMap_append,List.append_assoc,bytecode_append]

def HeapFree : Op → Bool
  | .putScalar _ _ =>  false
  | _ =>  true

theorem applyBlock_scalarHeap (b : List Op) (s : State) (h:∀o∈b,HeapFree o=true) :
    (applyBlock b s).scalarHeap=s.scalarHeap := by
  induction b generalizing s with
  | nil =>  rfl
  | cons o b ih => 
    have ho:=h o (by simp)
    have hb:∀p∈b,HeapFree p=true:=fun p hp=> h p (by simp [hp])
    rw [applyBlock,ih _ hb]
    cases o  <;>  first | rfl | simp [HeapFree] at ho

def Frame (s u : State) : Prop :=
  u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders

theorem block_frame (b : List Op) (s : State) (h:∀o∈b,HeapFree o=true) :
    Frame s (applyBlock b s) :=
  ⟨applyBlock_scalarHeap b s h,(applyBlock_outputs b s).1,(applyBlock_outputs b s).2⟩

theorem product_frame (s : State) : Frame s (productEnd s) := by
  exact block_frame productBlock {s with pc:=productPC+1}
    (by simp [productBlock,recipesBlock,productRecipes,Recipe.block,emitRow,HeapFree])
theorem inverse_frame (s : State) : Frame s (inverseEnd s) := by
  exact block_frame inverseBlock {s with pc:=inversePC+1}
    (by simp [inverseBlock,recipesBlock,inverseRecipes,Recipe.block,emitRow,HeapFree])

theorem Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.trans h.2.2⟩

theorem product_loop (n : ℕ) (x : Fin n → ℂ) (r a B fuel j : ℕ) (s : State)
    (heap : ℕ→Option ℕ) (hj:j+fuel=r) (hc:Constants r a s) (hd:ProductData a j s)
    (hp:s.pc=productPC) (hw:s.natHeap=putWords 0 (productBytes a j) heap)
    (hB:a+24*r+200 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns tableProgram n x B s (52*fuel) u ∧ Constants r a u ∧ ProductData a r u ∧
    u.pc=productPC ∧ u.natHeap=putWords 0 (productBytes a r) heap ∧ Frame s u := by
  induction fuel generalizing j s with
  | zero => 
    have he:j=r:=by omega
    subst j
    exact ⟨s,.refl hs,hc,hd,hp,hw,rfl,rfl,rfl⟩
  | succ fuel ih => 
    have hjr:j < r:=by omega
    obtain ⟨hrun,hc',hd',hw'⟩:=product_iteration n x r a j B s hc hd hp hjr hB hs
    have hw'':(productEnd s).natHeap=putWords 0 (productBytes a (j+1)) heap := by
      rw [hw',hw,productBytes_succ,putWords_append,productBytes_length]
      simp
    obtain ⟨u,hu,hcu,hdu,hpu,hwu,hfu⟩:=ih (j+1) (productEnd s) (by omega)
      hc' hd' rfl hw'' hrun.final_bound
    refine ⟨u,?_,hcu,hdu,hpu,hwu,(product_frame s).trans hfu⟩
    convert hrun.trans hu using 1; omega

theorem inverse_loop (n : ℕ) (x : Fin n → ℂ) (r a B fuel j : ℕ) (s : State)
    (heap : ℕ→Option ℕ) (hj:j+fuel=r) (hc:Constants r a s) (hd:InverseData r a j s)
    (hp:s.pc=inversePC) (hw:s.natHeap=putWords 0 (inverseBytes r a j) heap)
    (hB:a+24*r+200 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedRuns tableProgram n x B s (34*fuel) u ∧ Constants r a u ∧ InverseData r a r u ∧
    u.pc=inversePC ∧ u.natHeap=putWords 0 (inverseBytes r a r) heap ∧ Frame s u := by
  induction fuel generalizing j s with
  | zero => 
    have he:j=r:=by omega
    subst j
    exact ⟨s,.refl hs,hc,hd,hp,hw,rfl,rfl,rfl⟩
  | succ fuel ih => 
    have hjr:j < r:=by omega
    obtain ⟨hrun,hc',hd',hw'⟩:=inverse_iteration n x r a j B s hc hd hp hjr hB hs
    have hw'':(inverseEnd s).natHeap=putWords 0 (inverseBytes r a (j+1)) heap := by
      rw [hw',hw,inverseBytes_succ,putWords_append,inverseBytes_length]
      simp
    obtain ⟨u,hu,hcu,hdu,hpu,hwu,hfu⟩:=ih (j+1) (inverseEnd s) (by omega)
      hc' hd' rfl hw'' hrun.final_bound
    refine ⟨u,?_,hcu,hdu,hpu,hwu,(inverse_frame s).trans hfu⟩
    convert hrun.trans hu using 1; omega

/-- Actual fixed RAM table production. There is no NatTable premise. -/
theorem table_execution (n : ℕ) (x : Fin n → ℂ) (r a B : ℕ) (s : State)
    (hp:s.pc=0) (hr:s.natReg 16=r) (ha:s.natReg 17=a)
    (hB:a+24*r+200 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution tableProgram n x B s (86*r+49) u ∧
    u.natHeap=putWords 0 (bytecode (rows r a)) s.natHeap ∧
    NatTable (compile (UniformNewton.Preparation.finalProgram r) a) u ∧ Frame s u ∧ Constants r a u := by
  have hstart:=block_runs startBlock tableProgram 0 n B x s start_at hp hs
    (by change 0+39 ≤ B;omega) (by simp [readable,startBlock,recipesBlock,baseRecipes,
      Recipe.block,emitRow,Op.readable]) (start_peak r a B s hr ha hB)
  obtain ⟨hc,hd⟩:=start_data r a s hr ha
  have hpc:(applyBlock startBlock s).pc=productPC:=by rw [applyBlock_pc,hp];rfl
  obtain ⟨p,hprod,hcp,hdp,hpp,hwp,hfp⟩:=product_loop n x r a B r 0 (applyBlock startBlock s)
    s.natHeap (by omega) hc hd hpc (start_heap s) hB hstart.final_bound
  let entered:State:={p with pc:=switchPC}
  have hentered:WordBound B entered:=changePC_bound B _ _ hprod.final_bound
    (by rw [switchPC_val];omega)
  have branch:BoundedRuns tableProgram n x B p 1 entered:=by
    refine .next hprod.final_bound ?_ (.refl hentered)
    rw [step,hpp,productPC_val,table_product_branch]
    simp [entered,switchPC_val,hcp.order,hdp.index]
  have hswitch:=block_runs switchBlock tableProgram switchPC n B x entered switch_at rfl
    hentered (by change 91+7 ≤ B;omega) (by simp [readable,switchBlock,Op.readable])
    (switch_peak r a B entered hcp.withPC hB)
  obtain ⟨hci,hdi⟩:=switch_data r a entered hcp.withPC hdp.pointer
  have hipc:(applyBlock switchBlock entered).pc=inversePC:=by rw [applyBlock_pc];rfl
  have hiheap:(applyBlock switchBlock entered).natHeap=putWords 0 (inverseBytes r a 0) s.natHeap := by
    simpa [switchBlock,applyBlock,Op.apply,writeNat,next,inverseBytes,productBytes] using hwp
  obtain ⟨u,hinv,hcu,hdu,hpu,hwu,hfu⟩:=inverse_loop n x r a B r 0
    (applyBlock switchBlock entered) s.natHeap (by omega) hci hdi hipc hiheap hB hswitch.final_bound
  have hex:BoundedExecution tableProgram n x B u 2 {u with pc:=exitPC} := by
    have hb:=changePC_bound B u exitPC hinv.final_bound (by rw [exitPC_val];omega)
    refine .next hinv.final_bound ?_ (.halt hb ?_)
    · rw [step,hpu,inversePC_val,table_inverse_branch]
      simp [hcu.order,hdu.index,exitPC_val]
    · simp only [UniformMachine.step,exitPC_val,table_halt]
  have hall:=hstart.trans (hprod.trans (branch.trans (hswitch.trans hinv)))
  have hwfinal:{u with pc:=exitPC}.natHeap=putWords 0 (bytecode (rows r a)) s.natHeap:=by
    exact hwu
  refine ⟨{u with pc:=exitPC},?_,hwfinal,?_,?_,hcu.withPC⟩
  · convert hall.executes hex using 1
    change 86*r+49=39+(52*r+(1+(7+34*r)))+2
    omega
  · intro j q hq
    rw [←rows_eq_compile] at hq
    obtain ⟨ho,hl,hr⟩:=bytecode_get (rows r a) j q hq
    have hj:j < (rows r a).length:=(List.getElem?_eq_some_iff.1 hq).choose
    rw [hwfinal]
    have hget (i:ℕ) (hi:i < 3*(rows r a).length) :
        putWords 0 (bytecode (rows r a)) s.natHeap i=(bytecode (rows r a))[i]? := by
      simpa only [Nat.zero_add] using putWords_get 0 (bytecode (rows r a)) s.natHeap i
        (by rw [bytecode_length];exact hi)
    exact ⟨(hget (3*j) (by omega)).trans ho,
      (hget (3*j+1) (by omega)).trans hl,(hget (3*j+2) (by omega)).trans hr⟩
  · have hfstart:=block_frame startBlock s (by simp [startBlock,recipesBlock,baseRecipes,
      Recipe.block,emitRow,HeapFree])
    have hfswitch:=block_frame switchBlock entered (by simp [switchBlock,HeapFree])
    exact hfstart.trans (hfp.trans (hfswitch.trans hfu))

theorem product_literals (r : ℕ) (s : State)
    (h1:s.scalarHeap 3=some ⟨1,false⟩) (hm:s.scalarHeap 4=some ⟨-1,false⟩) :
    LiteralsReady (UniformNewton.Preparation.productProgram r) s := by
  induction r with
  | zero =>  simpa [UniformNewton.Preparation.productProgram,LiteralsReady,LiteralReady] using ⟨h1,hm⟩
  | succ r ih =>  simpa [UniformNewton.Preparation.productProgram,LiteralsReady,LiteralReady] using ih

theorem inverse_literals (r j : ℕ) (hj:j ≤ r) (s : State)
    (h1:s.scalarHeap 3=some ⟨1,false⟩) (hm:s.scalarHeap 4=some ⟨-1,false⟩) :
    LiteralsReady (UniformNewton.Preparation.inverseProgram r j hj) s := by
  induction j with
  | zero =>  exact product_literals r s h1 hm
  | succ j ih => 
    simpa [UniformNewton.Preparation.inverseProgram,LiteralsReady,LiteralReady] using ih (by omega)

def saveBlock : List Op := (List.range 6).flatMap (fun j=> [
  .literal 41 j,.add 42 19 41,.getScalar 3 41,.putScalar 42 3])
def restoreBlock : List Op := (List.range 6).flatMap (fun j=> [
  .literal 41 j,.add 42 19 41,.getScalar 3 42,.putScalar 41 3])
def literalBlock : List Op := [
  .literal 40 0,.literalScalar 3 0,.putScalar 40 3,
  .getScalar 3 18,.literal 40 1,.putScalar 40 3,
  .literalScalar 3 1,.literal 40 3,.putScalar 40 3,
  .literalScalar 3 (-1),.literal 40 4,.putScalar 40 3]

def setupBlock : List Op := saveBlock++literalBlock
def interpreterStart : List Op := [.literal 43 8,.mul 0 16 43,.add 0 0 31,.add 9 17 30]

def program : Program := setupBlock.map Op.code ++
  tableProgram.map (relocate 36 169) ++ interpreterStart.map Op.code ++
  UniformPreparationMachine.program.map (relocate 173 204) ++ restoreBlock.map Op.code ++ [.halt]

theorem program_length : program.length=229 := rfl
theorem setup_at : BlockAt setupBlock program 0 := by
  intro i hi;change i < 36 at hi;interval_cases i  <;>  rfl
theorem table_code : CodeAt tableProgram program 36 169 := by
  intro i hi;change i < 133 at hi;interval_cases i  <;>  rfl
theorem interpreter_start_at : BlockAt interpreterStart program 169 := by
  intro i hi;change i < 4 at hi;interval_cases i  <;>  rfl
theorem interpreter_code : CodeAt UniformPreparationMachine.program program 173 204 := by
  intro i hi;change i < 31 at hi;interval_cases i  <;>  rfl
theorem restore_at : BlockAt restoreBlock program 204 := by
  intro i hi;change i < 24 at hi;interval_cases i  <;>  rfl
theorem program_halt : program[228]?=some .halt := rfl

def Bank (bank : Fin 6→Scalar) (s : State) : Prop :=
  ∀j:Fin 6,s.scalarHeap j.val=some (bank j)
def SavedBank (scratch : ℕ) (bank : Fin 6→Scalar) (s : State) : Prop :=
  ∀j:Fin 6,s.scalarHeap (scratch+j.val)=some (bank j)

theorem save_readable (scratch : ℕ) (bank : Fin 6→Scalar) (s : State)
    (hb:Bank bank s) (hs:s.natReg 19=scratch) (hdis:6 ≤ scratch) : readable saveBlock s := by
  have h0:=hb 0;have h1:=hb 1;have h2:=hb 2;have h3:=hb 3;have h4:=hb 4;have h5:=hb 5
  norm_num at h0 h1 h2 h3 h4 h5
  simp (disch:=omega) [readable,saveBlock,List.range_succ,Op.readable,Op.apply,writeNat,writeScalar,next,
    hs,h0,h1,h2,h3,h4,h5]

theorem save_peak (scratch B : ℕ) (s : State) (hs:s.natReg 19=scratch)
    (hB:scratch+6 ≤ B) : peak saveBlock s ≤ B := by
  simp [peak,saveBlock,List.range_succ,Op.peak,Op.apply,writeNat,writeScalar,next,hs]
  omega

theorem save_bank (scratch : ℕ) (bank : Fin 6→Scalar) (s : State)
    (hb:Bank bank s) (hs:s.natReg 19=scratch) (hdis:6 ≤ scratch) :
    SavedBank scratch bank (applyBlock saveBlock s) := by
  have h0:=hb 0;have h1:=hb 1;have h2:=hb 2;have h3:=hb 3;have h4:=hb 4;have h5:=hb 5
  norm_num at h0 h1 h2 h3 h4 h5
  intro j
  fin_cases j  <;> 
    simp (disch:=omega) [applyBlock,saveBlock,List.range_succ,Op.apply,writeNat,writeScalar,next,
      hs,h0,h1,h2,h3,h4,h5]

theorem save_other (scratch : ℕ) (s : State) (hs:s.natReg 19=scratch) (i : ℕ)
    (hi:i < scratch∨scratch+6 ≤ i) : (applyBlock saveBlock s).scalarHeap i=s.scalarHeap i := by
  simp (disch:=omega) [applyBlock,saveBlock,List.range_succ,Op.apply,writeNat,writeScalar,next,hs]


def KeepsNat (i : ℕ) : UniformMachine.Instruction→Prop
  | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _ => d≠i
  | _ => True

theorem step_keeps_nat (p : Program) (n : ℕ) (x : Fin n→ℂ) (s u : State) (i : ℕ)
    (hcode:∀ins∈p,KeepsNat i ins) (h:UniformMachine.step p n x s=.running u) :
    u.natReg i=s.natReg i := by
  cases hg:p[s.pc]? with
  | none => simp [UniformMachine.step,hg] at h
  | some ins =>
    obtain ⟨hp,he⟩:=List.getElem?_eq_some_iff.1 hg
    have hi:=hcode ins (List.mem_of_getElem he)
    cases ins <;> simp only [UniformMachine.step,hg] at h
    all_goals simp only [KeepsNat] at hi
    all_goals try simp only [StepResult.running.injEq] at h
    all_goals repeat' (first | (subst u;simp_all [writeNat,writeScalar,next]) |
      (split at h <;> simp_all [writeNat,writeScalar,next,ne_comm]))
    all_goals first | exact Function.update_of_ne (Ne.symm hi) _ _ | contradiction

theorem Executes.keeps_nat {p : Program} {n t i : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Executes p n x s t u) (hcode:∀ins∈p,KeepsNat i ins) : u.natReg i=s.natReg i := by
  induction h with
  | halt _ => rfl
  | next hh _ ih => exact ih.trans (step_keeps_nat p n x _ _ i hcode hh)

theorem table_keeps_nat (i : ℕ) (hi:i < 20) : ∀ins∈tableProgram,KeepsNat i ins := by
  simp [tableProgram,startBlock,productBlock,switchBlock,inverseBlock,recipesBlock,
    baseRecipes,productRecipes,inverseRecipes,Recipe.block,emitRow,Op.code,KeepsNat]
  omega
theorem interpreter_keeps_nat (i : ℕ) (hi:10 ≤ i) :
    ∀ins∈UniformPreparationMachine.program,KeepsNat i ins := by
  simp [UniformPreparationMachine.program,KeepsNat]
  omega

theorem setup_roots (r scratch source : ℕ) (omega : ℂ) (s : State)
    (h19:s.natReg 19=scratch) (h18:s.natReg 18=source)
    (hroot:s.scalarHeap source=some ⟨omega,false⟩) (hdis:6 ≤ scratch)
    (hsource:scratch+6 ≤ source) :
    RootsReady (UniformNewton.Preparation.roots omega) (applyBlock setupBlock s) ∧
    LiteralsReady (UniformNewton.Preparation.finalProgram r) (applyBlock setupBlock s) := by
  have hsave:(applyBlock saveBlock s).scalarHeap source=some ⟨omega,false⟩ :=
    (save_other scratch s h19 source (Or.inr hsource)).trans hroot
  have hs18:(applyBlock saveBlock s).natReg 18=source := by
    simp [applyBlock,saveBlock,List.range_succ,Op.apply,writeNat,writeScalar,next,h18]
  have h0:(applyBlock setupBlock s).scalarHeap 0=some ⟨0,false⟩ := by
    rw [setupBlock,applyBlock_append]
    simp [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next]
  have h1:(applyBlock setupBlock s).scalarHeap 1=some ⟨omega,false⟩ := by
    rw [setupBlock,applyBlock_append]
    simp [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next,hs18,
      show source≠0 by omega,hsave]
  have ho:(applyBlock setupBlock s).scalarHeap 3=some ⟨1,false⟩ := by
    rw [setupBlock,applyBlock_append]
    simp [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next]
  have hm:(applyBlock setupBlock s).scalarHeap 4=some ⟨-1,false⟩ := by
    rw [setupBlock,applyBlock_append]
    simp [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next]
  refine ⟨⟨h0,?_⟩,inverse_literals r r le_rfl _ ho hm⟩
  intro j
  fin_cases j
  exact h1

theorem readable_append (b c : List Op) (s : State) :
    readable (b++c) s ↔ readable b s ∧ readable c (applyBlock b s) := by
  induction b generalizing s with
  | nil => simp [readable,applyBlock]
  | cons o b ih => simp [readable,applyBlock,ih,and_assoc]

theorem peak_append (b c : List Op) (s : State) :
    peak (b++c) s=max (peak b s) (peak c (applyBlock b s)) := by
  induction b generalizing s with
  | nil => simp [peak,applyBlock]
  | cons o b ih => simp [peak,applyBlock,ih,max_assoc]

theorem setup_readable (scratch source : ℕ) (omega : ℂ) (bank : Fin 6→Scalar) (s : State)
    (hb:Bank bank s) (h19:s.natReg 19=scratch) (h18:s.natReg 18=source)
    (hroot:s.scalarHeap source=some ⟨omega,false⟩) (hdis:6 ≤ scratch)
    (hsource:scratch+6 ≤ source) : readable setupBlock s := by
  rw [setupBlock,readable_append]
  refine ⟨save_readable scratch bank s hb h19 hdis,?_⟩
  have hh:(applyBlock saveBlock s).scalarHeap source=some ⟨omega,false⟩:=
    (save_other scratch s h19 source (Or.inr hsource)).trans hroot
  have hr:(applyBlock saveBlock s).natReg 18=source:=by
    simp [applyBlock,saveBlock,List.range_succ,Op.apply,writeNat,writeScalar,next,h18]
  simp [readable,literalBlock,Op.readable,Op.apply,writeNat,writeScalar,next,hr,
    show source≠0 by omega,hh]

theorem setup_peak (scratch B : ℕ) (s : State) (h19:s.natReg 19=scratch)
    (hB:scratch+6 ≤ B) : peak setupBlock s ≤ B := by
  rw [setupBlock,peak_append]
  refine max_le (save_peak scratch B s h19 hB) ?_
  simp [peak,literalBlock,Op.peak,Op.apply,writeNat,writeScalar,next]
  omega

theorem setup_saved (scratch : ℕ) (bank : Fin 6→Scalar) (s : State)
    (hb:Bank bank s) (h19:s.natReg 19=scratch) (hdis:6 ≤ scratch) :
    SavedBank scratch bank (applyBlock setupBlock s) := by
  have hh:=save_bank scratch bank s hb h19 hdis
  intro j
  rw [setupBlock,applyBlock_append]
  have hj:scratch+j.val≥6:=by omega
  simpa (disch:=omega) [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next,
    show scratch+j.val≠0 by omega,show scratch+j.val≠1 by omega,
    show scratch+j.val≠3 by omega,show scratch+j.val≠4 by omega] using hh j

theorem setup_register (s : State) (i : ℕ) (hi:i < 20) :
    (applyBlock setupBlock s).natReg i=s.natReg i := by
  simp [applyBlock,setupBlock,saveBlock,literalBlock,List.range_succ,Op.apply,
    writeNat,writeScalar,next,show i≠40 by omega,show i≠41 by omega,show i≠42 by omega]

theorem restore_readable (scratch : ℕ) (bank : Fin 6→Scalar) (s : State)
    (hb:SavedBank scratch bank s) (h19:s.natReg 19=scratch) (hdis:6 ≤ scratch) :
    readable restoreBlock s := by
  have h0:=hb 0;have h1:=hb 1;have h2:=hb 2;have h3:=hb 3;have h4:=hb 4;have h5:=hb 5
  norm_num at h0 h1 h2 h3 h4 h5
  simp (disch:=omega) [readable,restoreBlock,List.range_succ,Op.readable,Op.apply,
    writeNat,writeScalar,next,h19,h0,h1,h2,h3,h4,h5]

theorem restore_peak (scratch B : ℕ) (s : State) (h19:s.natReg 19=scratch)
    (hB:scratch+6 ≤ B) : peak restoreBlock s ≤ B := by
  simp [peak,restoreBlock,List.range_succ,Op.peak,Op.apply,writeNat,writeScalar,next,h19]
  omega

theorem restore_bank (scratch : ℕ) (bank : Fin 6→Scalar) (s : State)
    (hb:SavedBank scratch bank s) (h19:s.natReg 19=scratch) (hdis:6 ≤ scratch) :
    Bank bank (applyBlock restoreBlock s) := by
  have h0:=hb 0;have h1:=hb 1;have h2:=hb 2;have h3:=hb 3;have h4:=hb 4;have h5:=hb 5
  norm_num at h0 h1 h2 h3 h4 h5
  intro j
  fin_cases j <;>
    simp (disch:=omega) [applyBlock,restoreBlock,List.range_succ,Op.apply,
      writeNat,writeScalar,next,h19,h0,h1,h2,h3,h4,h5]

theorem restore_other (s : State) (i : ℕ) (hi:6 ≤ i) :
    (applyBlock restoreBlock s).scalarHeap i=s.scalarHeap i := by
  simp [applyBlock,restoreBlock,List.range_succ,Op.apply,writeNat,writeScalar,next,
    show i≠0 by omega,show i≠1 by omega,show i≠2 by omega,show i≠3 by omega,
    show i≠4 by omega,show i≠5 by omega]

theorem ValidSchedule.heap_outside {qs : List Row} {s u : State}
    (h:ValidSchedule qs s u) (i : ℕ)
    (hi:i < s.natReg 9 ∨ s.natReg 9+qs.length ≤ i) : u.scalarHeap i=s.scalarHeap i := by
  induction h with
  | nil s => rfl
  | @cons q qs s u l r v hr ht ih =>
    have hf:=row_frame q s l r v
    have hi':i < (rowEnd q s l r v).natReg 9 ∨
        (rowEnd q s l r v).natReg 9+qs.length ≤ i:=by
      rw [hf.2.2.2.2.2.1]
      simp only [List.length_cons] at hi
      omega
    rw [ih hi',hf.2.2.2.2.2.2.2.1,Function.update_of_ne]
    simp only [List.length_cons] at hi
    omega

theorem totalCost_append (qs ps : List Row) : totalCost (qs++ps)=totalCost qs+totalCost ps := by
  simp [totalCost,List.map_append,List.sum_append]

theorem rows_cost (r a : ℕ) : totalCost (rows r a)=166*r+51 := by
  have hp (j:ℕ) : totalCost ((List.range j).flatMap (productRows a))=103*j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [List.range_succ,List.flatMap_append,totalCost_append,ih]
      norm_num [productRows,totalCost,rowCost]
      omega
  have hi (j:ℕ) : totalCost ((List.range j).flatMap (inverseRows r a))=63*j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [List.range_succ,List.flatMap_append,totalCost_append,ih]
      norm_num [inverseRows,totalCost,rowCost]
      omega
  rw [rows,totalCost_append,totalCost_append,hp,hi]
  norm_num [baseRows,totalCost,rowCost]
  omega

def PreparedOutputs (r : ℕ) (omega : ℂ) (a : ℕ) (s : State) : Prop :=
  ∀j:Fin r,∀q:Fin 5,s.scalarHeap
    (a+((UniformNewton.Preparation.table r).output (finProdFinEquiv (j,q))).val)=
      some ⟨UniformNewton.Preparation.expected omega j.val q,false⟩

theorem values_outputs (r a : ℕ) (omega : ℂ) (hr:0 < r) (hroot:IsPrimitiveRoot omega r)
    (s : State) (hv:Values (UniformNewton.Preparation.finalProgram r)
      (UniformNewton.Preparation.roots omega) a s) : PreparedOutputs r omega a s := by
  intro j q
  have h:=values_output (UniformNewton.Preparation.table r) (UniformNewton.Preparation.roots omega)
    (UniformNewton.Preparation.table_admissible hr hroot) a s hv (finProdFinEquiv (j,q))
  rw [UniformNewton.Preparation.table_run hr hroot] at h
  exact h

theorem interpreter_ready (n : ℕ) (x : Fin n→ℂ) (r a B : ℕ) (omega : ℂ) (s : State)
    (hr:0 < r) (hroot:IsPrimitiveRoot omega r) (hp:s.pc=0)
    (hcount:s.natReg 0=8*r+3) (haddr:s.natReg 9=a)
    (ha:8*r+5 ≤ a) (hB:a+32*r+52 ≤ B) (hs:WordBound B s)
    (hroots:RootsReady (UniformNewton.Preparation.roots omega) s)
    (hlit:LiteralsReady (UniformNewton.Preparation.finalProgram r) s)
    (htable:NatTable (compile (UniformNewton.Preparation.finalProgram r) a) s) : ∃u,
    BoundedExecution UniformPreparationMachine.program n x B s (166*r+56) u ∧
    Values (UniformNewton.Preparation.finalProgram r) (UniformNewton.Preparation.roots omega) a u ∧
    (∀i,i < a ∨ a+(8*r+3) ≤ i→u.scalarHeap i=s.scalarHeap i) ∧
    (∀i,10 ≤ i→u.natReg i=s.natReg i) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ u.natHeap=s.natHeap := by
  let k:=UniformNewton.Preparation.inverseCount r r
  have hk:k=8*r+3:=by dsimp [k];rw [UniformNewton.Preparation.inverseCount_formula];omega
  have hregs:Registers k a 0 (initialized s):=by
    simp [Registers,initialized,writeNat,next,hp,hcount,haddr,hk]
  obtain ⟨u,hvalid,hru,hvu,hbase⟩:=compile_valid
    (UniformNewton.Preparation.finalProgram r) (UniformNewton.Preparation.roots omega) k a
    (initialized s) le_rfl (by omega) hregs hroots
    ((literals_heap_eq _ s (initialized s) rfl).2 hlit) htable
    (UniformNewton.Preparation.inverseProgram_admissible hr hroot r le_rfl)
  have hl:(compile (UniformNewton.Preparation.finalProgram r) a).length=8*r+3:=by
    rw [compile_length,UniformNewton.Preparation.inverseCount_formula];omega
  have he:=interpreted_schedule n x (compile (UniformNewton.Preparation.finalProgram r) a) a B s u
    (by rw [hl];omega) hp (by rw [hl];exact hcount) haddr hs hvalid
  have hcost:totalCost (compile (UniformNewton.Preparation.finalProgram r) a)+5=166*r+56:=by
    rw [←rows_eq_compile,rows_cost]
  refine ⟨{u with pc:=30},?_,hvu,?_,?_,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩
  · simpa only [hcost] using he.1
  · intro i hi
    have h:=ValidSchedule.heap_outside hvalid i (by simpa [initialized,writeNat,next,haddr,hl] using hi)
    exact h
  · intro i hi
    exact Executes.keeps_nat he.1.executes (interpreter_keeps_nat i hi)

theorem setup_other (scratch : ℕ) (s : State) (h19:s.natReg 19=scratch) (i : ℕ)
    (hi:6 ≤ i) (hout:i < scratch ∨ scratch+6 ≤ i) :
    (applyBlock setupBlock s).scalarHeap i=s.scalarHeap i := by
  rw [setupBlock,applyBlock_append]
  have h:=save_other scratch s h19 i hout
  simpa [literalBlock,applyBlock,Op.apply,writeNat,writeScalar,next,
    show i≠0 by omega,show i≠1 by omega,show i≠3 by omega,show i≠4 by omega] using h

/-- The layout is local. In particular Nat heap [0,24*r+9) is allocated;
preservation of an earlier CRT table in that region is not claimed. -/
structure Layout (r a scratch source : ℕ) : Prop where
  results : 8*r+5 ≤ a
  afterResults : a+(8*r+3) ≤ scratch
  root : scratch+6 ≤ source

/-- A single fixed literal program produces and executes the Newton DAG.
No ready row table, rational bank, DAG scalar, or division certificate is an
entry assumption. Only the already supplied primitive axis root is read. -/
theorem preparation_execution (n : ℕ) (x : Fin n→ℂ) (r a scratch source B : ℕ)
    (omega : ℂ) (bank : Fin 6→Scalar) (s : State)
    (hr:0 < r) (hroot:IsPrimitiveRoot omega r) (hl:Layout r a scratch source)
    (hp:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=a)
    (h18:s.natReg 18=source) (h19:s.natReg 19=scratch)
    (hb:Bank bank s) (haxis:s.scalarHeap source=some ⟨omega,false⟩)
    (hB:a+32*r+300 ≤ B) (hscratch:scratch+6 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (252*r+170) u ∧
    PreparedOutputs r omega a u ∧ Bank bank u ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=putWords 0 (bytecode (rows r a)) s.natHeap ∧
    (∀i,6 ≤ i→(i < a∨a+(8*r+3) ≤ i)→(i < scratch∨scratch+6 ≤ i)→
      u.scalarHeap i=s.scalarHeap i) := by
  have hdis:6 ≤ scratch:=by have:=hl.results;have:=hl.afterResults;omega
  let z:=applyBlock setupBlock s
  have hsetup:=block_runs setupBlock program 0 n B x s setup_at hp hs
    (by change 0+36 ≤ B;omega)
    (setup_readable scratch source omega bank s hb h19 h18 haxis hdis hl.root)
    (setup_peak scratch B s h19 hscratch)
  have hzpc:z.pc=36:=by dsimp [z];rw [applyBlock_pc,hp];rfl
  let e:State:={z with pc:=0}
  have heb:WordBound B e:=changePC_bound B _ _ hsetup.final_bound (by omega)
  obtain ⟨t,ht,hth,htt,hframe,hconst⟩:=table_execution n x r a B e rfl
    ((setup_register s 16 (by decide)).trans h16) ((setup_register s 17 (by decide)).trans h17)
    (by omega) heb
  have hzplaced:placed 36 e=z:=by
    change {z with pc:=36}=z
    rw [←hzpc]
  have htable:BoundedRuns program n x B z (86*r+49) {t with pc:=169}:=by
    simpa only [hzplaced] using UniformBoundedAssembly.boundedExecution_placed table_code
      (by rw [tableProgram_length];omega) (by omega) ht
  let w:State:={t with pc:=169}
  have hwconst:Constants r a w:=hconst.withPC
  have hw19:w.natReg 19=scratch:=by
    have h:=Executes.keeps_nat ht.executes (table_keeps_nat 19 (by decide))
    exact h.trans ((setup_register s 19 (by decide)).trans h19)
  have hstart:=block_runs interpreterStart program 169 n B x w interpreter_start_at rfl
    htable.final_bound (by change 169+4 ≤ B;omega)
    (by simp [readable,interpreterStart,Op.readable]) (by
      simp [peak,interpreterStart,Op.peak,Op.apply,writeNat,next,
        hwconst.order,hwconst.base,hwconst.three,hwconst.zero]
      omega)
  let v:=applyBlock interpreterStart w
  have hvpc:v.pc=173:=by dsimp [v];rw [applyBlock_pc];rfl
  have hvcount:v.natReg 0=8*r+3:=by
    simp [v,interpreterStart,applyBlock,Op.apply,writeNat,next,
      hwconst.order,hwconst.three];omega
  have hvaddr:v.natReg 9=a:=by
    simp [v,interpreterStart,applyBlock,Op.apply,writeNat,next,hwconst.base,hwconst.zero]
  have hv19:v.natReg 19=scratch:=by
    simpa [v,interpreterStart,applyBlock,Op.apply,writeNat,next] using hw19
  have hvheap:v.scalarHeap=z.scalarHeap:=by
    have h:Frame w v:=block_frame interpreterStart w (by simp [interpreterStart,HeapFree])
    exact h.1.trans hframe.1
  have hvnat:v.natHeap=t.natHeap:=by
    exact applyBlock_natHeap interpreterStart w (by simp [interpreterStart,NatHeapFree])
  obtain ⟨hroots,hlit⟩:=setup_roots r scratch source omega s h19 h18 haxis hdis hl.root
  let iv:State:={v with pc:=0}
  have hiv:WordBound B iv:=changePC_bound B _ _ hstart.final_bound (by omega)
  have roots:RootsReady (UniformNewton.Preparation.roots omega) iv:=by
    unfold RootsReady at *
    simpa only [show iv.scalarHeap=z.scalarHeap from hvheap] using hroots
  have literals:LiteralsReady (UniformNewton.Preparation.finalProgram r) iv:=
    (literals_heap_eq _ z iv hvheap).2 hlit
  have table:NatTable (compile (UniformNewton.Preparation.finalProgram r) a) iv:=by
    intro j q hq
    simpa only [show iv.natHeap=t.natHeap from hvnat] using htt j q hq
  obtain ⟨u,hu,hvalues,houtside,hregs,houtputs,horders,hheap⟩:=interpreter_ready n x r a B omega iv
    hr hroot rfl hvcount hvaddr hl.results (by omega) hiv roots literals table
  have hvplaced:placed 173 iv=v:=by
    change {v with pc:=173}=v
    rw [←hvpc]
  have hinterp:BoundedRuns program n x B v (166*r+56) {u with pc:=204}:=by
    simpa only [hvplaced] using UniformBoundedAssembly.boundedExecution_placed interpreter_code
      (by change 173+31 ≤ B;omega) (by omega) hu
  let q:State:={u with pc:=204}
  have hq19:q.natReg 19=scratch:=(hregs 19 (by decide)).trans hv19
  have saved:SavedBank scratch bank q:=by
    have hz:=setup_saved scratch bank s hb h19 hdis
    intro j
    calc
      q.scalarHeap (scratch+j.val)=iv.scalarHeap (scratch+j.val):=
        houtside _ (Or.inr (by have:=hl.afterResults;omega))
      _=z.scalarHeap (scratch+j.val):=congrFun hvheap _
      _=some (bank j):=hz j
  have hrestore:=block_runs restoreBlock program 204 n B x q restore_at rfl hinterp.final_bound
    (by change 204+24 ≤ B;omega) (restore_readable scratch bank q saved hq19 hdis)
    (restore_peak scratch B q hq19 hscratch)
  let out:=applyBlock restoreBlock q
  have hopc:out.pc=228:=by dsimp [out];rw [applyBlock_pc];rfl
  have halt:BoundedExecution program n x B out 1 out:=
    .halt hrestore.final_bound (by rw [step,hopc,program_halt])
  have hall:=hsetup.trans (htable.trans (hstart.trans (hinterp.trans hrestore)))
  refine ⟨out,?_,?_,restore_bank scratch bank q saved hq19 hdis,?_,?_,?_,?_⟩
  · convert hall.executes halt using 1
    change 252*r+170=36+((86*r+49)+(4+((166*r+56)+24)))+1
    omega
  · apply values_outputs r a omega hr hroot
    intro j
    rw [restore_other q _ (by have:=hl.results;omega)]
    exact hvalues j
  · have ho:out.outputs=q.outputs:=(applyBlock_outputs restoreBlock q).1
    have hv:v.outputs=w.outputs:=(applyBlock_outputs interpreterStart w).1
    exact ho.trans (houtputs.trans (hv.trans (hframe.2.1.trans (applyBlock_outputs setupBlock s).1)))
  · have ho:out.rootOrders=q.rootOrders:=(applyBlock_outputs restoreBlock q).2
    have hv:v.rootOrders=w.rootOrders:=(applyBlock_outputs interpreterStart w).2
    exact ho.trans (horders.trans (hv.trans (hframe.2.2.trans (applyBlock_outputs setupBlock s).2)))
  · have ho:out.natHeap=q.natHeap:=applyBlock_natHeap restoreBlock q
      (by simp [restoreBlock,List.range_succ,NatHeapFree])
    rw [ho,hheap,hvnat,hth]
    congr 1
  · intro i hi hresult hsave
    calc
      out.scalarHeap i=q.scalarHeap i:=restore_other q i hi
      _=iv.scalarHeap i:=houtside i hresult
      _=z.scalarHeap i:=congrFun hvheap i
      _=s.scalarHeap i:=setup_other scratch s h19 i hi hsave

def resultBase (r : ℕ) : ℕ := 8*r+5
def scratchBase (r : ℕ) : ℕ := 16*r+8
def rootAddress (r : ℕ) : ℕ := 16*r+14
def wordBudget (r : ℕ) : ℕ := 40*r+305

theorem canonical_layout (r : ℕ) : Layout r (resultBase r) (scratchBase r) (rootAddress r) := by
  constructor
  all_goals simp [resultBase,scratchBase,rootAddress]
  all_goals omega

/-- The canonical allocation has a linear address-value bound, hence the
existing RAM's word convention requires only logarithmically many bits. -/
theorem wordBudget_polynomial (r : ℕ) : wordBudget r≤305*(r+1) := by
  simp [wordBudget];omega

theorem canonical_execution (n : ℕ) (x : Fin n→ℂ) (r : ℕ) (omega : ℂ)
    (bank : Fin 6→Scalar) (s : State) (hr:0 < r) (hroot:IsPrimitiveRoot omega r)
    (hp:s.pc=0) (h16:s.natReg 16=r) (h17:s.natReg 17=resultBase r)
    (h18:s.natReg 18=rootAddress r) (h19:s.natReg 19=scratchBase r)
    (hb:Bank bank s) (haxis:s.scalarHeap (rootAddress r)=some ⟨omega,false⟩)
    (hs:WordBound (wordBudget r) s) : ∃u,
    BoundedExecution program n x (wordBudget r) s (252*r+170) u ∧
    PreparedOutputs r omega (resultBase r) u ∧ Bank bank u ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=putWords 0 (bytecode (rows r (resultBase r))) s.natHeap ∧
    (∀i,6 ≤ i→(i < resultBase r∨resultBase r+(8*r+3) ≤ i)→
      (i < scratchBase r∨scratchBase r+6 ≤ i)→u.scalarHeap i=s.scalarHeap i) := by
  exact preparation_execution n x r (resultBase r) (scratchBase r) (rootAddress r)
    (wordBudget r) omega bank s hr hroot (canonical_layout r) hp h16 h17 h18 h19 hb haxis
    (by simp [resultBase,wordBudget];omega) (by simp [scratchBase,wordBudget];omega) hs

end
end ExactFourierCircuits.UniformNewtonTableMachine
