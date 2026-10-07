import UniformInPlaceMachine
import UniformContext
import TypedKernelWords

set_option autoImplicit false

/-! A literal heap implementation of the fixed two-coordinate kernel. Address
setup and coefficient preparation are explicit caller obligations. -/
namespace ExactFourierCircuits.UniformPairMachine
open UniformMachine

/-- Nat registers0/1 are the two data addresses; prepared scalar registers0/1
are the diagonal/off-diagonal coefficients. Original inputs are loaded before
any store. Registers2..7 are scalar temporaries. -/
def program : Program :=
  [.loadScalar 2 0, .loadScalar 3 1,
   .fieldBinary .mul 4 0 2, .fieldBinary .mul 5 1 3, .fieldBinary .add 6 4 5,
   .fieldBinary .mul 4 1 2, .fieldBinary .mul 5 0 3, .fieldBinary .add 7 4 5,
   .storeScalar 0 6, .storeScalar 1 7, .halt]

theorem program_length : program.length = 11 := rfl

theorem contextFree : UniformContext.ContextFree program := by
  simp [UniformContext.ContextFree,UniformContext.instructionFree,program]

noncomputable section

def prepared (c : ℂ) : Scalar := ⟨c,false⟩
def product (c : ℂ) (v : Scalar) : Scalar := ⟨c*v.value,v.dependent⟩
def combine (c d : ℂ) (u v : Scalar) : Scalar :=
  ⟨c*u.value+d*v.value,u.dependent || v.dependent⟩

def loadedLeft (s : State) (u : Scalar) : State := writeScalar s 2 u
def loadedBoth (s : State) (u v : Scalar) : State := writeScalar (loadedLeft s u) 3 v
def productLeft (s : State) (c : ℂ) (u v : Scalar) : State :=
  writeScalar (loadedBoth s u v) 4 (product c u)
def productRight (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (productLeft s c u v) 5 (product d v)
def addedLeft (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (productRight s c d u v) 6 (combine c d u v)
def productOtherLeft (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (addedLeft s c d u v) 4 (product d u)
def productOtherRight (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (productOtherLeft s c d u v) 5 (product c v)
def addedRight (s : State) (c d : ℂ) (u v : Scalar) : State :=
  writeScalar (productOtherRight s c d u v) 7 (combine d c u v)
def storedLeft (s : State) (c d : ℂ) (u v : Scalar) : State :=
  {next (addedRight s c d u v) with scalarHeap := Function.update s.scalarHeap (s.natReg 0) (some (combine c d u v))}
def finalState (s : State) (c d : ℂ) (u v : Scalar) : State :=
  {next (storedLeft s c d u v) with scalarHeap := Function.update (storedLeft s c d u v).scalarHeap (s.natReg 1) (some (combine d c u v))}

structure Ready (c d : ℂ) (u v : Scalar) (s : State) : Prop where
  pc : s.pc=0
  left : s.scalarHeap (s.natReg 0)=some u
  right : s.scalarHeap (s.natReg 1)=some v
  diagonal : s.scalarReg 0=prepared c
  offDiagonal : s.scalarReg 1=prepared d

theorem prepared_mul (c : ℂ) (u : Scalar) :
    evalField .mul (prepared c) u=some (product c u) := by
  simp [evalField,prepared,product]

theorem product_add (c d : ℂ) (u v : Scalar) :
    evalField .add (product c u) (product d v)=some (combine c d u v) := rfl

/-- Every load, multiplication, addition, store and halt costs one instruction.
The result does not require scalar nonzero tests or initialized scratch slots. -/
theorem bounded_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (c d : ℂ) (u v : Scalar) (hr : Ready c d u v s)
    (hB : 11 ≤ B) (hs : WordBound B s) :
    BoundedExecution program n x B s 11 (finalState s c d u v) := by
  obtain ⟨hp,hu,hv,hc,hd⟩ := hr
  have h1 := writeScalar_bound B s 2 u hs (by omega)
  have h2 := writeScalar_bound B (loadedLeft s u) 3 v h1
    (by simp [loadedLeft,writeScalar,next,hp];omega)
  have h3 := writeScalar_bound B (loadedBoth s u v) 4 (product c u) h2
    (by simp [loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h4 := writeScalar_bound B (productLeft s c u v) 5 (product d v) h3
    (by simp [productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h5 := writeScalar_bound B (productRight s c d u v) 6 (combine c d u v) h4
    (by simp [productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h6 := writeScalar_bound B (addedLeft s c d u v) 4 (product d u) h5
    (by simp [addedLeft,productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h7 := writeScalar_bound B (productOtherLeft s c d u v) 5 (product c v) h6
    (by simp [productOtherLeft,addedLeft,productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h8 := writeScalar_bound B (productOtherRight s c d u v) 7 (combine d c u v) h7
    (by simp [productOtherRight,productOtherLeft,addedLeft,productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
  have h9 := UniformInPlaceMachine.storeScalar_bound B (addedRight s c d u v)
    (s.natReg 0) (combine c d u v) h8
    (by simp [addedRight,productOtherRight,productOtherLeft,addedLeft,productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
    (hs.2.1 0)
  have h10 := UniformInPlaceMachine.storeScalar_bound B (storedLeft s c d u v)
    (s.natReg 1) (combine d c u v) h9
    (by simp [storedLeft,addedRight,productOtherRight,productOtherLeft,addedLeft,productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,hp];omega)
    (hs.2.1 1)
  refine .next hs (u:=loadedLeft s u) ?_ (.next h1 (u:=loadedBoth s u v) ?_
    (.next h2 (u:=productLeft s c u v) ?_ (.next h3 (u:=productRight s c d u v) ?_
      (.next h4 (u:=addedLeft s c d u v) ?_ (.next h5 (u:=productOtherLeft s c d u v) ?_
        (.next h6 (u:=productOtherRight s c d u v) ?_ (.next h7 (u:=addedRight s c d u v) ?_
          (.next h8 (u:=storedLeft s c d u v) ?_ (.next h9 (u:=finalState s c d u v) ?_
            (.halt h10 ?_))))))))))
  all_goals simp [step,program,finalState,storedLeft,addedRight,productOtherRight,
    productOtherLeft,addedLeft,productRight,productLeft,loadedBoth,loadedLeft,
    writeScalar,next,hp,hu,hv,hc,hd,prepared_mul,product_add]

theorem final_frame (s : State) (c d : ℂ) (u v : Scalar) :
    (finalState s c d u v).natReg=s.natReg ∧
    (finalState s c d u v).natHeap=s.natHeap ∧
    (finalState s c d u v).outputs=s.outputs ∧
    (finalState s c d u v).rootOrders=s.rootOrders ∧
    ∀ r, r<2 ∨ 8≤r → (finalState s c d u v).scalarReg r=s.scalarReg r := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  have h2 : r≠2 := by omega
  have h3 : r≠3 := by omega
  have h4 : r≠4 := by omega
  have h5 : r≠5 := by omega
  have h6 : r≠6 := by omega
  have h7 : r≠7 := by omega
  simp [finalState,storedLeft,addedRight,productOtherRight,productOtherLeft,addedLeft,
    productRight,productLeft,loadedBoth,loadedLeft,writeScalar,next,h2,h3,h4,h5,h6,h7]

theorem final_heap (s : State) (c d : ℂ) (u v : Scalar) :
    (finalState s c d u v).scalarHeap=Function.update
      (Function.update s.scalarHeap (s.natReg 0) (some (combine c d u v)))
      (s.natReg 1) (some (combine d c u v)) := rfl

theorem final_values (s : State) (c d : ℂ) (u v : Scalar) (hne : s.natReg 0≠s.natReg 1) :
    (finalState s c d u v).scalarHeap (s.natReg 0)=some (combine c d u v) ∧
    (finalState s c d u v).scalarHeap (s.natReg 1)=some (combine d c u v) := by
  simp [final_heap,hne]

theorem untouched (s : State) (c d : ℂ) (u v : Scalar) (i : ℕ)
    (h0 : i≠s.natReg 0) (h1 : i≠s.natReg 1) :
    (finalState s c d u v).scalarHeap i=s.scalarHeap i := by
  simp [final_heap,h0,h1]

/-- The same actual execution computes the paper's fixed C matrix. -/
theorem C_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State) (u v : Scalar)
    (hr : Ready a b u v s) (hB : 11≤B) (hs : WordBound B s)
    (hne : s.natReg 0≠s.natReg 1) :
    BoundedExecution program n x B s 11 (finalState s a b u v) ∧
      (finalState s a b u v).scalarHeap (s.natReg 0)=
        some ⟨C.mulVec ![u.value,v.value] 0,u.dependent || v.dependent⟩ ∧
      (finalState s a b u v).scalarHeap (s.natReg 1)=
        some ⟨C.mulVec ![u.value,v.value] 1,u.dependent || v.dependent⟩ := by
  have hv := final_values s a b u v hne
  refine ⟨bounded_execution n x B s a b u v hr hB hs,?_,?_⟩
  · simpa [combine,C,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hv.1
  · simpa [combine,C,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hv.2

/-- Fixed rational arithmetic prepares C's two coefficients from a previously
prepared i. Extracting i from the master root is a separate charged phase. -/
def coefficientProgram : Program :=
  [.scalarLiteral 1 1,.scalarLiteral 4 (1/2),
   .fieldBinary .add 2 1 0,.fieldBinary .sub 3 1 0,
   .fieldBinary .mul 0 4 2,.fieldBinary .mul 1 4 3,.halt]

theorem coefficientProgram_length : coefficientProgram.length=7 := rfl

def coefficientOne (s : State) : State := writeScalar s 1 (prepared 1)
def coefficientHalf (s : State) : State := writeScalar (coefficientOne s) 4 (prepared (1/2))
def coefficientSum (s : State) : State :=
  writeScalar (coefficientHalf s) 2 (prepared (1+Complex.I))
def coefficientDifference (s : State) : State :=
  writeScalar (coefficientSum s) 3 (prepared (1-Complex.I))
def coefficientDiagonal (s : State) : State :=
  writeScalar (coefficientDifference s) 0 (prepared ((1/2)*(1+Complex.I)))
def coefficientState (s : State) : State :=
  writeScalar (coefficientDiagonal s) 1 (prepared ((1/2)*(1-Complex.I)))

theorem coefficient_execution (n : ℕ) (x : Fin n → ℂ) (B : ℕ) (s : State)
    (hp : s.pc=0) (hi : s.scalarReg 0=prepared Complex.I)
    (hB : 7≤B) (hs : WordBound B s) :
    BoundedExecution coefficientProgram n x B s 7 (coefficientState s) := by
  have h1 := writeScalar_bound B s 1 (prepared 1) hs (by omega)
  have h2 := writeScalar_bound B (coefficientOne s) 4 (prepared (1/2)) h1
    (by simp [coefficientOne,writeScalar,next,hp];omega)
  have h3 := writeScalar_bound B (coefficientHalf s) 2 (prepared (1+Complex.I)) h2
    (by simp [coefficientHalf,coefficientOne,writeScalar,next,hp];omega)
  have h4 := writeScalar_bound B (coefficientSum s) 3 (prepared (1-Complex.I)) h3
    (by simp [coefficientSum,coefficientHalf,coefficientOne,writeScalar,next,hp];omega)
  have h5 := writeScalar_bound B (coefficientDifference s) 0 (prepared ((1/2)*(1+Complex.I))) h4
    (by simp [coefficientDifference,coefficientSum,coefficientHalf,coefficientOne,writeScalar,next,hp];omega)
  have h6 := writeScalar_bound B (coefficientDiagonal s) 1 (prepared ((1/2)*(1-Complex.I))) h5
    (by simp [coefficientDiagonal,coefficientDifference,coefficientSum,coefficientHalf,coefficientOne,writeScalar,next,hp];omega)
  refine .next hs (u:=coefficientOne s) ?_ (.next h1 (u:=coefficientHalf s) ?_
    (.next h2 (u:=coefficientSum s) ?_ (.next h3 (u:=coefficientDifference s) ?_
      (.next h4 (u:=coefficientDiagonal s) ?_ (.next h5 (u:=coefficientState s) ?_ (.halt h6 ?_))))))
  all_goals simp [step,coefficientProgram,coefficientState,coefficientDiagonal,
    coefficientDifference,coefficientSum,coefficientHalf,coefficientOne,
    writeScalar,next,hp,hi,prepared,evalField]

theorem coefficient_values (s : State) :
    (coefficientState s).scalarReg 0=prepared a ∧
      (coefficientState s).scalarReg 1=prepared b := by
  have ha : (1/2:ℂ)*(1+Complex.I)=a := by unfold a;ring
  have hb : (1/2:ℂ)*(1-Complex.I)=b := by unfold b;ring
  change prepared ((1/2)*(1+Complex.I))=prepared a ∧ prepared ((1/2)*(1-Complex.I))=prepared b
  rw [ha,hb]
  exact ⟨rfl,rfl⟩

theorem coefficient_frame (s : State) :
    (coefficientState s).natReg=s.natReg ∧ (coefficientState s).natHeap=s.natHeap ∧
      (coefficientState s).scalarHeap=s.scalarHeap ∧ (coefficientState s).outputs=s.outputs ∧
      (coefficientState s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl,rfl⟩

end
end ExactFourierCircuits.UniformPairMachine
