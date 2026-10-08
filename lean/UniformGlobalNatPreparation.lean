import UniformNatCopyMachine
import UniformReciprocalMachine
import UniformCRTTraversalMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalNatPreparation
open UniformMachine UniformAssembly

/-- Complete contiguous metadata: primes, CRT rows, digits, alpha and beta. -/
def amount (ell L : ℕ) : ℕ := 6*ell+5+2*L
/-- Copy above both the metadata and every later local row prefix for r<=L. -/
def destination (ell L : ℕ) : ℕ := amount ell L+24*L+9

/-- Save nextPrime/n/ell/L/D in Nat100..104, d/M in105/106. All instructions
are literal Nat operations; no prepared or copied array is assumed. -/
def setup : List UniformNewtonTableMachine.Op := [
  .literal 107 0,.add 100 0 107,.add 101 8 107,.add 102 10 107,
  .add 103 17 107,.add 104 24 107,.literal 108 6,.mul 106 10 108,
  .literal 108 5,.add 106 106 108,.literal 108 2,.mul 109 17 108,
  .add 106 106 109,.literal 108 24,.mul 109 17 108,.add 105 106 109,
  .literal 108 9,.add 105 105 108,.add 53 106 107,.literal 54 0,.add 55 105 107]

def program : Program := setup.map UniformNewtonTableMachine.Op.code ++
  UniformNatCopyMachine.program.map (relocate 21 31) ++ [.halt]

theorem program_length : program.length=32 := rfl
theorem setup_at : UniformNewtonTableMachine.BlockAt setup program 0 := by
  intro i hi;change i < 21 at hi;interval_cases i <;> rfl
theorem copy_code : CodeAt UniformNatCopyMachine.program program 21 31 := by
  intro i hi;change i < 10 at hi;interval_cases i <;> rfl
theorem halt_at : program[31]?=some .halt := rfl

noncomputable section

structure Headers (nextPrime n ell L D : ℕ) (s : State) : Prop where
  nextPrime : s.natReg 0=nextPrime
  inputLength : s.natReg 8=n
  count : s.natReg 10=ell
  workingLength : s.natReg 17=L
  masterRoot : s.natReg 24=D

structure SavedHeaders (nextPrime n ell L D : ℕ) (s : State) : Prop where
  nextPrime : s.natReg 100=nextPrime
  inputLength : s.natReg 101=n
  count : s.natReg 102=ell
  workingLength : s.natReg 103=L
  masterRoot : s.natReg 104=D
  copyAddress : s.natReg 105=destination ell L
  copyLength : s.natReg 106=amount ell L

theorem Headers.withPC {nextPrime n ell L D pc : ℕ} {s : State}
    (hh:Headers nextPrime n ell L D s) : Headers nextPrime n ell L D {s with pc:=pc} := by
  cases hh;constructor <;> assumption

theorem SavedHeaders.withPC {nextPrime n ell L D pc : ℕ} {s : State}
    (hh:SavedHeaders nextPrime n ell L D s) : SavedHeaders nextPrime n ell L D {s with pc:=pc} := by
  cases hh;constructor <;> assumption

def Protected (ell L : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop :=
  ∀j,j < amount ell L→s.natHeap (destination ell L+j)=heap j

def NatFrame (s u : State) : Prop := ∀i,
  (i < 53 ∨ 61 ≤ i)→(i < 100 ∨ 110 ≤ i)→u.natReg i=s.natReg i

theorem setup_registers (nextPrime n ell L D : ℕ) (s : State)
    (hh:Headers nextPrime n ell L D s) :
    SavedHeaders nextPrime n ell L D (UniformNewtonTableMachine.applyBlock setup s) := by
  cases hh
  constructor <;> simp_all [UniformNewtonTableMachine.applyBlock,setup,
    UniformNewtonTableMachine.Op.apply,writeNat,next,amount,destination,
    Nat.mul_comm,Nat.add_assoc]

theorem setup_copy_registers (ell L : ℕ) (s : State) (h10:s.natReg 10=ell)
    (h17:s.natReg 17=L) :
    (UniformNewtonTableMachine.applyBlock setup s).natReg 53=amount ell L ∧
    (UniformNewtonTableMachine.applyBlock setup s).natReg 54=0 ∧
    (UniformNewtonTableMachine.applyBlock setup s).natReg 55=destination ell L := by
  simp [UniformNewtonTableMachine.applyBlock,setup,UniformNewtonTableMachine.Op.apply,
    writeNat,next,h10,h17,amount,destination,Nat.mul_comm,Nat.add_assoc]

theorem setup_heap (s : State) : (UniformNewtonTableMachine.applyBlock setup s).natHeap=s.natHeap :=
  UniformNewtonTableMachine.applyBlock_natHeap setup s
    (by simp [setup,UniformNewtonTableMachine.NatHeapFree])

theorem setup_frame (s : State) : UniformNatCopyMachine.Frame s
    (UniformNewtonTableMachine.applyBlock setup s) := by
  constructor <;> first | rfl | simp [UniformNewtonTableMachine.applyBlock,setup,
    UniformNewtonTableMachine.Op.apply,writeNat,next]

theorem setup_nat (s : State) : NatFrame s (UniformNewtonTableMachine.applyBlock setup s) := by
  intro i hi hj
  simp (disch:=omega) [UniformNewtonTableMachine.applyBlock,setup,
    UniformNewtonTableMachine.Op.apply,writeNat,next]

def wordBudget (ell L : ℕ) : ℕ := 12*ell+28*L+160

theorem wordBudget_polynomial (ell L : ℕ) : wordBudget ell L ≤ 160*(ell+L+1) := by
  unfold wordBudget;omega

theorem destination_disjoint (ell L : ℕ) : 0+amount ell L ≤ destination ell L := by
  unfold destination;omega

theorem destination_fits (ell L : ℕ) : destination ell L+amount ell L ≤ wordBudget ell L := by
  unfold destination amount wordBudget;omega

theorem setup_peak (ell L B : ℕ) (s : State) (h10:s.natReg 10=ell)
    (h17:s.natReg 17=L) (hs:WordBound B s) (hB:wordBudget ell L ≤ B) :
    UniformNewtonTableMachine.peak setup s ≤ B := by
  have h0:=hs.2.1 0;have h8:=hs.2.1 8;have h24:=hs.2.1 24
  simp [UniformNewtonTableMachine.peak,setup,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,h10,h17]
  unfold wordBudget at hB
  omega


theorem SavedHeaders.transport {nextPrime n ell L D : ℕ} {s u : State}
    (hh:SavedHeaders nextPrime n ell L D s)
    (hr:∀i,100 ≤ i→u.natReg i=s.natReg i) : SavedHeaders nextPrime n ell L D u := by
  constructor
  · exact (hr 100 (by decide)).trans hh.nextPrime
  · exact (hr 101 (by decide)).trans hh.inputLength
  · exact (hr 102 (by decide)).trans hh.count
  · exact (hr 103 (by decide)).trans hh.workingLength
  · exact (hr 104 (by decide)).trans hh.masterRoot
  · exact (hr 105 (by decide)).trans hh.copyAddress
  · exact (hr 106 (by decide)).trans hh.copyLength

/-- Protect the ENTIRE prefix, including both length-L permutation tables.
Its presence is explicit pending the actual global CRT-cycle producer proof. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (nextPrime ell L D B : ℕ) (s : State)
    (hh:Headers nextPrime n ell L D s)
    (hsrc:UniformNatCopyMachine.Source (amount ell L) 0 s.natHeap)
    (hpc:s.pc=0) (hB:wordBudget ell L ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s (7*amount ell L+26) u ∧
    SavedHeaders nextPrime n ell L D u ∧ Headers nextPrime n ell L D u ∧
    Protected ell L s.natHeap u ∧
    (∀j,j < amount ell L→u.natHeap j=s.natHeap j) ∧
    UniformNatCopyMachine.Outside (destination ell L) (amount ell L) s.natHeap u ∧
    UniformNatCopyMachine.Frame s u ∧ NatFrame s u := by
  have hB':160 ≤ B:=by unfold wordBudget at hB;omega
  have hz:=UniformNewtonTableMachine.block_runs setup program 0 n B x s setup_at hpc hs
    (by change 0+21 ≤ B;omega)
    (by simp [UniformNewtonTableMachine.readable,setup,UniformNewtonTableMachine.Op.readable])
    (setup_peak ell L B s hh.count hh.workingLength hs hB)
  have hSaved:=setup_registers nextPrime n ell L D s hh
  have hRegs:=setup_copy_registers ell L s hh.count hh.workingLength
  have hHeap:=setup_heap s
  have hFrame:=setup_frame s
  have hNat:=setup_nat s
  have hPC:(UniformNewtonTableMachine.applyBlock setup s).pc=21:=by
    rw [UniformNewtonTableMachine.applyBlock_pc,hpc];rfl
  generalize hEq:UniformNewtonTableMachine.applyBlock setup s=z at hz hSaved hRegs hHeap hFrame hNat hPC
  let t:State:={z with pc:=0}
  have htz:t.natHeap=s.natHeap:=hHeap
  have hsrc':UniformNatCopyMachine.Source (amount ell L) 0 t.natHeap:=by rw [htz];exact hsrc
  obtain ⟨hm,ha,hd⟩:=hRegs
  have ht:WordBound B t:=changePC_bound B z 0 hz.final_bound (by omega)
  obtain ⟨v,hv,hcopy,hsource,houtside,hframe,hnat⟩:=UniformNatCopyMachine.execution n x
    (amount ell L) 0 (destination ell L) B t hsrc' (destination_disjoint ell L)
    ((destination_fits ell L).trans hB) (by omega) rfl hm ha hd ht
  have hc:=UniformBoundedAssembly.boundedExecution_placed copy_code
    (by rw [UniformNatCopyMachine.program_length];omega : 21+UniformNatCopyMachine.program.length ≤ B)
    (by omega : 31 ≤ B) hv
  have hplaced:placed 21 t=z:=by change {z with pc:=21}=z;rw [←hPC]
  rw [hplaced] at hc
  have he:BoundedExecution program n x B {v with pc:=31} 1 {v with pc:=31}:=
    .halt hc.final_bound (by rw [step,halt_at])
  have hsv:SavedHeaders nextPrime n ell L D v:=SavedHeaders.transport
    hSaved (fun i hi=>hnat i (Or.inr (by omega)))
  have hh':Headers nextPrime n ell L D v:=by
    have hreg (i : ℕ) (hi:i < 53) (hj:i < 100) : v.natReg i=s.natReg i:=
      (hnat i (Or.inl hi)).trans (hNat i (Or.inl hi) (Or.inl hj))
    constructor
    · exact (hreg 0 (by decide) (by decide)).trans hh.nextPrime
    · exact (hreg 8 (by decide) (by decide)).trans hh.inputLength
    · exact (hreg 10 (by decide) (by decide)).trans hh.count
    · exact (hreg 17 (by decide) (by decide)).trans hh.workingLength
    · exact (hreg 24 (by decide) (by decide)).trans hh.masterRoot
  refine ⟨{v with pc:=31},?_,hsv.withPC,hh'.withPC,?_,?_,?_,hFrame.trans hframe,?_⟩
  · convert hz.executes (hc.executes he) using 1
    change 7*amount ell L+26=21+(7*amount ell L+4+1)
    omega
  · intro j hj
    simpa only [Nat.zero_add,htz] using hcopy j hj
  · intro j hj
    simpa only [Nat.zero_add,htz] using hsource j hj
  · intro j hj
    exact (houtside j hj).trans (congrFun htz j)
  · intro i hi hj
    exact (hnat i hi).trans (hNat i hi hj)

theorem runtime_formula (ell L : ℕ) : 7*amount ell L+26=42*ell+14*L+61 := by
  unfold amount;omega

theorem runtime_bound (ell L : ℕ) : 7*amount ell L+26 ≤ 13*amount ell L := by
  unfold amount;omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (nextPrime ell L D : ℕ) (s : State)
    (hh:Headers nextPrime n ell L D s)
    (hsrc:UniformNatCopyMachine.Source (amount ell L) 0 s.natHeap)
    (hpc:s.pc=0) (hs:WordBound (wordBudget ell L) s) : ∃u,
    BoundedExecution program n x (wordBudget ell L) s (7*amount ell L+26) u ∧
    SavedHeaders nextPrime n ell L D u ∧ Headers nextPrime n ell L D u ∧
    Protected ell L s.natHeap u ∧
    (∀j,j < amount ell L→u.natHeap j=s.natHeap j) ∧
    UniformNatCopyMachine.Outside (destination ell L) (amount ell L) s.natHeap u ∧
    UniformNatCopyMachine.Frame s u ∧ NatFrame s u :=
  execution n x nextPrime ell L D _ s hh hsrc hpc le_rfl hs

/-- Relocation changes array ADDRESS offsets, not their stored logical indices. -/
theorem protected_bank (ell L offset k : ℕ) (heap : ℕ→Option ℕ) (s : State)
    (h:Protected ell L heap s) (hk:offset+k ≤ amount ell L) :
    ∀j,j < k→s.natHeap (destination ell L+offset+j)=heap (offset+j) := by
  intro j hj
  simpa [Nat.add_assoc] using h (offset+j) (by omega)

def PermutationBank (k offset : ℕ) (heap : ℕ→Option ℕ)
    (phi : Fin k≃Fin k) : Prop := ∀j:Fin k,heap (offset+j.val)=some (phi j).val

theorem protected_permutation (ell L offset k : ℕ) (heap : ℕ→Option ℕ) (s : State)
    (phi : Fin k≃Fin k) (h:Protected ell L heap s) (hk:offset+k ≤ amount ell L)
    (hp:PermutationBank k offset heap phi) :
    PermutationBank k (destination ell L+offset) s.natHeap phi := by
  intro j
  rw [protected_bank ell L offset k heap s h hk j.val j.isLt]
  exact hp j

/-- Alpha and beta's same actual inverse permutation certificate survives.
Presence and correctness of the original arrays are explicit caller premises. -/
theorem protected_inverse_permutations (ell L alpha beta : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (phi : Fin L≃Fin L) (h:Protected ell L heap s)
    (ha:alpha+L ≤ amount ell L) (hb:beta+L ≤ amount ell L)
    (hpa:PermutationBank L alpha heap phi) (hpb:PermutationBank L beta heap phi.symm) :
    PermutationBank L (destination ell L+alpha) s.natHeap phi ∧
    PermutationBank L (destination ell L+beta) s.natHeap phi.symm :=
  ⟨protected_permutation ell L alpha L heap s phi h ha hpa,
    protected_permutation ell L beta L heap s phi.symm h hb hpb⟩

/-- Actual bytecode prefix length, including opcode and both operand words. -/
theorem rowBytes_length (r a : ℕ) :
    (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)).length=24*r+9 := by
  rw [UniformDAGLowering.bytecode_length,UniformNewtonTableMachine.rows_length]
  omega

theorem destination_above_rows (ell L r : ℕ) (hr:r ≤ L) : 24*r+9 ≤ destination ell L := by
  unfold destination;omega

/-- The copy is above every actual local row prefix for r<=L. -/
theorem protected_row_write (ell L r a : ℕ) (heap : ℕ→Option ℕ) (s : State)
    (h:Protected ell L heap s) (hr:r ≤ L) :
    ∀j,j < amount ell L→UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap
      (destination ell L+j)=heap j := by
  intro j hj
  rw [UniformNewtonTableMachine.putWords_after]
  · exact h j hj
  · rw [rowBytes_length]
    have hd:=destination_above_rows ell L r hr
    omega


theorem protected_after_row_post {ell L r a : ℕ} {heap : ℕ→Option ℕ} {s u : State}
    (h:Protected ell L heap s) (hr:r ≤ L)
    (hw:u.natHeap=UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap) :
    Protected ell L heap u := by
  intro j hj
  rw [hw]
  exact protected_row_write ell L r a heap s h hr j hj

theorem newton_setup_keeps_high (i : ℕ) (hi:100 ≤ i) :∀ins∈UniformNewtonTableMachine.setupBlock.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins := by
  simp [UniformNewtonTableMachine.setupBlock,UniformNewtonTableMachine.saveBlock,
    UniformNewtonTableMachine.literalBlock,List.range_succ,UniformNewtonTableMachine.Op.code,
    UniformNewtonTableMachine.KeepsNat]
  omega

theorem newton_table_keeps_high (i : ℕ) (hi:100 ≤ i) :∀ins∈UniformNewtonTableMachine.tableProgram,UniformNewtonTableMachine.KeepsNat i ins := by
  simp [UniformNewtonTableMachine.tableProgram,UniformNewtonTableMachine.startBlock,
    UniformNewtonTableMachine.productBlock,UniformNewtonTableMachine.switchBlock,
    UniformNewtonTableMachine.inverseBlock,UniformNewtonTableMachine.recipesBlock,
    UniformNewtonTableMachine.baseRecipes,UniformNewtonTableMachine.productRecipes,
    UniformNewtonTableMachine.inverseRecipes,UniformNewtonTableMachine.Recipe.block,
    UniformNewtonTableMachine.emitRow,UniformNewtonTableMachine.Op.code,
    UniformNewtonTableMachine.KeepsNat]
  omega

theorem newton_start_keeps_high (i : ℕ) (hi:100 ≤ i) :∀ins∈UniformNewtonTableMachine.interpreterStart.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins := by
  simp [UniformNewtonTableMachine.interpreterStart,UniformNewtonTableMachine.Op.code,
    UniformNewtonTableMachine.KeepsNat]
  omega

theorem newton_interpreter_keeps_high (i : ℕ) (hi:100 ≤ i) :∀ins∈UniformPreparationMachine.program,UniformNewtonTableMachine.KeepsNat i ins :=
  UniformNewtonTableMachine.interpreter_keeps_nat i (by omega)

theorem newton_restore_keeps_high (i : ℕ) (hi:100 ≤ i) :∀ins∈UniformNewtonTableMachine.restoreBlock.map UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins := by
  simp [UniformNewtonTableMachine.restoreBlock,List.range_succ,UniformNewtonTableMachine.Op.code,
    UniformNewtonTableMachine.KeepsNat]
  omega

theorem newton_keeps_high (i : ℕ) (hi:100 ≤ i) :
    ∀ins∈UniformNewtonTableMachine.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hs:=newton_setup_keeps_high i hi
  have ht:=newton_table_keeps_high i hi
  have hc:=newton_start_keeps_high i hi
  have hp:=newton_interpreter_keeps_high i hi
  have hr:=newton_restore_keeps_high i hi
  have hh:∀ins∈([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformNewtonTableMachine.program,List.append_assoc] using
    UniformReciprocalMachine.keeps_append i
      (UniformReciprocalMachine.keeps_append i
        (UniformReciprocalMachine.keeps_append i
          (UniformReciprocalMachine.keeps_append i
            (UniformReciprocalMachine.keeps_append i hs (UniformReciprocalMachine.keeps_relocate i 36 169 ht)) hc)
          (UniformReciprocalMachine.keeps_relocate i 173 204 hp)) hr) hh

theorem reciprocal_keeps_high (i : ℕ) (hi:100 ≤ i) :
    ∀ins∈UniformReciprocalMachine.completeProgram,UniformNewtonTableMachine.KeepsNat i ins := by
  have hn:=UniformReciprocalMachine.keeps_relocate i 0 229 (newton_keeps_high i hi)
  have ha:∀ins∈UniformReciprocalMachine.afterNewtonBlock.map UniformReciprocalMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformReciprocalMachine.afterNewtonBlock,UniformReciprocalMachine.adapterBlock,
      UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
    omega
  have hr:=UniformReciprocalMachine.keeps_relocate i 237 268
    (UniformReciprocalMachine.program_keeps_nat i (Or.inr (by omega)))
  have hh:∀ins∈([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformReciprocalMachine.completeProgram,List.append_assoc] using
    UniformReciprocalMachine.keeps_append i
      (UniformReciprocalMachine.keeps_append i (UniformReciprocalMachine.keeps_append i hn ha) hr) hh

theorem saved_after_actual_newton {n t nextPrime ell L D : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Executes UniformNewtonTableMachine.program n x s t u)
    (hh:SavedHeaders nextPrime n ell L D s) : SavedHeaders nextPrime n ell L D u :=
  hh.transport (fun i hi=>UniformNewtonTableMachine.Executes.keeps_nat h (newton_keeps_high i hi))

theorem saved_after_actual_reciprocal {n t nextPrime ell L D : ℕ} {x : Fin n→ℂ} {s u : State}
    (h:Executes UniformReciprocalMachine.completeProgram n x s t u)
    (hh:SavedHeaders nextPrime n ell L D s) : SavedHeaders nextPrime n ell L D u :=
  hh.transport (fun i hi=>UniformNewtonTableMachine.Executes.keeps_nat h (reciprocal_keeps_high i hi))


/-- Reuses the actual charged Newton producer, with no row/action certificate.
Its actual row writes retain the entire protected global copy and saved headers.
Scalar allocation/layout and axis-root provision remain explicit local premises. -/
theorem after_actual_newton (n : ℕ) (x : Fin n→ℂ) (nextPrime ell L D r a scratch source B : ℕ)
    (omega : ℂ) (bank : Fin 6→Scalar) (heap : ℕ→Option ℕ) (s : State)
    (hp:Protected ell L heap s) (hh:SavedHeaders nextPrime n ell L D s)
    (hr:0 < r) (hrL:r ≤ L) (hroot:IsPrimitiveRoot omega r)
    (hl:UniformNewtonTableMachine.Layout r a scratch source) (hpc:s.pc=0)
    (h16:s.natReg 16=r) (h17:s.natReg 17=a) (h18:s.natReg 18=source)
    (h19:s.natReg 19=scratch) (hb:UniformNewtonTableMachine.Bank bank s)
    (haxis:s.scalarHeap source=some (UniformReciprocalMachine.prepared omega))
    (hB:a+32*r+300 ≤ B) (hscratch:scratch+6 ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution UniformNewtonTableMachine.program n x B s (252*r+170) u ∧
    Protected ell L heap u ∧ SavedHeaders nextPrime n ell L D u ∧
    UniformNewtonTableMachine.PreparedOutputs r omega a u ∧ UniformNewtonTableMachine.Bank bank u ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap := by
  obtain ⟨u,hu,hpu,hbu,hout,hroots,hw,_⟩:=UniformNewtonTableMachine.preparation_execution
    n x r a scratch source B omega bank s hr hroot hl hpc h16 h17 h18 h19 hb haxis hB hscratch hs
  exact ⟨u,hu,protected_after_row_post hp hrL hw,saved_after_actual_newton hu.executes hh,
    hpu,hbu,hout,hroots,hw⟩

/-- Actual Newton+reciprocal execution retains the same global Nat copy. This
calls the frozen269-instruction producer, not a desired-action/count premise. -/
theorem after_actual_reciprocal (n : ℕ) (x : Fin n→ℂ) (nextPrime ell L D r a scratch source B : ℕ)
    (omega : ℂ) (bank : Fin 6→Scalar) (heap : ℕ→Option ℕ) (s : State)
    (hp:Protected ell L heap s) (hh:SavedHeaders nextPrime n ell L D s)
    (hr:0 < r) (hrL:r ≤ L) (hroot:IsPrimitiveRoot omega r)
    (hl:UniformNewtonTableMachine.Layout r a scratch source) (hpc:s.pc=0)
    (h16:s.natReg 16=r) (h17:s.natReg 17=a) (h18:s.natReg 18=source)
    (h19:s.natReg 19=scratch) (hb:UniformNewtonTableMachine.Bank bank s)
    (haxis:s.scalarHeap source=some (UniformReciprocalMachine.prepared omega))
    (hB:UniformReciprocalMachine.completeWordBudget r a source ≤ B) (hs:WordBound B s) : ∃u,
    BoundedExecution UniformReciprocalMachine.completeProgram n x B s
      (UniformReciprocalMachine.completeRuntime r) u ∧ Protected ell L heap u ∧
    SavedHeaders nextPrime n ell L D u ∧
    UniformReciprocalMachine.GPrefix r (source+1) (OAI.ExactFourier.NewtonFourier.invH omega) u ∧
    UniformNewtonTableMachine.PreparedOutputs r omega a u ∧ UniformNewtonTableMachine.Bank bank u ∧
    u.scalarHeap source=some (UniformReciprocalMachine.prepared omega) ∧
    u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
    u.natHeap=UniformNewtonTableMachine.putWords 0
      (UniformDAGLowering.bytecode (UniformNewtonTableMachine.rows r a)) s.natHeap := by
  obtain ⟨u,hu,hgu,hpu,hbu,haxis',hout,hroots,hw,_⟩:=UniformReciprocalMachine.complete_execution
    n x r a scratch source B omega bank s hr hroot hl hpc h16 h17 h18 h19 hb haxis hB hs
  exact ⟨u,hu,protected_after_row_post hp hrL hw,saved_after_actual_reciprocal hu.executes hh,
    hgu,hpu,hbu,haxis',hout,hroots,hw⟩

/-- The original metadata and permutation offsets remain available after the
local producers: high headers define the same copy base, not recomputed guesses. -/
theorem saved_copy_addresses {nextPrime n ell L D : ℕ} {s : State}
    (hh:SavedHeaders nextPrime n ell L D s) :
    s.natReg 105=6*ell+26*L+14 ∧ s.natReg 106=6*ell+5+2*L := by
  constructor
  · rw [hh.copyAddress];unfold destination amount;omega
  · exact hh.copyLength


/-- The protected prefix ends exactly after the actual CRT traversal beta bank. -/
theorem amount_eq_traversal_end (ell L : ℕ) :
    amount ell L=UniformCRTTraversalMachine.betaBase ell L+L := by
  unfold amount UniformCRTTraversalMachine.betaBase UniformCRTTraversalMachine.alphaBase
    UniformCRTTraversalMachine.digitBase
  omega

theorem traversal_alpha_fits (ell L : ℕ) :
    UniformCRTTraversalMachine.alphaBase ell+L ≤ amount ell L := by
  unfold amount UniformCRTTraversalMachine.alphaBase UniformCRTTraversalMachine.digitBase
  omega

theorem protected_traversal_permutations (ell L : ℕ) (heap : ℕ→Option ℕ)
    (s : State) (phi : Fin L≃Fin L) (h:Protected ell L heap s)
    (ha:PermutationBank L (UniformCRTTraversalMachine.alphaBase ell) heap phi)
    (hb:PermutationBank L (UniformCRTTraversalMachine.betaBase ell L) heap phi.symm) :
    PermutationBank L (destination ell L+UniformCRTTraversalMachine.alphaBase ell) s.natHeap phi ∧
    PermutationBank L (destination ell L+UniformCRTTraversalMachine.betaBase ell L) s.natHeap phi.symm :=
  protected_inverse_permutations ell L _ _ heap s phi h (traversal_alpha_fits ell L)
    (by rw [amount_eq_traversal_end]) ha hb

theorem no_scalar_input_root_output : program.any UniformNatCopyMachine.isScalar=false := rfl

end
end ExactFourierCircuits.UniformGlobalNatPreparation
