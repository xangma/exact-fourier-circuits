import UniformLocalSeedTableMachine

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ExactFourierCircuits.UniformAllAxisSeedPreparation
open UniformMachine UniformAssembly
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
namespace R
abbrev Op := UniformReciprocalMachine.Op
end R
namespace N
abbrev Op := UniformNewtonTableMachine.Op
end N
noncomputable section

abbrev axisCount (n : ℕ) := ell n+1
abbrev radix (n : ℕ) (j : Fin (axisCount n)) := UniformGlobalLocalPreparation.radix n j

def radixAt (n k : ℕ) : ℕ := if h:k<axisCount n then radix n ⟨k,h⟩ else 0
def prefixSum (n k : ℕ) : ℕ := ∑i ∈ Finset.range k,radixAt n i
def axisBase (n k : ℕ) : ℕ := UniformLocalSeedTableMachine.poolBase n+5*prefixSum n k
/-- Above the independently produced beta inverse, not in the old low workspace. -/
def directoryBase (n : ℕ) : ℕ := UniformPermutationInversePreparation.inverseBase n+len n

theorem radixAt_eq (n : ℕ) (j : Fin (axisCount n)) : radixAt n j.val=radix n j := by
  simp [radixAt,j.isLt]
theorem prefix_zero (n : ℕ) : prefixSum n 0=0 := rfl
theorem prefix_succ (n k : ℕ) : prefixSum n (k+1)=prefixSum n k+radixAt n k := by
  exact Finset.sum_range_succ _ _
theorem prefix_mono (n : ℕ) {a b : ℕ} (h:a ≤ b) : prefixSum n a ≤ prefixSum n b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _=>Nat.zero_le _)
theorem prefix_bound (n k : ℕ) (hk:k ≤ axisCount n) : prefixSum n k ≤ k*len n := by
  calc prefixSum n k ≤ ∑i ∈ Finset.range k,len n := by
        apply Finset.sum_le_sum
        intro i hi
        have hil:i<axisCount n:=by have h:=Finset.mem_range.mp hi;omega
        rw [radixAt,dite_eq_left hil]
        exact UniformGlobalLocalPreparation.radix_le_length _ _
       _ = k*len n := by simp

theorem axisBase_mono (n : ℕ) {a b : ℕ} (h:a ≤ b) : axisBase n a ≤ axisBase n b := by
  have hp:=prefix_mono n h;unfold axisBase;omega

theorem axisBase_next (n : ℕ) (j : Fin (axisCount n)) :
    axisBase n (j.val+1)=axisBase n j.val+5*radix n j := by
  unfold axisBase;rw [prefix_succ,radixAt_eq];omega

theorem directory_after_protected (n : ℕ) :
    copyBase n+UniformGlobalNatPreparation.amount (ell n) (len n)+len n=directoryBase n := rfl

theorem directory_formula (n : ℕ) : directoryBase n=12*ell n+29*len n+19 := by
  dsimp [directoryBase,UniformPermutationInversePreparation.inverseBase,copyBase,
    UniformGlobalNatPreparation.destination,UniformGlobalNatPreparation.amount]
  omega

theorem word_setup {n : ℕ} (hn:0<n) : 469 ≤ (n+2)^19 ∧
    axisBase n (axisCount n) ≤ (n+2)^19 ∧ directoryBase n+2*axisCount n ≤ (n+2)^19 := by
  have he:ell n ≤ 2*n:=by have h:=UniformWorkingLength.firstExceed_bound n;unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:=prefix_bound n (axisCount n) (le_refl _)
  have hsmall:300 ≤ (n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 17;norm_num at h;omega
  have hb:300*(n+2)^2 ≤ (n+2)^19:=by
    rw [show 19=17+2 by decide,pow_add];exact Nat.mul_le_mul_right ((n+2)^2) hsmall
  have hprod:(ell n+1)*len n ≤ (2*n+1)*(4*n):=Nat.mul_le_mul (by omega) (by omega)
  have hbPool:axisBase n (axisCount n) ≤ 300*(n+2)^2:=by
    unfold axisBase UniformLocalSeedTableMachine.poolBase
    rw [UniformGlobalLocalPreparation.globalEnd_formula]
    nlinarith
  have hbDir:directoryBase n+2*axisCount n ≤ 300*(n+2)^2:=by
    rw [directory_formula];unfold axisCount;nlinarith
  exact ⟨by nlinarith,hbPool.trans hb,hbDir.trans hb⟩

/-- Persistent loop data is kept in Nat200..209, outside both local producers. -/
def boot : List N.Op := [.literal 200 0,.literal 201 0,.literal 203 1,.literal 209 0,
  .add 202 102 203,.add 204 106 105,.add 204 204 103]
def offsetSetup : List R.Op := [.literal 125 5,.mul 112 201 125,.add 120 120 112]
def emitHead : Program := UniformLocalSeedTableMachine.globalHead++offsetSetup.map UniformReciprocalMachine.Op.code
def post : List N.Op := [.literal 206 2,.mul 207 200 206,.add 207 207 204,.putNat 207 120,
  .add 207 207 203,.putNat 207 117,.add 201 201 117,.add 200 200 203]
def head : Program := boot.map UniformNewtonTableMachine.Op.code++[.branchLT 200 202 8 468,.natBinary .add 110 200 209]
def program : Program := head++UniformGlobalLocalPreparation.program.map (relocate 9 308)++emitHead++
  UniformLocalSeedTableMachine.program.map (relocate 339 459)++post.map UniformNewtonTableMachine.Op.code++[.jump 7,.halt]

theorem boot_length : boot.length=7 := rfl
theorem post_length : post.length=8 := rfl
theorem emitHead_length : emitHead.length=31 := rfl
theorem head_length : head.length=9 := rfl
theorem program_length : program.length=469 := by
  simp only [program,List.length_append,List.length_map,head_length,
    UniformGlobalLocalPreparation.program_length,emitHead_length,UniformLocalSeedTableMachine.program_length,
    post_length];rfl

theorem boot_code : UniformNewtonTableMachine.BlockAt boot program 0 := by
  intro i hi;change i<7 at hi;interval_cases i <;> rfl

theorem branch_code : program[7]?=some (.branchLT 200 202 8 468) := rfl
theorem axis_code : program[8]?=some (.natBinary .add 110 200 209) := rfl


theorem lookup_segment (pre block suf : Program) (i : ℕ) (hi:i<block.length) :
    (pre++block++suf)[pre.length+i]?=block[i]? := by
  rw [List.getElem?_append_left (by simp;omega)]
  rw [List.getElem?_append_right (by omega)]
  simp

theorem local_lookup (i : ℕ) (hi:i<299) :
    program[9+i]?=(UniformGlobalLocalPreparation.program.map (relocate 9 308))[i]? := by
  have h:=lookup_segment head (UniformGlobalLocalPreparation.program.map (relocate 9 308))
    (emitHead++UniformLocalSeedTableMachine.program.map (relocate 339 459)++
      post.map UniformNewtonTableMachine.Op.code++[.jump 7,.halt]) i
    (by simpa only [List.length_map,UniformGlobalLocalPreparation.program_length] using hi)
  simpa only [program,List.append_assoc,head_length] using h

theorem local_code : CodeAt UniformGlobalLocalPreparation.program program 9 308 := by
  intro i hi
  rw [local_lookup i (by simpa only [UniformGlobalLocalPreparation.program_length] using hi),List.getElem?_map]

theorem emit_lookup (i : ℕ) (hi:i<31) : program[308+i]?=emitHead[i]? := by
  have h:=lookup_segment (head++UniformGlobalLocalPreparation.program.map (relocate 9 308)) emitHead
    (UniformLocalSeedTableMachine.program.map (relocate 339 459)++
      post.map UniformNewtonTableMachine.Op.code++[.jump 7,.halt]) i (by simpa only [emitHead_length] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,
    head_length,UniformGlobalLocalPreparation.program_length] using h

theorem emit_pointer_code : UniformReciprocalMachine.BlockAt UniformLocalSeedTableMachine.globalPointer program 308 := by
  intro i hi
  have hi4:i<4:=hi
  rw [emit_lookup i (by omega)]
  interval_cases i <;> rfl

theorem emit_load_code : program[312]?=some (.loadNat 117 108) := by
  rw [show 312=308+4 by decide,emit_lookup 4 (by decide)];rfl

theorem emit_setup_code : UniformReciprocalMachine.BlockAt UniformLocalSeedTableMachine.globalSetup program 313 := by
  intro i hi
  have hi23:i<23:=hi
  rw [show 313+i=308+(5+i) by omega,emit_lookup (5+i) (by omega)]
  interval_cases i <;> rfl

theorem emit_offset_code : UniformReciprocalMachine.BlockAt offsetSetup program 336 := by
  intro i hi
  have hi3:i<3:=hi
  rw [show 336+i=308+(28+i) by omega,emit_lookup (28+i) (by omega)]
  interval_cases i <;> rfl

theorem compact_lookup (i : ℕ) (hi:i<120) :
    program[339+i]?=(UniformLocalSeedTableMachine.program.map (relocate 339 459))[i]? := by
  have h:=lookup_segment (head++UniformGlobalLocalPreparation.program.map (relocate 9 308)++emitHead)
    (UniformLocalSeedTableMachine.program.map (relocate 339 459))
    (post.map UniformNewtonTableMachine.Op.code++[.jump 7,.halt]) i
    (by simpa only [List.length_map,UniformLocalSeedTableMachine.program_length] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformGlobalLocalPreparation.program_length,emitHead_length] using h

theorem emit_code : CodeAt UniformLocalSeedTableMachine.program program 339 459 := by
  intro i hi
  rw [compact_lookup i (by simpa only [UniformLocalSeedTableMachine.program_length] using hi),List.getElem?_map]

theorem post_lookup (i : ℕ) (hi:i<8) : program[459+i]?=(post.map UniformNewtonTableMachine.Op.code)[i]? := by
  have h:=lookup_segment (head++UniformGlobalLocalPreparation.program.map (relocate 9 308)++emitHead++
    UniformLocalSeedTableMachine.program.map (relocate 339 459))
    (post.map UniformNewtonTableMachine.Op.code) [.jump 7,.halt] i
    (by simpa only [List.length_map,post_length] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformGlobalLocalPreparation.program_length,emitHead_length,UniformLocalSeedTableMachine.program_length] using h

theorem post_code : UniformNewtonTableMachine.BlockAt post program 459 := by
  intro i hi
  rw [post_lookup i (by simpa only [post_length] using hi),List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some]

theorem final_lookup (i : ℕ) (hi:i<2) : program[467+i]?=([.jump 7,.halt]:Program)[i]? := by
  have h:=lookup_segment (head++UniformGlobalLocalPreparation.program.map (relocate 9 308)++emitHead++
    UniformLocalSeedTableMachine.program.map (relocate 339 459)++post.map UniformNewtonTableMachine.Op.code)
    [.jump 7,.halt] [] i hi
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformGlobalLocalPreparation.program_length,emitHead_length,UniformLocalSeedTableMachine.program_length,
    post_length,List.append_nil] using h

theorem jump_code : program[467]?=some (.jump 7) := by rw [show 467=467+0 by decide,final_lookup 0 (by decide)];rfl
theorem halt_code : program[468]?=some .halt := by rw [show 468=467+1 by decide,final_lookup 1 (by decide)];rfl

theorem local_keeps_driver (i : ℕ) (hi:200 ≤ i) :
    ∀ins ∈ UniformGlobalLocalPreparation.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hh:∀ins ∈ UniformGlobalLocalPreparation.head,UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformGlobalLocalPreparation.head,UniformGlobalLocalPreparation.pointer,
      UniformGlobalLocalPreparation.setup,UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
    omega
  have hc:=UniformReciprocalMachine.keeps_relocate i 29 298
    (UniformGlobalNatPreparation.reciprocal_keeps_high i (by omega))
  have ht:∀ins ∈ ([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformGlobalLocalPreparation.program,embed,UniformGlobalLocalPreparation.head_length,List.append_assoc] using
    UniformReciprocalMachine.keeps_append i (UniformReciprocalMachine.keeps_append i hh hc) ht


theorem compact_keeps_driver (i : ℕ) (hi:200 ≤ i) :
    ∀ins ∈ UniformLocalSeedTableMachine.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hconst:∀ins ∈ UniformLocalSeedTableMachine.constants.map UniformReciprocalMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformLocalSeedTableMachine.constants,UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
    omega
  have hchild:∀ins ∈ UniformLocalSeedTableMachine.Strided.program,UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformLocalSeedTableMachine.Strided.program,UniformNewtonTableMachine.KeepsNat];omega
  have hrows (j:Fin 7):∀ins ∈ ((UniformLocalSeedTableMachine.rowSetup j).map UniformReciprocalMachine.Op.code++
      UniformLocalSeedTableMachine.Strided.program.map
        (relocate (UniformLocalSeedTableMachine.childBase j) (UniformLocalSeedTableMachine.rowEnd j))),
      UniformNewtonTableMachine.KeepsNat i ins:=by
    apply UniformReciprocalMachine.keeps_append i
    · fin_cases j <;> simp [UniformLocalSeedTableMachine.rowSetup,UniformReciprocalMachine.Op.code,
        UniformNewtonTableMachine.KeepsNat] <;> omega
    · exact UniformReciprocalMachine.keeps_relocate i _ _ hchild
  have hflat:∀ins ∈ (List.ofFn fun j:Fin 7=>(UniformLocalSeedTableMachine.rowSetup j).map UniformReciprocalMachine.Op.code++
      UniformLocalSeedTableMachine.Strided.program.map
        (relocate (UniformLocalSeedTableMachine.childBase j) (UniformLocalSeedTableMachine.rowEnd j))).flatten,
      UniformNewtonTableMachine.KeepsNat i ins:=by
    intro ins hins
    obtain ⟨b,hb,hins⟩:=List.mem_flatten.mp hins
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hb
    exact hrows j ins hins
  have ht:∀ins ∈ ([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformLocalSeedTableMachine.program,List.append_assoc] using
    UniformReciprocalMachine.keeps_append i (UniformReciprocalMachine.keeps_append i hconst hflat) ht

structure Retained (n k : ℕ) (s : State) : Prop where
  coefficients : ∀j:Fin (axisCount n),j.val<k → UniformLocalSeedTableMachine.Compact (radix n j)
    (axisBase n j.val) (OAI.ExactFourier.zeta (radix n j)) s
  address : ∀j:Fin (axisCount n),j.val<k → s.natHeap (directoryBase n+2*j.val)=some (axisBase n j.val)
  width : ∀j:Fin (axisCount n),j.val<k → s.natHeap (directoryBase n+2*j.val+1)=some (radix n j)

structure Header (n k : ℕ) (s : State) : Prop where
  index : s.natReg 200=k
  offset : s.natReg 201=prefixSum n k
  count : s.natReg 202=axisCount n
  one : s.natReg 203=1
  directory : s.natReg 204=directoryBase n
  zero : s.natReg 209=0

/-- Protected metadata and both independent permutation banks precede the directory. -/
def ProtectedFrame (n : ℕ) (s u : State) : Prop :=
  (∀i,copyBase n ≤ i → i<directoryBase n → u.natHeap i=s.natHeap i) ∧
  (∀i,i<UniformGlobalLocalPreparation.globalEnd n → u.scalarHeap i=s.scalarHeap i) ∧
  (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders


theorem ProtectedFrame.trans {n : ℕ} {s u v : State} (h:ProtectedFrame n s u) (h':ProtectedFrame n u v) :
    ProtectedFrame n s v := ⟨fun i hi hj=>(h'.1 i hi hj).trans (h.1 i hi hj),
  fun i hi=>(h'.2.1 i hi).trans (h.2.1 i hi),fun i hi hj=>(h'.2.2.1 i hi hj).trans (h.2.2.1 i hi hj),
  h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.trans h.2.2.2.2⟩

theorem ProtectedFrame.metadata {n : ℕ} {s u : State} (h:ProtectedFrame n s u) (hm:Metadata n s) : Metadata n u := by
  apply hm.transport_saved
  · constructor
    · exact (h.2.2.1 100 (by decide) (by decide)).trans hm.saved.nextPrime
    · exact (h.2.2.1 101 (by decide) (by decide)).trans hm.saved.inputLength
    · exact (h.2.2.1 102 (by decide) (by decide)).trans hm.saved.count
    · exact (h.2.2.1 103 (by decide) (by decide)).trans hm.saved.workingLength
    · exact (h.2.2.1 104 (by decide) (by decide)).trans hm.saved.masterRoot
    · exact (h.2.2.1 105 (by decide) (by decide)).trans hm.saved.copyAddress
    · exact (h.2.2.1 106 (by decide) (by decide)).trans hm.saved.copyLength
  · intro a ha
    apply h.1 _ (by omega)
    unfold directoryBase UniformPermutationInversePreparation.inverseBase;omega

theorem ProtectedFrame.operands {n : ℕ} {x : Fin n → ℂ} {s u : State}
    (h:ProtectedFrame n s u) (ho:UniformInitialPreparation.Operands n x s) : UniformInitialPreparation.Operands n x u :=
  UniformGlobalLocalPreparation.operands_transport_below ho h.2.1

theorem ProtectedFrame.beta_inverse {n : ℕ} {s u : State} (h:ProtectedFrame n s u)
    (hb:UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) s.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm) :
    UniformGlobalNatPreparation.PermutationBank (len n)
      (UniformPermutationInversePreparation.inverseBase n) u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm := by
  intro j
  exact (h.1 _ (by unfold UniformPermutationInversePreparation.inverseBase;omega)
    (by unfold directoryBase;have hj:=j.isLt;omega)).trans (hb j)

theorem ProtectedFrame.alpha_copied {n : ℕ} {s u : State} (h:ProtectedFrame n s u) (j : Fin (len n)) :
    u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=
      s.scalarHeap (UniformInputPermutationPreparation.destination n+j.val) :=
  h.2.1 _ (by unfold UniformGlobalLocalPreparation.globalEnd;have hj:=j.isLt;omega)

theorem Header.withPC {n k pc : ℕ} {s : State} (h:Header n k s) : Header n k {s with pc:=pc} := by
  cases h;constructor <;> assumption

theorem Header.transport {n k : ℕ} {s u : State} (h:Header n k s)
    (hh:∀i,200 ≤ i → u.natReg i=s.natReg i) : Header n k u :=
  ⟨(hh _ (by decide)).trans h.index,(hh _ (by decide)).trans h.offset,
    (hh _ (by decide)).trans h.count,(hh _ (by decide)).trans h.one,
    (hh _ (by decide)).trans h.directory,(hh _ (by decide)).trans h.zero⟩

theorem Retained.withPC {n k pc : ℕ} {s : State} (h:Retained n k s) : Retained n k {s with pc:=pc} :=
  ⟨h.coefficients,h.address,h.width⟩

theorem Retained.transport_high {n k : ℕ} {s u : State} (h:Retained n k s)
    (hh:∀i,UniformLocalSeedTableMachine.poolBase n ≤ i → u.scalarHeap i=s.scalarHeap i)
    (hn:∀i,copyBase n ≤ i → u.natHeap i=s.natHeap i) : Retained n k u := by
  constructor
  · intro j hj q l
    exact (hh _ (by unfold axisBase;omega)).trans (h.coefficients j hj q l)
  · intro j hj
    exact (hn _ (by unfold directoryBase UniformPermutationInversePreparation.inverseBase;omega)).trans (h.address j hj)
  · intro j hj
    exact (hn _ (by unfold directoryBase UniformPermutationInversePreparation.inverseBase;omega)).trans (h.width j hj)

theorem compact_address_before {n k : ℕ} (j : Fin (axisCount n)) (hj:j.val<k) (q : Fin 5) (l : Fin (radix n j)) :
    axisBase n j.val+q.val*radix n j+l.val<axisBase n k := by
  have ho:=axisBase_mono n (show j.val+1 ≤ k by omega)
  rw [axisBase_next] at ho
  have hq:q.val*radix n j ≤ 4*radix n j:=Nat.mul_le_mul_right _ (by have h:=q.isLt;omega)
  have hl:=l.isLt
  omega

theorem Retained.transport_before {n k : ℕ} {s u : State} (h:Retained n k s)
    (hh:∀i,i<axisBase n k → u.scalarHeap i=s.scalarHeap i) (hn:u.natHeap=s.natHeap) : Retained n k u := by
  constructor
  · intro j hj q l
    exact (hh _ (compact_address_before j hj q l)).trans (h.coefficients j hj q l)
  · intro j hj;exact (congrFun hn _).trans (h.address j hj)
  · intro j hj;exact (congrFun hn _).trans (h.width j hj)

structure Invariant (n k : ℕ) (x : Fin n → ℂ) (s : State) : Prop where
  header : Header n k s
  metadata : Metadata n s
  operands : UniformInitialPreparation.Operands n x s
  retained : Retained n k s

theorem boot_header {n : ℕ} (s : State) (hm:Metadata n s) :
    Header n 0 (UniformNewtonTableMachine.applyBlock boot s) := by
  constructor <;> simp [UniformNewtonTableMachine.applyBlock,boot,UniformNewtonTableMachine.Op.apply,
    writeNat,next,hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,
    prefix_zero,axisCount,directoryBase,UniformPermutationInversePreparation.inverseBase,Nat.add_comm]

theorem boot_frame (n : ℕ) (s : State) : ProtectedFrame n s (UniformNewtonTableMachine.applyBlock boot s) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  simp (disch:=omega) [UniformNewtonTableMachine.applyBlock,boot,UniformNewtonTableMachine.Op.apply,writeNat,next]

theorem boot_invariant {n : ℕ} {x : Fin n → ℂ} (s : State) (hm:Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) : Invariant n 0 x (UniformNewtonTableMachine.applyBlock boot s) :=
  ⟨boot_header s hm,(boot_frame n s).metadata hm,(boot_frame n s).operands ho,
    ⟨by intro j hj;omega,by intro j hj;omega,by intro j hj;omega⟩⟩

theorem boot_peak {n B : ℕ} (s : State) (hm:Metadata n s)
    (hd:directoryBase n+2*axisCount n ≤ B) (hc:469 ≤ B) : UniformNewtonTableMachine.peak boot s ≤ B := by
  simp [UniformNewtonTableMachine.peak,boot,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,hm.saved.count,hm.saved.copyAddress,
    hm.saved.copyLength,hm.saved.workingLength]
  rw [←directory_after_protected] at hd
  simp only [copyBase] at hd
  unfold axisCount at hd
  omega

/-- Every iteration cost comes from the real local producer and compact copy. -/
def axisCost (n k : ℕ) : ℕ := UniformReciprocalMachine.completeRuntime (radixAt n k)+40*radixAt n k+143

def loopCost (n k : ℕ) : ℕ → ℕ | 0=>0 | f+1=>axisCost n k+loopCost n (k+1) f

theorem loopCost_eq_sum (n k f : ℕ) : loopCost n k f=∑i:Fin f,axisCost n (k+i.val) := by
  induction f generalizing k with
  | zero=>simp [loopCost]
  | succ f ih=>rw [loopCost,Fin.sum_univ_succ,ih];simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_comm,Nat.add_left_comm]


def emittedHeader (s : State) (r : ℕ) : State := UniformReciprocalMachine.applyBlock offsetSetup
  (UniformLocalSeedTableMachine.globalInitialized s r)

theorem emittedHeader_heap (s : State) (r : ℕ) :
    (emittedHeader s r).scalarHeap=s.scalarHeap ∧ (emittedHeader s r).natHeap=s.natHeap ∧
    (emittedHeader s r).outputs=s.outputs ∧ (emittedHeader s r).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩

theorem emittedHeader_nat (s : State) (r i : ℕ) (hi:200 ≤ i) : (emittedHeader s r).natReg i=s.natReg i := by
  simp (disch:=omega) [emittedHeader,offsetSetup,UniformLocalSeedTableMachine.globalInitialized,
    UniformLocalSeedTableMachine.globalLoaded,UniformLocalSeedTableMachine.globalPointer,
    UniformLocalSeedTableMachine.globalSetup,UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,
    writeNat,next]

theorem emittedHeader_saved (s : State) (r i : ℕ) (hi:100 ≤ i) (hj:i ≤ 106) :
    (emittedHeader s r).natReg i=s.natReg i := by
  simp (disch:=omega) [emittedHeader,offsetSetup,UniformLocalSeedTableMachine.globalInitialized,
    UniformLocalSeedTableMachine.globalLoaded,UniformLocalSeedTableMachine.globalPointer,
    UniformLocalSeedTableMachine.globalSetup,UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,
    writeNat,next]

theorem emittedHeader_registers {n k : ℕ} (j : Fin (axisCount n)) (s : State) (hm:Metadata n s)
    (hh:Header n k s) :
    let r:=radix n j
    (emittedHeader s r).natReg 117=r ∧
    (emittedHeader s r).natReg 118=UniformGlobalLocalPreparation.resultBase n r ∧
    (emittedHeader s r).natReg 119=UniformGlobalLocalPreparation.rootSource n r+1 ∧
    (emittedHeader s r).natReg 120=axisBase n k := by
  obtain ⟨h117,h118,h119,h120⟩:=UniformLocalSeedTableMachine.globalInitialized_registers j s hm
  have h201:(UniformLocalSeedTableMachine.globalInitialized s (radix n j)).natReg 201=prefixSum n k:=by
    simp [UniformLocalSeedTableMachine.globalInitialized,UniformLocalSeedTableMachine.globalLoaded,
      UniformLocalSeedTableMachine.globalPointer,UniformLocalSeedTableMachine.globalSetup,
      UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,writeNat,next,hh.offset]
  simp [emittedHeader,offsetSetup,UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,
    writeNat,next,h117,h118,h119,h120,h201,axisBase,Nat.mul_comm]

/-- Actual offset computation; the chosen destination is after all earlier axes. -/
theorem offset_peak {n k B : ℕ} (j : Fin (axisCount n)) (s : State) (hm:Metadata n s) (hh:Header n k s)
    (hk:k ≤ axisCount n) (hB:axisBase n (axisCount n) ≤ B) (hc:469 ≤ B) :
    UniformReciprocalMachine.peak offsetSetup (UniformLocalSeedTableMachine.globalInitialized s (radix n j)) ≤ B := by
  obtain ⟨_,_,_,h120⟩:=UniformLocalSeedTableMachine.globalInitialized_registers j s hm
  have h201:(UniformLocalSeedTableMachine.globalInitialized s (radix n j)).natReg 201=prefixSum n k:=by
    simp [UniformLocalSeedTableMachine.globalInitialized,UniformLocalSeedTableMachine.globalLoaded,
      UniformLocalSeedTableMachine.globalPointer,UniformLocalSeedTableMachine.globalSetup,
      UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,writeNat,next,hh.offset]
  have hb:=axisBase_mono n hk
  simp [UniformReciprocalMachine.peak,offsetSetup,UniformReciprocalMachine.Op.peak,
    UniformReciprocalMachine.Op.apply,writeNat,next,h120,h201]
  unfold axisBase at hb hB
  omega

/-- The actual compact-copy segment after the real local producer. -/
theorem emit_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (axisCount n)) (s : State)
    (hh:Header n j.val s) (hm:Metadata n s) (hret:Retained n j.val s)
    (hp:UniformNewtonTableMachine.PreparedOutputs (radix n j) (OAI.ExactFourier.zeta (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta (radix n j))) s)
    (hpc:s.pc=308) (h110:s.natReg 110=j.val) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (40*radix n j+102) u ∧
    Header n j.val u ∧ Retained n j.val u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (axisBase n j.val) (OAI.ExactFourier.zeta (radix n j)) u ∧
    ProtectedFrame n s u ∧ u.natReg 117=radix n j ∧ u.natReg 120=axisBase n j.val ∧ u.pc=459 := by
  let B:=(n+2)^19
  let r:=radix n j
  obtain ⟨hcode,hpool,hdir⟩:=word_setup hn
  obtain ⟨_,hcopy,_⟩:=UniformGlobalLocalPreparation.word_setup hn j
  obtain ⟨_,hpoolOne⟩:=UniformLocalSeedTableMachine.pool_word_bound hn j
  change UniformLocalSeedTableMachine.poolBase n+5*r ≤ B at hpoolOne
  have hptr:=UniformReciprocalMachine.block_runs UniformLocalSeedTableMachine.globalPointer program 308 n B x s
    emit_pointer_code hpc hs (by change 312 ≤ B;omega) (by trivial)
    (UniformLocalSeedTableMachine.globalPointer_peak j B s hm h110 hcopy (by omega))
  have h312:(UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).pc=312:=by
    rw [UniformReciprocalMachine.applyBlock_pc,hpc];rfl
  have hl:(UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).natHeap
      ((UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).natReg 108)=some r:=by
    rw [UniformLocalSeedTableMachine.globalPointer_address j s hm h110,UniformReciprocalMachine.applyBlock_natHeap]
    exact (hm.crt j).1
  have hloadB:WordBound B (UniformLocalSeedTableMachine.globalLoaded s r):=writeNat_bound B _ 117 r hptr.final_bound
    (by rw [h312];omega) (by omega)
  have hload:BoundedRuns program n x B (UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s)
      1 (UniformLocalSeedTableMachine.globalLoaded s r):=
    .next hptr.final_bound (by simp [step,h312,emit_load_code,hl,UniformLocalSeedTableMachine.globalLoaded]) (.refl hloadB)
  have h313:(UniformLocalSeedTableMachine.globalLoaded s r).pc=313:=by
    simp [UniformLocalSeedTableMachine.globalLoaded,writeNat,next,h312]
  have hsetup:=UniformReciprocalMachine.block_runs UniformLocalSeedTableMachine.globalSetup program 313 n B x
    (UniformLocalSeedTableMachine.globalLoaded s r) emit_setup_code h313 hloadB (by change 336 ≤ B;omega) (by trivial)
    (UniformLocalSeedTableMachine.globalSetup_peak j B s hm hpoolOne (by omega))
  have h336:(UniformLocalSeedTableMachine.globalInitialized s r).pc=336:=
    (UniformReciprocalMachine.applyBlock_pc _ _).trans (by rw [h313];rfl)
  have hoff:=UniformReciprocalMachine.block_runs offsetSetup program 336 n B x
    (UniformLocalSeedTableMachine.globalInitialized s r) emit_offset_code h336 hsetup.final_bound
    (by change 339 ≤ B;omega) (by trivial) (offset_peak j s hm hh (by omega) hpool hcode)
  let z:=emittedHeader s r
  let e:State:={z with pc:=0}
  have heB:WordBound B e:=changePC_bound B z 0 hoff.final_bound (by omega)
  obtain ⟨h117,h118,h119,h120⟩:=emittedHeader_registers j s hm hh
  have heNat:e.natReg=(emittedHeader s r).natReg:=rfl
  have heHeap:e.scalarHeap=(emittedHeader s r).scalarHeap:=rfl
  have he117:e.natReg 117=r:=(congrFun heNat 117).trans h117
  have he118:e.natReg 118=UniformGlobalLocalPreparation.resultBase n r:=(congrFun heNat 118).trans h118
  have he119:e.natReg 119=UniformGlobalLocalPreparation.rootSource n r+1:=(congrFun heNat 119).trans h119
  have he120:e.natReg 120=axisBase n j.val:=(congrFun heNat 120).trans h120
  have heh:e.scalarHeap=s.scalarHeap:=heHeap.trans (emittedHeader_heap s r).1
  have hpe:UniformNewtonTableMachine.PreparedOutputs r (OAI.ExactFourier.zeta r)
      (UniformGlobalLocalPreparation.resultBase n r) e:=by intro i q;exact (congrFun heh _).trans (hp i q)
  have hge:UniformReciprocalMachine.GPrefix r (UniformGlobalLocalPreparation.rootSource n r+1)
      (OAI.ExactFourier.NewtonFourier.invH (OAI.ExactFourier.zeta r)) e:=by intro i hi;exact (congrFun heh _).trans (hg i hi)
  obtain ⟨ha,hG⟩:=UniformLocalSeedTableMachine.selected_source_bounds n j
  change UniformGlobalLocalPreparation.resultBase n r+8*r+5 ≤ UniformLocalSeedTableMachine.poolBase n at ha
  change UniformGlobalLocalPreparation.rootSource n r+1+r ≤ UniformLocalSeedTableMachine.poolBase n at hG
  have hA:UniformLocalSeedTableMachine.poolBase n ≤ axisBase n j.val:=by unfold axisBase;omega
  have hAB:axisBase n j.val+5*r ≤ B:=by
    rw [←axisBase_next]
    exact (axisBase_mono n (by have h:=j.isLt;omega)).trans hpool
  obtain ⟨u,hu,hcompact,houtside,hframe,hpu⟩:=UniformLocalSeedTableMachine.execution_from_local n x r
    (UniformGlobalLocalPreparation.resultBase n r) (UniformGlobalLocalPreparation.rootSource n r+1)
    (axisBase n j.val) B (OAI.ExactFourier.zeta r) e (UniformGlobalLocalPreparation.radix_pos n j)
    (ha.trans hA) (hG.trans hA) hAB (by omega) hpe hge rfl he117 he118 he119 he120 heB
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed emit_code
    (by rw [UniformLocalSeedTableMachine.program_length];omega :339+UniformLocalSeedTableMachine.program.length ≤ B)
    (by omega :459 ≤ B) hu
  have hz:z.pc=339:=(UniformReciprocalMachine.applyBlock_pc offsetSetup _).trans (by rw [h336];rfl)
  have heq:placed 339 e=z:=by change {z with pc:=339}=z;rw [←hz]
  rw [heq] at hplaced
  let final:State:={u with pc:=459}
  have hNat:final.natHeap=s.natHeap:=hframe.1.1.trans (emittedHeader_heap s r).2.1
  have hScalar:∀i,i<axisBase n j.val → final.scalarHeap i=s.scalarHeap i:=by
    intro i hi;exact (houtside i (Or.inl hi)).trans (congrFun heh i)
  have hf:ProtectedFrame n s final:=by
    refine ⟨fun i _ _=>congrFun hNat i,?_,?_,?_,?_⟩
    · intro i hi
      exact hScalar i (by unfold axisBase UniformLocalSeedTableMachine.poolBase;omega)
    · intro i hi hiu
      exact (hframe.2 i (Or.inl (by omega)) (by omega)).trans (emittedHeader_saved s r i hi hiu)
    · exact hframe.1.2.1.trans (emittedHeader_heap s r).2.2.1
    · exact hframe.1.2.2.1.trans (emittedHeader_heap s r).2.2.2
  have hhf:Header n j.val final:=hh.transport (fun i hi=>
    (UniformNewtonTableMachine.Executes.keeps_nat hu.executes (compact_keeps_driver i hi)).trans
      (emittedHeader_nat s r i hi))
  refine ⟨final,?_,hhf,hret.transport_before hScalar hNat,hcompact,hf,?_,?_,rfl⟩
  · convert ((hptr.trans hload).trans hsetup).trans hoff |>.trans hplaced using 1
    change 40*r+102=4+1+23+3+(40*r+71);omega
  · exact (hframe.2 117 (Or.inl (by decide)) (by decide)).trans he117
  · exact (hframe.2 120 (Or.inl (by decide)) (by decide)).trans he120


def afterPost (s : State) : State := UniformNewtonTableMachine.applyBlock post s

theorem post_header {n : ℕ} (j : Fin (axisCount n)) (s : State) (hh:Header n j.val s)
    (h117:s.natReg 117=radix n j) : Header n (j.val+1) (afterPost s) := by
  constructor
  · simp [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next,hh.index,hh.one]
  · simp [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next,hh.offset,h117,prefix_succ,radixAt_eq]
  · simpa [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next] using hh.count
  · simpa [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next] using hh.one
  · simpa [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next] using hh.directory
  · simpa [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next] using hh.zero

theorem post_heap {n : ℕ} (j : Fin (axisCount n)) (s : State) (hh:Header n j.val s)
    (h117:s.natReg 117=radix n j) (h120:s.natReg 120=axisBase n j.val) :
    (afterPost s).natHeap=Function.update
      (Function.update s.natHeap (directoryBase n+2*j.val) (some (axisBase n j.val)))
      (directoryBase n+2*j.val+1) (some (radix n j)) := by
  simp [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
    writeNat,next,hh.index,hh.one,hh.directory,h117,h120,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm]

theorem post_frame {n : ℕ} (j : Fin (axisCount n)) (s : State) (hh:Header n j.val s)
    (h117:s.natReg 117=radix n j) (h120:s.natReg 120=axisBase n j.val) : ProtectedFrame n s (afterPost s) := by
  refine ⟨?_,fun _ _=>rfl,?_,rfl,rfl⟩
  · intro i hi hj
    rw [post_heap j s hh h117 h120,Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  · intro i hi hj
    simp (disch:=omega) [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
      writeNat,next]

theorem post_retained {n : ℕ} (j : Fin (axisCount n)) (s : State) (hh:Header n j.val s)
    (h117:s.natReg 117=radix n j) (h120:s.natReg 120=axisBase n j.val) (hr:Retained n j.val s)
    (hc:UniformLocalSeedTableMachine.Compact (radix n j) (axisBase n j.val) (OAI.ExactFourier.zeta (radix n j)) s) :
    Retained n (j.val+1) (afterPost s) := by
  constructor
  · intro i hi
    by_cases he:i.val=j.val
    · have heq:i=j:=Fin.ext he
      subst i;exact hc
    · exact hr.coefficients i (by omega)
  · intro i hi
    rw [post_heap j s hh h117 h120]
    by_cases he:i.val=j.val
    · have heq:i=j:=Fin.ext he
      subst i;simp
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hr.address i (by omega)
  · intro i hi
    rw [post_heap j s hh h117 h120]
    by_cases he:i.val=j.val
    · have heq:i=j:=Fin.ext he
      subst i;simp
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hr.width i (by omega)

theorem post_peak {n B : ℕ} (j : Fin (axisCount n)) (s : State) (hh:Header n j.val s)
    (h117:s.natReg 117=radix n j) (h120:s.natReg 120=axisBase n j.val)
    (hc:469 ≤ B) (hA:axisBase n (axisCount n) ≤ B) (hd:directoryBase n+2*axisCount n ≤ B) :
    UniformNewtonTableMachine.peak post s ≤ B := by
  have hj:=j.isLt
  have hprefix:=axisBase_mono n (show j.val+1 ≤ axisCount n by omega)
  rw [axisBase_next] at hprefix
  have hr:=UniformGlobalLocalPreparation.radix_pos n j
  have hpsum:=prefix_bound n (axisCount n) (le_refl _)
  simp [UniformNewtonTableMachine.peak,post,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,hh.index,hh.offset,hh.one,hh.directory,h117,h120]
  unfold axisBase at hA hprefix
  dsimp only [axisBase]
  omega


def axisState (s : State) : State := writeNat {s with pc:=8} 110 (s.natReg 200+s.natReg 209)

theorem axis_frame (n : ℕ) (s : State) : ProtectedFrame n s (axisState s) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  simp [axisState,writeNat,next,show i ≠ 110 by omega]

theorem axis_invariant {n k : ℕ} {x : Fin n → ℂ} {s : State} (h:Invariant n k x s) : Invariant n k x (axisState s) := by
  refine ⟨h.header.transport ?_,(axis_frame n s).metadata h.metadata,(axis_frame n s).operands h.operands,?_⟩
  · intro i hi;simp [axisState,writeNat,next,show i ≠ 110 by omega]
  · exact ⟨h.retained.coefficients,h.retained.address,h.retained.width⟩

/-- One real loop iteration prepares a selected root's local banks, copies them
past all retained axes, writes its directory row, and advances both counters. -/
theorem iteration {n k : ℕ} (hn:0<n) (x : Fin n → ℂ) (s : State) (hi:Invariant n k x s)
    (hk:k<axisCount n) (hpc:s.pc=7) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (axisCost n k) u ∧
    Invariant n (k+1) x u ∧ ProtectedFrame n s u ∧ u.pc=7 := by
  let j:Fin (axisCount n):=⟨k,hk⟩
  let r:=radix n j
  let B:=(n+2)^19
  obtain ⟨hcode,hpool,hdir⟩:=word_setup hn
  have hb:WordBound B {s with pc:=8}:=changePC_bound B s 8 hs (by omega)
  have hkB:k ≤ B:=by simpa only [hi.header.index] using hs.2.1 200
  have ha:WordBound B (axisState s):=writeNat_bound B {s with pc:=8} 110 _ hb
    (by change 9 ≤ B;omega) (by rw [hi.header.index,hi.header.zero];omega)
  have hbefore:BoundedRuns program n x B s 2 (axisState s):=by
    refine .next hs ?_ (.next hb ?_ (.refl ha))
    · simp [step,hpc,branch_code,hi.header.index,hi.header.count,hk]
    · simp [step,axis_code,axisState,evalNat]
  let a:=axisState s
  have hai:Invariant n k x a:=axis_invariant hi
  let e:State:={a with pc:=0}
  have heB:WordBound B e:=changePC_bound B a 0 ha (by omega)
  have hmE:Metadata n e:=hai.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hoE:UniformInitialPreparation.Operands n x e:=hai.operands.transport rfl
  have h110:e.natReg 110=j.val:=by simp [e,a,axisState,writeNat,next,hi.header.index,hi.header.zero,j]
  obtain ⟨v,hv,hmv,hov,hp,hg,hroot,hfv,hpv⟩:=UniformGlobalLocalPreparation.preparation_execution_budget
    hn x j e hmE hoE rfl h110 heB
  have hhigh:=UniformLocalSeedTableMachine.local_execution_high_pool_budget hn x j e v hmE hoE rfl h110 heB hv
  have hDriver:∀i,200 ≤ i → v.natReg i=e.natReg i:=fun i hi=>
    UniformNewtonTableMachine.Executes.keeps_nat hv.executes (local_keeps_driver i hi)
  have hvHeader:Header n k v:=hai.header.transport hDriver
  have hvRetained:Retained n k v:=hai.retained.transport_high hhigh hfv.2.1
  have hlocalFrame:ProtectedFrame n a v:=⟨fun i hi _=>hfv.2.1 i hi,hfv.1,hfv.2.2.1,hfv.2.2.2.1,hfv.2.2.2.2⟩
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed local_code
    (by rw [UniformGlobalLocalPreparation.program_length];omega :9+UniformGlobalLocalPreparation.program.length ≤ B)
    (by omega :308 ≤ B) hv
  have hae:placed 9 e=a:=by change {a with pc:=9}=a;rfl
  rw [hae] at hplaced
  let w:State:={v with pc:=308}
  have hmw:Metadata n w:=hmv.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have h110w:w.natReg 110=j.val:=by
    have hkeep:∀ins ∈ UniformGlobalLocalPreparation.program,UniformNewtonTableMachine.KeepsNat 110 ins:=by
      have hhead:∀ins ∈ UniformGlobalLocalPreparation.head,UniformNewtonTableMachine.KeepsNat 110 ins:=by
        simp [UniformGlobalLocalPreparation.head,UniformGlobalLocalPreparation.pointer,
          UniformGlobalLocalPreparation.setup,UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
      have hc:=UniformReciprocalMachine.keeps_relocate 110 29 298
        (UniformGlobalNatPreparation.reciprocal_keeps_high 110 (by decide))
      have ht:∀ins ∈ ([.halt]:Program),UniformNewtonTableMachine.KeepsNat 110 ins:=by simp [UniformNewtonTableMachine.KeepsNat]
      simpa only [UniformGlobalLocalPreparation.program,embed,UniformGlobalLocalPreparation.head_length,List.append_assoc] using
        UniformReciprocalMachine.keeps_append 110 (UniformReciprocalMachine.keeps_append 110 hhead hc) ht
    exact (UniformNewtonTableMachine.Executes.keeps_nat hv.executes hkeep).trans h110
  obtain ⟨u,hu,hhu,hru,hcu,hfu,h117,h120,hpu⟩:=emit_execution hn x j w hvHeader.withPC hmw hvRetained.withPC hp hg
    rfl h110w hplaced.final_bound
  have hpost:=UniformNewtonTableMachine.block_runs post program 459 n B x u post_code hpu hu.final_bound
    (by change 467 ≤ B;omega) (by trivial) (post_peak j u hhu h117 h120 hcode hpool hdir)
  let z:=afterPost u
  let final:State:={z with pc:=7}
  have hz:WordBound B z:=hpost.final_bound
  have hfB:WordBound B final:=changePC_bound B z 7 hz (by omega)
  have hpz:z.pc=467:=(UniformNewtonTableMachine.applyBlock_pc post u).trans (by rw [hpu,post_length])
  have hstep:step program n x z=.running final:=by simp [step,hpz,jump_code,final]
  have hjump:BoundedRuns program n x B z 1 final:=.next hz hstep (.refl hfB)
  have hpostFr:=post_frame j u hhu h117 h120
  have hFr:ProtectedFrame n s final:=(axis_frame n s).trans (hlocalFrame.trans (hfu.trans hpostFr))
  have hInv:Invariant n (k+1) x final:=
    ⟨(post_header j u hhu h117).withPC,(hpostFr.metadata (hfu.metadata hmw)).transport (fun _ _=>rfl) (fun _ _=>rfl),
      (hpostFr.operands (hfu.operands (hov.transport rfl))).transport rfl, (post_retained j u hhu h117 h120 hru hcu).withPC⟩
  refine ⟨final,?_,hInv,hFr,rfl⟩
  convert (((hbefore.trans hplaced).trans hu).trans hpost).trans hjump using 1
  change axisCost n k=2+(UniformReciprocalMachine.completeRuntime r+30)+(40*r+102)+8+1
  unfold axisCost
  rw [show radixAt n k=r from radixAt_eq n j]
  omega


/-- Literal machine loop; no host iteration or preprinted compact table. -/
theorem loop {n k f : ℕ} (hn:0<n) (x : Fin n → ℂ) (s : State) (hi:Invariant n k x s)
    (hk:k+f=axisCount n) (hpc:s.pc=7) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (loopCost n k f) u ∧
    Invariant n (axisCount n) x u ∧ ProtectedFrame n s u ∧ u.pc=7 := by
  induction f generalizing k s with
  | zero=>
    have he:k=axisCount n:=by omega
    subst k
    exact ⟨s,.refl hs,hi,⟨fun _ _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩,hpc⟩
  | succ f ih=>
    obtain ⟨u,hu,hiu,hfu,hpu⟩:=iteration hn x s hi (by omega) hpc hs
    obtain ⟨v,hv,hiv,hfv,hpv⟩:=ih (k:=k+1) u hiu (by omega) hpu hu.final_bound
    exact ⟨v,hu.trans hv,hiv,hfu.trans hfv,hpv⟩

def preparationRuntime (n : ℕ) : ℕ := 9+loopCost n 0 (axisCount n)

def preparationBudget (n : ℕ) : ℕ := 9+∑j:Fin (axisCount n),
  (494*(radix n j)^2+40*radix n j+113)

theorem runtime_bound (n : ℕ) : preparationRuntime n ≤ preparationBudget n := by
  unfold preparationRuntime preparationBudget
  apply Nat.add_le_add_left
  rw [loopCost_eq_sum]
  apply Finset.sum_le_sum
  intro j _
  unfold axisCost
  simp only [Nat.zero_add,radixAt_eq]
  have h:=UniformGlobalLocalPreparation.runtime_quadratic n j
  change UniformReciprocalMachine.completeRuntime (radix n j)+30 ≤ 494*(radix n j)^2 at h
  omega

theorem budget_polynomial (n : ℕ) :
    preparationBudget n ≤ 9+axisCount n*(494*(len n)^2+40*len n+113) := by
  unfold preparationBudget
  apply Nat.add_le_add_left
  calc (∑j:Fin (axisCount n), (494*(radix n j)^2+40*radix n j+113)) ≤ ∑_j:Fin (axisCount n),(494*(len n)^2+40*len n+113) := by
        apply Finset.sum_le_sum
        intro j _
        have hr:radix n j ≤ len n:=UniformGlobalLocalPreparation.radix_le_length n j
        have hsq:(radix n j)^2 ≤ (len n)^2:=Nat.pow_le_pow_left hr 2
        omega
       _ = axisCount n*(494*(len n)^2+40*len n+113) := by simp

/-- All selected axes are actually prepared, copied and indexed under the same
ambient polynomial word bound. Local working banks may overlap; retained pools do not. -/
theorem execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (s : State) (hm:Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s) (hpc:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s (preparationRuntime n) u ∧
    Retained n (axisCount n) u ∧ Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    ProtectedFrame n s u ∧ u.pc=468 ∧ preparationRuntime n ≤ preparationBudget n := by
  obtain ⟨hc,hpool,hdir⟩:=word_setup hn
  have hboot:=UniformNewtonTableMachine.block_runs boot program 0 n ((n+2)^19) x s boot_code hpc hs
    (by change 7 ≤ (n+2)^19;omega) (by trivial) (boot_peak s hm hdir hc)
  let z:=UniformNewtonTableMachine.applyBlock boot s
  have h7:z.pc=7:=(UniformNewtonTableMachine.applyBlock_pc boot s).trans (by rw [hpc,boot_length])
  obtain ⟨v,hv,hiv,hfv,hpv⟩:=loop (k:=0) (f:=axisCount n) hn x z (boot_invariant s hm ho) (by omega) h7 hboot.final_bound
  let final:State:={v with pc:=468}
  have hfB:WordBound ((n+2)^19) final:=changePC_bound _ v 468 hv.final_bound (by omega)
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=.halt hfB (by simp [step,final,halt_code])
  have hfinish:BoundedExecution program n x ((n+2)^19) v 2 final:=by
    refine .next hv.final_bound ?_ hhalt
    simp [step,hpv,branch_code,hiv.header.index,hiv.header.count,final]
  refine ⟨final,?_,hiv.retained.withPC,hiv.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),
    hiv.operands.transport rfl,(boot_frame n s).trans hfv,rfl,runtime_bound n⟩
  convert hboot.executes (hv.executes hfinish) using 1
  change preparationRuntime n=7+(loopCost n 0 (axisCount n)+2)
  unfold preparationRuntime;omega

/-- Actual directory entries are complete and point to the corresponding five
prepared scalar lanes, for every selected axis including a unit binary factor. -/
theorem retained_complete {n : ℕ} {s : State} (h:Retained n (axisCount n) s) (j : Fin (axisCount n)) :
    s.natHeap (directoryBase n+2*j.val)=some (axisBase n j.val) ∧
    s.natHeap (directoryBase n+2*j.val+1)=some (radix n j) ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (axisBase n j.val) (OAI.ExactFourier.zeta (radix n j)) s :=
  ⟨h.address j j.isLt,h.width j j.isLt,h.coefficients j j.isLt⟩


/-- Closed empty-state composition: actualstartup465, allaxis469, final halt. -/
def fullHead : Program := UniformPermutationInversePreparation.program.map (relocate 0 465)
def fullProgram : Program := embed fullHead program [.halt] 934

theorem fullHead_length : fullHead.length=465 := by simp only [fullHead,List.length_map,UniformPermutationInversePreparation.program_length]
theorem fullProgram_length : fullProgram.length=935 := by rw [fullProgram,embed_length,fullHead_length,program_length];rfl

theorem startup_code : CodeAt UniformPermutationInversePreparation.program fullProgram 0 465 := by
  intro i hi
  have hi465:i<465:=by simpa only [UniformPermutationInversePreparation.program_length] using hi
  change (fullHead++program.map (relocate 465 934)++[.halt])[0+i]?=_
  rw [List.getElem?_append_left (by simp only [List.length_append,fullHead_length,List.length_map,program_length];omega)]
  rw [List.getElem?_append_left (by rw [fullHead_length];omega)]
  simp only [fullHead,Nat.zero_add,List.getElem?_map]

theorem driver_code : CodeAt program fullProgram 465 934 := by
  simpa only [fullProgram,fullHead_length] using embed_code fullHead program [.halt] 934

theorem full_halt : fullProgram[934]?=some .halt := by
  simp only [fullProgram,embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,fullHead_length,List.length_map,program_length];omega)]
  simp [fullHead_length,program_length]

def fullBudget (n : ℕ) : ℕ := UniformPermutationInversePreparation.preparationBudget n+preparationBudget n+1

theorem full_word_bound {n : ℕ} (hn:0<n) : 935 ≤ (n+2)^19 := by
  have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 19
  norm_num at h;omega

/-- One fixed program, starting from empty heaps, produces all retained selected
axis seeds and their directory. Global chirps/input/kernel/normalization, actual
alpha gather, independent beta inverse and the single original master root remain. -/
theorem initial_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) : ∃t u,
    BoundedExecution fullProgram n x ((n+2)^19) initial (t+preparationRuntime n+1) u ∧
    t ≤ UniformPermutationInversePreparation.preparationBudget n ∧
    Retained n (axisCount n) u ∧ Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some
      (UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
        (UniformCRTTraversalCycle.alphaPermutation n j).val)) ∧
    UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
      u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.pc=934 ∧ t+preparationRuntime n+1 ≤ fullBudget n := by
  obtain ⟨t,v,hv,hm,ho,hinput,hbeta,hroots,houtputs,hpc,hcost⟩:=UniformPermutationInversePreparation.preparation_execution hn x
  have hbig:=full_word_bound hn
  have hstart:=UniformBoundedAssembly.boundedExecution_placed startup_code
    (by rw [UniformPermutationInversePreparation.program_length];omega :0+UniformPermutationInversePreparation.program.length ≤ (n+2)^19)
    (by omega :465 ≤ (n+2)^19) hv
  change BoundedRuns fullProgram n x ((n+2)^19) initial t {v with pc:=465} at hstart
  let e:State:={v with pc:=0}
  have hme:Metadata n e:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hoe:UniformInitialPreparation.Operands n x e:=ho.transport rfl
  obtain ⟨u,hu,hret,hmu,hou,hframe,hpu,hbound⟩:=execution hn x e hme hoe rfl
    (changePC_bound _ v 0 hv.final_bound (by omega))
  have htail:=UniformBoundedAssembly.boundedExecution_placed driver_code
    (by rw [program_length];omega :465+program.length ≤ (n+2)^19) (by omega :934 ≤ (n+2)^19) hu
  have heq:placed 465 e={v with pc:=465}:=rfl
  rw [heq] at htail
  let final:State:={u with pc:=934}
  have hhalt:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=.halt htail.final_bound
    (by simp [step,final,full_halt])
  have hb:UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
      e.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm:=hbeta
  refine ⟨t,final,?_,hcost,hret.withPC,hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,
    ?_,hframe.beta_inverse hb,hframe.2.2.2.2.trans hroots,hframe.2.2.2.1.trans houtputs,rfl,?_⟩
  · exact hstart.executes (htail.executes hhalt)
  · intro j;exact (hframe.alpha_copied j).trans (hinput j)
  · unfold fullBudget;omega

end
end ExactFourierCircuits.UniformAllAxisSeedPreparation
