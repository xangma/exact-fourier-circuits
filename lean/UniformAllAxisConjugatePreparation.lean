import UniformSeedConjugateRetention
import UniformScalarCopyMachine
import UniformAllAxisSeedCost

set_option autoImplicit false
namespace ExactFourierCircuits.UniformAllAxisConjugatePreparation
open UniformMachine UniformAssembly
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
namespace N
abbrev Op := UniformNewtonTableMachine.Op
end N

def boot : List N.Op := [.literal 1700 0,.literal 1701 0,.literal 1702 1,
  .literal 1703 2,.literal 1704 5,.add 1705 102 1702,
  .add 1706 105 106,.add 1706 1706 103,
  .mul 1707 1705 1703,.add 1707 1706 1707,.literal 1708 0,.add 1709 1247 1708]
def head : Program := UniformSeedConjugatePreparation.boot ++ boot.map UniformNewtonTableMachine.Op.code ++
  [.branchLT 1700 1705 28 523,.natBinary .add 110 1700 1708]
def pointer : List N.Op := [.mul 1710 1700 1703,.add 1710 1706 1710,.add 1710 1710 1702]
def copySetup : List N.Op := [.mul 147 1711 1704,.add 148 1709 1708,
  .mul 1712 103 1704,.add 1712 1709 1712,.mul 1713 1701 1704,.add 149 1712 1713]
def post : List N.Op := [.mul 1714 1700 1703,.add 1714 1707 1714,
  .putNat 1714 149,.add 1714 1714 1702,.putNat 1714 1711,
  .add 1701 1701 1711,.add 1700 1700 1702]
def program : Program := head ++ UniformSeedConjugatePreparation.program.map (relocate 29 495) ++
  pointer.map UniformNewtonTableMachine.Op.code ++ [.loadNat 1711 1710] ++
  copySetup.map UniformNewtonTableMachine.Op.code ++
  UniformScalarCopyMachine.program.map (relocate 505 515) ++
  post.map UniformNewtonTableMachine.Op.code ++ [.jump 27,.halt]

theorem head_length : head.length=29 := rfl
theorem program_length : program.length=524 := by
  simp only [program,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,UniformScalarCopyMachine.program_length]
  rfl
theorem boot_code : UniformNewtonTableMachine.BlockAt boot program 15 := by
  intro i hi
  change i < 12 at hi
  interval_cases i <;> rfl
theorem branch_code : program[27]?=some (.branchLT 1700 1705 28 523) := rfl
theorem axis_code : program[28]?=some (.natBinary .add 110 1700 1708) := rfl
theorem selected_code : CodeAt UniformSeedConjugatePreparation.program program 29 495 := by
  intro i hi
  have h:=UniformAllAxisSeedPreparation.lookup_segment head
    (UniformSeedConjugatePreparation.program.map (relocate 29 495))
    (pointer.map UniformNewtonTableMachine.Op.code ++ [.loadNat 1711 1710] ++
      copySetup.map UniformNewtonTableMachine.Op.code ++
      UniformScalarCopyMachine.program.map (relocate 505 515) ++
      post.map UniformNewtonTableMachine.Op.code ++ [.jump 27,.halt]) i
    (by simpa only [List.length_map] using hi)
  simpa only [program,List.append_assoc,head_length,List.getElem?_map] using h

noncomputable section
def pool (n : ℕ) : ℕ := UniformSeedConjugatePreparation.destination n+5*len n
def axisBase (n k : ℕ) : ℕ := pool n+5*UniformAllAxisSeedPreparation.prefixSum n k
def directoryBase (n : ℕ) : ℕ := UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n
theorem axisBase_zero (n : ℕ) : axisBase n 0=pool n := rfl
theorem axisBase_next (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    axisBase n (j.val+1)=axisBase n j.val+5*UniformAllAxisSeedPreparation.radix n j := by
  unfold axisBase
  rw [UniformAllAxisSeedPreparation.prefix_succ,UniformAllAxisSeedPreparation.radixAt_eq]
  omega
theorem axisBase_mono (n : ℕ) {a b : ℕ} (h:a   ≤   b) : axisBase n a   ≤   axisBase n b := by
  have hp:=UniformAllAxisSeedPreparation.prefix_mono n h
  unfold axisBase
  omega
theorem scalar_temporary_before (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    UniformSeedConjugatePreparation.destination n+5*UniformAllAxisSeedPreparation.radix n j   ≤   pool n := by
  have hr:=UniformGlobalLocalPreparation.radix_le_length n j
  change UniformAllAxisSeedPreparation.radix n j  ≤  len n at hr
  unfold pool
  omega
theorem original_directory_before (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    UniformAllAxisSeedPreparation.directoryBase n+2*j.val+1 < directoryBase n := by
  have hj:=j.isLt
  unfold directoryBase
  omega
theorem compact_address_before {n k : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (hj:j.val < k)
    (q : Fin 5) (l : Fin (UniformAllAxisSeedPreparation.radix n j)) :
    axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+l.val < axisBase n k := by
  have he:=axisBase_mono n (show j.val+1   ≤   k by omega)
  rw [axisBase_next] at he
  have hq:=Nat.mul_le_mul_right (UniformAllAxisSeedPreparation.radix n j) (show q.val   ≤   4 by omega)
  have hl:=l.isLt
  omega
theorem word_setup {n : ℕ} (hn:0 < n) : 524   ≤   (n+2)^19    ∧
    axisBase n (UniformAllAxisSeedPreparation.axisCount n)   ≤   (n+2)^19    ∧
    directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n   ≤   (n+2)^19 := by
  have he:ell n   ≤   2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount
    omega
  have hL:len n < 4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:=UniformAllAxisSeedPreparation.prefix_bound n (UniformAllAxisSeedPreparation.axisCount n) (le_refl _)
  have hprod:(ell n+1)*len n   ≤   (2*n+1)*(4*n):=Nat.mul_le_mul (by omega) (by omega)
  have hsmall:1000   ≤   (n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3   ≤   n+2 by omega) 17
    norm_num at h
    omega
  have hb:1000*(n+2)^2   ≤   (n+2)^19:=by
    rw [show 19=17+2 by decide,pow_add]
    exact Nat.mul_le_mul_right ((n+2)^2) hsmall
  have hpool:axisBase n (UniformAllAxisSeedPreparation.axisCount n)   ≤   1000*(n+2)^2:=by
    dsimp only [axisBase,pool,UniformSeedConjugatePreparation.destination,
      UniformSeedConjugatePreparation.O.axisBase,UniformSeedConjugatePreparation.O.axisCount,
      UniformAllAxisSeedPreparation.axisBase,UniformLocalSeedTableMachine.poolBase]
    rw [UniformGlobalLocalPreparation.globalEnd_formula]
    change UniformAllAxisSeedPreparation.prefixSum n (ell n+1)   ≤   (ell n+1)*len n at hp
    nlinarith
  have hdir:directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n   ≤   1000*(n+2)^2:=by
    dsimp only [directoryBase]
    rw [UniformAllAxisSeedPreparation.directory_formula]
    unfold UniformAllAxisSeedPreparation.axisCount
    nlinarith
  exact ⟨by nlinarith,hpool.trans hb,hdir.trans hb⟩

structure Header (n k : ℕ) (s : State) : Prop where
  index : s.natReg 1700=k
  offset : s.natReg 1701=UniformAllAxisSeedPreparation.prefixSum n k
  one : s.natReg 1702=1
  two : s.natReg 1703=2
  five : s.natReg 1704=5
  count : s.natReg 1705=UniformAllAxisSeedPreparation.axisCount n
  originalDirectory : s.natReg 1706=UniformAllAxisSeedPreparation.directoryBase n
  directory : s.natReg 1707=directoryBase n
  zero : s.natReg 1708=0
  temporary : s.natReg 1709=UniformSeedConjugatePreparation.destination n
theorem Header.withPC {n k pc : ℕ} {s : State} (h:Header n k s) : Header n k {s with pc:=pc} := by
  cases h
  constructor <;> assumption
theorem Header.transport {n k : ℕ} {s u : State} (h:Header n k s)
    (hn:∀i,1700   ≤   i   →   u.natReg i=s.natReg i) : Header n k u :=
  ⟨(hn _ (by omega)).trans h.index,(hn _ (by omega)).trans h.offset,
    (hn _ (by omega)).trans h.one,(hn _ (by omega)).trans h.two,
    (hn _ (by omega)).trans h.five,(hn _ (by omega)).trans h.count,
    (hn _ (by omega)).trans h.originalDirectory,(hn _ (by omega)).trans h.directory,
    (hn _ (by omega)).trans h.zero,(hn _ (by omega)).trans h.temporary⟩
structure Retained (n k : ℕ) (s : State) : Prop where
  coefficients : ∀j:Fin (UniformAllAxisSeedPreparation.axisCount n),j.val < k   →   UniformLocalSeedTableMachine.Compact
    (UniformAllAxisSeedPreparation.radix n j) (axisBase n j.val) (UniformSeedConjugatePreparation.axisRoot (UniformAllAxisSeedPreparation.radix n j)) s
  address : ∀j:Fin (UniformAllAxisSeedPreparation.axisCount n),j.val < k   →   s.natHeap (directoryBase n+2*j.val)=some (axisBase n j.val)
  width : ∀j:Fin (UniformAllAxisSeedPreparation.axisCount n),j.val < k   →   s.natHeap (directoryBase n+2*j.val+1)=some (UniformAllAxisSeedPreparation.radix n j)
theorem Retained.withPC {n k pc : ℕ} {s : State} (h:Retained n k s) : Retained n k {s with pc:=pc} :=
  ⟨h.coefficients,h.address,h.width⟩
theorem Retained.transport {n k : ℕ} {s u : State} (h:Retained n k s)
    (hc:∀i,pool n   ≤   i   →   i < axisBase n k   →   u.scalarHeap i=s.scalarHeap i)
    (hn:u.natHeap=s.natHeap) : Retained n k u := by
  refine ⟨?_,?_,?_⟩
  · intro j hj q l
    exact (hc _ (by unfold axisBase;omega) (compact_address_before j hj q l)).trans (h.coefficients j hj q l)
  · intro j hj
    exact (congrFun hn _).trans (h.address j hj)
  · intro j hj
    exact (congrFun hn _).trans (h.width j hj)

/-- Original protected metadata and its original directory remain; local
Newton scratch below copyBase is deliberately outside this frame. -/
def Frame (n : ℕ) (s u : State) : Prop :=
  (∀i,copyBase n   ≤   i   →   i < directoryBase n   →   u.natHeap i=s.natHeap i)    ∧
  (∀i,i < UniformGlobalLocalPreparation.globalEnd n   →   u.scalarHeap i=s.scalarHeap i)    ∧
  (∀i,100   ≤   i   →   i   ≤   106   →   u.natReg i=s.natReg i)    ∧   u.outputs=s.outputs    ∧   u.rootOrders=s.rootOrders
theorem Frame.trans {n : ℕ} {s u v : State} (h:Frame n s u) (h':Frame n u v) : Frame n s v :=
  ⟨fun i hi hj=>(h'.1 i hi hj).trans (h.1 i hi hj),
    fun i hi=>(h'.2.1 i hi).trans (h.2.1 i hi),
    fun i hi hj=>(h'.2.2.1 i hi hj).trans (h.2.2.1 i hi hj),
    h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.trans h.2.2.2.2⟩
theorem Frame.protected {n : ℕ} {s u : State} (h:Frame n s u) :
    UniformAllAxisSeedPreparation.ProtectedFrame n s u := by
  refine ⟨?_,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  intro i hi hj
  exact h.1 i hi (by unfold directoryBase;omega)
theorem Frame.metadata {n : ℕ} {s u : State} (h:Frame n s u) (hm:Metadata n s) : Metadata n u :=
  h.protected.metadata hm
theorem Frame.operands {n : ℕ} {x : Fin n   →   ℂ} {s u : State} (h:Frame n s u)
    (ho:UniformInitialPreparation.Operands n x s) : UniformInitialPreparation.Operands n x u :=
  h.protected.operands ho

structure Invariant (n k : ℕ) (x : Fin n   →   ℂ) (s : State) : Prop where
  header : Header n k s
  metadata : Metadata n s
  operands : UniformInitialPreparation.Operands n x s
  original : UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s
  retained : Retained n k s

theorem pointer_lookup (i : ℕ) (hi:i < 3) : program[495+i]?=(pointer.map UniformNewtonTableMachine.Op.code)[i]? := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495))
    (pointer.map UniformNewtonTableMachine.Op.code)
    ([.loadNat 1711 1710]++copySetup.map UniformNewtonTableMachine.Op.code++
      UniformScalarCopyMachine.program.map (relocate 505 515)++post.map UniformNewtonTableMachine.Op.code++[.jump 27,.halt]) i hi
  simpa only [program,List.append_assoc,List.length_append,List.length_map,
    head_length,UniformSeedConjugatePreparation.program_length] using h
theorem pointer_code : UniformNewtonTableMachine.BlockAt pointer program 495 := by
  intro i hi
  rw [pointer_lookup i hi,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
theorem load_width_code : program[498]?=some (.loadNat 1711 1710) := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495)++pointer.map UniformNewtonTableMachine.Op.code)
    [.loadNat 1711 1710]
    (copySetup.map UniformNewtonTableMachine.Op.code++UniformScalarCopyMachine.program.map (relocate 505 515)++
      post.map UniformNewtonTableMachine.Op.code++[.jump 27,.halt]) 0 (by decide)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,pointer,List.length_cons,List.length_nil,Nat.reduceAdd,List.getElem?_cons_zero] using h
theorem setup_lookup (i : ℕ) (hi:i < 6) : program[499+i]?=(copySetup.map UniformNewtonTableMachine.Op.code)[i]? := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495)++pointer.map UniformNewtonTableMachine.Op.code++[.loadNat 1711 1710])
    (copySetup.map UniformNewtonTableMachine.Op.code)
    (UniformScalarCopyMachine.program.map (relocate 505 515)++post.map UniformNewtonTableMachine.Op.code++[.jump 27,.halt]) i hi
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,pointer,List.length_cons,List.length_nil,Nat.reduceAdd] using h
theorem setup_code : UniformNewtonTableMachine.BlockAt copySetup program 499 := by
  intro i hi
  rw [setup_lookup i hi,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
theorem copy_code : CodeAt UniformScalarCopyMachine.program program 505 515 := by
  intro i hi
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495)++pointer.map UniformNewtonTableMachine.Op.code++
      [.loadNat 1711 1710]++copySetup.map UniformNewtonTableMachine.Op.code)
    (UniformScalarCopyMachine.program.map (relocate 505 515))
    (post.map UniformNewtonTableMachine.Op.code++[.jump 27,.halt]) i (by simpa only [List.length_map] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,pointer,copySetup,List.length_cons,
    List.length_nil,Nat.reduceAdd,List.getElem?_map] using h
theorem post_lookup (i : ℕ) (hi:i < 7) : program[515+i]?=(post.map UniformNewtonTableMachine.Op.code)[i]? := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495)++pointer.map UniformNewtonTableMachine.Op.code++
      [.loadNat 1711 1710]++copySetup.map UniformNewtonTableMachine.Op.code++UniformScalarCopyMachine.program.map (relocate 505 515))
    (post.map UniformNewtonTableMachine.Op.code) [.jump 27,.halt] i hi
  simpa only [program,List.append_assoc,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,UniformScalarCopyMachine.program_length,
    pointer,copySetup,List.length_cons,List.length_nil,Nat.reduceAdd] using h
theorem post_code : UniformNewtonTableMachine.BlockAt post program 515 := by
  intro i hi
  rw [post_lookup i hi,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some]
theorem final_lookup (i : ℕ) (hi:i < 2) : program[522+i]?=([.jump 27,.halt]:Program)[i]? := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (head++UniformSeedConjugatePreparation.program.map (relocate 29 495)++pointer.map UniformNewtonTableMachine.Op.code++
      [.loadNat 1711 1710]++copySetup.map UniformNewtonTableMachine.Op.code++UniformScalarCopyMachine.program.map (relocate 505 515)++
      post.map UniformNewtonTableMachine.Op.code) [.jump 27,.halt] [] i hi
  simpa only [program,List.append_assoc,List.append_nil,List.length_append,List.length_map,head_length,
    UniformSeedConjugatePreparation.program_length,UniformScalarCopyMachine.program_length,
    pointer,copySetup,post,List.length_cons,List.length_nil,Nat.reduceAdd] using h
theorem jump_code : program[522]?=some (.jump 27) := by
  rw [show 522=522+0 by decide,final_lookup 0 (by decide)]
  rfl
theorem halt_code : program[523]?=some .halt := by
  rw [show 523=522+1 by decide,final_lookup 1 (by decide)]
  rfl

theorem boot_header {n : ℕ} (s : State) (hm:Metadata n s)
    (hd:s.natReg 1247=UniformSeedConjugatePreparation.destination n) :
    Header n 0 (UniformNewtonTableMachine.applyBlock boot s) := by
  constructor <;> simp [UniformNewtonTableMachine.applyBlock,boot,UniformNewtonTableMachine.Op.apply,
    writeNat,next,hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,
    hd,directoryBase,UniformAllAxisSeedPreparation.directoryBase,UniformPermutationInversePreparation.inverseBase,
    UniformAllAxisSeedPreparation.prefix_zero,UniformAllAxisSeedPreparation.axisCount,Nat.add_comm,Nat.mul_comm]
theorem boot_frame (n : ℕ) (s : State) : Frame n s (UniformNewtonTableMachine.applyBlock boot s) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  simp (disch:=omega) [UniformNewtonTableMachine.applyBlock,boot,UniformNewtonTableMachine.Op.apply,writeNat,next]
theorem boot_peak {n B : ℕ} (s : State) (hm:Metadata n s)
    (hd:directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n  ≤  B) (_hc:524  ≤  B)
    (ht:s.natReg 1247 ≤ B) :
    UniformNewtonTableMachine.peak boot s  ≤  B := by
  simp [UniformNewtonTableMachine.peak,boot,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,hm.saved.count,hm.saved.copyAddress,
    hm.saved.copyLength,hm.saved.workingLength]
  unfold directoryBase at hd
  rw [←UniformAllAxisSeedPreparation.directory_after_protected] at hd
  unfold UniformAllAxisSeedPreparation.axisCount copyBase at hd
  omega
theorem boot_invariant {n : ℕ} {x : Fin n  →  ℂ} (s : State) (hm:Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s)
    (hd:s.natReg 1247=UniformSeedConjugatePreparation.destination n)
    (hr:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s) :
    Invariant n 0 x (UniformNewtonTableMachine.applyBlock boot s) := by
  refine ⟨boot_header s hm hd,(boot_frame n s).metadata hm,(boot_frame n s).operands ho,?_,?_⟩
  · exact hr.transport_high (fun _ _=>rfl) (fun _ _=>rfl)
  · exact ⟨by intro j hj;omega,by intro j hj;omega,by intro j hj;omega⟩

theorem compact_source {r d : ℕ} {omega : ℂ} {s : State} (hr:0 < r)
    (hc:UniformLocalSeedTableMachine.Compact r d omega s) : UniformScalarCopyMachine.Source (5*r) d s.scalarHeap := by
  intro i hi
  let q:Fin 5:=⟨i/r,(Nat.div_lt_iff_lt_mul hr).mpr (by omega)⟩
  let j:Fin r:=⟨i%r,Nat.mod_lt _ hr⟩
  refine ⟨UniformPairMachine.prepared (UniformLocalSeedTableMachine.seedValue omega q j.val),?_⟩
  have h:=hc q j
  have he:q.val*r+j.val=i:=by dsimp [q,j];simpa only [Nat.mul_comm] using Nat.div_add_mod i r
  simpa only [←he,Nat.add_assoc] using h

theorem compact_copied {r a d : ℕ} {omega : ℂ} {s u : State}
    (hc:UniformLocalSeedTableMachine.Compact r a omega s)
    (hh:∀i,i < 5*r  →  u.scalarHeap (d+i)=s.scalarHeap (a+i)) :
    UniformLocalSeedTableMachine.Compact r d omega u := by
  intro q j
  have hi:q.val*r+j.val < 5*r:=by
    have hq:=Nat.mul_le_mul_right r (show q.val  ≤  4 by omega)
    have hj:=j.isLt
    omega
  have he : u.scalarHeap (d+q.val*r+j.val)=s.scalarHeap (a+q.val*r+j.val) :=
    by simpa only [Nat.add_assoc] using hh _ hi
  exact he.trans (hc q j)

theorem Header.transport_fields {n k : ℕ} {s u : State} (h:Header n k s)
    (hh:∀i,1700  ≤  i  →  i  ≤  1709  →  u.natReg i=s.natReg i) : Header n k u :=
  ⟨(hh _ (by omega) (by omega)).trans h.index,(hh _ (by omega) (by omega)).trans h.offset,
    (hh _ (by omega) (by omega)).trans h.one,(hh _ (by omega) (by omega)).trans h.two,
    (hh _ (by omega) (by omega)).trans h.five,(hh _ (by omega) (by omega)).trans h.count,
    (hh _ (by omega) (by omega)).trans h.originalDirectory,(hh _ (by omega) (by omega)).trans h.directory,
    (hh _ (by omega) (by omega)).trans h.zero,(hh _ (by omega) (by omega)).trans h.temporary⟩

def pointed (s : State) := UniformNewtonTableMachine.applyBlock pointer s
def loadedWidth (s : State) (r : ℕ) := writeNat (pointed s) 1711 r
def readyCopy (s : State) (r : ℕ) := UniformNewtonTableMachine.applyBlock copySetup (loadedWidth s r)
theorem readyCopy_heap (s : State) (r : ℕ) :
    (readyCopy s r).scalarHeap=s.scalarHeap   ∧  (readyCopy s r).natHeap=s.natHeap   ∧
    (readyCopy s r).outputs=s.outputs   ∧  (readyCopy s r).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩
theorem readyCopy_nat (s : State) (r i : ℕ) (hi:1700  ≤  i) (hj:i  ≤  1709) :
    (readyCopy s r).natReg i=s.natReg i := by
  simp (disch:=omega) [readyCopy,loadedWidth,pointed,UniformNewtonTableMachine.applyBlock,
    pointer,copySetup,UniformNewtonTableMachine.Op.apply,writeNat,next]
theorem readyCopy_frame (n : ℕ) (s : State) (r : ℕ) : Frame n s (readyCopy s r) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  simp (disch:=omega) [readyCopy,loadedWidth,pointed,UniformNewtonTableMachine.applyBlock,
    pointer,copySetup,UniformNewtonTableMachine.Op.apply,writeNat,next]
theorem readyCopy_registers {n k : ℕ} (s : State) (r : ℕ) (hh:Header n k s)
    (hm:Metadata n s) :
    (readyCopy s r).natReg 147=5*r   ∧
    (readyCopy s r).natReg 148=UniformSeedConjugatePreparation.destination n   ∧
    (readyCopy s r).natReg 149=axisBase n k   ∧
    (readyCopy s r).natReg 1711=r := by
  simp [readyCopy,loadedWidth,pointed,UniformNewtonTableMachine.applyBlock,
    pointer,copySetup,UniformNewtonTableMachine.Op.apply,writeNat,next,
    hh.five,hh.zero,hh.offset,hh.temporary,hm.saved.workingLength,pool,axisBase,Nat.mul_comm,Nat.add_assoc]

theorem copy_setup_execution {n : ℕ} (hn:0 < n) (x : Fin n  →  ℂ)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hm:Metadata n s)
    (hr:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (hpc:s.pc=495) (hs:WordBound ((n+2)^19) s) :
    BoundedRuns program n x ((n+2)^19) s 10 (readyCopy s (UniformAllAxisSeedPreparation.radix n j))   ∧
    (readyCopy s (UniformAllAxisSeedPreparation.radix n j)).pc=505 := by
  let B:=(n+2)^19
  let r:=UniformAllAxisSeedPreparation.radix n j
  obtain ⟨hcode,hpool,hdir⟩:=word_setup hn
  have hcurrent:=axisBase_mono n (show j.val+1  ≤  UniformAllAxisSeedPreparation.axisCount n by omega)
  rw [axisBase_next] at hcurrent
  have hrL:r  ≤  len n:=UniformGlobalLocalPreparation.radix_le_length n j
  have ht:=scalar_temporary_before n j
  have hp:=UniformNewtonTableMachine.block_runs pointer program 495 n B x s pointer_code hpc hs
    (by change 498  ≤  B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,pointer,UniformNewtonTableMachine.Op.peak,
        UniformNewtonTableMachine.Op.apply,writeNat,next,hh.index,hh.two,hh.one,hh.originalDirectory]
      have hj:=j.isLt
      unfold directoryBase at hdir
      omega)
  have hpointed:(pointed s).pc=498:=
    (UniformNewtonTableMachine.applyBlock_pc pointer s).trans (by rw [hpc];rfl)
  have haddress:(pointed s).natReg 1710=UniformAllAxisSeedPreparation.directoryBase n+2*j.val+1:=by
    simp [pointed,UniformNewtonTableMachine.applyBlock,pointer,UniformNewtonTableMachine.Op.apply,
      writeNat,next,hh.index,hh.two,hh.one,hh.originalDirectory,Nat.mul_comm]
  have hread:(pointed s).natHeap ((pointed s).natReg 1710)=some r:=by
    rw [haddress]
    exact hr.width j j.isLt
  have hb:WordBound B (loadedWidth s r):=writeNat_bound B (pointed s) 1711 r hp.final_bound
    (by rw [hpointed];omega) (by unfold axisBase pool at hpool;omega)
  have hl:BoundedRuns program n x B (pointed s) 1 (loadedWidth s r):=
    .next hp.final_bound (by simp [step,hpointed,load_width_code,hread,loadedWidth]) (.refl hb)
  have hloaded:(loadedWidth s r).pc=499:=by simp [loadedWidth,writeNat,next,hpointed]
  have hc:=UniformNewtonTableMachine.block_runs copySetup program 499 n B x (loadedWidth s r)
    setup_code hloaded hb (by change 505  ≤  B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,copySetup,UniformNewtonTableMachine.Op.peak,
        UniformNewtonTableMachine.Op.apply,loadedWidth,pointed,UniformNewtonTableMachine.applyBlock,
        pointer,writeNat,next,hh.five,hh.zero,hh.offset,hh.temporary,hm.saved.workingLength]
      dsimp only [axisBase,pool] at hpool hcurrent ht
      omega)
  refine ⟨?_,?_⟩
  · convert (hp.trans hl).trans hc using 1 <;> rfl
  · exact (UniformNewtonTableMachine.applyBlock_pc copySetup (loadedWidth s r)).trans (by rw [hloaded];rfl)

def afterPost (s : State) := UniformNewtonTableMachine.applyBlock post s
theorem post_heap {n : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j)
    (ha:s.natReg 149=axisBase n j.val) :
    (afterPost s).natHeap=Function.update
      (Function.update s.natHeap (directoryBase n+2*j.val) (some (axisBase n j.val)))
      (directoryBase n+2*j.val+1) (some (UniformAllAxisSeedPreparation.radix n j)) := by
  simp [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,
    writeNat,next,hh.index,hh.two,hh.one,hh.directory,hr,ha,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm]
theorem post_header {n : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j) :
    Header n (j.val+1) (afterPost s) := by
  constructor <;> simp [afterPost,UniformNewtonTableMachine.applyBlock,post,
    UniformNewtonTableMachine.Op.apply,writeNat,next,hh.index,hh.offset,hh.one,hh.two,
    hh.five,hh.count,hh.originalDirectory,hh.directory,hh.zero,hh.temporary,hr,
    UniformAllAxisSeedPreparation.prefix_succ,UniformAllAxisSeedPreparation.radixAt_eq]
theorem post_frame {n : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j)
    (ha:s.natReg 149=axisBase n j.val) : Frame n s (afterPost s) := by
  refine ⟨?_,fun _ _=>rfl,?_,rfl,rfl⟩
  · intro i hi hj
    rw [post_heap j s hh hr ha,Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
  · intro i hi hj
    simp (disch:=omega) [afterPost,UniformNewtonTableMachine.applyBlock,post,UniformNewtonTableMachine.Op.apply,writeNat,next]
theorem post_original {n : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j)
    (ha:s.natReg 149=axisBase n j.val)
    (ho:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s) :
    UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) (afterPost s) := by
  refine ⟨ho.coefficients,?_,?_⟩
  · intro i hi
    rw [post_heap j s hh hr ha,Function.update_of_ne (by have h:=original_directory_before n i;omega),
      Function.update_of_ne (by have h:=original_directory_before n i;omega)]
    exact ho.address i hi
  · intro i hi
    rw [post_heap j s hh hr ha,Function.update_of_ne (by have h:=original_directory_before n i;omega),
      Function.update_of_ne (by have h:=original_directory_before n i;omega)]
    exact ho.width i hi
theorem post_retained {n : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j)
    (ha:s.natReg 149=axisBase n j.val) (ho:Retained n j.val s)
    (hc:UniformLocalSeedTableMachine.Compact (UniformAllAxisSeedPreparation.radix n j)
      (axisBase n j.val) (UniformSeedConjugatePreparation.axisRoot (UniformAllAxisSeedPreparation.radix n j)) s) :
    Retained n (j.val+1) (afterPost s) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    by_cases he:i.val=j.val
    · have h:i=j:=Fin.ext he
      subst i
      exact hc
    · exact ho.coefficients i (by omega)
  · intro i hi
    rw [post_heap j s hh hr ha]
    by_cases he:i.val=j.val
    · have h:i=j:=Fin.ext he
      subst i
      simp
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact ho.address i (by omega)
  · intro i hi
    rw [post_heap j s hh hr ha]
    by_cases he:i.val=j.val
    · have h:i=j:=Fin.ext he
      subst i
      simp
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact ho.width i (by omega)
theorem post_peak {n B : ℕ} (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (s : State)
    (hh:Header n j.val s) (hr:s.natReg 1711=UniformAllAxisSeedPreparation.radix n j)
    (ha:s.natReg 149=axisBase n j.val) (_hc:524  ≤  B)
    (hA:axisBase n (UniformAllAxisSeedPreparation.axisCount n)  ≤  B)
    (hd:directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n  ≤  B) :
    UniformNewtonTableMachine.peak post s  ≤  B := by
  have hp:=axisBase_mono n (show j.val+1  ≤  UniformAllAxisSeedPreparation.axisCount n by omega)
  rw [axisBase_next] at hp
  have hj:=j.isLt
  have hprefix:=UniformAllAxisSeedPreparation.prefix_bound n (UniformAllAxisSeedPreparation.axisCount n) (le_refl _)
  simp [UniformNewtonTableMachine.peak,post,UniformNewtonTableMachine.Op.peak,
    UniformNewtonTableMachine.Op.apply,writeNat,next,hh.index,hh.offset,hh.one,hh.two,hh.directory,hr,ha]
  dsimp only [axisBase] at hp hA ⊢
  omega

theorem initial_bootPrefix_code : UniformNewtonTableMachine.BlockAt
    UniformSeedConjugatePreparation.bootPrefix program 0 := by
  intro i hi
  change i < 9 at hi
  interval_cases i <;> rfl
theorem initial_load_base_code : program[9]?=some (.loadNat 1247 1246) := rfl
theorem initial_bootMiddle_code : UniformNewtonTableMachine.BlockAt
    UniformSeedConjugatePreparation.bootMiddle program 10 := by
  intro i hi
  change i < 1 at hi
  interval_cases i
  rfl
theorem initial_load_width_code : program[11]?=some (.loadNat 1248 1246) := rfl
theorem initial_bootSuffix_code : UniformNewtonTableMachine.BlockAt
    UniformSeedConjugatePreparation.bootSuffix program 12 := by
  intro i hi
  change i < 3 at hi
  interval_cases i <;> rfl

theorem initial_boot_execution {n : ℕ} (hn:0 < n) (x : Fin n → ℂ) (j : Fin (UniformSeedConjugatePreparation.O.axisCount n)) (s : State)
    (hm:Metadata n s) (hr:UniformSeedConjugatePreparation.O.Retained n (UniformSeedConjugatePreparation.O.axisCount n) s)
    (hpc:s.pc=0) (hs:WordBound ((n+2)^19) s) :
    BoundedRuns program n x ((n+2)^19) s 15 (UniformSeedConjugatePreparation.bootState n s) := by
  let B:=(n+2)^19
  obtain ⟨hc,hpool,hdir⟩:=UniformSeedConjugatePreparation.word_setup hn j
  have hl:0 < len n:=UniformWorkingLength.workingLength_pos hn
  have hlast:UniformSeedConjugatePreparation.O.axisBase n (UniformSeedConjugatePreparation.lastAxis n).val  ≤  UniformSeedConjugatePreparation.destination n:=
    UniformAllAxisSeedPreparation.axisBase_mono n (Nat.le_of_lt (UniformSeedConjugatePreparation.lastAxis n).isLt)
  have hrLast:UniformSeedConjugatePreparation.radix n (UniformSeedConjugatePreparation.lastAxis n)  ≤  len n:=UniformConjugateLocalPreparation.radix_le_length n (UniformSeedConjugatePreparation.lastAxis n)
  have hL:len n  ≤  B:=by rw [←hm.saved.workingLength];exact hs.2.1 103
  have hp:=UniformNewtonTableMachine.block_runs UniformSeedConjugatePreparation.bootPrefix program 0 n B x s initial_bootPrefix_code hpc hs
    (by change 9  ≤  B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,UniformSeedConjugatePreparation.bootPrefix,UniformNewtonTableMachine.Op.peak,UniformNewtonTableMachine.Op.apply,writeNat,next,
        hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength]
      change UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n  ≤  _ at hdir
      rw [←UniformAllAxisSeedPreparation.directory_after_protected] at hdir
      unfold UniformAllAxisSeedPreparation.axisCount at hdir
      unfold copyBase at hdir
      omega)
  have hp9:(UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootPrefix s).pc=9:=
    (UniformNewtonTableMachine.applyBlock_pc _ _).trans (by rw [hpc,UniformSeedConjugatePreparation.bootPrefix_length])
  have hload:(UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootPrefix s).natHeap
      ((UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootPrefix s).natReg 1246)=some (UniformSeedConjugatePreparation.O.axisBase n (UniformSeedConjugatePreparation.lastAxis n).val):=by
    rw [UniformSeedConjugatePreparation.boot_address s hm,UniformNewtonTableMachine.applyBlock_natHeap _ _ (by simp [UniformSeedConjugatePreparation.bootPrefix,UniformNewtonTableMachine.NatHeapFree])]
    exact hr.address (UniformSeedConjugatePreparation.lastAxis n) (UniformSeedConjugatePreparation.lastAxis n).isLt
  have hb:WordBound B (UniformSeedConjugatePreparation.firstLoaded n s):=writeNat_bound B _ 1247 _ hp.final_bound
    (by rw [hp9];omega) (by omega)
  have hfirst:BoundedRuns program n x B (UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootPrefix s) 1 (UniformSeedConjugatePreparation.firstLoaded n s):=
    .next hp.final_bound (by simp [step,hp9,initial_load_base_code,hload,UniformSeedConjugatePreparation.firstLoaded]) (.refl hb)
  have hp10:(UniformSeedConjugatePreparation.firstLoaded n s).pc=10:=by simp [UniformSeedConjugatePreparation.firstLoaded,writeNat,next,hp9]
  have hmrun:=UniformNewtonTableMachine.block_runs UniformSeedConjugatePreparation.bootMiddle program 10 n B x (UniformSeedConjugatePreparation.firstLoaded n s)
    initial_bootMiddle_code hp10 hb (by change 11  ≤  B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,UniformSeedConjugatePreparation.bootMiddle,UniformNewtonTableMachine.Op.peak,
        UniformSeedConjugatePreparation.firstLoaded,writeNat,next,UniformSeedConjugatePreparation.boot_address s hm,UniformSeedConjugatePreparation.boot_one]
      have ht: (UniformSeedConjugatePreparation.lastAxis n).val < UniformSeedConjugatePreparation.O.axisCount n :=(UniformSeedConjugatePreparation.lastAxis n).isLt
      omega)
  have hp11:(UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootMiddle (UniformSeedConjugatePreparation.firstLoaded n s)).pc=11:=
    (UniformNewtonTableMachine.applyBlock_pc _ _).trans (by rw [hp10,UniformSeedConjugatePreparation.bootMiddle_length])
  have hw:(UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootMiddle (UniformSeedConjugatePreparation.firstLoaded n s)).natHeap
      ((UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootMiddle (UniformSeedConjugatePreparation.firstLoaded n s)).natReg 1246)=some (UniformSeedConjugatePreparation.radix n (UniformSeedConjugatePreparation.lastAxis n)):=by
    rw [UniformSeedConjugatePreparation.middle_address s hm]
    exact hr.width (UniformSeedConjugatePreparation.lastAxis n) (UniformSeedConjugatePreparation.lastAxis n).isLt
  have hwB:WordBound B (UniformSeedConjugatePreparation.secondLoaded n s):=writeNat_bound B _ 1248 _ hmrun.final_bound
    (by rw [hp11];omega) (by omega)
  have hsecond:BoundedRuns program n x B (UniformNewtonTableMachine.applyBlock UniformSeedConjugatePreparation.bootMiddle (UniformSeedConjugatePreparation.firstLoaded n s))
      1 (UniformSeedConjugatePreparation.secondLoaded n s):=.next hmrun.final_bound
        (by simp [step,hp11,initial_load_width_code,hw,UniformSeedConjugatePreparation.secondLoaded]) (.refl hwB)
  have hp12:(UniformSeedConjugatePreparation.secondLoaded n s).pc=12:=by simp [UniformSeedConjugatePreparation.secondLoaded,writeNat,next,hp11]
  have hsuffix:=UniformNewtonTableMachine.block_runs UniformSeedConjugatePreparation.bootSuffix program 12 n B x (UniformSeedConjugatePreparation.secondLoaded n s)
    initial_bootSuffix_code hp12 hwB (by change 15  ≤  B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,UniformSeedConjugatePreparation.bootSuffix,UniformNewtonTableMachine.Op.peak,UniformNewtonTableMachine.Op.apply,
        UniformSeedConjugatePreparation.secondLoaded,UniformSeedConjugatePreparation.firstLoaded,UniformNewtonTableMachine.applyBlock,UniformSeedConjugatePreparation.bootMiddle,writeNat,next]
      rw [Nat.mul_comm,←UniformSeedConjugatePreparation.destination_tail]
      omega)
  convert (((hp.trans hfirst).trans hmrun).trans hsecond).trans hsuffix using 1 <;> rfl

theorem copy_before_directory (n : ℕ) : copyBase n ≤ directoryBase n := by
  unfold directoryBase
  rw [←UniformAllAxisSeedPreparation.directory_after_protected]
  omega
theorem Retained.transport_high {n k : ℕ} {s u : State} (h:Retained n k s)
    (hc:∀i,pool n ≤ i → u.scalarHeap i=s.scalarHeap i)
    (hn:∀i,directoryBase n ≤ i → u.natHeap i=s.natHeap i) : Retained n k u := by
  refine ⟨?_,?_,?_⟩
  · intro j hj q l
    exact (hc _ (by unfold axisBase;omega)).trans (h.coefficients j hj q l)
  · intro j hj
    exact (hn _ (by omega)).trans (h.address j hj)
  · intro j hj
    exact (hn _ (by omega)).trans (h.width j hj)

def axisState (s : State) := writeNat {s with pc:=28} 110 (s.natReg 1700+s.natReg 1708)
theorem axis_frame (n : ℕ) (s : State) : Frame n s (axisState s) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  simp [axisState,writeNat,next,show i ≠ 110 by omega]
theorem axis_invariant {n k : ℕ} {x : Fin n → ℂ} {s : State} (h:Invariant n k x s) :
    Invariant n k x (axisState s) := by
  refine ⟨h.header.transport ?_,(axis_frame n s).metadata h.metadata,
    (axis_frame n s).operands h.operands,?_,?_⟩
  · intro i hi
    simp [axisState,writeNat,next,show i ≠ 110 by omega]
  · exact h.original.transport_high (fun _ _=>rfl) (fun _ _=>rfl)
  · exact h.retained.transport_high (fun _ _=>rfl) (fun _ _=>rfl)

def axisCost (n k : ℕ) : ℕ := UniformReciprocalMachine.completeRuntime
  (UniformAllAxisSeedPreparation.radixAt n k)+75*UniformAllAxisSeedPreparation.radixAt n k+172
def loopCost (n k : ℕ) : ℕ → ℕ
 | 0=>0
 | f+1=>axisCost n k+loopCost n (k+1) f

theorem axisCost_step (n : ℕ) (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    axisCost n j.val=2+(UniformReciprocalMachine.completeRuntime (UniformAllAxisSeedPreparation.radix n j)+
      40*UniformAllAxisSeedPreparation.radix n j+148)+10+
      (7*(5*UniformAllAxisSeedPreparation.radix n j)+4)+(post.length+1) := by
  unfold axisCost
  rw [UniformAllAxisSeedPreparation.radixAt_eq]
  change _=2+(_+40*_+148)+10+(7*(5*_)+4)+(7+1)
  omega

/-- The source of the stable copy is derived from actual466 output, never an
entry readiness certificate. Every directory write and continuation is charged. -/
theorem iteration {n k : ℕ} (hn:0 < n) (x : Fin n → ℂ) (s : State)
    (hi:Invariant n k x s) (hk:k < UniformAllAxisSeedPreparation.axisCount n)
    (hpc:s.pc=27) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (axisCost n k) u  ∧
    Invariant n (k+1) x u  ∧ Frame n s u  ∧ u.pc=27  ∧
    (∀i,axisBase n (UniformAllAxisSeedPreparation.axisCount n) ≤ i → u.scalarHeap i=s.scalarHeap i) := by
  let j:Fin (UniformAllAxisSeedPreparation.axisCount n):=⟨k,hk⟩
  let r:=UniformAllAxisSeedPreparation.radix n j
  let B:=(n+2)^19
  obtain ⟨hcode,hpool,hdir⟩:=word_setup hn
  have hb:WordBound B {s with pc:=28}:=changePC_bound B s 28 hs (by omega)
  have ha:WordBound B (axisState s):=writeNat_bound B {s with pc:=28} 110 _ hb
    (by change 29 ≤ B;omega) (by have h:=hs.2.1 1700; rw [hi.header.index] at h; simpa [hi.header.index,hi.header.zero,B] using h)
  have start:BoundedRuns program n x B s 2 (axisState s):=by
    refine .next hs ?_ (.next hb ?_ (.refl ha))
    · simp [step,hpc,branch_code,hi.header.index,hi.header.count,hk]
    · simp [step,axisState,axis_code,evalNat]
  let a:=axisState s
  have hai:=axis_invariant hi
  let e:State:={a with pc:=0}
  have heB:=changePC_bound B a 0 ha (by omega)
  have h110:e.natReg 110=j.val:=by
    simp [e,a,axisState,writeNat,next,hi.header.index,hi.header.zero,j]
  obtain ⟨v,hv,hcompact,_,hmv,hov,horig,hfv,hhigh,hpv⟩:=
    UniformSeedConjugateRetention.execution hn x j e
      (hai.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl))
      (hai.operands.transport rfl) hai.original.withPC rfl h110 heB
  have hheader:Header n k v:=hai.header.transport
    (fun i hh=>UniformSeedConjugateRetention.driver_frame hv i (by omega))
  have hnew:Retained n k v:=hai.retained.transport_high
    (fun i hh=>hhigh i ((scalar_temporary_before n j).trans hh))
    (fun i hh=>hfv.1.2.1 i ((copy_before_directory n).trans hh))
  have selectedFrame:Frame n a v:=
    ⟨fun i hh _=>hfv.1.2.1 i hh,hfv.1.1,hfv.1.2.2.1,hfv.1.2.2.2.1,hfv.1.2.2.2.2⟩
  have selected:=UniformBoundedAssembly.boundedExecution_placed selected_code
    (by rw [UniformSeedConjugatePreparation.program_length];omega :29+UniformSeedConjugatePreparation.program.length ≤ B)
    (by omega :495 ≤ B) hv
  have heq:placed 29 e=a:=rfl
  rw [heq] at selected
  let w:State:={v with pc:=495}
  have hwmeta:Metadata n w:=hmv.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hworig:=horig.withPC (pc:=495)
  obtain ⟨setup,hsetupPC⟩:=copy_setup_execution hn x j w hheader.withPC hwmeta hworig rfl selected.final_bound
  let z:=readyCopy w r
  have hregs:=readyCopy_registers w r hheader.withPC hwmeta
  have hzheader:Header n k z:=hheader.withPC.transport_fields (readyCopy_nat w r)
  have hzcompact:UniformLocalSeedTableMachine.Compact r (UniformSeedConjugatePreparation.destination n)
      (UniformSeedConjugatePreparation.axisRoot r) z:=by
    intro q l
    exact hcompact q l
  have hzret:Retained n k z:=hnew.transport_high (fun _ _=>rfl) (fun _ _=>rfl)
  have hzorig:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) z:=hworig.transport_high (fun _ _=>rfl) (fun _ _=>rfl)
  let ce:State:={z with pc:=0}
  obtain ⟨u,hu,hcopied,_,houtside,hcf,hnf⟩:=UniformScalarCopyMachine.execution n x (5*r)
    (UniformSeedConjugatePreparation.destination n) (axisBase n k) B ce
    (compact_source (UniformGlobalLocalPreparation.radix_pos n j) hzcompact)
    ((scalar_temporary_before n j).trans (by unfold axisBase;omega))
    (by have h:=axisBase_mono n (show k+1 ≤ UniformAllAxisSeedPreparation.axisCount n by omega)
        change axisBase n (j.val+1) ≤ _ at h
        rw [axisBase_next] at h
        exact h.trans hpool)
    (by omega) rfl hregs.1 hregs.2.1 hregs.2.2.1
    (changePC_bound B z 0 setup.final_bound (by omega))
  have huc:UniformLocalSeedTableMachine.Compact r (axisBase n k)
      (UniformSeedConjugatePreparation.axisRoot r) u:=compact_copied hzcompact hcopied
  have hur:Retained n k u:=hzret.transport
    (fun i _ hh=>houtside i (Or.inl hh)) hcf.1
  have huo:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u:=
    hzorig.transport_before
      (fun i hh=>houtside i (Or.inl (by
        change i < UniformSeedConjugatePreparation.destination n at hh
        unfold axisBase pool
        omega))) hcf.1
  have huh:Header n k u:=hzheader.transport (fun i hh=>hnf i (Or.inr (by omega)))
  have hu149:u.natReg 149=axisBase n k:=
    (UniformNewtonTableMachine.Executes.keeps_nat hu.executes (by
      simp [UniformScalarCopyMachine.program,UniformNewtonTableMachine.KeepsNat])).trans hregs.2.2.1
  have hu1711:u.natReg 1711=r:=(hnf 1711 (Or.inr (by omega))).trans hregs.2.2.2
  have copyFrame:Frame n z u:=by
    refine ⟨fun i _ _=>congrFun hcf.1 i,?_,?_,hcf.2.1,hcf.2.2.1⟩
    · intro i hh
      have hp:=UniformSeedConjugatePreparation.pool_before_destination n
      unfold UniformLocalSeedTableMachine.poolBase at hp
      exact houtside i (Or.inl (by unfold axisBase pool;omega))
    · intro i hh hh'
      exact hnf i (Or.inl (by omega))
  have copied:=UniformBoundedAssembly.boundedExecution_placed copy_code
    (by rw [UniformScalarCopyMachine.program_length];omega :505+UniformScalarCopyMachine.program.length ≤ B)
    (by omega :515 ≤ B) hu
  have ceq:placed 505 ce=z:=by change {z with pc:=505}=z;rw [←hsetupPC]
  rw [ceq] at copied
  let q:State:={u with pc:=515}
  have posts:=UniformNewtonTableMachine.block_runs post program 515 n B x q post_code rfl copied.final_bound
    (by change 522 ≤ B;omega) (by trivial)
    (post_peak j q huh.withPC hu1711 hu149 hcode hpool hdir)
  let final:State:={afterPost q with pc:=27}
  have hpq:(afterPost q).pc=522:=(UniformNewtonTableMachine.applyBlock_pc post q).trans (by rfl)
  have hfinal:=changePC_bound B (afterPost q) 27 posts.final_bound (by omega)
  have jump:BoundedRuns program n x B (afterPost q) 1 final:=
    .next posts.final_bound (by simp [step,hpq,jump_code,final]) (.refl hfinal)
  have before:Frame n s q:=(axis_frame n s).trans
    (selectedFrame.trans ((readyCopy_frame n w r).trans copyFrame))
  have hpostframe:=post_frame j q huh.withPC hu1711 hu149
  have hf:Frame n s final:=before.trans hpostframe
  have hinv:Invariant n (k+1) x final:=by
    refine ⟨(post_header j q huh.withPC hu1711).withPC,?_,?_,?_,?_⟩
    · exact (hf.metadata hi.metadata).transport (fun _ _=>rfl) (fun _ _=>rfl)
    · exact (hf.operands hi.operands).transport rfl
    · exact (post_original j q huh.withPC hu1711 hu149 huo.withPC).withPC
    · exact (post_retained j q huh.withPC hu1711 hu149 hur.withPC huc).withPC
  refine ⟨final,?_,hinv,hf,rfl,?_⟩
  · have actual:=(((start.trans selected).trans setup).trans copied).trans (posts.trans jump)
    rw [←axisCost_step n j] at actual
    exact actual
  · intro i hh
    have hpost:(afterPost q).scalarHeap i=q.scalarHeap i:=rfl
    have hcopy:u.scalarHeap i=z.scalarHeap i:=houtside i (Or.inr (by
      have h:=axisBase_mono n (show k+1 ≤ UniformAllAxisSeedPreparation.axisCount n by omega)
      change axisBase n (j.val+1) ≤ _ at h
      rw [axisBase_next] at h
      exact (show axisBase n k+5*r ≤ axisBase n (UniformAllAxisSeedPreparation.axisCount n) from by simpa only [j,r] using h).trans hh))
    have hlocal:v.scalarHeap i=e.scalarHeap i:=hhigh i ((scalar_temporary_before n j).trans (by
      unfold axisBase at hh
      omega))
    exact hpost.trans (hcopy.trans hlocal)


theorem loopCost_eq_sum (n k f : ℕ) : loopCost n k f=∑i:Fin f,axisCost n (k+i.val) := by
  induction f generalizing k with
  | zero=>simp [loopCost]
  | succ f ih=>rw [loopCost,Fin.sum_univ_succ,ih];simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_comm,Nat.add_left_comm]

/-- The fixed machine revisits its branch; this induction is its execution proof. -/
theorem loop {n k f : ℕ} (hn:0<n) (x : Fin n → ℂ) (s : State) (hi:Invariant n k x s)
    (hk:k+f=UniformAllAxisSeedPreparation.axisCount n) (hpc:s.pc=27)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (loopCost n k f) u ∧
    Invariant n (UniformAllAxisSeedPreparation.axisCount n) x u ∧ Frame n s u ∧ u.pc=27 ∧
    (∀i,axisBase n (UniformAllAxisSeedPreparation.axisCount n) ≤ i → u.scalarHeap i=s.scalarHeap i) := by
  induction f generalizing k s with
  | zero=>
    have he:k=UniformAllAxisSeedPreparation.axisCount n:=by omega
    subst k
    exact ⟨s,.refl hs,hi,⟨fun _ _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩,hpc,fun _ _=>rfl⟩
  | succ f ih=>
    obtain ⟨u,hu,hiu,hfu,hpu,highu⟩:=iteration hn x s hi (by omega) hpc hs
    obtain ⟨v,hv,hiv,hfv,hpv,highv⟩:=ih (k:=k+1) u hiu (by omega) hpu hu.final_bound
    exact ⟨v,hu.trans hv,hiv,hfu.trans hfv,hpv,fun i hh=>(highv i hh).trans (highu i hh)⟩

def preparationRuntime (n : ℕ) : ℕ := 29+loopCost n 0 (UniformAllAxisSeedPreparation.axisCount n)
def preparationBudget (n : ℕ) : ℕ := 29+∑j:Fin (UniformAllAxisSeedPreparation.axisCount n),
  (494*(UniformAllAxisSeedPreparation.radix n j)^2+75*UniformAllAxisSeedPreparation.radix n j+142)

theorem runtime_bound (n : ℕ) : preparationRuntime n ≤ preparationBudget n := by
  unfold preparationRuntime preparationBudget
  apply Nat.add_le_add_left
  rw [loopCost_eq_sum]
  apply Finset.sum_le_sum
  intro j _
  unfold axisCost
  simp only [Nat.zero_add,UniformAllAxisSeedPreparation.radixAt_eq]
  have h:=UniformGlobalLocalPreparation.runtime_quadratic n j
  change UniformReciprocalMachine.completeRuntime (UniformAllAxisSeedPreparation.radix n j)+30 ≤
    494*(UniformAllAxisSeedPreparation.radix n j)^2 at h
  omega

theorem initial_boot_frame (n : ℕ) (s : State) : Frame n s (UniformSeedConjugatePreparation.bootState n s) := by
  obtain ⟨hc,hn,hr,ho,hd⟩:=UniformSeedConjugatePreparation.boot_frames n s
  exact ⟨fun i _ _=>congrFun hn i,fun i _=>congrFun hc i,
    fun i _ hj=>hr i (by omega),ho,hd⟩

/-- Actual roots, produced lanes, and all copy source reads are derived inside
this continuous fixed524 execution. Only the original prepared935 postcondition
is an entry premise. -/
theorem execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (s : State) (hm:Metadata n s)
    (ho:UniformInitialPreparation.Operands n x s)
    (hr:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (hpc:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s (preparationRuntime n) u ∧
    Retained n (UniformAllAxisSeedPreparation.axisCount n) u ∧
    UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧ Frame n s u ∧ u.pc=523 ∧
    (∀i,axisBase n (UniformAllAxisSeedPreparation.axisCount n) ≤ i → u.scalarHeap i=s.scalarHeap i) ∧
    preparationRuntime n ≤ preparationBudget n := by
  obtain ⟨hc,hpool,hdir⟩:=word_setup hn
  have initialBoot:=initial_boot_execution hn x (UniformSeedConjugatePreparation.lastAxis n) s hm hr hpc hs
  let b:=UniformSeedConjugatePreparation.bootState n s
  have hb:Metadata n b:=(initial_boot_frame n s).metadata hm
  have hob:UniformInitialPreparation.Operands n x b:=(initial_boot_frame n s).operands ho
  have hrb:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) b:=
    hr.transport_high (fun _ _=>rfl) (fun _ _=>rfl)
  have hd:b.natReg 1247=UniformSeedConjugatePreparation.destination n:=
    (UniformSeedConjugatePreparation.boot_registers s hm).1
  have hp15:b.pc=15:=by
    simp [b,UniformSeedConjugatePreparation.bootState,UniformSeedConjugatePreparation.secondLoaded,
      UniformSeedConjugatePreparation.firstLoaded,UniformNewtonTableMachine.applyBlock_pc,hpc,
      UniformSeedConjugatePreparation.bootPrefix_length,UniformSeedConjugatePreparation.bootMiddle_length,
      UniformSeedConjugatePreparation.bootSuffix_length,writeNat,next]
  have hboot:=UniformNewtonTableMachine.block_runs boot program 15 n ((n+2)^19) x b boot_code hp15 initialBoot.final_bound
    (by change 27≤(n+2)^19;omega) (by trivial)
    (boot_peak b hb hdir hc (initialBoot.final_bound.2.1 1247))
  let z:=UniformNewtonTableMachine.applyBlock boot b
  have hp27:z.pc=27:=(UniformNewtonTableMachine.applyBlock_pc boot b).trans (by rw [hp15];rfl)
  obtain ⟨v,hv,hiv,hfv,hpv,highv⟩:=loop (k:=0) (f:=UniformAllAxisSeedPreparation.axisCount n) hn x z
    (boot_invariant b hb hob hd hrb) (by omega) hp27 hboot.final_bound
  let final:State:={v with pc:=523}
  have hfB:=changePC_bound ((n+2)^19) v 523 hv.final_bound (by omega)
  have hhalt:BoundedExecution program n x ((n+2)^19) final 1 final:=.halt hfB
    (by simp [step,final,halt_code])
  have hfinish:BoundedExecution program n x ((n+2)^19) v 2 final:=by
    refine .next hv.final_bound ?_ hhalt
    simp [step,hpv,branch_code,hiv.header.index,hiv.header.count,final]
  refine ⟨final,?_,hiv.retained.withPC,hiv.original.withPC,
    hiv.metadata.transport (fun _ _=>rfl) (fun _ _=>rfl),hiv.operands.transport rfl,
    (initial_boot_frame n s).trans ((boot_frame n b).trans hfv),rfl,highv,runtime_bound n⟩
  have actual:=initialBoot.executes (hboot.executes (hv.executes hfinish))
  have ht:15+(boot.length+(loopCost n 0 (UniformAllAxisSeedPreparation.axisCount n)+2))=preparationRuntime n:=by
    change 15+(12+(_+2))=29+_;omega
  rw [ht] at actual
  exact actual

theorem retained_complete {n : ℕ} {s : State} (h:Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    s.natHeap (directoryBase n+2*j.val)=some (axisBase n j.val) ∧
    s.natHeap (directoryBase n+2*j.val+1)=some (UniformAllAxisSeedPreparation.radix n j) ∧
    UniformSeedConjugatePreparation.ConjugateCompact (UniformAllAxisSeedPreparation.radix n j) (axisBase n j.val) s :=
  ⟨h.address j j.isLt,h.width j j.isLt,UniformSeedConjugatePreparation.conjugateCompact_of_compact
    (UniformGlobalLocalPreparation.radix_pos n j) (h.coefficients j j.isLt)⟩

/-- The selected root cells and original compact directory survive all axes. -/
theorem original_directory_retained {n : ℕ} {s u : State} (hf:Frame n s u)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    u.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*j.val)=s.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*j.val) ∧
    u.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*j.val+1)=s.natHeap (UniformAllAxisSeedPreparation.directoryBase n+2*j.val+1) := by
  have hlo:copyBase n≤UniformAllAxisSeedPreparation.directoryBase n:=by
    rw [←UniformAllAxisSeedPreparation.directory_after_protected];omega
  exact ⟨hf.1 _ (by omega) (by have h:=original_directory_before n j;omega),
    hf.1 _ (by omega) (original_directory_before n j)⟩



theorem coefficientwise_conjugate {n : ℕ} {s u : State}
    (original:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (new:Retained n (UniformAllAxisSeedPreparation.axisCount n) u)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (q : Fin 5)
    (l : Fin (UniformAllAxisSeedPreparation.radix n j)) :
    u.scalarHeap (axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+l.val)=
      (s.scalarHeap (UniformAllAxisSeedPreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+l.val)).map
        (fun v:Scalar=>⟨starRingEnd ℂ v.value,v.dependent⟩) := by
  rw [original.coefficients j j.isLt q l]
  exact (retained_complete new j).2.2 q l


theorem original_compact_retained {n : ℕ} {s u : State}
    (before:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
    (after:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) (q : Fin 5)
    (l : Fin (UniformAllAxisSeedPreparation.radix n j)) :
    u.scalarHeap (UniformAllAxisSeedPreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+l.val)=
      s.scalarHeap (UniformAllAxisSeedPreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+l.val) :=
  (after.coefficients j j.isLt q l).trans (before.coefficients j j.isLt q l).symm

theorem selected_root_retained {n : ℕ} {s u : State} (h:Frame n s u)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) : u.scalarHeap (6+j.val)=s.scalarHeap (6+j.val) := by
  apply h.2.1
  have hj:=j.isLt
  rw [UniformGlobalLocalPreparation.globalEnd_formula]
  unfold UniformAllAxisSeedPreparation.axisCount at hj
  omega

/-- O(log^5 n) follows from actual selected-radix work; no local phase is free. -/
theorem budget_axis_power {n : ℕ} (hn:0<n) : preparationBudget n≤10000029*(ell n+2)^5 := by
  let t:=ell n+2
  have ht:2≤t:=by dsimp [t];omega
  have h24:t^2≤t^4:=by
    have h1:1≤t^2:=by nlinarith
    rw [show t^4=(t^2)^2 by ring]
    nlinarith
  have hterm (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
      494*(UniformAllAxisSeedPreparation.radix n j)^2+75*UniformAllAxisSeedPreparation.radix n j+142≤10000000*t^4 := by
    have hr:UniformAllAxisSeedPreparation.radix n j≤128*t^2:=UniformSelectedCRT.radix_quadratic hn j
    have hs:=Nat.pow_le_pow_left hr 2
    rw [show (128*t^2)^2=16384*t^4 by ring] at hs
    nlinarith
  have hsum:(∑j:Fin (UniformAllAxisSeedPreparation.axisCount n),
      (494*(UniformAllAxisSeedPreparation.radix n j)^2+75*UniformAllAxisSeedPreparation.radix n j+142))
      ≤UniformAllAxisSeedPreparation.axisCount n*(10000000*t^4):=by
    calc _≤∑_j:Fin (UniformAllAxisSeedPreparation.axisCount n),10000000*t^4:=Finset.sum_le_sum (fun j _=>hterm j)
         _=_:=by simp
  have hcount:UniformAllAxisSeedPreparation.axisCount n≤t:=by dsimp [UniformAllAxisSeedPreparation.axisCount,t];omega
  have hmul:=Nat.mul_le_mul_right (10000000*t^4) hcount
  have h5:1≤t^5:=by have h:0<t^5:=pow_pos (by omega) 5;omega
  rw [show t*(10000000*t^4)=10000000*t^5 by ring] at hmul
  unfold preparationBudget
  change 29+_≤10000029*t^5
  omega

theorem budget_isBigO_log_five :
    (fun n : ℕ=>(preparationBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ=>Real.log (n:ℝ)^5) := by
  have haxis:(fun n : ℕ=>(preparationBudget n:ℝ)) =O[Filter.atTop]
      (fun n : ℕ=>((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5) := by
    apply Asymptotics.IsBigO.of_bound 10000029
    filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with n hn
    have h:(preparationBudget n:ℝ)≤10000029*((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5:=by
      exact_mod_cast budget_axis_power (show 0<n by omega)
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (by positivity :0≤((UniformWorkingLength.axisCount n+2:ℕ):ℝ)^5)] using h
  exact haxis.trans (UniformWorkingPreparation.axisCount_plus_two_isBigO_log.pow 5)



/-- Charged935 original preparation followed by this fixed524 driver. -/
def fullHead : Program := UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)
def fullProgram : Program := fullHead++(program.map (relocate 935 1459)++[.halt])

theorem fullHead_length : fullHead.length=935 := by
  simp only [fullHead,List.length_map,UniformAllAxisSeedPreparation.fullProgram_length]
theorem fullProgram_length : fullProgram.length=1460 := by
  simp only [fullProgram,List.length_append,List.length_map,fullHead_length,program_length];rfl

-- Keep the already verified935 syntax symbolic during proof elaboration.
-- This local transparency setting neither changes bytecode nor adds an axiom.
attribute [local irreducible] UniformAllAxisSeedPreparation.fullProgram

theorem relocated_prefix_code (p suffix : Program) (ret : ℕ) :
    CodeAt p (p.map (relocate 0 ret)++suffix) 0 ret := by
  intro i hi
  rw [Nat.zero_add,List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]

theorem original_code : CodeAt UniformAllAxisSeedPreparation.fullProgram fullProgram 0 935 := by
  rw [fullProgram,fullHead]
  exact relocated_prefix_code UniformAllAxisSeedPreparation.fullProgram (program.map (relocate 935 1459)++[.halt]) 935

theorem driver_code : CodeAt program fullProgram 935 1459 := by
  have h:=embed_code fullHead program [.halt] 1459
  simpa only [embed,List.append_assoc,fullProgram,fullHead_length] using h

theorem full_halt : fullProgram[1459]?=some .halt := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (fullHead++program.map (relocate 935 1459)) [.halt] [] 0 (by decide)
  simpa only [List.append_nil,List.append_assoc,fullProgram,List.length_append,List.length_map,
    fullHead_length,program_length,List.getElem?_cons_zero] using h

def fullBudget (n : ℕ) : ℕ := UniformAllAxisSeedPreparation.fullBudget n+preparationBudget n+1

theorem full_word_bound {n : ℕ} (hn:0<n) : 1460≤(n+2)^19 := by
  have h:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 19
  norm_num at h;omega

/-- A closed empty-start execution. Its one master-root request comes from
actual935; the conjugate driver introduces no additional input/root request. -/
theorem initial_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) : ∃t u,
    BoundedExecution fullProgram n x ((n+2)^19) initial
      (t+UniformAllAxisSeedPreparation.preparationRuntime n+1+preparationRuntime n+1) u ∧
    t≤UniformPermutationInversePreparation.preparationBudget n ∧
    Retained n (UniformAllAxisSeedPreparation.axisCount n) u ∧
    UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧ u.pc=1459 ∧
    t+UniformAllAxisSeedPreparation.preparationRuntime n+1+preparationRuntime n+1≤fullBudget n := by
  obtain ⟨t,v,hv,hcost,hr,hm,ho,_,_,hroots,hout,_,hbudget⟩:=UniformAllAxisSeedPreparation.initial_execution hn x
  have hbig:=full_word_bound hn
  have start:=UniformBoundedAssembly.boundedExecution_placed original_code
    (by rw [UniformAllAxisSeedPreparation.fullProgram_length];omega :0+UniformAllAxisSeedPreparation.fullProgram.length≤(n+2)^19)
    (by omega :935≤(n+2)^19) hv
  change BoundedRuns fullProgram n x ((n+2)^19) initial
    (t+UniformAllAxisSeedPreparation.preparationRuntime n+1) {v with pc:=935} at start
  let e:State:={v with pc:=0}
  obtain ⟨u,hu,hnew,hru,hmu,hou,hf,_,_,hb⟩:=execution hn x e
    (hm.transport (fun _ _=>rfl) (fun _ _=>rfl)) (ho.transport rfl) hr.withPC rfl
    (changePC_bound _ v 0 hv.final_bound (by omega))
  have tail:=UniformBoundedAssembly.boundedExecution_placed driver_code
    (by rw [program_length];omega :935+program.length≤(n+2)^19)
    (by omega :1459≤(n+2)^19) hu
  have heq:placed 935 e={v with pc:=935}:=rfl
  rw [heq] at tail
  let final:State:={u with pc:=1459}
  have halt:BoundedExecution fullProgram n x ((n+2)^19) final 1 final:=.halt tail.final_bound
    (by simp [step,final,full_halt])
  refine ⟨t,final,?_,hcost,hnew.withPC,hru.withPC,
    hmu.transport (fun _ _=>rfl) (fun _ _=>rfl),hou.transport rfl,
    hf.2.2.2.2.trans hroots,hf.2.2.2.1.trans hout,rfl,?_⟩
  · exact start.executes (tail.executes halt)
  · unfold fullBudget;omega



end
end ExactFourierCircuits.UniformAllAxisConjugatePreparation
