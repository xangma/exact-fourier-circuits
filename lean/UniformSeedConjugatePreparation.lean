import UniformConjugateLocalPreparation
import UniformAllAxisSeedPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedConjugatePreparation
open UniformMachine UniformAssembly UniformPairMachine
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
namespace R
abbrev Op := UniformReciprocalMachine.Op
end R
namespace N
abbrev Op := UniformNewtonTableMachine.Op
end N
namespace O
abbrev axisCount := UniformAllAxisSeedPreparation.axisCount
abbrev axisBase := UniformAllAxisSeedPreparation.axisBase
abbrev directoryBase := UniformAllAxisSeedPreparation.directoryBase
abbrev Retained := UniformAllAxisSeedPreparation.Retained
end O
noncomputable section

abbrev radix := UniformConjugateLocalPreparation.radix
abbrev axisRoot := UniformConjugateLocalPreparation.axisRoot
def destination (n : ℕ) : ℕ := O.axisBase n (O.axisCount n)
def lastAxis (n : ℕ) : Fin (O.axisCount n) := Fin.last (ell n)

theorem destination_tail (n : ℕ) : destination n=O.axisBase n (lastAxis n).val+5*radix n (lastAxis n) := by
  simpa only [destination,lastAxis,Fin.val_last] using
    UniformAllAxisSeedPreparation.axisBase_next n (lastAxis n)

theorem pool_before_destination (n : ℕ) : UniformLocalSeedTableMachine.poolBase n ≤ destination n := by
  unfold destination O.axisBase UniformAllAxisSeedPreparation.axisBase
  omega

theorem word_setup {n : ℕ} (hn:0<n) (j : Fin (O.axisCount n)) :
    466 ≤ (n+2)^19 ∧ destination n+5*radix n j ≤ (n+2)^19 ∧
    O.directoryBase n+2*O.axisCount n ≤ (n+2)^19 := by
  have he:ell n ≤ 2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount
    omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:=UniformAllAxisSeedPreparation.prefix_bound n (O.axisCount n) (le_refl _)
  have hr:=UniformConjugateLocalPreparation.radix_le_length n j
  have hsmall:400 ≤ (n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 17
    norm_num at h
    omega
  have hb:400*(n+2)^2 ≤ (n+2)^19:=by
    rw [show 19=17+2 by decide,pow_add]
    exact Nat.mul_le_mul_right ((n+2)^2) hsmall
  have hprod:(ell n+1)*len n ≤ (2*n+1)*(4*n):=Nat.mul_le_mul (by omega) (by omega)
  have hpool:destination n+5*radix n j ≤ 400*(n+2)^2:=by
    unfold destination O.axisBase UniformAllAxisSeedPreparation.axisBase UniformLocalSeedTableMachine.poolBase
    rw [UniformGlobalLocalPreparation.globalEnd_formula]
    nlinarith
  have hdir:O.directoryBase n+2*O.axisCount n ≤ 400*(n+2)^2:=by
    change UniformAllAxisSeedPreparation.directoryBase n+2*(ell n+1) ≤ _
    rw [UniformAllAxisSeedPreparation.directory_formula]
    nlinarith
  exact ⟨by nlinarith,hpool.trans hb,hdir.trans hb⟩

/-- Real directory loads compute the fresh destination, rather than a supplied
conjugate-bank address. Original driver headers100..106 are read and retained. -/
def bootPrefix : List N.Op := [.literal 1240 0,.literal 1241 1,.literal 1242 2,
  .add 1243 102 1241,.add 1244 106 105,.add 1244 1244 103,
  .sub 1245 1243 1241,.mul 1246 1245 1242,.add 1246 1246 1244]
def bootMiddle : List N.Op := [.add 1246 1246 1241]
def bootSuffix : List N.Op := [.literal 1249 5,.mul 1248 1248 1249,.add 1247 1247 1248]
def boot : Program := bootPrefix.map UniformNewtonTableMachine.Op.code++[.loadNat 1247 1246]++
  bootMiddle.map UniformNewtonTableMachine.Op.code++[.loadNat 1248 1246]++bootSuffix.map UniformNewtonTableMachine.Op.code

def override : List R.Op := [.add 120 1247 1240]
def emitHead : Program := UniformLocalSeedTableMachine.globalHead++override.map UniformReciprocalMachine.Op.code
def program : Program := boot++UniformConjugateLocalPreparation.program.map (relocate 15 316)++emitHead++
  UniformLocalSeedTableMachine.program.map (relocate 345 465)++[.halt]

theorem bootPrefix_length : bootPrefix.length=9 := rfl
theorem bootMiddle_length : bootMiddle.length=1 := rfl
theorem bootSuffix_length : bootSuffix.length=3 := rfl
theorem boot_length : boot.length=15 := rfl
theorem emitHead_length : emitHead.length=29 := rfl
theorem program_length : program.length=466 := by
  simp only [program,List.length_append,List.length_map,boot_length,
    UniformConjugateLocalPreparation.program_length,emitHead_length,
    UniformLocalSeedTableMachine.program_length]
  rfl

theorem bootPrefix_code : UniformNewtonTableMachine.BlockAt bootPrefix program 0 := by
  intro i hi
  change i<9 at hi
  interval_cases i <;> rfl
theorem load_base_code : program[9]?=some (.loadNat 1247 1246) := rfl
theorem bootMiddle_code : UniformNewtonTableMachine.BlockAt bootMiddle program 10 := by
  intro i hi
  change i<1 at hi
  interval_cases i
  rfl
theorem load_width_code : program[11]?=some (.loadNat 1248 1246) := rfl
theorem bootSuffix_code : UniformNewtonTableMachine.BlockAt bootSuffix program 12 := by
  intro i hi
  change i<3 at hi
  interval_cases i <;> rfl

theorem local_code : CodeAt UniformConjugateLocalPreparation.program program 15 316 := by
  intro i hi
  have h:=UniformAllAxisSeedPreparation.lookup_segment boot
    (UniformConjugateLocalPreparation.program.map (relocate 15 316))
    (emitHead++UniformLocalSeedTableMachine.program.map (relocate 345 465)++[.halt]) i
    (by simpa only [List.length_map] using hi)
  simpa only [program,List.append_assoc,boot_length,List.getElem?_map] using h

theorem emit_lookup (i : ℕ) (hi:i<29) : program[316+i]?=emitHead[i]? := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (boot++UniformConjugateLocalPreparation.program.map (relocate 15 316)) emitHead
    (UniformLocalSeedTableMachine.program.map (relocate 345 465)++[.halt]) i
    (by simpa only [emitHead_length] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,
    boot_length,UniformConjugateLocalPreparation.program_length] using h

theorem emit_pointer_code : UniformReciprocalMachine.BlockAt UniformLocalSeedTableMachine.globalPointer program 316 := by
  intro i hi
  have hi4:i<4:=hi
  rw [emit_lookup i (by omega)]
  interval_cases i <;> rfl

theorem emit_load_code : program[320]?=some (.loadNat 117 108) := by
  rw [show 320=316+4 by decide,emit_lookup 4 (by decide)]
  rfl

theorem emit_setup_code : UniformReciprocalMachine.BlockAt UniformLocalSeedTableMachine.globalSetup program 321 := by
  intro i hi
  have hi23:i<23:=hi
  rw [show 321+i=316+(5+i) by omega,emit_lookup (5+i) (by omega)]
  interval_cases i <;> rfl

theorem override_code : UniformReciprocalMachine.BlockAt override program 344 := by
  intro i hi
  have hi1:i<1:=hi
  rw [show 344+i=316+(28+i) by omega,emit_lookup (28+i) (by omega)]
  interval_cases i
  rfl

theorem compact_code : CodeAt UniformLocalSeedTableMachine.program program 345 465 := by
  intro i hi
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (boot++UniformConjugateLocalPreparation.program.map (relocate 15 316)++emitHead)
    (UniformLocalSeedTableMachine.program.map (relocate 345 465)) [.halt] i
    (by simpa only [List.length_map] using hi)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,
    boot_length,UniformConjugateLocalPreparation.program_length,emitHead_length,List.getElem?_map] using h

theorem halt_code : program[465]?=some .halt := by
  have h:=UniformAllAxisSeedPreparation.lookup_segment
    (boot++UniformConjugateLocalPreparation.program.map (relocate 15 316)++emitHead++
      UniformLocalSeedTableMachine.program.map (relocate 345 465)) [.halt] [] 0 (by decide)
  simpa only [program,List.append_assoc,List.length_append,List.length_map,
    boot_length,UniformConjugateLocalPreparation.program_length,emitHead_length,
    UniformLocalSeedTableMachine.program_length,List.append_nil,Nat.reduceAdd,List.getElem?_cons_zero] using h


def firstLoaded (n : ℕ) (s : State) : State := writeNat
  (UniformNewtonTableMachine.applyBlock bootPrefix s) 1247 (O.axisBase n (lastAxis n).val)
def secondLoaded (n : ℕ) (s : State) : State := writeNat
  (UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s)) 1248 (radix n (lastAxis n))
def bootState (n : ℕ) (s : State) : State := UniformNewtonTableMachine.applyBlock bootSuffix (secondLoaded n s)

theorem boot_address {n : ℕ} (s : State) (hm:Metadata n s) :
    (UniformNewtonTableMachine.applyBlock bootPrefix s).natReg 1246=O.directoryBase n+2*(lastAxis n).val := by
  simp [UniformNewtonTableMachine.applyBlock,bootPrefix,UniformNewtonTableMachine.Op.apply,writeNat,next,
    hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,lastAxis,
    UniformAllAxisSeedPreparation.directoryBase,UniformPermutationInversePreparation.inverseBase,Nat.mul_comm,Nat.add_comm]

theorem boot_one (s : State) : (UniformNewtonTableMachine.applyBlock bootPrefix s).natReg 1241=1 := by
  simp [UniformNewtonTableMachine.applyBlock,bootPrefix,UniformNewtonTableMachine.Op.apply,writeNat,next]

theorem middle_address {n : ℕ} (s : State) (hm:Metadata n s) :
    (UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s)).natReg 1246=
      O.directoryBase n+2*(lastAxis n).val+1 := by
  simp [firstLoaded,UniformNewtonTableMachine.applyBlock,bootMiddle,UniformNewtonTableMachine.Op.apply,
    writeNat,next,boot_address s hm,boot_one]

theorem boot_registers {n : ℕ} (s : State) (_hm:Metadata n s) :
    (bootState n s).natReg 1247=destination n ∧ (bootState n s).natReg 1240=0 := by
  simp [bootState,secondLoaded,firstLoaded,UniformNewtonTableMachine.applyBlock,
    bootPrefix,bootMiddle,bootSuffix,UniformNewtonTableMachine.Op.apply,writeNat,next]
  rw [Nat.mul_comm,←destination_tail]

theorem boot_frames (n : ℕ) (s : State) :
    (bootState n s).scalarHeap=s.scalarHeap ∧ (bootState n s).natHeap=s.natHeap ∧
    (∀i,i<1240→(bootState n s).natReg i=s.natReg i) ∧
    (bootState n s).outputs=s.outputs ∧ (bootState n s).rootOrders=s.rootOrders := by
  refine ⟨rfl,rfl,?_,rfl,rfl⟩
  intro i hi
  simp (disch:=omega) [bootState,secondLoaded,firstLoaded,UniformNewtonTableMachine.applyBlock,
    bootPrefix,bootMiddle,bootSuffix,UniformNewtonTableMachine.Op.apply,writeNat,next]

theorem boot_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s) (hr:O.Retained n (O.axisCount n) s)
    (hpc:s.pc=0) (hs:WordBound ((n+2)^19) s) :
    BoundedRuns program n x ((n+2)^19) s 15 (bootState n s) := by
  let B:=(n+2)^19
  obtain ⟨hc,hpool,hdir⟩:=word_setup hn j
  have hl:0<len n:=UniformWorkingLength.workingLength_pos hn
  have hlast:O.axisBase n (lastAxis n).val ≤ destination n:=
    UniformAllAxisSeedPreparation.axisBase_mono n (Nat.le_of_lt (lastAxis n).isLt)
  have hrLast:radix n (lastAxis n) ≤ len n:=UniformConjugateLocalPreparation.radix_le_length n (lastAxis n)
  have hL:len n ≤ B:=by rw [←hm.saved.workingLength];exact hs.2.1 103
  have hp:=UniformNewtonTableMachine.block_runs bootPrefix program 0 n B x s bootPrefix_code hpc hs
    (by change 9 ≤ B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,bootPrefix,UniformNewtonTableMachine.Op.peak,UniformNewtonTableMachine.Op.apply,writeNat,next,
        hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength]
      change UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n ≤ _ at hdir
      rw [←UniformAllAxisSeedPreparation.directory_after_protected] at hdir
      unfold UniformAllAxisSeedPreparation.axisCount at hdir
      unfold copyBase at hdir
      omega)
  have hp9:(UniformNewtonTableMachine.applyBlock bootPrefix s).pc=9:=
    (UniformNewtonTableMachine.applyBlock_pc _ _).trans (by rw [hpc,bootPrefix_length])
  have hload:(UniformNewtonTableMachine.applyBlock bootPrefix s).natHeap
      ((UniformNewtonTableMachine.applyBlock bootPrefix s).natReg 1246)=some (O.axisBase n (lastAxis n).val):=by
    rw [boot_address s hm,UniformNewtonTableMachine.applyBlock_natHeap _ _ (by simp [bootPrefix,UniformNewtonTableMachine.NatHeapFree])]
    exact hr.address (lastAxis n) (lastAxis n).isLt
  have hb:WordBound B (firstLoaded n s):=writeNat_bound B _ 1247 _ hp.final_bound
    (by rw [hp9];omega) (by omega)
  have hfirst:BoundedRuns program n x B (UniformNewtonTableMachine.applyBlock bootPrefix s) 1 (firstLoaded n s):=
    .next hp.final_bound (by simp [step,hp9,load_base_code,hload,firstLoaded]) (.refl hb)
  have hp10:(firstLoaded n s).pc=10:=by simp [firstLoaded,writeNat,next,hp9]
  have hmrun:=UniformNewtonTableMachine.block_runs bootMiddle program 10 n B x (firstLoaded n s)
    bootMiddle_code hp10 hb (by change 11 ≤ B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,bootMiddle,UniformNewtonTableMachine.Op.peak,
        firstLoaded,writeNat,next,boot_address s hm,boot_one]
      have ht: (lastAxis n).val<O.axisCount n :=(lastAxis n).isLt
      omega)
  have hp11:(UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s)).pc=11:=
    (UniformNewtonTableMachine.applyBlock_pc _ _).trans (by rw [hp10,bootMiddle_length])
  have hw:(UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s)).natHeap
      ((UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s)).natReg 1246)=some (radix n (lastAxis n)):=by
    rw [middle_address s hm]
    exact hr.width (lastAxis n) (lastAxis n).isLt
  have hwB:WordBound B (secondLoaded n s):=writeNat_bound B _ 1248 _ hmrun.final_bound
    (by rw [hp11];omega) (by omega)
  have hsecond:BoundedRuns program n x B (UniformNewtonTableMachine.applyBlock bootMiddle (firstLoaded n s))
      1 (secondLoaded n s):=.next hmrun.final_bound
        (by simp [step,hp11,load_width_code,hw,secondLoaded]) (.refl hwB)
  have hp12:(secondLoaded n s).pc=12:=by simp [secondLoaded,writeNat,next,hp11]
  have hsuffix:=UniformNewtonTableMachine.block_runs bootSuffix program 12 n B x (secondLoaded n s)
    bootSuffix_code hp12 hwB (by change 15 ≤ B;omega) (by trivial) (by
      simp [UniformNewtonTableMachine.peak,bootSuffix,UniformNewtonTableMachine.Op.peak,UniformNewtonTableMachine.Op.apply,
        secondLoaded,firstLoaded,UniformNewtonTableMachine.applyBlock,bootMiddle,writeNat,next]
      rw [Nat.mul_comm,←destination_tail]
      omega)
  convert (((hp.trans hfirst).trans hmrun).trans hsecond).trans hsuffix using 1 <;> rfl


theorem local_keeps_driver (i : ℕ) (hi:200 ≤ i) :
    ∀ins ∈ UniformConjugateLocalPreparation.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hh:∀ins ∈ UniformConjugateLocalPreparation.head,UniformNewtonTableMachine.KeepsNat i ins:=by
    simp [UniformConjugateLocalPreparation.head,UniformConjugateLocalPreparation.pointer,
      UniformConjugateLocalPreparation.setup,UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
    omega
  have hc:=UniformReciprocalMachine.keeps_relocate i 31 300
    (UniformGlobalNatPreparation.reciprocal_keeps_high i (by omega))
  have ht:∀ins ∈ ([.halt]:Program),UniformNewtonTableMachine.KeepsNat i ins:=by simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformConjugateLocalPreparation.program,embed,UniformConjugateLocalPreparation.head_length,List.append_assoc] using
    UniformReciprocalMachine.keeps_append i (UniformReciprocalMachine.keeps_append i hh hc) ht

theorem local_keeps_index :
    ∀ins ∈ UniformConjugateLocalPreparation.program,UniformNewtonTableMachine.KeepsNat 110 ins := by
  have hh:∀ins ∈ UniformConjugateLocalPreparation.head,UniformNewtonTableMachine.KeepsNat 110 ins:=by
    simp [UniformConjugateLocalPreparation.head,UniformConjugateLocalPreparation.pointer,
      UniformConjugateLocalPreparation.setup,UniformReciprocalMachine.Op.code,UniformNewtonTableMachine.KeepsNat]
  have hc:=UniformReciprocalMachine.keeps_relocate 110 31 300
    (UniformGlobalNatPreparation.reciprocal_keeps_high 110 (by decide))
  have ht:∀ins ∈ ([.halt]:Program),UniformNewtonTableMachine.KeepsNat 110 ins:=by simp [UniformNewtonTableMachine.KeepsNat]
  simpa only [UniformConjugateLocalPreparation.program,embed,UniformConjugateLocalPreparation.head_length,List.append_assoc] using
    UniformReciprocalMachine.keeps_append 110 (UniformReciprocalMachine.keeps_append 110 hh hc) ht


def emittedHeader (s : State) (r : ℕ) : State := UniformReciprocalMachine.applyBlock override
  (UniformLocalSeedTableMachine.globalInitialized s r)

theorem emittedHeader_heap (s : State) (r : ℕ) :
    (emittedHeader s r).scalarHeap=s.scalarHeap ∧ (emittedHeader s r).natHeap=s.natHeap ∧
    (emittedHeader s r).outputs=s.outputs ∧ (emittedHeader s r).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩

theorem emittedHeader_saved (s : State) (r i : ℕ) (hi:100 ≤ i) (hj:i ≤ 106) :
    (emittedHeader s r).natReg i=s.natReg i := by
  simp (disch:=omega) [emittedHeader,override,UniformLocalSeedTableMachine.globalInitialized,
    UniformLocalSeedTableMachine.globalLoaded,UniformLocalSeedTableMachine.globalPointer,
    UniformLocalSeedTableMachine.globalSetup,UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,
    writeNat,next]

theorem emittedHeader_registers {n : ℕ} (j : Fin (O.axisCount n)) (s : State) (hm:Metadata n s)
    (hd:s.natReg 1247=destination n) (hz:s.natReg 1240=0) :
    let r:=radix n j
    (emittedHeader s r).natReg 117=r ∧
    (emittedHeader s r).natReg 118=UniformGlobalLocalPreparation.resultBase n r ∧
    (emittedHeader s r).natReg 119=UniformGlobalLocalPreparation.rootSource n r+1 ∧
    (emittedHeader s r).natReg 120=destination n := by
  obtain ⟨h117,h118,h119,_⟩:=UniformLocalSeedTableMachine.globalInitialized_registers j s hm
  have h1247:(UniformLocalSeedTableMachine.globalInitialized s (radix n j)).natReg 1247=destination n:=by
    simp [UniformLocalSeedTableMachine.globalInitialized,UniformLocalSeedTableMachine.globalLoaded,
      UniformLocalSeedTableMachine.globalPointer,UniformLocalSeedTableMachine.globalSetup,
      UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,writeNat,next,hd]
  have h1240:(UniformLocalSeedTableMachine.globalInitialized s (radix n j)).natReg 1240=0:=by
    simp [UniformLocalSeedTableMachine.globalInitialized,UniformLocalSeedTableMachine.globalLoaded,
      UniformLocalSeedTableMachine.globalPointer,UniformLocalSeedTableMachine.globalSetup,
      UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,writeNat,next,hz]
  simp [emittedHeader,override,UniformReciprocalMachine.applyBlock,UniformReciprocalMachine.Op.apply,
    writeNat,next,h117,h118,h119,h1247,h1240]

/-- The compact caller headers are produced by charged pointer/load/arithmetic steps. -/
theorem emit_initialize {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s) (hpc:s.pc=316) (h110:s.natReg 110=j.val)
    (hd:s.natReg 1247=destination n) (hz:s.natReg 1240=0)
    (hs:WordBound ((n+2)^19) s) :
    BoundedRuns program n x ((n+2)^19) s 29 (emittedHeader s (radix n j)) ∧
      (emittedHeader s (radix n j)).pc=345 := by
  let B:=(n+2)^19
  let r:=radix n j
  obtain ⟨hcode,hpool,_⟩:=word_setup hn j
  obtain ⟨_,hcopy,_⟩:=UniformGlobalLocalPreparation.word_setup hn j
  obtain ⟨_,hpoolOne⟩:=UniformLocalSeedTableMachine.pool_word_bound hn j
  change UniformLocalSeedTableMachine.poolBase n+5*r ≤ B at hpoolOne
  have hptr:=UniformReciprocalMachine.block_runs UniformLocalSeedTableMachine.globalPointer program 316 n B x s
    emit_pointer_code hpc hs (by change 320 ≤ B;omega) (by trivial)
    (UniformLocalSeedTableMachine.globalPointer_peak j B s hm h110 hcopy (by omega))
  have h320:(UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).pc=320:=by
    rw [UniformReciprocalMachine.applyBlock_pc,hpc];rfl
  have hl:(UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).natHeap
      ((UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s).natReg 108)=some r:=by
    rw [UniformLocalSeedTableMachine.globalPointer_address j s hm h110,UniformReciprocalMachine.applyBlock_natHeap]
    exact (hm.crt j).1
  have hloadB:WordBound B (UniformLocalSeedTableMachine.globalLoaded s r):=writeNat_bound B _ 117 r hptr.final_bound
    (by rw [h320];omega) (by omega)
  have hload:BoundedRuns program n x B (UniformReciprocalMachine.applyBlock UniformLocalSeedTableMachine.globalPointer s)
      1 (UniformLocalSeedTableMachine.globalLoaded s r):=
    .next hptr.final_bound (by simp [step,h320,emit_load_code,hl,UniformLocalSeedTableMachine.globalLoaded]) (.refl hloadB)
  have h321:(UniformLocalSeedTableMachine.globalLoaded s r).pc=321:=by
    simp [UniformLocalSeedTableMachine.globalLoaded,writeNat,next,h320]
  have hsetup:=UniformReciprocalMachine.block_runs UniformLocalSeedTableMachine.globalSetup program 321 n B x
    (UniformLocalSeedTableMachine.globalLoaded s r) emit_setup_code h321 hloadB (by change 344 ≤ B;omega) (by trivial)
    (UniformLocalSeedTableMachine.globalSetup_peak j B s hm hpoolOne (by omega))
  have h344:(UniformLocalSeedTableMachine.globalInitialized s r).pc=344:=
    (UniformReciprocalMachine.applyBlock_pc _ _).trans (by rw [h321];rfl)
  have hpeak:UniformReciprocalMachine.peak override (UniformLocalSeedTableMachine.globalInitialized s r) ≤ B:=by
    simp [UniformReciprocalMachine.peak,override,UniformReciprocalMachine.Op.peak,
      UniformReciprocalMachine.Op.apply,UniformLocalSeedTableMachine.globalInitialized,
      UniformLocalSeedTableMachine.globalLoaded,UniformLocalSeedTableMachine.globalPointer,
      UniformLocalSeedTableMachine.globalSetup,UniformReciprocalMachine.applyBlock,writeNat,next,hd,hz]
    omega
  have hoff:=UniformReciprocalMachine.block_runs override program 344 n B x
    (UniformLocalSeedTableMachine.globalInitialized s r) override_code h344 hsetup.final_bound
    (by change 345 ≤ B;omega) (by trivial) hpeak
  refine ⟨?_,?_⟩
  · simpa only [UniformLocalSeedTableMachine.globalPointer_length,UniformLocalSeedTableMachine.globalSetup_length,
      show override.length=1 from rfl,Nat.reduceAdd,emittedHeader] using ((hptr.trans hload).trans hsetup).trans hoff
  · exact (UniformReciprocalMachine.applyBlock_pc override _).trans (by rw [h344];rfl)

/-- The actual copier executes from opaque, physically initialized caller headers. -/
theorem copy_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hp:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) s)
    (hpc:s.pc=345) (h117:s.natReg 117=radix n j)
    (h118:s.natReg 118=UniformGlobalLocalPreparation.resultBase n (radix n j))
    (h119:s.natReg 119=UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
    (h120:s.natReg 120=destination n) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (40*radix n j+71) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    (∀i,i<destination n → u.scalarHeap i=s.scalarHeap i) ∧ u.natHeap=s.natHeap ∧
    (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.pc=465 := by
  let B:=(n+2)^19
  let r:=radix n j
  let e:State:={s with pc:=0}
  obtain ⟨hcode,hpool,_⟩:=word_setup hn j
  obtain ⟨ha,hG⟩:=UniformLocalSeedTableMachine.selected_source_bounds n j
  change UniformGlobalLocalPreparation.resultBase n r+8*r+5 ≤ UniformLocalSeedTableMachine.poolBase n at ha
  change UniformGlobalLocalPreparation.rootSource n r+1+r ≤ UniformLocalSeedTableMachine.poolBase n at hG
  obtain ⟨u,hu,hcompact,houtside,hframe,_⟩:=UniformLocalSeedTableMachine.execution_from_local n x r
    (UniformGlobalLocalPreparation.resultBase n r) (UniformGlobalLocalPreparation.rootSource n r+1)
    (destination n) B (axisRoot r) e (UniformGlobalLocalPreparation.radix_pos n j)
    (ha.trans (pool_before_destination n)) (hG.trans (pool_before_destination n)) hpool (by omega)
    hp hg rfl h117 h118 h119 h120 (changePC_bound B s 0 hs (by omega))
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed compact_code
    (by rw [UniformLocalSeedTableMachine.program_length];omega :345+UniformLocalSeedTableMachine.program.length ≤ B)
    (by omega :465 ≤ B) hu
  have heq:placed 345 e=s:=by change {s with pc:=345}=s;rw [←hpc]
  rw [heq] at hplaced
  refine ⟨{u with pc:=465},hplaced,hcompact,?_,hframe.1.1,?_,hframe.1.2.1,hframe.1.2.2.1,rfl⟩
  · intro i hi;exact houtside i (Or.inl hi)
  · intro i hi hj;exact hframe.2 i (Or.inl (by omega)) (by omega)

/-- Initialization and copying are continuous; no host transition prepares headers. -/
theorem emit_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s)
    (hp:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) s)
    (hpc:s.pc=316) (h110:s.natReg 110=j.val)
    (hd:s.natReg 1247=destination n) (hz:s.natReg 1240=0)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (40*radix n j+100) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    (∀i,i<destination n → u.scalarHeap i=s.scalarHeap i) ∧ u.natHeap=s.natHeap ∧
    (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.pc=465 := by
  obtain ⟨hinit,hinitPC⟩:=emit_initialize hn x j s hm hpc h110 hd hz hs
  obtain ⟨h117,h118,h119,h120⟩:=emittedHeader_registers j s hm hd hz
  have hh:=(emittedHeader_heap s (radix n j)).1
  have hpe:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) (emittedHeader s (radix n j)):=by
    intro i q;exact (congrFun hh _).trans (hp i q)
  have hge:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) (emittedHeader s (radix n j)):=by
    intro i hi;exact (congrFun hh _).trans (hg i hi)
  obtain ⟨u,hu,hcompact,hbefore,hNat,hsaved,hout,hroot,hupc⟩:=copy_execution hn x j
    (emittedHeader s (radix n j)) hpe hge hinitPC h117 h118 h119 h120 hinit.final_bound
  refine ⟨u,?_,hcompact,?_,?_,?_,?_,?_,hupc⟩
  · convert hinit.trans hu using 1
    omega
  · intro i hi;exact (hbefore i hi).trans (congrFun hh i)
  · exact hNat.trans (emittedHeader_heap s (radix n j)).2.1
  · intro i hi hj;exact (hsaved i hi hj).trans (emittedHeader_saved s (radix n j) i hi hj)
  · exact hout.trans (emittedHeader_heap s (radix n j)).2.2.1
  · exact hroot.trans (emittedHeader_heap s (radix n j)).2.2.2

/-- All original compact lanes and their physical directory are retained. -/
def Frame (n : ℕ) (s u : State) : Prop := UniformConjugateLocalPreparation.Frame n s u ∧
  (∀i,UniformLocalSeedTableMachine.poolBase n ≤ i → i<destination n → u.scalarHeap i=s.scalarHeap i)

theorem boot_protected (n : ℕ) (s : State) :
    UniformAllAxisSeedPreparation.ProtectedFrame n s (bootState n s) := by
  obtain ⟨hh,hhN,hNat,ho,hr⟩:=boot_frames n s
  exact ⟨fun i _ _=>congrFun hhN i,fun i _=>congrFun hh i,
    fun i _ hi=>hNat i (by omega),ho,hr⟩

theorem boot_pc {n : ℕ} {s : State} (hpc:s.pc=0) : (bootState n s).pc=15 := by
  simp [bootState,secondLoaded,firstLoaded,UniformNewtonTableMachine.applyBlock_pc,
    writeNat,next,bootPrefix_length,bootMiddle_length,bootSuffix_length,hpc]

/-- Compact lanes have order H, scale, inverse diagonal, invH, reciprocal(invH). -/
theorem seedValue_conjugate (r : ℕ) (hr:0<r) (q : Fin 5) (j : Fin r) :
    UniformLocalSeedTableMachine.seedValue (axisRoot r) q j.val=
      starRingEnd ℂ (UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta r) q j.val) := by
  fin_cases q
  · simpa [UniformLocalSeedTableMachine.seedValue,UniformNewton.Preparation.expected]
      using UniformConjugateLocalPreparation.expected_conjugate r hr j (0:Fin 5)
  · simpa [UniformLocalSeedTableMachine.seedValue,UniformNewton.Preparation.expected]
      using UniformConjugateLocalPreparation.expected_conjugate r hr j (1:Fin 5)
  · simpa [UniformLocalSeedTableMachine.seedValue,UniformNewton.Preparation.expected]
      using UniformConjugateLocalPreparation.expected_conjugate r hr j (4:Fin 5)
  · simpa [UniformLocalSeedTableMachine.seedValue,UniformNewton.Preparation.expected]
      using UniformConjugateLocalPreparation.expected_conjugate r hr j (2:Fin 5)
  · simpa [UniformLocalSeedTableMachine.seedValue] using
      UniformConjugateLocalPreparation.reciprocal_coeff_conjugate _ _ r hr
        (UniformConjugateLocalPreparation.invH_coeff_conjugate r hr) j.val j.isLt

def ConjugateCompact (r d : ℕ) (s : State) : Prop :=
  ∀q:Fin 5,∀j:Fin r,s.scalarHeap (d+q.val*r+j.val)=some (prepared
    (starRingEnd ℂ (UniformLocalSeedTableMachine.seedValue (OAI.ExactFourier.zeta r) q j.val)))

theorem conjugateCompact_of_compact {r d : ℕ} {s : State} (hr:0<r)
    (h:UniformLocalSeedTableMachine.Compact r d (axisRoot r) s) : ConjugateCompact r d s := by
  intro q j
  rw [←seedValue_conjugate r hr q j]
  exact h q j

/-- One continuous466-instruction program physically inverts the selected root,
runs Newton and the reciprocal recurrence, and copies all five compact lanes.
The only array premises are the original startup metadata/operands/seed bank. -/
theorem execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hr:O.Retained n (O.axisCount n) s) (hpc:s.pc=0) (hj:s.natReg 110=j.val)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s
      (UniformReciprocalMachine.completeRuntime (radix n j)+40*radix n j+148) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    ConjugateCompact (radix n j) (destination n) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧ O.Retained n (O.axisCount n) u ∧
    Frame n s u ∧ u.pc=465 := by
  let B:=(n+2)^19
  let b:=bootState n s
  let e:State:={b with pc:=0}
  obtain ⟨hc,_,_⟩:=word_setup hn j
  have hboot:=boot_execution hn x j s hm hr hpc hs
  have hbf:=boot_protected n s
  have hme:Metadata n e:=(hbf.metadata hm).transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hoe:UniformInitialPreparation.Operands n x e:=(hbf.operands ho).transport rfl
  have hre:O.Retained n (O.axisCount n) e:=hr.transport_high
    (fun i _=>congrFun (boot_frames n s).1 i) (fun i _=>congrFun (boot_frames n s).2.1 i)
  have hje:e.natReg 110=j.val:=((boot_frames n s).2.2.1 110 (by decide)).trans hj
  have heB:WordBound B e:=changePC_bound B b 0 hboot.final_bound (by omega)
  obtain ⟨v,hv,hmv,hov,hp,hg,_,hvf,hvpc,hvpool⟩:=
    UniformConjugateLocalPreparation.preparation_execution_budget hn x j e hme hoe rfl hje heB
  have hl:=UniformBoundedAssembly.boundedExecution_placed local_code
    (by rw [UniformConjugateLocalPreparation.program_length];omega :15+UniformConjugateLocalPreparation.program.length ≤ B)
    (by omega :316 ≤ B) hv
  have heq:placed 15 e=b:=by change {b with pc:=15}=b;rw [←boot_pc hpc]
  rw [heq] at hl
  let v':State:={v with pc:=316}
  have hvd:v'.natReg 1247=destination n:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes (local_keeps_driver 1247 (by decide))).trans
      (boot_registers s hm).1
  have hvz:v'.natReg 1240=0:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes (local_keeps_driver 1240 (by decide))).trans
      (boot_registers s hm).2
  have hvj:v'.natReg 110=j.val:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes local_keeps_index).trans hje
  obtain ⟨u,hu,hcompact,hbefore,hNat,hsaved,hout,hroot,hupc⟩:=emit_execution hn x j v'
    (hmv.transport (fun _ _=>rfl) (fun _ _=>rfl)) hp hg rfl hvj hvd hvz hl.final_bound
  have hhalt:BoundedExecution program n x B u 1 u:=.halt hu.final_bound (by simp [step,hupc,halt_code])
  have hNatHigh:∀i,copyBase n ≤ i → u.natHeap i=s.natHeap i:=by
    intro i hi
    exact (congrFun hNat i).trans ((hvf.2.1 i hi).trans (congrFun (boot_frames n s).2.1 i))
  have hlow:∀i,i<UniformConjugateLocalPreparation.globalEnd n → u.scalarHeap i=s.scalarHeap i:=by
    intro i hi
    have hid:i<destination n:=by
      have hb:=pool_before_destination n
      unfold UniformLocalSeedTableMachine.poolBase at hb
      change UniformGlobalLocalPreparation.globalEnd n+17*len n+16 ≤ destination n at hb
      change i<UniformGlobalLocalPreparation.globalEnd n at hi
      omega
    exact (hbefore i hid).trans ((hvf.1 i hi).trans (congrFun (boot_frames n s).1 i))
  have hf:UniformConjugateLocalPreparation.Frame n s u:=by
    refine ⟨hlow,hNatHigh,?_,?_,?_⟩
    · intro i hi hjj
      exact (hsaved i hi hjj).trans ((hvf.2.2.1 i hi hjj).trans ((boot_frames n s).2.2.1 i (by omega)))
    · exact hout.trans (hvf.2.2.2.1.trans (boot_frames n s).2.2.2.1)
    · exact hroot.trans (hvf.2.2.2.2.trans (boot_frames n s).2.2.2.2)
  have hpoolFrame:∀i,UniformLocalSeedTableMachine.poolBase n ≤ i → i<destination n →
      u.scalarHeap i=s.scalarHeap i:=by
    intro i hi hid
    exact (hbefore i hid).trans ((hvpool i hi).trans (congrFun (boot_frames n s).1 i))
  have hrv:O.Retained n (O.axisCount n) v':=hre.transport_high hvpool hvf.2.1
  have hret:O.Retained n (O.axisCount n) u:=hrv.transport_before hbefore hNat
  have hpf:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=
    ⟨fun i hi _=>hNatHigh i hi,hlow,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2⟩
  refine ⟨u,?_,hcompact,conjugateCompact_of_compact (UniformConjugateLocalPreparation.radix_pos n j) hcompact,
    hpf.metadata hm,hpf.operands ho,hret,⟨hf,hpoolFrame⟩,hupc⟩
  convert hboot.executes (hl.executes (hu.executes hhalt)) using 1
  dsimp only [radix]
  omega


/-- Both words of every original directory row survive exactly. -/
theorem Frame.original_directory {n : ℕ} {s u : State} (h:Frame n s u)
    (j : Fin (O.axisCount n)) (q : Fin 2) :
    u.natHeap (O.directoryBase n+2*j.val+q.val)=s.natHeap (O.directoryBase n+2*j.val+q.val) := by
  apply h.1.2.1
  unfold O.directoryBase UniformAllAxisSeedPreparation.directoryBase UniformPermutationInversePreparation.inverseBase
  omega

theorem Frame.original_compact {n : ℕ} {s u : State} (h:Frame n s u)
    (j : Fin (O.axisCount n)) (q : Fin 5) (k : Fin (radix n j)) :
    u.scalarHeap (O.axisBase n j.val+q.val*radix n j+k.val)=
      s.scalarHeap (O.axisBase n j.val+q.val*radix n j+k.val) := by
  apply h.2
  · unfold O.axisBase UniformAllAxisSeedPreparation.axisBase;omega
  · exact UniformAllAxisSeedPreparation.compact_address_before j j.isLt q k

/-- The loaded root stays at its original selected-axis address. -/
theorem Frame.selected_root {n : ℕ} {s u : State} (h:Frame n s u)
    (j : Fin (O.axisCount n)) : u.scalarHeap (6+j.val)=s.scalarHeap (6+j.val) := by
  apply h.1.1
  rw [UniformConjugateLocalPreparation.globalEnd_formula]
  have hj:=j.isLt
  change j.val<ell n+1 at hj
  omega

theorem Frame.master_root {n : ℕ} {s u : State} (h:Frame n s u) : u.scalarHeap 0=s.scalarHeap 0 := by
  apply h.1.1
  rw [UniformConjugateLocalPreparation.globalEnd_formula];omega

/-- A physical original compact cell and its newly prepared conjugate cell
have equal conjugate values, including exact zeros; neither is inspected for zero. -/
theorem lane_pair {n : ℕ} {s u : State} (j : Fin (O.axisCount n))
    (hret:O.Retained n (O.axisCount n) s) (hnew:ConjugateCompact (radix n j) (destination n) u)
    (q : Fin 5) (k : Fin (radix n j)) : ∃v:ℂ,
    s.scalarHeap (O.axisBase n j.val+q.val*radix n j+k.val)=some (prepared v) ∧
    u.scalarHeap (destination n+q.val*radix n j+k.val)=some (prepared (starRingEnd ℂ v)) :=
  ⟨_,hret.coefficients j j.isLt q k,hnew q k⟩

theorem runtime_quadratic (n : ℕ) (j : Fin (O.axisCount n)) :
    UniformReciprocalMachine.completeRuntime (radix n j)+40*radix n j+148 ≤ 652*(radix n j)^2 := by
  have hb:=UniformConjugateLocalPreparation.runtime_quadratic n j
  have hr:=UniformConjugateLocalPreparation.radix_pos n j
  change UniformReciprocalMachine.completeRuntime (radix n j)+32 ≤ 496*(radix n j)^2 at hb
  nlinarith [sq_nonneg ((radix n j:ℤ)-1)]

end
end ExactFourierCircuits.UniformSeedConjugatePreparation
