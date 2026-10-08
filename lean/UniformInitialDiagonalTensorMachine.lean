import UniformAllAxisDiagonalPreparation
import UniformAllAxisSeedCost

set_option autoImplicit false

namespace ExactFourierCircuits.UniformInitialDiagonalTensorMachine
open UniformMachine UniformAssembly
open UniformInitialPreparation (ell len)
open UniformAllAxisSeedPreparation (axisCount radix prefixSum axisBase directoryBase Retained ProtectedFrame)
open UniformAllAxisDiagonalPreparation (rowPool permutationPool coefficientPool)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
noncomputable section

/-- The lane is a finite literal program parameter. No length-dependent program,
ready tensor bank, or prefilled caller descriptor is supplied. -/
def constants : List Op := [.literal 420 0,.literal 421 1,.literal 422 2,
  .literal 423 3,.literal 424 5,.literal 425 8,.literal 426 20,.literal 427 24]
def address (q : Fin 5) : List Op := [.add 330 102 421,.add 331 105 106,
  .add 331 331 103,.literal 332 q.val,.mul 428 102 422,.add 428 331 428]
def fetch : List Op := [.getNat 429 428,.add 428 428 421,.getNat 430 428]
def pool : List Op := [.mul 431 430 424,.add 335 429 431,.add 432 102 427,
  .mul 433 101 422,.add 432 432 433,.mul 433 103 426,.add 432 432 433,.sub 434 335 432]
def caller : List Op := [.mul 435 330 422,.add 333 331 435,.mul 435 330 423,
  .add 334 333 435,.add 6 334 434,.add 16 335 434,.add 15 16 330,
  .add 1 330 420,.add 5 333 420,.add 7 102 425,.mul 433 101 422,
  .add 7 7 433,.mul 433 103 422,.add 7 7 433]
def setup (q : Fin 5) : Program := constants.map Op.code++(address q).map Op.code++
  fetch.map Op.code++pool.map Op.code++[.natBinary .div 434 434 424]++caller.map Op.code

def startupHead : Program := UniformAllAxisSeedPreparation.fullProgram.map (relocate 0 935)
def head (q : Fin 5) : Program := startupHead++setup q
def program (q : Fin 5) : Program := embed (head q) UniformAllAxisDiagonalPreparation.fullProgram [.halt] 1083

theorem constants_length : constants.length=8 := rfl
theorem address_length (q : Fin 5) : (address q).length=6 := rfl
theorem fetch_length : fetch.length=3 := rfl
theorem pool_length : pool.length=8 := rfl
theorem caller_length : caller.length=14 := rfl
theorem setup_length (q : Fin 5) : (setup q).length=40 := rfl
theorem startupHead_length : startupHead.length=935 := by
  simp only [startupHead,List.length_map,UniformAllAxisSeedPreparation.fullProgram_length]
theorem head_length (q : Fin 5) : (head q).length=975 := by
  rw [head,List.length_append,startupHead_length,setup_length]
theorem program_length (q : Fin 5) : (program q).length=1084 := by
  rw [program,embed_length,head_length,UniformAllAxisDiagonalPreparation.fullProgram_length];rfl

theorem startup_code (q : Fin 5) :
    CodeAt UniformAllAxisSeedPreparation.fullProgram (program q) 0 935 := by
  intro i hi
  have h935:i < 935:=by simpa only [UniformAllAxisSeedPreparation.fullProgram_length] using hi
  simp only [program,embed,Nat.zero_add]
  rw [List.getElem?_append_left (by rw [List.length_append,List.length_map,head_length,UniformAllAxisDiagonalPreparation.fullProgram_length];omega)]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head]
  rw [List.getElem?_append_left (by rw [startupHead_length];omega)]
  simp only [startupHead,List.getElem?_map]

theorem setup_lookup (q : Fin 5) (i : ℕ) (hi:i < 40) :
    (program q)[935+i]?=(setup q)[i]? := by
  simp only [program,embed]
  rw [List.getElem?_append_left (by rw [List.length_append,List.length_map,head_length,UniformAllAxisDiagonalPreparation.fullProgram_length];omega)]
  rw [List.getElem?_append_left (by rw [head_length];omega)]
  simp only [head]
  rw [List.getElem?_append_right (by rw [startupHead_length];omega)]
  simp only [startupHead_length,show 935+i-935=i by omega]

theorem constants_code (q : Fin 5) : BlockAt constants (program q) 935 := by
  intro i hi;change i < 8 at hi
  rw [setup_lookup q i (by omega)]
  interval_cases i <;> rfl

theorem address_code (q : Fin 5) : BlockAt (address q) (program q) 943 := by
  intro i hi;change i < 6 at hi
  rw [show 943+i=935+(8+i) by omega,setup_lookup q (8+i) (by omega)]
  interval_cases i <;> rfl

theorem fetch_code (q : Fin 5) : BlockAt fetch (program q) 949 := by
  intro i hi;change i < 3 at hi
  rw [show 949+i=935+(14+i) by omega,setup_lookup q (14+i) (by omega)]
  interval_cases i <;> rfl

theorem pool_code (q : Fin 5) : BlockAt pool (program q) 952 := by
  intro i hi;change i < 8 at hi
  rw [show 952+i=935+(17+i) by omega,setup_lookup q (17+i) (by omega)]
  interval_cases i <;> rfl

theorem divide_code (q : Fin 5) : (program q)[960]?=some (.natBinary .div 434 434 424) := by
  rw [show 960=935+25 by decide,setup_lookup q 25 (by decide)];rfl

theorem caller_code (q : Fin 5) : BlockAt caller (program q) 961 := by
  intro i hi;change i < 14 at hi
  rw [show 961+i=935+(26+i) by omega,setup_lookup q (26+i) (by omega)]
  interval_cases i <;> rfl

theorem diagonal_code (q : Fin 5) :
    CodeAt UniformAllAxisDiagonalPreparation.fullProgram (program q) 975 1083 := by
  simpa only [program,head_length] using embed_code (head q)
    UniformAllAxisDiagonalPreparation.fullProgram [.halt] 1083

theorem halt_code (q : Fin 5) : (program q)[1083]?=some .halt := by
  simp only [program,embed]
  rw [List.getElem?_append_right (by rw [List.length_append,List.length_map,head_length,
    UniformAllAxisDiagonalPreparation.fullProgram_length])]
  simp only [List.length_append,List.length_map,head_length,
    UniformAllAxisDiagonalPreparation.fullProgram_length]
  rfl

def totalRadices (n : ℕ) : ℕ := prefixSum n (axisCount n)
def natStack (n : ℕ) : ℕ := permutationPool n+totalRadices n
def scalarStack (n : ℕ) : ℕ := coefficientPool n+totalRadices n
def destination (n : ℕ) : ℕ := scalarStack n+axisCount n

theorem source_formula (n : ℕ) : UniformInputPermutationPreparation.destination n=ell n+8+2*n+2*len n := by
  dsimp [UniformInputPermutationPreparation.destination,UniformNormalizationPreparation.normBase,
    UniformChirpKernelPreparation.kernelBase,UniformPaddedInputPreparation.dataBase,ell,len];omega

theorem pool_formula (n : ℕ) : UniformLocalSeedTableMachine.poolBase n=ell n+24+2*n+20*len n := by
  rw [UniformLocalSeedTableMachine.poolBase,UniformGlobalLocalPreparation.globalEnd_formula];omega

theorem layout_envelope {n : ℕ} (hn:0 < n) :
    1084 ≤ (n+2)^19 ∧ natStack n+3*axisCount n ≤ (n+2)^19 ∧
    destination n+len n ≤ (n+2)^19 := by
  have he:ell n ≤ 2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount;omega
  have hL:len n < 4*n:=UniformWorkingLength.workingLength_upper hn
  have hT:=UniformAllAxisSeedPreparation.prefix_bound n (axisCount n) (le_refl _)
  have hprod:(ell n+1)*len n ≤ (2*n+1)*(4*n):=Nat.mul_le_mul (by omega) (by omega)
  have hT':totalRadices n ≤ (2*n+1)*(4*n):=hT.trans hprod
  have hs:300 ≤ (n+2)^17:=by
    have h:=Nat.pow_le_pow_left (show 3 ≤ n+2 by omega) 17;norm_num at h;omega
  have hb:300*(n+2)^2 ≤ (n+2)^19:=by
    rw [show 19=17+2 by decide,pow_add];exact Nat.mul_le_mul_right ((n+2)^2) hs
  have hnat:natStack n+3*axisCount n ≤ 300*(n+2)^2:=by
    unfold natStack UniformAllAxisDiagonalPreparation.permutationPool UniformAllAxisDiagonalPreparation.rowPool axisCount
    rw [UniformAllAxisSeedPreparation.directory_formula];nlinarith
  have hscalar:destination n+len n ≤ 300*(n+2)^2:=by
    unfold destination scalarStack UniformAllAxisDiagonalPreparation.coefficientPool axisBase
    rw [pool_formula];unfold totalRadices axisCount;nlinarith
  exact ⟨by nlinarith,hnat.trans hb,hscalar.trans hb⟩

def layout (n : ℕ) (hn:0 < n) : UniformTensorMonomialMachine.Layout where
  B := (n+2)^19
  ell := axisCount n
  row := rowPool n
  natStack := natStack n
  scalarStack := scalarStack n
  source := UniformInputPermutationPreparation.destination n
  destination := destination n
  volume := len n
  codeBound := by have h:=layout_envelope hn;omega
  rowsBelow := by unfold natStack UniformAllAxisDiagonalPreparation.permutationPool;omega
  natStackBound := by simpa only [Nat.mul_comm] using (layout_envelope hn).2.1
  scalarStackBound := by have h:=(layout_envelope hn).2.2;unfold destination at h;omega
  sourceBelow := by
    unfold scalarStack UniformAllAxisDiagonalPreparation.coefficientPool axisBase
    rw [pool_formula,source_formula];omega
  destinationAbove := le_refl _
  destinationBound := (layout_envelope hn).2.2

def afterConstants (s : State) : State := applyBlock constants s
def afterAddress (q : Fin 5) (s : State) : State := applyBlock (address q) (afterConstants s)
def afterFetch (q : Fin 5) (s : State) : State := applyBlock fetch (afterAddress q s)
def afterPool (q : Fin 5) (s : State) : State := applyBlock pool (afterFetch q s)
def afterDivide (q : Fin 5) (s : State) : State :=
  let v:=afterPool q s
  writeNat v 434 (v.natReg 434/v.natReg 424)
def setupState (q : Fin 5) (s : State) : State := applyBlock caller (afterDivide q s)

theorem constants_values (s : State) :
    (afterConstants s).natReg 420=0 ∧ (afterConstants s).natReg 421=1 ∧
    (afterConstants s).natReg 422=2 ∧ (afterConstants s).natReg 423=3 ∧
    (afterConstants s).natReg 424=5 ∧ (afterConstants s).natReg 425=8 ∧
    (afterConstants s).natReg 426=20 ∧ (afterConstants s).natReg 427=24 := by
  simp [afterConstants,applyBlock,constants,Op.apply,writeNat,next]

theorem address_values (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) :
    (afterAddress q s).natReg 330=axisCount n ∧
    (afterAddress q s).natReg 331=directoryBase n ∧
    (afterAddress q s).natReg 332=q.val ∧
    (afterAddress q s).natReg 428=directoryBase n+2*ell n := by
  simp [afterAddress,address,applyBlock,Op.apply,afterConstants,constants,writeNat,next,
    hm.saved.count,hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,
    UniformAllAxisSeedPreparation.directory_after_protected,axisCount,Nat.mul_comm]

def lastAxis (n : ℕ) : Fin (axisCount n) := ⟨ell n,by unfold axisCount;omega⟩

def Op.natDestination : Op → Option ℕ
  | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _ => some d
  | _ => none

theorem Op.nat_frame (o : Op) (i : ℕ) (s : State) (hi:Op.natDestination o ≠ some i) :
    (o.apply s).natReg i=s.natReg i := by
  cases o <;> simp_all [Op.natDestination,Op.apply,writeNat,writeScalar,next,Function.update]
  all_goals intro h;exact False.elim (hi h.symm)

def natDestinations (b : List Op) : List ℕ := b.filterMap Op.natDestination

theorem block_nat_frame (b : List Op) (i : ℕ) (s : State) (hi:i ∉ natDestinations b) :
    (applyBlock b s).natReg i=s.natReg i := by
  induction b generalizing s with
  | nil => rfl
  | cons o b ih =>
    have hb:i ∉ natDestinations b:=by
      intro h;apply hi;exact List.mem_filterMap.mpr (by
        obtain ⟨a,ha,hv⟩:=List.mem_filterMap.mp h;exact ⟨a,List.mem_cons_of_mem _ ha,hv⟩)
    have ho:Op.natDestination o ≠ some i:=by
      intro h;apply hi;exact List.mem_filterMap.mpr ⟨o,by simp,h⟩
    exact (ih (o.apply s) hb).trans (Op.nat_frame o i s ho)

theorem constants_nat (s : State) (i : ℕ) (hi:i < 420) :
    (afterConstants s).natReg i=s.natReg i :=
  block_nat_frame constants i s (by simp [natDestinations,constants,Op.natDestination];omega)

theorem address_nat (q : Fin 5) (s : State) (i : ℕ)
    (hi:i ≠ 330 ∧ i ≠ 331 ∧ i ≠ 332 ∧ i ≠ 428) :
    (afterAddress q s).natReg i=(afterConstants s).natReg i :=
  block_nat_frame (address q) i (afterConstants s) (by
    simp [natDestinations,address,Op.natDestination,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2])

theorem fetch_nat (q : Fin 5) (s : State) (i : ℕ)
    (hi:i ≠ 429 ∧ i ≠ 428 ∧ i ≠ 430) :
    (afterFetch q s).natReg i=(afterAddress q s).natReg i :=
  block_nat_frame fetch i (afterAddress q s) (by
    simp [natDestinations,fetch,Op.natDestination,hi.1,hi.2.1,hi.2.2])

theorem pool_nat (q : Fin 5) (s : State) (i : ℕ)
    (hi:i ≠ 431 ∧ i ≠ 335 ∧ i ≠ 432 ∧ i ≠ 433 ∧ i ≠ 434) :
    (afterPool q s).natReg i=(afterFetch q s).natReg i :=
  block_nat_frame pool i (afterFetch q s) (by
    simp [natDestinations,pool,Op.natDestination,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2])

theorem divide_nat (q : Fin 5) (s : State) (i : ℕ) (hi:i ≠ 434) :
    (afterDivide q s).natReg i=(afterPool q s).natReg i := by
  simp only [afterDivide,writeNat,Function.update_of_ne hi]

theorem fetched_constant (q : Fin 5) (s : State) (i : ℕ) (hi:420 ≤ i ∧ i ≤ 427) :
    (afterFetch q s).natReg i=(afterConstants s).natReg i := by
  rw [fetch_nat q s i (by omega),address_nat q s i (by omega)]

theorem divided_constant (q : Fin 5) (s : State) (i : ℕ) (hi:420 ≤ i ∧ i ≤ 427) :
    (afterDivide q s).natReg i=(afterConstants s).natReg i := by
  rw [divide_nat q s i (by omega),pool_nat q s i (by omega),fetched_constant q s i hi]

theorem fetched_saved (q : Fin 5) (s : State) (i : ℕ) (hi:100 ≤ i ∧ i ≤ 106) :
    (afterFetch q s).natReg i=s.natReg i := by
  rw [fetch_nat q s i (by omega),address_nat q s i (by omega),constants_nat s i (by omega)]

theorem divided_saved (q : Fin 5) (s : State) (i : ℕ) (hi:100 ≤ i ∧ i ≤ 106) :
    (afterDivide q s).natReg i=s.natReg i := by
  rw [divide_nat q s i (by omega),pool_nat q s i (by omega),fetched_saved q s i hi]

theorem fetch_values_of (s : State) (a A r : ℕ)
    (hp:s.natReg 428=a) (h1:s.natReg 421=1)
    (ha:s.natHeap a=some A) (hr:s.natHeap (a+1)=some r) :
    (applyBlock fetch s).natReg 429=A ∧ (applyBlock fetch s).natReg 430=r := by
  simp [fetch,applyBlock,Op.apply,writeNat,next,hp,h1,ha,hr]

theorem fetch_values (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    (afterFetch q s).natReg 429=axisBase n (ell n) ∧
    (afterFetch q s).natReg 430=radix n (lastAxis n) := by
  apply fetch_values_of (afterAddress q s) (directoryBase n+2*ell n)
  · exact (address_values n q s hm).2.2.2
  · rw [address_nat q s 421 (by decide)];exact (constants_values s).2.1
  · exact hr.address (lastAxis n) (lastAxis n).isLt
  · exact hr.width (lastAxis n) (lastAxis n).isLt

theorem pool_values_of (s : State) (e n L A r T : ℕ)
    (h102:s.natReg 102=e) (h101:s.natReg 101=n) (h103:s.natReg 103=L)
    (h429:s.natReg 429=A) (h430:s.natReg 430=r)
    (h422:s.natReg 422=2) (h424:s.natReg 424=5) (h426:s.natReg 426=20) (h427:s.natReg 427=24)
    (hA:A+5*r=e+24+2*n+20*L+5*T) :
    (applyBlock pool s).natReg 335=A+5*r ∧
    (applyBlock pool s).natReg 432=e+24+2*n+20*L ∧
    (applyBlock pool s).natReg 434=5*T := by
  simp [pool,applyBlock,Op.apply,writeNat,next,h102,h101,h103,h429,h430,h422,h424,h426,h427,Nat.mul_comm]
  omega

theorem pool_values (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    (afterPool q s).natReg 335=coefficientPool n ∧
    (afterPool q s).natReg 432=UniformLocalSeedTableMachine.poolBase n ∧
    (afterPool q s).natReg 434=5*totalRadices n := by
  have hlast:=UniformAllAxisSeedPreparation.axisBase_next n (lastAxis n)
  change coefficientPool n=axisBase n (ell n)+5*radix n (lastAxis n) at hlast
  have hf:=fetch_values n q s hm hr
  have hfields:=(constants_values s)
  have hp:=pool_values_of (afterFetch q s) (ell n) n (len n) (axisBase n (ell n))
    (radix n (lastAxis n)) (totalRadices n)
    ((fetched_saved q s 102 (by decide)).trans hm.saved.count)
    ((fetched_saved q s 101 (by decide)).trans hm.saved.inputLength)
    ((fetched_saved q s 103 (by decide)).trans hm.saved.workingLength)
    hf.1 hf.2
    ((fetched_constant q s 422 (by decide)).trans hfields.2.2.1)
    ((fetched_constant q s 424 (by decide)).trans hfields.2.2.2.2.1)
    ((fetched_constant q s 426 (by decide)).trans hfields.2.2.2.2.2.2.1)
    ((fetched_constant q s 427 (by decide)).trans hfields.2.2.2.2.2.2.2)
    (by rw [←hlast];unfold coefficientPool axisBase totalRadices;rw [pool_formula])
  exact ⟨hp.1.trans hlast.symm,hp.2.1.trans (pool_formula n).symm,hp.2.2⟩

theorem divided_values (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    (afterDivide q s).natReg 434=totalRadices n := by
  have hp:=pool_values n q s hm hr
  have h424:(afterPool q s).natReg 424=5:=
    (pool_nat q s 424 (by decide)).trans ((fetched_constant q s 424 (by decide)).trans
      (constants_values s).2.2.2.2.1)
  simp [afterDivide,writeNat,hp.2.2,h424]

structure CallerInput (n : ℕ) (q : Fin 5) (s : State) : Prop where
  count : s.natReg 330=axisCount n
  directory : s.natReg 331=directoryBase n
  lane : s.natReg 332=q.val
  coefficient : s.natReg 335=coefficientPool n
  total : s.natReg 434=totalRadices n
  savedCount : s.natReg 102=ell n
  savedLength : s.natReg 101=n
  savedVolume : s.natReg 103=len n
  zero : s.natReg 420=0
  two : s.natReg 422=2
  three : s.natReg 423=3
  eight : s.natReg 425=8

theorem caller_input (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    CallerInput n q (afterDivide q s) := by
  have ha:=address_values n q s hm
  have hp:=pool_values n q s hm hr
  have hc:=constants_values s
  refine ⟨?_,?_,?_,?_,divided_values n q s hm hr,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [divide_nat q s 330 (by decide),pool_nat q s 330 (by decide),fetch_nat q s 330 (by decide)];exact ha.1
  · rw [divide_nat q s 331 (by decide),pool_nat q s 331 (by decide),fetch_nat q s 331 (by decide)];exact ha.2.1
  · rw [divide_nat q s 332 (by decide),pool_nat q s 332 (by decide),fetch_nat q s 332 (by decide)];exact ha.2.2.1
  · rw [divide_nat q s 335 (by decide)];exact hp.1
  · exact (divided_saved q s 102 (by decide)).trans hm.saved.count
  · exact (divided_saved q s 101 (by decide)).trans hm.saved.inputLength
  · exact (divided_saved q s 103 (by decide)).trans hm.saved.workingLength
  · exact (divided_constant q s 420 (by decide)).trans hc.1
  · exact (divided_constant q s 422 (by decide)).trans hc.2.2.1
  · exact (divided_constant q s 423 (by decide)).trans hc.2.2.2.1
  · exact (divided_constant q s 425 (by decide)).trans hc.2.2.2.2.2.1

theorem caller_header_of (n : ℕ) (q : Fin 5) (s : State) (h:CallerInput n q s) :
    UniformAllAxisDiagonalPreparation.Header n (rowPool n) (permutationPool n) (coefficientPool n) q
      (applyBlock caller s) := by
  constructor <;> simp [caller,applyBlock,Op.apply,writeNat,next,h.count,h.directory,h.lane,h.coefficient,
    h.two,h.three,UniformAllAxisDiagonalPreparation.rowPool,
    UniformAllAxisDiagonalPreparation.permutationPool,Nat.mul_comm]

theorem caller_call_of {n : ℕ} (hn:0 < n) (q : Fin 5) (s : State) (h:CallerInput n q s) :
    UniformTensorMonomialMachine.Call (layout n hn) (applyBlock caller s) := by
  constructor <;> simp [caller,applyBlock,Op.apply,writeNat,next,layout,h.count,h.directory,h.coefficient,
    h.total,h.savedCount,h.savedLength,h.savedVolume,h.zero,h.two,h.three,h.eight,source_formula,
    natStack,scalarStack,destination,UniformAllAxisDiagonalPreparation.rowPool,
    UniformAllAxisDiagonalPreparation.permutationPool,Nat.mul_comm]

theorem setup_header (n : ℕ) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    UniformAllAxisDiagonalPreparation.Header n (rowPool n) (permutationPool n) (coefficientPool n) q
      (setupState q s) := caller_header_of n q _ (caller_input n q s hm hr)

theorem setup_call {n : ℕ} (hn:0 < n) (q : Fin 5) (s : State)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s) :
    UniformTensorMonomialMachine.Call (layout n hn) (setupState q s) :=
  caller_call_of hn q _ (caller_input n q s hm hr)

theorem setup_pc (q : Fin 5) (s : State) : (setupState q s).pc=s.pc+40 := by
  simp [setupState,afterDivide,afterPool,afterFetch,afterAddress,afterConstants,
    UniformTensorMonomialMachine.applyBlock_pc,writeNat,next,
    constants_length,address_length,fetch_length,pool_length,caller_length]

theorem setup_frame (n : ℕ) (q : Fin 5) (s : State) : ProtectedFrame n s (setupState q s) := by
  refine ⟨fun _ _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
  intro i hi hj
  have hc:=block_nat_frame caller i (afterDivide q s) (by
    simp [natDestinations,caller,Op.natDestination];omega)
  exact hc.trans (divided_saved q s i ⟨hi,hj⟩)

theorem setup_retained (n : ℕ) (q : Fin 5) (s : State) (hr:Retained n (axisCount n) s) :
    Retained n (axisCount n) (setupState q s) := ⟨hr.coefficients,hr.address,hr.width⟩

structure SetupBounds (n B : ℕ) : Prop where
  code : 1084 ≤ B
  directory : directoryBase n+2*ell n+1 ≤ B
  coefficient : coefficientPool n ≤ B
  natStack : natStack n ≤ B
  scalarEnd : scalarStack n+axisCount n ≤ B

theorem selected_setup_bounds {n : ℕ} (hn:0 < n) : SetupBounds n ((n+2)^19) := by
  have h:=layout_envelope hn
  have hd:directoryBase n+2*ell n+1 ≤ natStack n:=by
    unfold natStack UniformAllAxisDiagonalPreparation.permutationPool
      UniformAllAxisDiagonalPreparation.rowPool axisCount;omega
  have hc:coefficientPool n ≤ destination n:=by unfold destination scalarStack;omega
  exact ⟨h.1,by omega,by omega,by omega,by unfold destination at h;omega⟩

theorem constants_safe (s : State) (B : ℕ) (hB:24 ≤ B) :
    readable constants s ∧ peak constants s ≤ B := by
  simp [constants,readable,Op.readable,peak,Op.peak];omega

theorem address_safe (n : ℕ) (q : Fin 5) (s : State) (B : ℕ)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hB:SetupBounds n B) :
    readable (address q) (afterConstants s) ∧ peak (address q) (afterConstants s) ≤ B := by
  have hq:=q.isLt
  have hd:=hB.directory;have hb:=hB.code
  have hdir:=UniformAllAxisSeedPreparation.directory_formula n
  have h421:=(constants_values s).2.1
  have h422:=(constants_values s).2.2.1
  have h102:(afterConstants s).natReg 102=ell n:=(constants_nat s 102 (by decide)).trans hm.saved.count
  have h105:(afterConstants s).natReg 105=UniformInitialPreparation.copyBase n:=
    (constants_nat s 105 (by decide)).trans hm.saved.copyAddress
  have h106:(afterConstants s).natReg 106=UniformGlobalNatPreparation.amount (ell n) (len n):=
    (constants_nat s 106 (by decide)).trans hm.saved.copyLength
  have h103:(afterConstants s).natReg 103=len n:=
    (constants_nat s 103 (by decide)).trans hm.saved.workingLength
  simp [address,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    h421,h422,h102,h105,h106,h103,Nat.mul_comm]
  have hf:=UniformAllAxisSeedPreparation.directory_after_protected n
  omega

theorem fetch_safe_of (s : State) (a A r B : ℕ) (hp:s.natReg 428=a) (h1:s.natReg 421=1)
    (ha:s.natHeap a=some A) (hr:s.natHeap (a+1)=some r) (hA:A ≤ B) (hR:r ≤ B) (hab:a+1 ≤ B) :
    readable fetch s ∧ peak fetch s ≤ B := by
  simp [fetch,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,hp,h1,ha,hr];omega

theorem fetch_safe (n : ℕ) (q : Fin 5) (s : State) (B : ℕ)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s)
    (hB:SetupBounds n B) : readable fetch (afterAddress q s) ∧ peak fetch (afterAddress q s) ≤ B := by
  have hl:=UniformAllAxisSeedPreparation.axisBase_next n (lastAxis n)
  change coefficientPool n=axisBase n (ell n)+5*radix n (lastAxis n) at hl
  have hc:=hB.coefficient
  apply fetch_safe_of (afterAddress q s) (directoryBase n+2*ell n)
    (axisBase n (ell n)) (radix n (lastAxis n)) B
    (address_values n q s hm).2.2.2
    ((address_nat q s 421 (by decide)).trans (constants_values s).2.1)
    (hr.address (lastAxis n) (lastAxis n).isLt) (hr.width (lastAxis n) (lastAxis n).isLt)
    (by omega) (by omega) hB.directory

theorem pool_safe_of (s : State) (e n L A r T B : ℕ)
    (h102:s.natReg 102=e) (h101:s.natReg 101=n) (h103:s.natReg 103=L)
    (h429:s.natReg 429=A) (h430:s.natReg 430=r)
    (h422:s.natReg 422=2) (h424:s.natReg 424=5) (h426:s.natReg 426=20) (h427:s.natReg 427=24)
    (hA:A+5*r=e+24+2*n+20*L+5*T) (hB:A+5*r ≤ B) :
    readable pool s ∧ peak pool s ≤ B := by
  simp [pool,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    h102,h101,h103,h429,h430,h422,h424,h426,h427];omega

theorem pool_safe (n : ℕ) (q : Fin 5) (s : State) (B : ℕ)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s)
    (hB:SetupBounds n B) : readable pool (afterFetch q s) ∧ peak pool (afterFetch q s) ≤ B := by
  have hlast:=UniformAllAxisSeedPreparation.axisBase_next n (lastAxis n)
  change coefficientPool n=axisBase n (ell n)+5*radix n (lastAxis n) at hlast
  have hf:=fetch_values n q s hm hr
  have hc:=constants_values s
  exact pool_safe_of (afterFetch q s) (ell n) n (len n) (axisBase n (ell n))
    (radix n (lastAxis n)) (totalRadices n) B
    ((fetched_saved q s 102 (by decide)).trans hm.saved.count)
    ((fetched_saved q s 101 (by decide)).trans hm.saved.inputLength)
    ((fetched_saved q s 103 (by decide)).trans hm.saved.workingLength)
    hf.1 hf.2
    ((fetched_constant q s 422 (by decide)).trans hc.2.2.1)
    ((fetched_constant q s 424 (by decide)).trans hc.2.2.2.2.1)
    ((fetched_constant q s 426 (by decide)).trans hc.2.2.2.2.2.2.1)
    ((fetched_constant q s 427 (by decide)).trans hc.2.2.2.2.2.2.2)
    (by rw [←hlast];unfold coefficientPool axisBase totalRadices;rw [pool_formula])
    (hlast ▸ hB.coefficient)

theorem caller_safe_of (n : ℕ) (q : Fin 5) (s : State) (B : ℕ)
    (h:CallerInput n q s) (hB:SetupBounds n B) : readable caller s ∧ peak caller s ≤ B := by
  have hn:=hB.natStack;have hc:=hB.scalarEnd
  have hsource:UniformInputPermutationPreparation.destination n ≤ scalarStack n:=by
    unfold scalarStack UniformAllAxisDiagonalPreparation.coefficientPool axisBase
    rw [pool_formula,source_formula];omega
  have hcoef:coefficientPool n=ell n+24+2*n+20*len n+5*totalRadices n:=by
    unfold coefficientPool axisBase totalRadices;rw [pool_formula]
  simp [caller,readable,Op.readable,peak,Op.peak,Op.apply,writeNat,next,
    h.count,h.directory,h.coefficient,h.total,h.savedCount,h.savedLength,h.savedVolume,
    h.zero,h.two,h.three,h.eight,Nat.mul_comm]
  unfold natStack scalarStack UniformAllAxisDiagonalPreparation.permutationPool
    UniformAllAxisDiagonalPreparation.rowPool axisCount at *
  rw [source_formula] at hsource
  omega

theorem setup_bounded (n : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State) (B : ℕ)
    (hm:UniformPermutationInversePreparation.Metadata n s) (hr:Retained n (axisCount n) s)
    (hB:SetupBounds n B) (hpc:s.pc=935) (hs:WordBound B s) :
    BoundedRuns (program q) n x B s 40 (setupState q s) := by
  have hcode:=hB.code
  have cs:=constants_safe s B (by omega)
  have cRun:=block_runs constants (program q) 935 n B x s (constants_code q) hpc hs
    (by rw [constants_length];omega) cs.1 cs.2
  have ac:=(address_safe n q s B hm hB)
  have aRun:=block_runs (address q) (program q) 943 n B x (afterConstants s) (address_code q)
    (by rw [afterConstants,UniformTensorMonomialMachine.applyBlock_pc,constants_length,hpc])
    cRun.final_bound (by rw [address_length];omega) ac.1 ac.2
  have fs:=fetch_safe n q s B hm hr hB
  have fRun:=block_runs fetch (program q) 949 n B x (afterAddress q s) (fetch_code q)
    (by simp [afterAddress,afterConstants,UniformTensorMonomialMachine.applyBlock_pc,
      constants_length,address_length,hpc])
    aRun.final_bound (by rw [fetch_length];omega) fs.1 fs.2
  have ps:=pool_safe n q s B hm hr hB
  have pRun:=block_runs pool (program q) 952 n B x (afterFetch q s) (pool_code q)
    (by simp [afterFetch,afterAddress,afterConstants,UniformTensorMonomialMachine.applyBlock_pc,
      constants_length,address_length,fetch_length,hpc])
    fRun.final_bound (by rw [pool_length];omega) ps.1 ps.2
  have pp:(afterPool q s).pc=960:=by
    simp [afterPool,afterFetch,afterAddress,afterConstants,UniformTensorMonomialMachine.applyBlock_pc,
      constants_length,address_length,fetch_length,pool_length,hpc]
  have h424:(afterPool q s).natReg 424=5:=
    (pool_nat q s 424 (by decide)).trans ((fetched_constant q s 424 (by decide)).trans
      (constants_values s).2.2.2.2.1)
  have hpv:=pool_values n q s hm hr
  have hbv:totalRadices n ≤ B:=by
    have h:=hB.coefficient
    have he:coefficientPool n=UniformLocalSeedTableMachine.poolBase n+5*totalRadices n:=rfl
    omega
  have dv:WordBound B (afterDivide q s):=by
    apply writeNat_bound B (afterPool q s) 434 _ pRun.final_bound (by rw [pp];omega)
    simp only [h424,hpv.2.2]
    omega
  have dRun:BoundedRuns (program q) n x B (afterPool q s) 1 (afterDivide q s):=by
    refine .next pRun.final_bound ?_ (.refl dv)
    simp [step,pp,divide_code,evalNat,h424,afterDivide]
  have cv:=caller_safe_of n q (afterDivide q s) B (caller_input n q s hm hr) hB
  have final:=block_runs caller (program q) 961 n B x (afterDivide q s) (caller_code q)
    (by simp [afterDivide,writeNat,next,pp]) dv (by rw [caller_length];omega) cv.1 cv.2
  convert cRun.trans (aRun.trans (fRun.trans (pRun.trans (dRun.trans final)))) using 1 <;> rfl

def selectedAxes (n : ℕ) (q : Fin 5) : List UniformTensorMonomialMachine.Axis :=
  UniformAllAxisDiagonalPreparation.axes n q (permutationPool n) (coefficientPool n)
def passCost (n : ℕ) : ℕ := 9*totalRadices n+27*axisCount n+
  UniformTensorMonomialMachine.treeCost (UniformSelectedDFSMachine.selectedRadices n)+18

/-- Strengthen the frozen108 theorem by deriving its protected frame from
its actual physical producer and actual recursive tensor execution. -/
theorem pass_execution {n : ℕ} (hn:0 < n) (q : Fin 5) (x : Fin n → ℂ) (s : State)
    (h:UniformAllAxisDiagonalPreparation.Header n (rowPool n) (permutationPool n) (coefficientPool n) q s)
    (hr:Retained n (axisCount n) s) (hcall:UniformTensorMonomialMachine.Call (layout n hn) s)
    (hsrc:UniformTensorMonomialMachine.SourceAt (layout n hn) s) (hpc:s.pc=0)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution UniformAllAxisDiagonalPreparation.fullProgram n x ((n+2)^19) s (passCost n) u ∧
    ProtectedFrame n s u ∧ Retained n (axisCount n) u ∧
    ∀j:Fin (UniformTensorMonomialMachine.radices (selectedAxes n q)).prod,∀v,
      s.scalarHeap ((layout n hn).source+j.val)=some v →
      u.scalarHeap ((layout n hn).destination+
        (UniformTensorMonomialMachine.tensorPermutation (selectedAxes n q) j).val)=
      some (UniformPairMachine.product (UniformTensorMonomialMachine.tensorCoefficient (selectedAxes n q) j) v) := by
  let L:=layout n hn
  have hLB:L.B=(n+2)^19:=rfl
  have l:=UniformAllAxisDiagonalPreparation.selected_pools_fit hn
  have hbig:=(layout_envelope hn).1
  have hinput:L.source+L.volume ≤ coefficientPool n:=by
    change UniformInputPermutationPreparation.destination n+len n ≤ coefficientPool n
    unfold coefficientPool axisBase;rw [source_formula,pool_formula];omega
  obtain ⟨t,run,tp,_,_,tr,tw,tf⟩:=UniformAllAxisDiagonalPreparation.execution n (rowPool n)
    (permutationPool n) (coefficientPool n) ((n+2)^19) q x s h hr l hpc hs
  have banks:=UniformAllAxisDiagonalPreparation.written_banks n (permutationPool n) (coefficientPool n) q L t tw
    (le_refl _) (le_refl _)
  let entry:=setPC t 0
  have eb:WordBound L.B entry:=changePC_bound _ t 0 run.final_bound (by omega)
  have ec:UniformTensorMonomialMachine.Call L entry:=by
    constructor
    · exact (tf.2.2.1 1 (by omega) (by omega)).trans hcall.axes
    · exact (tf.2.2.1 5 (by omega) (by omega)).trans hcall.row
    · exact (tf.2.2.1 6 (by omega) (by omega)).trans hcall.natStack
    · exact (tf.2.2.1 7 (by omega) (by omega)).trans hcall.source
    · exact (tf.2.2.1 15 (by omega) (by omega)).trans hcall.destination
    · exact (tf.2.2.1 16 (by omega) (by omega)).trans hcall.scalarStack
  have es:UniformTensorMonomialMachine.SourceAt L entry:=by
    intro j hj
    obtain ⟨v,hv⟩:=hsrc j hj
    exact ⟨v,(tf.2.2.2.2.2 _ (Or.inl (by omega))).trans hv⟩
  have be:=UniformTensorMonomialMachine.banks_transfer (selectedAxes n q) 0 L t entry
    (by rw [selectedAxes,UniformAllAxisDiagonalPreparation.axes_length];change 0+axisCount n ≤ axisCount n;omega)
    banks (fun _ _=>rfl) (fun _ _=>rfl)
  obtain ⟨consumer,ce,action⟩:=UniformTensorMonomialMachine.tensor_execution (selectedAxes n q) L n x entry rfl
    (UniformAllAxisDiagonalPreparation.axes_length n q _ _).symm
    (UniformAllAxisDiagonalPreparation.axes_volume n _ _ q).symm ec be es eb
  have producer:=UniformBoundedAssembly.boundedExecution_placed UniformAllAxisDiagonalPreparation.producer_code
    (by rw [UniformAllAxisDiagonalPreparation.program_length];omega) (by omega) run
  let final:=setPC (UniformTensorMonomialMachine.finalState (selectedAxes n q) entry) 107
  have tensor:=UniformBoundedAssembly.boundedExecution_placed UniformAllAxisDiagonalPreparation.tensor_code
    (by rw [UniformTensorMonomialMachine.program_length];omega) (by omega) consumer
  have tensorStart:placed 41 entry=setPC t 41:=rfl
  have initialEq:placed 0 s=s:=by
    change setPC s (0+s.pc)=s;simpa using UniformAllAxisDiagonalPreparation.setPC_same s s.pc rfl
  rw [initialEq] at producer
  rw [tensorStart] at tensor
  have halt:BoundedExecution UniformAllAxisDiagonalPreparation.fullProgram n x L.B final 1 final:=
    .halt tensor.final_bound (by simp [step,final,setPC,UniformAllAxisDiagonalPreparation.full_halt])
  have hf:ProtectedFrame n s t:=UniformAllAxisDiagonalPreparation.protected_frame l tf
  have globalLow:UniformGlobalLocalPreparation.globalEnd n ≤ L.scalarStack:=by
    change UniformGlobalLocalPreparation.globalEnd n ≤ coefficientPool n+totalRadices n
    unfold coefficientPool axisBase UniformLocalSeedTableMachine.poolBase;omega
  have directoryLow:directoryBase n+2*axisCount n ≤ L.natStack:=by
    change directoryBase n+2*axisCount n ≤ natStack n
    unfold natStack UniformAllAxisDiagonalPreparation.permutationPool UniformAllAxisDiagonalPreparation.rowPool;omega
  have cf:ProtectedFrame n t final:=by
    refine ⟨?_,?_,?_,ce.frame.2.1,ce.frame.1⟩
    · intro a _ ha;exact ce.natFrame a (Or.inl (by omega))
    · intro a ha;exact ce.scalarLow a (by omega)
    · intro i hi _;exact ce.frame.2.2.1 i (by omega)
  have cr:Retained n (axisCount n) final:=by
    constructor
    · intro j hj b i
      have ha:=UniformAllAxisSeedPreparation.compact_address_before j hj b i
      have hbound:axisBase n (axisCount n) ≤ L.scalarStack:=by
        change coefficientPool n ≤ coefficientPool n+totalRadices n;omega
      exact (ce.scalarLow _ (by omega)).trans (tr.coefficients j hj b i)
    · intro j hj
      have hj':=j.isLt
      exact (ce.natFrame _ (Or.inl (by omega))).trans (tr.address j hj)
    · intro j hj
      have hj':=j.isLt
      exact (ce.natFrame _ (Or.inl (by omega))).trans (tr.width j hj)
  refine ⟨final,?_,hf.trans cf,cr,?_⟩
  · convert producer.executes (tensor.executes halt) using 1
    rw [selectedAxes,UniformAllAxisDiagonalPreparation.axes_radices]
    unfold passCost totalRadices;omega
  · intro j v hv
    apply action j v
    have hj:j.val < L.volume:=by
      change j.val < len n
      rw [←UniformAllAxisDiagonalPreparation.axes_volume n (permutationPool n) (coefficientPool n) q]
      exact j.isLt
    exact (tf.2.2.2.2.2 _ (Or.inl (by omega))).trans hv

theorem tensorPermutation_identity (as : List UniformTensorMonomialMachine.Axis)
    (h:∀a∈as,a.permutation=Equiv.refl _) :
    UniformTensorMonomialMachine.tensorPermutation as=Equiv.refl _ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha:=h a (by simp)
    have ht:=ih (fun b hb=>h b (by simp [hb]))
    ext j
    simp only [UniformTensorMonomialMachine.tensorPermutation,ha,ht]
    change (finProdFinEquiv (finProdFinEquiv.symm j)).val=j.val
    change Fin (a.radix*(UniformTensorMonomialMachine.radices as).prod) at j
    exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)

theorem selected_permutation_identity (n : ℕ) (q : Fin 5) :
    UniformTensorMonomialMachine.tensorPermutation (selectedAxes n q)=Equiv.refl _ := by
  apply tensorPermutation_identity
  intro a ha
  simp only [selectedAxes,UniformAllAxisDiagonalPreparation.axes,List.mem_ofFn] at ha
  obtain ⟨j,rfl⟩:=ha
  rfl

def coefficient (n : ℕ) (q : Fin 5) (j : Fin (len n)) : ℂ :=
  UniformTensorMonomialMachine.tensorCoefficient (selectedAxes n q)
    (Fin.cast (UniformAllAxisDiagonalPreparation.axes_volume n (permutationPool n) (coefficientPool n) q).symm j)
def gathered (n : ℕ) (x : Fin n → ℂ) (j : Fin (len n)) : Scalar :=
  UniformPaddedInputMachine.paddedScalar (OAI.ExactFourier.zeta (2*n)) x
    (UniformCRTTraversalCycle.alphaPermutation n j).val

def runtime (n t : ℕ) : ℕ := t+UniformAllAxisSeedPreparation.preparationRuntime n+1+40+passCost n+1

/-- The startup/header boundary exposes only proved physical state facts. -/
structure Ready (n : ℕ) (hn:0 < n) (q : Fin 5) (x : Fin n → ℂ) (s : State) : Prop where
  metadata : UniformPermutationInversePreparation.Metadata n s
  operands : UniformInitialPreparation.Operands n x s
  retained : Retained n (axisCount n) s
  input : ∀j:Fin (len n),s.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some (gathered n x j)
  inverse : UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
    s.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm
  roots : s.rootOrders=[UniformMasterRootMachine.order n]
  outputs : s.outputs=initial.outputs
  pc : s.pc=975
  header : UniformAllAxisDiagonalPreparation.Header n (rowPool n) (permutationPool n) (coefficientPool n) q s
  call : UniformTensorMonomialMachine.Call (layout n hn) s

theorem prepare_execution {n : ℕ} (hn:0 < n) (q : Fin 5) (x : Fin n → ℂ) : ∃t u,
    BoundedRuns (program q) n x ((n+2)^19) initial
      (t+UniformAllAxisSeedPreparation.preparationRuntime n+1+40) u ∧
    t ≤ UniformPermutationInversePreparation.preparationBudget n ∧ Ready n hn q x u := by
  obtain ⟨t,s,start,ht,hr,hm,ho,hinput,hbeta,hroot,hout,_,_⟩:=UniformAllAxisSeedPreparation.initial_execution hn x
  have hbig:=(layout_envelope hn).1
  have startup:=UniformBoundedAssembly.boundedExecution_placed (startup_code q)
    (by rw [UniformAllAxisSeedPreparation.fullProgram_length];omega) (by omega) start
  change BoundedRuns (program q) n x ((n+2)^19) initial
    (t+UniformAllAxisSeedPreparation.preparationRuntime n+1) (setPC s 935) at startup
  let entry:=setPC s 935
  have me:UniformPermutationInversePreparation.Metadata n entry:=hm.transport (fun _ _=>rfl) (fun _ _=>rfl)
  have re:Retained n (axisCount n) entry:=hr.withPC
  have setupRun:=setup_bounded n q x entry ((n+2)^19) me re (selected_setup_bounds hn) rfl startup.final_bound
  have frame:ProtectedFrame n s (setupState q entry):=setup_frame n q entry
  refine ⟨t,setupState q entry,startup.trans setupRun,ht,?_,⟩
  refine ⟨frame.metadata hm,frame.operands ho,setup_retained n q entry re,?_,frame.beta_inverse hbeta,
    frame.2.2.2.2.trans hroot,frame.2.2.2.1.trans hout,?_,setup_header n q entry me re,setup_call hn q entry me re⟩
  · intro j;exact (frame.alpha_copied j).trans (hinput j)
  · rw [setup_pc];rfl

theorem Ready.source {n : ℕ} {hn:0 < n} {q : Fin 5} {x : Fin n → ℂ} {s : State}
    (h:Ready n hn q x s) : UniformTensorMonomialMachine.SourceAt (layout n hn) s := by
  intro j hj
  exact ⟨gathered n x ⟨j,hj⟩,h.input ⟨j,hj⟩⟩

theorem Call.withPC {L : UniformTensorMonomialMachine.Layout} {s : State}
    (h:UniformTensorMonomialMachine.Call L s) (pc : ℕ) : UniformTensorMonomialMachine.Call L (setPC s pc) :=
  ⟨h.axes,h.row,h.natStack,h.source,h.destination,h.scalarStack⟩

/-- Empty-state startup, actual charged header installation, produced physical
banks and one complete tensor diagonal pass. The result is in the literal
Horner tensor coordinates of the frozen66 consumer; no global fast DFT or
CRT-to-tensor scheduler is asserted. -/
theorem initial_execution {n : ℕ} (hn:0 < n) (q : Fin 5) (x : Fin n → ℂ) : ∃t u,
    BoundedExecution (program q) n x ((n+2)^19) initial (runtime n t) u ∧
    t ≤ UniformPermutationInversePreparation.preparationBudget n ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    Retained n (axisCount n) u ∧
    UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
      u.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧ u.pc=1083 ∧
    (∀j:Fin (len n),u.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some (gathered n x j)) ∧
    (∀j:Fin (len n),u.scalarHeap (destination n+j.val)=
      some (UniformPairMachine.product (coefficient n q j) (gathered n x j))) := by
  obtain ⟨t,s,setupRun,ht,ready⟩:=prepare_execution hn q x
  have hbig:=(layout_envelope hn).1
  let entry:=setPC s 0
  have eb:=changePC_bound ((n+2)^19) s 0 setupRun.final_bound (by omega)
  have head:UniformAllAxisDiagonalPreparation.Header n (rowPool n) (permutationPool n) (coefficientPool n) q entry:=
    UniformAllAxisDiagonalPreparation.header_withPC ready.header
  have call:=Call.withPC ready.call 0
  have src:UniformTensorMonomialMachine.SourceAt (layout n hn) entry:=ready.source
  obtain ⟨v,pass,hpf,hvr,action⟩:=pass_execution hn q x entry head ready.retained.withPC call src rfl eb
  have joined:=UniformBoundedAssembly.boundedExecution_placed (diagonal_code q)
    (by rw [UniformAllAxisDiagonalPreparation.fullProgram_length];omega) (by omega) pass
  have heq:placed 975 entry=s:=by
    change setPC s (975+0)=s
    exact UniformAllAxisDiagonalPreparation.setPC_same s _ ready.pc
  rw [heq] at joined
  let final:=setPC v 1083
  have last:BoundedExecution (program q) n x ((n+2)^19) final 1 final:=
    .halt joined.final_bound (by simp [step,final,setPC,halt_code])
  have frame:ProtectedFrame n s final:=hpf
  refine ⟨t,final,?_,ht,frame.metadata ready.metadata,frame.operands ready.operands,
    hvr.withPC,frame.beta_inverse ready.inverse,frame.2.2.2.2.trans ready.roots,
    frame.2.2.2.1.trans ready.outputs,rfl,?_,?_⟩
  · convert setupRun.executes (joined.executes last) using 1
    unfold runtime;omega
  · intro j;exact (frame.alpha_copied j).trans (ready.input j)
  · intro j
    let k:Fin (UniformTensorMonomialMachine.radices (selectedAxes n q)).prod:=
      Fin.cast (UniformAllAxisDiagonalPreparation.axes_volume n (permutationPool n) (coefficientPool n) q).symm j
    have h:=action k (gathered n x j) (ready.input j)
    rw [selected_permutation_identity] at h
    exact h

/-- Every scanned local radix is charged by the already executed preparation
budget. This also proves the new pool sizing work is sublinear. -/
theorem totalRadices_le_preparationBudget (n : ℕ) :
    totalRadices n ≤ UniformAllAxisSeedPreparation.preparationBudget n := by
  unfold totalRadices prefixSum
  rw [←Fin.sum_univ_eq_sum_range]
  have h:(∑j:Fin (axisCount n),UniformAllAxisSeedPreparation.radixAt n j.val) ≤
      ∑j:Fin (axisCount n),(494*(radix n j)^2+40*radix n j+113):=by
    apply Finset.sum_le_sum
    intro j _
    rw [UniformAllAxisSeedPreparation.radixAt_eq]
    omega
  unfold UniformAllAxisSeedPreparation.preparationBudget
  omega

def runtimeBudget (n : ℕ) : ℕ := UniformAllAxisSeedPreparation.fullBudget n+
  36*totalRadices n+153*len n+59

theorem runtime_bound (n t : ℕ)
    (ht:t+UniformAllAxisSeedPreparation.preparationRuntime n+1 ≤ UniformAllAxisSeedPreparation.fullBudget n) :
    runtime n t ≤ runtimeBudget n := by
  have hm:=UniformAllAxisDiagonalPreparation.prefix_count n (axisCount n) (le_refl _)
  have htree:=UniformTensorMonomialMachine.instruction_bound_selected (selectedAxes n ⟨0,by decide⟩) n
    (UniformAllAxisDiagonalPreparation.axes_radices n _ _ _)
  rw [selectedAxes,UniformAllAxisDiagonalPreparation.axes_radices] at htree
  unfold runtime runtimeBudget passCost totalRadices at *
  omega

theorem totalRadices_isLittleO_input :
    (fun n : ℕ=>(totalRadices n:ℝ)) =o[Filter.atTop] (fun n : ℕ=>(n:ℝ)) := by
  have h:(fun n : ℕ=>(totalRadices n:ℝ)) =O[Filter.atTop]
      (fun n : ℕ=>(UniformAllAxisSeedPreparation.preparationBudget n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with n
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),one_mul] using
      (show (totalRadices n:ℝ) ≤ (UniformAllAxisSeedPreparation.preparationBudget n:ℝ) by
        exact_mod_cast totalRadices_le_preparationBudget n)
  exact h.trans_isLittleO UniformAllAxisSeedCost.budget_isLittleO_input

theorem runtimeBudget_isBigO_input :
    (fun n : ℕ=>(runtimeBudget n:ℝ)) =O[Filter.atTop] (fun n : ℕ=>(n:ℝ)) := by
  have ht:=totalRadices_isLittleO_input.isBigO.const_mul_left 36
  have hL:=UniformAllAxisSeedCost.workingLength_isBigO_input.const_mul_left 153
  have hc:(fun _n : ℕ=>(59:ℝ)) =O[Filter.atTop] (fun n : ℕ=>(n:ℝ)):=
    ((Asymptotics.isLittleO_const_id_atTop (59:ℝ)).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [runtimeBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    ((UniformAllAxisSeedCost.fullBudget_isBigO_input.add ht).add hL).add hc

structure Outcome (n : ℕ) (q : Fin 5) (x : Fin n → ℂ) (s : State) : Prop where
  metadata : UniformPermutationInversePreparation.Metadata n s
  operands : UniformInitialPreparation.Operands n x s
  retained : Retained n (axisCount n) s
  inverse : UniformGlobalNatPreparation.PermutationBank (len n) (UniformPermutationInversePreparation.inverseBase n)
    s.natHeap (UniformCRTTraversalCycle.betaPermutation n).symm
  roots : s.rootOrders=[UniformMasterRootMachine.order n]
  outputs : s.outputs=initial.outputs
  pc : s.pc=1083
  input : ∀j:Fin (len n),s.scalarHeap (UniformInputPermutationPreparation.destination n+j.val)=some (gathered n x j)
  diagonal : ∀j:Fin (len n),s.scalarHeap (destination n+j.val)=
    some (UniformPairMachine.product (coefficient n q j) (gathered n x j))

/-- Universal initial-state theorem with a proved linear asymptotic budget,
computed physical headers and no caller-installed tables or input bank. -/
theorem initial_bounded_execution {n : ℕ} (hn:0 < n) (q : Fin 5) (x : Fin n → ℂ) : ∃t u,
    BoundedExecution (program q) n x ((n+2)^19) initial (runtime n t) u ∧
    runtime n t ≤ runtimeBudget n ∧ Outcome n q x u := by
  obtain ⟨t,u,run,ht,hm,ho,hr,hb,hroots,hout,hpc,hinput,hdiag⟩:=initial_execution hn q x
  have cost:t+UniformAllAxisSeedPreparation.preparationRuntime n+1 ≤ UniformAllAxisSeedPreparation.fullBudget n:=by
    have hb:=UniformAllAxisSeedPreparation.runtime_bound n
    unfold UniformAllAxisSeedPreparation.fullBudget
    omega
  exact ⟨t,u,run,runtime_bound n t cost,hm,ho,hr,hb,hroots,hout,hpc,hinput,hdiag⟩

end
end ExactFourierCircuits.UniformInitialDiagonalTensorMachine
