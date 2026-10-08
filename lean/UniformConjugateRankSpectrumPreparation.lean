import UniformRankCrossPreparationMachine
import UniformAllAxisConjugatePreparation
import UniformSpectrumReversalMachine
import UniformChirpOutputMachine
import UniformSeedChunkPreparation
import UniformMatchingConjugateLoadMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformConjugateRankSpectrumPreparation
open UniformMachine UniformAssembly
open OAI.ExactFourier
open scoped BigOperators
namespace RC
abbrev Parameters := UniformRankCrossPreparationMachine.Parameters
end RC
namespace O
abbrev axisCount := UniformAllAxisSeedPreparation.axisCount
abbrev radix := UniformAllAxisSeedPreparation.radix
end O
noncomputable section

/-- The standard character, including its specified positive phase. -/
theorem char_conjugate {N:ℕ} [NeZero N] (j:ZMod N) :
 starRingEnd ℂ (ZMod.stdAddChar j)=ZMod.stdAddChar (-j) := by
 change starRingEnd ℂ (ZMod.toCircle j:ℂ)=(ZMod.toCircle (-j):ℂ)
 rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

theorem positiveDFT_conjugate {N:ℕ} [NeZero N] (v:ZMod N→ℂ) (j:ZMod N) :
 UniformCyclic.positiveDFT (fun i=>starRingEnd ℂ (v i)) (-j)=
 starRingEnd ℂ (UniformCyclic.positiveDFT v j) := by
 simp only [UniformCyclic.positiveDFT_apply,map_sum,map_mul,char_conjugate,mul_neg]


def reverseFin {N:ℕ} (hN:0<N) (j:Fin N):Fin N:=⟨(N-j.val)%N,Nat.mod_lt _ hN⟩
theorem reverseFin_ZMod {N:ℕ} [NeZero N] (hN:0<N) (j:Fin N) :
 FourierCRT.finZMod N (reverseFin hN j)= -(FourierCRT.finZMod N j) := by
 exact UniformChirpOutputMachine.negativeIndex_ZMod j.val (by have:=j.isLt;omega)

theorem fourier_conjugate {N:ℕ} [NeZero N] (hN:0<N) (v:Fin N→ℂ) (j:Fin N) :
 (fourierMatrix N).mulVec (fun i=>starRingEnd ℂ (v i)) (reverseFin hN j)=
 starRingEnd ℂ ((fourierMatrix N).mulVec v j) := by
 rw [←UniformCyclic.positiveDFT_fin,reverseFin_ZMod]
 rw [show UniformCyclic.toZMod (fun i=>starRingEnd ℂ (v i))=
   fun i=>starRingEnd ℂ (UniformCyclic.toZMod v i) from rfl]
 rw [positiveDFT_conjugate,UniformCyclic.positiveDFT_fin]

theorem power_conjugate {N:ℕ} [NeZero N] (hN:0<N) (j:Fin N) :
 zeta N^(reverseFin hN j).val=starRingEnd ℂ (zeta N^j.val) := by
 rw [←FourierCRT.standard_root,←FourierCRT.char_nat,←FourierCRT.char_nat]
 rw [char_conjugate]
 exact congrArg ZMod.stdAddChar (reverseFin_ZMod hN j)

theorem cross_conjugate (s:ℕ) (h g:ℕ→ℂ) (i j:ℕ) :
 OAI.ExactFourier.ToeplitzLayers.cross s (fun i=>starRingEnd ℂ (h i))
  (fun i=>starRingEnd ℂ (g i)) i j=
 starRingEnd ℂ (OAI.ExactFourier.ToeplitzLayers.cross s h g i j) := by
 simp [OAI.ExactFourier.ToeplitzLayers.cross]

theorem inputVector_conjugate (k t:ℕ) (f:Fin (UniformRadixTwoDAG.width k)→Fin (t+1))
 (v:Fin t→ℂ) (j:Fin (UniformRadixTwoDAG.width k)) :
 UniformConvolutionDAG.inputVector k t f (fun i=>starRingEnd ℂ (v i)) j=
 starRingEnd ℂ (UniformConvolutionDAG.inputVector k t f v j) := by
 unfold UniformConvolutionDAG.inputVector
 generalize f j=z
 refine Fin.lastCases ?_ (fun i=>?_) z <;> simp

theorem leftFactor_conjugate (M:ℕ→ℕ→ℂ) (v w:ℕ→ℂ) (b:Fin 3) (i:ℕ) :
 UniformToeplitzCrossDAG.leftFactor (fun i j=>starRingEnd ℂ (M i j))
  (fun i=>starRingEnd ℂ (v i)) (fun i=>starRingEnd ℂ (w i)) b i=
 starRingEnd ℂ (UniformToeplitzCrossDAG.leftFactor M v w b i) := by
 unfold UniformToeplitzCrossDAG.leftFactor
 by_cases hi:i=0
 all_goals split_ifs <;> simp [OAI.ExactFourier.Displacement.delta,hi]

theorem rightFactor_conjugate (M:ℕ→ℕ→ℂ) (v w:ℕ→ℂ) (b:Fin 3) (i:ℕ) :
 UniformToeplitzCrossDAG.rightFactor (fun i j=>starRingEnd ℂ (M i j))
  (fun i=>starRingEnd ℂ (v i)) (fun i=>starRingEnd ℂ (w i)) b i=
 starRingEnd ℂ (UniformToeplitzCrossDAG.rightFactor M v w b i) := by
 unfold UniformToeplitzCrossDAG.rightFactor
 split_ifs <;> simp [OAI.ExactFourier.Displacement.delta,apply_ite]

theorem kernels_conjugate (p:RC.Parameters) (h g:ℕ→ℂ) :
 UniformRankCrossPreparationMachine.kernelValues p (fun i=>starRingEnd ℂ (h i))
  (fun i=>starRingEnd ℂ (g i))=
 fun b j=>starRingEnd ℂ (UniformRankCrossPreparationMachine.kernelValues p h g b j) := by
 have hm:UniformRankKernelMachine.matrixValue p.rank (fun i=>starRingEnd ℂ (h i))
   (fun i=>starRingEnd ℂ (g i))=fun i j=>starRingEnd ℂ (UniformRankKernelMachine.matrixValue p.rank h g i j):=by
   funext i j;exact cross_conjugate _ h g _ _
 have hv:UniformRankKernelMachine.vValue p.rank (fun i=>starRingEnd ℂ (h i))=
   fun i=>starRingEnd ℂ (UniformRankKernelMachine.vValue p.rank h i):=by funext i;simp [UniformRankKernelMachine.vValue]
 have hw:UniformRankKernelMachine.wValue p.rank (fun i=>starRingEnd ℂ (g i))=
   fun i=>starRingEnd ℂ (UniformRankKernelMachine.wValue p.rank g i):=rfl
 funext b j
 simp only [UniformRankCrossPreparationMachine.kernelValues,hm,hv,hw,UniformToeplitzCrossDAG.rankKernels]
 split_ifs <;> simp only [rightFactor_conjugate,leftFactor_conjugate] <;>
 exact inputVector_conjugate _ _ _ _ _


open UniformRadixTwoDAG (width)
open UniformPairMachine (prepared)

def bankValue (k:ℕ) (v:Fin 6→Fin (width k)→ℂ) (i:Fin (7*width k)) : ℂ :=
 UniformToeplitzCrossDAG.sharedBank k v ⟨i.val,by have:=i.isLt;change i.val<width k+6*width k;omega⟩

def blockIndex (N:ℕ) (b:Fin 7) (j:Fin N):Fin (7*N) :=
 ⟨b.val*N+j.val,by have hb:=Nat.mul_le_mul_right N (show b.val ≤ 6 by omega);have:=j.isLt;omega⟩

theorem bankValue_power (k:ℕ) (v:Fin 6→Fin (width k)→ℂ) (j:Fin (width k)) :
 bankValue k v (blockIndex (width k) 0 j)=zeta (width k)^j.val := by
 have he:(⟨(blockIndex (width k) 0 j).val,by have:=(blockIndex (width k) 0 j).isLt;change _<width k+6*width k;omega⟩:Fin (UniformToeplitzCrossDAG.bankSize k))=
   j.castAdd (6*width k):=Fin.ext (by simp [blockIndex])
 unfold bankValue;rw [he,UniformToeplitzCrossDAG.sharedBank,Fin.addCases_left]

theorem bankValue_spectrum (k:ℕ) (v:Fin 6→Fin (width k)→ℂ) (b:Fin 6) (j:Fin (width k)) :
 bankValue k v (blockIndex (width k) ⟨b.val+1,by have:=b.isLt;omega⟩ j)=
 (fourierMatrix (width k)).mulVec (v b) j := by
 have he:(⟨(blockIndex (width k) ⟨b.val+1,by have:=b.isLt;omega⟩ j).val,
   by have:=(blockIndex (width k) ⟨b.val+1,by have:=b.isLt;omega⟩ j).isLt;change _<width k+6*width k;omega⟩:Fin (UniformToeplitzCrossDAG.bankSize k))=
   (finProdFinEquiv (b,j)).natAdd (width k):=Fin.ext (by simp [blockIndex,finProdFinEquiv,Nat.add_mul];ac_rfl)
 unfold bankValue;rw [he,UniformToeplitzCrossDAG.sharedBank,Fin.addCases_right,Equiv.symm_apply_apply]

theorem reverseNat_block (N:ℕ) (hN:0<N) (b:Fin 7) (j:Fin N) :
 UniformSpectrumReversalMachine.reverseNat N (blockIndex N b j).val=
 (blockIndex N b (reverseFin hN j)).val := by
 have hd:j.val/N=0:=Nat.div_eq_of_lt j.isLt
 have hm:j.val%N=j.val:=Nat.mod_eq_of_lt j.isLt
 simp only [UniformSpectrumReversalMachine.reverseNat,blockIndex,reverseFin]
 rw [Nat.mul_comm b.val N,Nat.mul_add_div hN,Nat.mul_add_mod,hd,hm]
 simp [Nat.mul_comm]

theorem bankValue_reverse_block (k:ℕ) (v:Fin 6→Fin (width k)→ℂ) (b:Fin 7) (j:Fin (width k)) :
 bankValue k (fun b j=>starRingEnd ℂ (v b j)) (blockIndex (width k) b (reverseFin (UniformRadixTwoDAG.width_pos k) j))=
 starRingEnd ℂ (bankValue k v (blockIndex (width k) b j)) := by
 by_cases hz:b.val=0
 · have hb:b=0:=Fin.ext hz
   subst b
   rw [bankValue_power,bankValue_power]
   exact power_conjugate (UniformRadixTwoDAG.width_pos k) j
 · let c:Fin 6:=⟨b.val-1,by have:=b.isLt;omega⟩
   have hb:b=⟨c.val+1,by have:=c.isLt;omega⟩:=Fin.ext (by simp [c];omega)
   rw [hb,bankValue_spectrum,bankValue_spectrum]
   exact fourier_conjugate (UniformRadixTwoDAG.width_pos k) (v c) j

theorem bankValue_reverse (k:ℕ) (v:Fin 6→Fin (width k)→ℂ) (i:Fin (7*width k)) :
 bankValue k (fun b j=>starRingEnd ℂ (v b j))
  ⟨UniformSpectrumReversalMachine.reverseNat (width k) i.val,
   UniformSpectrumReversalMachine.index_lt (UniformRadixTwoDAG.width_pos k) i.isLt⟩=
 starRingEnd ℂ (bankValue k v i) := by
 let N:=width k
 have hn:0<N:=UniformRadixTwoDAG.width_pos k
 let j:Fin N:=⟨i.val%N,Nat.mod_lt _ hn⟩
 let b:Fin 7:=⟨i.val/N,(Nat.div_lt_iff_lt_mul hn).mpr (by exact i.isLt)⟩
 have hi:i=blockIndex N b j:=Fin.ext (by
   change i.val=(i.val/N)*N+i.val%N
   have h:=Nat.mod_add_div i.val N
   simpa [Nat.mul_comm,Nat.add_comm] using h.symm)
 have hv:=bankValue_reverse_block k v b j
 convert hv using 1
 · congr 1
 · rw [hi]


namespace T
abbrev Op:=UniformTensorMonomialMachine.Op
end T

def boot : List T.Op := [.literal 1823 1,.literal 1824 2,.literal 1825 3,.literal 1826 0,
 .add 1827 105 106,.add 1827 1827 103,.add 1828 102 1823,.mul 1828 1828 1824,
 .add 1827 1827 1828,.mul 1828 1821 1824,.add 1828 1827 1828,
 .getNat 480 1828,.add 1828 1828 1823,.getNat 481 1828,
 .add 483 481 1826,.mul 1829 481 1825,.add 480 480 1829,.add 482 480 481]
def reversalSetup : List T.Op := [.literal 1803 0,.add 1800 489 1803,
 .add 1801 529 1803,.add 1802 1820 1803]
def program : Program := boot.map UniformTensorMonomialMachine.Op.code ++
 UniformRankCrossPreparationMachine.program.map (relocate 18 740) ++
 reversalSetup.map UniformTensorMonomialMachine.Op.code ++
 UniformSpectrumReversalMachine.program.map (relocate 744 762) ++ [.halt]
theorem boot_length : boot.length=18:=rfl
theorem reversalSetup_length : reversalSetup.length=4:=rfl
theorem program_length : program.length=763:=by
 simp only [program,List.length_append,List.length_map,boot_length,reversalSetup_length,
 UniformRankCrossPreparationMachine.program_length,UniformSpectrumReversalMachine.program_length];rfl

theorem boot_code : UniformTensorMonomialMachine.BlockAt boot program 0 := by
 intro i hi;change i<18 at hi;interval_cases i <;> rfl

attribute [local irreducible] UniformRankCrossPreparationMachine.program

theorem rank_code : CodeAt UniformRankCrossPreparationMachine.program program 18 740 := by
 have he:program=boot.map UniformTensorMonomialMachine.Op.code ++
   UniformRankCrossPreparationMachine.program.map (relocate 18 740) ++
   (reversalSetup.map UniformTensorMonomialMachine.Op.code ++
    UniformSpectrumReversalMachine.program.map (relocate 744 762) ++ [.halt]):=by
   simp only [program,List.append_assoc]
 rw [he]
 exact UniformRankCrossPreparationMachine.segment_code _ _ _ _ _ rfl

theorem reversalSetup_lookup (i:ℕ) (hi:i<4) : program[740+i]?=
 (reversalSetup.map UniformTensorMonomialMachine.Op.code)[i]? := by
 let pre:=boot.map UniformTensorMonomialMachine.Op.code ++
   UniformRankCrossPreparationMachine.program.map (relocate 18 740)
 have hl:pre.length=740:=by simp only [pre,List.length_append,List.length_map,boot_length,
   UniformRankCrossPreparationMachine.program_length]
 have he:program=pre ++ (reversalSetup.map UniformTensorMonomialMachine.Op.code ++
   UniformSpectrumReversalMachine.program.map (relocate 744 762) ++ [.halt]):=by
   simp only [program,pre,List.append_assoc]
 rw [he,List.getElem?_append_right (by omega)]
 simp only [hl,show 740+i-740=i by omega]
 simp only [List.append_assoc]
 rw [List.getElem?_append_left (by simp only [List.length_map,reversalSetup_length];omega)]

theorem reversalSetup_code : UniformTensorMonomialMachine.BlockAt reversalSetup program 740 := by
 intro i hi
 rw [reversalSetup_lookup i (by simpa only [reversalSetup_length] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]

theorem reversal_code : CodeAt UniformSpectrumReversalMachine.program program 744 762 := by
 let pre:=boot.map UniformTensorMonomialMachine.Op.code ++
   UniformRankCrossPreparationMachine.program.map (relocate 18 740) ++
   reversalSetup.map UniformTensorMonomialMachine.Op.code
 have hl:pre.length=744:=by simp [pre,boot_length,reversalSetup_length,UniformRankCrossPreparationMachine.program_length]
 have he:program=pre ++ UniformSpectrumReversalMachine.program.map (relocate 744 762) ++ [.halt]:=by
   simp only [program,pre,List.append_assoc]
 rw [he];exact UniformRankCrossPreparationMachine.segment_code pre [.halt] _ _ _ hl

def selected (n:ℕ) (j:Fin (O.axisCount n)) (p:RC.Parameters) : RC.Parameters :=
 { p with
   H := UniformAllAxisConjugatePreparation.axisBase n j.val+3*O.radix n j
   G := UniformAllAxisConjugatePreparation.axisBase n j.val+4*O.radix n j
   hSize := O.radix n j
   gSize := O.radix n j
   D := UniformMasterRootMachine.order n }

def Arguments (n:ℕ) (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest:ℕ) (s:State):Prop:=
 s.natReg 1820=dest ∧ s.natReg 1821=j.val ∧
 ∀r,r∈UniformRankCrossPreparationMachine.headerRegisters → r≠480 → r≠481 → r≠482 → r≠483 →
 s.natReg r=(selected n j p).register r

def dirEnd (n:ℕ):ℕ:=UniformAllAxisConjugatePreparation.directoryBase n+2*O.axisCount n
def seedEnd (n:ℕ):ℕ:=UniformAllAxisConjugatePreparation.axisBase n (O.axisCount n)

structure Allocation (n:ℕ) (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest B:ℕ):Prop where
 layout:UniformRankCrossPreparationMachine.Layout (selected n j p) B
 seedFresh:seedEnd n ≤ p.S
 globalFresh:UniformGlobalLocalPreparation.globalEnd n ≤ p.S
 natFreshRows:dirEnd n ≤ p.d
 natFreshConv:dirEnd n ≤ p.conv
 natFreshTape:dirEnd n ≤ p.tape
 natFreshDepth:dirEnd n ≤ p.depth
 directoryBound:dirEnd n ≤ B
 reversedFresh:p.C+7*width p.K+1 ≤ dest
 reversedBound:dest+7*width p.K ≤ B
 code:763 ≤ B

abbrev bootState (s:State):State:=UniformTensorMonomialMachine.applyBlock boot s

theorem boot_frame (s:State) : (bootState s).natHeap=s.natHeap ∧ (bootState s).scalarHeap=s.scalarHeap ∧
 (bootState s).scalarReg=s.scalarReg ∧ (bootState s).outputs=s.outputs ∧ (bootState s).rootOrders=s.rootOrders ∧
 (∀r,r≠480 → r≠481 → r≠482 → r≠483 → (r<1823 ∨ 1829<r) → (bootState s).natReg r=s.natReg r) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h0 h1 h2 h3 hr
 simp (disch:=omega) [bootState,boot,UniformTensorMonomialMachine.applyBlock,UniformTensorMonomialMachine.Op.apply,
 writeNat,next]

theorem boot_spec {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest:ℕ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s)
 (hr:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s)
 (args:Arguments n j p dest s) : UniformRankCrossPreparationMachine.Header (selected n j p) (bootState s) ∧
 (bootState s).natReg 1820=dest := by
 have hd: s.natHeap (UniformAllAxisConjugatePreparation.directoryBase n+2*j.val)=
   some (UniformAllAxisConjugatePreparation.axisBase n j.val):=hr.address j j.isLt
 have hw:s.natHeap (UniformAllAxisConjugatePreparation.directoryBase n+2*j.val+1)=some (O.radix n j):=hr.width j j.isLt
 have hp:s.natReg 105+s.natReg 106+s.natReg 103+(s.natReg 102+1)*2=
   UniformAllAxisConjugatePreparation.directoryBase n:=by
   rw [hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,hm.saved.count]
   unfold UniformAllAxisConjugatePreparation.directoryBase
   rw [←UniformAllAxisSeedPreparation.directory_after_protected]
   unfold UniformAllAxisSeedPreparation.axisCount UniformInitialPreparation.copyBase
   omega
 have hc:HAdd.hAdd (s.natReg 105) (s.natReg 106)+s.natReg 103+(s.natReg 102+1)*2+j.val*2=
   UniformAllAxisConjugatePreparation.directoryBase n+2*j.val:=by rw [hp];omega
 refine ⟨?_,?_⟩
 · intro r rr
   simp only [UniformRankCrossPreparationMachine.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at rr
   rcases rr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp [bootState,boot,UniformTensorMonomialMachine.applyBlock,UniformTensorMonomialMachine.Op.apply,
     writeNat,next,args.2.1,hc,hd,hw,selected,UniformRankCrossPreparationMachine.Parameters.register]
   all_goals try omega
   all_goals try exact args.2.2 _ (by simp [UniformRankCrossPreparationMachine.headerRegisters]) (by decide) (by decide) (by decide) (by decide)
 · exact (boot_frame s).2.2.2.2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans args.1


theorem directory_calculation {n:ℕ} {s:State} (hm:UniformPermutationInversePreparation.Metadata n s) :
 s.natReg 105+s.natReg 106+s.natReg 103+(s.natReg 102+1)*2=
 UniformAllAxisConjugatePreparation.directoryBase n := by
 rw [hm.saved.copyAddress,hm.saved.copyLength,hm.saved.workingLength,hm.saved.count]
 unfold UniformAllAxisConjugatePreparation.directoryBase
 rw [←UniformAllAxisSeedPreparation.directory_after_protected]
 unfold UniformAllAxisSeedPreparation.axisCount UniformInitialPreparation.copyBase
 omega

theorem boot_safe {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest B:ℕ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s)
 (hr:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s)
 (args:Arguments n j p dest s) (alloc:Allocation n j p dest B) :
 UniformTensorMonomialMachine.readable boot s ∧ UniformTensorMonomialMachine.peak boot s ≤ B := by
 have hd:=hr.address j j.isLt
 have hw:=hr.width j j.isLt
 have hdir:=directory_calculation hm
 have hc:s.natReg 105+s.natReg 106+s.natReg 103+(s.natReg 102+1)*2+j.val*2=
   UniformAllAxisConjugatePreparation.directoryBase n+2*j.val:=by rw [hdir];omega
 have seedB:=alloc.layout.1.gFresh
 have outB:=alloc.layout.1.outputBound
 simp only [UniformRankCrossPreparationMachine.Parameters.rank,selected] at seedB outB
 change UniformAllAxisConjugatePreparation.axisBase n j.val+4*O.radix n j+O.radix n j ≤ p.S at seedB
 change s.natHeap (UniformAllAxisConjugatePreparation.directoryBase n+2*j.val+1)=some (O.radix n j) at hw
 have dirB:=alloc.directoryBound
 have hj:=j.isLt
 have hpcount:s.natReg 102+1=O.axisCount n:=by rw [hm.saved.count]
 unfold dirEnd at dirB
 constructor
 · simp [UniformTensorMonomialMachine.readable,boot,UniformTensorMonomialMachine.Op.readable,
     UniformTensorMonomialMachine.Op.apply,writeNat,next,
     args.2.1,hc,hd,hw]
 · simp only [UniformTensorMonomialMachine.peak,boot,UniformTensorMonomialMachine.Op.peak,
     UniformTensorMonomialMachine.Op.apply,writeNat,next,
     Function.update_self,max_le_iff]
   simp [args.2.1,hc,hd,hw]
   omega

theorem boot_execution {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest B:ℕ) (x:Fin n→ℂ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s)
 (hr:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s)
 (args:Arguments n j p dest s) (alloc:Allocation n j p dest B) (pc:s.pc=0) (hs:WordBound B s) :
 BoundedRuns program n x B s 18 (bootState s) := by
 have safe:=boot_safe j p dest B s hm hr args alloc
 exact UniformTensorMonomialMachine.block_runs boot program 0 n B x s boot_code pc hs
   (by rw [boot_length];have:=alloc.code;omega) safe.1 safe.2


def originalH (n:ℕ) (j:Fin (O.axisCount n)) :ℕ→ℂ:=
 UniformLocalSeedTableMachine.seedValue (zeta (O.radix n j)) 3

def originalG (n:ℕ) (j:Fin (O.axisCount n)) :ℕ→ℂ:=
 UniformLocalSeedTableMachine.seedValue (zeta (O.radix n j)) 4

theorem selected_banks {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (s:State)
 (hr:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s) :
 UniformRankKernelMachine.Bank (selected n j p).H (selected n j p).hSize
   (fun i=>starRingEnd ℂ (originalH n j i)) s ∧
 UniformRankKernelMachine.Bank (selected n j p).G (selected n j p).gSize
   (fun i=>starRingEnd ℂ (originalG n j i)) s := by
 have bank:UniformSeedConjugatePreparation.ConjugateCompact (O.radix n j)
   (UniformAllAxisConjugatePreparation.axisBase n j.val) s:=
   (UniformAllAxisConjugatePreparation.retained_complete hr j).2.2
 constructor
 · intro i hi
   exact bank 3 ⟨i,hi⟩
 · intro i hi
   exact bank 4 ⟨i,hi⟩


theorem rank_call (p:RC.Parameters) (B n:ℕ) (h g:ℕ→ℂ) (x:Fin n→ℂ) (s:State)
 (header:UniformRankCrossPreparationMachine.Header p s) (layout:UniformRankCrossPreparationMachine.Layout p B)
 (bh:UniformRankKernelMachine.Bank p.H p.hSize h s) (bg:UniformRankKernelMachine.Bank p.G p.gSize g s)
 (master:s.scalarHeap 0=some (prepared (zeta p.D))) (pc:s.pc=18) (code:763 ≤ B) (hs:WordBound B s) : ∃u t,
 BoundedRuns program n x B s t u ∧ t ≤ UniformRankCrossPreparationMachine.runtimeBudget p ∧ u.pc=740 ∧
 UniformRankCrossPreparationMachine.ReadyHeader p u ∧ UniformKernelSpectrumMachine.Result p.K p.C
  (UniformRankCrossPreparationMachine.kernelValues p h g) u ∧ UniformRankCrossPreparationMachine.Frame p s u := by
 let e:State:={s with pc:=0}
 have eb:=changePC_bound B s 0 hs (by omega)
 obtain ⟨v,t,run,tb,vp,vh,values,root,tape,depth,height,bh',bg',vf,vm⟩:=
   UniformRankCrossPreparationMachine.execution p B n h g x e (header.withPC 0) layout bh bg master rfl eb
 have call:=UniformBoundedAssembly.boundedExecution_placed rank_code
   (by rw [UniformRankCrossPreparationMachine.program_length];omega) (by omega) run
 have he:placed 18 e=s:=UniformPreparedFFTMachine.reset_placed s 18 pc
 rw [he] at call
 exact ⟨{v with pc:=740},t,call,tb,rfl,vh.withPC 740,values,vf⟩

def setupState (s:State):State:=UniformTensorMonomialMachine.applyBlock reversalSetup s

theorem setup_frame (s:State) : (setupState s).natHeap=s.natHeap ∧ (setupState s).scalarHeap=s.scalarHeap ∧
 (setupState s).outputs=s.outputs ∧ (setupState s).rootOrders=s.rootOrders ∧
 (∀r,(r<1800 ∨ 1803<r) → (setupState s).natReg r=s.natReg r) := by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro r hr;simp (disch:=omega) [setupState,reversalSetup,UniformTensorMonomialMachine.applyBlock,
   UniformTensorMonomialMachine.Op.apply,writeNat,next]

theorem reverse_call (p:RC.Parameters) (dest B n:ℕ) (values:Fin 6→Fin (width p.K)→ℂ) (x:Fin n→ℂ) (s:State)
 (header:UniformRankCrossPreparationMachine.ReadyHeader p s)
 (bank:UniformKernelSpectrumMachine.Result p.K p.C values s) (arg:s.natReg 1820=dest)
 (fresh:p.C+7*width p.K ≤ dest) (bound:dest+7*width p.K ≤ B) (code:763 ≤ B)
 (pc:s.pc=740) (hs:WordBound B s) : ∃u,
 BoundedRuns program n x B s (91*width p.K+10) u ∧ u.pc=762 ∧
 (∀i:Fin (7*width p.K),u.scalarHeap (dest+i.val)=some (prepared (bankValue p.K values
    ⟨UniformSpectrumReversalMachine.reverseNat (width p.K) i.val,
      UniformSpectrumReversalMachine.index_lt (UniformRadixTwoDAG.width_pos p.K) i.isLt⟩))) ∧
 UniformSpectrumReversalMachine.Outside (width p.K) dest s u ∧
 u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,(r<1800 ∨ 1809<r) → u.natReg r=s.natReg r) := by
 have Nval:=header.2.1
 have Cval:s.natReg 529=p.C:=header.1 _ (by decide)
 have safe:UniformTensorMonomialMachine.peak reversalSetup s ≤ B:=by
   simp [reversalSetup,UniformTensorMonomialMachine.peak,UniformTensorMonomialMachine.Op.peak,
     UniformTensorMonomialMachine.Op.apply,writeNat,next,Nval,Cval,arg]
   omega
 have setup:=UniformTensorMonomialMachine.block_runs reversalSetup program 740 n B x s reversalSetup_code pc hs
   (by rw [reversalSetup_length];omega) (by trivial) safe
 let v:=setupState s
 have vp:v.pc=744:=by
   change (UniformTensorMonomialMachine.applyBlock reversalSetup s).pc=744
   rw [UniformTensorMonomialMachine.applyBlock_pc,pc,reversalSetup_length]
 have vn:v.natReg 1800=width p.K:=by simp [v,setupState,reversalSetup,UniformTensorMonomialMachine.applyBlock,
   UniformTensorMonomialMachine.Op.apply,writeNat,next,Nval]
 have va:v.natReg 1801=p.C:=by simp [v,setupState,reversalSetup,UniformTensorMonomialMachine.applyBlock,
   UniformTensorMonomialMachine.Op.apply,writeNat,next,Cval]
 have vd:v.natReg 1802=dest:=by simp [v,setupState,reversalSetup,UniformTensorMonomialMachine.applyBlock,
   UniformTensorMonomialMachine.Op.apply,writeNat,next,arg]
 have bv:UniformSpectrumReversalMachine.Bank (width p.K) p.C (fun i=>prepared (bankValue p.K values i)) v:=by
   intro i;exact bank ⟨i.val,by have:=i.isLt;change _<width p.K+6*width p.K;omega⟩
 let e:State:={v with pc:=0}
 have eb:=changePC_bound B v 0 setup.final_bound (by omega)
 obtain ⟨w,run,wp,bw,source,out,frame⟩:=UniformSpectrumReversalMachine.execution n (width p.K) p.C dest B x
   (fun i=>prepared (bankValue p.K values i)) e (UniformRadixTwoDAG.width_pos p.K) vn va vd bv fresh bound (by omega) rfl eb
 have call:=UniformBoundedAssembly.boundedExecution_placed reversal_code
   (by rw [UniformSpectrumReversalMachine.program_length];omega) (by omega) run
 have he:placed 744 e=v:=UniformPreparedFFTMachine.reset_placed v 744 vp
 rw [he] at call
 refine ⟨{w with pc:=762},?_,rfl,bw,out,frame.1,frame.2.1,frame.2.2.1,?_⟩
 · rw [reversalSetup_length] at setup
   convert setup.trans call using 1;omega
 · intro r hr
   exact (frame.2.2.2.1 r (by omega)).trans ((setup_frame s).2.2.2.2 r (by omega))

/-- The final bank is exactly the conjugate of the original positive-root shared
bank. No transformed input state or preexisting conjugate spectrum is assumed. -/
def Result (n:ℕ) (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest:ℕ) (s:State):Prop:=
 ∀i:Fin (7*width p.K),s.scalarHeap (dest+i.val)=some (prepared (starRingEnd ℂ
   (bankValue p.K (UniformRankCrossPreparationMachine.kernelValues (selected n j p)
     (originalH n j) (originalG n j)) i)))


theorem halt_code : program[762]?=some .halt := by
 let pre:=boot.map UniformTensorMonomialMachine.Op.code ++
   UniformRankCrossPreparationMachine.program.map (relocate 18 740) ++
   reversalSetup.map UniformTensorMonomialMachine.Op.code ++
   UniformSpectrumReversalMachine.program.map (relocate 744 762)
 have hl:pre.length=762:=by simp only [pre,List.length_append,List.length_map,boot_length,reversalSetup_length,
   UniformRankCrossPreparationMachine.program_length,UniformSpectrumReversalMachine.program_length]
 have he:program=pre ++ [.halt]:=by simp only [program,pre,List.append_assoc]
 rw [he,List.getElem?_append_right (by omega),hl];rfl

def Frame (p:RC.Parameters) (dest:ℕ) (s u:State):Prop:=
 (∀i,(i < p.d ∨ p.d+3*UniformRadixTwoDAG.count p.K  ≤  i) →
   (i < p.conv ∨ p.conv+5*UniformToeplitzCrossTopologyMachine.G p.K  ≤  i) →
   (i < p.tape ∨ p.tape+5*UniformRankCrossPreparationMachine.Shape p  ≤  i) →
   (i < p.depth ∨ p.depth+p.e+1+UniformRankCrossPreparationMachine.Shape p  ≤  i) → u.natHeap i=s.natHeap i) ∧
 (∀i,(i < p.S ∨ p.S+6*width p.K  ≤  i) →
   (i < p.A ∨ UniformPreparedFFTMachine.rootAddress p.K p.A+1  ≤  i) →
   (i < p.C ∨ p.C+7*width p.K+1  ≤  i) →
   (i < dest ∨ dest+7*width p.K  ≤  i) → u.scalarHeap i=s.scalarHeap i) ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,((100  ≤  r ∧ r  ≤  106) ∨ 1830  ≤  r) → u.natReg r=s.natReg r)

theorem Allocation.scalar_chain {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ}
 (a:Allocation n j p dest B):p.S ≤ p.A ∧ p.A ≤ p.C ∧ p.C ≤ dest := by
 have hA:=a.layout.2.1.1
 have hC:=a.layout.2.1.bankAfter
 change p.S+6*width p.K ≤ p.A at hA
 change UniformPreparedFFTMachine.rootAddress p.K p.A+1 ≤ p.C at hC
 unfold UniformPreparedFFTMachine.rootAddress UniformPreparedFFTMachine.powerBase at hC
 have hd:=a.reversedFresh
 omega

theorem Frame.scalar_before {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ} {s u:State}
 (a:Allocation n j p dest B) (f:Frame p dest s u) (i:ℕ) (hi:i<p.S):u.scalarHeap i=s.scalarHeap i := by
 have chain:=a.scalar_chain
 exact f.2.1 i (Or.inl hi) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

theorem Frame.nat_before {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ} {s u:State}
 (a:Allocation n j p dest B) (f:Frame p dest s u) (i:ℕ) (hi:i<dirEnd n):u.natHeap i=s.natHeap i :=
 f.1 i (Or.inl (lt_of_lt_of_le hi a.natFreshRows)) (Or.inl (lt_of_lt_of_le hi a.natFreshConv))
   (Or.inl (lt_of_lt_of_le hi a.natFreshTape)) (Or.inl (lt_of_lt_of_le hi a.natFreshDepth))

/-- A single fixed763 program selects the genuine conjugate H/G lanes,
produces their six kernel spectra from the retained master, and physically
reverses all7 frequency blocks into the coefficientwise conjugate bank. -/
theorem execution {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest B:ℕ) (x:Fin n→ℂ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s)
 (hc:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s)
 (args:Arguments n j p dest s) (alloc:Allocation n j p dest B)
 (master:s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n))))
 (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧
 t ≤ UniformRankCrossPreparationMachine.runtimeBudget (selected n j p)+91*width p.K+29 ∧
 u.pc=762 ∧ Result n j p dest u ∧ Frame p dest s u := by
 let q:=selected n j p
 have start:=boot_execution j p dest B x s hm hc args alloc pc hs
 have bh:UniformRankKernelMachine.Bank q.H q.hSize (fun i=>starRingEnd ℂ (originalH n j i)) (bootState s):=
   (selected_banks j p s hc).1
 have bg:UniformRankKernelMachine.Bank q.G q.gSize (fun i=>starRingEnd ℂ (originalG n j i)) (bootState s):=
   (selected_banks j p s hc).2
 have header:=boot_spec j p dest s hm hc args
 have bp:(bootState s).pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,boot_length]
 obtain ⟨v,t,call,tb,vp,vh,spectra,vf⟩:=rank_call q B n
   (fun i=>starRingEnd ℂ (originalH n j i)) (fun i=>starRingEnd ℂ (originalG n j i)) x
   (bootState s) header.1 alloc.layout bh bg master bp alloc.code start.final_bound
 have vd:v.natReg 1820=dest:=(vf.2.2.2.2 _ (Or.inr (Or.inr (by decide)))).trans header.2
 obtain ⟨w,rev,wp,values,out,nh,outputs,roots,nats⟩:=reverse_call q dest B n
   (UniformRankCrossPreparationMachine.kernelValues q (fun i=>starRingEnd ℂ (originalH n j i))
    (fun i=>starRingEnd ℂ (originalG n j i))) x v vh spectra vd (by exact Nat.le_of_lt alloc.reversedFresh)
    alloc.reversedBound alloc.code vp call.final_bound
 have stop:BoundedExecution program n x B w 1 w:=.halt rev.final_bound (by simp [step,wp,halt_code])
 refine ⟨w,18+(t+(91*width p.K+10+1)),start.executes (call.executes (rev.executes stop)),?_,wp,?_,?_⟩
 · dsimp only [q] at tb
   omega
 · intro i
   have val:=values i
   dsimp only [q,selected] at val
   rw [kernels_conjugate _ (originalH n j) (originalG n j),bankValue_reverse] at val
   exact val
 · refine ⟨?_,?_,outputs.trans vf.2.2.1,roots.trans vf.2.2.2.1,?_⟩
   · intro i h0 h1 h2 h3
     exact (congrFun nh i).trans (vf.1 i h0 h1 h2 h3)
   · intro i h0 h1 h2 h3
     exact (out i h3).trans (vf.2.1 i h0 h1 h2)
   · intro r hr
     have old:UniformRankCrossPreparationMachine.Preserved r:=by
       unfold UniformRankCrossPreparationMachine.Preserved;omega
     exact (nats r (by omega)).trans ((vf.2.2.2.2 r old).trans
       ((boot_frame s).2.2.2.2.2 r (by omega) (by omega) (by omega) (by omega) (by omega)))


theorem originalEnd_le_seedEnd (n:ℕ) :
 UniformAllAxisSeedPreparation.axisBase n (O.axisCount n) ≤ seedEnd n := by
 unfold seedEnd UniformAllAxisConjugatePreparation.axisBase UniformAllAxisConjugatePreparation.pool
 change UniformSeedConjugatePreparation.destination n ≤ UniformSeedConjugatePreparation.destination n+5*UniformInitialPreparation.len n+_
 omega

theorem Frame.protected {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ} {s u:State}
 (a:Allocation n j p dest B) (f:Frame p dest s u) : UniformAllAxisSeedPreparation.ProtectedFrame n s u := by
 refine ⟨?_,?_,?_,f.2.2.1,f.2.2.2.1⟩
 · intro i _ hi
   exact f.nat_before a i (by unfold dirEnd UniformAllAxisConjugatePreparation.directoryBase;omega)
 · intro i hi
   exact f.scalar_before a i (lt_of_lt_of_le hi a.globalFresh)
 · intro r h0 h1;exact f.2.2.2.2 r (Or.inl ⟨h0,h1⟩)

theorem Frame.retained {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ} {s u:State}
 (a:Allocation n j p dest B) (f:Frame p dest s u)
 (original:UniformAllAxisSeedPreparation.Retained n (O.axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s) :
 UniformAllAxisSeedPreparation.Retained n (O.axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) u := by
 have scal:∀i,i<seedEnd n → u.scalarHeap i=s.scalarHeap i:=fun i hi=>f.scalar_before a i (lt_of_lt_of_le hi a.seedFresh)
 have nat:∀i,i<dirEnd n → u.natHeap i=s.natHeap i:=fun i hi=>f.nat_before a i hi
 constructor
 · refine ⟨?_,?_,?_⟩
   · intro k hk q l
     exact (scal _ (lt_of_lt_of_le (UniformAllAxisSeedPreparation.compact_address_before k hk q l)
       (originalEnd_le_seedEnd n))).trans (original.coefficients k hk q l)
   · intro k hk
     exact (nat _ (by have:=k.isLt;unfold dirEnd UniformAllAxisConjugatePreparation.directoryBase;omega)).trans (original.address k hk)
   · intro k hk
     exact (nat _ (by have:=k.isLt;unfold dirEnd UniformAllAxisConjugatePreparation.directoryBase;omega)).trans (original.width k hk)
 · refine ⟨?_,?_,?_⟩
   · intro k hk q l
     exact (scal _ (UniformAllAxisConjugatePreparation.compact_address_before k hk q l)).trans (conjugate.coefficients k hk q l)
   · intro k hk
     exact (nat _ (by have:=k.isLt;unfold dirEnd;omega)).trans (conjugate.address k hk)
   · intro k hk
     exact (nat _ (by have:=k.isLt;unfold dirEnd;omega)).trans (conjugate.width k hk)

/-- Startup operands discharge the prepared master source, while both original
and conjugate compact banks/directories survive the actual whole execution. -/
theorem execution_retained {n:ℕ} (j:Fin (O.axisCount n)) (p:RC.Parameters) (dest B:ℕ) (x:Fin n→ℂ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s) (ops:UniformInitialPreparation.Operands n x s)
 (original:UniformAllAxisSeedPreparation.Retained n (O.axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) s)
 (args:Arguments n j p dest s) (alloc:Allocation n j p dest B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧
 t ≤ UniformRankCrossPreparationMachine.runtimeBudget (selected n j p)+91*width p.K+29 ∧
 u.pc=762 ∧ Result n j p dest u ∧ Frame p dest s u ∧
 UniformAllAxisSeedPreparation.Retained n (O.axisCount n) u ∧
 UniformAllAxisConjugatePreparation.Retained n (O.axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 u.scalarHeap 0=s.scalarHeap 0 := by
 obtain ⟨u,t,run,tb,pcu,values,f⟩:=execution j p dest B x s hm conjugate args alloc
   (UniformSeedRankCrossPreparation.operands_master ops) pc hs
 have retained:=f.retained alloc original conjugate
 have pf:=f.protected alloc
 refine ⟨u,t,run,tb,pcu,values,f,retained.1,retained.2,pf.metadata hm,pf.operands ops,?_⟩
 exact pf.2.1 0 (by rw [UniformGlobalLocalPreparation.globalEnd_formula];omega)

/-- In particular any already-produced original spectrum below the fresh
workspace is retained, with its exact stored tag. -/
theorem original_spectrum_retained {n:ℕ} {j:Fin (O.axisCount n)} {p:RC.Parameters} {dest B:ℕ} {s u:State}
 (a:Allocation n j p dest B) (f:Frame p dest s u) (C R:ℕ) (before:C+R ≤ p.S) :
 ∀i:Fin R,u.scalarHeap (C+i.val)=s.scalarHeap (C+i.val) := by
 intro i;exact f.scalar_before a _ (by have:=i.isLt;omega)

theorem originalH_eq (n:ℕ) (j:Fin (O.axisCount n)) : originalH n j=UniformSeedRankCrossPreparation.hValue n j := by
 funext i
 simp [originalH,UniformLocalSeedTableMachine.seedValue,UniformSeedRankCrossPreparation.hValue,
   UniformSeedRankCrossPreparation.omega,NewtonFourier.invH,PowerSeries.coeff_mk]

theorem originalG_eq (n:ℕ) (j:Fin (O.axisCount n)) : originalG n j=UniformSeedRankCrossPreparation.gValue n j := by
 funext i
 simp [originalG,UniformLocalSeedTableMachine.seedValue,UniformSeedRankCrossPreparation.gValue,
   UniformSeedRankCrossPreparation.omega]

/-- Retain chunk geometry while giving its producer an independent fresh
workspace. These are address changes, not a matrix/action certificate. -/
def relocated (original work:RC.Parameters) : RC.Parameters :=
 { work with
   K := original.K
   a := original.a
   e := original.e
   i0 := original.i0
   j0 := original.j0
   split := original.split }

theorem kernelValues_selected_relocated (n:ℕ) (j:Fin (O.axisCount n)) (original work:RC.Parameters) (h g:ℕ→ℂ) :
 UniformRankCrossPreparationMachine.kernelValues (selected n j (relocated original work)) h g=
 UniformRankCrossPreparationMachine.kernelValues original h g := rfl

/-- Algebraic join of two actual produced-bank postconditions. All three
original banks and the new conjugate bank remain physical guarded sources. -/
theorem seedHeight_sources {n:ℕ} (j:Fin (O.axisCount n)) (c:UniformSeedHeightPreparation.Config) (B dest:ℕ)
 (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedHeightPreparation.parameters n j c) B)
 (work:RC.Parameters) (s:State)
 (orig:UniformSeedHeightPreparation.Result n j c B layout s)
 (new:Result n j (relocated (UniformSeedHeightPreparation.parameters n j c).base work) dest s) :
 UniformMatchingConjugateLoadMachine.Sources c.exponent c.C c.negative c.constants dest
   (fun i:Fin (7*c.width)=>UniformRankCrossReplayPreparationMachine.bankValues
     (UniformSeedHeightPreparation.parameters n j c) (UniformSeedRankCrossPreparation.hValue n j)
       (UniformSeedRankCrossPreparation.gValue n j) i.val) s := by
 let p:=UniformSeedHeightPreparation.parameters n j c
 have pos:=UniformRankCrossReplayPreparationMachine.bank_source (p:=p) orig.positive
 refine ⟨?_,?_,?_,orig.constants⟩
 · intro i;exact pos i.val i.isLt
 · intro i;exact orig.negative i.val i.isLt
 · intro i
   have hi:i.val<UniformToeplitzCrossDAG.bankSize p.base.K:=by
     change i.val<width p.base.K+6*width p.base.K
     have h:=i.isLt;change i.val<7*width p.base.K at h;omega
   have value:=new i
   change s.scalarHeap (dest+i.val)=some (prepared (starRingEnd ℂ
     (bankValue p.base.K (UniformRankCrossPreparationMachine.kernelValues
       (selected n j (relocated p.base work)) (originalH n j) (originalG n j)) i))) at value
   rw [kernelValues_selected_relocated,originalH_eq,originalG_eq] at value
   dsimp only [p] at hi value
   simpa only [UniformRankCrossReplayPreparationMachine.bankValues,dite_eq_left hi,bankValue] using value


/-- Original positive, negative and constant banks are transported through the
actual fresh-workspace execution, not accepted as freshly supplied sources. -/
theorem seedHeight_sources_retained {n:ℕ} (j:Fin (O.axisCount n)) (c:UniformSeedHeightPreparation.Config) (B dest:ℕ)
 (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (UniformSeedHeightPreparation.parameters n j c) B)
 (work:RC.Parameters) (s u:State)
 (orig:UniformSeedHeightPreparation.Result n j c B layout s)
 (new:Result n j (relocated (UniformSeedHeightPreparation.parameters n j c).base work) dest u)
 (alloc:Allocation n j (relocated (UniformSeedHeightPreparation.parameters n j c).base work) dest B)
 (frame:Frame (relocated (UniformSeedHeightPreparation.parameters n j c).base work) dest s u)
 (positive:c.C+7*c.width ≤ work.S) (negative:c.negative+7*c.width ≤ work.S)
 (constants:c.constants+6 ≤ work.S) :
 UniformMatchingConjugateLoadMachine.Sources c.exponent c.C c.negative c.constants dest
   (fun i:Fin (7*c.width)=>UniformRankCrossReplayPreparationMachine.bankValues
     (UniformSeedHeightPreparation.parameters n j c) (UniformSeedRankCrossPreparation.hValue n j)
       (UniformSeedRankCrossPreparation.gValue n j) i.val) u := by
 let p:=UniformSeedHeightPreparation.parameters n j c
 have pos:=UniformRankCrossReplayPreparationMachine.bank_source (p:=p) orig.positive
 refine ⟨?_,?_,?_,?_⟩
 · intro i
   exact (frame.scalar_before alloc _ (by have:=i.isLt;change _<work.S;omega)).trans (pos i.val i.isLt)
 · intro i
   exact (frame.scalar_before alloc _ (by have:=i.isLt;change _<work.S;omega)).trans (orig.negative i.val i.isLt)
 · intro i
   have hi:i.val<UniformToeplitzCrossDAG.bankSize p.base.K:=by
     change i.val<width p.base.K+6*width p.base.K
     have h:=i.isLt;change i.val<7*width p.base.K at h;omega
   have value:=new i
   change u.scalarHeap (dest+i.val)=some (prepared (starRingEnd ℂ
     (bankValue p.base.K (UniformRankCrossPreparationMachine.kernelValues
       (selected n j (relocated p.base work)) (originalH n j) (originalG n j)) i))) at value
   rw [kernelValues_selected_relocated,originalH_eq,originalG_eq] at value
   dsimp only [p] at hi value
   simpa only [UniformRankCrossReplayPreparationMachine.bankValues,dite_eq_left hi,bankValue] using value
 · intro i hi
   exact (frame.scalar_before alloc _ (by change _<work.S;omega)).trans (orig.constants i hi)

/-- The selected matching-chunk postcondition contains the same original
produced coefficient sources; its geometry does not change their meaning. -/
theorem seedChunk_sources {n:ℕ} (hn:0<n) (j:Fin (O.axisCount n)) (c:UniformSeedChunkPreparation.Config) (B dest:ℕ)
 (layout:UniformSeedChunkPreparation.Layout n j c B) (work:RC.Parameters) (s:State)
 (orig:UniformSeedChunkPreparation.Result n j c B hn layout s)
 (new:Result n j (relocated (UniformSeedHeightPreparation.parameters n j c.seed).base work) dest s) :
 UniformMatchingConjugateLoadMachine.Sources c.seed.exponent c.seed.C c.seed.negative c.seed.constants dest
   (fun i:Fin (7*c.seed.width)=>UniformRankCrossReplayPreparationMachine.bankValues
     (UniformSeedHeightPreparation.parameters n j c.seed) (UniformSeedRankCrossPreparation.hValue n j)
       (UniformSeedRankCrossPreparation.gValue n j) i.val) s :=
 seedHeight_sources j c.seed B dest (layout.seed.replay hn j c.seed B) work s orig.prepared new

end
end ExactFourierCircuits.UniformConjugateRankSpectrumPreparation
