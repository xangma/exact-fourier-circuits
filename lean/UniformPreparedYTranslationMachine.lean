import UniformRepeatedMaskMachine
import UniformXorTranslationMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformPreparedYTranslationMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformXorTableMachine (Entries Outside TableFrame tableProgram)
open UniformXorTranslationMachine (volume)
open BinaryFrames

def remember : List Op := [.literal 3373 1,.mul 3368 3420 3373,.mul 3354 3421 3373]
def headers : List Op := [.literal 3366 1,.mul 3353 3423 3366,.mul 3361 3369 3366,
 .mul 3362 3375 3366,.mul 3363 3371 3366,.mul 3421 3354 3366]
/-- A single literal program produces its own xor table, reads the actual
original-width descriptor, computes its copied direction and translates data.
It neither requests roots nor uses a ready output mask/table. -/
def program : Program := remember.map Op.code++tableProgram.map (relocate 3 41)++
 UniformRepeatedMaskMachine.program.map (relocate 41 57)++headers.map Op.code++
 UniformXorTranslationMachine.program.map (relocate 63 115)++[.halt]
lemma program_length : program.length=116 := rfl
lemma remember_code : BlockAt remember program 0 := by intro i hi;change i < 3 at hi;interval_cases i <;> rfl
lemma table_code : CodeAt tableProgram program 3 41 := by intro i hi;change i < 38 at hi;interval_cases i <;> rfl
lemma mask_code : CodeAt UniformRepeatedMaskMachine.program program 41 57 := by intro i hi;change i < 16 at hi;interval_cases i <;> rfl
lemma headers_code : BlockAt headers program 57 := by intro i hi;change i < 6 at hi;interval_cases i <;> rfl
lemma translation_code : CodeAt UniformXorTranslationMachine.program program 63 115 := by intro i hi;change i < 52 at hi;interval_cases i <;> rfl
lemma halt_at : program[115]?=some .halt := rfl

def tableCost (q : ℕ) := 4*q+10+(12*q+15)*(2^q*2^q)
def runtime (q w : ℕ) := tableCost q+9*(q*w)+(17*w+25)*volume q w+31
noncomputable section

def Changed (r : ℕ) := UniformXorTranslationMachine.Changed r ∨ r=3368 ∨
 r=3353 ∨ r=3354 ∨ (3361 ≤ r∧r<3364) ∨ (3371 ≤ r∧r<3379) ∨ (3400 ≤ r∧r<3431)
structure Frame (q A E T w : ℕ) (s v : State) : Prop where
 natHeap : Outside q T s.natHeap v
 outputs : v.outputs=s.outputs
 roots : v.rootOrders=s.rootOrders
 natReg : ∀r,¬Changed r → v.natReg r=s.natReg r
 scalarReg : ∀r,r ≠ 100 → r ≠ 114 → v.scalarReg r=s.scalarReg r
 scalarHeap : ∀z,(z < A ∨ A+volume q w ≤ z) → (z < E ∨ E+volume q w ≤ z) → v.scalarHeap z=s.scalarHeap z

/-- Entry contains only ordinary addresses, q/width and actual original data /
original descriptor cells. All new banks and readiness are produced by code. -/
theorem execution (q w A E T U B n : ℕ) (u : Vec (Fin w)) (x : Fin n → ℂ)
 (f : Fin (volume q w) → Scalar) (s : State) (pc : s.pc=0)
 (hq : s.natReg 3420=q) (hT : s.natReg 3421=T) (hw : s.natReg 3369=w)
 (hU : s.natReg 3370=U) (hA : s.natReg 3360=A) (hE : s.natReg 3364=E)
 (descriptor : UniformRepeatedMaskMachine.Source U u s)
 (data : ∀j,s.scalarHeap (A+j.val)=some (f j))
 (sourceBeforeTable : U+w ≤ T) (separate : A+volume q w ≤ E)
 (bound : WordBound B s) (code : 116 ≤ B) (tableEnd : T+2^q*2^q ≤ B) (extent : E+volume q w ≤ B) : ∃v,
 BoundedExecution program n x B s (runtime q w) v ∧ v.pc=115 ∧
 (∀j,v.scalarHeap (A+j.val)=some (UniformXorTranslationMachine.translated q w
  (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).val
  (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).isLt f j)) ∧ Frame q A E T w s v := by
 have safe : readable remember s∧peak remember s ≤ B := by
  have qB:=bound.2.1 3420
  have tB:=bound.2.1 3421
  simp [remember,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,hq,hT]
  omega
 have first:=block_runs remember program 0 n B x s remember_code pc bound (by change 3 ≤ B;omega) safe.1 safe.2
 let saved:=applyBlock remember s
 let tableEntry:=setPC saved 0
 have eb:=changePC_bound B saved 0 first.final_bound (by omega)
 have tq : tableEntry.natReg 3420=q := by simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hq]
 have tb : tableEntry.natReg 3421=T := by simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hT]
 obtain ⟨t,rt,pt,sz,et,ot,ft⟩:=UniformXorCallerInterface.table_execution_bounded_size n q T B x tableEntry rfl tq tb eb (by omega) tableEnd
 have placedT:=UniformBoundedAssembly.boundedExecution_placed table_code (by change 3+38 ≤ B;omega) (by omega) rt
 have same : UniformAssembly.placed 3 tableEntry=saved := by
  simp [UniformAssembly.placed,tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,pc]
 rw [same] at placedT
 let maskEntry:=setPC t 0
 have mb:=changePC_bound B t 0 rt.final_bound (by omega)
 have mq : maskEntry.natReg 3368=q := by
  rw [show maskEntry.natReg 3368=t.natReg 3368 by rfl,ft.2.2.2.2 3368 (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hq]
 have mw : maskEntry.natReg 3369=w := by
  rw [show maskEntry.natReg 3369=t.natReg 3369 by rfl,ft.2.2.2.2 3369 (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hw]
 have mu : maskEntry.natReg 3370=U := by
  rw [show maskEntry.natReg 3370=t.natReg 3370 by rfl,ft.2.2.2.2 3370 (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hU]
 have desc : UniformRepeatedMaskMachine.Source U u maskEntry := by
  intro j
  rw [show maskEntry.natHeap (U+j.val)=t.natHeap (U+j.val) by rfl,ot (U+j.val) (Or.inl (by have hj:=j.isLt;omega))]
  exact descriptor j
 have ve : volume q w ≤ B:=by omega
 obtain ⟨m,rm,pm,mask,power,fm⟩:=UniformRepeatedMaskMachine.execution q w U B n u x maskEntry rfl mq mw mu desc mb
  (by omega) (by omega) ve
 have placedM:=UniformBoundedAssembly.boundedExecution_placed mask_code (by change 41+16 ≤ B;omega) (by omega) rm
 let afterTable:=setPC t 41
 have sameM : UniformAssembly.placed 41 maskEntry=afterTable:=rfl
 rw [sameM] at placedM
 let headerEntry:=setPC m 57
 have hb:=changePC_bound B m 57 rm.final_bound (by omega)
 have keep (r : ℕ) (hr : r < 3371) : headerEntry.natReg r=tableEntry.natReg r :=
  (fm.natReg r (Or.inl hr)).trans (ft.2.2.2.2 r (Or.inl (by omega)))
 have aH : headerEntry.natReg 3360=A := by
  rw [keep _ (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hA]
 have eH : headerEntry.natReg 3364=E := by
  rw [keep _ (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hE]
 have wH : headerEntry.natReg 3369=w := by
  rw [keep _ (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hw]
 have bH : headerEntry.natReg 3354=T := by
  rw [keep _ (by omega)]
  simp [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next,hT]
 have sizeH : headerEntry.natReg 3423=2^q := (fm.natReg _ (by omega)).trans sz
 have powerH : headerEntry.natReg 3375=volume q w := power
 have maskH : headerEntry.natReg 3371=(UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).val := mask
 have safeH : readable headers headerEntry∧peak headers headerEntry ≤ B := by
  have mm:=(UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)).isLt
  have sizeB:=rm.final_bound.2.1 3423
  change headerEntry.natReg 3423 ≤ B at sizeB
  rw [sizeH] at sizeB
  simp [headers,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,wH,bH,sizeH,powerH,maskH]
  unfold volume at *
  omega
 have install:=block_runs headers program 57 n B x headerEntry headers_code rfl hb (by change 63 ≤ B;omega) safeH.1 safeH.2
 let ready:=applyBlock headers headerEntry
 let caller:=setPC ready 0
 have cb:=changePC_bound B ready 0 install.final_bound (by omega)
 let maskFin:=UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)
 have hdr : UniformXorTranslationMachine.Header q w maskFin.val A E caller := by
  constructor <;> simp [caller,setPC,ready,headers,applyBlock,Op.apply,writeNat,next,aH,eH,wH,bH,sizeH,powerH,maskH,maskFin]
 have baseH : caller.natReg 3421=T := by
  simp [caller,setPC,ready,headers,applyBlock,Op.apply,writeNat,next,bH]
 have dataC : ∀j,caller.scalarHeap (A+j.val)=some (f j) := by
  intro j
  rw [show caller.scalarHeap=m.scalarHeap by rfl,fm.scalarHeap,show maskEntry.scalarHeap=t.scalarHeap by rfl,ft.1]
  exact data j
 have entriesC : Entries q T (2^q*2^q) caller := by
  intro j hj
  rw [show caller.natHeap=m.natHeap by rfl,fm.natHeap]
  exact et j hj
 obtain ⟨v,rv,pv,values,fv,_⟩:=UniformXorTranslationMachine.execution q w maskFin.val A E T B n maskFin.isLt x f caller rfl hdr dataC baseH entriesC
  separate cb (by omega) tableEnd extent
 have placedV:=UniformBoundedAssembly.boundedExecution_placed translation_code (by change 63+52 ≤ B;omega) (by omega) rv
 have sameV : UniformAssembly.placed 63 caller=ready := by
  simp [UniformAssembly.placed,caller,setPC,ready,headers,applyBlock,Op.apply,writeNat,next,headerEntry]
 rw [sameV] at placedV
 let result:=setPC v 115
 have rb:=changePC_bound B v 115 rv.final_bound (by omega)
 have halt : BoundedExecution program n x B result 1 result:=.halt rb (by simp [step,result,setPC,halt_at])
 have frame : Frame q A E T w s result := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    rw [show result.natHeap=v.natHeap by rfl,fv.natHeap,show caller.natHeap=m.natHeap by rfl,fm.natHeap]
    exact ot z hz
  · exact fv.outputs.trans (fm.outputs.trans ft.2.2.1)
  · exact fv.roots.trans (fm.roots.trans ft.2.2.2.1)
  · intro r hr
    have nr:=fv.natReg r (fun h=>hr (Or.inl h))
    rw [show result.natReg r=v.natReg r by rfl,nr]
    have h1:r ≠ 3353∧r ≠ 3361∧r ≠ 3362∧r ≠ 3363∧r ≠ 3366∧r ≠ 3421:=by unfold Changed UniformXorTranslationMachine.Changed at hr;omega
    have h2:r < 3371∨3379 ≤ r:=by unfold Changed at hr;omega
    have h3:r < 3400∨3431 ≤ r:=by unfold Changed at hr;omega
    simp only [caller,setPC,ready,headers,applyBlock,Op.apply,writeNat,next]
    simp only [Function.update_apply]
    simp only [h1.1,h1.2.1,h1.2.2.1,h1.2.2.2.1,h1.2.2.2.2.1,h1.2.2.2.2.2,ite_false]
    change m.natReg r=s.natReg r
    rw [fm.natReg r h2]
    change t.natReg r=s.natReg r
    rw [ft.2.2.2.2 r h3]
    unfold Changed at hr
    simp (disch:=omega) [tableEntry,setPC,saved,remember,applyBlock,Op.apply,writeNat,next]
  · intro r h100 h114
    exact (fv.scalarReg r h100 h114).trans ((congrFun fm.scalarReg r).trans (congrFun ft.2.1 r))
  · intro z hA hE
    exact (fv.scalarHeap z hA hE).trans ((congrFun fm.scalarHeap z).trans (congrFun ft.1 z))
 refine ⟨result,?_,rfl,values,frame⟩
 convert first.trans (placedT.trans (placedM.trans (install.trans placedV))) |>.executes halt using 1
 simp only [remember,headers,List.length_cons,List.length_nil,runtime,tableCost,volume]
 ring
/-- The physical native addresses are the explicit binary coordinates. This
is exactly the copied Y direction, not the residual tensor-C operation. -/
theorem coordinate_execution (q w A E T U B n : ℕ) (u : Vec (Fin w)) (x : Fin n → ℂ)
 (f : Vec (Fin (q*w)) → Scalar) (s : State) (pc : s.pc=0)
 (hq : s.natReg 3420=q) (hT : s.natReg 3421=T) (hw : s.natReg 3369=w)
 (hU : s.natReg 3370=U) (hA : s.natReg 3360=A) (hE : s.natReg 3364=E)
 (descriptor : UniformRepeatedMaskMachine.Source U u s)
 (data : ∀j:Fin (volume q w),s.scalarHeap (A+j.val)=some (f (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j)))
 (sourceBeforeTable : U+w ≤ T) (separate : A+volume q w ≤ E)
 (bound : WordBound B s) (code : 116 ≤ B) (tableEnd : T+2^q*2^q ≤ B) (extent : E+volume q w ≤ B) : ∃v,
 BoundedExecution program n x B s (runtime q w) v ∧ v.pc=115 ∧
 (∀j:Fin (volume q w),v.scalarHeap (A+j.val)=some
  (f (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j+ColumnTerminalFlat.direction q u))) ∧ Frame q A E T w s v := by
 obtain ⟨v,rv,pv,values,frame⟩:=execution q w A E T U B n u x
  (fun j=>f (UniformBinaryXorCoordinates.binaryCoordinates (q*w) j)) s pc hq hT hw hU hA hE descriptor data sourceBeforeTable separate bound code tableEnd extent
 refine ⟨v,rv,pv,?_,frame⟩
 intro j
 rw [values]
 change some (f (UniformBinaryXorCoordinates.binaryCoordinates (q*w)
  (UniformBinaryXorCoordinates.xorIndex j (UniformBinaryXorCoordinates.encode (ColumnTerminalFlat.direction q u)))))=some _
 exact congrArg (fun z=>some (f z)) (UniformBinaryXorCoordinates.translated_address (k:=q*w) j (ColumnTerminalFlat.direction q u))

/-- With fixed original width at least three, table construction and every
mask/index/load/store instruction fit one linear array-work allowance. -/
theorem runtime_linear (q w : ℕ) (hw : 3 ≤ w) : runtime q w ≤ (17*w+90)*volume q w := by
 have fit : 3*q ≤ q*w := by
  calc 3*q=q*3 := by ring
       _ ≤ q*w := Nat.mul_le_mul_left q hw
 have table:=UniformXorWordBounds.table_cost_array_bound q (q*w) fit
 change tableCost q ≤ 25*volume q w at table
 have bit : q*w ≤ volume q w:=Nat.le_of_lt Nat.lt_two_pow_self
 have positive : 1 ≤ volume q w:=Nat.two_pow_pos (q*w)
 unfold runtime
 nlinarith only [table,bit,positive]
end
end ExactFourierCircuits.UniformPreparedYTranslationMachine

