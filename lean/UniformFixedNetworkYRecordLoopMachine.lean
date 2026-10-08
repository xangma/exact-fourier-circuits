import UniformFixedNetworkExchangeRecordMachine
import UniformFixedNetworkYRecordMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkYRecordLoopMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords)
namespace S
export UniformFixedNetworkChildDispatchMachine (scalarProgram shearRecord scalar_execution ScalarFrame ScalarChanged)
end S
namespace P
export UniformFixedNetworkPaddingChildMachine (dispatchProgram record dispatch_execution FullFrame FullChanged values)
end P
namespace Y
export UniformFixedNetworkYRecordMachine (Direction record execution FullFrame FullChanged actions runtime)
end Y
namespace E
export UniformFixedNetworkExchangeRecordMachine (Pair record execution FullFrame FullChanged actions)
end E

/-- Four implemented record kinds. Other opcodes retain an explicit failure
branch; this is not yet the complete fixed saving-network interpreter. -/
inductive Item (R w:ℕ) where
 | scalar (d source:Fin R) (distinct:d≠source) (code:Fin 5)
 | padding (first count:ℕ) (capacity:first+count≤R)
 | exchange (pairs:List (E.Pair R))
 | translation (directions:List (Y.Direction R w))
def Item.record {R:ℕ} (q w:ℕ) : Item R w→Record
 | .scalar d source _ k=>S.shearRecord q w d source k
 | .padding first count _=>P.record q w first count
 | .exchange pairs=>E.record q w pairs
 | .translation ds=>Y.record q w ds
def Item.length {R:ℕ} (q w:ℕ) (item:Item R w) := (item.record q w).data.length
lemma Item.length_pos {R:ℕ} (q w:ℕ) (item:Item R w) : 8 ≤ item.length q w := by
 cases item <;> simp [Item.length,Item.record,
   UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkChildDispatchMachine.shearRecord,
   UniformFixedNetworkScheduleMachine.Record.data_length ]
def size {R:ℕ} (q w:ℕ) (items:List (Item R w)) := (items.map (Item.length q w)).sum
lemma size_cons {R:ℕ} (q w:ℕ) (item:Item R w) (items:List (Item R w)) :
 size q w (item::items)=item.length q w+size q w items := rfl

def boot : List Op := [.literal 3310 1,.literal 3311 5,.literal 3312 0,.literal 3314 4,.literal 3315 3]
def control : Program := boot.map Op.code++
 [.branchLT 2850 3301 6 534,.loadNat 3313 2850,
 .branchLT 3313 3310 15 8,.branchLT 3310 3313 9 16,
 .branchLT 3313 3315 15 10,.branchLT 3315 3313 11 336,
 .branchLT 3313 3314 15 12,.branchLT 3314 3313 13 238,
 .branchLT 3313 3311 15 14,.branchLT 3311 3313 15 122,
 .natBinary .div 3312 3312 3312]
def program : Program := control++S.scalarProgram.map (relocate 16 533)++
 P.dispatchProgram.map (relocate 122 533)++UniformFixedNetworkExchangeRecordMachine.program.map (relocate 238 533)++
 UniformFixedNetworkYRecordMachine.program.map (relocate 336 533)++[.jump 5,.halt]
lemma control_length : control.length=16 := rfl
lemma program_length : program.length=535 := by
 simp only [program,List.length_append,List.length_map,control_length,
  UniformFixedNetworkChildDispatchMachine.scalarProgram_length,UniformFixedNetworkPaddingChildMachine.dispatchProgram_length,
  UniformFixedNetworkExchangeRecordMachine.program_length,UniformFixedNetworkYRecordMachine.program_length]
 rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma scalar_code : CodeAt S.scalarProgram program 16 533 := by intro i hi;change i<106 at hi;interval_cases i <;> rfl
lemma padding_code : CodeAt P.dispatchProgram program 122 533 := by intro i hi;change i<116 at hi;interval_cases i <;> rfl
lemma exchange_code : CodeAt UniformFixedNetworkExchangeRecordMachine.program program 238 533 := by intro i hi;change i<98 at hi;interval_cases i <;> rfl
lemma y_prefix_length : (control++S.scalarProgram.map (relocate 16 533)++P.dispatchProgram.map (relocate 122 533)++UniformFixedNetworkExchangeRecordMachine.program.map (relocate 238 533)).length=336 := by
 simp only [List.length_append,List.length_map,control_length,UniformFixedNetworkChildDispatchMachine.scalarProgram_length,UniformFixedNetworkPaddingChildMachine.dispatchProgram_length,UniformFixedNetworkExchangeRecordMachine.program_length]
lemma y_code : CodeAt UniformFixedNetworkYRecordMachine.program program 336 533 := by
 intro i hi
 unfold program
 rw [List.getElem?_append_left (by rw [List.length_append,y_prefix_length,List.length_map];omega)]
 rw [List.getElem?_append_right (by rw [y_prefix_length];omega)]
 simp only [y_prefix_length,Nat.add_sub_cancel_left,List.getElem?_map]
lemma branch_at : program[5]?=some (.branchLT 2850 3301 6 534) := rfl
lemma read_at : program[6]?=some (.loadNat 3313 2850) := rfl
lemma decision_at (i:ℕ) (hi:i<8) : program[7+i]?=
 ([.branchLT 3313 3310 15 8,.branchLT 3310 3313 9 16,
 .branchLT 3313 3315 15 10,.branchLT 3315 3313 11 336,
 .branchLT 3313 3314 15 12,.branchLT 3314 3313 13 238,
 .branchLT 3313 3311 15 14,.branchLT 3311 3313 15 122]:Program)[i]? := by interval_cases i <;> rfl
lemma guard_at : program[15]?=some (.natBinary .div 3312 3312 3312) := rfl
lemma prefix_length : (control++S.scalarProgram.map (relocate 16 533)++P.dispatchProgram.map (relocate 122 533)++
 UniformFixedNetworkExchangeRecordMachine.program.map (relocate 238 533)++
 UniformFixedNetworkYRecordMachine.program.map (relocate 336 533)).length=533 := by
 simp only [List.length_append,List.length_map,control_length,UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
 UniformFixedNetworkPaddingChildMachine.dispatchProgram_length,UniformFixedNetworkExchangeRecordMachine.program_length,
 UniformFixedNetworkYRecordMachine.program_length]
lemma jump_at : program[533]?=some (.jump 5) := by
 unfold program
 rw [List.getElem?_append_right (by simpa only [prefix_length] using (by decide:533≤533)),prefix_length];rfl
lemma halt_at : program[534]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simpa only [prefix_length] using (by decide:533≤534)),prefix_length];rfl

noncomputable section
def Item.action {R:ℕ} (q w:ℕ) (f:Fin R→Fin (2^(q*w))→Scalar) : Item R w→Fin R→Fin (2^(q*w))→Scalar
 | .scalar d source _ k=>UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode k) f
 | .padding first count _=>P.values (q*w) first count f
 | .exchange pairs=>E.actions pairs f
 | .translation ds=>Y.actions q w ds f
def Item.cost {R:ℕ} (q w:ℕ) : Item R w→ℕ
 | .scalar _ _ _ k=>10*2^(q*w)+4*(q*w)+k.val+67
 | .padding _ count _=>count*((q*w)*(25*2^(q*w-1)+11)+15)+4*(q*w)+61
 | .exchange pairs=>(10*2^(q*w)+21)*pairs.length+4*(q*w)+59
 | .translation ds=>Y.runtime q w ds.length+7
def actions {R:ℕ} (q w:ℕ) (items:List (Item R w)) (f:Fin R→Fin (2^(q*w))→Scalar) :=
 items.foldl (fun a item=>item.action q w a) f
def cost {R:ℕ} (q w:ℕ) (items:List (Item R w)) := (items.map (Item.cost q w)).sum
structure Header (A T E Buf X:ℕ) (s:State) : Prop where
 pc:s.pc=5
 base:s.natReg 3300=A
 cursor:s.natReg 2850=T
 endptr:s.natReg 3301=E
 one:s.natReg 3310=1
 five:s.natReg 3311=5
 zero:s.natReg 3312=0
 four:s.natReg 3314=4
 three:s.natReg 3315=3
 buffer:s.natReg 3364=Buf
 table:s.natReg 3389=X

def Changed (r:ℕ) : Prop := S.ScalarChanged r∨P.FullChanged r∨E.FullChanged r∨Y.FullChanged r∨r=3313
structure Frame (q w A W Buf X:ℕ) (s u:State) : Prop where
 natHeap:UniformXorTableMachine.Outside q X s.natHeap u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀ r, ¬Changed r→u.natReg r=s.natReg r
 scalarReg:∀ r, 115≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,(z<A∨A+W≤z)→(z<Buf∨Buf+2^(q*w)≤z)→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (q w A W Buf X:ℕ) (s:State) : Frame q w A W Buf X s s := ⟨fun _ _=>rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
lemma Frame.pc {q w A W Buf X:ℕ} {s u:State} (f:Frame q w A W Buf X s u) (p:ℕ) : Frame q w A W Buf X s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {q w A W Buf X:ℕ} {s u t:State} (f:Frame q w A W Buf X s u) (g:Frame q w A W Buf X u t) : Frame q w A W Buf X s t :=
 ⟨fun z h=>(g.natHeap z h).trans (f.natHeap z h),g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
 fun z h j=>(g.scalarHeap z h j).trans (f.scalarHeap z h j)⟩
lemma Frame.scalar {q w A W Buf X D L:ℕ} {s u:State} (lo:A≤D) (hi:D+L≤A+W) (f:S.ScalarFrame D L s u) : Frame q w A W Buf X s u := by
 refine ⟨fun z _=>congrFun f.natHeap z,f.outputs,f.roots,?_,?_,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;apply f.scalarReg <;> omega
 · intro z h _;apply f.scalarHeap;omega
lemma Frame.padding {q w A W Buf X D L:ℕ} {s u:State} (lo:A≤D) (hi:D+L≤A+W) (f:P.FullFrame D L s u) : Frame q w A W Buf X s u := by
 refine ⟨fun z _=>congrFun f.natHeap z,f.outputs,f.roots,?_,?_,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;apply f.scalarReg;omega
 · intro z h _;apply f.scalarHeap;omega
lemma Frame.exchange {q w A W Buf X:ℕ} {s u:State} (f:E.FullFrame A W s u) : Frame q w A W Buf X s u := by
 refine ⟨fun z _=>congrFun f.natHeap z,f.outputs,f.roots,?_,?_,fun z h _=>f.scalarHeap z h⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;exact f.scalarReg r (Or.inr (by omega))
lemma Frame.y {q w A W Buf X:ℕ} {s u:State} (f:Y.FullFrame q A W Buf X w s u) : Frame q w A W Buf X s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,?_,f.scalarHeap⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;exact f.scalarReg r (by omega) (by omega)
lemma Frame.constants {q w A W Buf X:ℕ} {s u:State} (ha:3≤A) (sep:A+W≤Buf) (f:Frame q w A W Buf X s u)
 (con:UniformBinaryCStageMachine.Constants s) : UniformBinaryCStageMachine.Constants u := by
 unfold UniformBinaryCStageMachine.Constants
 rw [f.scalarHeap 1 (by omega) (by omega),f.scalarHeap 2 (by omega) (by omega)];exact con

def selected (tag entry:ℕ) (s:State) := setPC (writeNat (setPC s 6) 3313 tag) entry
lemma selected_frame (q w A W Buf X tag entry:ℕ) (s:State) : Frame q w A W Buf X s (selected tag entry s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [selected,setPC,writeNat,next]

/-- Every supported branch reads the real opcode from the physical table. -/
lemma select_runs (A T E Buf X B n tag:ℕ) (x:Fin n→ℂ) (s:State) (h:Header A T E Buf X s)
 (yes:T<E) (supported:tag=1∨tag=3∨tag=4∨tag=5) (head:s.natHeap T=some tag) (hs:WordBound B s) (code:535≤B) :
 BoundedRuns program n x B s (if tag=1 then 4 else if tag=3 then 6 else if tag=4 then 8 else 10)
 (selected tag (if tag=1 then 16 else if tag=3 then 336 else if tag=4 then 238 else 122) s) := by
 let e:=setPC s 6
 have eb:=changePC_bound B s 6 hs (by omega)
 have first:step program n x s=.running e:=by simp [step,h.pc,branch_at,h.cursor,h.endptr,yes,e,setPC]
 rcases supported with rfl|rfl|rfl|rfl
 · let r:=writeNat e 3313 1
   have rb:=writeNat_bound B e 3313 1 eb (by change 7≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤535) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 8 (by omega)) ?_ (.refl (bp 16 (by omega))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,decision_at 0 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 1 (by decide),h.one,selected]
 · let r:=writeNat e 3313 3
   have rb:=writeNat_bound B e 3313 3 eb (by change 7≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤535) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 8 (by omega)) ?_ (.next (bp 9 (by omega)) ?_ (.next (bp 10 (by omega)) ?_ (.refl (bp 336 (by omega))))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,decision_at 0 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 1 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 2 (by decide),h.three]
   · simp [step,r,e,setPC,writeNat,next,decision_at 3 (by decide),h.three,selected]
 · let r:=writeNat e 3313 4
   have rb:=writeNat_bound B e 3313 4 eb (by change 7≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤535) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 8 (by omega)) ?_ (.next (bp 9 (by omega)) ?_ (.next (bp 10 (by omega)) ?_ (.next (bp 11 (by omega)) ?_ (.next (bp 12 (by omega)) ?_ (.refl (bp 238 (by omega))))))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,decision_at 0 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 1 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 2 (by decide),h.three]
   · simp [step,r,e,setPC,writeNat,next,decision_at 3 (by decide),h.three]
   · simp [step,r,e,setPC,writeNat,next,decision_at 4 (by decide),h.four]
   · simp [step,r,e,setPC,writeNat,next,decision_at 5 (by decide),h.four,selected]
 · let r:=writeNat e 3313 5
   have rb:=writeNat_bound B e 3313 5 eb (by change 7≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤535) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 8 (by omega)) ?_ (.next (bp 9 (by omega)) ?_ (.next (bp 10 (by omega)) ?_ (.next (bp 11 (by omega)) ?_ (.next (bp 12 (by omega)) ?_ (.next (bp 13 (by omega)) ?_ (.next (bp 14 (by omega)) ?_ (.refl (bp 122 (by omega))))))))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,decision_at 0 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 1 (by decide),h.one]
   · simp [step,r,e,setPC,writeNat,next,decision_at 2 (by decide),h.three]
   · simp [step,r,e,setPC,writeNat,next,decision_at 3 (by decide),h.three]
   · simp [step,r,e,setPC,writeNat,next,decision_at 4 (by decide),h.four]
   · simp [step,r,e,setPC,writeNat,next,decision_at 5 (by decide),h.four]
   · simp [step,r,e,setPC,writeNat,next,decision_at 6 (by decide),h.five]
   · simp [step,r,e,setPC,writeNat,next,decision_at 7 (by decide),h.five,selected]

lemma branch_execution {R:ℕ} (q w A T E Buf X B n:ℕ) (x:Fin n→ℂ) (item:Item R w)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E Buf X s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:535≤B) (tableEnd:T+item.length q w≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤Buf) (bufferEnd:Buf+2^(q*w)≤B) (fresh:T+item.length q w≤X) (tableCapacity:X+2^q*2^q≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w-1) (setPC u 533) ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 u.natReg 2850=T+item.length q w ∧ Frame q w A (R*2^(q*w)) Buf X s u ∧
 UniformBinaryCStageMachine.Constants u := by
 have bufB : Buf≤B := (Nat.le_add_right Buf (2^(q*w))).trans bufferEnd
 have globalB : A+R*2^(q*w)≤B := extent.trans bufB
 cases item with
 | scalar d source ne k=>
   have actual:s.natHeap T=some 1:=by simpa [Item.record,S.shearRecord,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A T E Buf X B n 1 x s h yes (Or.inl rfl) actual hs code
   let e:=selected 1 16 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩:=S.scalar_execution q w A T B n x d source ne k f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data cb (by omega) (by simpa [Item.length,Item.record,UniformFixedNetworkChildDispatchMachine.shearRecord,UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkScheduleMachine.Record.data_length] using tableEnd) width globalB
   have placed:=UniformBoundedAssembly.boundedExecution_placed scalar_code (by change 122≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 16 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤UniformFixedNetworkShearChildMachine.roleBase A (2^(q*w)) d.val:=by unfold UniformFixedNetworkShearChildMachine.roleBase;omega
   have hi:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*w)) d
   have full:Frame q w A (R*2^(q*w)) Buf X s child:=((selected_frame q w _ _ Buf X 1 16 s).pc 0).trans (Frame.scalar lo hi cf)
   refine ⟨child,?_,output,cursor,full,full.constants ha extent con⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
 | padding first count capacity=>
   have actual:s.natHeap T=some 5:=by simpa [Item.record,P.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A T E Buf X B n 5 x s h yes (Or.inr (Or.inr (Or.inr rfl))) actual hs code
   let e:=selected 5 122 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf,cc⟩:=P.dispatch_execution q w A T first count B n x f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data con capacity ha hr cb (by omega) (by simpa [Item.length,Item.record,UniformFixedNetworkChildDispatchMachine.shearRecord,UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkScheduleMachine.Record.data_length] using tableEnd) width globalB
   have placed:=UniformBoundedAssembly.boundedExecution_placed padding_code (by change 238≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 122 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤A+first*2^(q*w):=by omega
   have hi:A+first*2^(q*w)+count*2^(q*w)≤A+R*2^(q*w):=by
     have hp:=Nat.mul_le_mul_right (2^(q*w)) capacity
     rw [Nat.add_mul] at hp;omega
   have full:Frame q w A (R*2^(q*w)) Buf X s child:=((selected_frame q w _ _ Buf X 5 122 s).pc 0).trans (Frame.padding lo hi cf)
   refine ⟨child,?_,output,cursor,full,cc⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
 | exchange pairs=>
   have actual:s.natHeap T=some 4:=by simpa [Item.record,UniformFixedNetworkExchangeRecordMachine.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A T E Buf X B n 4 x s h yes (Or.inr (Or.inr (Or.inl rfl))) actual hs code
   let e:=selected 4 238 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩ :=UniformFixedNetworkExchangeRecordMachine.execution q w A T B n x pairs f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data hr cb (by omega) globalB
     (by simpa [Item.length,Item.record,UniformFixedNetworkExchangeRecordMachine.record_length,Nat.add_assoc] using tableEnd) width
   have placed:=UniformBoundedAssembly.boundedExecution_placed exchange_code (by change 336≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 238 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have full:Frame q w A (R*2^(q*w)) Buf X s child:=((selected_frame q w _ _ Buf X 4 238 s).pc 0).trans (Frame.exchange cf)
   refine ⟨child,?_,output,?_,full,full.constants ha extent con⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · simpa [Item.length,Item.record,UniformFixedNetworkExchangeRecordMachine.record_length,Nat.add_assoc] using cursor

 | translation ds=>
   have actual:s.natHeap T=some 3:=by simpa [Item.record,UniformFixedNetworkYRecordMachine.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A T E Buf X B n 3 x s h yes (Or.inr (Or.inl rfl)) actual hs code
   let e:=selected 3 336 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩:=Y.execution q w A Buf X T B n x ds f ce rfl
    (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
    (by simp [ce,e,selected,setPC,writeNat,next,h.buffer]) (by simp [ce,e,selected,setPC,writeNat,next,h.table])
    bank data cb (by omega) fresh extent tableCapacity bufferEnd width
   have placed:=UniformBoundedAssembly.boundedExecution_placed y_code (by rw [UniformFixedNetworkYRecordMachine.program_length];omega) (by omega) run
   have entry:UniformAssembly.placed 336 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have full:Frame q w A (R*2^(q*w)) Buf X s child:=((selected_frame q w _ _ Buf X 3 336 s).pc 0).trans (Frame.y cf)
   refine ⟨child,?_,output,cursor,full,full.constants ha extent con⟩
   convert selection.trans placed using 1
   · norm_num [Item.cost];omega
   · rfl


def KeptHeader (r:ℕ) : Prop := r=3300∨r=3301∨r=3310∨r=3311∨r=3312∨r=3314∨r=3315∨r=3364∨r=3389
lemma kept_unchanged (r:ℕ) (hr:KeptHeader r) : ¬Changed r := by
 unfold KeptHeader at hr
 rcases hr with h|h|h|h|h|h|h|h|h <;> subst r <;>
 norm_num [Changed,S.ScalarChanged,P.FullChanged,UniformFixedNetworkPaddingChildMachine.Changed,UniformBinaryTensorCMachine.Changed,
  E.FullChanged,UniformFixedNetworkExchangeRecordMachine.Changed,Y.FullChanged,UniformFixedNetworkYRecordMachine.Changed,
  UniformPreparedYTranslationMachine.Changed,UniformXorTranslationMachine.Changed]
lemma round_execution {R:ℕ} (q w A T E Buf X B n:ℕ) (x:Fin n→ℂ) (item:Item R w)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E Buf X s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:535≤B) (tableEnd:T+item.length q w≤B) (width:w+1≤B)
 (extent:A+R*2^(q*w)≤Buf) (bufferEnd:Buf+2^(q*w)≤B) (fresh:T+item.length q w≤X) (tableCapacity:X+2^q*2^q≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 Header A (T+item.length q w) E Buf X u ∧ Frame q w A (R*2^(q*w)) Buf X s u ∧ UniformBinaryCStageMachine.Constants u := by
 obtain ⟨child,run,out,cursor,frame,cc⟩:=branch_execution q w A T E Buf X B n x item f s h yes bank data con ha hr hs code tableEnd width extent bufferEnd fresh tableCapacity
 let u:=setPC child 5
 have ub:=changePC_bound B (setPC child 533) 5 run.final_bound (by omega)
 have jump:BoundedRuns program n x B (setPC child 533) 1 u:=.next run.final_bound
  (by simp [step,setPC,jump_at,u]) (.refl ub)
 have keep (r:ℕ) (hr:KeptHeader r) : u.natReg r=s.natReg r:=frame.natReg r (kept_unchanged r hr)
 have result:Header A (T+item.length q w) E Buf X u:=by
  constructor
  · rfl
  · rw [keep 3300 (by unfold KeptHeader;omega)];exact h.base
  · exact cursor
  · rw [keep 3301 (by unfold KeptHeader;omega)];exact h.endptr
  · rw [keep 3310 (by unfold KeptHeader;omega)];exact h.one
  · rw [keep 3311 (by unfold KeptHeader;omega)];exact h.five
  · rw [keep 3312 (by unfold KeptHeader;omega)];exact h.zero
  · rw [keep 3314 (by unfold KeptHeader;omega)];exact h.four
  · rw [keep 3315 (by unfold KeptHeader;omega)];exact h.three
  · rw [keep 3364 (by unfold KeptHeader;omega)];exact h.buffer
  · rw [keep 3389 (by unfold KeptHeader;omega)];exact h.table
 refine ⟨u,?_,out,result,frame.pc 5,cc⟩
 convert run.trans jump using 1
 cases item <;> simp [Item.cost]

lemma printed_transport {R q w X T:ℕ} {items:List (Item R w)} {s u:State}
 (bank:PrintedRecords T (items.map (Item.record q w)) s)
 (endbound:T+size q w items≤X) (frame:UniformXorTableMachine.Outside q X s.natHeap u) :
 PrintedRecords T (items.map (Item.record q w)) u := by
 induction items generalizing T with
 | nil=>trivial
 | cons item items ih=>
  refine ⟨?_,?_⟩
  · intro j hj
    have jb : j < item.length q w := hj
    rw [frame (T+j) (Or.inl (by simp only [size_cons] at endbound;omega))]
    exact bank.1 j hj
  · apply ih bank.2
    simp only [size_cons] at endbound
    change T+item.length q w+size q w items≤X
    omega

/-- Actual mixed records: no supplied handler or next state, and the XOR
producer's fresh Nat footprint is disjoint from the entire printed tape. -/
theorem loop_execution {R:ℕ} (q w A Buf X B n:ℕ) (x:Fin n→ℂ) (items:List (Item R w))
 (ha:3≤A) (hr:0<R) (width:w+1≤B) (code:535≤B) (extent:A+R*2^(q*w)≤Buf)
 (bufferEnd:Buf+2^(q*w)≤B) (tableCapacity:X+2^q*2^q≤B) :
 ∀T s (f:Fin R→Fin (2^(q*w))→Scalar),Header A T (T+size q w items) Buf X s→
 PrintedRecords T (items.map (Item.record q w)) s→UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s→
 UniformBinaryCStageMachine.Constants s→WordBound B s→T+size q w items≤X→∃u,
 BoundedExecution program n x B s (cost q w items+2) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+size q w items ∧ Frame q w A (R*2^(q*w)) Buf X s u ∧ UniformBinaryCStageMachine.Constants u := by
 induction items with
 | nil=>
  intro T s f h bank data con hs endbound
  let u:=setPC s 534
  have ub:=changePC_bound B s 534 hs (by omega)
  refine ⟨u,?_,data,?_,(Frame.refl q w _ _ Buf X s).pc 534,con⟩
  · change BoundedExecution program n x B s 2 u
    exact .next hs (by simp [step,h.pc,branch_at,h.cursor,h.endptr,u,setPC,size]) (.halt ub (by simp [step,u,setPC,halt_at]))
  · simpa [u,setPC,size] using h.cursor
 | cons item items ih=>
  intro T s f h bank data con hs endbound
  have yes:T<T+size q w (item::items):=by have positive:=Item.length_pos q w item;simp only [size_cons];omega
  have fresh:T+item.length q w≤X:=by simp only [size_cons] at endbound;omega
  have tableEnd:T+item.length q w≤B:=fresh.trans ((Nat.le_add_right X (2^q*2^q)).trans tableCapacity)
  obtain ⟨mid,round,out,head,frame,constants⟩:=round_execution q w A T (T+size q w (item::items)) Buf X B n x item f s h yes
   bank.1 data con ha hr hs code tableEnd width extent bufferEnd fresh tableCapacity
  have newHead:Header A (T+item.length q w) (T+item.length q w+size q w items) Buf X mid:=by
   convert head using 1
   simp only [size_cons];omega
  have tail:PrintedRecords (T+item.length q w) (items.map (Item.record q w)) mid:=by
   apply printed_transport (q:=q) (X:=X) bank.2
   · simp only [size_cons] at endbound;change T+item.length q w+size q w items≤X;omega
   · exact frame.natHeap
  obtain ⟨u,last,result,cursor,rest,cu⟩:=ih (T+item.length q w) mid (item.action q w f) newHead tail out constants round.final_bound
   (by simp only [size_cons] at endbound;omega)
  refine ⟨u,?_,result,?_,frame.trans rest,cu⟩
  · convert round.executes last using 1
    simp only [cost,List.map_cons,List.sum_cons];omega
  · simp only [size_cons] at *;omega

def FullChanged (r:ℕ) : Prop := Changed r∨(3310≤r∧r<3316)
structure FullFrame (q w A W Buf X:ℕ) (s u:State) : Prop where
 natHeap:UniformXorTableMachine.Outside q X s.natHeap u
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬FullChanged r→u.natReg r=s.natReg r
 scalarReg:∀r,115≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,(z<A∨A+W≤z)→(z<Buf∨Buf+2^(q*w)≤z)→u.scalarHeap z=s.scalarHeap z
lemma full_boot (q w A W Buf X:ℕ) (s:State) : FullFrame q w A W Buf X s (applyBlock boot s) := by
 refine ⟨fun _ _=>rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _ _=>rfl⟩
 intro r h;unfold FullChanged at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma FullFrame.child {q w A W Buf X:ℕ} {s u t:State} (f:FullFrame q w A W Buf X s u) (g:Frame q w A W Buf X u t) : FullFrame q w A W Buf X s t :=
 ⟨fun z h=>(g.natHeap z h).trans (f.natHeap z h),g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r (fun j=>h (Or.inl j))).trans (f.natReg r h),
 fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),fun z h j=>(g.scalarHeap z h j).trans (f.scalarHeap z h j)⟩
/-- One fixed535 program executes arbitrary chronological scalar, Y, exchange
and padding records. Residual and global layout opcodes still have the guard;
this theorem does not supply the missing recursive saving-network execution. -/
theorem execution {R:ℕ} (q w A T Buf X B n:ℕ) (x:Fin n→ℂ) (items:List (Item R w))
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (pc:s.pc=0) (base:s.natReg 3300=A)
 (ptr:s.natReg 2850=T) (endptr:s.natReg 3301=T+size q w items)
 (buffer:s.natReg 3364=Buf) (table:s.natReg 3389=X)
 (bank:PrintedRecords T (items.map (Item.record q w)) s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R) (width:w+1≤B)
 (hs:WordBound B s) (code:535≤B) (extent:A+R*2^(q*w)≤Buf) (bufferEnd:Buf+2^(q*w)≤B)
 (fresh:T+size q w items≤X) (tableCapacity:X+2^q*2^q≤B) : ∃u,
 BoundedExecution program n x B s (cost q w items+7) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+size q w items ∧ FullFrame q w A (R*2^(q*w)) Buf X s u ∧ UniformBinaryCStageMachine.Constants u := by
 have safe:readable boot s∧peak boot s≤B:=by simp [boot,readable,peak,Op.readable,Op.peak];omega
 have run:=block_runs boot program 0 n B x s boot_code pc hs (by change 5≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have h:Header A T (T+size q w items) Buf X ready:=by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc,base,ptr,endptr,buffer,table]
 obtain ⟨u,last,result,cursor,frame,cu⟩:=loop_execution q w A Buf X B n x items ha hr width code extent bufferEnd tableCapacity T ready f h
  (UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport bank (fun _ _=>rfl)) data con run.final_bound fresh
 refine ⟨u,?_,result,cursor,(full_boot q w _ _ Buf X s).child frame,cu⟩
 convert run.executes last using 1
 change cost q w items+7=5+(cost q w items+2);omega
end
end ExactFourierCircuits.UniformFixedNetworkYRecordLoopMachine
