import UniformFixedNetworkExchangeRecordMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkRecordLoopMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords)
namespace S
export UniformFixedNetworkChildDispatchMachine (scalarProgram shearRecord scalar_execution ScalarFrame ScalarChanged)
end S
namespace P
export UniformFixedNetworkPaddingChildMachine (dispatchProgram record dispatch_execution FullFrame FullChanged values)
end P
namespace E
export UniformFixedNetworkExchangeRecordMachine (Pair record execution FullFrame FullChanged actions)
end E

/-- Three implemented record kinds. Other opcodes retain an explicit failure
branch; this is not yet the complete fixed saving-network interpreter. -/
inductive Item (R:ℕ) where
 | scalar (d source:Fin R) (distinct:d≠source) (code:Fin 5)
 | padding (first count:ℕ) (capacity:first+count≤R)
 | exchange (pairs:List (E.Pair R))
def Item.record {R:ℕ} (q w:ℕ) : Item R→Record
 | .scalar d source _ k=>S.shearRecord q w d source k
 | .padding first count _=>P.record q w first count
 | .exchange pairs=>E.record q w pairs
def Item.length {R:ℕ} (q w:ℕ) (item:Item R) := (item.record q w).data.length
lemma Item.length_pos {R:ℕ} (q w:ℕ) (item:Item R) : 8 ≤ item.length q w := by
 cases item <;> simp [Item.length,Item.record,
   UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkChildDispatchMachine.shearRecord,
   UniformFixedNetworkScheduleMachine.Record.data_length]
def size {R:ℕ} (q w:ℕ) (items:List (Item R)) := (items.map (Item.length q w)).sum
lemma size_cons {R:ℕ} (q w:ℕ) (item:Item R) (items:List (Item R)) :
 size q w (item::items)=item.length q w+size q w items := rfl

def boot : List Op := [.literal 3310 1,.literal 3311 5,.literal 3312 0,.literal 3314 4]
def control : Program := boot.map Op.code++
 [.branchLT 2850 3301 5 334,.loadNat 3313 2850,
 .branchLT 3313 3310 12 7,.branchLT 3310 3313 8 13,
 .branchLT 3313 3314 12 9,.branchLT 3314 3313 10 235,
 .branchLT 3313 3311 12 11,.branchLT 3311 3313 12 119,
 .natBinary .div 3312 3312 3312]
def program : Program := control++S.scalarProgram.map (relocate 13 333)++
 P.dispatchProgram.map (relocate 119 333)++UniformFixedNetworkExchangeRecordMachine.program.map (relocate 235 333)++[.jump 4,.halt]
lemma control_length : control.length=13 := rfl
lemma program_length : program.length=335 := by
 simp only [program,List.length_append,List.length_map,control_length,
   UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
   UniformFixedNetworkPaddingChildMachine.dispatchProgram_length,
   UniformFixedNetworkExchangeRecordMachine.program_length]
 rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma scalar_code : CodeAt S.scalarProgram program 13 333 := by intro i hi;change i<106 at hi;interval_cases i <;> rfl
lemma padding_code : CodeAt P.dispatchProgram program 119 333 := by intro i hi;change i<116 at hi;interval_cases i <;> rfl
lemma exchange_code : CodeAt UniformFixedNetworkExchangeRecordMachine.program program 235 333 := by intro i hi;change i<98 at hi;interval_cases i <;> rfl
lemma branch_at : program[4]?=some (.branchLT 2850 3301 5 334) := rfl
lemma read_at : program[5]?=some (.loadNat 3313 2850) := rfl
lemma lower_at : program[6]?=some (.branchLT 3313 3310 12 7) := rfl
lemma one_at : program[7]?=some (.branchLT 3310 3313 8 13) := rfl
lemma lowerfour_at : program[8]?=some (.branchLT 3313 3314 12 9) := rfl
lemma four_at : program[9]?=some (.branchLT 3314 3313 10 235) := rfl
lemma upper_at : program[10]?=some (.branchLT 3313 3311 12 11) := rfl
lemma five_at : program[11]?=some (.branchLT 3311 3313 12 119) := rfl
lemma guard_at : program[12]?=some (.natBinary .div 3312 3312 3312) := rfl
lemma prefix_length : (control++S.scalarProgram.map (relocate 13 333)++P.dispatchProgram.map (relocate 119 333)++UniformFixedNetworkExchangeRecordMachine.program.map (relocate 235 333)).length=333 := by
 simp only [List.length_append,List.length_map,control_length,
   UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
   UniformFixedNetworkPaddingChildMachine.dispatchProgram_length,
   UniformFixedNetworkExchangeRecordMachine.program_length]
lemma jump_at : program[333]?=some (.jump 4) := by
 unfold program
 rw [List.getElem?_append_right (by simpa only [prefix_length] using (by decide:333≤333)),prefix_length]
 rfl
lemma halt_at : program[334]?=some .halt := by
 unfold program
 rw [List.getElem?_append_right (by simpa only [prefix_length] using (by decide:333≤334)),prefix_length]
 rfl

noncomputable section
def Item.action {R:ℕ} (q w:ℕ) (f:Fin R→Fin (2^(q*w))→Scalar) : Item R→Fin R→Fin (2^(q*w))→Scalar
 | .scalar d source _ k=>UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode k) f
 | .padding first count _=>P.values (q*w) first count f
 | .exchange pairs=>E.actions pairs f
def Item.cost {R:ℕ} (q w:ℕ) : Item R→ℕ
 | .scalar _ _ _ k=>10*2^(q*w)+4*(q*w)+k.val+67
 | .padding _ count _=>count*((q*w)*(25*2^(q*w-1)+11)+15)+4*(q*w)+59
 | .exchange pairs=>(10*2^(q*w)+21)*pairs.length+4*(q*w)+57
def actions {R:ℕ} (q w:ℕ) (items:List (Item R)) (f:Fin R→Fin (2^(q*w))→Scalar) :=
 items.foldl (fun a item=>item.action q w a) f
def cost {R:ℕ} (q w:ℕ) (items:List (Item R)) := (items.map (Item.cost q w)).sum
structure Header (A T E:ℕ) (s:State) : Prop where
 pc:s.pc=4
 base:s.natReg 3300=A
 cursor:s.natReg 2850=T
 endptr:s.natReg 3301=E
 one:s.natReg 3310=1
 five:s.natReg 3311=5
 zero:s.natReg 3312=0
 four:s.natReg 3314=4

def Changed (r:ℕ) : Prop := S.ScalarChanged r∨P.FullChanged r∨UniformFixedNetworkExchangeRecordMachine.FullChanged r∨(3310≤r∧r<3315)
structure Frame (A V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg:∀r,114≤r→u.scalarReg r=s.scalarReg r
 scalarHeap:∀z,z<A∨A+V≤z→u.scalarHeap z=s.scalarHeap z
lemma Frame.refl (A V:ℕ) (s:State) : Frame A V s s := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.pc {A V:ℕ} {s u:State} (f:Frame A V s u) (p:ℕ) : Frame A V s (setPC u p) :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,f.scalarReg,f.scalarHeap⟩
lemma Frame.trans {A V:ℕ} {s u t:State} (f:Frame A V s u) (g:Frame A V u t) : Frame A V s t :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun r h=>(g.natReg r h).trans (f.natReg r h),fun r h=>(g.scalarReg r h).trans (f.scalarReg r h),
 fun z h=>(g.scalarHeap z h).trans (f.scalarHeap z h)⟩
lemma Frame.scalar {A V D L:ℕ} {s u:State} (lo:A≤D) (hi:D+L≤A+V) (f:S.ScalarFrame D L s u) : Frame A V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,?_,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;apply f.scalarReg <;> omega
 · intro z h;apply f.scalarHeap;omega
lemma Frame.padding {A V D L:ℕ} {s u:State} (lo:A≤D) (hi:D+L≤A+V) (f:P.FullFrame D L s u) : Frame A V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,?_,?_⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;apply f.scalarReg;omega
 · intro z h;apply f.scalarHeap;omega
lemma Frame.exchange {A V:ℕ} {s u:State} (f:E.FullFrame A V s u) : Frame A V s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,?_,f.scalarHeap⟩
 · intro r h;apply f.natReg;unfold Changed at h;tauto
 · intro r h;exact f.scalarReg r (Or.inr h)
lemma Frame.constants {A V:ℕ} {s u:State} (ha:3≤A) (f:Frame A V s u)
 (con:UniformBinaryCStageMachine.Constants s) : UniformBinaryCStageMachine.Constants u := by
 unfold UniformBinaryCStageMachine.Constants
 rw [f.scalarHeap 1 (by omega),f.scalarHeap 2 (by omega)];exact con
lemma frame_boot (A V:ℕ) (s:State) : Frame A V s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
def selected (tag entry:ℕ) (s:State) := setPC (writeNat (setPC s 5) 3313 tag) entry
lemma selected_frame (A V tag entry:ℕ) (s:State) : Frame A V s (selected tag entry s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [selected,setPC,writeNat,next]

/-- Every supported branch reads the real opcode from the physical table. -/
lemma select_runs (A _V T E B n tag:ℕ) (x:Fin n→ℂ) (s:State) (h:Header A T E s)
 (yes:T<E) (supported:tag=1∨tag=4∨tag=5) (head:s.natHeap T=some tag) (hs:WordBound B s) (code:335≤B) :
 BoundedRuns program n x B s (if tag=1 then 4 else if tag=4 then 6 else 8)
 (selected tag (if tag=1 then 13 else if tag=4 then 235 else 119) s) := by
 let e:=setPC s 5
 have eb:=changePC_bound B s 5 hs (by omega)
 have first:step program n x s=.running e:=by simp [step,h.pc,branch_at,h.cursor,h.endptr,yes,e,setPC]
 rcases supported with rfl|rfl|rfl
 · let r:=writeNat e 3313 1
   have rb:=writeNat_bound B e 3313 1 eb (by change 6≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤335) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 7 (by omega)) ?_ (.refl (bp 13 (by omega))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,lower_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,one_at,h.one,selected]
 · let r:=writeNat e 3313 4
   have rb:=writeNat_bound B e 3313 4 eb (by change 6≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤335) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 7 (by omega)) ?_ (.next (bp 8 (by omega)) ?_ (.next (bp 9 (by omega)) ?_ (.refl (bp 235 (by omega))))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,lower_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,one_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,lowerfour_at,h.four]
   · simp [step,r,e,setPC,writeNat,next,four_at,h.four,selected]
 · let r:=writeNat e 3313 5
   have rb:=writeNat_bound B e 3313 5 eb (by change 6≤B;omega) (by omega)
   have bp (p:ℕ) (hp:p≤335) : WordBound B (setPC r p):=changePC_bound B r p rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next (bp 7 (by omega)) ?_ (.next (bp 8 (by omega)) ?_ (.next (bp 9 (by omega)) ?_ (.next (bp 10 (by omega)) ?_ (.next (bp 11 (by omega)) ?_ (.refl (bp 119 (by omega))))))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,lower_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,one_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,lowerfour_at,h.four]
   · simp [step,r,e,setPC,writeNat,next,four_at,h.four]
   · simp [step,r,e,setPC,writeNat,next,upper_at,h.five]
   · simp [step,r,e,setPC,writeNat,next,five_at,h.five,selected]

def KeptHeader (r:ℕ) : Prop := r=3300∨r=3301∨r=3310∨r=3311∨r=3312∨r=3314
lemma selected_kept (tag entry:ℕ) (s:State) (r:ℕ) (hr:KeptHeader r) :
 (selected tag entry s).natReg r=s.natReg r := by
 unfold KeptHeader at hr
 rcases hr with h|h|h|h|h|h <;> subst r <;> simp [selected,setPC,writeNat,next]

lemma branch_execution {R:ℕ} (q w A T E B n:ℕ) (x:Fin n→ℂ) (item:Item R)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:335≤B) (tableEnd:T+item.length q w≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w-1) (setPC u 333) ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 u.natReg 2850=T+item.length q w ∧ Frame A (R*2^(q*w)) s u ∧
 (∀r,KeptHeader r→u.natReg r=s.natReg r) ∧ UniformBinaryCStageMachine.Constants u := by
 cases item with
 | scalar d source ne k=>
   have actual:s.natHeap T=some 1:=by simpa [Item.record,S.shearRecord,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A (R*2^(q*w)) T E B n 1 x s h yes (Or.inl rfl) actual hs code
   let e:=selected 1 13 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩:=S.scalar_execution q w A T B n x d source ne k f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data cb (by omega) (by simpa [Item.length,Item.record,UniformFixedNetworkChildDispatchMachine.shearRecord,UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkScheduleMachine.Record.data_length] using tableEnd) width extent
   have placed:=UniformBoundedAssembly.boundedExecution_placed scalar_code (by change 119≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 13 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤UniformFixedNetworkShearChildMachine.roleBase A (2^(q*w)) d.val:=by unfold UniformFixedNetworkShearChildMachine.roleBase;omega
   have hi:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*w)) d
   have full:Frame A (R*2^(q*w)) s child:=((selected_frame _ _ 1 13 s).pc 0).trans (Frame.scalar lo hi cf)
   refine ⟨child,?_,output,cursor,full,?_,full.constants ha con⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · intro r kept
     rw [cf.natReg r (by unfold KeptHeader at kept;rcases kept with h|h|h|h|h|h <;> subst r <;> norm_num [S.ScalarChanged])]
     exact selected_kept 1 13 s r kept
 | padding first count capacity=>
   have actual:s.natHeap T=some 5:=by simpa [Item.record,P.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A (R*2^(q*w)) T E B n 5 x s h yes (Or.inr (Or.inr rfl)) actual hs code
   let e:=selected 5 119 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf,cc⟩:=P.dispatch_execution q w A T first count B n x f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data con capacity ha hr cb (by omega) (by simpa [Item.length,Item.record,UniformFixedNetworkChildDispatchMachine.shearRecord,UniformFixedNetworkPaddingChildMachine.record,UniformFixedNetworkScheduleMachine.Record.data_length] using tableEnd) width extent
   have placed:=UniformBoundedAssembly.boundedExecution_placed padding_code (by change 235≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 119 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤A+first*2^(q*w):=by omega
   have hi:A+first*2^(q*w)+count*2^(q*w)≤A+R*2^(q*w):=by
     have hp:=Nat.mul_le_mul_right (2^(q*w)) capacity
     rw [Nat.add_mul] at hp;omega
   have full:Frame A (R*2^(q*w)) s child:=((selected_frame _ _ 5 119 s).pc 0).trans (Frame.padding lo hi cf)
   refine ⟨child,?_,output,cursor,full,?_,cc⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · intro r kept
     rw [cf.natReg r (by unfold KeptHeader at kept;rcases kept with h|h|h|h|h|h <;> subst r <;>
       norm_num [P.FullChanged,UniformFixedNetworkPaddingChildMachine.Changed,UniformBinaryTensorCMachine.Changed])]
     exact selected_kept 5 119 s r kept
 | exchange pairs=>
   have actual:s.natHeap T=some 4:=by simpa [Item.record,UniformFixedNetworkExchangeRecordMachine.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A (R*2^(q*w)) T E B n 4 x s h yes (Or.inr (Or.inl rfl)) actual hs code
   let e:=selected 4 235 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩ :=UniformFixedNetworkExchangeRecordMachine.execution q w A T B n x pairs f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data hr cb (by omega) extent
     (by simpa [Item.length,Item.record,UniformFixedNetworkExchangeRecordMachine.record_length,Nat.add_assoc] using tableEnd) width
   have placed:=UniformBoundedAssembly.boundedExecution_placed exchange_code (by change 333≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 235 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have full:Frame A (R*2^(q*w)) s child:=((selected_frame _ _ 4 235 s).pc 0).trans (Frame.exchange cf)
   refine ⟨child,?_,output,?_,full,?_,full.constants ha con⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · simpa [Item.length,Item.record,UniformFixedNetworkExchangeRecordMachine.record_length,Nat.add_assoc] using cursor
   · intro r kept
     rw [cf.natReg r (by unfold KeptHeader at kept;rcases kept with h|h|h|h|h|h <;> subst r <;>
       norm_num [UniformFixedNetworkExchangeRecordMachine.FullChanged,UniformFixedNetworkExchangeRecordMachine.Changed])]
     exact selected_kept 4 235 s r kept

lemma round_execution {R:ℕ} (q w A T E B n:ℕ) (x:Fin n→ℂ) (item:Item R)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:335≤B) (tableEnd:T+item.length q w≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 Header A (T+item.length q w) E u ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 obtain ⟨child,run,out,cursor,frame,kept,cc⟩:=branch_execution q w A T E B n x item f s h yes bank data con ha hr hs code tableEnd width extent
 let u:=setPC child 4
 have ub:=changePC_bound B _ 4 run.final_bound (by omega)
 have jump:BoundedRuns program n x B (setPC child 333) 1 u:=.next run.final_bound
   (by simp [step,setPC,jump_at,u]) (.refl ub)
 have result:Header A (T+item.length q w) E u:=⟨rfl,(kept 3300 (by exact Or.inl rfl)).trans h.base,cursor,
   (kept 3301 (by exact Or.inr (Or.inl rfl))).trans h.endptr,
   (kept 3310 (by exact Or.inr (Or.inr (Or.inl rfl)))).trans h.one,
   (kept 3311 (by exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h.five,
   (kept 3312 (by exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans h.zero,
   (kept 3314 (by exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans h.four⟩
 refine ⟨u,?_,out,result,frame.pc 4,cc⟩
 convert run.trans jump using 1
 cases item <;> simp [Item.cost]


/-- Iterate the real records and execute each implemented child. The printed
Natheap is retained; no action handler, decoded header or next state is supplied. -/
theorem loop_execution {R:ℕ} (q w A B n:ℕ) (x:Fin n→ℂ) (items:List (Item R))
 (ha:3≤A) (hr:0<R) (width:w+1≤B) (code:335≤B) (extent:A+R*2^(q*w)≤B) :
 ∀T s (f:Fin R→Fin (2^(q*w))→Scalar),Header A T (T+size q w items) s→
 PrintedRecords T (items.map (Item.record q w)) s→UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s→
 UniformBinaryCStageMachine.Constants s→WordBound B s→T+size q w items≤B→∃u,
 BoundedExecution program n x B s (cost q w items+2) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+size q w items ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 induction items with
 | nil=>
   intro T s f h bank data con hs endbound
   let u:=setPC s 334
   have ub:=changePC_bound B s 334 hs (by omega)
   refine ⟨u,?_,data,?_,(Frame.refl _ _ s).pc 334,con⟩
   · change BoundedExecution program n x B s 2 u
     exact .next hs (by simp [step,h.pc,branch_at,h.cursor,h.endptr,u,setPC,size])
       (.halt ub (by simp [step,u,setPC,halt_at]))
   · simpa [u,setPC,size] using h.cursor
 | cons item items ih=>
   intro T s f h bank data con hs endbound
   have yes:T<T+size q w (item::items):=by
     have positive:=Item.length_pos q w item
     simp only [size_cons];omega
   have tableEnd:T+item.length q w≤B:=by simp only [size_cons] at endbound;omega
   obtain ⟨mid,round,out,head,frame,constants⟩:=round_execution q w A T (T+size q w (item::items)) B n x item f s h yes
     bank.1 data con ha hr hs code tableEnd width extent
   have newHead:Header A (T+item.length q w) (T+item.length q w+size q w items) mid:=by
     convert head using 1
     simp only [size_cons]
     omega
   have tail:PrintedRecords (T+item.length q w) (items.map (Item.record q w)) mid:=by
     have source:=bank.2
     change PrintedRecords (T+item.length q w) (items.map (Item.record q w)) s at source
     exact UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport source (fun z _=>congrFun frame.natHeap z)
   obtain ⟨u,last,result,cursor,rest,cu⟩:=ih (T+item.length q w) mid (item.action q w f) newHead tail out constants round.final_bound
     (by simp only [size_cons] at endbound;omega)
   refine ⟨u,?_,result,?_,frame.trans rest,cu⟩
   · convert round.executes last using 1
     simp only [cost,List.map_cons,List.sum_cons];omega
   · simp only [size_cons] at *;omega

/-- One fixed335 literal program initializes its control constants, reads
mixed scalar/exchange/padding records and runs every actual child continuously. Other
opcodes have the explicit guard; the full saving-network opcode set is open. -/
theorem execution {R:ℕ} (q w A T B n:ℕ) (x:Fin n→ℂ) (items:List (Item R))
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (pc:s.pc=0) (base:s.natReg 3300=A)
 (ptr:s.natReg 2850=T) (endptr:s.natReg 3301=T+size q w items)
 (bank:PrintedRecords T (items.map (Item.record q w)) s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R) (width:w+1≤B)
 (hs:WordBound B s) (code:335≤B) (extent:A+R*2^(q*w)≤B) (tableEnd:T+size q w items≤B) : ∃u,
 BoundedExecution program n x B s (cost q w items+6) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+size q w items ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 have safe:readable boot s ∧ peak boot s≤B:=by simp [boot,readable,peak,Op.readable,Op.peak];omega
 have run:=block_runs boot program 0 n B x s boot_code pc hs (by change 4≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have h:Header A T (T+size q w items) ready:=by
   constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc,base,ptr,endptr]
 obtain ⟨u,last,result,cursor,frame,cu⟩:=loop_execution q w A B n x items ha hr width code extent T ready f h
   (UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport bank (fun _ _=>rfl)) data con run.final_bound tableEnd
 refine ⟨u,?_,result,cursor,(frame_boot _ _ s).trans frame,cu⟩
 convert run.executes last using 1
 change cost q w items+6=4+(cost q w items+2);omega

end
end ExactFourierCircuits.UniformFixedNetworkRecordLoopMachine
