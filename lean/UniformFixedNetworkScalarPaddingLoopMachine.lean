import UniformFixedNetworkPaddingChildMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkScalarPaddingLoopMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformFixedNetworkScheduleMachine (Record Printed PrintedRecords)
namespace S
export UniformFixedNetworkChildDispatchMachine (scalarProgram shearRecord scalar_execution ScalarFrame ScalarChanged)
end S
namespace P
export UniformFixedNetworkPaddingChildMachine (dispatchProgram record dispatch_execution FullFrame FullChanged values)
end P

/-- Two implemented record kinds. Other opcodes retain an explicit failure
branch; this is not yet the complete fixed saving-network interpreter. -/
inductive Item (R:ℕ) where
 | scalar (d source:Fin R) (distinct:d≠source) (code:Fin 5)
 | padding (first count:ℕ) (capacity:first+count≤R)
def Item.record {R:ℕ} (q w:ℕ) : Item R→Record
 | .scalar d source _ k=>S.shearRecord q w d source k
 | .padding first count _=>P.record q w first count
lemma Item.record_length {R:ℕ} (q w:ℕ) (item:Item R) : (item.record q w).data.length=8 := by cases item <;> rfl

def boot : List Op := [.literal 3310 1,.literal 3311 5,.literal 3312 0]
def control : Program := boot.map Op.code++
 [.branchLT 2850 3301 4 233,.loadNat 3313 2850,
 .branchLT 3313 3310 9 6,.branchLT 3310 3313 7 10,
 .branchLT 3313 3311 9 8,.branchLT 3311 3313 9 116,
 .natBinary .div 3312 3312 3312]
def program : Program := control++S.scalarProgram.map (relocate 10 232)++
 P.dispatchProgram.map (relocate 116 232)++[.jump 3,.halt]
lemma control_length : control.length=10 := rfl
lemma program_length : program.length=234 := by
 simp only [program,List.length_append,List.length_map,control_length,
   UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
   UniformFixedNetworkPaddingChildMachine.dispatchProgram_length]
 rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma scalar_code : CodeAt S.scalarProgram program 10 232 := by intro i hi;change i<106 at hi;interval_cases i <;> rfl
lemma padding_code : CodeAt P.dispatchProgram program 116 232 := by intro i hi;change i<116 at hi;interval_cases i <;> rfl
lemma branch_at : program[3]?=some (.branchLT 2850 3301 4 233) := rfl
lemma read_at : program[4]?=some (.loadNat 3313 2850) := rfl
lemma lower_at : program[5]?=some (.branchLT 3313 3310 9 6) := rfl
lemma one_at : program[6]?=some (.branchLT 3310 3313 7 10) := rfl
lemma upper_at : program[7]?=some (.branchLT 3313 3311 9 8) := rfl
lemma five_at : program[8]?=some (.branchLT 3311 3313 9 116) := rfl
lemma guard_at : program[9]?=some (.natBinary .div 3312 3312 3312) := rfl
lemma jump_at : program[232]?=some (.jump 3) := by
 have len:(control++S.scalarProgram.map (relocate 10 232)++P.dispatchProgram.map (relocate 116 232)).length=232:=by
   simp only [List.length_append,List.length_map,control_length,
     UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
     UniformFixedNetworkPaddingChildMachine.dispatchProgram_length]
 unfold program
 rw [List.getElem?_append_right (by simpa only [len] using (by decide:232≤232)),len]
 rfl
lemma halt_at : program[233]?=some .halt := by
 have len:(control++S.scalarProgram.map (relocate 10 232)++P.dispatchProgram.map (relocate 116 232)).length=232:=by
   simp only [List.length_append,List.length_map,control_length,
     UniformFixedNetworkChildDispatchMachine.scalarProgram_length,
     UniformFixedNetworkPaddingChildMachine.dispatchProgram_length]
 unfold program
 rw [List.getElem?_append_right (by simpa only [len] using (by decide:232≤233)),len]
 rfl

noncomputable section
def Item.action {R:ℕ} (q w:ℕ) (f:Fin R→Fin (2^(q*w))→Scalar) : Item R→Fin R→Fin (2^(q*w))→Scalar
 | .scalar d source _ k=>UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode k) f
 | .padding first count _=>P.values (q*w) first count f
def Item.cost {R:ℕ} (q w:ℕ) : Item R→ℕ
 | .scalar _ _ _ k=>10*2^(q*w)+4*(q*w)+k.val+67
 | .padding _ count _=>count*((q*w)*(25*2^(q*w-1)+11)+15)+4*(q*w)+57
def actions {R:ℕ} (q w:ℕ) (items:List (Item R)) (f:Fin R→Fin (2^(q*w))→Scalar) :=
 items.foldl (fun a item=>item.action q w a) f
def cost {R:ℕ} (q w:ℕ) (items:List (Item R)) := (items.map (Item.cost q w)).sum
structure Header (A T E:ℕ) (s:State) : Prop where
 pc:s.pc=3
 base:s.natReg 3300=A
 cursor:s.natReg 2850=T
 endptr:s.natReg 3301=E
 one:s.natReg 3310=1
 five:s.natReg 3311=5
 zero:s.natReg 3312=0

def Changed (r:ℕ) : Prop := S.ScalarChanged r∨P.FullChanged r∨(3310≤r∧r<3314)
structure Frame (A V:ℕ) (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬Changed r→u.natReg r=s.natReg r
 scalarReg:∀r,105≤r→u.scalarReg r=s.scalarReg r
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
lemma Frame.constants {A V:ℕ} {s u:State} (ha:3≤A) (f:Frame A V s u)
 (con:UniformBinaryCStageMachine.Constants s) : UniformBinaryCStageMachine.Constants u := by
 unfold UniformBinaryCStageMachine.Constants
 rw [f.scalarHeap 1 (by omega),f.scalarHeap 2 (by omega)];exact con
lemma frame_boot (A V:ℕ) (s:State) : Frame A V s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
def selected (tag entry:ℕ) (s:State) := setPC (writeNat (setPC s 4) 3313 tag) entry
lemma selected_frame (A V tag entry:ℕ) (s:State) : Frame A V s (selected tag entry s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [selected,setPC,writeNat,next]

/-- Select actual opcode1/5 from a real Natheap read, with every branch charged. -/
lemma select_runs (A _V T E B n tag:ℕ) (x:Fin n→ℂ) (s:State) (h:Header A T E s)
 (yes:T<E) (supported:tag=1∨tag=5) (head:s.natHeap T=some tag) (hs:WordBound B s) (code:234≤B) :
 BoundedRuns program n x B s (if tag=1 then 4 else 6) (selected tag (if tag=1 then 10 else 116) s) := by
 let e:=setPC s 4
 have eb:=changePC_bound B s 4 hs (by omega)
 have first:step program n x s=.running e:=by simp [step,h.pc,branch_at,h.cursor,h.endptr,yes,e,setPC]
 rcases supported with rfl|rfl
 · let r:=writeNat e 3313 1
   have rb:=writeNat_bound B e 3313 1 eb (by change 5≤B;omega) (by omega)
   have b6:=changePC_bound B r 6 rb (by omega)
   have b10:=changePC_bound B r 10 rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next b6 ?_ (.refl b10))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,lower_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,one_at,h.one,selected]
 · let r:=writeNat e 3313 5
   have rb:=writeNat_bound B e 3313 5 eb (by change 5≤B;omega) (by omega)
   have b6:=changePC_bound B r 6 rb (by omega)
   have b7:=changePC_bound B r 7 rb (by omega)
   have b8:=changePC_bound B r 8 rb (by omega)
   have b116:=changePC_bound B r 116 rb (by omega)
   refine .next hs first (.next eb ?_ (.next rb ?_ (.next b6 ?_ (.next b7 ?_ (.next b8 ?_ (.refl b116))))))
   · simp [step,e,setPC,read_at,h.cursor,head]
   · simp [step,r,e,setPC,writeNat,next,lower_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,one_at,h.one]
   · simp [step,r,e,setPC,writeNat,next,upper_at,h.five]
   · simp [step,r,e,setPC,writeNat,next,five_at,h.five,selected]

def KeptHeader (r:ℕ) : Prop := r=3300∨r=3301∨r=3310∨r=3311∨r=3312
lemma selected_kept (tag entry:ℕ) (s:State) (r:ℕ) (hr:KeptHeader r) :
 (selected tag entry s).natReg r=s.natReg r := by
 unfold KeptHeader at hr
 rcases hr with h|h|h|h|h <;> subst r <;> simp [selected,setPC,writeNat,next]

lemma branch_execution {R:ℕ} (q w A T E B n:ℕ) (x:Fin n→ℂ) (item:Item R)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:234≤B) (tableEnd:T+8≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w-1) (setPC u 232) ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 u.natReg 2850=T+8 ∧ Frame A (R*2^(q*w)) s u ∧
 (∀r,KeptHeader r→u.natReg r=s.natReg r) ∧ UniformBinaryCStageMachine.Constants u := by
 cases item with
 | scalar d source ne k=>
   have actual:s.natHeap T=some 1:=by simpa [Item.record,S.shearRecord,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A (R*2^(q*w)) T E B n 1 x s h yes (Or.inl rfl) actual hs code
   let e:=selected 1 10 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf⟩:=S.scalar_execution q w A T B n x d source ne k f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data cb (by omega) tableEnd width extent
   have placed:=UniformBoundedAssembly.boundedExecution_placed scalar_code (by change 116≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 10 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤UniformFixedNetworkShearChildMachine.roleBase A (2^(q*w)) d.val:=by unfold UniformFixedNetworkShearChildMachine.roleBase;omega
   have hi:=UniformFixedNetworkShearChildMachine.role_bound A (2^(q*w)) d
   have full:Frame A (R*2^(q*w)) s child:=((selected_frame _ _ 1 10 s).pc 0).trans (Frame.scalar lo hi cf)
   refine ⟨child,?_,output,cursor,full,?_,full.constants ha con⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · intro r kept
     rw [cf.natReg r (by unfold KeptHeader at kept;rcases kept with h|h|h|h|h <;> subst r <;> norm_num [S.ScalarChanged])]
     exact selected_kept 1 10 s r kept
 | padding first count capacity=>
   have actual:s.natHeap T=some 5:=by simpa [Item.record,P.record,UniformFixedNetworkScheduleMachine.Record.header] using bank.header (0:Fin 8)
   have selection:=select_runs A (R*2^(q*w)) T E B n 5 x s h yes (Or.inr rfl) actual hs code
   let e:=selected 5 116 s
   let ce:=setPC e 0
   have cb:=changePC_bound B e 0 selection.final_bound (by omega)
   obtain ⟨child,run,output,cursor,cf,cc⟩:=P.dispatch_execution q w A T first count B n x f ce rfl
     (by simp [ce,e,selected,setPC,writeNat,next,h.cursor]) (by simp [ce,e,selected,setPC,writeNat,next,h.base])
     bank data con capacity ha hr cb (by omega) tableEnd width extent
   have placed:=UniformBoundedAssembly.boundedExecution_placed padding_code (by change 232≤B;omega) (by omega) run
   have entry:UniformAssembly.placed 116 ce=e:=by simp [UniformAssembly.placed,ce,e,selected,setPC,writeNat,next]
   rw [entry] at placed
   have lo:A≤A+first*2^(q*w):=by omega
   have hi:A+first*2^(q*w)+count*2^(q*w)≤A+R*2^(q*w):=by
     have hp:=Nat.mul_le_mul_right (2^(q*w)) capacity
     rw [Nat.add_mul] at hp;omega
   have full:Frame A (R*2^(q*w)) s child:=((selected_frame _ _ 5 116 s).pc 0).trans (Frame.padding lo hi cf)
   refine ⟨child,?_,output,cursor,full,?_,cc⟩
   · convert selection.trans placed using 1
     · norm_num [Item.cost];omega
     · rfl
   · intro r kept
     rw [cf.natReg r (by unfold KeptHeader at kept;rcases kept with h|h|h|h|h <;> subst r <;>
       norm_num [P.FullChanged,UniformFixedNetworkPaddingChildMachine.Changed,UniformBinaryTensorCMachine.Changed])]
     exact selected_kept 5 116 s r kept

lemma round_execution {R:ℕ} (q w A T E B n:ℕ) (x:Fin n→ℂ) (item:Item R)
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (h:Header A T E s) (yes:T<E)
 (bank:Printed T (item.record q w).data s) (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R)
 (hs:WordBound B s) (code:234≤B) (tableEnd:T+8≤B) (width:w+1≤B) (extent:A+R*2^(q*w)≤B) : ∃u,
 BoundedRuns program n x B s (item.cost q w) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (item.action q w f) u ∧
 Header A (T+8) E u ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 obtain ⟨child,run,out,cursor,frame,kept,cc⟩:=branch_execution q w A T E B n x item f s h yes bank data con ha hr hs code tableEnd width extent
 let u:=setPC child 3
 have ub:=changePC_bound B _ 3 run.final_bound (by omega)
 have jump:BoundedRuns program n x B (setPC child 232) 1 u:=.next run.final_bound
   (by simp [step,setPC,jump_at,u]) (.refl ub)
 have result:Header A (T+8) E u:=⟨rfl,(kept 3300 (by exact Or.inl rfl)).trans h.base,cursor,
   (kept 3301 (by exact Or.inr (Or.inl rfl))).trans h.endptr,
   (kept 3310 (by exact Or.inr (Or.inr (Or.inl rfl)))).trans h.one,
   (kept 3311 (by exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h.five,
   (kept 3312 (by exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans h.zero⟩
 refine ⟨u,?_,out,result,frame.pc 3,cc⟩
 convert run.trans jump using 1
 cases item <;> simp [Item.cost]


/-- Iterate the real records and execute each implemented child. The printed
Natheap is retained; no action handler, decoded header or next state is supplied. -/
theorem loop_execution {R:ℕ} (q w A B n:ℕ) (x:Fin n→ℂ) (items:List (Item R))
 (ha:3≤A) (hr:0<R) (width:w+1≤B) (code:234≤B) (extent:A+R*2^(q*w)≤B) :
 ∀T s (f:Fin R→Fin (2^(q*w))→Scalar),Header A T (T+8*items.length) s→
 PrintedRecords T (items.map (Item.record q w)) s→UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s→
 UniformBinaryCStageMachine.Constants s→WordBound B s→T+8*items.length≤B→∃u,
 BoundedExecution program n x B s (cost q w items+2) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+8*items.length ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 induction items with
 | nil=>
   intro T s f h bank data con hs endbound
   let u:=setPC s 233
   have ub:=changePC_bound B s 233 hs (by omega)
   refine ⟨u,?_,data,?_,(Frame.refl _ _ s).pc 233,con⟩
   · change BoundedExecution program n x B s 2 u
     exact .next hs (by simp [step,h.pc,branch_at,h.cursor,h.endptr,u,setPC])
       (.halt ub (by simp [step,u,setPC,halt_at]))
   · simpa [u,setPC] using h.cursor
 | cons item items ih=>
   intro T s f h bank data con hs endbound
   have yes:T<T+8*(item::items).length:=by simp only [List.length_cons];omega
   have tableEnd:T+8≤B:=by simp only [List.length_cons] at endbound;omega
   obtain ⟨mid,round,out,head,frame,constants⟩:=round_execution q w A T (T+8*(item::items).length) B n x item f s h yes
     bank.1 data con ha hr hs code tableEnd width extent
   have newHead:Header A (T+8) (T+8+8*items.length) mid:=by
     convert head using 1
     simp only [List.length_cons]
     omega
   have tail:PrintedRecords (T+8) (items.map (Item.record q w)) mid:=by
     have source:=bank.2
     rw [Item.record_length] at source
     exact UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport source (fun z _=>congrFun frame.natHeap z)
   obtain ⟨u,last,result,cursor,rest,cu⟩:=ih (T+8) mid (item.action q w f) newHead tail out constants round.final_bound
     (by simp only [List.length_cons] at endbound;omega)
   refine ⟨u,?_,result,?_,frame.trans rest,cu⟩
   · convert round.executes last using 1
     simp only [cost,List.map_cons,List.sum_cons];omega
   · simp only [List.length_cons] at *;omega

/-- One fixed234 literal program initializes its control constants, reads
mixed scalar/padding records and runs every actual child continuously. Other
opcodes have the explicit guard; the full saving-network opcode set is open. -/
theorem execution {R:ℕ} (q w A T B n:ℕ) (x:Fin n→ℂ) (items:List (Item R))
 (f:Fin R→Fin (2^(q*w))→Scalar) (s:State) (pc:s.pc=0) (base:s.natReg 3300=A)
 (ptr:s.natReg 2850=T) (endptr:s.natReg 3301=T+8*items.length)
 (bank:PrintedRecords T (items.map (Item.record q w)) s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) f s)
 (con:UniformBinaryCStageMachine.Constants s) (ha:3≤A) (hr:0<R) (width:w+1≤B)
 (hs:WordBound B s) (code:234≤B) (extent:A+R*2^(q*w)≤B) (tableEnd:T+8*items.length≤B) : ∃u,
 BoundedExecution program n x B s (cost q w items+5) u ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(q*w)) (actions q w items f) u ∧
 u.natReg 2850=T+8*items.length ∧ Frame A (R*2^(q*w)) s u ∧ UniformBinaryCStageMachine.Constants u := by
 have safe:readable boot s ∧ peak boot s≤B:=by simp [boot,readable,peak,Op.readable,Op.peak];omega
 have run:=block_runs boot program 0 n B x s boot_code pc hs (by change 3≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have h:Header A T (T+8*items.length) ready:=by
   constructor <;> simp [ready,boot,applyBlock,Op.apply,writeNat,next,pc,base,ptr,endptr]
 obtain ⟨u,last,result,cursor,frame,cu⟩:=loop_execution q w A B n x items ha hr width code extent T ready f h
   (UniformFixedNetworkLiteralDecoderMachine.PrintedRecords.transport bank (fun _ _=>rfl)) data con run.final_bound tableEnd
 refine ⟨u,?_,result,cursor,(frame_boot _ _ s).trans frame,cu⟩
 convert run.executes last using 1
 change cost q w items+5=3+(cost q w items+2);omega

end
end ExactFourierCircuits.UniformFixedNetworkScalarPaddingLoopMachine
