import UniformTensorFiberCopyMachine
import UniformBoundedAssembly
import UniformRadixInstructionMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSelectedAxisFiberPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformInitialPreparation (ell len copyBase protectedView)
open UniformPermutationInversePreparation (Metadata)
open UniformCRTTraversalCycle (place)
namespace A
abbrev Op := UniformRadixInstructionMachine.AOp
end A
/-- Caller1910=axis,1911=fiber,1912=native source,1913=fresh bank. -/
def boot : List Op := [.literal 1915 1,.literal 1916 4,.add 1917 105 102,
 .literal 1918 0,.literal 1919 1,.literal 1920 0]
def advance : List Op := [.mul 1921 1918 1916,.add 1921 1917 1921,.getNat 1922 1921,
 .mul 1919 1919 1922,.add 1918 1918 1915]
def readRadix : List Op := [.mul 1921 1910 1916,.add 1921 1917 1921,.getNat 1923 1921]
def quotients : List A.Op := [.bin .mul 1924 1919 1923,.bin .div 1925 103 1924]
def decodeSetup : List Op := [.add 70 1919 1920,.add 71 1923 1920,.add 72 1925 1920,
 .add 73 1911 1920,.add 81 1920 1920]
def copySetup (scatter:Bool) : List Op := [.add 1929 1912 99,.add 1900 1923 1920,
 .add 1901 (if scatter then 1913 else 1929) 1920,
 .add 1902 (if scatter then 1929 else 1913) 1920,
 .add 1903 (if scatter then 1915 else 1919) 1920,
 .add 1904 (if scatter then 1919 else 1915) 1920]
def head : Program := boot.map Op.code++[.branchLT 1918 1910 7 13]++advance.map Op.code++[.jump 6]++
 readRadix.map Op.code++quotients.map UniformRadixInstructionMachine.AOp.code++decodeSetup.map Op.code
/-- Two fixed programs. The Boolean selects copy direction at construction. -/
def program (scatter:Bool) : Program := head++UniformTensorAddressMachine.program.map (relocate 23 30)++
 (copySetup scatter).map Op.code++UniformTensorFiberCopyMachine.program.map (relocate 36 48)++[.halt]
theorem program_length (scatter:Bool) : (program scatter).length=49 := by cases scatter <;> rfl
theorem decoder_code (scatter:Bool) : CodeAt UniformTensorAddressMachine.program (program scatter) 23 30 := by
 intro i hi;rw [UniformTensorAddressMachine.program_length] at hi;interval_cases i <;> cases scatter <;> rfl
theorem copy_code (scatter:Bool) : CodeAt UniformTensorFiberCopyMachine.program (program scatter) 36 48 := by
 intro i hi;rw [UniformTensorFiberCopyMachine.program_length] at hi;interval_cases i <;> cases scatter <;> rfl
noncomputable section
abbrev radices := UniformCRTTraversalCycle.radices
def lower (n:ℕ) (i:Fin (ell n+1)) := place (radices n) i.val
def upper (n:ℕ) (i:Fin (ell n+1)) := UniformTensorAddressMachine.upperCount (radices n) i
def start (n:ℕ) (i:Fin (ell n+1)) (j:ℕ) := UniformTensorAddressMachine.address (lower n i) (radices n i) j 0
structure Args (i j a d:ℕ) (s:State) : Prop where
 axis : s.natReg 1910=i
 fiber : s.natReg 1911=j
 array : s.natReg 1912=a
 bank : s.natReg 1913=d

def Protected (i:ℕ) : Prop := (i < 70 ∨ 74 ≤ i) ∧ i ≠ 81 ∧ (i < 89 ∨ 100 ≤ i) ∧
 (i < 1900 ∨ 1909 ≤ i) ∧ (i < 1915 ∨ 1930 ≤ i)
instance (i:ℕ) : Decidable (Protected i) := by unfold Protected;infer_instance
structure PureFrame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 scalarHeap : u.scalarHeap=s.scalarHeap
 scalarReg : u.scalarReg=s.scalarReg
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀ i, Protected i → u.natReg i=s.natReg i

theorem PureFrame.refl (s:State) : PureFrame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem PureFrame.trans {s u v:State} (f:PureFrame s u) (g:PureFrame u v) : PureFrame s v :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
 g.outputs.trans f.outputs,g.roots.trans f.roots,fun i hi=>(g.natReg i hi).trans (f.natReg i hi)⟩
theorem PureFrame.withPC {s u:State} {pc:ℕ} (f:PureFrame s u) : PureFrame s {u with pc:=pc} :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
theorem PureFrame.pc (s:State) (pc:ℕ) : PureFrame s {s with pc:=pc} := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem PureFrame.metadata {n:ℕ} {s u:State} (f:PureFrame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · exact ⟨(f.natReg 100 (by decide)).trans h.saved.nextPrime,
    (f.natReg 101 (by decide)).trans h.saved.inputLength,
    (f.natReg 102 (by decide)).trans h.saved.count,
    (f.natReg 103 (by decide)).trans h.saved.workingLength,
    (f.natReg 104 (by decide)).trans h.saved.masterRoot,
    (f.natReg 105 (by decide)).trans h.saved.copyAddress,
    (f.natReg 106 (by decide)).trans h.saved.copyLength⟩
 · intro a _;exact congrFun f.natHeap _
theorem PureFrame.args {i j a d:ℕ} {s u:State} (f:PureFrame s u) (h:Args i j a d s) : Args i j a d u :=
 ⟨(f.natReg _ (by decide)).trans h.axis,(f.natReg _ (by decide)).trans h.fiber,
 (f.natReg _ (by decide)).trans h.array,(f.natReg _ (by decide)).trans h.bank⟩

def Safe (o:Op) : Prop := match o with
 | .literal d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .getNat d _=>¬Protected d
 | _=>False

instance (o:Op) : Decidable (Safe o) := by cases o <;> unfold Safe <;> infer_instance

theorem writeNat_pure (s:State) (d v:ℕ) (h:¬Protected d) : PureFrame s (writeNat s d v) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro i hi
 have he:i≠d:=by intro e;subst i;exact h hi
 simp [writeNat,next,he]
theorem pure_op (o:Op) (s:State) (h:Safe o) : PureFrame s (o.apply s) := by
 cases o <;> simp only [Safe] at h
 all_goals exact writeNat_pure s _ _ h
theorem pure_block (os:List Op) (s:State) (h:∀o∈os,Safe o) : PureFrame s (applyBlock os s) := by
 induction os generalizing s with
 | nil=>exact PureFrame.refl s
 | cons o os ih=>exact (pure_op o s (h o (by simp))).trans (ih (o.apply s) (fun q hq=>h q (by simp [hq])))

theorem boot_frame (s:State) : PureFrame s (applyBlock boot s) := by
 apply pure_block;intro o ho;simp [boot] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem advance_frame (s:State) : PureFrame s (applyBlock advance s) := by
 apply pure_block;intro o ho;simp [advance] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl <;> decide

theorem radix_frame (s:State) : PureFrame s (applyBlock readRadix s) := by
 apply pure_block;intro o ho;simp [readRadix] at ho
 rcases ho with rfl|rfl|rfl <;> decide

theorem crt_cell {n:ℕ} (i:Fin (ell n+1)) (s:State) (h:Metadata n s) :
 s.natHeap (copyBase n+ell n+4*i.val)=some (radices n i) := by
 simpa [protectedView,UniformCRTHeaderMachine.tableAddress,Nat.add_assoc] using (h.crt i).1

theorem place_bound {n:ℕ} (hn:0<n) (k:ℕ) : place (radices n) k ≤ len n := by
 apply Nat.le_of_dvd (UniformWorkingLength.workingLength_pos hn)
 simpa only [UniformSelectedCRT.radices_product] using UniformCRTTraversalCycle.place_dvd_all (radices n) k

structure Cursor (n axis j a d k:ℕ) (s:State) : Prop where
 args : Args axis j a d s
 metadata : Metadata n s
 one : s.natReg 1915=1
 four : s.natReg 1916=4
 table : s.natReg 1917=copyBase n+ell n
 index : s.natReg 1918=k
 product : s.natReg 1919=place (radices n) k
 zero : s.natReg 1920=0

theorem Cursor.withPC {n axis j a d k pc:ℕ} {s:State} (h:Cursor n axis j a d k s) :
 Cursor n axis j a d k {s with pc:=pc} := by
 refine ⟨(PureFrame.pc s pc).args h.args,(PureFrame.pc s pc).metadata h.metadata,
 h.one,h.four,h.table,h.index,h.product,h.zero⟩

def advanceEnd (s:State) := {applyBlock advance {s with pc:=7} with pc:=6}
theorem advance_cursor {n axis j a d k:ℕ} {s:State} (h:Cursor n axis j a d k s)
 (hk:k < ell n+1) : Cursor n axis j a d (k+1) (advanceEnd s) := by
 let ik:Fin (ell n+1):=⟨k,hk⟩
 have cell:=crt_cell ik s h.metadata
 simp only [ik,Nat.mul_comm] at cell
 have f:PureFrame s (advanceEnd s):=(PureFrame.pc s 7).trans (advance_frame {s with pc:=7}).withPC
 refine ⟨f.args h.args,f.metadata h.metadata,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [advanceEnd,applyBlock,advance,Op.apply,writeNat,next,h.one,h.four,h.table,h.index,h.product,h.zero,
   cell]
 simpa only [ik,Fin.val_mk] using (UniformCRTTraversalCycle.place_succ (radices n) ik).symm

theorem boot_cursor {n:ℕ} (i:Fin (ell n+1)) (j a d:ℕ) (s:State) (h:Metadata n s) (args:Args i.val j a d s) :
 Cursor n i.val j a d 0 (applyBlock boot s) := by
 have f:=boot_frame s
 refine ⟨f.args args,f.metadata h,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [applyBlock,boot,Op.apply,writeNat,next,h.saved.count,h.saved.copyAddress,UniformCRTTraversalCycle.place_zero]

theorem advance_code (scatter:Bool) : BlockAt advance (program scatter) 7 := by
 intro i hi;change i < 5 at hi;interval_cases i <;> cases scatter <;> rfl

theorem advance_execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (j a d k B:ℕ)
 (x:Fin n → ℂ) (s:State) (h:Cursor n i.val j a d k s) (hk:k < i.val)
 (hc:49 ≤ B) (hp:s.pc=6) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 7 (advanceEnd s) := by
 let ik:Fin (ell n+1):=⟨k,by omega⟩
 have cell:=crt_cell ik s h.metadata
 simp only [ik,Nat.mul_comm] at cell
 have cb:=hs.2.2.1 _ _ cell
 have pb:=place_bound hn (k+1)
 have lb:len n ≤ B:=by rw [←h.metadata.saved.workingLength];exact hs.2.1 103
 have kth:k ≤ B:=by have hb:=hs.2.1 1910;rw [h.args.axis] at hb;omega
 have kp:=UniformCRTTraversalCycle.place_succ (radices n) ik
 simp only [ik] at kp
 let t:State:={s with pc:=7}
 have tb:=changePC_bound B s 7 hs (by omega)
 have enter:BoundedRuns (program scatter) n x B s 1 t:=.next hs
   (by cases scatter <;> simp [step,program,head,boot,advance,hp,h.index,h.args.axis,hk,t]) (.refl tb)
 have b:=block_runs advance (program scatter) 7 n B x t (advance_code scatter) rfl tb
   (by change 7+5 ≤ B;omega)
   (by simp [readable,advance,Op.readable,Op.apply,t,writeNat,next,h.index,h.four,h.table,cell])
   (by simp [peak,advance,Op.peak,Op.apply,t,writeNat,next,h.index,h.one,h.four,h.table,h.product,cell]
       have vb:=hs.2.2.1 _ _ cell
       rw [kp] at pb
       omega)
 have ep:(applyBlock advance t).pc=12:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have jump:BoundedRuns (program scatter) n x B (applyBlock advance t) 1 (advanceEnd s):=.next b.final_bound
   (by unfold step;rw [show (program scatter)[(applyBlock advance t).pc]?=some (.jump 6) by rw [ep];cases scatter <;> rfl];rfl)
   (.refl (changePC_bound B _ 6 b.final_bound (by omega)))
 convert enter.trans (b.trans jump) using 1;rfl

theorem loop {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (j a d k fuel B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:Cursor n i.val j a d k s) (count:k+fuel=i.val)
 (hc:49≤B) (hp:s.pc=6) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s (7*fuel) u ∧ Cursor n i.val j a d i.val u ∧
 u.pc=6 ∧ PureFrame s u := by
 induction fuel generalizing k s with
 | zero =>
   have he:k=i.val:=by omega
   subst k
   exact ⟨s,.refl hs,h,hp,PureFrame.refl s⟩
 | succ fuel ih =>
   have run:=advance_execution hn scatter i j a d k B x s h (by omega) hc hp hs
   have cu:=advance_cursor h (show k<ell n+1 by omega)
   obtain ⟨u,rest,hu,pu,fu⟩:=ih (k+1) (advanceEnd s) cu (by omega) rfl run.final_bound
   have fr:PureFrame s (advanceEnd s):=(PureFrame.pc s 7).trans (advance_frame {s with pc:=7}).withPC
   exact ⟨u,by convert run.trans rest using 1;omega,hu,pu,fr.trans fu⟩

theorem boot_code (scatter:Bool) : BlockAt boot (program scatter) 0 := by
 intro i hi;change i<6 at hi;interval_cases i <;> cases scatter <;> rfl

theorem prefix_execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val j a d s)
 (hc:49≤B) (hp:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s (7*i.val+7) u ∧ Cursor n i.val j a d i.val u ∧
 u.pc=13 ∧ PureFrame s u := by
 have cell:=crt_cell i s metadata
 have bound:=hs.2.2.1 _ _ cell
 have m105:s.natReg 105=copyBase n:=metadata.saved.copyAddress
 have start:=block_runs boot (program scatter) 0 n B x s (boot_code scatter) hp hs
   (by change 0+6≤B;omega) (by simp [readable,boot,Op.readable])
   (by simp [peak,boot,Op.peak,Op.apply,writeNat,next,m105,metadata.saved.count];omega)
 have pc:(applyBlock boot s).pc=6:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 obtain ⟨u,run,cu,pu,fu⟩:=loop hn scatter i j a d 0 i.val B x (applyBlock boot s)
   (boot_cursor i j a d s metadata args) (by omega) hc pc start.final_bound
 let v:State:={u with pc:=13}
 have endrun:BoundedRuns (program scatter) n x B u 1 v:=.next run.final_bound
   (by cases scatter <;> simp [step,pu,program,head,boot,cu.index,cu.args.axis,v])
   (.refl (changePC_bound B _ 13 run.final_bound (by omega)))
 exact ⟨v,by convert start.trans (run.trans endrun) using 1;simp [boot];omega,
  cu.withPC,rfl,
  (boot_frame s).trans (fu.trans (PureFrame.pc u 13))⟩

theorem selected_positive (n:ℕ) (i:Fin (ell n+1)) :
 0<lower n i ∧ 0<radices n i ∧ 0<upper n i :=
 ⟨UniformCRTTraversalCycle.place_pos _ (UniformSelectedCRT.radix_pos n) _,
 UniformSelectedCRT.radix_pos n i,UniformTensorAddressMachine.upperCount_pos _ (UniformSelectedCRT.radix_pos n) i⟩
theorem selected_product (n:ℕ) (i:Fin (ell n+1)) : lower n i*radices n i*upper n i=len n :=
 UniformTensorAddressMachine.selected_layout n i
theorem selected_quotient (n:ℕ) (i:Fin (ell n+1)) : len n/(lower n i*radices n i)=upper n i := by
 rw [←selected_product n i]
 exact Nat.mul_div_right _ (Nat.mul_pos (selected_positive n i).1 (selected_positive n i).2.1)

def parametersState (s:State) := applyBlock decodeSetup
 (UniformRadixInstructionMachine.block quotients (applyBlock readRadix s))
structure Parameters (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ) (s:State) : Prop where
 args : Args i.val j a d s
 metadata : Metadata n s
 one : s.natReg 1915=1
 zero : s.natReg 1920=0
 product : s.natReg 1919=lower n i
 radix : s.natReg 1923=radices n i
 quotient : s.natReg 1925=upper n i
 p : s.natReg 70=lower n i
 r : s.natReg 71=radices n i
 q : s.natReg 72=upper n i
 j : s.natReg 73=j
 t : s.natReg 81=0

theorem quotients_frame (s:State) : PureFrame s (UniformRadixInstructionMachine.block quotients s) := by
 exact (writeNat_pure s 1924 _ (by decide)).trans (writeNat_pure _ 1925 _ (by decide))
theorem decodeSetup_frame (s:State) : PureFrame s (applyBlock decodeSetup s) := by
 apply pure_block;intro o ho;simp [decodeSetup] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl <;> decide
theorem parameters_frame (s:State) : PureFrame s (parametersState s) :=
 (radix_frame s).trans ((quotients_frame _).trans (decodeSetup_frame _))
theorem parameters_values {n:ℕ} (i:Fin (ell n+1)) (j a d:ℕ) (s:State)
 (h:Cursor n i.val j a d i.val s) : Parameters n i j a d (parametersState s) := by
 have cell:=crt_cell i s h.metadata
 simp only [Nat.mul_comm] at cell
 have hp0:place (radices n) i.val≠0:=Nat.ne_of_gt (selected_positive n i).1
 have hr0:radices n i≠0:=Nat.ne_of_gt (selected_positive n i).2.1
 have quot:len n/(place (radices n) i.val*radices n i)=upper n i:=selected_quotient n i
 have f:=parameters_frame s
 refine ⟨f.args h.args,f.metadata h.metadata,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [parametersState,applyBlock,readRadix,quotients,decodeSetup,Op.apply,writeNat,next,
 UniformRadixInstructionMachine.block,UniformRadixInstructionMachine.AOp.apply,
 UniformRadixInstructionMachine.AOp.value,evalNat,h.zero,h.one,h.table,h.args.axis,h.four,h.product,
 h.args.fiber,h.metadata.saved.workingLength,cell,lower,hp0,hr0,quot]

theorem radix_code (scatter:Bool) : BlockAt readRadix (program scatter) 13 := by
 intro i hi;change i<3 at hi;interval_cases i <;> cases scatter <;> rfl
theorem quotients_code (scatter:Bool) : UniformRadixInstructionMachine.BlockAt quotients (program scatter) 16 := by
 intro i;fin_cases i <;> cases scatter <;> rfl
theorem decodeSetup_code (scatter:Bool) : BlockAt decodeSetup (program scatter) 18 := by
 intro i hi;change i<5 at hi;interval_cases i <;> cases scatter <;> rfl

theorem parameters_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:Cursor n i.val j a d i.val s)
 (hc:49≤B) (hp:s.pc=13) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 10 (parametersState s) := by
 have cell:=crt_cell i s h.metadata
 simp only [Nat.mul_comm] at cell
 have cb:=hs.2.2.1 _ _ cell
 have lb:len n≤B:=by rw [←h.metadata.saved.workingLength];exact hs.2.1 103
 have pos:=selected_positive n i
 have prod:=selected_product n i
 have prb:lower n i*radices n i≤B:=by nlinarith [show 1≤upper n i by omega]
 have qb:upper n i≤B:=by nlinarith [show 1≤lower n i*radices n i by nlinarith]
 have hp0:place (radices n) i.val≠0:=Nat.ne_of_gt pos.1
 have hr0:radices n i≠0:=Nat.ne_of_gt pos.2.1
 have quot:len n/(place (radices n) i.val*radices n i)=upper n i:=selected_quotient n i
 have jb:j≤B:=by have hh:=hs.2.1 1911;rw [h.args.fiber] at hh;exact hh
 have rd:=block_runs readRadix (program scatter) 13 n B x s (radix_code scatter) hp hs
   (by change 13+3≤B;omega)
   (by simp [readable,readRadix,Op.readable,Op.apply,writeNat,next,h.args.axis,h.four,h.table,cell])
   (by simp [peak,readRadix,Op.peak,Op.apply,writeNat,next,h.args.axis,h.four,h.table,cell];omega)
 let t:=applyBlock readRadix s
 have pt:t.pc=16:=by rw [UniformTensorMonomialMachine.applyBlock_pc,hp];rfl
 have rq:=UniformRadixInstructionMachine.block_runs quotients (program scatter) 16 n B x t
   (quotients_code scatter) pt rd.final_bound (by change 16+2≤B;omega)
   (by simp [UniformRadixInstructionMachine.validBlock,quotients,UniformRadixInstructionMachine.AOp.valid,
       UniformRadixInstructionMachine.AOp.apply,UniformRadixInstructionMachine.AOp.value,t,applyBlock,
       readRadix,Op.apply,writeNat,next,h.args.axis,h.four,h.table,h.product,cell,evalNat,hp0,hr0])
   (by simp [UniformRadixInstructionMachine.peakBlock,quotients,UniformRadixInstructionMachine.AOp.value,
       UniformRadixInstructionMachine.AOp.apply,t,applyBlock,readRadix,Op.apply,writeNat,next,h.args.axis,
       h.four,h.table,h.product,cell,evalNat,h.metadata.saved.workingLength,hp0,hr0,quot];
       exact ⟨prb,qb⟩)
 let u:=UniformRadixInstructionMachine.block quotients t
 have pu:u.pc=18:=by rw [UniformRadixInstructionMachine.block_pc,pt];rfl
 have ds:=block_runs decodeSetup (program scatter) 18 n B x u (decodeSetup_code scatter) pu rq.final_bound
   (by change 18+5≤B;omega) (by simp [readable,decodeSetup,Op.readable])
   (by simp [peak,decodeSetup,Op.peak,Op.apply,u,t,quotients,UniformRadixInstructionMachine.block,
       UniformRadixInstructionMachine.AOp.apply,UniformRadixInstructionMachine.AOp.value,
       readRadix,applyBlock,Op.apply,writeNat,next,evalNat,h.zero,h.product,h.args.axis,h.args.fiber,
       h.four,h.table,h.metadata.saved.workingLength,cell,hp0,hr0,quot];
       have pb:lower n i≤B:=by have hh:=hs.2.1 1919;rw [h.product] at hh;exact hh
       exact ⟨pb,cb.2,qb,jb⟩)
 convert rd.trans (rq.trans ds) using 1 <;> rfl


theorem address_affine (P r j t:ℕ) : UniformTensorAddressMachine.address P r j t=
 UniformTensorAddressMachine.address P r j 0+t*P := by
 unfold UniformTensorAddressMachine.address;ring

theorem start_bounds (n:ℕ) (i:Fin (ell n+1)) (j:ℕ) (hj:j<lower n i*upper n i) :
 start n i j<len n ∧ start n i j+radices n i*lower n i≤2*len n := by
 have pos:=selected_positive n i
 have prod:=selected_product n i
 have h:=UniformTensorAddressMachine.address_lt _ _ _ j 0 hj pos.2.1
 have st:start n i j<len n:=by simpa only [start,prod] using h
 have pr:radices n i*lower n i≤len n:=by nlinarith [show 1≤upper n i by omega]
 omega

structure CopyArgs (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ) (s:State) : Prop where
 args : Args i.val j a d s
 metadata : Metadata n s
 one : s.natReg 1915=1
 zero : s.natReg 1920=0
 product : s.natReg 1919=lower n i
 radix : s.natReg 1923=radices n i
 offset : s.natReg 99=start n i j

theorem decoder_pure {s u:State} (f:UniformTensorAddressMachine.Frame s u) : PureFrame s u := by
 refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
 intro z hz;apply f.2.2.2.2.2;unfold Protected at hz;omega

theorem decode_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:Parameters n i j a d s) (hj:j<lower n i*upper n i)
 (hc:49≤B) (hp:s.pc=23) (hs:WordBound B s) : ∃u,
 BoundedRuns (program scatter) n x B s 7 u ∧ CopyArgs n i j a d u ∧ u.pc=30 ∧ PureFrame s u := by
 let v:State:={s with pc:=0}
 have vb:=changePC_bound B s 0 hs (by omega)
 have lb:len n≤B:=by rw [←h.metadata.saved.workingLength];exact hs.2.1 103
 obtain ⟨u,run,offset,_range,fr,_pu⟩:=UniformTensorAddressMachine.execution n x
   (lower n i) (radices n i) (upper n i) j 0 B v (selected_positive n i).1 hj
   (selected_positive n i).2.1 (by rw [selected_product];exact lb) (by omega) rfl
   h.p h.r h.q h.j h.t vb
 have placed:=UniformBoundedAssembly.boundedExecution_placed (decoder_code scatter)
   (by rw [UniformTensorAddressMachine.program_length];omega) (by omega) run
 have pf:PureFrame s {u with pc:=30}:=(PureFrame.pc s 0).trans (decoder_pure fr).withPC
 refine ⟨{u with pc:=30},?_,⟨pf.args h.args,pf.metadata h.metadata,?_,?_,?_,?_,offset⟩,rfl,pf⟩
 · have eq:UniformAssembly.placed 23 v=s:=by change {s with pc:=23}=s;rw [←hp]
   rw [eq] at placed;exact placed
 · exact (fr.2.2.2.2.2 1915 (by omega)).trans h.one
 · exact (fr.2.2.2.2.2 1920 (by omega)).trans h.zero
 · exact (fr.2.2.2.2.2 1919 (by omega)).trans h.product
 · exact (fr.2.2.2.2.2 1923 (by omega)).trans h.radix

theorem copySetup_code (scatter:Bool) : BlockAt (copySetup scatter) (program scatter) 30 := by
 intro i hi;change i<6 at hi;interval_cases i <;> cases scatter <;> rfl
theorem copySetup_frame (scatter:Bool) (s:State) : PureFrame s (applyBlock (copySetup scatter) s) := by
 apply pure_block;intro o ho;simp [copySetup] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl <;> cases scatter <;> decide

def fromAddress (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ) : ℕ := if scatter then d else a+start n i j
def toAddress (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ) : ℕ := if scatter then a+start n i j else d
def fromStride (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) : ℕ := if scatter then 1 else lower n i
def toStride (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) : ℕ := if scatter then lower n i else 1

theorem copySetup_header {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d:ℕ) (s:State)
 (h:CopyArgs n i j a d s) : UniformTensorFiberCopyMachine.Header (radices n i)
 (fromAddress scatter n i j a d) (toAddress scatter n i j a d)
 (fromStride scatter n i) (toStride scatter n i) (applyBlock (copySetup scatter) s) := by
 constructor <;> cases scatter <;> simp [applyBlock,copySetup,Op.apply,writeNat,next,
 h.one,h.zero,h.product,h.radix,h.offset,h.args.array,h.args.bank,
 fromAddress,toAddress,fromStride,toStride]

theorem copySetup_execution {n:ℕ} (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (h:CopyArgs n i j a d s) (hj:j<lower n i*upper n i)
 (ha:a+2*len n≤B) (hd:d+radices n i≤B)
 (hc:49≤B) (hp:s.pc=30) (hs:WordBound B s) :
 BoundedRuns (program scatter) n x B s 6 (applyBlock (copySetup scatter) s) := by
 have st:=start_bounds n i j hj
 have pb:lower n i≤B:=by rw [←h.product];exact hs.2.1 1919
 have rb:radices n i≤B:=by rw [←h.radix];exact hs.2.1 1923
 apply block_runs (copySetup scatter) (program scatter) 30 n B x s (copySetup_code scatter) hp hs
   (by change 30+6≤B;omega) (by cases scatter <;> simp [readable,copySetup,Op.readable])
 cases scatter <;> simp [peak,copySetup,Op.peak,Op.apply,writeNat,next,
 h.one,h.zero,h.product,h.radix,h.offset,h.args.array,h.args.bank] <;> omega


/-- Input values are ordinary physical heap entries; all dependency flags are allowed. -/
def PhysicalSource (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (a d:ℕ) (heap:ℕ→Option Scalar) : Prop :=
 if scatter then ∀t,t<radices n i→∃v,heap (d+t)=some v
 else ∀z,z<len n→∃v,heap (a+z)=some v

structure Frame (s u:State) : Prop where
 natHeap : u.natHeap=s.natHeap
 outputs : u.outputs=s.outputs
 roots : u.rootOrders=s.rootOrders
 natReg : ∀z,Protected z→u.natReg z=s.natReg z
 scalarReg : ∀z,z≠100→u.scalarReg z=s.scalarReg z

theorem PureFrame.frame {s u:State} (f:PureFrame s u) : Frame s u :=
 ⟨f.natHeap,f.outputs,f.roots,f.natReg,fun z _=>congrFun f.scalarReg z⟩
theorem Frame.trans {s u v:State} (f:Frame s u) (g:Frame u v) : Frame s v :=
 ⟨g.natHeap.trans f.natHeap,g.outputs.trans f.outputs,g.roots.trans f.roots,
 fun z hz=>(g.natReg z hz).trans (f.natReg z hz),fun z hz=>(g.scalarReg z hz).trans (f.scalarReg z hz)⟩
theorem Frame.pc (s:State) (pc:ℕ) : Frame s {s with pc:=pc} := ⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
theorem Frame.metadata {n:ℕ} {s u:State} (f:Frame s u) (h:Metadata n s) : Metadata n u := by
 apply h.transport_saved
 · exact ⟨(f.natReg 100 (by decide)).trans h.saved.nextPrime,
    (f.natReg 101 (by decide)).trans h.saved.inputLength,(f.natReg 102 (by decide)).trans h.saved.count,
    (f.natReg 103 (by decide)).trans h.saved.workingLength,(f.natReg 104 (by decide)).trans h.saved.masterRoot,
    (f.natReg 105 (by decide)).trans h.saved.copyAddress,(f.natReg 106 (by decide)).trans h.saved.copyLength⟩
 · intro z _;exact congrFun f.natHeap (copyBase n+z)

theorem copy_frame {s u:State} (f:UniformTensorFiberCopyMachine.Frame s u) : Frame s u := by
 refine ⟨f.natHeap,f.outputs,f.roots,?_,f.scalarReg⟩
 intro z hz;apply f.natReg;unfold Protected at hz;omega

theorem source_from_array (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ)
 (heap:ℕ→Option Scalar) (hj:j<lower n i*upper n i) (src:PhysicalSource scatter n i a d heap) :
 UniformTensorFiberCopyMachine.Source (radices n i) (fromAddress scatter n i j a d)
 (fromStride scatter n i) heap := by
 intro t ht
 cases scatter with
 | false =>
   have hz:=UniformTensorAddressMachine.address_lt (lower n i) (radices n i) (upper n i) j t hj ht
   rw [selected_product] at hz
   simpa only [fromAddress,fromStride,Bool.false_eq_true,ite_false,Nat.add_assoc,←address_affine,start] using src _ hz
 | true => simpa [PhysicalSource,fromAddress,fromStride] using src t ht

theorem copy_separate (scatter:Bool) (n:ℕ) (i:Fin (ell n+1)) (j a d:ℕ)
 (hj:j<lower n i*upper n i) (sep:a+len n≤d) : ∀t,t<radices n i→∀v,v<radices n i→
 fromAddress scatter n i j a d+t*fromStride scatter n i≠
 toAddress scatter n i j a d+v*toStride scatter n i := by
 intro t ht v hv
 have range (k:ℕ) (hk:k<radices n i) : a+start n i j+k*lower n i<a+len n := by
   have h:=UniformTensorAddressMachine.address_lt (lower n i) (radices n i) (upper n i) j k hj hk
   rw [selected_product,address_affine] at h
   change start n i j+k*lower n i<len n at h
   omega
 cases scatter <;> simp [fromAddress,toAddress,fromStride,toStride]
 · have h:=range t ht;omega
 · have h:=range v hv;omega

/-- One continuous selected-metadata-to-copy run. No P/r/Q, decoded address,
strided table or helper header is supplied by the caller. -/
theorem execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (j a d B:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val j a d s)
 (hj:j<lower n i*upper n i) (src:PhysicalSource scatter n i a d s.scalarHeap)
 (sep:a+len n≤d) (ha:a+2*len n≤B) (hd:d+radices n i≤B)
 (hc:49≤B) (hp:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution (program scatter) n x B s (9*radices n i+7*i.val+35) u ∧ u.pc=48 ∧
 (∀t,t<radices n i→u.scalarHeap (toAddress scatter n i j a d+t*toStride scatter n i)=
   s.scalarHeap (fromAddress scatter n i j a d+t*fromStride scatter n i)) ∧
 UniformTensorFiberCopyMachine.Outside (toAddress scatter n i j a d) (toStride scatter n i)
   (radices n i) s.scalarHeap u ∧ Frame s u ∧ Metadata n u := by
 obtain ⟨p,prun,cp,pp,fp⟩:=prefix_execution hn scatter i j a d B x s metadata args hc hp hs
 have p2:=parameters_execution scatter i j a d B x p cp hc pp prun.final_bound
 have pv:=parameters_values i j a d p cp
 have ppc:(parametersState p).pc=23:=by
   simp [parametersState,UniformTensorMonomialMachine.applyBlock_pc,UniformRadixInstructionMachine.block_pc,pp,
     decodeSetup,quotients,readRadix]
 obtain ⟨z,drun,cz,pz,fz⟩:=decode_execution scatter i j a d B x (parametersState p) pv hj hc ppc p2.final_bound
 have crun:=copySetup_execution scatter i j a d B x z cz hj ha hd hc pz drun.final_bound
 let c:=applyBlock (copySetup scatter) z
 have pc:c.pc=36:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pz];cases scatter <;> rfl
 have fc:PureFrame s c:=fp.trans ((parameters_frame p).trans (fz.trans (copySetup_frame scatter z)))
 have header:=copySetup_header scatter i j a d z cz
 have ss:UniformTensorFiberCopyMachine.Source (radices n i) (fromAddress scatter n i j a d)
   (fromStride scatter n i) c.scalarHeap:=by
   rw [fc.scalarHeap];exact source_from_array scatter n i j a d s.scalarHeap hj src
 have se:=copy_separate scatter n i j a d hj sep
 have sb:=start_bounds n i j hj
 have hfrom:fromAddress scatter n i j a d+radices n i*fromStride scatter n i≤B:=by
   cases scatter <;> simp [fromAddress,fromStride] <;> omega
 have hto:toAddress scatter n i j a d+radices n i*toStride scatter n i≤B:=by
   cases scatter <;> simp [toAddress,toStride] <;> omega
 let c0:State:={c with pc:=0}
 obtain ⟨u,run,pu,copied,outside,fu⟩:=UniformTensorFiberCopyMachine.execution n B (radices n i)
   (fromAddress scatter n i j a d) (toAddress scatter n i j a d)
   (fromStride scatter n i) (toStride scatter n i) x c0 header.withPC
   (by cases scatter <;> simp [toStride];exact (selected_positive n i).1)
   ss se hfrom hto (by omega) rfl (changePC_bound B c 0 crun.final_bound (by omega))
 have placed:=UniformBoundedAssembly.boundedExecution_placed (copy_code scatter)
   (by rw [UniformTensorFiberCopyMachine.program_length];omega) (by omega) run
 have eq:UniformAssembly.placed 36 c0=c:=by
   change {c with pc:=36}=c;rw [←pc]
 rw [eq] at placed
 let v:State:={u with pc:=48}
 have stop:BoundedExecution (program scatter) n x B v 1 v:=.halt placed.final_bound
   (by unfold step;rw [show (program scatter)[v.pc]?=some .halt by cases scatter <;> rfl])
 have frame:Frame s v:=fc.frame.trans ((Frame.pc c 0).trans ((copy_frame fu).trans (Frame.pc u 48)))
 refine ⟨v,?_,rfl,?_,?_,frame,frame.metadata metadata⟩
 · convert prun.executes (p2.executes (drun.executes (crun.executes (placed.executes stop)))) using 1;omega
 · intro t ht;simpa only [v,c0,fc.scalarHeap] using copied t ht
 · intro z hz;simpa only [v,c0,fc.scalarHeap] using outside z hz


/-- The copy result preserves every physical operand below a fresh destination. -/
theorem operands_of_below {n:ℕ} {x:Fin n→ℂ} {s u:State} (d:ℕ)
 (h:UniformInitialPreparation.Operands n x s) (hd:UniformNormalizationPreparation.normBase n<d)
 (fr:∀z,z<d→u.scalarHeap z=s.scalarHeap z) : UniformInitialPreparation.Operands n x u := by
 have nb:UniformNormalizationPreparation.normBase n=ell n+7+2*n+2*len n:=by
   change ell n+7+2*n+len n+len n=ell n+7+2*n+2*len n;omega
 constructor
 · intro j;rw [fr j.val (by have:=j.isLt;omega)];exact h.constants j
 · intro j;rw [fr (6+j.val) (by have:=j.isLt;omega)];exact h.roots j
 · intro j hj
   rw [fr (ell n+7+2*j) (by omega),fr (ell n+7+2*j+1) (by omega)]
   exact h.chirps j hj
 · intro j hj
   rw [fr (UniformPaddedInputPreparation.dataBase n+j) (by change ell n+7+2*n+j<d;omega)]
   exact h.input j hj
 · intro j hj
   rw [fr (UniformChirpKernelPreparation.kernelBase n+j) (by
       change ell n+7+2*n+len n+j<d;omega)]
   exact h.kernel j hj
 · rw [fr (UniformNormalizationPreparation.normBase n) hd];exact h.normalization

theorem native_source {n:ℕ} (i:Fin (ell n+1)) (d:ℕ) {x:Fin n→ℂ} {s:State}
 (h:UniformInitialPreparation.Operands n x s) :
 PhysicalSource false n i (UniformPaddedInputPreparation.dataBase n) d s.scalarHeap := by
 intro z hz;exact ⟨_,h.input z hz⟩

theorem canonical_code_bound {n:ℕ} (hn:0<n) : 49≤(n+2)^19 := by
 have h:49≤3^19:=by norm_num
 exact h.trans (Nat.pow_le_pow_left (show 3≤n+2 by omega) 19)

/-- SAME global word budget. Pools are ordinary caller allocation bounds. -/
theorem canonical_execution {n:ℕ} (hn:0<n) (scatter:Bool) (i:Fin (ell n+1)) (j a d:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val j a d s)
 (hj:j<lower n i*upper n i) (src:PhysicalSource scatter n i a d s.scalarHeap)
 (sep:a+len n≤d) (ha:a+2*len n≤(n+2)^19) (hd:d+radices n i≤(n+2)^19)
 (hp:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
 BoundedExecution (program scatter) n x ((n+2)^19) s (9*radices n i+7*i.val+35) u ∧ u.pc=48 ∧
 (∀t,t<radices n i→u.scalarHeap (toAddress scatter n i j a d+t*toStride scatter n i)=
   s.scalarHeap (fromAddress scatter n i j a d+t*fromStride scatter n i)) ∧
 UniformTensorFiberCopyMachine.Outside (toAddress scatter n i j a d) (toStride scatter n i)
   (radices n i) s.scalarHeap u ∧ Frame s u ∧ Metadata n u :=
 execution hn scatter i j a d _ x s metadata args hj src sep ha hd (canonical_code_bound hn) hp hs

/-- Actual padded/chirped native operand cells, with all operand/root banks
retained by placing the fresh fiber above their physical end. -/
theorem native_gather_execution {n:ℕ} (hn:0<n) (i:Fin (ell n+1)) (j d:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (operands:UniformInitialPreparation.Operands n x s)
 (args:Args i.val j (UniformPaddedInputPreparation.dataBase n) d s)
 (hj:j<lower n i*upper n i) (fresh:UniformNormalizationPreparation.normBase n<d)
 (ha:UniformPaddedInputPreparation.dataBase n+2*len n≤(n+2)^19)
 (hd:d+radices n i≤(n+2)^19) (hp:s.pc=0) (hs:WordBound ((n+2)^19) s) : ∃u,
 BoundedExecution (program false) n x ((n+2)^19) s (9*radices n i+7*i.val+35) u ∧
 (∀t,t<radices n i→u.scalarHeap (d+t)=some (UniformPaddedInputMachine.paddedScalar
   (OAI.ExactFourier.zeta (2*n)) x (UniformTensorAddressMachine.address (lower n i) (radices n i) j t))) ∧
 Frame s u ∧ Metadata n u ∧ UniformInitialPreparation.Operands n x u := by
 have sep:UniformPaddedInputPreparation.dataBase n+len n≤d:=by
   change UniformPaddedInputPreparation.dataBase n+len n+len n<d at fresh;omega
 obtain ⟨u,run,_pc,copy,outside,frame,hm⟩:=canonical_execution hn false i j _ d x s metadata args hj
   (native_source i d operands) sep ha hd hp hs
 refine ⟨u,run,?_,frame,hm,operands_of_below d operands fresh ?_⟩
 · intro t ht
   have h:=copy t ht
   simp only [toAddress,fromAddress,toStride,fromStride,Bool.false_eq_true,ite_false,Nat.mul_one,Nat.add_assoc,
     ←address_affine,start] at h
   rw [h]
   apply operands.input
   rw [←selected_product n i]
   exact UniformTensorAddressMachine.address_lt _ _ _ j t hj ht
 · intro z hz;apply outside;intro t _;simp [toAddress,toStride];omega

/-- Each full native position has ONE selected fiber/digit pair. This is a
partition lemma, not an uncharged all-fiber driver. -/
theorem selected_coverage (n:ℕ) (i:Fin (ell n+1)) (z:Fin (len n)) :
 ∃!jt:Fin (lower n i*upper n i)×Fin (radices n i),
 UniformTensorAddressMachine.address (lower n i) (radices n i) jt.1.val jt.2.val=z.val := by
 have h:=UniformTensorAddressMachine.address_coverage (lower n i) (radices n i) (upper n i)
   ⟨z.val,by rw [selected_product];exact z.isLt⟩
 exact h

theorem inverse_positions (n:ℕ) (i:Fin (ell n+1)) (j:ℕ) (hj:j<lower n i*upper n i)
 (t:ℕ) (ht:t<radices n i) :
 ((UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i)).symm
  ⟨UniformTensorAddressMachine.address (lower n i) (radices n i) j t,
    UniformTensorAddressMachine.address_lt _ _ _ j t hj ht⟩).1.val=j ∧
 ((UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i)).symm
  ⟨UniformTensorAddressMachine.address (lower n i) (radices n i) j t,
    UniformTensorAddressMachine.address_lt _ _ _ j t hj ht⟩).2.val=t := by
 have eq:= (UniformTensorAddressMachine.fiberEquiv (lower n i) (radices n i) (upper n i)).symm_apply_apply
   (⟨j,hj⟩,⟨t,ht⟩)
 exact ⟨congrArg (fun z=>z.1.val) eq,congrArg (fun z=>z.2.val) eq⟩
end
end ExactFourierCircuits.UniformSelectedAxisFiberPreparation
