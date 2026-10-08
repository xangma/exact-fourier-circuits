import UniformSectorMetadataMachine
import UniformSectorPackingMachine
import UniformNatCopyMachine
import UniformPermutationInversePreparation
import UniformAllAxisSeedPreparation
import UniformRankCrossPreparationMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformMultiAxisSectorMetadataPreparation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)

/-- Nat3200=count,3201=actual four-word records,3202=fresh three-word records.
The copier reads each field physically; the fourth permutation field is retained. -/
def boot : List Op := [.literal 3204 1,.literal 3205 3,.literal 3206 4,.literal 3207 0]
def install : List Op := [.literal 53 3,.mul 3208 3207 3206,.add 54 3201 3208,
 .mul 3209 3207 3205,.add 55 3202 3209]
def projection : Program := boot.map Op.code ++ [.branchLT 3207 3200 5 22] ++
 install.map Op.code ++ UniformNatCopyMachine.program.map (relocate 10 20) ++
 [.natBinary .add 3207 3207 3204,.jump 4,.halt]
lemma projection_length : projection.length=23 := rfl
lemma boot_length : boot.length=4 := rfl
lemma install_length : install.length=5 := rfl
lemma boot_code : BlockAt boot projection 0 := by
 intro i hi;change i  <  4 at hi;interval_cases i  <;>  rfl
lemma install_code : BlockAt install projection 5 := by
 intro i hi;change i  <  5 at hi;interval_cases i  <;>  rfl
lemma copy_code : CodeAt UniformNatCopyMachine.program projection 10 20 := by
 exact UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++[.branchLT 3207 3200 5 22]++install.map Op.code)
  [.natBinary .add 3207 3207 3204,.jump 4,.halt] _ 10 20 (by rfl)
lemma branch_at : projection[4]?=some (.branchLT 3207 3200 5 22) := rfl
lemma advance_at : projection[20]?=some (.natBinary .add 3207 3207 3204) := rfl
lemma jump_at : projection[21]?=some (.jump 4) := rfl
lemma halt_at : projection[22]?=some .halt := rfl

noncomputable section
lemma placed_zero (s:State) (b:ℕ) (hp:s.pc=b):UniformAssembly.placed b (setPC s 0)=s :=by
 cases s;simp_all [UniformAssembly.placed,setPC]

def Source (m a:ℕ) (heap:ℕ → Option ℕ):Prop :=
 ∀i,i  <  m → ∀f,f  <  3 → ∃v,heap (a+4*i+f)=some v
def Outside (d m:ℕ) (heap:ℕ → Option ℕ) (s:State):Prop :=
 ∀i,(i  <  d  ∨ d+3*m ≤ i) → s.natHeap i=heap i
structure Invariant (m a d j:ℕ) (heap:ℕ → Option ℕ) (s:State):Prop where
 count:s.natReg 3200=m
 source:s.natReg 3201=a
 target:s.natReg 3202=d
 one:s.natReg 3204=1
 three:s.natReg 3205=3
 four:s.natReg 3206=4
 index:s.natReg 3207=j
 copied:∀i,i  <  j → ∀f,f  <  3 → s.natHeap (d+3*i+f)=heap (a+4*i+f)
 outside:Outside d m heap s

def Frame (s u:State):Prop :=u.scalarHeap=s.scalarHeap  ∧ u.scalarReg=s.scalarReg  ∧
 u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧
 ∀i,(i  <  53  ∨ 61 ≤ i) → (i  <  3204  ∨ 3210 ≤ i) → u.natReg i=s.natReg i
lemma Frame.refl (s:State):Frame s s :=⟨rfl,rfl,rfl,rfl,fun _ _ _=> rfl⟩
lemma Frame.trans {s u v:State} (h:Frame s u) (k:Frame u v):Frame s v :=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
 k.2.2.2.1.trans h.2.2.2.1,fun i hi hj=> (k.2.2.2.2 i hi hj).trans (h.2.2.2.2 i hi hj)⟩
lemma Invariant.withPC {m a d j pc:ℕ} {heap:ℕ → Option ℕ} {s:State}
 (h:Invariant m a d j heap s):Invariant m a d j heap (setPC s pc) :=by
 cases h;constructor  <;>  assumption
lemma install_frame (s:State):Frame s (applyBlock install s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i hi hj
 simp (disch:=omega) [install,applyBlock,Op.apply,writeNat,next]
lemma install_invariant {m a d j:ℕ} {heap:ℕ → Option ℕ} {s:State}
 (h:Invariant m a d j heap s):Invariant m a d j heap (applyBlock install s) :=by
 rcases h with ⟨hc,ha,hd,h1,h3,h4,hj,copy,out⟩
 constructor
 all_goals first
  | simpa [install,applyBlock,Op.apply,writeNat,next] using hc
  | simpa [install,applyBlock,Op.apply,writeNat,next] using ha
  | simpa [install,applyBlock,Op.apply,writeNat,next] using hd
  | simpa [install,applyBlock,Op.apply,writeNat,next] using h1
  | simpa [install,applyBlock,Op.apply,writeNat,next] using h3
  | simpa [install,applyBlock,Op.apply,writeNat,next] using h4
  | simpa [install,applyBlock,Op.apply,writeNat,next] using hj
  | exact copy
  | exact out
lemma install_args {m a d j:ℕ} {heap:ℕ → Option ℕ} {s:State}
 (h:Invariant m a d j heap s):
 (applyBlock install s).natReg 53=3  ∧ (applyBlock install s).natReg 54=a+4*j  ∧
 (applyBlock install s).natReg 55=d+3*j :=by
 simp [install,applyBlock,Op.apply,writeNat,next,h.source,h.target,h.index,h.three,h.four,Nat.mul_comm]
lemma install_safe {m a d j B:ℕ} {heap:ℕ → Option ℕ} {s:State}
 (h:Invariant m a d j heap s) (hj:j  <  m) (sep:a+4*m ≤ d) (fit:d+3*m ≤ B):
 readable install s  ∧ peak install s ≤ B :=by
 have h3:3 ≤ B:=by omega
 have hs:a+j*4 ≤ B:=by omega
 have hd:d+j*3 ≤ B:=by omega
 simp [install,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  h.source,h.target,h.index,h.three,h.four,h3,hs,hd]

lemma advanced_invariant {m a d j:ℕ} {heap:ℕ → Option ℕ} {s u:State}
 (h:Invariant m a d j heap s) (hj:j  <  m)
 (copy:∀f,f  <  3 → u.natHeap (d+3*j+f)=s.natHeap (a+4*j+f))
 (out:UniformNatCopyMachine.Outside (d+3*j) 3 s.natHeap u)
 (nf:UniformNatCopyMachine.NatFrame s u) (sep:a+4*m ≤ d):
 Invariant m a d (j+1) heap (setPC (writeNat (setPC u 20) 3207 (j+1)) 4) :=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa [setPC,writeNat,next] using (nf 3200 (by omega)).trans h.count
 · simpa [setPC,writeNat,next] using (nf 3201 (by omega)).trans h.source
 · simpa [setPC,writeNat,next] using (nf 3202 (by omega)).trans h.target
 · simpa [setPC,writeNat,next] using (nf 3204 (by omega)).trans h.one
 · simpa [setPC,writeNat,next] using (nf 3205 (by omega)).trans h.three
 · simpa [setPC,writeNat,next] using (nf 3206 (by omega)).trans h.four
 · simp [setPC,writeNat,next]
 · intro i hi f hf
   change u.natHeap (d+3*i+f)=heap (a+4*i+f)
   by_cases eq:i=j
   · subst i
     rw [copy f hf,h.outside _ (Or.inl (by omega))]
   · rw [out _ (Or.inl (by omega))]
     exact h.copied i (by omega) f hf
 · intro i hi
   change u.natHeap i=heap i
   rw [out i (by rcases hi with hi|hi  <;>  omega)]
   exact h.outside i hi

/-- One actual record copy, including the nested copier and continuation. -/
theorem iteration (n:ℕ) (x:Fin n → ℂ) (m a d j B:ℕ) (heap:ℕ → Option ℕ) (s:State)
 (inv:Invariant m a d j heap s) (src:Source m a heap) (hj:j  <  m)
 (sep:a+4*m ≤ d) (fit:d+3*m ≤ B) (code:23 ≤ B) (pc:s.pc=4) (wb:WordBound B s):∃u,
 BoundedRuns projection n x B s 33 u  ∧ Invariant m a d (j+1) heap u  ∧ u.pc=4  ∧ Frame s u :=by
 let entered:=setPC s 5
 have eb:=changePC_bound B s 5 wb (by omega)
 have branch:BoundedRuns projection n x B s 1 entered:=.next wb
  (by simp [step,pc,branch_at,inv.index,inv.count,hj,entered,setPC]) (.refl eb)
 have safe:=install_safe inv hj sep fit
 have installed:=block_runs install projection 5 n B x entered install_code rfl eb
  (by rw [install_length];omega) safe.1 safe.2
 let ready:=setPC (applyBlock install entered) 0
 have rb:=changePC_bound B (applyBlock install entered) 0 installed.final_bound (by omega)
 have ri:Invariant m a d j heap ready:=(install_invariant inv.withPC).withPC
 have args:=install_args (s:=entered) (inv.withPC (pc:=5))
 have source:UniformNatCopyMachine.Source 3 (a+4*j) ready.natHeap:=by
  intro f hf
  obtain ⟨v,val⟩:=src j hj f hf
  exact ⟨v,(ri.outside _ (Or.inl (by omega))).trans val⟩
 obtain ⟨v,cr,copy,_old,out,cf,nf⟩:=UniformNatCopyMachine.execution n x 3 (a+4*j) (d+3*j) B ready
  source (by omega) (by omega) (by omega) rfl args.1 args.2.1 args.2.2 rb
 have placed:=UniformBoundedAssembly.boundedExecution_placed copy_code
  (by rw [UniformNatCopyMachine.program_length];omega) (by omega) cr
 have rp:(applyBlock install entered).pc=10:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,install_length];rfl
 rw [show UniformAssembly.placed 10 ready=applyBlock install entered from
  placed_zero _ _ rp] at placed
 let advanced:=writeNat (setPC v 20) 3207 (j+1)
 have ab:=writeNat_bound B (setPC v 20) 3207 (j+1) placed.final_bound (by change 21 ≤ B;omega) (by omega)
 have val:(setPC v 20).natReg 3207+(setPC v 20).natReg 3204=j+1:=by
  change v.natReg 3207+v.natReg 3204=j+1
  rw [nf _ (by omega),nf _ (by omega),ri.index,ri.one]
 have stepA:BoundedRuns projection n x B (setPC v 20) 1 advanced:=.next placed.final_bound
  (by simp only [step,show (setPC v 20).pc=20 from rfl,advance_at,evalNat,val];rfl) (.refl ab)
 let u:=setPC advanced 4
 have ub:=changePC_bound B advanced 4 ab (by omega)
 have ret:BoundedRuns projection n x B advanced 1 u:=.next ab
  (by simp [step,advanced,writeNat,next,setPC,jump_at,u]) (.refl ub)
 have af:Frame (setPC v 20) u:=by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i hi hj
  simp [u,advanced,setPC,writeNat,next,show i≠3207 by omega]
 have ff:Frame ready (setPC v 20):=⟨cf.1,cf.2.1,cf.2.2.1,cf.2.2.2,fun i hi _=> nf i hi⟩
 have inst:Frame s ready:=install_frame s
 refine ⟨u,?_,advanced_invariant ri hj copy out nf sep,rfl,inst.trans (ff.trans af)⟩
 convert branch.trans (installed.trans (placed.trans (stepA.trans ret))) using 1
 norm_num [install_length]

/-- Actual outer-loop induction; every nested three-word copy is charged. -/
theorem loop (n:ℕ) (x:Fin n → ℂ) (m a d j fuel B:ℕ) (heap:ℕ → Option ℕ) (s:State)
 (inv:Invariant m a d j heap s) (src:Source m a heap) (left:j+fuel=m)
 (sep:a+4*m ≤ d) (fit:d+3*m ≤ B) (code:23 ≤ B) (pc:s.pc=4) (wb:WordBound B s):∃u,
 BoundedRuns projection n x B s (33*fuel) u ∧ Invariant m a d m heap u ∧u.pc=4 ∧Frame s u :=by
 induction fuel generalizing j s with
 | zero=>
  have eq:j=m:=by omega
  subst j
  exact ⟨s,.refl wb,inv,pc,Frame.refl s⟩
 | succ fuel ih=>
  obtain ⟨u,first,ui,up,uf⟩:=iteration n x m a d j B heap s inv src (by omega) sep fit code pc wb
  obtain ⟨v,last,vi,vp,vf⟩:=ih (j+1) u ui (by omega) up first.final_bound
  refine ⟨v,?_,vi,vp,uf.trans vf⟩
  convert first.trans last using 1;omega
lemma boot_frame (s:State):Frame s (applyBlock boot s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i hi hj
 simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_invariant (m a d:ℕ) (s:State) (count:s.natReg 3200=m)
 (source:s.natReg 3201=a) (target:s.natReg 3202=d):Invariant m a d 0 s.natHeap (applyBlock boot s) :=by
 constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,count,source,target,Outside]
/-- A fixed literal projection of actual four-word axis records into the
three-word metadata schema. Dirty fresh destinations and unrelated banks are allowed. -/
theorem projection_execution (n:ℕ) (x:Fin n → ℂ) (m a d B:ℕ) (s:State)
 (source:Source m a s.natHeap) (sep:a+4*m ≤ d) (fit:d+3*m ≤ B) (code:23 ≤ B)
 (pc:s.pc=0) (count:s.natReg 3200=m) (src:s.natReg 3201=a) (dst:s.natReg 3202=d)
 (wb:WordBound B s):∃u,
 BoundedExecution projection n x B s (33*m+6) u ∧ u.pc=22 ∧
 (∀i,i < m → ∀f,f < 3 → u.natHeap (d+3*i+f)=s.natHeap (a+4*i+f)) ∧
 Outside d m s.natHeap u ∧ Frame s u :=by
 have read:readable boot s:=by simp [boot,readable,Op.readable]
 have peakB:peak boot s ≤ B:=by simp [boot,peak,Op.peak];omega
 have initialized:=block_runs boot projection 0 n B x s boot_code pc wb
  (by rw [boot_length];omega) read peakB
 have inv:=boot_invariant m a d s count src dst
 have bp:(applyBlock boot s).pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,boot_length,pc]
 obtain ⟨v,run,vi,vp,vf⟩:=loop n x m a d 0 m B s.natHeap (applyBlock boot s)
  inv source (by omega) sep fit code bp initialized.final_bound
 let u:=setPC v 22
 have ub:=changePC_bound B v 22 run.final_bound (by omega)
 have exit:BoundedRuns projection n x B v 1 u:=.next run.final_bound
  (by simp [step,vp,branch_at,vi.index,vi.count,u,setPC]) (.refl ub)
 have halt:BoundedExecution projection n x B u 1 u:=.halt ub
  (by simp [step,u,setPC,halt_at])
 refine ⟨u,?_,rfl,vi.copied,vi.outside,(boot_frame s).trans vf⟩
 convert initialized.executes (run.executes (exit.executes halt)) using 1
 simp only [boot_length];omega

abbrev metadataAxes (as:List UniformSectorPackingMachine.PhysicalAxis) :=
 as.map (fun a=>({geometry:=a.geometry,widthsBase:=a.widthsBase}:UniformSectorMetadataMachine.Axis))
lemma metadataAxes_geometry (as:List UniformSectorPackingMachine.PhysicalAxis):
 UniformSectorMetadataMachine.axes (metadataAxes as)=UniformSectorPackingMachine.physicalAxes as :=by
 simp [metadataAxes,UniformSectorMetadataMachine.axes,UniformSectorPackingMachine.physicalAxes,List.map_map,Function.comp_def]
lemma metadataAxes_length (as:List UniformSectorPackingMachine.PhysicalAxis):(metadataAxes as).length=as.length :=by
 simp [metadataAxes]
lemma metadataAxes_volume (as:List UniformSectorPackingMachine.PhysicalAxis):
 UniformSectorMetadataMachine.volume (metadataAxes as)=UniformSectorPackingMachine.physicalVolume as :=by
 simp only [UniformSectorMetadataMachine.volume,UniformSectorPackingMachine.physicalVolume,metadataAxes_geometry]

lemma rows_source (as:List UniformSectorPackingMachine.PhysicalAxis) (depth a:ℕ) (s:State)
 (rows:UniformSectorPackingMachine.Rows as depth a s):Source as.length (a+4*depth) s.natHeap :=by
 induction as generalizing depth with
 | nil=>simp [Source]
 | cons head tail ih=>
  rcases rows with ⟨h0,h1,h2,_h3,hr⟩
  intro i hi f hf
  by_cases iz:i=0
  · subst i;interval_cases f
    · exact ⟨head.geometry.widths.length,by simpa using h0⟩
    · exact ⟨head.widthsBase,by simpa [Nat.add_assoc] using h1⟩
    · exact ⟨head.geometry.widths.sum,by simpa [Nat.add_assoc] using h2⟩
  · have hi':i < tail.length+1:=by simpa only [List.length_cons] using hi
    have ii:i-1 < tail.length:=by omega
    obtain ⟨v,hv⟩:=ih (depth+1) hr (i-1) ii f hf
    refine ⟨v,?_⟩
    have addr:a+4*depth+4*i+f=a+4*(depth+1)+4*(i-1)+f:=by omega
    rw [addr];exact hv

lemma rows_project (as:List UniformSectorPackingMachine.PhysicalAxis) (depth a d:ℕ) (s u:State)
 (rows:UniformSectorPackingMachine.Rows as depth a s)
 (copied:∀i,i < as.length → ∀f,f < 3 → u.natHeap (d+3*(depth+i)+f)=s.natHeap (a+4*(depth+i)+f)):
 UniformSectorMetadataMachine.Rows (metadataAxes as) depth d u :=by
 induction as generalizing depth with
 | nil=>trivial
 | cons head tail ih=>
  rcases rows with ⟨h0,h1,h2,_h3,hr⟩
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨?_,?_,?_,ih (depth+1) hr ?_⟩
  · simpa only [Nat.add_zero] using (copied 0 (by simp) 0 (by decide)).trans h0
  · simpa only [Nat.add_zero] using (copied 0 (by simp) 1 (by decide)).trans h1
  · simpa only [Nat.add_zero] using (copied 0 (by simp) 2 (by decide)).trans h2
  · intro i hi f hf
    have cc:=copied (i+1) (by simp only [List.length_cons];omega) f hf
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cc

lemma widths_transfer (as:List UniformSectorPackingMachine.PhysicalAxis) (s u:State)
 (old:UniformSectorPackingMachine.Widths as s) (low:ℕ)
 (below:∀a∈as,a.widthsBase+a.geometry.widths.length ≤ low)
 (same:∀j,j < low → u.natHeap j=s.natHeap j):UniformSectorMetadataMachine.Widths (metadataAxes as) u :=by
 intro a ha j
 obtain ⟨b,hb,eq⟩:=List.mem_map.mp ha
 subst a
 have jj:j.val < b.geometry.widths.length:=j.isLt
 have h:=below b hb
 have lo:b.widthsBase+j.val < low:=by omega
 exact (same _ lo).trans (old b hb j)


/-- The axis count is loaded from the retained CRT header. High registers name
ordinary fresh allocations; sector counts and suffixes are produced physically. -/
def countSetup : List Op := [.literal 3210 1,.add 3200 102 3210]
def metadataSetup : List Op := [.literal 3216 0,.add 450 3200 3216,.add 451 3202 3216,
 .add 452 3213 3216,.add 453 3214 3216,.add 454 3215 3216]
def program : Program := countSetup.map Op.code ++ projection.map (relocate 2 25) ++
 metadataSetup.map Op.code ++ UniformSectorMetadataMachine.program.map (relocate 31 123) ++ [.halt]
lemma countSetup_length : countSetup.length=2 := rfl
lemma metadataSetup_length : metadataSetup.length=6 := rfl
lemma program_length : program.length=124 :=by
 simp only [program,List.length_append,List.length_map,countSetup_length,projection_length,
  metadataSetup_length,UniformSectorMetadataMachine.program_length,List.length_singleton]
lemma countSetup_code : BlockAt countSetup program 0 :=by
 intro i hi;change i < 2 at hi;interval_cases i <;> rfl
lemma projection_code : CodeAt projection program 2 25 :=by
 let after:=metadataSetup.map Op.code++UniformSectorMetadataMachine.program.map (relocate 31 123)++[.halt]
 have eq:program=countSetup.map Op.code++projection.map (relocate 2 25)++after:=by
  simp only [program,after,List.append_assoc]
 rw [eq]
 exact UniformRankCrossPreparationMachine.segment_code (countSetup.map Op.code) after
  projection 2 25 (by rw [List.length_map,countSetup_length])
lemma metadataSetup_code : BlockAt metadataSetup program 25 :=by
 intro i hi;change i < 6 at hi;interval_cases i <;> rfl
lemma metadata_code : CodeAt UniformSectorMetadataMachine.program program 31 123 :=by
 exact UniformRankCrossPreparationMachine.segment_code
  (countSetup.map Op.code++projection.map (relocate 2 25)++metadataSetup.map Op.code)
  [.halt] _ 31 123 (by simp only [List.length_append,List.length_map,countSetup_length,
   projection_length,metadataSetup_length])
lemma program_halt : program[123]?=some .halt :=by
 unfold program
 rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,countSetup_length,
  projection_length,metadataSetup_length,UniformSectorMetadataMachine.program_length];omega)]
 simp only [List.length_append,List.length_map,countSetup_length,projection_length,
  metadataSetup_length,UniformSectorMetadataMachine.program_length];rfl

/-- Exact scalar/root/output retention and the seven live CRT header registers. -/
def Retention (s u:State):Prop := u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 ∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i
lemma Retention.refl (s:State):Retention s s :=⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩
lemma Retention.trans {s u v:State} (h:Retention s u) (k:Retention u v):Retention s v :=
 ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,k.2.2.2.1.trans h.2.2.2.1,
  fun i hi hj=>(k.2.2.2.2 i hi hj).trans (h.2.2.2.2 i hi hj)⟩
lemma countSetup_retention (s:State):Retention s (applyBlock countSetup s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i hi hj
 simp (disch:=omega) [countSetup,applyBlock,Op.apply,writeNat,next]
lemma metadataSetup_retention (s:State):Retention s (applyBlock metadataSetup s) :=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩
 intro i hi hj
 simp (disch:=omega) [metadataSetup,applyBlock,Op.apply,writeNat,next]
lemma Frame.retention {s u:State} (h:Frame s u):Retention s u :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i hi hj=>h.2.2.2.2 i (by omega) (by omega)⟩
lemma metadata_retention {s u:State} (h:UniformSectorMetadataMachine.Frame s u):Retention s u :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i hi hj=>h.2.2.2.2 i (by omega)⟩
lemma countSetup_state (m a d:ℕ) (s:State) (hc:s.natReg 102+1=m)
 (ha:s.natReg 3201=a) (hd:s.natReg 3202=d):
 (applyBlock countSetup s).natReg 3200=m ∧(applyBlock countSetup s).natReg 3201=a ∧
 (applyBlock countSetup s).natReg 3202=d :=by
 simp [countSetup,applyBlock,Op.apply,writeNat,next,hc,ha,hd]
lemma metadataSetup_header (L:UniformSectorMetadataMachine.Layout) (s:State)
 (hc:s.natReg 3200=L.ell) (hr:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hd:s.natReg 3215=L.directory):
 UniformSectorMetadataMachine.Header L (applyBlock metadataSetup s) :=by
 constructor <;> simp [metadataSetup,applyBlock,Op.apply,writeNat,next,hc,hr,hs,ht,hd]
lemma metadataSetup_safe (L:UniformSectorMetadataMachine.Layout) (s:State)
 (hc:s.natReg 3200=L.ell) (hr:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hd:s.natReg 3215=L.directory):
 readable metadataSetup s ∧peak metadataSetup s ≤ L.B :=by
 have b0:=L.code;have b1:=L.rowsBelow;have b2:=L.suffixBelow;have b3:=L.stackBelow
 have b4:=L.directoryBound
 simp [metadataSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,hc,hr,hs,ht,hd]
 omega


/-- Only projected records, computed suffixes, DFS stack, and sector directory
may change in the Nat heap. All physical source banks outside these ranges remain. -/
def OutsideWork (L:UniformSectorMetadataMachine.Layout) (sectors:ℕ) (s u:State):Prop :=
 ∀j,(j < L.rows ∨ L.rows+3*L.ell ≤ j) →
  (j < L.suffix ∨ L.suffix+L.ell+1 ≤ j) →
  (j < L.stack ∨ L.stack+5*L.ell ≤ j) →
  (j < L.directory ∨ L.directory+3*sectors ≤ j) → u.natHeap j=s.natHeap j

/-- Continuous physical 4-to-3 schema projection followed by suffix production
and the complete multi-axis sector traversal. Actual axis rows and width banks
are entry data; generated rows, suffixes, sectors, and traversal safety are not. -/
theorem execution (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout) (n a:ℕ) (x:Fin n → ℂ) (s:State)
 (hlen:as.length=L.ell) (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows:UniformSectorPackingMachine.Rows as 0 a s) (widths:UniformSectorPackingMachine.Widths as s)
 (below:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (sep:a+4*L.ell ≤ L.rows) (code:124 ≤ L.B) (pc:s.pc=0)
 (count:s.natReg 102+1=L.ell) (ha:s.natReg 3201=a) (hd:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hq:s.natReg 3215=L.directory)
 (wb:WordBound L.B s):∃u,
 BoundedExecution program n x L.B s
  (UniformSectorMetadataMachine.treeCost (UniformSectorMetadataMachine.counts (metadataAxes as))+43*L.ell+31) u ∧
 u.pc=123 ∧UniformSectorMetadataMachine.Header L u ∧
 UniformSectorMetadataMachine.Directory L 0
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)) u ∧
 UniformSectorMetadataMachine.WrittenSuffix (metadataAxes as) L 0 u ∧
 Retention s u ∧(∀j,j < L.rows → u.natHeap j=s.natHeap j) ∧
 OutsideWork L (UniformSectorMetadataMachine.counts (metadataAxes as)).prod s u :=by
 have r0:=L.rowsBelow;have r1:=L.suffixBelow;have r2:=L.stackBelow;have r3:=L.directoryBound
 have fit:L.rows+3*L.ell ≤ L.B:=by omega
 have countSafe:readable countSetup s ∧peak countSetup s ≤ L.B:=by
  simp [countSetup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next]
  omega
 have first:=block_runs countSetup program 0 n L.B x s countSetup_code pc wb
  (by rw [countSetup_length];omega) countSafe.1 countSafe.2
 let ready:=setPC (applyBlock countSetup s) 0
 have rb:=changePC_bound L.B (applyBlock countSetup s) 0 first.final_bound (by omega)
 have args:=countSetup_state L.ell a L.rows s count ha hd
 have source:Source L.ell a ready.natHeap:=by
  simpa only [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next,Nat.mul_zero,Nat.add_zero,hlen]
   using rows_source as 0 a s rows
 obtain ⟨v,copyRun,vpc,copied,out,frame⟩:=projection_execution n x L.ell a L.rows L.B ready
  source sep fit (by omega) rfl args.1 args.2.1 args.2.2 rb
 have placedCopy:=UniformBoundedAssembly.boundedExecution_placed projection_code
  (by rw [projection_length];omega) (by omega) copyRun
 have firstpc:(applyBlock countSetup s).pc=2:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,countSetup_length,pc]
 rw [show placed 2 ready=applyBlock countSetup s from placed_zero _ _ firstpc] at placedCopy
 let afterCopy:=setPC v 25
 have vc:afterCopy.natReg 3200=L.ell:=(frame.2.2.2.2 3200 (by omega) (by omega)).trans args.1
 have vd:afterCopy.natReg 3202=L.rows:=(frame.2.2.2.2 3202 (by omega) (by omega)).trans args.2.2
 have vs:afterCopy.natReg 3213=L.suffix:=by
  rw [show afterCopy.natReg 3213=ready.natReg 3213 from frame.2.2.2.2 3213 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using hs
 have vt:afterCopy.natReg 3214=L.stack:=by
  rw [show afterCopy.natReg 3214=ready.natReg 3214 from frame.2.2.2.2 3214 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using ht
 have vq:afterCopy.natReg 3215=L.directory:=by
  rw [show afterCopy.natReg 3215=ready.natReg 3215 from frame.2.2.2.2 3215 (by omega) (by omega)]
  simpa [ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using hq
 have installed:=block_runs metadataSetup program 25 n L.B x afterCopy metadataSetup_code rfl
  placedCopy.final_bound (by rw [metadataSetup_length];omega)
  (metadataSetup_safe L afterCopy vc vd vs vt vq).1
  (metadataSetup_safe L afterCopy vc vd vs vt vq).2
 let metadataReady:=setPC (applyBlock metadataSetup afterCopy) 0
 have mb:=changePC_bound L.B (applyBlock metadataSetup afterCopy) 0 installed.final_bound (by omega)
 have mr:UniformSectorMetadataMachine.Rows (metadataAxes as) 0 L.rows metadataReady:=by
  apply rows_project as 0 a L.rows s metadataReady rows
  intro i hi f hf
  change v.natHeap (L.rows+3*(0+i)+f)=s.natHeap (a+4*(0+i)+f)
  simpa only [Nat.zero_add,ready,setPC,countSetup,applyBlock,Op.apply,writeNat,next] using copied i (by omega) f hf
 have low:∀j,j < L.rows → metadataReady.natHeap j=s.natHeap j:=by
  intro j hj
  exact out j (Or.inl hj)
 have mw:=widths_transfer as s metadataReady widths L.rows below low
 have mbelow:∀ax∈metadataAxes as,ax.widthsBase+ax.geometry.widths.length ≤ L.suffix:=by
  intro ax axin
  obtain ⟨b,hb,eq⟩:=List.mem_map.mp axin
  subst ax
  have bound:=below b hb
  exact bound.trans (by omega)
 obtain ⟨t,metaRun,_tpc,header,_constants,_cursor,directory,suffix,metaOutside,metaFrame⟩:=
  UniformSectorMetadataMachine.execution (metadataAxes as) L n x metadataReady
   (by rw [metadataAxes_length,hlen]) (by rw [metadataAxes_volume,hvolume])
   (UniformSectorMetadataMachine.header_setPC L _ 0 (metadataSetup_header L afterCopy vc vd vs vt vq)) mr mw mbelow rfl mb
 have placedMeta:=UniformBoundedAssembly.boundedExecution_placed metadata_code
  (by rw [UniformSectorMetadataMachine.program_length];omega) (by omega) metaRun
 have installedpc:(applyBlock metadataSetup afterCopy).pc=31:=by
  rw [UniformTensorMonomialMachine.applyBlock_pc,metadataSetup_length];rfl
 rw [show placed 31 metadataReady=applyBlock metadataSetup afterCopy from placed_zero _ _ installedpc]
  at placedMeta
 let u:=setPC t 123
 have halt:BoundedExecution program n x L.B u 1 u:=.halt placedMeta.final_bound
  (by simp [step,u,setPC,program_halt])
 have rcopy:Retention (applyBlock countSetup s) afterCopy:=frame.retention
 have rmeta:Retention (applyBlock metadataSetup afterCopy) u:=metadata_retention metaFrame
 have ret:Retention s u:=(countSetup_retention s).trans
  (rcopy.trans ((metadataSetup_retention afterCopy).trans rmeta))
 refine ⟨u,?_,rfl,UniformSectorMetadataMachine.header_setPC L t 123 header,?_,suffix,ret,?_,?_⟩
 · convert first.executes (placedCopy.executes (installed.executes (placedMeta.executes halt))) using 1
   simp only [countSetup_length,metadataSetup_length]
   omega
 · apply UniformSectorMetadataMachine.directory_transfer L 0 _ t u ?_ (fun _ _ _=>rfl)
   simpa only [metadataAxes_geometry] using directory
 · intro j hj
   exact (UniformSectorMetadataMachine.protected_prefix _ L metadataReady t metaOutside j (by omega)).trans (low j hj)
 · intro j jrows jsuffix jstack jdir
   exact (metaOutside j jsuffix (by simpa only [Nat.mul_comm] using jstack)
    (by simpa only [Nat.mul_comm] using jdir)).trans (out j jrows)


lemma execution_cost (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout) (hlen:as.length=L.ell)
 (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total):
 UniformSectorMetadataMachine.treeCost (UniformSectorMetadataMachine.counts (metadataAxes as))+43*L.ell+31
 ≤ 163*L.total+31 :=by
 have h:=UniformSectorMetadataMachine.execution_cost (metadataAxes as) L
  (by rw [metadataAxes_length,hlen]) (by rw [metadataAxes_volume,hvolume])
 have dims:=UniformSectorPackingMachine.axis_count_bound as
 rw [hlen,hvolume] at dims
 omega

lemma source_rows_retained (as:List UniformSectorPackingMachine.PhysicalAxis) (depth a low:ℕ)
 (s u:State) (h:UniformSectorPackingMachine.Rows as depth a s)
 (bound:a+4*(depth+as.length) ≤ low) (same:∀j,j < low → u.natHeap j=s.natHeap j):
 UniformSectorPackingMachine.Rows as depth a u :=by
 induction as generalizing depth with
 | nil=>trivial
 | cons ax tail ih=>
  rcases h with ⟨h0,h1,h2,h3,hr⟩
  have b:a+4*depth+3 < low:=by simp only [List.length_cons] at bound;omega
  refine ⟨(same _ (by omega)).trans h0,(same _ (by omega)).trans h1,
   (same _ (by omega)).trans h2,(same _ b).trans h3,ih (depth+1) hr ?_⟩
  simp only [List.length_cons] at bound
  omega
lemma physical_widths_retained (as:List UniformSectorPackingMachine.PhysicalAxis) (low:ℕ)
 (s u:State) (h:UniformSectorPackingMachine.Widths as s)
 (bound:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ low)
 (same:∀j,j < low → u.natHeap j=s.natHeap j):UniformSectorPackingMachine.Widths as u :=by
 intro ax ha j
 exact (same _ (by have b:=bound ax ha;have ji:=j.isLt;omega)).trans (h ax ha j)
lemma physical_permutations_retained (as:List UniformSectorPackingMachine.PhysicalAxis) (low:ℕ)
 (s u:State) (h:UniformSectorPackingMachine.Permutations as s)
 (bound:∀ax∈as,ax.permutationBase+ax.geometry.widths.sum ≤ low)
 (same:∀j,j < low → u.natHeap j=s.natHeap j):UniformSectorPackingMachine.Permutations as u :=by
 intro ax ha j
 exact (same _ (by have b:=bound ax ha;have ji:=j.isLt;omega)).trans (h ax ha j)
lemma retained_metadata {n:ℕ} {s u:State} (h:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retention s u) (low:ℕ)
 (bound:UniformInitialPreparation.copyBase n+
  UniformGlobalNatPreparation.amount (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) ≤ low)
 (same:∀j,j < low → u.natHeap j=s.natHeap j):UniformPermutationInversePreparation.Metadata n u :=by
 have saved:UniformGlobalNatPreparation.SavedHeaders (UniformWorkingLength.nextPrime n)
  n (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) (UniformMasterRootMachine.order n) u :=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (ret.2.2.2.2 100 (by decide) (by decide)).trans h.saved.nextPrime
  · exact (ret.2.2.2.2 101 (by decide) (by decide)).trans h.saved.inputLength
  · exact (ret.2.2.2.2 102 (by decide) (by decide)).trans h.saved.count
  · exact (ret.2.2.2.2 103 (by decide) (by decide)).trans h.saved.workingLength
  · exact (ret.2.2.2.2 104 (by decide) (by decide)).trans h.saved.masterRoot
  · exact (ret.2.2.2.2 105 (by decide) (by decide)).trans h.saved.copyAddress
  · exact (ret.2.2.2.2 106 (by decide) (by decide)).trans h.saved.copyLength
 exact h.transport_saved saved (fun j hj=>same _ (by omega))

/-- Genuine retained-CRT entry specialization. All valid physical axis records
are provided by the matching producer; whole suffix/directory/readiness/action
certificates are absent. Positive-length selected radices are all at least two,
as proved below; the all-axis physical matching producer remains separate. -/
theorem metadata_execution (as:List UniformSectorPackingMachine.PhysicalAxis)
 (L:UniformSectorMetadataMachine.Layout) (n a:ℕ) (x:Fin n → ℂ) (s:State)
 (hm:UniformPermutationInversePreparation.Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
 (hlen:as.length=L.ell) (hcount:L.ell=UniformAllAxisSeedPreparation.axisCount n)
 (hvolume:UniformSectorPackingMachine.physicalVolume as=L.total)
 (rows:UniformSectorPackingMachine.Rows as 0 a s) (widths:UniformSectorPackingMachine.Widths as s)
 (perms:UniformSectorPackingMachine.Permutations as s)
 (below:∀ax∈as,ax.widthsBase+ax.geometry.widths.length ≤ L.rows)
 (pbelow:∀ax∈as,ax.permutationBase+ax.geometry.widths.sum ≤ L.rows)
 (protectedBound:UniformInitialPreparation.copyBase n+
  UniformGlobalNatPreparation.amount (UniformInitialPreparation.ell n) (UniformInitialPreparation.len n) ≤ L.rows)
 (sep:a+4*L.ell ≤ L.rows) (code:124 ≤ L.B) (pc:s.pc=0)
 (ha:s.natReg 3201=a) (hd:s.natReg 3202=L.rows)
 (hs:s.natReg 3213=L.suffix) (ht:s.natReg 3214=L.stack) (hq:s.natReg 3215=L.directory)
 (wb:WordBound L.B s):∃u,
 BoundedExecution program n x L.B s
  (UniformSectorMetadataMachine.treeCost (UniformSectorMetadataMachine.counts (metadataAxes as))+43*L.ell+31) u ∧
 u.pc=123 ∧UniformSectorMetadataMachine.Header L u ∧
 UniformSectorMetadataMachine.Directory L 0
  (UniformSectorPacking.sectorStates (UniformSectorPackingMachine.physicalAxes as)) u ∧
 UniformSectorMetadataMachine.WrittenSuffix (metadataAxes as) L 0 u ∧
 UniformPermutationInversePreparation.Metadata n u ∧UniformInitialPreparation.Operands n x u ∧
 UniformSectorPackingMachine.Rows as 0 a u ∧UniformSectorPackingMachine.Widths as u ∧
 UniformSectorPackingMachine.Permutations as u ∧Retention s u ∧
 (∀j,j < L.rows → u.natHeap j=s.natHeap j) ∧
 OutsideWork L (UniformSectorMetadataMachine.counts (metadataAxes as)).prod s u :=by
 have hc:s.natReg 102+1=L.ell:=by rw [hm.saved.count,hcount]
 obtain ⟨u,run,up,header,dir,suffix,ret,low,outside⟩:=execution as L n a x s hlen hvolume rows widths below
  sep code pc hc ha hd hs ht hq wb
 exact ⟨u,run,up,header,dir,suffix,retained_metadata hm ret L.rows protectedBound low,
  ho.transport ret.1,source_rows_retained as 0 a L.rows s u rows (by rw [hlen];omega) low,
  physical_widths_retained as L.rows s u widths below low,
  physical_permutations_retained as L.rows s u perms pbelow low,ret,low,outside⟩


/-- The odd maximal product cannot equal the even threshold for positive n. -/
lemma oddProduct_lt_threshold {n:ℕ} (hn:0 < n):UniformWorkingLength.oddProduct n < 2*n :=by
 have h:= (UniformWorkingLength.maximal_product hn).1
 obtain ⟨k,hk⟩:=UniformWorkingLength.primeProduct_odd (UniformWorkingLength.axisCount n)
 change UniformWorkingLength.oddProduct n=2*k+1 at hk
 omega
/-- Although the generic selected-factor syntax allows a width-one binary
factor, the actual positive-length startup never selects one. -/
lemma selected_binary_two {n:ℕ} (hn:0 < n):2 ≤ UniformWorkingLength.binaryFactor n :=by
 have oddBound:=oddProduct_lt_threshold hn
 have factorPos:0 < UniformWorkingLength.binaryFactor n:=by
  exact pow_pos (by decide) _
 have work:=UniformWorkingLength.workingLength_lower n
 change 2*n ≤ UniformWorkingLength.oddProduct n*UniformWorkingLength.binaryFactor n at work
 by_contra no
 have one:UniformWorkingLength.binaryFactor n=1:=by omega
 rw [one,Nat.mul_one] at work
 omega
lemma selected_radix_two {n:ℕ} (hn:0 < n)
 (j:Fin (UniformAllAxisSeedPreparation.axisCount n)):2 ≤ UniformSelectedCRT.radices n j :=by
 refine Fin.lastCases ?_ (fun i=>?_) j
 · simpa only [UniformSelectedCRT.radices,Fin.snoc_last] using selected_binary_two hn
 · have h:=UniformWorkingLength.oddPrime_gt_two i.val
   simpa only [UniformSelectedCRT.radices,Fin.snoc_castSucc] using h.le

end
end ExactFourierCircuits.UniformMultiAxisSectorMetadataPreparation
