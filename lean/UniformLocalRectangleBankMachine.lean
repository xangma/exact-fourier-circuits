import UniformLocalCacheTreeCoverage
import UniformSeedEdgeRetention

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleBankMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformWorkspacePlanner UniformBalancedToeplitz
open UniformAllAxisSeedPreparation (axisCount radix Retained)

/-- Source is the actual seven-word row written by the forest printer. -/
def RowSource (D : ℕ) (q : Row) (s : State) : Prop :=
 ∀f:Fin 7,s.natHeap (D+f.val)=some (q.words[f.val]'f.isLt)

def geometry (q : Row) (work : UniformSeedHeightPreparation.Config) :
 UniformSeedHeightPreparation.Config :=
 {work with a:=q.a,e:=q.e,split:=q.split,i0:=q.i0,j0:=q.j0}

/-- Axis/cell headers are ordinary integers. Kernel geometry is loaded from
the physically emitted row; its subtree offset is not added to h/g indices. -/
def install : List Op := [.literal 4202 0,.literal 4203 1,.add 1120 4200 4202,
 .add 4204 4201 4202,.getNat 4205 4204,.add 4204 4204 4203,
 .getNat 4206 4204,.add 4204 4204 4203,.getNat 1122 4204,.add 4204 4204 4203,
 .getNat 1123 4204,.add 4204 4204 4203,.getNat 1126 4204,.add 4204 4204 4203,
 .getNat 1124 4204,.add 4204 4204 4203,.getNat 1125 4204]
def program : Program := install.map Op.code++
 UniformSeedHeightPreparation.program.map (relocate 17 1063)++[.halt]
lemma install_length : install.length=17 := rfl
lemma program_length : program.length=1064 := by
 simp only [program,List.length_append,List.length_map,install_length,
  UniformSeedHeightPreparation.program_length];rfl
lemma install_code : BlockAt install program 0 := by
 intro i hi
 change i<17 at hi
 interval_cases i <;>rfl

lemma seed_code : CodeAt UniformSeedHeightPreparation.program program 17 1063 :=
 UniformRankCrossPreparationMachine.segment_code (install.map Op.code) [.halt]
  UniformSeedHeightPreparation.program 17 1063 (by rw [List.length_map,install_length])
lemma halt_at : program[1063]?=some .halt := by
 rw [program,List.getElem?_append_right (by rw [List.length_append,List.length_map,
  List.length_map,install_length,UniformSeedHeightPreparation.program_length])]
 simp only [List.length_append,List.length_map,install_length,
  UniformSeedHeightPreparation.program_length]
 rfl

lemma rows_geometry (v o : ℕ) (q : Row) (hn:2 ≤ v) (hv:0<selected v)
 (hq:q ∈ rows v o (selected v)) :
 0<q.a ∧ 0<q.e ∧ q.i0+q.a ≤ v ∧ q.split<v ∧ q.split ≤ q.i0 ∧
 q.j0+q.e ≤ q.split ∧ gateCount q.a q.e+q.a+q.e ≤ v ∧ q.width=v ∧ q.offset=o := by
 rw [rows_pairs] at hq
 obtain ⟨p,_,rfl⟩:=List.mem_map.mp hq
 let request:=UniformLocalPreparationDAG.pairRequest hn hv (le_refl v) p
 have fit:=selected_fit hv (size_mem _ _ p.1) (size_mem _ _ p.2)
 exact ⟨request.positive,request.sourcePositive,request.hBound,request.gBound,
  request.interior,request.sourceBound,fit,rfl,rfl⟩

noncomputable section
def Args {n : ℕ} (j:Fin (axisCount n)) (D:ℕ)
 (work:UniformSeedHeightPreparation.Config) (s:State) : Prop :=
 s.natReg 4200=j.val ∧ s.natReg 4201=D ∧
 (∀r,1127 ≤ r → r ≤ 1137 → s.natReg r=work.register r) ∧
 (∀r,1220 ≤ r → r ≤ 1224 → s.natReg r=work.register r)

lemma install_source {D : ℕ} {q : Row} {s:State} (source:RowSource D q s)
 (address:s.natReg 4201=D) :
 (applyBlock install s).natReg 4205=q.width ∧
 (applyBlock install s).natReg 4206=q.offset ∧
 (applyBlock install s).natReg 1122=q.a ∧
 (applyBlock install s).natReg 1123=q.e ∧
 (applyBlock install s).natReg 1126=q.split ∧
 (applyBlock install s).natReg 1124=q.i0 ∧
 (applyBlock install s).natReg 1125=q.j0 := by
 have h0:s.natHeap D=some q.width:=by simpa [Row.words] using source ⟨0,by decide⟩
 have h1:s.natHeap (D+1)=some q.offset:=by simpa [Row.words] using source ⟨1,by decide⟩
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h4:s.natHeap (D+4)=some q.split:=by simpa [Row.words] using source ⟨4,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 simp [install,applyBlock,Op.apply,writeNat,next,address,Nat.add_assoc,h0,h1,h2,h3,h4,h5,h6]

lemma install_keeps (s:State) (r:ℕ)
 (notWrite:r ∉ [4202,4203,1120,4204,4205,4206,1122,1123,1126,1124,1125]) :
 (applyBlock install s).natReg r=s.natReg r := by
 apply UniformSeedRankCrossPreparation.block_register_keeps
 intro o ho
 simp only [install,List.mem_cons,List.not_mem_nil,or_false] at ho
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at notWrite
 rcases notWrite with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp [UniformSeedRankCrossPreparation.KeepsRegister,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

lemma geometry_register (q:Row) (work:UniformSeedHeightPreparation.Config)
 (r:ℕ) (lo:1127 ≤ r) (hi:r ≤ 1137) :
 (geometry q work).register r=work.register r := by
 interval_cases r <;>rfl

lemma install_args {n:ℕ} (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (work:UniformSeedHeightPreparation.Config) (s:State) (args:Args j D work s)
 (source:RowSource D q s) :
 UniformSeedHeightPreparation.Args n j (geometry q work) (applyBlock install s) := by
 rcases install_source source args.2.1 with ⟨hw,ho,ha,he,hb,hi,hj⟩
 refine ⟨?_,?_,?_⟩
 · simp [install,applyBlock,Op.apply,writeNat,next,args.1]
 · intro r lo up
   by_cases low:r<1127
   · interval_cases r
     · exact ha
     · exact he
     · exact hi
     · exact hj
     · exact hb
   · have keep:=install_keeps s r (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)
     rw [keep,args.2.2.1 r (by omega) up,geometry_register q work r (by omega) up]
 · intro r lo hi
   have keep:=install_keeps s r (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)
   rw [keep,args.2.2.2 r lo hi]
   interval_cases r <;>rfl

lemma install_safe {n D B:ℕ} {q:Row} (j:Fin (axisCount n))
 (work:UniformSeedHeightPreparation.Config) (s:State) (args:Args j D work s)
 (source:RowSource D q s) (hs:WordBound B s) (endRow:D+6 ≤ B) (_one:1 ≤ B) :
 readable install s ∧ peak install s ≤ B := by
 have h0:s.natHeap D=some q.width:=by simpa [Row.words] using source ⟨0,by decide⟩
 have h1:s.natHeap (D+1)=some q.offset:=by simpa [Row.words] using source ⟨1,by decide⟩
 have h2:s.natHeap (D+2)=some q.a:=by simpa [Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (D+3)=some q.e:=by simpa [Row.words] using source ⟨3,by decide⟩
 have h4:s.natHeap (D+4)=some q.split:=by simpa [Row.words] using source ⟨4,by decide⟩
 have h5:s.natHeap (D+5)=some q.i0:=by simpa [Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (D+6)=some q.j0:=by simpa [Row.words] using source ⟨6,by decide⟩
 have b0:=(hs.2.2.1 _ _ h0).2
 have b1:=(hs.2.2.1 _ _ h1).2
 have b2:=(hs.2.2.1 _ _ h2).2
 have b3:=(hs.2.2.1 _ _ h3).2
 have b4:=(hs.2.2.1 _ _ h4).2
 have b5:=(hs.2.2.1 _ _ h5).2
 have b6:=(hs.2.2.1 _ _ h6).2
 have axis:=hs.2.1 4200
 simp [install,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,args.2.1,
  Nat.add_assoc,h0,h1,h2,h3,h4,h5,h6]
 omega

lemma install_frame {n:ℕ} (s:State) :
 UniformSeedRankCrossPreparation.PreservedFrame n s (applyBlock install s) := by
 refine ⟨fun _ _=>rfl,fun _ _=>rfl,?_,rfl,rfl⟩
 intro r lo hi
 exact install_keeps s r (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega)

/-- Opaque execution boundary avoids duplicating the17-write State in the
large dependent producer contracts. It is definitionally the real block. -/
def loadedState (s:State) : State := applyBlock install s
lemma loadedState_eq (s:State) : loadedState s=applyBlock install s := rfl
attribute [irreducible] loadedState
lemma loadedState_natHeap (s:State) : (loadedState s).natHeap=s.natHeap := by
 rw [loadedState_eq];rfl
lemma loadedState_scalarHeap (s:State) : (loadedState s).scalarHeap=s.scalarHeap := by
 rw [loadedState_eq];rfl
lemma reset_frame {n:ℕ} (s:State) (pc:ℕ) :
 UniformSeedRankCrossPreparation.PreservedFrame n s (setPC s pc) :=
 ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl,rfl,rfl⟩

lemma startup {n:ℕ} (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (work:UniformSeedHeightPreparation.Config) (B:ℕ) (x:Fin n→ℂ) (s:State)
 (args:Args j D work s) (source:RowSource D q s)
 (endRow:D+6 ≤ B) (code:1064 ≤ B) (pc:s.pc=0) (hs:WordBound B s) :
 BoundedRuns program n x B s 17 (loadedState s) ∧ (loadedState s).pc=17 ∧
 UniformSeedHeightPreparation.Args n j (geometry q work) (loadedState s) ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s (loadedState s) := by
 rw [loadedState_eq]
 have safe:=install_safe j work s args source hs endRow (by omega)
 have run:=block_runs install program 0 n B x s install_code pc hs
  (by rw [install_length];omega) safe.1 safe.2
 refine ⟨?_,?_,install_args j D q work s args source,install_frame s⟩
 · simpa only [install_length] using run
 · rw [applyBlock_pc,pc,install_length]

/-- One continuous physical row reader and actual1046 producer. No exponent,
kernel, spectra, sorted order, colors, or later-phase ready table is supplied. -/
theorem execution {n:ℕ} (hn:0<n) (j:Fin (axisCount n)) (D:ℕ) (q:Row)
 (work:UniformSeedHeightPreparation.Config) (B:ℕ) (x:Fin n→ℂ) (s:State)
 (args:Args j D work s) (source:RowSource D q s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
 (layout:UniformSeedHeightPreparation.Layout n j (geometry q work) B)
 (endRow:D+6 ≤ B) (code:1064 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧
 t ≤ UniformSeedHeightPreparation.runtimeBudget n j (geometry q work)+18 ∧ u.pc=1063 ∧
 UniformSeedHeightPreparation.Result n j (geometry q work) B (layout.replay hn j (geometry q work) B) u ∧
 Retained n (axisCount n) u ∧ UniformPermutationInversePreparation.Metadata n u ∧
 UniformInitialPreparation.Operands n x u ∧ UniformSeedRankCrossPreparation.PreservedFrame n s u ∧
 UniformSeedEdgeRetention.Height.Outside n j (geometry q work) s u := by
 obtain ⟨start,ap,ia,frame⟩:=startup j D q work B x s args source endRow code pc hs
 let a:=loadedState s
 let entry:=setPC a 0
 have eb:=changePC_bound B a 0 start.final_bound (by omega)
 have entryFrame:=frame.trans (reset_frame a 0)
 obtain ⟨v,t,run,time,vp,result,_,_,_,last,outside⟩:=UniformSeedEdgeRetention.Height.execution hn j
  (geometry q work) B x entry ia (entryFrame.protected.metadata metadata)
  (entryFrame.retained ret) (entryFrame.protected.operands ops) layout rfl eb
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedHeightPreparation.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero a 17 ap] at placedRun
 let u:=setPC v 1063
 have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
  (by simp [step,u,setPC,halt_at])
 have allFrame:UniformSeedRankCrossPreparation.PreservedFrame n s u:=entryFrame.trans last
 refine ⟨u,17+t+1,?_,by omega,rfl,⟨result.source.withPC,result.cursor.withPC,result.processed,result.positive,result.root,
  result.negative,result.constants⟩,allFrame.retained ret,
  allFrame.protected.metadata metadata,allFrame.protected.operands ops,allFrame,?_,?_⟩
 · exact start.executes (placedRun.executes stop)
 · intro r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
   exact (outside.1 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9).trans
    (congrFun (loadedState_natHeap s) r)
 · intro r h0 h1 h2 h3 h4
   exact (outside.2 r h0 h1 h2 h3 h4).trans
    (congrFun (loadedState_scalarHeap s) r)

end
end ExactFourierCircuits.UniformLocalRectangleBankMachine
