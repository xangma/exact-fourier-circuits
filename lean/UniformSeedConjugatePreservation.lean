import UniformHighDataConjugateMatchingPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedConjugatePreservation
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformPairMachine (prepared)
open UniformAllAxisSeedPreparation (axisCount radix axisBase directoryBase Retained)
open OAI.ExactFourier
noncomputable section

/-- Exact prefixes preserved by the real producer. These are address geometry,
not supplied coefficient values or a ready generated-table certificate. -/
structure PrefixFrame (P Q : ℕ) (s u : State) : Prop where
 scalar : ∀i,i<P→u.scalarHeap i=s.scalarHeap i
 nat : ∀i,i<Q→u.natHeap i=s.natHeap i

structure Fresh (P Q : ℕ) (c : UniformSeedRankCrossPreparation.Config) : Prop where
 row : Q≤c.d
 convolution : Q≤c.conv
 tape : Q≤c.tape
 depth : Q≤c.depth
 order : Q≤c.order
 directory : Q≤c.directory
 kernels : P≤c.S
 fft : P≤c.A
 positive : P≤c.C
 negative : P≤c.negative
 constants : P≤c.constants

namespace Rank
open UniformSeedRankCrossPreparation
theorem execution {n : ℕ} (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (x : Fin n→ℂ) (s : State) (args:Args n j c s)
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
    (layout:UniformRankCrossReplayPreparationMachine.ReplayLayout (parameters n j c) B)
    (fresh:UniformSeedRankCrossPreparation.Fresh n c) (P Q : ℕ) (extra:UniformSeedConjugatePreservation.Fresh P Q c) (pc:s.pc=0) (hs:WordBound B s) (hB:835 ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ runtimeBudget n j c ∧ u.pc=834 ∧
    UniformRankCrossReplayPreparationMachine.PreparedReplay (parameters n j c) B layout
      (hValue n j) (gValue n j) u ∧ Retained n (axisCount n) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    PreservedFrame n s u ∧ PrefixFrame P Q s u := by
  have safe:=sourceSetup_safe j c s B args metadata ret layout hs
  have first:=block_runs sourceSetup program 0 n B x s sourceSetup_code pc hs
    (by rw [sourceSetup_length];omega) safe.1 safe.2
  let loaded:=applyBlock sourceSetup s
  have head:=sourceSetup_loaded j c s args metadata ret
  have lp:loaded.pc=18:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,sourceSetup_length]
  have installSafe:=headerSetup_safe j c loaded B head first.final_bound
  have second:=block_runs headerSetup program 18 n B x loaded headerSetup_code lp first.final_bound
    (by rw [headerSetup_length];omega) installSafe.1 installSafe.2
  let installed:=applyBlock headerSetup loaded
  have installedPC:installed.pc=35:=by rw [UniformTensorMonomialMachine.applyBlock_pc,lp,headerSetup_length]
  have installedHeaders:=headerSetup_spec j c loaded head
  let entry:=setPC installed 0
  have eb:=changePC_bound B installed 0 second.final_bound (by omega)
  have entryH:UniformRankKernelMachine.Bank (parameters n j c).base.H (parameters n j c).base.hSize
      (hValue n j) entry:=retained_h ret j
  have entryG:UniformRankKernelMachine.Bank (parameters n j c).base.G (parameters n j c).base.gSize
      (gValue n j) entry:=retained_g ret j
  have master:entry.scalarHeap 0=some (prepared (zeta (parameters n j c).base.D)):=by
    change s.scalarHeap 0=some (prepared (zeta (UniformMasterRootMachine.order n)))
    exact operands_master ops
  obtain ⟨v,t,run,tc,vp,post,frame⟩:=UniformRankCrossReplayPreparationMachine.execution
    (parameters n j c) B n layout (hValue n j) (gValue n j) x entry
    (installedHeaders.1.withPC 0) (installedHeaders.2.withPC 0) entryH entryG master rfl eb
  have placedRun:=UniformBoundedAssembly.boundedExecution_placed replay_code
    (by rw [UniformRankCrossReplayPreparationMachine.program_length];omega) (by omega) run
  have placedEq:placed 35 entry=installed:=placed_zero installed 35 installedPC
  rw [placedEq] at placedRun
  let u:=setPC v 834
  have stop:BoundedExecution program n x B u 1 u:=.halt placedRun.final_bound
    (by simp [step,u,setPC,halt_at])
  have total:BoundedExecution program n x B s (t+36) u:=by
    convert first.executes (second.executes (placedRun.executes stop)) using 1
    simp only [sourceSetup_length,headerSetup_length];omega
  have startFrame:=SetupFrame.trans (sourceSetup_frame s) (headerSetup_frame loaded)
  have finalFrame:PreservedFrame n s u:=startFrame.preserved.trans (replay_frame j c fresh frame)
  have pref:PrefixFrame P Q s u:=by
    constructor
    · intro q hq
      change v.scalarHeap q=s.scalarHeap q
      have eq:=frame.scalar q (Or.inl (lt_of_lt_of_le hq extra.kernels))
        (Or.inl (lt_of_lt_of_le hq extra.fft)) (Or.inl (lt_of_lt_of_le hq extra.positive))
        (Or.inl (lt_of_lt_of_le hq extra.negative)) (Or.inl (lt_of_lt_of_le hq extra.constants))
      exact eq
    · intro q hq
      change v.natHeap q=s.natHeap q
      exact frame.nat q (Or.inl (lt_of_lt_of_le hq extra.row))
        (Or.inl (lt_of_lt_of_le hq extra.convolution)) (Or.inl (lt_of_lt_of_le hq extra.tape))
        (Or.inl (lt_of_lt_of_le hq extra.depth)) (Or.inl (lt_of_lt_of_le hq extra.order))
        (Or.inl (lt_of_lt_of_le hq extra.directory))
  refine ⟨u,t+36,total,by unfold runtimeBudget;omega,rfl,
    ⟨post.toBasePost.withPC 834,post.buckets.withPC 834,post.negative,post.constants⟩,
    finalFrame.retained ret,finalFrame.protected.metadata metadata,
    finalFrame.protected.operands ops,finalFrame,pref⟩

end Rank

namespace Height
open UniformSeedHeightPreparation
theorem execution {n : ℕ} (hn:0<n) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
 (x : Fin n→ℂ) (s : State) (args:Args n j c s)
 (metadata:UniformPermutationInversePreparation.Metadata n s)
 (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
 (h:Layout n j c B) (P Q : ℕ) (extra:Fresh P Q c.seed) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
 BoundedExecution program n x B s t u ∧ t≤runtimeBudget n j c ∧ u.pc=1045 ∧
 Result n j c B (h.replay hn j c B) u ∧ Retained n (axisCount n) u ∧
 UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
 UniformSeedRankCrossPreparation.PreservedFrame n s u ∧ PrefixFrame P Q s u := by
 have hc:=h.codeBound
 let layout:=h.replay hn j c B
 obtain ⟨v,first,vp,vc,vf⟩:=sizing_initialized j c B x s args pc hs h.width_bound (by omega)
 let seedEntry:=setPC v 0
 have eb:WordBound B seedEntry:=changePC_bound B v 0 first.final_bound (by omega)
 have seedArgs:UniformSeedRankCrossPreparation.Args n j c.seed seedEntry:=
  sizing_args j c args (vc.withPC 0) (vf.trans (SizingFrame.withPC v 0))
 have startFrame:UniformSeedRankCrossPreparation.PreservedFrame n s seedEntry:=
  (vf.trans (SizingFrame.withPC v 0)).preserved
 obtain ⟨w,t,seedRun,seedCost,wp,post,_,_,_,seedFrame,pref⟩:=
  Rank.execution j c.seed B x seedEntry seedArgs
   (startFrame.protected.metadata metadata) (startFrame.retained ret)
   (startFrame.protected.operands ops) layout h.oldBanks P Q extra rfl eb (by omega)
 have seedPlaced:=UniformBoundedAssembly.boundedExecution_placed seed_code
  (by rw [UniformSeedRankCrossPreparation.program_length];omega) (by omega) seedRun
 have entered:placed 11 seedEntry=v:=UniformSeedRankCrossPreparation.placed_zero v 11 vp
 rw [entered] at seedPlaced
 let afterSeed:=setPC w 846
 have oldArgs:∀q,1220≤q→q≤1224→afterSeed.natReg q=c.register q:=by
  intro q hq hq'
  exact (execution_highNat seed_ceiling seedRun q hq).trans
   ((vf.2.2.2.2.2 q (by omega) (by omega)).trans (args.2.2 q hq hq'))
 have post':UniformRankCrossReplayPreparationMachine.PreparedReplay (parameters n j c) B layout
   (UniformSeedRankCrossPreparation.hValue n j) (UniformSeedRankCrossPreparation.gValue n j) afterSeed:=
  ⟨post.toBasePost.withPC 846,post.buckets.withPC 846,post.negative,post.constants⟩
 have safe:=heightSetup_safe j c B layout afterSeed post' seedPlaced.final_bound
 have install:=block_runs heightSetup program 846 n B x afterSeed heightSetup_code rfl
  seedPlaced.final_bound (by rw [heightSetup_length];omega) safe.1 safe.2
 let installed:=applyBlock heightSetup afterSeed
 have ip:installed.pc=859:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have header:=heightSetup_spec j c B layout afterSeed post' oldArgs
 let heightEntry:=setPC installed 0
 have ih:WordBound B heightEntry:=changePC_bound B installed 0 install.final_bound (by omega)
 have source:UniformCrossHeightPreparationMachine.Source c.height
   (UniformRankCrossReplayPreparationMachine.cross (parameters n j c) layout).program heightEntry:=by
  have old:=height_source j c B layout post'
  refine ⟨?_,?_,?_⟩
  · intro q hq;exact old.bank q hq
  · intro q hq;exact old.directory q hq
  · intro q hq;exact old.tape q hq
 have tape:UniformToeplitzCrossTopologyMachine.RowTable
   (UniformToeplitzCrossTopologyMachine.crossRows c.exponent c.a c.e) c.tape heightEntry:=by
  rw [UniformToeplitzCrossTopologyMachine.crossRows_typed c.exponent c.a c.e (widths c).1 (widths c).2]
  exact source.tape
 obtain ⟨z,ticks,heightRun,heightCost,zp,cursor,finalSource,processed,outside,frame⟩:=
  UniformCrossHeightPreparationMachine.cross_execution c.height c.negative B n (widths c).1 (widths c).2
   x heightEntry (header.withPC 0) rfl ih h.heightLayout h.heightEnvelope source.bank source.directory tape
 have heightPlaced:=UniformBoundedAssembly.boundedExecution_placed height_code
  (by rw [UniformCrossHeightPreparationMachine.program_length];omega) (by omega) heightRun
 have enteredHeight:placed 859 heightEntry=installed:=UniformSeedRankCrossPreparation.placed_zero installed 859 ip
 rw [enteredHeight] at heightPlaced
 let u:=setPC z 1045
 have stop:BoundedExecution program n x B u 1 u:=.halt heightPlaced.final_bound
  (by simp [step,u,setPC,halt_at])
 have all:BoundedExecution program n x B s (4*c.exponent+8+t+13+ticks+1) u:=by
  convert first.executes (seedPlaced.executes (install.executes (heightPlaced.executes stop))) using 1
  rw [heightSetup_length];omega
 have middle:UniformSeedRankCrossPreparation.PreservedFrame n s installed:=
  startFrame.trans (seedFrame.trans (heightSetup_frame afterSeed).preserved)
 have last:=height_preserved h outside frame
 have full:UniformSeedRankCrossPreparation.PreservedFrame n s u:=middle.trans last
 have scalar:u.scalarHeap=w.scalarHeap:=frame.1
 have combined:PrefixFrame P Q s u:=by
  constructor
  · intro q hq
    change z.scalarHeap q=s.scalarHeap q
    exact (congrFun frame.1 q).trans ((congrFun (heightSetup_frame afterSeed).2.1 q).trans
      ((pref.scalar q hq).trans (congrFun vf.2.1 q)))
  · intro q hq
    have before:q<c.rows:=by
      have hd:=h.heightLayout.directory
      change c.directory+c.gates+2≤c.rows at hd
      have dir:Q≤c.directory:=extra.directory
      omega
    have rows:c.rows≤c.colors:=by
      have hr:=h.heightLayout.rows
      change c.rows+6*c.gates*(8*c.exponent+7)≤c.colors at hr;omega
    have colors:c.colors≤c.palette:=by
      have hc:=h.heightLayout.colors
      change c.colors+2*c.gates*(8*c.exponent+7)≤c.palette at hc;omega
    have palette:=h.heightLayout.palette
    change c.palette+12≤c.heightDirectory at palette
    exact (outside q (Or.inl before) (Or.inl (by change q<c.colors;omega))
      (Or.inl (by change q<c.palette;omega))
      (Or.inl (by change q<c.heightDirectory;omega))).trans
      ((congrFun (heightSetup_frame afterSeed).1 q).trans ((pref.nat q hq).trans (congrFun vf.1 q)))
 refine ⟨u,4*c.exponent+8+t+13+ticks+1,all,?_,rfl,
  ⟨finalSource.withPC,cursor.withPC,processed,?_,?_,?_,?_⟩,full.retained ret,
  full.protected.metadata metadata,full.protected.operands ops,full,combined⟩
 · change ticks≤4*c.exponent+27+(8*c.exponent+7)*(64*c.gates+200*(2*c.gates+1)^2+56) at heightCost
   unfold runtimeBudget;omega
 · intro i;rw [scalar];exact post.positive i
 · rw [scalar];exact post.root
 · intro i hi;rw [scalar];exact post.negative i hi
 · intro i hi;rw [scalar];exact post.constants i hi

end Height

namespace Chunk
open UniformSeedChunkPreparation
theorem execution {n : ℕ} (hn:0<n) (j : Fin (axisCount n)) (c : Config) (B : ℕ)
    (x : Fin n→ℂ) (s : State) (args:Args n j c s)
    (metadata:UniformPermutationInversePreparation.Metadata n s)
    (ret:Retained n (axisCount n) s) (ops:UniformInitialPreparation.Operands n x s)
    (h:Layout n j c B) (P Q : ℕ) (extra:Fresh P Q c.seed.seed) (pc:s.pc=0) (hs:WordBound B s) : ∃u t,
    BoundedExecution program n x B s t u ∧ t≤runtimeBudget n j c ∧ u.pc=1285 ∧
    Result n j c B hn h u ∧ Retained n (axisCount n) u ∧
    UniformPermutationInversePreparation.Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧
    UniformSeedRankCrossPreparation.PreservedFrame n s u ∧ PrefixFrame P Q s u := by
  have code:=h.code
  have safe:=boot_safe hs
  have first:=block_runs boot program 0 n B x s boot_code pc hs
    (by rw [boot_length];omega) safe.1 safe.2
  let v:=applyBlock boot s
  have vp:v.pc=4:=by rw [UniformTensorMonomialMachine.applyBlock_pc,pc,boot_length]
  let seedEntry:=setPC v 0
  have eb:WordBound B seedEntry:=changePC_bound B v 0 first.final_bound (by omega)
  have start:UniformSeedRankCrossPreparation.PreservedFrame n s seedEntry:=(boot_frame s).preserved
  obtain ⟨w,t,seedRun,seedCost,wp,post,_,_,_,seedFrame,pref⟩:=
    Height.execution hn j c.seed B x seedEntry (boot_args args)
      (start.protected.metadata metadata) (start.retained ret) (start.protected.operands ops)
      h.seed P Q extra rfl eb
  have middle:=UniformBoundedAssembly.boundedExecution_placed seed_code
    (by rw [UniformSeedHeightPreparation.program_length];omega) (by omega) seedRun
  rw [UniformSeedRankCrossPreparation.placed_zero v 4 vp] at middle
  let afterSeed:=setPC w 1050
  have carry:Carried n j c afterSeed:=(boot_carried args).transport (by
    intro q lo _
    have eq : w.natReg q=seedEntry.natReg q:=UniformNewtonTableMachine.Executes.keeps_nat seedRun.executes (ceiling_keeps q lo)
    exact eq)
  have old:UniformSeedRankCrossPreparation.PreservedFrame n s afterSeed:=start.trans seedFrame
  have carriedMeta:UniformPermutationInversePreparation.Metadata n afterSeed:=old.protected.metadata metadata
  have carriedRet:Retained n (axisCount n) afterSeed:=old.retained ret
  have install:=setup_runs (c:=c) (j:=j) x carriedMeta carriedRet carry rfl middle.final_bound (by omega)
  let installed:=applyBlock setup afterSeed
  have ip:installed.pc=1070:=by rw [UniformTensorMonomialMachine.applyBlock_pc,setup_length];rfl
  let chunkEntry:=setPC installed 0
  have ib:WordBound B chunkEntry:=changePC_bound B installed 0 install.final_bound (by omega)
  have head:=setup_spec carriedMeta carriedRet carry (post.cursor.header.withPC 1050)
  have transported:UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) chunkEntry:=
    seedResult_transport hn h post (fun _ _=>rfl) rfl
      (fun q lo hi=>(setup_frame afterSeed).2.2.2.2.2 q (by omega))
  obtain ⟨ticks,z,cost,last,header,count,rows,widths,perms,mapped,processed,outside,frame⟩:=
    UniformChunkMatchingPreparation.cross_execution (c.chunk n j) c.seed.negative B n x chunkEntry
      (UniformSeedHeightPreparation.widths c.seed).1 (UniformSeedHeightPreparation.widths c.seed).2
      h.chunk head transported.processed rfl ib
  have lastPlaced:=UniformBoundedAssembly.boundedExecution_placed chunk_code
    (by rw [UniformChunkMatchingPreparation.program_length];omega) (by omega) last
  rw [UniformSeedRankCrossPreparation.placed_zero installed 1070 ip] at lastPlaced
  let u:=setPC z 1285
  have stop:BoundedExecution program n x B u 1 u:=.halt lastPlaced.final_bound
    (by simp [step,u,setPC,halt_at])
  have all:BoundedExecution program n x B s (4+t+20+ticks+1) u:=by
    simpa only [boot_length,Nat.add_assoc] using first.executes (middle.executes (install.executes (lastPlaced.executes stop)))
  have pre:UniformSeedRankCrossPreparation.PreservedFrame n s chunkEntry:=
    old.trans (setup_frame afterSeed).preserved
  have full:UniformSeedRankCrossPreparation.PreservedFrame n s u:=pre.trans (chunk_preserved h outside frame)
  have prepared:UniformSeedHeightPreparation.Result n j c.seed B (h.seed.replay hn j c.seed B) u:=
    seedResult_transport hn h transported (fun q hq=>outside q (Or.inl hq)) frame.1
      (fun q lo hi=>frame.2.2.2.2 q (by unfold UniformChunkMatchingPreparation.Protected;omega))
  have combined:PrefixFrame P Q s u:=by
    constructor
    · intro q hq
      change z.scalarHeap q=s.scalarHeap q
      exact (congrFun frame.1 q).trans ((congrFun (setup_frame afterSeed).2.1 q).trans
        ((pref.scalar q hq).trans (congrFun (boot_frame s).2.1 q)))
    · intro q hq
      have hd:=h.seed.heightLayout.directory
      have hr:=h.oldRows
      change c.seed.directory+c.seed.gates+2≤c.seed.rows at hd
      change c.seed.rows+6*c.seed.gates*(8*c.seed.exponent+7)≤c.borrowed at hr
      have dir:Q≤c.seed.directory:=extra.directory
      exact (outside q (Or.inl (by change q<c.borrowed;omega))).trans
        ((congrFun (setup_frame afterSeed).1 q).trans ((pref.nat q hq).trans (congrFun (boot_frame s).1 q)))
  refine ⟨u,4+t+20+ticks+1,all,?_,rfl,⟨prepared,header.withPC 1285,count,rows,widths,perms,mapped⟩,
    full.retained ret,full.protected.metadata metadata,full.protected.operands ops,full,combined⟩
  unfold runtimeBudget
  change ticks≤4*c.seed.exponent+180*radix n j+92 at cost
  omega


end Chunk

/-- The physically retained conjugate pool and two-field directory survive;
no state is obtained by semantic conjugation. -/
theorem PrefixFrame.conjugate {n : ℕ} {s u : State}
 (f:PrefixFrame (UniformAllAxisConjugatePreparation.axisBase n (axisCount n))
  (UniformAllAxisConjugatePreparation.directoryBase n+2*axisCount n) s u)
 (h:UniformAllAxisConjugatePreparation.Retained n (axisCount n) s) :
 UniformAllAxisConjugatePreparation.Retained n (axisCount n) u:=by
 refine ⟨?_,?_,?_⟩
 · intro j hj q l
   exact (f.scalar _ (UniformAllAxisConjugatePreparation.compact_address_before j hj q l)).trans
     (h.coefficients j hj q l)
 · intro j hj
   exact (f.nat _ (by omega)).trans (h.address j hj)
 · intro j hj
   exact (f.nat _ (by omega)).trans (h.width j hj)
end
end ExactFourierCircuits.UniformSeedConjugatePreservation
