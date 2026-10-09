import UniformDirectLeafForestRow
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestIteration
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafForestData UniformDirectLeafForestState
open UniformDirectLeafForestModel UniformLocalCacheTreeMachine
noncomputable section

lemma frame_source {p:Parameters}{visits:List Visit}{i:ℕ}{s r u:State}
 (f:UniformDirectLeafForestLeafStep.StepFrame p visits i r u)
 (nh:r.natHeap=s.natHeap)(sh:r.scalarHeap=s.scalarHeap)
 (out:r.outputs=s.outputs)(roots:r.rootOrders=s.rootOrders):
 UniformDirectLeafForestLeafStep.StepFrame p visits i s u:=by
 exact ⟨fun a h=>(f.scalarOutside a h).trans (congrFun sh a),
  fun a h h' h''=>(f.natBefore a h h' h'').trans (congrFun nh a),
  fun a h=>(f.natHigh a h).trans (congrFun nh a),f.outputs.trans out,f.roots.trans roots⟩

structure Invariant(p:Parameters)(visits:List Visit)(n A i:ℕ)(positive:2≤p.radix)(s:State):Prop where
 pc:s.pc=31
 cursor:Cursor p visits i s
 sources:Sources p visits n s
 counts:UniformDirectLeafForestBoot.Counts p visits s
 ranges:Ranges p visits i s
 cached:Cached p visits A positive i s

/-- A whole initialized outer iteration reads the real node and starts,
executes the real leaf/split route, and advances all physical cursors. -/
theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}
 (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))(x:Fin n→ℂ)(s:State)
 (hi:i<visits.length)(positive:2≤p.radix)
 (inv:Invariant p visits n (UniformAllAxisSeedPreparation.axisBase n axis.val) i positive s)
 (facts:Facts p visits)(bounds:SeedBounds p n)
 (radix:p.radix=UniformAllAxisSeedPreparation.radix n axis)
 (od:p.start.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:p.start.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (l:Placement p (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B visits)
 (wb:WordBound B s):∃u ticks,
 BoundedRuns UniformDirectLeafForestProgram.program n x B s ticks u ∧
 ticks≤(62*p.radix+246)*operations visits[i]+93 ∧
 Invariant p visits n (UniformAllAxisSeedPreparation.axisBase n axis.val) (i+1) positive u ∧
 UniformDirectLeafForestLeafStep.StepFrame p visits i s u:=by
 have read:=UniformDirectLeafForestRowStart.execution x s hi inv.cursor inv.sources l.code inv.pc wb
 let r:=UniformDirectLeafForestRowStart.state s
 obtain ⟨u,ticks,body,cost,done⟩:=UniformDirectLeafForestRow.from_read axis x r hi
  (UniformDirectLeafForestRowStart.header hi inv.cursor inv.sources)
  (UniformDirectLeafForestRowStart.sources inv.sources) facts radix positive od cd l rfl read.final_bound
 have frame:=frame_source done.frame (s:=s) (r:=r) rfl rfl rfl rfl
 refine ⟨u,6+ticks,read.trans body,by omega,?_,frame⟩
 refine ⟨done.pc,done.cursor,sources_transport inv.sources bounds l hi frame,
  UniformDirectLeafForestCacheRetention.counts_transport l hi inv.counts frame,?_,?_⟩
 · have previous:=UniformDirectLeafForestCacheRetention.ranges_transport l hi inv.ranges frame
   intro j hj lower
   by_cases old : j < i
   · exact previous j hj old
   · have eq:j=i:=by omega
     subst j
     exact done.range
 · have previous:=UniformDirectLeafForestCacheRetention.cached_transport l facts hi positive inv.cached frame
   intro j hj lower stop k hk
   by_cases old : j < i
   · exact previous j hj old stop k hk
   · have eq:j=i:=by omega
     subst j
     exact done.events stop k hk
end
end ExactFourierCircuits.UniformDirectLeafForestIteration
