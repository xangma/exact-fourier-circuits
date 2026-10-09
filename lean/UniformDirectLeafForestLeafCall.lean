import UniformDirectLeafForestAdvance
import UniformDirectLeafForestGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestLeafCall
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestControl
open UniformDirectLeafCacheLoopGeometry UniformDirectLeafCacheProducedSource
open UniformDirectLeafCacheLoopBoot UniformDirectLeafCacheLoopChoice
open UniformLocalCacheTreeMachine UniformLocalCacheTreeIteration
noncomputable section

lemma original_transport {n k:ℕ}{s u:State}
 (ret:UniformAllAxisSeedPreparation.Retained n k s)
 (nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap):
 UniformAllAxisSeedPreparation.Retained n k u:=by
 constructor
 · intro j hj q t;rw[sh];exact ret.coefficients j hj q t
 · intro j hj;rw[nh];exact ret.address j hj
 · intro j hj;rw[nh];exact ret.width j hj
lemma conjugate_transport {n k:ℕ}{s u:State}
 (ret:UniformAllAxisConjugatePreparation.Retained n k s)
 (nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap):
 UniformAllAxisConjugatePreparation.Retained n k u:=by
 constructor
 · intro j hj q t;rw[sh];exact ret.coefficients j hj q t
 · intro j hj;rw[nh];exact ret.address j hj
 · intro j hj;rw[nh];exact ret.width j hj
lemma constants_transport {s u:State}(h:UniformHadamardPairMachine.Constants s)
 (sh:u.scalarHeap=s.scalarHeap):UniformHadamardPairMachine.Constants u:=by
 rcases h with ⟨a,b,c,d,e⟩
 exact ⟨(congrFun sh _).trans a,(congrFun sh _).trans b,(congrFun sh _).trans c,
  (congrFun sh _).trans d,(congrFun sh _).trans e⟩

lemma source_transport {c:UniformDirectLeafCacheReader.Config}{D H r A C:ℕ}
 {qs:List UniformTransposeDescriptorMachine.Record}{positive:2≤r}{s u v:State}
 (res:UniformDirectLeafHighLeafExecution.Result c D H r A C qs positive u v)
 (nh:u.natHeap=s.natHeap)(sh:u.scalarHeap=s.scalarHeap)
 (out:u.outputs=s.outputs)(root:u.rootOrders=s.rootOrders):
 UniformDirectLeafHighLeafExecution.Result c D H r A C qs positive s v:=by
 refine ⟨res.pc,res.args,res.controls,res.inputs,res.events,?_,?_,?_,?_,
  res.outputs.trans out,res.roots.trans root⟩
 · intro j h;exact (res.scalarOutside j h).trans (congrFun sh j)
 · intro j h;exact (res.natPrefix j h).trans (congrFun nh j)
 · intro j h h';exact (res.natBefore j h h').trans (congrFun nh j)
 · intro j h;exact (res.natHigh j h).trans (congrFun nh j)

/-- Charged forward setup followed by the actual388 descriptor/cache producer.
The only coefficient sources are the two retained compact seed banks. -/
theorem execution {p:Parameters}{visits:List Visit}{i n B:ℕ}
 (axis:Fin (UniformAllAxisSeedPreparation.axisCount n))(x:Fin n→ℂ)(s:State)
 (hi:i<visits.length)(h:ReadCursor p visits i visits[i] s)
 (radix:p.radix=UniformAllAxisSeedPreparation.radix n axis)
 (positive:2≤p.radix)
 (original:UniformAllAxisSeedPreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (conjugate:UniformAllAxisConjugatePreparation.Retained n (UniformAllAxisSeedPreparation.axisCount n) s)
 (constants:UniformHadamardPairMachine.Constants s)
 (od:p.start.originalDirectory=UniformAllAxisSeedPreparation.directoryBase n+2*axis.val)
 (cd:p.start.conjugateDirectory=UniformAllAxisConjugatePreparation.directoryBase n+2*axis.val)
 (node:AtNode p.nodes i visits[i].task visits[i].rectangleBase s)
 (stop:leaf visits[i]) (extent:visits[i].task.offset+visits[i].task.width≤p.radix)
 (duration:visits[i].task.width+14*visits[i].task.width*(visits[i].task.width-1)≤p.rootDuration)
 (l:UniformDirectLeafForestGeometry.Layout p (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val) B visits)
 (nodeEnd:p.nodes+7*visits.length≤p.start.permutation)
 (hp:s.pc=39)(wb:WordBound B s):∃u ticks,
 BoundedRuns UniformDirectLeafForestProgram.program n x B s (9+ticks) (setPC u 436) ∧
 ticks≤(62*p.radix+246)*size visits[i].task.width+64 ∧
 UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
  p.forward (p.transpose+4*size visits[i].task.width) p.radix
  (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val)
  (records visits[i].task.width visits[i].task.offset
   (UniformAllAxisSeedPreparation.axisBase n axis.val+3*p.radix) 0) positive s u ∧
 Control p visits i (setPC u 436):=by
 have timeB:p.rootDuration+4≤B:=by have:=l.time;omega
 have durationB:=duration.trans (by have:=l.time;omega:p.rootDuration≤B)
 have forward:=UniformDirectLeafForestForward.execution x s h durationB timeB l.code hp wb
 let z:=UniformDirectLeafForestForward.result s
 have zp:z.pc=48:=by rw[UniformDirectLeafForestForward.pc,hp]
 have zh:=UniformDirectLeafForestForward.header h
 have za:=UniformDirectLeafForestForward.args h
 have zc:=UniformDirectLeafForestControl.forward (ofCursor h.toCursor)
 let start:=setPC z 0
 have nh:start.natHeap=s.natHeap:=(UniformDirectLeafForestForward.frame s).1
 have sh:start.scalarHeap=s.scalarHeap:=(UniformDirectLeafForestForward.frame s).2.1
 have out:start.outputs=s.outputs:=(UniformDirectLeafForestForward.frame s).2.2.2.1
 have root:start.rootOrders=s.rootOrders:=(UniformDirectLeafForestForward.frame s).2.2.2.2
 have origStart:=original_transport original nh sh
 have conjStart:=conjugate_transport conjugate nh sh
 have constantsStart:=constants_transport constants sh
 have args:UniformDirectLeafCacheReader.Args (UniformDirectLeafForestForward.config p visits i) start:=
  UniformDirectLeafCacheSetup.Args.setPC za 0
 have h0:=node (0:Fin 7)
 have h1:=node (1:Fin 7)
 change s.natHeap (p.nodes+7*i+0)=some visits[i].task.width at h0
 change s.natHeap (p.nodes+7*i+1)=some visits[i].task.offset at h1
 simp only[Nat.add_zero] at h0
 have leafBound:size visits[i].task.width≤p.radix^2:=by
  have bound:=UniformJointCacheTime.leaf_records_bound visits[i].task.width 0 0
  rw[UniformTransposeDescriptorMachine.leafRecords_length] at bound
  exact bound.trans (Nat.pow_le_pow_left (by omega:visits[i].task.width≤p.radix) 2)
 have layout:=UniformDirectLeafForestGeometry.phase_layout l hi stop (by omega) duration
 have rpos:2≤UniformAllAxisSeedPreparation.radix n axis:=by rw[←radix];exact positive
 have extent':visits[i].task.offset+visits[i].task.width≤UniformAllAxisSeedPreparation.radix n axis:=by
  rw[←radix];exact extent
 have widthBound:visits[i].task.width*(visits[i].task.width-1)≤B:=by nlinarith only[durationB]
 have ss:9*UniformAllAxisSeedPreparation.radix n axis≤B:=by rw[←radix];exact l.scalarStride
 have ns:3*UniformAllAxisSeedPreparation.radix n axis+11≤B:=by rw[←radix];exact l.natStride
 obtain ⟨u,ticks,body,cost,result⟩:=UniformDirectLeafHighLeafExecution.execution_from_constants
  (UniformDirectLeafForestForward.config p visits i) axis visits[i].task.width visits[i].task.offset
  (p.nodes+7*i) p.forward p.transpose 0 x start origStart conjStart constantsStart args
  zh.1 zh.2.1 zh.2.2.1 zh.2.2.2.1 h0 h1
  (by simpa only[UniformDirectLeafForestForward.config,position] using od)
  (by simpa only[UniformDirectLeafForestForward.config,position] using cd)
  extent' rpos
  (by simpa only[bank,ite_true,←radix,UniformDirectLeafForestForward.config,
    UniformDirectLeafForestGeometry.config] using layout)
  (by have:=l.rows;have:=l.cacheEnd;omega)
  (by have:=l.directory;have:=l.rows;have:=l.cacheEnd;change p.start.originalDirectory+2≤p.forward;omega)
  (by have:=l.conjugateDirectory;have:=l.rows;have:=l.cacheEnd;change p.start.conjugateDirectory+1≤p.forward;omega)
  (by have:=l.descriptors;omega)
  (by have:=l.descriptorEnd;omega)
  (by have:=l.cacheEnd
      have mul:=Nat.mul_le_mul_left (3*p.radix+11) (before_le visits i)
      simp only[UniformDirectLeafForestForward.config,position]
      omega)
  widthBound ss ns (by have:=l.code;omega) rfl (changePC_bound B z 0 forward.final_bound (by omega))
 have placed:=UniformBoundedAssembly.boundedExecution_placed UniformDirectLeafForestProgram.first_code
  (by rw[UniformDirectLeafCacheLeafProgram.program_length];have:=l.code;omega)
  (by have:=l.code;omega) body
 have startEq:UniformAssembly.placed 48 start=z:=by change setPC z 48=z;rw[←zp];cases z;rfl
 rw[startEq] at placed
 have result':UniformDirectLeafHighLeafExecution.Result (UniformDirectLeafForestForward.config p visits i)
  p.forward (p.transpose+4*size visits[i].task.width) p.radix
  (UniformAllAxisSeedPreparation.axisBase n axis.val)
  (UniformAllAxisConjugatePreparation.axisBase n axis.val)
  (records visits[i].task.width visits[i].task.offset
   (UniformAllAxisSeedPreparation.axisBase n axis.val+3*p.radix) 0) positive s u:=by
  apply source_transport (u:=start) (nh:=nh) (sh:=sh) (out:=out) (root:=root)
  simpa only[bank,ite_true,←radix,UniformDirectLeafForestForward.config,position] using result
 have controls:=UniformDirectLeafForestControl.produced (withPC zc 0) body
 refine ⟨u,ticks,forward.trans placed,?_,result',withPC controls 436⟩
 simpa only[←radix] using cost
end
end ExactFourierCircuits.UniformDirectLeafForestLeafCall
