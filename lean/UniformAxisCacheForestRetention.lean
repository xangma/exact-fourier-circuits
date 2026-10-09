import UniformAxisCacheForestGeometry
import UniformDirectLeafForestContents
import UniformDirectLeafForestBankFrame
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheForestRetention
open UniformMachine UniformAxisCacheStartupMachine UniformAxisCacheSelectedPreparation
open UniformAxisCacheForestEntry UniformAxisCacheForestGeometry UniformAxisCacheInputs
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestExecution
open UniformJointCacheAllocation UniformJointAllocation UniformAxisCachePhysical
noncomputable section

def semantic_withPC {c:UniformDirectLeafCacheReader.Config} {r:ℕ}
 {q:UniformTransposeDescriptorMachine.Record} {mu:ℂ} {positive:2≤r} {s:State}
 (h:UniformDirectLeafCacheSemanticExecution.SemanticResult c r q mu positive s) (pc:ℕ):
 UniformDirectLeafCacheSemanticExecution.SemanticResult c r q mu positive
  (UniformTensorMonomialMachine.setPC s pc):=by
 let result:UniformDirectLeafCacheExecution.Result c r q mu positive (UniformTensorMonomialMachine.setPC s pc):=
  ⟨h.count,h.kind,h.edges,h.matching,h.inRange,h.count_eq,h.kind_eq,
   h.entry,h.rows,h.widths,h.permutations,h.scale,h.shear⟩
 exact ⟨result,h.endpoints,h.unused⟩

lemma contents_withPC {p:Parameters} {vs:List UniformLocalCacheTreeMachine.Visit} {A:ℕ}
 {positive:2≤p.radix} {s:State}
 (h:UniformDirectLeafForestContents.Contents p vs A positive s) (pc:ℕ):
 UniformDirectLeafForestContents.Contents p vs A positive (UniformTensorMonomialMachine.setPC s pc):=by
 refine ⟨⟨h.counts.rectangles,h.counts.nodes⟩,?_,?_,h.root⟩
 · intro i hi low
   exact ⟨(h.ranges i hi low).first,(h.ranges i hi low).count⟩
 · intro i hi low stop k hk
   obtain ⟨event⟩:=h.cached i hi low stop k hk
   exact ⟨semantic_withPC event pc⟩

lemma endpoints_withPC {p:Parameters} {vs:List UniformLocalCacheTreeMachine.Visit} {s:State}
 (h:UniformDirectLeafForestExit.Endpoints p vs s) (pc:ℕ):
 UniformDirectLeafForestExit.Endpoints p vs (UniformTensorMonomialMachine.setPC s pc):=
 ⟨h.pool,h.permutation,h.widths,h.markers,h.axis,h.entry,h.innerPool,h.ordinal⟩

lemma low_nat {p:Parameters} {vs:List UniformLocalCacheTreeMachine.Visit} {s u:State}
 (f:Frame p vs s u) (ranges:p.start.rows≤p.ranges) (permutation:p.start.rows≤p.start.permutation):
 ∀a,a<p.start.rows→u.natHeap a=s.natHeap a:=by
 intro a low
 exact f.natBefore a (by omega) (Or.inl low) (Or.inl (by omega))
  (Or.inl (by unfold UniformDirectLeafForestBoot.countHeader;omega))

theorem inputs {c n j x s u} (hn:0<n) (input:Inputs n x s)
 (src:Sources (parameters c n j) (visits c n j) n u)
 (frame:Frame (parameters c n j) (visits c n j) s u)
 (saved:∀q,100≤q→q≤106→u.natReg q=s.natReg q):Inputs n x u:=by
 have l:=placement c n hn j
 have b:=bounds c n hn j
 have rows:(parameters c n j).start.rows≤(parameters c n j).ranges:=by
  change UniformLocalRectangleWorkspaceHeaders.z n≤(axis c n j).tasks
  have h:=b.rows;omega
 have nat:=low_nat frame rows (by have h:=l.rows;omega)
 have word:=(UniformAllAxisSeedPreparation.word_setup hn).2
 change _≤UniformLocalRectangleWorkspaceHeaders.z n ∧_≤UniformLocalRectangleWorkspaceHeaders.z n at word
 have scalar:UniformAllAxisSeedPreparation.axisBase n (Seed.axisCount n)≤
   (parameters c n j).start.pool:=by
  change _≤(axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
  have lower:=(UniformAxisCachePhysical.axis_lower c n j).2
  have low:=low_rows c n
  omega
 have preserved:UniformSeedRankCrossPreparation.PreservedFrame n s u:=
  ⟨fun a hi=>nat a (hi.trans_le word.2),
   fun a hi=>frame.scalarOutside a (Or.inl (hi.trans_le scalar)),saved,frame.outputs,frame.roots⟩
 exact ⟨preserved.protected.metadata input.metadata,preserved.protected.operands input.operands,
  src.original,src.conjugate⟩

theorem earlier {c n i j s u} (_hn:0<n) (old:i.val<j.val)
 (frame:Frame (parameters c n j) (visits c n j) s u):Heaps c n i s u:=by
 have sep:=axis_separation c n i j old
 have lower:=axis_lower c n i
 have low:=low_rows c n
 have order:=control_after_tasks c n j
 constructor
 · intro a lo hi
   apply frame.natBefore a
   · change a<(axis c n j).control+(3*Seed.radix n j+11)*rectangleCount c n j
     omega
   · right
     change UniformLocalRectangleWorkspaceHeaders.z n+3≤a
     omega
   · left
     exact hi.trans_le sep.1
   · left
     unfold UniformDirectLeafForestBoot.countHeader
     change a<(axis c n j).tasks+4*Seed.radix n j+4
     omega
 · intro a lo hi
   apply frame.scalarOutside a
   left
   change a<(axis c n j).pool+9*Seed.radix n j*rectangleCount c n j
   omega

end
end ExactFourierCircuits.UniformAxisCacheForestRetention
