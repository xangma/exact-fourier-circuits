import UniformDirectLeafCacheLoopRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopData
open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheChronology
open UniformTransposeDescriptorMachine (Record)
noncomputable section

def nextConfig (c:Config) (r:ℕ) (q:Record) : Config :=
 ⟨c.record+4,c.originalDirectory,c.conjugateDirectory,c.pool+9*r,c.rows,
  c.permutation+(3*r+11),c.widths+(3*r+11),c.markers+(3*r+11),
  c.axis+(3*r+11),c.entry+(3*r+11),c.time+duration q⟩

structure Controls (r N i:ℕ) (s:State) : Prop where
 zero:s.natReg 6620=0
 one:s.natReg 6621=1
 four:s.natReg 6623=4
 count:s.natReg 6628=N
 index:s.natReg 6629=i
 tick:s.natReg 6630=28
 scalarStride:s.natReg 6633=9*r
 natStride:s.natReg 6634=3*r+11

lemma Controls.setPC {r N i:ℕ} {s:State} (h:Controls r N i s) (pc:ℕ):
 Controls r N i (UniformTensorMonomialMachine.setPC s pc):=
 ⟨h.zero,h.one,h.four,h.count,h.index,h.tick,h.scalarStride,h.natStride⟩

lemma controls_body {r N i n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:Controls r N i s) (run:BoundedExecution UniformDirectLeafCacheProgram.program n x B s t u):
 Controls r N i u:=by
 have keep (j:ℕ) (lo:6620≤j) (hi:j≤6634):u.natReg j=s.natReg j:=
  UniformDirectLeafCacheFrames.execution_nat run j (by omega) (Or.inl (by omega))
 exact ⟨(keep _ (by omega) (by omega)).trans h.zero,(keep _ (by omega) (by omega)).trans h.one,
  (keep _ (by omega) (by omega)).trans h.four,(keep _ (by omega) (by omega)).trans h.count,
  (keep _ (by omega) (by omega)).trans h.index,(keep _ (by omega) (by omega)).trans h.tick,
  (keep _ (by omega) (by omega)).trans h.scalarStride,(keep _ (by omega) (by omega)).trans h.natStride⟩

lemma args_body {c:Config} {n B t:ℕ} {x:Fin n→ℂ} {s u:State}
 (h:Args c s) (run:BoundedExecution UniformDirectLeafCacheProgram.program n x B s t u):Args c u:=by
 have keep (j:ℕ) (lo:6600≤j) (hi:j≤6610):u.natReg j=s.natReg j:=
  UniformDirectLeafCacheFrames.execution_nat run j (by omega) (Or.inl (by omega))
 exact ⟨(keep _ (by omega) (by omega)).trans h.record,(keep _ (by omega) (by omega)).trans h.originalDirectory,
  (keep _ (by omega) (by omega)).trans h.conjugateDirectory,(keep _ (by omega) (by omega)).trans h.pool,
  (keep _ (by omega) (by omega)).trans h.rows,(keep _ (by omega) (by omega)).trans h.permutation,
  (keep _ (by omega) (by omega)).trans h.widths,(keep _ (by omega) (by omega)).trans h.markers,
  (keep _ (by omega) (by omega)).trans h.axis,(keep _ (by omega) (by omega)).trans h.entry,
  (keep _ (by omega) (by omega)).trans h.time⟩

structure Fits (c:Config) (B:ℕ) : Prop where
 record:c.record≤B
 pool:c.pool≤B
 permutation:c.permutation≤B
 widths:c.widths≤B
 markers:c.markers≤B
 axis:c.axis≤B
 entry:c.entry≤B
 time:c.time≤B

end
end ExactFourierCircuits.UniformDirectLeafCacheLoopData
