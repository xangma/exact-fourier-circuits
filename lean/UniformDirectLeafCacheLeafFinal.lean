import UniformDirectLeafCacheLeafExecution
import UniformDirectLeafCacheLoopFrames
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLeafFinal
open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheLoopGeometry
open UniformDirectLeafCacheProducedSource UniformDirectLeafCacheChronology UniformDirectLeafCacheLoopBoot
open UniformTransposeDescriptorMachine (Record)
noncomputable section
lemma records_elapsed (v o K flip:ℕ):elapsed (records v o K flip)=v+14*v*(v-1):=by
 by_cases f:flip=0
 · simp only[records,f,ite_true];exact leaf_elapsed v o K
 · simp only[records,f,ite_false];exact transpose_elapsed v o K

/-- Actual measured clock, not a supplied event timestamp array. -/
theorem final_time {c:Config}{readOnly r A C:ℕ}{qs:List Record}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C qs positive s u):
 u.natReg 6610=c.time+elapsed qs:=by
 simpa only[slot,starts,List.take_length] using res.args.time

theorem final_pool {c:Config}{readOnly r A C:ℕ}{qs:List Record}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C qs positive s u):
 u.natReg 6603=c.pool+9*r*qs.length:=res.args.pool

theorem final_partition {c:Config}{readOnly r A C:ℕ}{qs:List Record}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C qs positive s u):
 u.natReg 6605=c.permutation+(3*r+11)*qs.length ∧
 u.natReg 6606=c.widths+(3*r+11)*qs.length ∧
 u.natReg 6607=c.markers+(3*r+11)*qs.length ∧
 u.natReg 6608=c.axis+(3*r+11)*qs.length ∧
 u.natReg 6609=c.entry+(3*r+11)*qs.length:=
 ⟨res.args.permutation,res.args.widths,res.args.markers,res.args.axis,res.args.entry⟩

theorem final_leaf_time {c:Config}{readOnly r A C v o K flip:ℕ}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C (records v o K flip) positive s u):
 u.natReg 6610=c.time+(v+14*v*(v-1)):=by
 rw[final_time res,records_elapsed]

/-- Every actual retained compact lane is preserved when its physical
address precedes the fresh pool; both retained directory fields precede the
actual descriptor bank and reused row bank. -/
theorem retained_original {n k:ℕ}{c:Config}{readOnly r A C:ℕ}{qs:List Record}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C qs positive s u)
 (ret:UniformAllAxisSeedPreparation.Retained n k s)
 (coeff:∀(j:Fin (UniformAllAxisSeedPreparation.axisCount n)),j.val<k →
  ∀(q:Fin 5)(i:Fin (UniformAllAxisSeedPreparation.radix n j)),
  UniformAllAxisSeedPreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+i.val<c.pool)
 (dirs:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤ min readOnly c.rows):
 UniformAllAxisSeedPreparation.Retained n k u:=by
 constructor
 · intro j hj q i
   exact (res.scalarOutside _ (Or.inl (coeff j hj q i))).trans (ret.coefficients j hj q i)
 · intro j hj
   exact (res.natPrefix _ (by have:=j.isLt;omega)).trans (ret.address j hj)
 · intro j hj
   exact (res.natPrefix _ (by have:=j.isLt;omega)).trans (ret.width j hj)

theorem retained_conjugate {n k:ℕ}{c:Config}{readOnly r A C:ℕ}{qs:List Record}{positive:2≤r}{s u:State}
 (res:UniformDirectLeafCacheLeafExecution.Result c readOnly r A C qs positive s u)
 (ret:UniformAllAxisConjugatePreparation.Retained n k s)
 (coeff:∀(j:Fin (UniformAllAxisSeedPreparation.axisCount n)),j.val<k →
  ∀(q:Fin 5)(i:Fin (UniformAllAxisSeedPreparation.radix n j)),
  UniformAllAxisConjugatePreparation.axisBase n j.val+q.val*UniformAllAxisSeedPreparation.radix n j+i.val<c.pool)
 (dirs:UniformAllAxisConjugatePreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤ min readOnly c.rows):
 UniformAllAxisConjugatePreparation.Retained n k u:=by
 constructor
 · intro j hj q i
   exact (res.scalarOutside _ (Or.inl (coeff j hj q i))).trans (ret.coefficients j hj q i)
 · intro j hj
   exact (res.natPrefix _ (by have:=j.isLt;omega)).trans (ret.address j hj)
 · intro j hj
   exact (res.natPrefix _ (by have:=j.isLt;omega)).trans (ret.width j hj)
end
end ExactFourierCircuits.UniformDirectLeafCacheLeafFinal
