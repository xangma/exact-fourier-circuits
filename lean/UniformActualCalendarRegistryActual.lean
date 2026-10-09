import UniformActualCalendarRegistryBundle
import UniformActualCalendarRectangleFamily
import UniformActualCalendarForestRegistry

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformMachine UniformJointAllocation UniformAllAxisSeedPreparation
open UniformLocalRequestPlan UniformLocalRequestGeometry
open UniformDirectLeafForestData UniformDirectLeafForestState UniformDirectLeafForestContents
open UniformLocalCacheTreeMachine
noncomputable section

def Family.cast {r r' O T B D D' stride stride' L L' s}
 (f:Family r O T B D stride L s)(radix:r=r')(address:D=D')(spacing:stride=stride')(rows:L=L'):
 Family r' O T B D' stride' L' s:=by
 subst r';subst D';subst stride';subst L'
 exact f

/-- One whole physical selection bank: the genuine continuous rectangle bank
followed by the corrected461 durable per-node banks, in literal90 order. -/
def of_actual {constants:Constants}{n:ℕ}{axisIndex:Fin (axisCount n)}{qs:List Request}{R N:ℕ}
 (g:Geometry constants n axisIndex qs R N){s:State}
 (all:∀i (hi:i<qs.length),Complete constants n axisIndex qs R N g i hi s)
 {p:Parameters}{visits:List Visit}{A:ℕ}{positive:2≤p.radix}
 (forest:Contents p visits A positive s)(facts:Facts p visits)(hn:0<n)
 {O T:ℕ}(scalarRoom:3*slab constants n≤O)(natRoom:3*slab constants n≤T)
 (radixRoom:radix n axisIndex≤envelope constants n)(sameRadix:p.radix=radix n axisIndex)
 (entry:p.start.entry=p.start.permutation+3*p.radix+4)
 (pool:p.start.pool+9*p.radix*UniformDirectLeafForestModel.demand visits≤O)
 (nat:p.start.permutation+(3*p.radix+11)*UniformDirectLeafForestModel.demand visits≤T):
 Bundle p.radix O T (envelope constants n) (UniformActualCalendarRectangleRegistry.base constants n axisIndex)
  (UniformActualCalendarRectangleRegistry.entries n qs)
  (UniformDirectLeafForestRangeSource.nodeRanges p visits A) s where
 rectangle:=(UniformActualCalendarRectangleRegistry.wholeFamily g all hn scalarRoom natRoom radixRoom).cast
  sameRadix.symm rfl (congrArg (fun r=>3*r+11) sameRadix.symm) rfl
 node:=fun i=>by
  have hi:i.val<visits.length:=by
   simpa only[UniformDirectLeafForestRangeSource.nodeRanges,List.length_ofFn] using i.isLt
  let index:Fin visits.length:=⟨i.val,hi⟩
  have f:=UniformActualCalendarForestRegistry.family forest facts entry pool nat
   (sameRadix.trans_le radixRoom) index
  have get:(UniformDirectLeafForestRangeSource.nodeRanges p visits A).get i=
   (⟨(position p visits i.val).entry,UniformDirectLeafForestModel.operations visits[i.val],
    UniformDirectLeafForestRangeSource.nodeRecords p visits A i.val hi⟩:UniformCacheRangeSelector.Range):=
   List.getElem_ofFn i.isLt
  rw[get]
  exact f

end
end ExactFourierCircuits.UniformActualCalendarRegistry
