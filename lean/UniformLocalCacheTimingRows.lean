import UniformLocalCacheTreeCoverage
import UniformCacheTimingRows

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheTimingRows
open UniformMachine UniformLocalRectangleDescriptors UniformLocalCacheTreeMachine
open UniformLocalCacheTreeCoverage UniformWorkspacePlanner

def indexedRow(v o b:ℕ)(i:Fin (chunkCount (v-v/2) b*chunkCount (v/2) b)):Row:=
 let p:=finProdFinEquiv.symm i
 row v o b p.1.val p.2.val

/-- The stored row order is exactly the lexicographic product order, including
ragged terminal rectangles. This is an ordinal statement, not membership. -/
lemma rows_ofFn(v o b:ℕ):rows v o b=List.ofFn (indexedRow v o b):=by
 have hrange(n:ℕ):(List.finRange n).map Fin.val=List.range n:=by
  apply List.ext_getElem
  · simp
  · intro i h1 h2;simp
 unfold rows
 rw [←hrange,←hrange]
 simp only [List.flatMap_def,←List.ofFn_eq_map]
 rw [List.ofFn_mul]
 simp only [List.map_ofFn]
 congr 1
 apply congrArg List.ofFn
 funext i
 apply congrArg List.ofFn
 funext j
 have eq:(⟨i.val*chunkCount (v/2) b+j.val,by
  have a:=i.isLt;have c:=j.isLt;nlinarith⟩:
  Fin (chunkCount (v-v/2) b*chunkCount (v/2) b))=finProdFinEquiv (i,j):=by
  apply Fin.ext
  change i.val*chunkCount (v/2) b+j.val=j.val+chunkCount (v/2) b*i.val
  ring
 change row v o b i.val j.val=indexedRow v o b _
 rw [eq]
 simp only [indexedRow,Equiv.symm_apply_apply]

lemma pair_index (v b h:ℕ)(hh:h<chunkCount (v-v/2) b*chunkCount (v/2) b):
 let p:=finProdFinEquiv.symm (⟨h,hh⟩:Fin (chunkCount (v-v/2) b*chunkCount (v/2) b))
 h=p.1.val*chunkCount (v/2) b+p.2.val:=by
 intro p
 have eq:=congrArg Fin.val (finProdFinEquiv.apply_symm_apply
  (⟨h,hh⟩:Fin (chunkCount (v-v/2) b*chunkCount (v/2) b)))
 change p.2.val+chunkCount (v/2) b*p.1.val=h at eq
 calc
  h=p.2.val+chunkCount (v/2) b*p.1.val:=eq.symm
  _=p.1.val*chunkCount (v/2) b+p.2.val:=by ring

/-- The physical seven-word table supplies exactly the a/e cells read by the
charged timing machine, at each flattened ordinal. -/
lemma tableAt_of_table(v o d b:ℕ)(s:State)(h:Table v o d b s):
 UniformCacheTimingRows.TableAt d 0 (rows v o b) s:=by
 intro t ht
 have bound:t<chunkCount (v-v/2) b*chunkCount (v/2) b:=by
  simpa only [rows_length] using ht
 let p:=finProdFinEquiv.symm (⟨t,bound⟩:Fin (chunkCount (v-v/2) b*chunkCount (v/2) b))
 have index:t=p.1.val*chunkCount (v/2) b+p.2.val:=pair_index v b t bound
 have value:(rows v o b)[t]'ht=row v o b p.1.val p.2.val:=by
  simp only [rows_ofFn,List.getElem_ofFn,indexedRow]
  rfl
 have a:=table_row v o d b s h p.1 p.2 ⟨2,by decide⟩
 have e:=table_row v o d b s h p.1 p.2 ⟨3,by decide⟩
 rw [←index] at a e
 simpa only [Nat.zero_add,value,Row.words,List.getElem_cons_succ,List.getElem_cons_zero]
  using And.intro a e

/-- Actual173 RequestTables feed the timing printer directly. Empty/direct
nodes have no rectangle reads; no ready timing table is supplied. -/
lemma tableAt_of_requestTables(visits:List Visit)(s:State)
 (h:UniformLocalCacheTreeExecution.RequestTables visits s):
 ∀q∈visits,UniformCacheTimingRows.TableAt q.rectangleBase 0 (currentRows q.task) s:=by
 intro q hq
 unfold currentRows
 split_ifs with bad
 · intro i hi;simp at hi
 · exact tableAt_of_table _ _ _ _ s (h q hq (by omega) (by omega))

end ExactFourierCircuits.UniformLocalCacheTimingRows
