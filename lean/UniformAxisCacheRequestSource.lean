import UniformAxisCacheTimingExecution
import UniformLocalRequestPlan
set_option autoImplicit false
namespace ExactFourierCircuits.UniformAxisCacheRequestSource
open UniformMachine UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
open UniformLocalCacheTreeExecution UniformLocalRectangleDescriptors UniformWorkspacePlanner
open UniformLocalRequestPlan UniformCacheTimingReference UniformLocalCacheTimingMetadata

def nodeRequests (q:Visit):List Request:=List.ofFn fun j:Fin (currentRows q.task).length=>
 ⟨(currentRows q.task)[j.val]'j.isLt,requestStart q j.val⟩
def requests (visits:List Visit):List Request:=visits.flatMap nodeRequests
lemma node_length(q:Visit):(nodeRequests q).length=emittedCount q.task.width:=by
 simp only [nodeRequests,List.length_ofFn,currentRows_length]
lemma requests_length(visits:List Visit):(requests visits).length=visitSum visits:=by
 induction visits with
 | nil=>rfl
 | cons q qs ih=>simpa only [requests,List.flatMap_cons,List.length_append,node_length,
   visitSum,List.map_cons,List.sum_cons] using congrArg (emittedCount q.task.width+·) ih
lemma node_rows(q:Visit):(nodeRequests q).map Request.row=currentRows q.task:=by
 apply List.ext_getElem
 · simp [nodeRequests]
 · intro i h1 h2;simp [nodeRequests]
lemma requests_rows(visits:List Visit):(requests visits).map Request.row=visitedRows visits:=by
 induction visits with
 | nil=>rfl
 | cons q qs ih=>simpa only [requests,List.flatMap_cons,List.map_append,node_rows,
   visitedRows,List.map_cons,List.flatten_cons] using congrArg (currentRows q.task++·) ih

lemma table_rowSource (v o d b:ℕ)(s:State)(h:Table v o d b s)(i:ℕ)(hi:i<(rows v o b).length):
 UniformLocalRectangleBankMachine.RowSource (d+7*i) ((rows v o b)[i]'hi) s:=by
 have bound:i<chunkCount (v-v/2) b*chunkCount (v/2) b:=by simpa only [rows_length] using hi
 let p:=finProdFinEquiv.symm (⟨i,bound⟩:Fin (chunkCount (v-v/2) b*chunkCount (v/2) b))
 have index:i=p.1.val*chunkCount (v/2) b+p.2.val:=UniformLocalCacheTimingRows.pair_index v b i bound
 have value:(rows v o b)[i]'hi=row v o b p.1.val p.2.val:=by
  simp only [UniformLocalCacheTimingRows.rows_ofFn,List.getElem_ofFn,UniformLocalCacheTimingRows.indexedRow]
  rfl
 intro f
 have stored:=table_row v o d b s h p.1 p.2 f
 rw [←index] at stored
 rw [value]
 exact stored

lemma source_append (R T:ℕ)(a b:List Request)(s:State)
 (ha:Source R T a s)(hb:Source (R+7*a.length) (T+a.length) b s):Source R T (a++b) s:=by
 constructor
 · intro i hi
   by_cases before:i<a.length
   · simpa only [List.getElem_append_left before] using ha.rows i before
   · have bound:i-a.length<b.length:=by simp only [List.length_append] at hi;omega
     have address:R+7*a.length+7*(i-a.length)=R+7*i:=by omega
     have hge:a.length ≤ i:=by omega
     simpa only [List.getElem_append_right hge,address] using hb.rows (i-a.length) bound
 · intro i hi
   by_cases before:i<a.length
   · simpa only [List.getElem_append_left before] using ha.times i before
   · have bound:i-a.length<b.length:=by simp only [List.length_append] at hi;omega
     have address:T+a.length+(i-a.length)=T+i:=by omega
     have hge:a.length ≤ i:=by omega
     simpa only [List.getElem_append_right hge,address] using hb.times (i-a.length) bound

lemma source_of_nodes (R T:ℕ)(visits:List Visit)(s:State)
 (parts:∀i (hi:i<visits.length),Source (R+7*visitSum (visits.take i))
  (T+visitSum (visits.take i)) (nodeRequests (visits[i]'hi)) s):Source R T (requests visits) s:=by
 induction visits generalizing R T with
 | nil=>constructor <;>intro i hi <;>simp [requests] at hi
 | cons q qs ih=>
   have head:Source R T (nodeRequests q) s:=by
    have item:=parts 0 (by simp)
    change Source R T (nodeRequests q) s at item
    exact item
   have tail:Source (R+7*(nodeRequests q).length) (T+(nodeRequests q).length) (requests qs) s:=by
    apply ih
    intro i hi
    have item:=parts (i+1) (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi)
    simpa only [List.take_succ_cons,visitSum,List.map_cons,List.sum_cons,Nat.mul_add,
     Nat.add_assoc,List.getElem_cons_succ,node_length] using item
   exact source_append R T (nodeRequests q) (requests qs) s head tail

/-- Actual seven-word forest tables and actual charged timing outputs become
the request loop's flat physical source in their exact preparation order. -/
theorem source (v o R U V T:ℕ)(s:State)
 (tables:RequestTables (rootVisits v o R) s)
 (printed:UniformLocalCacheTimingExecution.Printed v o R U V T s):
 Source R T (requests (rootVisits v o R)) s:=by
 apply source_of_nodes
 intro i hi
 let q:Visit:=(rootVisits v o R)[i]'hi
 have ordinal:q.rectangleBase=R+7*visitSum ((rootVisits v o R).take i):=
  UniformCacheTimingMetadata.walk_rectangle_prefix _ _ _ _ i hi
 constructor
 · intro j hj
   have bound:j<(currentRows q.task).length:=by simpa only [nodeRequests,List.length_ofFn] using hj
   have row:UniformLocalRectangleBankMachine.RowSource (q.rectangleBase+7*j)
     ((currentRows q.task)[j]'bound) s:=by
    by_cases bad:q.task.width<2 ∨ selected q.task.width=0
    · have empty:currentRows q.task=[]:=by rw [currentRows,ite_eq_left bad]
      simp only [empty,List.length_nil,Nat.not_lt_zero] at bound
    · have shape:currentRows q.task=rows q.task.width q.task.offset (selected q.task.width):=by
       rw [currentRows,ite_eq_right bad]
      have actualBound:j<(rows q.task.width q.task.offset (selected q.task.width)).length:=by
       rw [←shape];exact bound
      simpa only [shape] using table_rowSource _ _ _ _ s
       (tables q (List.getElem_mem hi) (by omega) (by omega)) j actualBound
   simpa only [nodeRequests,List.getElem_ofFn,ordinal] using row
 · intro j hj
   have bound:j<emittedCount q.task.width:=by simpa only [node_length] using hj
   simpa only [nodeRequests,List.getElem_ofFn] using printed.requests i hi j bound

end ExactFourierCircuits.UniformAxisCacheRequestSource
