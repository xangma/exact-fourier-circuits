import UniformActualCalendarBundleRefinement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
noncomputable section

lemma Scan.append_make_left (a b:Scan)(j elapsed:ℕ)(h:j<a.records.length):
 (a.append b).make j elapsed=a.make j elapsed:=by
 simp only[Scan.append,ite_eq_left h]

lemma Scan.append_make_right (a b:Scan)(j elapsed:ℕ):
 (a.append b).make (a.records.length+j) elapsed=b.make j elapsed:=by
 simp only[Scan.append,ite_eq_right (show ¬a.records.length+j<a.records.length by omega),Nat.add_sub_cancel_left]

lemma Scan.flatten_make (as:List Scan)(i:Fin as.length)(j elapsed:ℕ)(h:j<(as.get i).records.length):
 (Scan.flatten as).make (((as.take i.val).map Scan.records).flatten.length+j) elapsed=
 (as.get i).make j elapsed:=by
 induction as with
 | nil=>exact Fin.elim0 i
 | cons a as ih=>
  cases i using Fin.cases with
  | zero=>
   change (a.append (Scan.flatten as)).make (0+j) elapsed=a.make j elapsed
   simpa only[Nat.zero_add] using Scan.append_make_left a (Scan.flatten as) j elapsed h
  | succ i=>
   have step:=Scan.append_make_right a (Scan.flatten as)
    (((as.take i.val).map Scan.records).flatten.length+j) elapsed
   have bound:j<(as.get i).records.length:=h
   have tail:=ih i bound
   change (a.append (Scan.flatten as)).make
    (((List.take (i.val+1) (a::as)).map Scan.records).flatten.length+j) elapsed=(as.get i).make j elapsed
   simpa only[List.take_succ_cons,List.map_cons,List.flatten_cons,List.length_append,
    Fin.val_succ,List.get_cons_succ,Nat.add_assoc,Scan.flatten] using step.trans tail

lemma Bundle.scan_node_make {r O T B D:ℕ}{L:List (ℕ×ℕ)}
 {nodes:List UniformCacheRangeSelector.Range}{s:UniformMachine.State}
 (b:Bundle r O T B D L nodes s)(i:Fin nodes.length)(j elapsed:ℕ)
 (h:j<(nodes.get i).count):
 b.scan.make (L.length+
  (((List.ofFn (fun k:Fin nodes.length=>(b.node k).scan)).take i.val).map Scan.records).flatten.length+j) elapsed=
 (b.node i).make j elapsed:=by
 let as:=List.ofFn (fun k:Fin nodes.length=>(b.node k).scan)
 have hi:i.val<as.length:=by simp only[as,List.length_ofFn];exact i.isLt
 have bound:j<(as.get ⟨i.val,hi⟩).records.length:=by
  simp only[as,List.get_eq_getElem,List.getElem_ofFn,Family.scan,List.length_ofFn]
  exact h
 have tail:=Scan.flatten_make as ⟨i.val,hi⟩ j elapsed bound
 have head:=Scan.append_make_right b.rectangle.scan (Scan.flatten as)
  ((((as.take i.val).map Scan.records).flatten).length+j) elapsed
 have result:=head.trans tail
 simpa only[as,Bundle.scan,Family.scan,List.get_eq_getElem,List.getElem_ofFn,Nat.add_assoc] using result

end
end ExactFourierCircuits.UniformActualCalendarRegistry
