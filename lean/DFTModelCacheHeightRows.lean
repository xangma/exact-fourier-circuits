import DFTModelCacheHeightValues

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeight
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
abbrev NativeRow := UniformConvolutionTopologyMachine.Row
abbrev ShearRow := UniformInPlaceMachine.Row

def row3 (r:ShearRow):Row.T := (r.dst,(r.src,r.coefficient))
def input (n A C P d:ℕ) (enabled:Bool) (t order directory:Tape ℕ):Input.T :=
 ((n,(A,(C,(P,(d,if enabled then 1 else 0))))),(t,(order,directory)))

def Fields (G:ℕ) (rows:ℕ→NativeRow) (t:Tape ℕ):Prop := ∀i,i<G→
 t.look (5*i) 0=(rows i).opcode ∧ t.look (5*i+1) 0=(rows i).left ∧
 t.look (5*i+2) 0=(rows i).right ∧ t.look (5*i+3) 0=(rows i).kind ∧
 t.look (5*i+4) 0=(rows i).payload

theorem prefix_pairs (x:Input.T) (M:ℕ):
 rowsPrefix x (2*M)=(List.range M).flatMap (fun i=>
  (if accepts x (2*i) then [rowValue x (2*i)] else [])++
  (if accepts x (2*i+1) then [rowValue x (2*i+1)] else [])) := by
 induction M with
 | zero=>rfl
 | succ M ih=>
   rw [show 2*(M+1)=2*M+1+1 by omega,rowsPrefix_succ,rowsPrefix_succ,ih,
     List.range_succ,List.flatMap_append,List.flatMap_singleton]
   exact List.append_assoc _ _ _

theorem visible_value (n s:ℕ) (enabled:Bool):
 (if s<n then (if enabled then 1 else 0)≠0 else n<s) ↔
 UniformCrossShearTableMachine.visible n enabled s=true := by
 cases enabled <;>by_cases h:s<n <;>simp [UniformCrossShearTableMachine.visible,h]

theorem pair_expansion (n A C P d M start:ℕ) (enabled:Bool) (t ord dir:Tape ℕ)
 (rows:ℕ→NativeRow) (js:List ℕ) (i:ℕ) (hi:i<js.length)
 (hstart:dir.look d 0=start) (hord:ord.look (start+i) 0=js[i])
 (hf:Fields M rows t) (hj:js[i]<M) (hk:(rows js[i]).kind≤1):
 (if accepts (input n A C P d enabled t ord dir) (2*i) then
   [rowValue (input n A C P d enabled t ord dir) (2*i)] else [])++
 (if accepts (input n A C P d enabled t ord dir) (2*i+1) then
   [rowValue (input n A C P d enabled t ord dir) (2*i+1)] else [])=
 (UniformCrossShearTableMachine.expansion n A C P js[i] enabled (rows js[i])).map row3 := by
 have h0:gateValue (input n A C P d enabled t ord dir) (2*i)=js[i]:=by
   simp only [gateValue,input,hstart,Nat.mul_div_cancel_left _ (by decide:0<2),hord]
 have h1:gateValue (input n A C P d enabled t ord dir) (2*i+1)=js[i]:=by
   have he:(2*i+1)/2=i:=by omega
   simp only [gateValue,input,hstart,he,hord]
 have f0:=hf js[i] hj
 have hc:(if (rows js[i]).kind<1 then
     (if (rows js[i]).payload<2 then P else P+2) else C+(rows js[i]).payload)=
     UniformCrossShearTableMachine.coefficientAddress C P (rows js[i]):=by
   unfold UniformCrossShearTableMachine.coefficientAddress
   by_cases hz:(rows js[i]).kind=0
   · simp [hz]
   · have he:(rows js[i]).kind=1:=by omega
     simp [he]
 simp only [accepts,rowValue,fieldValue,h0,h1]
 simp only [input,show (2*i)%2=0 by omega,show (2*i+1)%2=1 by omega,
   ite_true,ite_false,one_ne_zero,true_or,false_or,true_and, Nat.add_zero,
   f0.1,f0.2.1,f0.2.2.1,f0.2.2.2.1,f0.2.2.2.2,hc,visible_value]
 unfold UniformCrossShearTableMachine.expansion UniformCrossShearTableMachine.emit
 by_cases ho:(rows js[i]).opcode<2
 all_goals by_cases hl:UniformCrossShearTableMachine.visible n enabled (rows js[i]).left=true
 all_goals by_cases hr:UniformCrossShearTableMachine.visible n enabled (rows js[i]).right=true
 all_goals simp [ho,hl,hr,row3]

theorem range_flatMap (xs:List ℕ) (f:ℕ→List Row.T):
 (List.range xs.length).flatMap (fun i=>f (xs[i]?.getD 0))=xs.flatMap f := by
 induction xs using List.reverseRecOn with
 | nil=>rfl
 | append_singleton xs a ih=>
   simp only [List.length_append,List.length_singleton,List.range_succ,
     List.flatMap_append,List.flatMap_singleton]
   have hc:(List.range xs.length).flatMap (fun i=>f ((xs++[a])[i]?.getD 0))=
       (List.range xs.length).flatMap (fun i=>f (xs[i]?.getD 0)):=by
     apply List.flatMap_congr
     intro i hi
     rw [List.getElem?_append_left (List.mem_range.mp hi)]
   rw [hc,ih,List.getElem?_append_right (by omega)]
   simp

theorem order_cell (G d:ℕ) (depth:ℕ→ℕ) (hd:d≤G) (i:ℕ)
 (hi:i<(UniformDAGBucketMachine.selected G d depth).length):
 (UniformDAGBucketMachine.order G depth)[UniformDAGBucketMachine.offset G d depth+i]?.getD 0=
 (UniformDAGBucketMachine.selected G d depth)[i] := by
 have he:=congrArg (fun xs:List ℕ=>xs[i]?)
   (UniformCrossDepthReplayPreparation.order_slice G d depth hd)
 have hopt:(UniformDAGBucketMachine.order G depth)[UniformDAGBucketMachine.offset G d depth+i]?=
     some (UniformDAGBucketMachine.selected G d depth)[i]:=by
   simpa only [List.getElem?_take,hi,decide_true,ite_true,List.getElem?_drop,
     List.getElem?_eq_getElem hi] using he
 rw [hopt]
 rfl

theorem tab_read (N i:ℕ) (f:ℕ→ℕ) (hi:i<N):
 (Tape.tab N f).look i 0=f i := by
 unfold Tape.look
 split
 · rfl
 · exact False.elim (by contradiction)

theorem selected_rows (n A C P G d:ℕ) (enabled:Bool) (t:Tape ℕ)
 (rows:ℕ→NativeRow) (depth:ℕ→ℕ) (hd:d≤G)
 (hb:∀i,i<G→depth i≤G) (hf:Fields G rows t)
 (hk:∀i,i<G→(rows i).kind≤1):
 rowsPrefix (input n A C P d enabled t
   (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
   (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth)))
  (slotCount (input n A C P d enabled t
   (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
   (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth))))=
 (UniformCrossShearTableMachine.orderedRows n A C P enabled rows
   (UniformDAGBucketMachine.selected G d depth)).map row3 := by
 let js:=UniformDAGBucketMachine.selected G d depth
 let start:=UniformDAGBucketMachine.offset G d depth
 have hs: start+js.length≤G:=UniformCrossDepthReplayPreparation.offset_span depth hd hb
 have hend:=UniformDAGBucketMachine.offset_succ G d depth
 have count:slotCount (input n A C P d enabled t
     (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
     (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth)))=2*js.length:=by
   change 2*((Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth)).look (d+1) 0-
     (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth)).look d 0)=2*js.length
   rw [tab_read _ _ _ (by omega),tab_read _ _ _ (by omega),hend,Nat.add_sub_cancel_left]
 rw [count,prefix_pairs]
 have he:(List.range js.length).flatMap (fun i=>
     (if accepts (input n A C P d enabled t
       (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
       (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth))) (2*i) then
       [rowValue (input n A C P d enabled t
         (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
         (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth))) (2*i)] else [])++
     (if accepts (input n A C P d enabled t
       (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
       (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth))) (2*i+1) then
       [rowValue (input n A C P d enabled t
         (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G depth)[j]?.getD 0))
         (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j depth))) (2*i+1)] else []))=
     (List.range js.length).flatMap (fun i=>
       (UniformCrossShearTableMachine.expansion n A C P (js[i]?.getD 0)
         enabled (rows (js[i]?.getD 0))).map row3):=by
   apply List.flatMap_congr
   intro i hi
   have hi':i<js.length:=List.mem_range.mp hi
   have hj:js[i]<G:=
     (UniformDAGBucketMachine.selected_mem G d depth js[i]).mp (List.getElem_mem hi') |>.1
   simp only [List.getElem?_eq_getElem hi',Option.getD_some]
   apply pair_expansion n A C P d G start enabled _ _ _ rows js i hi'
   · exact tab_read _ _ _ (by omega)
   · rw [tab_read _ _ _ (by omega)]
     exact order_cell G d depth hd i hi'
   · exact hf
   · exact hj
   · exact hk _ hj
 rw [he,range_flatMap js (fun j=>(UniformCrossShearTableMachine.expansion n A C P j enabled (rows j)).map row3)]
 simp only [UniformCrossShearTableMachine.orderedRows,List.map_flatMap]
 rfl

end
end ExactFourierCircuits.DFTModelCacheHeight
