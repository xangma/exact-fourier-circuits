import UniformActualCalendarHeaderCodes
import UniformLocalBroadcastSemantics

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarBroadcastCodes
open UniformReplayPrint UniformLocalCacheChronology UniformLocalRectangleDescriptors
noncomputable section

def signed {R : ℕ} (inverse : Bool) (code : ShearCode ℕ R) :=
 if inverse then code.inverse else code

def entries {R : ℕ} (q : Row) (slot : Slot) (g : ℕ) (ag : q.a≤g) :
 List (ShearCode ℕ R) :=
 if slot.color=0 then (List.finRange q.a).map
  (fun j=>signed slot.inverse (UniformLocalBroadcastSemantics.entry q.e q.a g ag j)) else []

def codeValue {R : ℕ} (q : Row) (g : ℕ) (fit : g+q.e+q.a≤q.width)
 (bank : Fin R→ℂ) (code : ShearCode ℕ R) : Nat × (Nat × Complex) :=
 (q.offset+UniformChunkPortMachine.mapped q.e g q.j0 q.i0
   (UniformLocalBroadcastPoolMachine.borrowedValue q g fit) code.dst,
  q.offset+UniformChunkPortMachine.mapped q.e g q.j0 q.i0
   (UniformLocalBroadcastPoolMachine.borrowedValue q g fit) code.src,
  code.coefficient.eval bank)

def occurrences (q : Row) (slot : Slot) (g P : ℕ) (fit : g+q.e+q.a≤q.width) :
 List (Nat × (Nat × Complex)) :=
 (UniformLocalBroadcastPoolMachine.rows q slot g P fit).map
  (fun row=>(row.dst,row.src,if slot.inverse then (-1:ℂ) else 1))

/-- The actual broadcast printer visits its real ascending endpoints even
when the coefficient is negative. -/
theorem occurrences_entries {R : ℕ} (q : Row) (slot : Slot) (g P : ℕ)
 (fit : g+q.e+q.a≤q.width) (ag : q.a≤g) (bank : Fin R→ℂ) :
 occurrences q slot g P fit=(entries (R:=R) q slot g ag).map (codeValue q g fit bank):=by
 by_cases color:slot.color=0
 · have full:UniformLocalBroadcastPoolMachine.count q slot=q.a:=by
    simp only[UniformLocalBroadcastPoolMachine.count,color,Nat.sub_zero,Nat.mul_one]
   unfold occurrences UniformLocalBroadcastPoolMachine.rows UniformLocalBroadcastPoolMachine.rawRows
   rw[full]
   simp only[UniformCrossBroadcastTableMachine.rowList,
    List.map_map,entries,color,ite_true,Function.comp_def]
   apply List.map_congr_left
   intro j _
   have bound:g-q.a+j.val<g:=by have:=j.isLt;omega
   have source:UniformChunkPortMachine.mapped q.e g q.j0 q.i0
     (UniformLocalBroadcastPoolMachine.borrowedValue q g fit) (q.e+1+(g-q.a)+j.val)=
     UniformLocalBroadcastPoolMachine.borrowedValue q g fit (g-q.a+j.val):=by
    rw[Nat.add_assoc (q.e+1)]
    exact UniformChunkPortMachine.mapped_gate _ _ _ _ _ _ bound
   cases slot.inverse <;>
    simp only[signed,Bool.false_eq_true,ite_false,ite_true,
     ShearCode.inverse,UniformLocalBroadcastSemantics.entry,codeValue,
     UniformChunkPortMachine.mapped_target,source,
     UniformTranslatedMatchingRows.translated,Coefficient.eval,Coefficient.negate]
   all_goals norm_num
 · have zero:1-slot.color=0:=by omega
   have empty:UniformLocalBroadcastPoolMachine.count q slot=0:=by
    simp only[UniformLocalBroadcastPoolMachine.count,zero,Nat.mul_zero]
   unfold occurrences UniformLocalBroadcastPoolMachine.rows UniformLocalBroadcastPoolMachine.rawRows
   rw[empty]
   simp only[UniformCrossBroadcastTableMachine.rowList,List.finRange_zero,List.map_nil,
    entries,color,ite_false]

/-- The literal replay layer and the actual broadcast occurrence list differ
only by the explicit reversal of the inverse slot's occurrence enumeration. -/
theorem layer_entries (k a e : ℕ) (ha : a≤UniformRadixTwoDAG.width k)
 (he : e≤UniformRadixTwoDAG.width k) (q : Row) (qa : q.a=a) (qe : q.e=e)
 (slot : Slot) (H : ℕ) (broadcast : slot.broadcast=true) :
 let D:=UniformToeplitzCrossDAG.crossDAG k a e ha he
 let ag:q.a≤D.size:=by rw[qa,UniformToeplitzCrossDAG.crossDAG_size];omega
 layer D H slot=if slot.inverse then (entries q slot D.size ag).reverse else entries q slot D.size ag:=by
 subst a;subst e
 simp only[layer,broadcast,ite_true]
 rw[UniformLocalBroadcastSemantics.cross_broadcast_color_at]
 by_cases color:slot.color=0
 · rw[ite_eq_left color,UniformLocalBroadcastSemantics.cross_broadcast_eq]
   cases inverse:slot.inverse <;>
    simp only[inverse,Bool.false_eq_true,ite_false,ite_true,entries,color,signed,
     reverseCode,List.map_reverse,List.map_map,Function.comp_def]
 · simp only[color,ite_false,entries,reverseCode,List.reverse_nil,List.map_nil]

end
end ExactFourierCircuits.UniformActualCalendarBroadcastCodes
