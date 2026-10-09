import UniformActualCalendarRegistrySegments
import UniformActualCalendarRegistryBundle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarRegistry
open UniformGlobalCalendarDispatch
noncomputable section

lemma events_parameters (D stride D' stride' tick:ℕ)(records:ℕ→ℕ×ℕ)(make:ℕ→ℕ→Event)(j fuel:ℕ):
 events D stride tick records make j fuel=events D' stride' tick records make j fuel:=by
 induction fuel generalizing j with
 | zero=>rfl
 | succ fuel ih=>
  simp only[events]
  split_ifs
  · exact congrArg (List.cons _) (ih (j+1))
  · exact ih (j+1)

structure Scan where
 records:List (ℕ×ℕ)
 make:ℕ→ℕ→Event

def Scan.selected (a:Scan)(tick:ℕ):List Event:=
 events 0 0 tick (fun i=>a.records[i]?.getD (0,0)) a.make 0 a.records.length

def Scan.empty:Scan:=⟨[],fun _ _=>defaultEvent⟩
def Scan.append (a b:Scan):Scan:=
 ⟨a.records++b.records,fun i elapsed=>if i<a.records.length then a.make i elapsed else b.make (i-a.records.length) elapsed⟩

def Scan.flatten:List Scan→Scan
 | []=>Scan.empty
 | a::as=>a.append (Scan.flatten as)

def Family.scan {r O T B D stride L s}(a:Family r O T B D stride L s):Scan:=⟨L,a.make⟩
lemma Family.scan_selected {r O T B D stride L s}(a:Family r O T B D stride L s)(tick:ℕ):
 a.scan.selected tick=a.selected tick:=events_parameters _ _ _ _ _ _ _ _ _

lemma Scan.selected_append (a b:Scan)(tick:ℕ):
 (a.append b).selected tick=a.selected tick++b.selected tick:=by
 unfold Scan.selected Scan.append
 rw[List.length_append,events_split]
 simp only[Nat.zero_add]
 congr 1
 · apply events_congr
   · intro i _ bound
     simp only[Nat.zero_add] at bound
     have get:(a.records++b.records)[i]?.getD (0,0)=a.records[i]?.getD (0,0):=by
      rw[List.getElem?_eq_getElem (by rw[List.length_append];omega),List.getElem?_eq_getElem bound]
      simp only[List.getElem_append_left bound]
     exact get
   · intro i _ bound elapsed
     rw[ite_eq_left (by omega)]
 · have shift:=events_shift 0 0 tick (fun i=>(a.records++b.records)[i]?.getD (0,0))
    (fun i elapsed=>if i<a.records.length then a.make i elapsed else b.make (i-a.records.length) elapsed)
    a.records.length 0 b.records.length
   simp only[Nat.add_zero] at shift
   rw[shift]
   apply events_congr
   · intro i _ bound
     simp only[Nat.zero_add] at bound
     have large:a.records.length≤a.records.length+i:=by omega
     have inAll:a.records.length+i<(a.records++b.records).length:=by rw[List.length_append];omega
     rw[List.getElem?_eq_getElem inAll,List.getElem?_eq_getElem bound]
     rw[List.getElem_append_right large]
     simp only[Nat.add_sub_cancel_left]
   · intro i _ bound elapsed
     rw[ite_eq_right (by omega)]
     simp only[Nat.add_sub_cancel_left]

lemma Scan.selected_flatten (as:List Scan)(tick:ℕ):
 (Scan.flatten as).selected tick=(as.map (fun a=>a.selected tick)).flatten:=by
 induction as with
 | nil=>rfl
 | cons a as ih=>simp only[Scan.flatten,Scan.selected_append,List.map_cons,List.flatten_cons,ih]

def Bundle.scan {r O T B D L nodes s}(b:Bundle r O T B D L nodes s):Scan:=
 b.rectangle.scan.append (Scan.flatten (List.ofFn (fun i:Fin nodes.length=>(b.node i).scan)))

lemma Bundle.events_scan {r O T B D L nodes s}(b:Bundle r O T B D L nodes s)(tick:ℕ):
 b.events tick=b.scan.selected tick:=by
 rw[Bundle.scan,Scan.selected_append,Scan.selected_flatten]
 simp only[Family.scan_selected,List.map_ofFn,Function.comp_def,Bundle.events]

end
end ExactFourierCircuits.UniformActualCalendarRegistry
