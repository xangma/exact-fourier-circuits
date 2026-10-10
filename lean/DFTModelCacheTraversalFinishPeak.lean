import DFTModelCacheTraversalPeak
import DFTModelCacheTraversalCharges

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
noncomputable section
attribute [local irreducible] append singleton frameChildren tail nextNode

theorem comp_peak {s t u : Ty} (f : Prog false s t) (g : Prog false t u) (x : s.T) :
    (run (.comp f g) x).peak=max (run f x).peak (run g (run f x).val).peak := by
  simp only [run,Code.run,Bill.pay,Bill.pass,max_zero]

theorem fork_peak {s t u : Ty} (f : Prog false s t) (g : Prog false s u) (x : s.T) :
    (run (.fork f g) x).peak=max (run f x).peak (run g x).peak := by
  simp only [run,Code.run,Bill.pass,Bill.one,max_zero]

theorem nextStack_peak (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) (B : ℕ) (hB : 7 ≤ B)
    (ht : t.offset+t.width ≤ B) (hs : (t::ts).length+2 ≤ B) (hn : ns.length+1 ≤ B) :
    (run nextStack (frame ⟨t::ts,ns,rs⟩ t)).peak ≤ B := by
  let x:=frame ⟨t::ts,ns,rs⟩ t
  have hc:(run frameChildren x).peak ≤ B := frameChildren_peak x B (by omega)
    (by simpa only [x,frame,encode,taskEncode,Nat.add_comm] using ht)
    (by simpa only [x,frame,encode,ofList_length] using (by omega:ns.length ≤ B))
  have hl:(ofList ((t::ts).map taskEncode)).len ≤ B := by
    rw [ofList_length,List.length_map];omega
  have hp:=tail_peak (ofList ((t::ts).map taskEncode)) B (by omega) hl
  have ha:=append_peak Task4 (run frameChildren x).val
    (run tail (ofList ((t::ts).map taskEncode))).val
  have cl:(run frameChildren x).val.len ≤ 2 := by
    rw [frameChildren_value,ofList_length,List.length_map]
    exact children_length t ns.length
  have tl:(run tail (ofList ((t::ts).map taskEncode))).val.len ≤ (t::ts).length := by
    rw [tail_value]
    simp only [Tape.tab,ofList,List.length_map]
    omega
  have fv:(run frameStack x).val=ofList ((t::ts).map taskEncode) := rfl
  have fp:(run frameStack x).peak=0 := rfl
  have value:(run (.fork frameChildren (.comp frameStack tail)) x).val=
    ((run frameChildren x).val,(run tail (ofList ((t::ts).map taskEncode))).val) := rfl
  rw [nextStack,comp_peak,fork_peak,comp_peak,fv,fp,value]
  dsimp only [x] at *
  simp only [zero_max]
  exact max_le (max_le hc hp) (ha.trans (by omega))

theorem nextNodes_peak (s : ListState) (t : Task) (B : ℕ) (hB : 7 ≤ B)
    (hn : s.nodes.length+1 ≤ B) (hr : 7*s.rectangles.length ≤ B)
    (he : (currentRows t).length ≤ B) : (run nextNodes (frame s t)).peak ≤ B := by
  let x:=frame s t
  have hp:(run nextNode x).peak ≤ B := nextNode_peak x B hB
    (by simpa only [x,frame,encode,ofList_length,List.length_map] using hr)
    (by simpa only [x,frame,ofList_length,List.length_map] using he)
  have one:=singleton_run Record7 (run nextNode x).val
  have ha:=append_peak Record7 (ofList s.nodes) (run (singleton Record7) (run nextNode x).val).val
  have fv:(run frameNodes x).val=ofList s.nodes := rfl
  have fp:(run frameNodes x).peak=0 := rfl
  have value:(run (.fork frameNodes (.comp nextNode (singleton Record7))) x).val=
    (ofList s.nodes,(run (singleton Record7) (run nextNode x).val).val) := rfl
  rw [nextNodes,comp_peak,fork_peak,comp_peak,fp,value,one]
  rw [one,ofList_length] at ha
  change (run (append Record7) (ofList s.nodes,Tape.tab 1 (fun _=>(run nextNode x).val))).peak ≤ s.nodes.length+1 at ha
  dsimp only [Bill.peak,Bill.val,x] at *
  simp only [zero_max]
  exact max_le (max_le hp (by omega)) (ha.trans hn)

theorem nextRows_peak (s : ListState) (t : Task) (B : ℕ)
    (hr : s.rectangles.length+(currentRows t).length ≤ B) :
    (run nextRows (frame s t)).peak ≤ B := by
  have ha:=append_peak Record7 (ofList (s.rectangles.map rectangleEncode))
    (ofList ((currentRows t).map rectangleEncode))
  have value:(run (.fork frameRows frameNewRows) (frame s t)).val=
    (ofList (s.rectangles.map rectangleEncode),ofList ((currentRows t).map rectangleEncode)) := rfl
  rw [nextRows,comp_peak,value]
  have fp:(run (.fork frameRows frameNewRows) (frame s t)).peak=0 := rfl
  rw [fp,zero_max]
  rw [ofList_length,ofList_length,List.length_map,List.length_map] at ha
  exact ha.trans hr

theorem finish_peak (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) (B : ℕ) (hB : 7 ≤ B)
    (ht : t.offset+t.width ≤ B) (hs : (t::ts).length+2 ≤ B) (hn : ns.length+1 ≤ B)
    (hr : rs.length+(currentRows t).length ≤ B) (h7 : 7*rs.length ≤ B) :
    (run finish (frame ⟨t::ts,ns,rs⟩ t)).peak ≤ B := by
  rw [finish,fork_peak,fork_peak]
  exact max_le (nextStack_peak t ts ns rs B hB ht hs hn)
    (max_le (nextNodes_peak ⟨t::ts,ns,rs⟩ t B hB hn h7 (by omega))
      (nextRows_peak ⟨t::ts,ns,rs⟩ t B hr))

end
end ExactFourierCircuits.DFTModelCacheTraversal
