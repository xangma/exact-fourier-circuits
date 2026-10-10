import DFTModelCacheTraversalStructure
import DFTModelCacheTraversalGrowth

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
noncomputable section
attribute [local irreducible] Bill.tab append singleton

theorem childrenCell_peak (x : FrameT.T) (j B : ℕ)
    (hB : 2 ≤ B) (ht : x.2.1.1+x.2.1.2.1 ≤ B) (hi : x.1.2.1.len ≤ B) :
    (run childrenCell (x,j)).peak ≤ B := by
  have hw : x.2.1.1 ≤ B := (Nat.le_add_right _ _).trans ht
  have div:x.2.1.1/2 ≤ x.2.1.1 := Nat.div_le_self _ _
  simp only [childrenCell,childLeft,childRight,frameSplit,integer,frameWidth,frameOffset,
    frameTask,frameId,frameNodes,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  by_cases hj:j=0 <;> simp only [hj,ite_true,ite_false]
  all_goals
    have hq:x.2.1.1/2 ≤ B := div.trans hw
    have hd:x.2.1.1-x.2.1.1/2 ≤ B := (Nat.sub_le _ _).trans hw
    have ho:x.2.1.2.1+x.2.1.1/2 ≤ B :=
      (Nat.add_le_add_left div _).trans (by simpa only [Nat.add_comm] using ht)
    have h1:1 ≤ B := by omega
    simp only [max_le_iff,Nat.zero_le,and_true,hB,hi,hq,hd,ho,h1]

theorem childrenTable_peak (x : FrameT.T) (n B : ℕ) (hn : n ≤ B)
    (hB : 2 ≤ B) (ht : x.2.1.1+x.2.1.2.1 ≤ B) (hi : x.1.2.1.len ≤ B) :
    (Bill.tab n Task4.blank (fun j=>run childrenCell (x,j))).peak ≤ B := by
  rw [ModelEquivalenceInterpreter.tab_peak]
  exact max_le hn (Finset.sup_le (fun j _=>childrenCell_peak x j B hB ht hi))

theorem frameChildren_peak (x : FrameT.T) (B : ℕ)
    (hB : 2 ≤ B) (ht : x.2.1.1+x.2.1.2.1 ≤ B) (hi : x.1.2.1.len ≤ B) :
    (run frameChildren x).peak ≤ B := by
  have h0:=childrenTable_peak x 0 B (by omega) hB ht hi
  have h2:=childrenTable_peak x 2 B hB hB ht hi
  simp only [frameChildren,emptyChildren,twoChildren,integer,frameWidth,frameTask,
    frameSelected,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay] at *
  by_cases hv:x.2.1.1<2 <;> by_cases hs:x.2.2.1=0 <;>
    simp only [hv,hs,ite_true,ite_false,Nat.one_ne_zero]
  all_goals simp only [max_le_iff];omega

theorem tailLength_run (x : Tape Task4.T) :
    run tailLength x=⟨x.len-1,5,max x.len 1,True⟩ := by
  simp [tailLength,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem tail_peak (x : Tape Task4.T) (B : ℕ) (hB : 1 ≤ B) (hx : x.len ≤ B) :
    (run tail x).peak ≤ B := by
  change (((run tailLength x).pass (fun n=>
    Bill.tab n Task4.blank (fun j=>run tailCell (x,j)))).pay 1 0).peak ≤ B
  rw [tailLength_run]
  change max (max (max x.len 1)
    (Bill.tab (x.len-1) Task4.blank (fun j=>run tailCell (x,j))).peak) 0 ≤ B
  rw [ModelEquivalenceInterpreter.tab_peak]
  have cells : (Finset.range (x.len-1)).sup (fun j=>(run tailCell (x,j)).peak) ≤ B := by
    apply Finset.sup_le
    intro j hj
    have hj:=Finset.mem_range.mp hj
    change max (max 0 (max 1 (j+1))) 0 ≤ B
    simp only [max_le_iff]
    omega
  simp only [max_le_iff]
  omega

theorem nextNode_peak (x : FrameT.T) (B : ℕ) (hB : 7 ≤ B)
    (hr : 7*x.1.2.2.len ≤ B) (he : x.2.2.2.len ≤ B) :
    (run nextNode x).peak ≤ B := by
  simp only [nextNode,frameWidth,frameOffset,frameSelected,frameParent,frameSide,frameTask,
    frameRows,frameNewRows,integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  simp only [max_le_iff]
  omega

end
end ExactFourierCircuits.DFTModelCacheTraversal
