import DFTModelCacheDescriptorNodeBounds
import DFTModelCacheDescriptorSearchPeak
import DFTModelCacheDescriptorRowsPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] selected rectangleRows rowCell nodeRows nodeSeed

theorem emptyRows_peak (v o b : ℕ) : (run emptyRows ((v,o),b)).peak=0 := rfl

theorem nodeRows_peak (v o b : ℕ) (hbv : b≤v) :
    (run nodeRows ((v,o),b)).peak≤10*(v+1)^2 := by
  have hbase : 2≤10*(v+1)^2 := by nlinarith
  have he:=emptyRows_peak v o b
  dsimp only [run] at he
  by_cases hz : b=0
  · subst b
    rw [nodeRows]
    dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    split_ifs <;> simp_all
  · have hr:=rectangleRows_peak v o b (by omega) hbv
    dsimp only [run] at hr
    rw [nodeRows]
    dsimp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    split_ifs <;> simp_all

theorem node_peak (v o : ℕ) : (run node (v,o)).peak≤4000*(v+1)^2 := by
  have hs:=selected_peak v
  have hr:=nodeRows_peak v o (UniformWorkspacePlanner.selected v) (UniformWorkspacePlanner.selected_le v)
  have seed : (run nodeSeed (v,o)).peak=(run selected v).peak := by
    rw [nodeSeed]
    dsimp only [run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
    simp only [zero_max,max_zero]
  rw [node]
  change max (max (run nodeSeed (v,o)).peak
    (max 0 (max (run nodeRows (run nodeSeed (v,o)).val).peak 0))) 0≤_
  rw [nodeSeed_value,seed]
  simp only [max_zero,zero_max,max_le_iff]
  exact ⟨hs,by nlinarith⟩

end
end ExactFourierCircuits.DFTModelCacheDescriptor
