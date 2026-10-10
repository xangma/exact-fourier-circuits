import DFTModelCacheRectangleCallerValues
import DFTModelCacheRectangleCallerNative

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheRectangleCaller
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

def argumentPeak (v:DFTModelCacheTopology.Config.T) : ℕ :=
 6+gateValue v+3*v.2.1+v.2.2

theorem argument_peak (x:Input.T) (v:DFTModelCacheTopology.Config.T) :
 (run argument (x,v)).peak≤argumentPeak v := by
 simp [argument,control,metadata,geometry,heightInput,seedRadix,master,C,P,depth,color,
  enabled,original,configuration,root,bases,slot,row,rows,dimensions,
  DFTModelCacheTopology.k,DFTModelCacheTopology.n,DFTModelCacheTopology.a,
  DFTModelCacheTopology.crossCount,DFTModelCacheTopology.gates,DFTModelCacheTopology.nat,
  run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,argumentPeak,gateValue]
 omega

end
end ExactFourierCircuits.DFTModelCacheRectangleCaller
