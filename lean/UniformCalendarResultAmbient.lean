import UniformCalendarAtomSourceTransport

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCalendarResultAmbient
noncomputable section
open UniformActualCalendarRectanglePhaseResult

def cast {r r' v:ℕ}{event:UniformGlobalCalendarDispatch.Event}{L:List (UniformLocalFourierLayers.Layer v)}
 {clock:ℕ}{band:Fin v↪Fin r}(result:Result event band L clock)
 (same:r=r')(target:Fin v↪Fin r')(coordinates:∀i,(target i).val=(band i).val):
 Result event target L clock:=by
 subst r'
 have eq:target=band:=by ext i;exact coordinates i
 exact ⟨result.snapshot,eq.symm▸result.source,result.matrix⟩

end
end ExactFourierCircuits.UniformCalendarResultAmbient
