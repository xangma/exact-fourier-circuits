import UniformActualCalendarHeaderCodes
import UniformBorrowedCoordinateBridge

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarPackedCodes
open UniformReplayPrint UniformDAGLayers UniformToeplitzChunkWord UniformChunkPortMachine
noncomputable section

def values {v R : ℕ} (offset : ℕ) (bank : Fin R→ℂ)
 (W : List (ShearCode (Fin v) R)) : List (Nat × (Nat × Complex)) :=
 W.map (fun code=>(offset+code.dst.val,offset+code.src.val,code.coefficient.eval bank))

lemma pack_values {v R e g a : ℕ} (he : 0<e) (f : Fin (e+g+a) ↪ Fin v)
 (offset : ℕ) (bank : Fin R→ℂ) (coordinate : ℕ→ℕ)
 (agree : ∀p,p∈Set.range (natPorts e g a)→(f (port (g:=g) (a:=a) he p)).val=coordinate p)
 (W : List (ShearCode ℕ R)) (stored : ∀s∈W,Stored e g a s) :
 values offset bank ((packList he W stored).map (relabelCode f))=
 W.map (fun code=>(offset+coordinate code.dst,offset+coordinate code.src,code.coefficient.eval bank)):=by
 induction W with
 | nil=>rfl
 | cons s W ih=>
   simp only[packList,List.map_cons,values,List.map_cons]
   apply congrArg₂ List.cons
   · simp only[relabelCode,packCode,agree _ (stored s (by simp)).1,
      agree _ (stored s (by simp)).2]
   · exact ih _

/-- Packed/relabelled typed replay slots have the exact same physical
coordinate values as the real Borrowed17/ChunkPort14 integer decoder. -/
theorem canonical_values {v R s e t a g : ℕ} (he : s + e ≤ v) (ha : t + a ≤ v)
 (separated : s + e ≤ t ∨ t + a ≤ s) (fit : g + e + a ≤ v) (positive : 0 < e)
 (offset : ℕ) (bank : Fin R→ℂ) (W : List (ShearCode ℕ R))
 (stored : ∀code∈W,Stored e g a code) :
 let P:=placementOfFit (g:=g) (intervalEmbedding v s e he) (intervalEmbedding v t a ha)
   (UniformBorrowedCoordinateBridge.interval_separated he ha separated) (by omega)
 values offset bank ((packList positive W stored).map (relabelCode P.embedding))=
 W.map (fun code=>(offset+UniformChunkPortMachine.mapped e g s t
   (UniformChunkPortMachine.borrowedCoordinate v s e t a g fit) code.dst,
   offset+UniformChunkPortMachine.mapped e g s t
   (UniformChunkPortMachine.borrowedCoordinate v s e t a g fit) code.src,
   code.coefficient.eval bank)):=by
 dsimp only
 apply pack_values
 intro p hp
 have eq:=UniformBorrowedCoordinateBridge.mapped_natPorts_eq he ha separated fit
  (port (g:=g) (a:=a) positive p)
 rw[natPorts_port positive p hp] at eq
 exact eq.symm

end
end ExactFourierCircuits.UniformActualCalendarPackedCodes
