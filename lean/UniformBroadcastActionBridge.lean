import UniformPhysicalReplayBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBroadcastActionBridge
open UniformReplayPrint UniformToeplitzCrossDAG UniformDAGLayers OAI.ExactFourier
noncomputable section

def lastBroadcast {R : ℕ} (n g a : ℕ) (ha : a≤g) : List (ShearCode ℕ R) :=
 (List.finRange a).map (fun j =>
  ⟨n+1+g+j.val,n+1+(g-a+j.val),by have:=j.isLt;omega,.rational 1⟩)

theorem cross_outputs (K a e : ℕ) (ha : a≤UniformRadixTwoDAG.width K)
 (he : e≤UniformRadixTwoDAG.width K) (j : Fin a) :
 ((crossDAG K a e ha he).outputs j).val=
 e+1+((crossDAG K a e ha he).size-a+j.val) := by
 simp only [crossDAG,DAG.sumThree,gateIndex]
 omega

theorem reference_present {R : ℕ} (d src : ℕ) (ref : Option ℕ)
 (c : Coefficient R) (avoid : ∀i,ref=some i→d≠i) (eq : ref=some src) :
 reference d ref c avoid = [⟨d,src,avoid src eq,c⟩] := by
 subst ref
 rfl

theorem lastBroadcast_eq {R n a : ℕ} (D : DAG R n a) (ha : a≤D.size)
 (outputs : ∀j, (D.outputs j).val=n+1+(D.size-a+j.val)) (enabled : Bool) :
 natBroadcast D enabled = lastBroadcast n D.size a ha := by
 have source (j : Fin a) : referenceMap enabled (fun i : Fin n => i.val)
   (fun i : Fin D.size => n+1+i.val) (D.outputs j)=some (n+1+(D.size-a+j.val)) := by
  have hj : D.size-a+j.val<D.size := by have:=j.isLt;omega
  have out : D.outputs j=(⟨D.size-a+j.val,hj⟩:Fin D.size).natAdd (n+1) :=
   Fin.ext (outputs j)
  rw [out]
  simp only [referenceMap,Fin.addCases_right]
 simp only [natBroadcast,lastBroadcast]
 have flatten : ∀L : List (Fin a), L.flatMap (fun j => reference (r:=R) (n+1+D.size+j.val)
    (referenceMap enabled (fun i : Fin n => i.val) (fun i : Fin D.size => n+1+i.val) (D.outputs j))
    (.rational 1) (by
     intro src hs
     have:=UniformDAGLayers.referenceMap_nat_some enabled (D.outputs j) src hs
     have:=(D.outputs j).isLt
     omega)) =
   L.map (fun j=>⟨n+1+D.size+j.val,n+1+(D.size-a+j.val),by have:=j.isLt;omega,.rational 1⟩) := by
  intro L
  induction L with
  | nil=>rfl
  | cons j L ih=>
   simp only [List.flatMap_cons,List.map_cons,ih]
   rw [reference_present _ _ _ _ _ (source j),List.singleton_append]
 exact flatten _

end
end ExactFourierCircuits.UniformBroadcastActionBridge
