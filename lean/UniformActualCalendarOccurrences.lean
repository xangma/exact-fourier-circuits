import UniformActualCalendarLocalSources

set_option autoImplicit false
namespace ExactFourierCircuits.UniformActualCalendarOccurrences
open UniformReplayPrint UniformToeplitzChunkWord UniformGlobalCalendarMatchingPhase
open UniformGlobalMatchingScaleBankBridge UniformActualCalendarLocalSources
noncomputable section

def actual {M : ℕ} (E : Fin M→UniformColoring.Edge) (mu : Fin M→ℂ) : List (Nat × (Nat × Complex)) :=
 List.ofFn (fun j=>((E j).left,(E j).right,mu j))

def typed {r v R : ℕ} (bank : Fin R→ℂ) (W : List (ShearCode (Fin v) R))
 (band : Fin v ↪ Fin r) : List (Nat × (Nat × Complex)) :=
 W.map (fun code=>((band code.dst).val,(band code.src).val,code.coefficient.eval bank))

lemma count {r v R M : ℕ} {E : Fin M→UniformColoring.Edge} {mu : Fin M→ℂ}
 {bank : Fin R→ℂ} {W : List (ShearCode (Fin v) R)} {band : Fin v ↪ Fin r}
 (eq : actual E mu=typed bank W band) : M=W.length:=by
 have h:=congrArg List.length eq
 simpa only[actual,typed,List.length_ofFn,List.length_map] using h

def order {r v R M : ℕ} {E : Fin M→UniformColoring.Edge} {mu : Fin M→ℂ}
 {bank : Fin R→ℂ} {W : List (ShearCode (Fin v) R)} {band : Fin v ↪ Fin r}
 (eq : actual E mu=typed bank W band) : Fin M ≃ Fin W.length := finCongr (count eq)

lemma occurrence_at {r v R M : ℕ} {E : Fin M→UniformColoring.Edge} {mu : Fin M→ℂ}
 {bank : Fin R→ℂ} {W : List (ShearCode (Fin v) R)} {band : Fin v ↪ Fin r}
 (eq : actual E mu=typed bank W band) (j : Fin M) :
 ((E j).left,(E j).right,mu j)=
 ((band (W.get (order eq j)).dst).val,(band (W.get (order eq j)).src).val,
  (W.get (order eq j)).coefficient.eval bank):=by
 have bound:j.val<W.length:=by rw[←count eq];exact j.isLt
 have h:=congrArg (fun L=>L[j.val]?) eq
 simpa only[actual,typed,List.getElem?_ofFn,List.getElem?_map,
  dite_eq_left j.isLt,List.getElem?_eq_getElem bound,Option.map_some,
  Option.some.injEq,List.get_eq_getElem,order,finCongr_apply,Fin.val_cast] using h

/-- An exact endpoint/coefficient occurrence list supplies every local source
field. The list equality is established from the actual printers separately. -/
def source {r v R M D elapsed pool P kind : ℕ}
 (E : Fin M→UniformColoring.Edge) (mu : Fin M→ℂ)
 (hmE : UniformMatchingAxisTableMachine.Matching E) (capacity : M≤r)
 (bank : Fin R→ℂ) (W : List (ShearCode (Fin v) R)) (hm : Matching W)
 (band : Fin v ↪ Fin r) (eq : actual E mu=typed bank W band)
 (p : UniformGlobalMatchingScaleMachine.Phase) :
 Source (UniformActualCalendarMatchingSource.event (r:=r) D elapsed pool P kind p
   (fun lane (i:Fin r)=>nativeFactor E mu lane i.val) E)
  (phaseSnapshot bank W hm p) band:=by
 apply UniformActualCalendarLocalSources.matching E mu hmE capacity bank W hm band (order eq)
 · intro j;exact congrArg Prod.fst (occurrence_at eq j)
 · intro j;exact congrArg (fun x:Nat × (Nat × Complex)=>x.2.1) (occurrence_at eq j)
 · intro j;exact congrArg (fun x:Nat × (Nat × Complex)=>x.2.2) (occurrence_at eq j)

end
end ExactFourierCircuits.UniformActualCalendarOccurrences
