import OAI.Computability.FourierCircuit.Prices
import UniformScalarPreparation

set_option autoImplicit false

/-! Printed dirty sweeps use only integer coordinates and prepared coefficient
references. Scalar evaluation is separate; no coefficient zero test changes
the topology. The complete replay and its layer/RAM lowering are subsequent
obligations. -/
namespace ExactFourierCircuits.UniformReplayPrint
open OAI.ExactFourier

inductive Coefficient (r : ℕ) where
  | rational (q : ℚ)
  | prepared (index : Fin r) (negative : Bool)
  deriving DecidableEq, Repr

def Coefficient.negate {r : ℕ} : Coefficient r → Coefficient r
  | .rational q => .rational (-q)
  | .prepared i neg => .prepared i (!neg)

noncomputable def Coefficient.eval {r : ℕ} (bank : Fin r → ℂ) : Coefficient r → ℂ
  | .rational q => q
  | .prepared i neg => if neg then -bank i else bank i

theorem Coefficient.eval_negate {r : ℕ} (bank : Fin r → ℂ) (c : Coefficient r) :
    c.negate.eval bank = -c.eval bank := by
  cases c with
  | rational q => simp [negate,eval]
  | prepared i neg => cases neg <;> simp [negate,eval]

structure ShearCode (ι : Type) (r : ℕ) where
  dst : ι
  src : ι
  different : dst ≠ src
  coefficient : Coefficient r

def ShearCode.inverse {ι : Type} {r : ℕ} (s : ShearCode ι r) : ShearCode ι r :=
  ⟨s.dst,s.src,s.different,s.coefficient.negate⟩

def ShearCode.sumInl {ι κ : Type} {r : ℕ} (s : ShearCode ι r) : ShearCode (ι ⊕ κ) r :=
  ⟨.inl s.dst,.inl s.src,fun h => s.different (Sum.inl.inj h),s.coefficient⟩

noncomputable def ShearCode.eval {ι : Type} {r : ℕ} (bank : Fin r → ℂ)
    (s : ShearCode ι r) : Shear ι := ⟨s.dst,s.src,s.different,s.coefficient.eval bank⟩

theorem ShearCode.eval_inverse {ι : Type} {r : ℕ} (bank : Fin r → ℂ) (s : ShearCode ι r) :
    s.inverse.eval bank = (s.eval bank).inv := by
  simp [inverse,eval,Coefficient.eval_negate,Matrix.TransvectionStruct.inv]

theorem ShearCode.eval_sumInl {ι κ : Type} {r : ℕ} (bank : Fin r → ℂ) (s : ShearCode ι r) :
    (s.sumInl (κ := κ)).eval bank = (s.eval bank).sumInl κ := rfl

def reverseCode {ι : Type} {r : ℕ} (W : List (ShearCode ι r)) : List (ShearCode ι r) :=
  W.reverse.map ShearCode.inverse

theorem reverseCode_length {ι : Type} {r : ℕ} (W : List (ShearCode ι r)) :
    (reverseCode W).length = W.length := by simp [reverseCode]

theorem reverseCode_eval {ι : Type} {r : ℕ} (bank : Fin r → ℂ) (W : List (ShearCode ι r)) :
    (reverseCode W).map (ShearCode.eval bank) = reverseShears (W.map (ShearCode.eval bank)) := by
  simp [reverseCode,reverseShears,List.map_map,Function.comp_def,ShearCode.eval_inverse]

def reference {ι : Type} {r : ℕ} (d : ι) (ref : Option ι) (c : Coefficient r)
    (h : ∀ i, ref = some i → d ≠ i) : List (ShearCode ι r) :=
  match ref with
  | none => []
  | some src => [⟨d,src,h src rfl,c⟩]

theorem reference_length {ι : Type} {r : ℕ} (d : ι) (ref : Option ι) (c : Coefficient r)
    (h : ∀ i, ref = some i → d ≠ i) : (reference d ref c h).length ≤ 1 := by
  cases ref <;> simp [reference]

theorem reference_spec {ι : Type} {r : ℕ} (bank : Fin r → ℂ) (d : ι) (ref : Option ι)
    (c : Coefficient r) (h : ∀ i, ref = some i → d ≠ i) (v : ι → ℂ) :
    runShears ((reference d ref c h).map (ShearCode.eval bank)) v d =
      v d + c.eval bank * readCoord ref v ∧
    ∀ i, i ≠ d → runShears ((reference d ref c h).map (ShearCode.eval bank)) v i = v i := by
  cases ref with
  | none => simp [reference,readCoord]
  | some src =>
    constructor
    · simp [reference,ShearCode.eval,Shear.act,readCoord]
    · intro i hi; simp [reference,ShearCode.eval,Shear.act,hi]

inductive Gate (r w : ℕ) where
  | add (left right : Fin w)
  | sub (left right : Fin w)
  | scale (coefficient : Coefficient r) (source : Fin w)

noncomputable def Gate.eval {r w : ℕ} (bank : Fin r → ℂ) : Gate r w → OAI.ExactFourier.Gate w
  | .add a b => .add a b
  | .sub a b => .sub a b
  | .scale c a => .scale (c.eval bank) a

def gateCode {ι : Type} {r w : ℕ} (d : ι) (refs : Fin w → Option ι)
    (h : ∀ a i, refs a = some i → d ≠ i) : Gate r w → List (ShearCode ι r)
  | .add a b => reference d (refs a) (.rational 1) (h a) ++
      reference d (refs b) (.rational 1) (h b)
  | .sub a b => reference d (refs a) (.rational 1) (h a) ++
      reference d (refs b) (.rational (-1)) (h b)
  | .scale c a => reference d (refs a) c (h a)

theorem gateCode_length {ι : Type} {r w : ℕ} (d : ι) (refs : Fin w → Option ι)
    (h : ∀ a i, refs a = some i → d ≠ i) (g : Gate r w) : (gateCode d refs h g).length ≤ 2 := by
  cases g with
  | add a b =>
    simp only [gateCode,List.length_append]
    exact Nat.add_le_add (reference_length d (refs a) (.rational 1) (h a))
      (reference_length d (refs b) (.rational 1) (h b))
  | sub a b =>
    simp only [gateCode,List.length_append]
    exact Nat.add_le_add (reference_length d (refs a) (.rational 1) (h a))
      (reference_length d (refs b) (.rational (-1)) (h b))
  | scale c a => exact (reference_length d (refs a) c (h a)).trans (by omega)

theorem gateCode_spec {ι : Type} {r w : ℕ} (bank : Fin r → ℂ) (d : ι)
    (refs : Fin w → Option ι) (h : ∀ a i, refs a = some i → d ≠ i) (g : Gate r w) (v : ι → ℂ) :
    runShears ((gateCode d refs h g).map (ShearCode.eval bank)) v d =
      v d + (g.eval bank).eval (fun a => readCoord (refs a) v) ∧
    ∀ i, i ≠ d → runShears ((gateCode d refs h g).map (ShearCode.eval bank)) v i = v i := by
  cases g with
  | scale c a => exact reference_spec bank d (refs a) c (h a) v
  | add a b =>
    simp only [gateCode,List.map_append,runShears_append]
    have hl := reference_spec bank d (refs a) (.rational 1 : Coefficient r) (h a) v
    have hr := reference_spec bank d (refs b) (.rational 1 : Coefficient r) (h b)
      (runShears ((reference d (refs a) (.rational 1) (h a)).map (ShearCode.eval bank)) v)
    constructor
    · rw [hr.1,hl.1,readCoord_congr_except d (refs b) (h b) _ _ hl.2]
      simp [Gate.eval,OAI.ExactFourier.Gate.eval,Coefficient.eval]
      ; ring
    · intro i hi; rw [hr.2 i hi,hl.2 i hi]
  | sub a b =>
    simp only [gateCode,List.map_append,runShears_append]
    have hl := reference_spec bank d (refs a) (.rational 1 : Coefficient r) (h a) v
    have hr := reference_spec bank d (refs b) (.rational (-1) : Coefficient r) (h b)
      (runShears ((reference d (refs a) (.rational 1) (h a)).map (ShearCode.eval bank)) v)
    constructor
    · rw [hr.1,hl.1,readCoord_congr_except d (refs b) (h b) _ _ hl.2]
      simp [Gate.eval,OAI.ExactFourier.Gate.eval,Coefficient.eval]
      ; ring
    · intro i hi; rw [hr.2 i hi,hl.2 i hi]

inductive Program (r n : ℕ) : ℕ → Type where
  | nil : Program r n 0
  | step {k : ℕ} (p : Program r n k) (gate : Gate r (n+1+k)) : Program r n (k+1)

noncomputable def Program.eval {r n : ℕ} (bank : Fin r → ℂ) :
    {k : ℕ} → Program r n k → OAI.ExactFourier.Program n k
  | 0,.nil => .nil
  | _+1,.step p g => .step (p.eval bank) (g.eval bank)

def Program.sweep {ι : Type} {r n : ℕ} : {k : ℕ} → (p : Program r n k) →
    (enabled : Bool) → (xs : Fin n → ι) → (zs : Fin k → ι) →
    (hz : Function.Injective zs) → (hxz : ∀ i j, xs i ≠ zs j) → List (ShearCode ι r)
  | 0,.nil,_,_,_,_,_ => []
  | k+1,.step p g,enabled,xs,zs,hz,hxz =>
    let zs' : Fin k → ι := fun j => zs j.castSucc
    let hzi : Function.Injective zs' := hz.comp (Fin.castSucc_injective k)
    let hxzi : ∀ i j, xs i ≠ zs' j := fun i j => hxz i j.castSucc
    let d := zs (Fin.last k)
    let hdold : ∀ j, d ≠ zs' j := by
      intro j he
      have hv := congrArg Fin.val (hz he)
      simp only [Fin.val_last,Fin.val_castSucc] at hv
      omega
    let hdx : ∀ i, d ≠ xs i := fun i => (hxz i (Fin.last k)).symm
    p.sweep enabled xs zs' hzi hxzi ++
      gateCode d (referenceMap enabled xs zs')
        (referenceMap_avoids enabled xs zs' d hdx hdold) g

theorem Program.sweep_length {ι : Type} {r n k : ℕ} (p : Program r n k)
    (enabled : Bool) (xs : Fin n → ι) (zs : Fin k → ι)
    (hz : Function.Injective zs) (hxz : ∀ i j, xs i ≠ zs j) :
    (p.sweep enabled xs zs hz hxz).length ≤ 2*k := by
  induction p with
  | nil => simp [sweep]
  | @step k p g ih =>
    simp only [sweep,List.length_append]
    have hp := ih (fun j => zs j.castSucc) (hz.comp (Fin.castSucc_injective k))
      (fun i j => hxz i j.castSucc)
    have hd : ∀ j : Fin k, zs (Fin.last k) ≠ zs j.castSucc := by
      intro j he
      have hv := congrArg Fin.val (hz he)
      simp only [Fin.val_last,Fin.val_castSucc] at hv
      omega
    have hav := referenceMap_avoids enabled xs (fun j => zs j.castSucc) (zs (Fin.last k))
      (fun i => (hxz i (Fin.last k)).symm) hd
    have hg := gateCode_length (zs (Fin.last k)) (referenceMap enabled xs (fun j => zs j.castSucc)) hav g
    omega

/-- The printed forward sweep works for arbitrary borrowed data. It restores
all source coordinates and touches only the assigned gate coordinates. -/
theorem Program.sweep_spec {ι : Type} {r n k : ℕ} (p : Program r n k)
    (bank : Fin r → ℂ) (enabled : Bool) (xs : Fin n → ι) (zs : Fin k → ι)
    (hz : Function.Injective zs) (hxz : ∀ i j, xs i ≠ zs j) (v : ι → ℂ) :
    (∀ j, runShears ((p.sweep enabled xs zs hz hxz).map (ShearCode.eval bank)) v (zs j) =
      (p.eval bank).dirtyScratch (replayInputs enabled xs v) (v ∘ zs) j) ∧
    (∀ q, (∀ j, q ≠ zs j) →
      runShears ((p.sweep enabled xs zs hz hxz).map (ShearCode.eval bank)) v q = v q) := by
  induction p generalizing v with
  | nil => exact ⟨fun j => Fin.elim0 j,fun _ _ => rfl⟩
  | @step k p g ih =>
    let zs' : Fin k → ι := fun j => zs j.castSucc
    have hzi : Function.Injective zs' := hz.comp (Fin.castSucc_injective k)
    have hxzi : ∀ i j, xs i ≠ zs' j := fun i j => hxz i j.castSucc
    let d := zs (Fin.last k)
    have hdold : ∀ j, d ≠ zs' j := by
      intro j he
      have hv := congrArg Fin.val (hz he)
      simp only [Fin.val_last,Fin.val_castSucc] at hv
      omega
    have hdx : ∀ i, d ≠ xs i := fun i => (hxz i (Fin.last k)).symm
    let W := p.sweep enabled xs zs' hzi hxzi
    let V := gateCode d (referenceMap enabled xs zs')
      (referenceMap_avoids enabled xs zs' d hdx hdold) g
    have hWe := ih zs' hzi hxzi
    have hVe := gateCode_spec bank d (referenceMap enabled xs zs')
      (referenceMap_avoids enabled xs zs' d hdx hdold) g
    have hsrc : replayInputs enabled xs (runShears (W.map (ShearCode.eval bank)) v) =
        replayInputs enabled xs v := by
      funext i
      simp only [replayInputs]
      congr 1
      exact (hWe v).2 (xs i) (hxzi i)
    have hscratch : (runShears (W.map (ShearCode.eval bank)) v) ∘ zs' =
        (p.eval bank).dirtyScratch (replayInputs enabled xs v) (v ∘ zs') := by
      funext j
      exact (hWe v).1 j
    change (∀ j, runShears ((W++V).map (ShearCode.eval bank)) v (zs j) =
      ((p.eval bank).step (g.eval bank)).dirtyScratch (replayInputs enabled xs v) (v ∘ zs) j) ∧ _
    constructor
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [List.map_append,runShears_append,(hVe _).1,(hWe v).2 d hdold,
          OAI.ExactFourier.Program.dirtyScratch_step_last]
        rw [read_referenceMap,hsrc,hscratch,← OAI.ExactFourier.Program.dirtyEval_available]
        rfl
      · rw [List.map_append,runShears_append,(hVe _).2 (zs j.castSucc) (hdold j).symm,
          (hWe v).1 j,OAI.ExactFourier.Program.dirtyScratch_step_cast]
        rfl
    · intro q hq
      change runShears ((W++V).map (ShearCode.eval bank)) v q = v q
      rw [List.map_append,runShears_append,(hVe _).2 q (hq (Fin.last k))]
      exact (hWe v).2 q (fun j => hq j.castSucc)

def broadcastOne {ι : Type} {r a : ℕ} (refs : Fin a → Option ι) (j : Fin a) :
    List (ShearCode (ι ⊕ Fin a) r) :=
  match refs j with
  | none => []
  | some src => [⟨.inr j,.inl src,(by intro h; cases h),.rational 1⟩]

def broadcastList {ι : Type} {r a : ℕ} (refs : Fin a → Option ι) :
    List (Fin a) → List (ShearCode (ι ⊕ Fin a) r)
  | [] => []
  | j::js => broadcastOne refs j ++ broadcastList refs js

def broadcast {ι : Type} {r a : ℕ} (refs : Fin a → Option ι) :
    List (ShearCode (ι ⊕ Fin a) r) := broadcastList refs (List.finRange a)

theorem broadcastOne_length {ι : Type} {r a : ℕ} (refs : Fin a → Option ι) (j : Fin a) :
    (broadcastOne (r := r) refs j).length ≤ 1 := by
  unfold broadcastOne
  split <;> simp

theorem broadcastList_length {ι : Type} {r a : ℕ} (refs : Fin a → Option ι)
    (L : List (Fin a)) : (broadcastList (r := r) refs L).length ≤ L.length := by
  induction L with
  | nil => exact le_rfl
  | cons j js ih =>
    simp only [broadcastList,List.length_append,List.length_cons]
    have h := broadcastOne_length (r := r) refs j
    omega

theorem broadcast_length {ι : Type} {r a : ℕ} (refs : Fin a → Option ι) :
    (broadcast (r := r) refs).length ≤ a := by
  simpa [broadcast] using broadcastList_length (r := r) refs (List.finRange a)

theorem broadcastOne_spec {ι : Type} {r a : ℕ} (bank : Fin r → ℂ)
    (refs : Fin a → Option ι) (j : Fin a) (v : ι → ℂ) (y : Fin a → ℂ) :
    runShears ((broadcastOne (r := r) refs j).map (ShearCode.eval bank)) (Sum.elim v y) =
      Sum.elim v (fun i => y i + if i=j then readCoord (refs j) v else 0) := by
  cases h : refs j with
  | none => simp [broadcastOne,h,readCoord]
  | some src =>
    funext i
    cases i with
    | inl q => simp [broadcastOne,h,ShearCode.eval,Shear.act]
    | inr q =>
      by_cases hj : q=j
      · subst q; simp [broadcastOne,h,ShearCode.eval,Coefficient.eval,Shear.act,readCoord]
      · simp [broadcastOne,h,ShearCode.eval,Coefficient.eval,Shear.act,readCoord,hj]

theorem broadcastList_spec {ι : Type} {r a : ℕ} (bank : Fin r → ℂ)
    (refs : Fin a → Option ι) (L : List (Fin a)) (hn : L.Nodup)
    (v : ι → ℂ) (y : Fin a → ℂ) :
    runShears ((broadcastList (r := r) refs L).map (ShearCode.eval bank)) (Sum.elim v y) =
      Sum.elim v (fun i => y i + if i∈L then readCoord (refs i) v else 0) := by
  induction L generalizing y with
  | nil => simp [broadcastList]
  | cons j js ih =>
    have hN := List.nodup_cons.mp hn
    rw [broadcastList,List.map_append,runShears_append,broadcastOne_spec,ih hN.2]
    funext i
    cases i with
    | inl q => rfl
    | inr q =>
      by_cases hj : q=j
      · subst q; simp [hN.1]
      · simp [hj,List.mem_cons]

theorem broadcast_spec {ι : Type} {r a : ℕ} (bank : Fin r → ℂ)
    (refs : Fin a → Option ι) (v : ι → ℂ) (y : Fin a → ℂ) :
    runShears ((broadcast (r := r) refs).map (ShearCode.eval bank)) (Sum.elim v y) =
      Sum.elim v (fun i => y i + readCoord (refs i) v) := by
  simpa [broadcast] using broadcastList_spec bank refs (List.finRange a) (List.nodup_finRange a) v y

def Program.memorySweep {r n k : ℕ} (p : Program r n k) (enabled : Bool) :
    List (ShearCode (Fin n ⊕ Fin k) r) :=
  p.sweep enabled Sum.inl Sum.inr (fun _ _ h => Sum.inr.inj h) (by intros; simp)

theorem Program.memorySweep_length {r n k : ℕ} (p : Program r n k) (enabled : Bool) :
    (p.memorySweep enabled).length ≤ 2*k := p.sweep_length enabled _ _ _ _

theorem Program.memorySweep_spec {r n k : ℕ} (p : Program r n k) (bank : Fin r → ℂ)
    (enabled : Bool) (x : Fin n → ℂ) (z : Fin k → ℂ) :
    runShears ((p.memorySweep enabled).map (ShearCode.eval bank)) (Sum.elim x z) =
      Sum.elim x ((p.eval bank).dirtyScratch (if enabled then x else 0) z) := by
  have he := p.sweep_spec bank enabled Sum.inl Sum.inr (fun _ _ h => Sum.inr.inj h)
    (by intros; simp) (Sum.elim x z)
  funext q
  cases q with
  | inl i => simpa [memorySweep] using he.2 (Sum.inl i) (by intros; simp)
  | inr j =>
    have h := he.1 j
    convert h using 1 <;> cases enabled <;> rfl

/-- Every structural branch depends on a Boolean source switch or an integer
reference. The scalar bank is absent from the complete printed schedule. -/
def replayCode {r n k a : ℕ} (p : Program r n k) (outputs : Fin a → Fin (n+1+k)) :
    List (ShearCode ((Fin n ⊕ Fin k) ⊕ Fin a) r) :=
  let refs (enabled : Bool) := fun j => referenceMap enabled Sum.inl Sum.inr (outputs j)
  let W := (p.memorySweep true).map (fun s => s.sumInl (κ := Fin a))
  let V := (p.memorySweep false).map (fun s => s.sumInl (κ := Fin a))
  W ++ broadcast (refs true) ++ reverseCode W ++
    V ++ reverseCode (broadcast (refs false)) ++ reverseCode V

theorem replayCode_length {r n k a : ℕ} (p : Program r n k)
    (outputs : Fin a → Fin (n+1+k)) : (replayCode p outputs).length ≤ 8*k+2*a := by
  have hw := p.memorySweep_length true
  have hv := p.memorySweep_length false
  have hb := broadcast_length (r := r)
    (fun j => referenceMap true Sum.inl Sum.inr (outputs j))
  have hd := broadcast_length (r := r)
    (fun j => referenceMap false Sum.inl Sum.inr (outputs j))
  simp only [replayCode,List.length_append,List.length_map,reverseCode_length]
  omega

/-- Literal two-pass replay, including every sweep and output read, restores
arbitrary borrowed coordinates and adds exactly the clean DAG output. -/
theorem replayCode_spec {r n k a : ℕ} (p : Program r n k) (bank : Fin r → ℂ)
    (outputs : Fin a → Fin (n+1+k)) (x : Fin n → ℂ) (y : Fin a → ℂ) (z : Fin k → ℂ) :
    runShears ((replayCode p outputs).map (ShearCode.eval bank)) (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z) (fun j => y j + (p.eval bank).eval x (outputs j)) := by
  let mem := Fin n ⊕ Fin k
  let refs (enabled : Bool) : Fin a → Option mem :=
    fun j => referenceMap enabled Sum.inl Sum.inr (outputs j)
  let R (enabled : Bool) (v : mem → ℂ) (j : Fin a) := readCoord (refs enabled j) v
  let W := (p.memorySweep true).map (ShearCode.eval bank)
  let V := (p.memorySweep false).map (ShearCode.eval bank)
  let B := (broadcast (r := r) (refs true)).map (ShearCode.eval bank)
  let D := (broadcast (r := r) (refs false)).map (ShearCode.eval bank)
  have hWe := p.memorySweep_spec bank true
  have hVe := p.memorySweep_spec bank false
  have hBe := broadcast_spec bank (refs true)
  have hDe := broadcast_spec bank (refs false)
  let W' := W.map (fun s => s.sumInl (Fin a))
  let V' := V.map (fun s => s.sumInl (Fin a))
  let first := W' ++ B ++ reverseShears W'
  let second := V' ++ reverseShears D ++ reverseShears V'
  have hcode : (replayCode p outputs).map (ShearCode.eval bank) = first++second := by
    simp [replayCode,first,second,W',V',W,V,B,D,refs,reverseCode_eval,
      List.map_map,Function.comp_def,ShearCode.eval_sumInl,List.append_assoc]
  have hR (enabled : Bool) (xs : Fin n → ℂ) (zs : Fin k → ℂ) (j : Fin a) :
      R enabled (Sum.elim xs zs) j = available (if enabled then xs else 0) zs (outputs j) := by
    have h := congrFun (read_referenceMap enabled
      (Sum.inl : Fin n → mem) Sum.inr (Sum.elim xs zs)) (outputs j)
    cases enabled <;> exact h
  have hFirst : runShears first (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z)
        (fun j => y j + (p.eval bank).dirtyEval x z (outputs j)) := by
    rw [show first = W.map (fun s => s.sumInl (Fin a)) ++ B ++
      reverseShears (W.map (fun s => s.sumInl (Fin a))) from rfl]
    rw [replay_readout W B (R true) hBe,hWe]
    simp only [ite_true,hR]
    rw [← OAI.ExactFourier.Program.dirtyEval_available]
  have hDrev : ∀ v y, runShears (reverseShears D) (Sum.elim v y) =
      Sum.elim v (fun j => y j + -R false v j) := by
    intro v y
    simpa only [sub_eq_add_neg] using broadcast_reverse D (R false) hDe v y
  have hSecond (ys : Fin a → ℂ) :
      runShears second (Sum.elim (Sum.elim x z) ys) =
        Sum.elim (Sum.elim x z)
          (fun j => ys j - (p.eval bank).dirtyEval 0 z (outputs j)) := by
    rw [show second = V.map (fun s => s.sumInl (Fin a)) ++ reverseShears D ++
      reverseShears (V.map (fun s => s.sumInl (Fin a))) from rfl]
    rw [replay_readout V (reverseShears D) (fun v j => -R false v j) hDrev,hVe]
    simp only [Bool.false_eq_true,ite_false,hR,sub_eq_add_neg]
    rw [← OAI.ExactFourier.Program.dirtyEval_available]
  rw [hcode,runShears_append,hFirst,hSecond]
  congr 1
  funext j
  rw [OAI.ExactFourier.Program.dirtyEval_split]
  simp [add_sub_assoc]

end ExactFourierCircuits.UniformReplayPrint
