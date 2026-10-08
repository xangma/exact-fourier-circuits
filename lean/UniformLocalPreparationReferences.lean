import UniformLocalPreparationDAG

set_option autoImplicit false

/-! Literal occurrence references for the balanced schedule.  Rational replay
coefficients are collected before the single conjugate/scale pass: inverse-FFT
normalizations are not silently assumed to exist in the input bank. -/
namespace ExactFourierCircuits.UniformLocalPreparationReferences
open UniformScalarPreparation UniformLocalPreparationDAG
open UniformBalancedToeplitz UniformWorkspacePlanner UniformReplayPrint
open OAI.ExactFourier TypedKernelWords

deriving instance DecidableEq for Request

def cacheFor {r N o : ℕ} (b : State r N o) (q : Request N)
    (hq : q∈b.cache.map Cached.request) : Cached N b.length :=
  b.cache.get ⟨(b.cache.map Cached.request).idxOf q,by
    have h := List.idxOf_lt_length_iff.mpr hq
    simpa only [List.length_map] using h⟩

theorem cacheFor_mem {r N o : ℕ} (b : State r N o) (q : Request N)
    (hq : q∈b.cache.map Cached.request) : cacheFor b q hq∈b.cache := List.get_mem _ _

theorem cacheFor_request {r N o : ℕ} (b : State r N o) (q : Request N)
    (hq : q∈b.cache.map Cached.request) : (cacheFor b q hq).request=q := by
  have h := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hq)
  simpa only [List.getElem_map,List.get_eq_getElem,cacheFor] using h

def cacheRef {r N o : ℕ} (b : State r N o) (q : Request N)
    (hq : q∈b.cache.map Cached.request) : Fin (UniformToeplitzCrossDAG.bankSize q.k) → Fin b.length :=
  fun j => (cacheFor b q hq).refs ((finCongr (congrArg (fun q => UniformToeplitzCrossDAG.bankSize q.k)
    (cacheFor_request b q hq))).symm j)

theorem cast_cached_value {r N l : ℕ} (c : Cached N l) (q : Request N) (he : c.request=q)
    (p : UniformScalarPreparation.Program r l) (roots : Fin r → ℂ) (h g : ℕ → ℂ) (hc : c.Good p roots h g)
    (j : Fin (UniformToeplitzCrossDAG.bankSize q.k)) :
    p.eval roots (c.refs ((finCongr (congrArg (fun q => UniformToeplitzCrossDAG.bankSize q.k) he)).symm j))=
      q.bank h g j := by
  subst q
  exact hc j

theorem cacheRef_value {r N o : ℕ} (b : State r N o) (q : Request N)
    (hq : q∈b.cache.map Cached.request) (roots : Fin r → ℂ) (h g : ℕ → ℂ)
    (hc : b.CachesGood roots h g) (j : Fin (UniformToeplitzCrossDAG.bankSize q.k)) :
    b.program.eval roots (cacheRef b q hq j)=q.bank h g j :=
  cast_cached_value (cacheFor b q hq) q (cacheFor_request _ _ _) b.program roots h g
    (hc _ (cacheFor_mem _ _ _)) j

/-- Syntax for each actual coefficient occurrence; it never contains ℂ literals. -/
inductive Atom (l : ℕ) where
  | literal (q : ℚ)
  | register (j : Fin l) (negative : Bool)
  deriving DecidableEq

noncomputable def Atom.value {l : ℕ} (v : Fin l → ℂ) : Atom l → ℂ
  | .literal q => q
  | .register j negative => if negative then -v j else v j

def atom {s l : ℕ} (refs : Fin s → Fin l) : Coefficient s → Atom l
  | .rational q => .literal q
  | .prepared j neg => .register (refs j) neg

theorem atom_value {s l : ℕ} (refs : Fin s → Fin l) (v : Fin l → ℂ) (c : Coefficient s) :
    (atom refs c).value v=c.eval (v ∘ refs) := by cases c <;> rfl

/-- Layer templates store concrete endpoints and register/rational coefficient
references. Parallel recursion is preserved, rather than serialized. -/
inductive Macro (l : ℕ) : ℕ → Type
  | scale {n : ℕ} (i : Fin n) (coefficient : Fin l) : Macro l n
  | shear {n : ℕ} (dst src : Fin n) (different : dst≠src) (coefficient : Atom l) : Macro l n
  | matching {n s : ℕ} (position : (Σ _ : Fin s, Fin 2) ↪ Fin n)
      (coefficients : Fin s → Atom l) : Macro l n
  | parallel {a b n : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin n)
      (L : Macro l a) (R : Macro l b) : Macro l n
  | seq {n : ℕ} (L R : Macro l n) : Macro l n
  | nil (n : ℕ) : Macro l n

def Macro.Valid {l n : ℕ} (values : Fin l → ℂ) : Macro l n → Prop
  | .scale _ c => values c≠0
  | .shear _ _ _ _ => True
  | .matching _ _ => True
  | .parallel _ L R => L.Valid values ∧ R.Valid values
  | .seq L R => L.Valid values ∧ R.Valid values
  | .nil _ => True

noncomputable def Macro.expand {l : ℕ} (values : Fin l → ℂ) :
    {n : ℕ} → (s : Macro l n) → s.Valid values → List (UniformLocalFourierLayers.Layer n)
  | _,.scale i c,h => [.step (UniformDirectToeplitz.scaleStep i (values c) h)]
  | _,.shear i j h t,_ => UniformLocalFourierLayers.serial
      (TensorWords.embeddedWord (Embedded.pair i j h) (UniformLocalShear.word (t.value values)))
  | _,.matching position coeff,_ => UniformLocalFourierLayers.batchWords 28 position
      (fun i => UniformLocalShear.word ((coeff i).value values))
      (fun _ => UniformLocalFourierLayers.localShear_length _)
  | _,.parallel e L R,h => UniformLocalFourierLayers.parallel e (L.expand values h.1) (R.expand values h.2)
  | _,.seq L R,h => L.expand values h.1 ++ R.expand values h.2
  | _,.nil _,_ => []

noncomputable def expand {l n : ℕ} (values : Fin l → ℂ) (W : List (Macro l n))
    (hW : ∀ s∈W,s.Valid values) : List (UniformLocalFourierLayers.Layer n) :=
  (W.attach.map (fun s => s.val.expand values (hW _ s.property))).flatten

theorem expand_append {l n : ℕ} (values : Fin l → ℂ) (W V : List (Macro l n))
    (hW : ∀ s∈W++V,s.Valid values) : expand values (W++V) hW=
      expand values W (fun s hs => hW s (List.mem_append_left _ hs)) ++
      expand values V (fun s hs => hW s (List.mem_append_right _ hs)) := by
  simp only [expand,List.attach_append,List.map_append,List.flatten_append,List.map_map,Function.comp_def]

def matchingMacro {v s l : ℕ} (refs : Fin s → Fin l)
    (W : List (ShearCode (Fin v) s)) (hW : UniformToeplitzChunkWord.Matching W) : Macro l v :=
  .matching (UniformToeplitzChunkWord.pairPosition W hW) (fun i => atom refs (W.get i).coefficient)

theorem matchingMacro_expand {v s l : ℕ} (refs : Fin s → Fin l) (values : Fin l → ℂ)
    (W : List (ShearCode (Fin v) s)) (hW : UniformToeplitzChunkWord.Matching W) :
    (matchingMacro refs W hW).expand values trivial=
      UniformLocalFourierLayers.matchingLayers (values ∘ refs) W hW := by
  change UniformLocalFourierLayers.batchWords 28 (UniformToeplitzChunkWord.pairPosition W hW)
    (fun i => UniformLocalShear.word ((atom refs (W.get i).coefficient).value values)) _=_
  simp only [atom_value]
  rfl

def shearMacros {v s l : ℕ} (refs : Fin s → Fin l) (L : List (List (ShearCode (Fin v) s)))
    (hL : ∀ W∈L,UniformToeplitzChunkWord.Matching W) : List (Macro l v) :=
  L.attach.map (fun W => matchingMacro refs W.val (hL _ W.property))

theorem shearMacros_valid {v s l : ℕ} (refs : Fin s → Fin l) (values : Fin l → ℂ)
    (L : List (List (ShearCode (Fin v) s))) (hL : ∀ W∈L,UniformToeplitzChunkWord.Matching W) :
    ∀ s∈shearMacros refs L hL,s.Valid values := by
  intro s hs
  obtain ⟨W,_,rfl⟩ := List.mem_map.mp hs
  trivial

theorem map_attach_val {α β : Type} (L : List α) (f : α → β) :
    L.attach.map (fun x => f x.val)=L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.attach_cons,List.map_cons,List.map_map,Function.comp_def,ih]

theorem shearMacros_expand {v s l : ℕ} (refs : Fin s → Fin l) (values : Fin l → ℂ)
    (L : List (List (ShearCode (Fin v) s))) (hL : ∀ W∈L,UniformToeplitzChunkWord.Matching W) :
    expand values (shearMacros refs L hL) (shearMacros_valid refs values L hL)=
      UniformLocalFourierLayers.shearLayers (values ∘ refs) L hL := by
  simp only [expand,shearMacros,List.attach_map,List.map_map,Function.comp_def]
  simp only [matchingMacro_expand]
  change (L.attach.attach.map (fun x => UniformLocalFourierLayers.matchingLayers
    (values ∘ refs) x.val.val (hL _ x.val.property))).flatten=_
  rw [map_attach_val (L.attach) (fun x => UniformLocalFourierLayers.matchingLayers (values ∘ refs) x.val (hL _ x.property))]
  rfl

def sequence {l n : ℕ} : List (Macro l n) → Macro l n
  | [] => .nil n
  | s::W => .seq s (sequence W)

theorem sequence_valid {l n : ℕ} (values : Fin l → ℂ) (W : List (Macro l n))
    (hW : ∀ s∈W,s.Valid values) : (sequence W).Valid values := by
  induction W with
  | nil => trivial
  | cons s W ih => exact ⟨hW s (by simp),ih (fun t ht => hW t (by simp [ht]))⟩

theorem sequence_expand {l n : ℕ} (values : Fin l → ℂ) (W : List (Macro l n))
    (hW : ∀ s∈W,s.Valid values) :
    (sequence W).expand values (sequence_valid values W hW)=expand values W hW := by
  induction W with
  | nil => rfl
  | cons s W ih =>
    change s.expand values _++(sequence W).expand values _=_
    rw [ih (fun t ht => hW t (by simp [ht]))]
    simp only [expand,List.attach_cons,List.map_cons,List.flatten_cons,List.map_map,Function.comp_def]

theorem sequence_nil {l n : ℕ} : sequence ([] : List (Macro l n))=Macro.nil n := rfl

theorem sequence_cons {l n : ℕ} (t : Macro l n) (W : List (Macro l n)) :
    sequence (t::W)=Macro.seq t (sequence W) := rfl

attribute [irreducible] sequence

def Covered {r N o n : ℕ} (b : State r N o) (P : Plan n) (hN : n≤N) : Prop :=
  ∀ q∈requests P hN,q∈b.cache.map Cached.request

theorem preparePlan_covered {r N o : ℕ} (b : State r N o) (P : Plan N) :
    Covered (preparePlan b P) P (le_refl _) := by
  intro q hq
  rw [preparePlan,compileRequests_cache_requests]
  exact List.mem_append_right _ hq

def pairLayers (n : ℕ) (hv : 0<selected n)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :=
  let a := size (n-n/2) (selected n) q.1
  let e := size (n/2) (selected n) q.2
  UniformToeplitzChunkWord.chunkLayers (printedCross a e) (size_pos _ _ hv q.2)
    (UniformToeplitzChunkWord.selectedPlacement hv (size_mem _ _ q.1) (size_mem _ _ q.2)
      (pairSource n hv q.2) (pairTarget n hv q.1) (fun _ _ => left_right n _ _))
    (printedCross_depth a e) (by decide) (printedCross_fanout a e)

theorem pairLayers_matching (n : ℕ) (hv : 0<selected n)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) :
    ∀ W∈pairLayers n hv q,UniformToeplitzChunkWord.Matching W := by
  dsimp only [pairLayers]
  exact UniformToeplitzChunkWord.chunkLayers_matching _ _ _
    (printedCross_depth _ _) (by decide) (printedCross_fanout _ _)

def pairRefs {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n) (hN : n≤N)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n)))
    (hq : pairRequest hn hv hN q∈b.cache.map Cached.request) :
    Fin (UniformToeplitzCrossDAG.bankSize
      (exponent (size (n-n/2) (selected n) q.1) (size (n/2) (selected n) q.2))) → Fin b.length :=
  cacheRef b (pairRequest hn hv hN q) hq

def pairMacro {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n) (hN : n≤N)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n)))
    (hq : pairRequest hn hv hN q∈b.cache.map Cached.request) : Macro b.length n :=
  sequence (shearMacros (pairRefs b hn hv hN q hq) (pairLayers n hv q) (pairLayers_matching _ _ _))

attribute [irreducible] pairMacro pairRefs pairLayers

theorem pairMacro_valid {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n) (hN : n≤N)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n)))
    (hq : pairRequest hn hv hN q∈b.cache.map Cached.request) (values : Fin b.length → ℂ) :
    (pairMacro b hn hv hN q hq).Valid values := by
  unfold pairMacro
  exact sequence_valid values (shearMacros (pairRefs b hn hv hN q hq) (pairLayers n hv q)
    (pairLayers_matching n hv q))
    (shearMacros_valid (pairRefs b hn hv hN q hq) values (pairLayers n hv q) (pairLayers_matching n hv q))

theorem pairMacro_expand {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n) (hN : n≤N)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n)))
    (hq : pairRequest hn hv hN q∈b.cache.map Cached.request) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹)) :
    (pairMacro b hn hv hN q hq).expand (b.program.eval roots) (pairMacro_valid b hn hv hN q hq (b.program.eval roots))=
      UniformLocalFourierLayers.pairSchedule n hv f q := by
  unfold pairMacro
  rw [sequence_expand _ _ (shearMacros_valid _ _ _ _),shearMacros_expand]
  have he : b.program.eval roots ∘ pairRefs b hn hv hN q hq=
      (pairRequest hn hv hN q).bank (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) :=
    by
      funext j
      unfold pairRefs
      exact cacheRef_value b (pairRequest hn hv hN q) hq roots _ _ hc j
  rw [he]
  unfold pairLayers
  rfl

def operationMacro {n l : ℕ} (refs : Fin n → Fin l) : UniformDirectToeplitz.Operation n → Macro l n
  | .scale i => .scale i (refs ⟨0,by exact Nat.zero_lt_of_lt i.isLt⟩)
  | .shear i j => .shear i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩
      (Ne.symm (ne_of_lt j.isLt)) (.register (refs (UniformDirectToeplitz.coefficientIndex (.shear i j))) false)

theorem operationMacro_valid {n l : ℕ} (refs : Fin n → Fin l) (values : Fin l → ℂ)
    (hn : 0<n) (h0 : values (refs ⟨0,hn⟩)≠0) (op : UniformDirectToeplitz.Operation n) :
    (operationMacro refs op).Valid values := by
  cases op with
  | scale i => exact h0
  | shear i j => trivial

theorem operationMacro_expand {n l : ℕ} (refs : Fin n → Fin l) (values : Fin l → ℂ)
    (hn : 0<n) (h0 : values (refs ⟨0,hn⟩)≠0) (op : UniformDirectToeplitz.Operation n) :
    (operationMacro refs op).expand values (operationMacro_valid _ _ _ h0 op)=
      UniformLocalFourierLayers.serial (UniformDirectToeplitz.render (values ∘ refs) hn h0 op) := by
  cases op <;> rfl

def directMacro {n l : ℕ} (refs : Fin n → Fin l) : Macro l n :=
  sequence ((UniformDirectToeplitz.topology n).map (operationMacro refs))

theorem directMacro_valid {n l : ℕ} (refs : Fin n → Fin l) (values : Fin l → ℂ)
    (hn : 0<n) (h0 : values (refs ⟨0,hn⟩)≠0) : (directMacro refs).Valid values := by
  apply sequence_valid
  intro s hs
  obtain ⟨op,_,rfl⟩ := List.mem_map.mp hs
  exact operationMacro_valid _ _ _ h0 op

theorem directMacro_expand {n l : ℕ} (refs : Fin n → Fin l) (values : Fin l → ℂ)
    (hn : 0<n) (h0 : values (refs ⟨0,hn⟩)≠0) :
    (directMacro refs).expand values (directMacro_valid _ _ _ h0)=
      UniformLocalFourierLayers.serial (UniformDirectToeplitz.word (values ∘ refs) hn h0) := by
  change (sequence ((UniformDirectToeplitz.topology n).map (operationMacro refs))).expand values _=_
  rw [sequence_expand values _ (by
    intro s hs
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hs
    exact operationMacro_valid refs values hn h0 op)]
  simp only [expand,List.attach_map,List.map_map,Function.comp_def]
  have hm : ((UniformDirectToeplitz.topology n).attach.map (fun x =>
      (operationMacro refs x.val).expand values (operationMacro_valid refs values hn h0 x.val)))=
      (UniformDirectToeplitz.topology n).map (fun op =>
        UniformLocalFourierLayers.serial (UniformDirectToeplitz.render (values ∘ refs) hn h0 op)) := by
    calc
      _ = (UniformDirectToeplitz.topology n).attach.map (fun x =>
          UniformLocalFourierLayers.serial (UniformDirectToeplitz.render (values ∘ refs) hn h0 x.val)) := by
        apply List.map_congr_left
        intro x hx
        exact operationMacro_expand refs values hn h0 x.val
      _ = _ := map_attach_val (UniformDirectToeplitz.topology n)
        (fun op : UniformDirectToeplitz.Operation n =>
          UniformLocalFourierLayers.serial (UniformDirectToeplitz.render (values ∘ refs) hn h0 op))
  rw [hm]
  rw [show (UniformDirectToeplitz.topology n).map (fun op =>
      UniformLocalFourierLayers.serial (UniformDirectToeplitz.render (values ∘ refs) hn h0 op)) =
      ((UniformDirectToeplitz.topology n).map (UniformDirectToeplitz.render (values ∘ refs) hn h0)).map
        UniformLocalFourierLayers.serial from (List.map_map ..).symm]
  change (((UniformDirectToeplitz.topology n).map (UniformDirectToeplitz.render (values ∘ refs) hn h0)).map
    (List.map UniformLocalFourierLayers.Layer.step)).flatten=_
  rw [←List.map_flatten,UniformDirectToeplitz.render_topology]
  rfl

/-! Literal scalars are appended once to the same register program. -/
structure LiteralExtension (r l : ℕ) where
  length : ℕ
  program : UniformScalarPreparation.Program r length
  old : Fin l → Fin length
  refs : List (Fin length)

def appendLiterals {r l : ℕ} (p : UniformScalarPreparation.Program r l) : List ℚ → LiteralExtension r l
  | [] => ⟨l,p,id,[]⟩
  | q::qs =>
    let f := appendLiterals (.step p (.rational q)) qs
    ⟨f.length,f.program,fun j => f.old j.castSucc,f.old (Fin.last l)::f.refs⟩

theorem appendLiterals_length {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) :
    (appendLiterals p qs).length=l+qs.length := by
  induction qs generalizing l with
  | nil => simp [appendLiterals]
  | cons q qs ih => rw [appendLiterals,ih];simp;omega

theorem appendLiterals_refs_length {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) :
    (appendLiterals p qs).refs.length=qs.length := by
  induction qs generalizing l with
  | nil => rfl
  | cons q qs ih => simp only [appendLiterals,List.length_cons,ih]

theorem appendLiterals_old_val {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) (j : Fin l) :
    ((appendLiterals p qs).old j).val=j.val := by
  induction qs generalizing l with
  | nil => rfl
  | cons q qs ih => exact ih (.step p (.rational q)) j.castSucc

theorem appendLiterals_old {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (roots : Fin r → ℂ) (j : Fin l) :
    (appendLiterals p qs).program.eval roots ((appendLiterals p qs).old j)=p.eval roots j := by
  induction qs generalizing l with
  | nil => rfl
  | cons q qs ih =>
    exact (ih (.step p (.rational q)) j.castSucc).trans
      (by simp only [UniformScalarPreparation.Program.eval,Fin.snoc_castSucc])

theorem appendLiterals_values {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (roots : Fin r → ℂ) :
    (appendLiterals p qs).refs.map ((appendLiterals p qs).program.eval roots)=qs.map (fun q : ℚ => (q:ℂ)) := by
  induction qs generalizing l with
  | nil => rfl
  | cons q qs ih =>
    simp only [appendLiterals,List.map_cons,appendLiterals_old,ih]
    simp only [UniformScalarPreparation.Program.eval,Fin.snoc_last,Instruction.eval]

theorem appendLiterals_admissible {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (roots : Fin r → ℂ) (hp : p.Admissible roots) : (appendLiterals p qs).program.Admissible roots := by
  induction qs generalizing l with
  | nil => exact hp
  | cons q qs ih =>
    apply ih (.step p (.rational q))
    exact And.intro hp trivial

theorem appendLiterals_counts {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) :
    (appendLiterals p qs).program.rootReads=p.rootReads ∧ (appendLiterals p qs).program.divisions=p.divisions := by
  induction qs generalizing l with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs ih => simpa only [appendLiterals,Program.rootReads,Program.divisions,Instruction.rootReads,
      Instruction.divisions,Nat.add_zero] using ih (.step p (.rational q))

def literalRef {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) (q : ℚ) (hq : q∈qs) :
    Fin (appendLiterals p qs).length :=
  (appendLiterals p qs).refs[qs.idxOf q]'(by
    rw [appendLiterals_refs_length]
    exact List.idxOf_lt_length_iff.mpr hq)

theorem literalRef_value {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) (q : ℚ)
    (hq : q∈qs) (roots : Fin r → ℂ) :
    (appendLiterals p qs).program.eval roots (literalRef p qs q hq)=(q:ℂ) := by
  have h := congrArg (fun L : List ℂ => L[qs.idxOf q]?) (appendLiterals_values p qs roots)
  have hi := List.idxOf_lt_length_iff.mpr hq
  have ho : qs.idxOf q<(appendLiterals p qs).refs.length := by simpa only [appendLiterals_refs_length] using hi
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ho,
    Option.map_some,List.getElem_idxOf hi,Option.some.injEq,literalRef] using h

def literalState {r N o : ℕ} (b : State r N o) (qs : List ℚ) : State r N o :=
  let f := appendLiterals b.program qs
  ⟨f.length,f.program,f.old ∘ b.original,f.old ∘ b.h,f.old ∘ b.g,f.old ∘ b.omega,
    b.cache.map (fun c => c.map f.old)⟩

def Atom.literals {l : ℕ} : Atom l → List ℚ
  | .literal q => [q]
  | .register _ _ => []

/-- A literal becomes its actual printed scalar register. Prepared references
are retained, with their original sign bit. -/
def bindAtom {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (t : Atom l) (ht : ∀ q∈t.literals,q∈qs) : Atom (appendLiterals p qs).length :=
  match t with
  | .literal q => .register (literalRef p qs q (ht q (by simp [Atom.literals]))) false
  | .register j neg => .register ((appendLiterals p qs).old j) neg

theorem bindAtom_value {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (t : Atom l) (ht : ∀ q∈t.literals,q∈qs) (roots : Fin r → ℂ) :
    (bindAtom p qs t ht).value ((appendLiterals p qs).program.eval roots)=t.value (p.eval roots) := by
  cases t with
  | literal q => exact literalRef_value _ _ _ _ _
  | register j neg => simp only [bindAtom,Atom.value,appendLiterals_old]

theorem Covered.left {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n)
    (L : Plan (n/2)) (R : Plan (n-n/2)) (hN : n≤N)
    (hc : Covered b (.split n hn hv L R) hN) : Covered b L (by omega) := by
  intro q hq
  apply hc q
  change q∈requests L _++requests R _++(pairs n).map (pairRequest hn hv hN)
  exact List.mem_append_left _ (List.mem_append_left _ hq)

theorem Covered.right {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n)
    (L : Plan (n/2)) (R : Plan (n-n/2)) (hN : n≤N)
    (hc : Covered b (.split n hn hv L R) hN) : Covered b R (by omega) := by
  intro q hq
  apply hc q
  change q∈requests L _++requests R _++(pairs n).map (pairRequest hn hv hN)
  exact List.mem_append_left _ (List.mem_append_right _ hq)

theorem Covered.pair {r N o n : ℕ} (b : State r N o) (hn : 2≤n) (hv : 0<selected n)
    (L : Plan (n/2)) (R : Plan (n-n/2)) (hN : n≤N)
    (hc : Covered b (.split n hn hv L R) hN)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) (hq : q∈pairs n) :
    pairRequest hn hv hN q∈b.cache.map Cached.request := by
  apply hc
  change pairRequest hn hv hN q∈requests L _++requests R _++(pairs n).map (pairRequest hn hv hN)
  exact List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩)

def axisRefs {r N o n : ℕ} (b : State r N o) (hN : n≤N) : Fin n → Fin b.length :=
  fun j => b.h ⟨j.val,j.isLt.trans_le hN⟩

def renderMacro {r N o n : ℕ} (b : State r N o) (P : Plan n) (hN : n≤N) (hc : Covered b P hN) : Macro b.length n :=
  match P with
  | .direct n _ => if hn : 0<n then directMacro (axisRefs b hN) else .nil n
  | .split n hn hv L R => .seq
      (.parallel (coordinates n)
        (renderMacro b L (by omega) (Covered.left b hn hv L R hN hc))
        (renderMacro b R (by omega) (Covered.right b hn hv L R hN hc)))
      (sequence ((pairs n).attach.map (fun q => pairMacro b hn hv hN q.val
        (Covered.pair b hn hv L R hN hc q.val q.property))))

theorem renderMacro_valid {r N o n : ℕ} (b : State r N o) (P : Plan n) (hN : n≤N) (hc : Covered b P hN)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hf : PowerSeries.constantCoeff f≠0) : (renderMacro b P hN hc).Valid (b.program.eval roots) := by
  induction P with
  | direct n cap =>
    dsimp only [renderMacro]
    split_ifs with hn
    · apply directMacro_valid _ _ hn
      dsimp only [axisRefs]
      rw [hi.1]
      simpa only [Fin.val_zero,PowerSeries.coeff_zero_eq_constantCoeff] using hf
    · trivial
  | split n hn hv L R ihL ihR =>
    change ((renderMacro b L _ _).Valid _ ∧ (renderMacro b R _ _).Valid _) ∧ _
    refine ⟨⟨ihL _ _,ihR _ _⟩,?_⟩
    apply sequence_valid
    intro s hs
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hs
    exact pairMacro_valid b hn hv hN q.val _ _

theorem renderMacro_expand {r N o n : ℕ} (b : State r N o) (P : Plan n) (hN : n≤N) (hc : Covered b P hN)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hg : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹)) (hf : PowerSeries.constantCoeff f≠0) :
    (renderMacro b P hN hc).expand (b.program.eval roots) (renderMacro_valid b P hN hc roots f hi hf)=
      UniformLocalFourierLayers.render P f hf := by
  induction P with
  | direct n cap =>
    dsimp only [renderMacro,UniformLocalFourierLayers.render,UniformBalancedToeplitz.render]
    split_ifs with hn
    · have h0 : b.program.eval roots (axisRefs b hN ⟨0,hn⟩)≠0 := by
        dsimp only [axisRefs]
        rw [hi.1]
        simpa only [Fin.val_zero,PowerSeries.coeff_zero_eq_constantCoeff] using hf
      rw [directMacro_expand (axisRefs b hN) (b.program.eval roots) hn h0]
      have he : b.program.eval roots ∘ axisRefs b hN=(fun j : Fin n => PowerSeries.coeff j.val f) :=
        funext (fun j => hi.1 ⟨j.val,j.isLt.trans_le hN⟩)
      simp only [he]
    · rfl
  | split n hn hv L R ihL ihR =>
    change UniformLocalFourierLayers.parallel (coordinates n)
        ((renderMacro b L _ _).expand _ _) ((renderMacro b R _ _).expand _ _) ++
        (sequence _).expand _ _=_
    rw [ihL _ _,ihR _ _,sequence_expand _ _ (by
      intro s hs
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hs
      exact pairMacro_valid b hn hv hN q.val _ (b.program.eval roots))]
    simp only [expand,List.attach_map,List.map_map,Function.comp_def]
    have he : ((pairs n).attach.attach.map (fun q =>
        (pairMacro b hn hv hN q.val.val (Covered.pair b hn hv L R hN hc q.val.val q.val.property)).expand
          (b.program.eval roots) (pairMacro_valid b hn hv hN q.val.val
            (Covered.pair b hn hv L R hN hc q.val.val q.val.property) (b.program.eval roots))))=
        (pairs n).map (UniformLocalFourierLayers.pairSchedule n hv f) := by
      calc
        _ = (pairs n).attach.attach.map (fun q => UniformLocalFourierLayers.pairSchedule n hv f q.val.val) := by
          apply List.map_congr_left
          intro q hq
          exact pairMacro_expand b hn hv hN q.val.val _ roots f hg
        _ = _ := by
          rw [map_attach_val (pairs n).attach
            (fun q => UniformLocalFourierLayers.pairSchedule n hv f q.val)]
          exact map_attach_val (pairs n) (UniformLocalFourierLayers.pairSchedule n hv f)
    rw [he]
    rfl

def Macro.literals {l : ℕ} : {n : ℕ} → Macro l n → List ℚ
  | _,.scale _ _ => []
  | _,.shear _ _ _ t => t.literals
  | _,.matching _ coeff => (List.ofFn coeff).flatMap Atom.literals
  | _,.parallel _ L R => L.literals++R.literals
  | _,.seq L R => L.literals++R.literals
  | _,.nil _ => []

def bindMacro {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ) :
    {n : ℕ} → (s : Macro l n) → (∀ q∈s.literals,q∈qs) → Macro (appendLiterals p qs).length n
  | _,.scale i c,_ => .scale i ((appendLiterals p qs).old c)
  | _,.shear i j h t,ht => .shear i j h (bindAtom p qs t ht)
  | _,.matching position coeff,ht => .matching position (fun i => bindAtom p qs (coeff i) (by
      intro q hq
      exact ht q (List.mem_flatMap.mpr ⟨coeff i,List.mem_ofFn.mpr ⟨i,rfl⟩,hq⟩)))
  | _,.parallel e L R,ht => .parallel e
      (bindMacro p qs L (fun q hq => ht q (List.mem_append_left _ hq)))
      (bindMacro p qs R (fun q hq => ht q (List.mem_append_right _ hq)))
  | _,.seq L R,ht => .seq
      (bindMacro p qs L (fun q hq => ht q (List.mem_append_left _ hq)))
      (bindMacro p qs R (fun q hq => ht q (List.mem_append_right _ hq)))
  | _,.nil n,_ => .nil n

theorem bindMacro_valid {r l n : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (s : Macro l n) (ht : ∀ q∈s.literals,q∈qs) (roots : Fin r → ℂ) (hs : s.Valid (p.eval roots)) :
    (bindMacro p qs s ht).Valid ((appendLiterals p qs).program.eval roots) := by
  induction s with
  | scale i c => change (appendLiterals p qs).program.eval roots ((appendLiterals p qs).old c)≠0;rw [appendLiterals_old];exact hs
  | shear i j h t => trivial
  | matching position coeff => trivial
  | parallel e L R ihL ihR => exact ⟨ihL _ hs.1,ihR _ hs.2⟩
  | seq L R ihL ihR => exact ⟨ihL _ hs.1,ihR _ hs.2⟩
  | nil n => trivial

theorem bindMacro_expand {r l n : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (s : Macro l n) (ht : ∀ q∈s.literals,q∈qs) (roots : Fin r → ℂ) (hs : s.Valid (p.eval roots)) :
    (bindMacro p qs s ht).expand ((appendLiterals p qs).program.eval roots) (bindMacro_valid _ _ _ _ _ hs)=
      s.expand (p.eval roots) hs := by
  induction s with
  | scale i c =>
    change [UniformLocalFourierLayers.Layer.step (UniformDirectToeplitz.scaleStep i _ _)]=_
    simp only [appendLiterals_old]
    rfl
  | shear i j h t =>
    change ∀ q∈t.literals,q∈qs at ht
    change UniformLocalFourierLayers.serial (TensorWords.embeddedWord (Embedded.pair i j h)
      (UniformLocalShear.word ((bindAtom p qs t ht).value _)))=_
    rw [bindAtom_value]
    rfl
  | matching position coeff =>
    change UniformLocalFourierLayers.batchWords 28 position
      (fun i => UniformLocalShear.word ((bindAtom p qs (coeff i) _).value _)) _=_
    simp only [bindAtom_value]
    rfl
  | parallel e L R ihL ihR =>
    change UniformLocalFourierLayers.parallel e
      ((bindMacro p qs L _).expand _ _) ((bindMacro p qs R _).expand _ _)=_
    rw [ihL _ hs.1,ihR _ hs.2]
    rfl
  | seq L R ihL ihR =>
    change (bindMacro p qs L _).expand _ _++(bindMacro p qs R _).expand _ _=_
    rw [ihL _ hs.1,ihR _ hs.2]
    rfl
  | nil n => rfl

theorem bindAtom_no_literals {r l : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (t : Atom l) (ht : ∀ q∈t.literals,q∈qs) : (bindAtom p qs t ht).literals=[] := by
  cases t <;> rfl

theorem bindMacro_no_literals {r l n : ℕ} (p : UniformScalarPreparation.Program r l) (qs : List ℚ)
    (s : Macro l n) (ht : ∀ q∈s.literals,q∈qs) : (bindMacro p qs s ht).literals=[] := by
  induction s with
  | scale i c => rfl
  | shear i j h t => cases t <;> rfl
  | matching position coeff =>
    change (List.ofFn (fun i => bindAtom p qs (coeff i) _)).flatMap Atom.literals=[]
    apply List.flatMap_eq_nil_iff.mpr
    intro t ht'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht'
    exact bindAtom_no_literals _ _ (coeff i) _
  | parallel e L R ihL ihR => simp only [bindMacro,Macro.literals,ihL,ihR,List.nil_append]
  | seq L R ihL ihR => simp only [bindMacro,Macro.literals,ihL,ihR,List.nil_append]
  | nil n => rfl

open UniformShearPreparation

def scalarIndex {l : ℕ} (t : Atom l) (ht : t.literals=[]) : Fin l × Fin 2 :=
  match t with
  | .register j neg => (j,if neg then 1 else 0)
  | .literal q => False.elim (by simp [Atom.literals] at ht)

theorem scalarIndex_value {l : ℕ} (t : Atom l) (ht : t.literals=[]) (v : Fin l → ℂ) :
    (if (scalarIndex t ht).2.val=0 then v (scalarIndex t ht).1 else -v (scalarIndex t ht).1)=t.value v := by
  cases t with
  | register j neg => cases neg <;> rfl
  | literal q => simp [Atom.literals] at ht

/-- Every varying diagonal in each occurrence reads one row of the SINGLE
finished bank. Zero coefficients use exactly the same six-C schema. -/
noncomputable def registerWord {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (rr j)=roots j) (t : Atom b.length) (ht : t.literals=[]) : List Step :=
  let js := scalarIndex t ht
  let row := fun q => (finish b rr).env.program.eval roots ((finish b rr).rows (finishIndex b js.1 js.2) q)
  scaledWord (row 2) (row 3) (finish_scales_ne_zero _ _ _ unit hr _ _ _) (finish_scales_ne_zero _ _ _ unit hr _ _ _) ++
  scaledWord (row 4) (row 5) (finish_scales_ne_zero _ _ _ unit hr _ _ _) (finish_scales_ne_zero _ _ _ unit hr _ _ _)

theorem registerWord_eq {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (rr j)=roots j) (t : Atom b.length) (ht : t.literals=[]) :
    registerWord b rr roots unit hr t ht=UniformLocalShear.word (t.value (b.program.eval roots)) := by
  let mu := t.value (b.program.eval roots)
  have hs (q : Fin 6) : (finish b rr).env.program.eval roots
      ((finish b rr).rows (finishIndex b (scalarIndex t ht).1 (scalarIndex t ht).2) q)=rowExpected mu q := by
    rw [finish_scales _ _ _ unit hr,scalarIndex_value]
  unfold registerWord
  exact congrArg₂ List.append
    (scaledWord_eq_of_values (UniformLocalShear.kappa mu) (UniformLocalShear.kappa_ne_zero mu)
      _ _ _ _ (by simpa [rowExpected] using hs 2) (by simpa [rowExpected] using hs 3))
    (scaledWord_eq_of_values (mu-UniformLocalShear.kappa mu) (UniformLocalShear.second_ne_zero mu)
      _ _ _ _ (by simpa [rowExpected] using hs 4) (by simpa [rowExpected] using hs 5))


/-- No coefficient literals remain in a bound matching layer. -/
theorem matching_no_literals {l s : ℕ} (coeff : Fin s → Atom l)
    (h : (List.ofFn coeff).flatMap Atom.literals=[]) (i : Fin s) : (coeff i).literals=[] :=
  List.flatMap_eq_nil_iff.mp h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem registerWord_length {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (rr j)=roots j) (t : Atom b.length) (ht : t.literals=[]) :
    (registerWord b rr roots unit hr t ht).length=28 := by
  rw [registerWord_eq]
  exact UniformLocalFourierLayers.localShear_length _

/-- Each scaling and six-C occurrence reads the SAME finished register bank.
The fixed C macro constants are the existing scalar schema; their separate
once-per-algorithm prepared-constant adapter is not asserted here. -/
noncomputable def referenceExpand {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1) (hr : ∀ j,b.program.eval roots (rr j)=roots j) :
    {n : ℕ} → (s : Macro b.length n) → s.Valid (b.program.eval roots) → s.literals=[] →
      List (UniformLocalFourierLayers.Layer n)
  | _,.scale i c,h,_ => [.step (UniformDirectToeplitz.scaleStep i
      ((finish b rr).env.program.eval roots ((finish b rr).env.mu (finishIndex b c 0)))
      (by rw [finish_value b rr roots unit hr c 0];exact h))]
  | _,.shear i j hij t,_,ht => UniformLocalFourierLayers.serial
      (TensorWords.embeddedWord (Embedded.pair i j hij) (registerWord b rr roots unit hr t ht))
  | _,.matching position coeff,_,ht => UniformLocalFourierLayers.batchWords 28 position
      (fun i => registerWord b rr roots unit hr (coeff i) (matching_no_literals coeff ht i))
      (fun i => registerWord_length b rr roots unit hr (coeff i) (matching_no_literals coeff ht i))
  | _,.parallel e L R,h,ht => UniformLocalFourierLayers.parallel e
      (referenceExpand b rr roots unit hr L h.1 (List.append_eq_nil_iff.mp ht).1)
      (referenceExpand b rr roots unit hr R h.2 (List.append_eq_nil_iff.mp ht).2)
  | _,.seq L R,h,ht => referenceExpand b rr roots unit hr L h.1 (List.append_eq_nil_iff.mp ht).1 ++
      referenceExpand b rr roots unit hr R h.2 (List.append_eq_nil_iff.mp ht).2
  | _,.nil _,_,_ => []

theorem referenceExpand_eq {r N o n : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1) (hr : ∀ j,b.program.eval roots (rr j)=roots j)
    (s : Macro b.length n) (hs : s.Valid (b.program.eval roots)) (ht : s.literals=[]) :
    referenceExpand b rr roots unit hr s hs ht=s.expand (b.program.eval roots) hs := by
  induction s with
  | scale i c =>
    change [UniformLocalFourierLayers.Layer.step (UniformDirectToeplitz.scaleStep i _ _)]=_
    simp only [finish_value b rr roots unit hr c 0,Fin.val_zero,ite_true]
    rfl
  | shear i j hij t =>
    change t.literals=[] at ht
    change UniformLocalFourierLayers.serial (TensorWords.embeddedWord (Embedded.pair i j hij)
      (registerWord b rr roots unit hr t ht))=_
    rw [registerWord_eq]
    rfl
  | matching position coeff =>
    change UniformLocalFourierLayers.batchWords 28 position
      (fun i => registerWord b rr roots unit hr (coeff i) _) _=_
    simp only [registerWord_eq]
    rfl
  | parallel e L R ihL ihR =>
    change UniformLocalFourierLayers.parallel e (referenceExpand b rr roots unit hr L _ _)
      (referenceExpand b rr roots unit hr R _ _)=_
    rw [ihL _ _,ihR _ _]
    rfl
  | seq L R ihL ihR =>
    change referenceExpand b rr roots unit hr L _ _++referenceExpand b rr roots unit hr R _ _=_
    rw [ihL _ _,ihR _ _]
    rfl
  | nil n => rfl

/-- A computable C-call count for the reference syntax. -/
def Macro.cost {l : ℕ} : {n : ℕ} → Macro l n → ℕ
  | _,.scale _ _ => 0
  | _,.shear _ _ _ _ => 6
  | _,@Macro.matching _ _ s _ _ => 6*s
  | _,.parallel _ L R => L.cost+R.cost
  | _,.seq L R => L.cost+R.cost
  | _,.nil _ => 0

theorem Macro.cost_eq {l n : ℕ} (s : Macro l n) (v : Fin l → ℂ) (hs : s.Valid v) :
    s.cost=UniformLocalFourierLayers.calls (s.expand v hs) := by
  induction s with
  | scale i c => rfl
  | shear i j h t =>
    simp only [cost,expand,UniformLocalFourierLayers.serial_calls,TensorWords.embeddedWord_calls,
      UniformLocalShear.word_calls]
  | matching position coeff =>
    simp only [cost,expand,UniformLocalFourierLayers.batchWords_calls,UniformLocalShear.word_calls,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  | parallel e L R ihL ihR =>
    simp only [cost,expand,UniformLocalFourierLayers.parallel_calls,←ihL hs.1,←ihR hs.2]
  | seq L R ihL ihR =>
    simp only [cost,expand,UniformLocalFourierLayers.calls_append,←ihL hs.1,←ihR hs.2]
  | nil n => rfl

theorem Atom.literals_length {l : ℕ} (t : Atom l) : t.literals.length≤1 := by
  cases t <;> simp [literals]

theorem literal_list_bound {l : ℕ} (L : List (Atom l)) : (L.flatMap Atom.literals).length≤L.length := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have ht := t.literals_length
    omega

theorem Macro.literals_bound {l n : ℕ} (s : Macro l n) : s.literals.length ≤ s.cost := by
  induction s with
  | scale i c => rfl
  | shear i j h t =>
    change t.literals.length≤6
    exact t.literals_length.trans (by omega)
  | matching position coeff =>
    have h := literal_list_bound (List.ofFn coeff)
    simp only [List.length_ofFn] at h
    exact h.trans (by dsimp only [cost];omega)
  | parallel e L R ihL ihR => simpa only [literals,cost,List.length_append] using Nat.add_le_add ihL ihR
  | seq L R ihL ihR => simpa only [literals,cost,List.length_append] using Nat.add_le_add ihL ihR
  | nil n => rfl

def planState {r N o : ℕ} (b : State r N o) (P : Plan N) : State r N o :=
  let raw := preparePlan b P
  literalState raw (renderMacro raw P (le_refl _) (preparePlan_covered b P)).literals

def planMacro {r N o : ℕ} (b : State r N o) (P : Plan N) : Macro (planState b P).length N :=
  let raw := preparePlan b P
  let m := renderMacro raw P (le_refl _) (preparePlan_covered b P)
  bindMacro raw.program m.literals m (fun _ h => h)

theorem planMacro_no_literals {r N o : ℕ} (b : State r N o) (P : Plan N) :
    (planMacro b P).literals=[] := bindMacro_no_literals _ _ _ _

theorem planMacro_valid {r N o : ℕ} (b : State r N o) (P : Plan N)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hf : PowerSeries.constantCoeff f≠0) : (planMacro b P).Valid ((planState b P).program.eval roots) :=
  bindMacro_valid _ _ _ _ roots
    (renderMacro_valid _ _ _ _ roots f (compileRequests_inputs b _ roots _ _ hi) hf)

theorem planMacro_expand {r N o : ℕ} (b : State r N o) (P : Plan N)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    (planMacro b P).expand ((planState b P).program.eval roots) (planMacro_valid b P roots f hi hf)=
      UniformLocalFourierLayers.render P f hf := by
  let raw := preparePlan b P
  let m := renderMacro raw P (le_refl _) (preparePlan_covered b P)
  have hv := renderMacro_valid raw P (le_refl _) (preparePlan_covered b P) roots f
    (compileRequests_inputs b _ roots _ _ hi) hf
  change (bindMacro raw.program m.literals m (fun _ h => h)).expand
    ((appendLiterals raw.program m.literals).program.eval roots) _=_
  exact (bindMacro_expand raw.program m.literals m (fun _ h => h) roots hv).trans
    (renderMacro_expand raw P (le_refl _) (preparePlan_covered b P) roots f
      (compileRequests_inputs b _ roots _ _ hi) (compileRequests_cache_good b _ roots _ _ ha hi hc) hf)

theorem planState_original {r N o : ℕ} (b : State r N o) (P : Plan N)
    (roots : Fin r → ℂ) (j : Fin o) :
    (planState b P).program.eval roots ((planState b P).original j)=b.program.eval roots (b.original j) := by
  exact (appendLiterals_old _ _ roots _).trans (compileRequests_original b _ roots j)

theorem planState_admissible {r N o : ℕ} (b : State r N o) (P : Plan N)
    (roots : Fin r → ℂ) (hb : b.program.Admissible roots) : (planState b P).program.Admissible roots :=
  appendLiterals_admissible _ _ roots (compileRequests_admissible b _ roots hb)

theorem planState_rootReads {r N o : ℕ} (b : State r N o) (P : Plan N) :
    (planState b P).program.rootReads=b.program.rootReads :=
  (appendLiterals_counts _ _).1.trans (compileRequests_counts b _).1

theorem planState_length {r N o : ℕ} (b : State r N o) (P : Plan N)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    (planState b P).length≤b.length+1000*(N+1)^4+16*N^3 := by
  have he := renderMacro_expand (preparePlan b P) P (le_refl _) (preparePlan_covered b P) roots f
    (compileRequests_inputs b _ roots _ _ hi) (compileRequests_cache_good b _ roots _ _ ha hi hc) hf
  have hl := (renderMacro (preparePlan b P) P (le_refl _) (preparePlan_covered b P)).literals_bound
  have hv := renderMacro_valid (preparePlan b P) P (le_refl _) (preparePlan_covered b P) roots f
    (compileRequests_inputs b _ roots _ _ hi) hf
  have hcost := (Macro.cost_eq (renderMacro (preparePlan b P) P (le_refl _) (preparePlan_covered b P))
    ((preparePlan b P).program.eval roots) hv).trans (congrArg UniformLocalFourierLayers.calls he)
  rw [hcost,UniformLocalFourierLayers.render_calls] at hl
  have hb := preparePlan_length b P
  have hm := UniformBalancedToeplitz.render_call_bound P f hf
  change (appendLiterals _ _).length≤_
  rw [appendLiterals_length]
  omega

/-- Concrete all-register balanced schedule, with a single shared scale bank.
Inputs/seed-root facts are coefficient-table facts, never action premises. -/
noncomputable def balancedSchedule {r N o : ℕ} (b : State r N o) (P : Plan N)
    (rr : Fin r → Fin o) (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hf : PowerSeries.constantCoeff f≠0) : List (UniformLocalFourierLayers.Layer N) :=
  referenceExpand (planState b P) (fun j => (planState b P).original (rr j)) roots unit
    (fun j => (planState_original b P roots _).trans (hr j)) (planMacro b P)
    (planMacro_valid b P roots f hi hf) (planMacro_no_literals b P)

theorem balancedSchedule_eq {r N o : ℕ} (b : State r N o) (P : Plan N)
    (rr : Fin r → Fin o) (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    balancedSchedule b P rr roots unit hr f hi hf=UniformLocalFourierLayers.render P f hf := by
  rw [balancedSchedule,referenceExpand_eq,planMacro_expand b P roots f hi hc ha hf]

theorem balancedSchedule_matrix {r N o : ℕ} (b : State r N o) (P : Plan N)
    (rr : Fin r → Fin o) (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    UniformLocalFourierLayers.matrix (balancedSchedule b P rr roots unit hr f hi hf)=
      CoefficientTime.truncMatrix N f := by
  rw [balancedSchedule_eq b P rr roots unit hr f hi hc ha hf,UniformLocalFourierLayers.render_matrix]
  exact UniformBalancedToeplitz.render_matrix P f hf

theorem balancedSchedule_calls {r N o : ℕ} (b : State r N o) (P : Plan N)
    (rr : Fin r → Fin o) (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    UniformLocalFourierLayers.calls (balancedSchedule b P rr roots unit hr f hi hf)=
      wordCalls (UniformBalancedToeplitz.render P f hf) := by
  rw [balancedSchedule_eq b P rr roots unit hr f hi hc ha hf,UniformLocalFourierLayers.render_calls]

theorem balancedSchedule_length {r N o : ℕ} (b : State r N o) (P : Plan N)
    (rr : Fin r → Fin o) (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots)
    (hf : PowerSeries.constantCoeff f≠0) :
    (balancedSchedule b P rr roots unit hr f hi hf).length≤depthUnit*(Nat.clog 2 N+1)^4 := by
  rw [balancedSchedule_eq b P rr roots unit hr f hi hc ha hf]
  exact UniformLocalFourierLayers.render_length P f hf


/-- The one bank used by all balanced occurrences and final diagonal refs. -/
def planBank {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o) :=
  finish (planState b P) (fun j => (planState b P).original (rr j))

theorem planBank_admissible {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1) (ha : b.program.Admissible roots)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j) :
    (planBank b P rr).env.program.Admissible roots :=
  finish_admissible _ _ roots unit (planState_admissible b P roots ha)
    (fun j => (planState_original b P roots _).trans (hr j))

theorem planBank_rootReads {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o) :
    (planBank b P rr).env.program.rootReads=b.program.rootReads :=
  (finish_rootReads _ _).trans (planState_rootReads b P)

theorem planBank_length {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots) (hf : PowerSeries.constantCoeff f≠0) :
    (planBank b P rr).env.length≤20*b.length+20000*(N+1)^4+320*N^3+r+44 := by
  have h := finish_length (planState b P) (fun j => (planState b P).original (rr j))
  have hs := planState_length b P roots f hi hc ha hf
  dsimp only [planBank]
  omega

theorem planBank_references {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ) (hi : b.Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹))
    (ha : b.program.Admissible roots) (hf : PowerSeries.constantCoeff f≠0) :
    referencesBound (20*b.length+20000*(N+1)^4+320*N^3+r+44) (planBank b P rr).env.program :=
  referencesBound_of_length _ (by omega) (planBank_length b P rr roots f hi hc ha hf)

/-- A retained seed reference in the actual final register program. -/
def finalRef {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o) (j : Fin o) :
    Fin (planBank b P rr).env.length :=
  (planBank b P rr).env.mu (finishIndex (planState b P) ((planState b P).original j) 0)

theorem finalRef_value {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j) (j : Fin o) :
    (planBank b P rr).env.program.eval roots (finalRef b P rr j)=b.program.eval roots (b.original j) := by
  rw [finalRef,planBank,finish_value _ _ roots unit
    (fun j => (planState_original b P roots _).trans (hr j))]
  exact planState_original b P roots j

/-- Each diagonal coordinate is a literal finite register ref, in the same bank. -/
noncomputable def diagonalReferences {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (refs : Fin N → Fin o) (hnz : ∀ j,b.program.eval roots (b.original (refs j))≠0) :
    UniformLocalFourierLayers.Layer N := .step (UniformLocalFourierWord.diagonalStep
      (fun j => (planBank b P rr).env.program.eval roots (finalRef b P rr (refs j)))
      (fun j => by rw [finalRef_value b P rr roots unit hr];exact hnz j))

theorem diagonalReferences_eq {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (refs : Fin N → Fin o) (hnz : ∀ j,b.program.eval roots (b.original (refs j))≠0) :
    diagonalReferences b P rr roots unit hr refs hnz=UniformLocalFourierLayers.Layer.step
      (UniformLocalFourierWord.diagonalStep (fun j => b.program.eval roots (b.original (refs j))) hnz) := by
  unfold diagonalReferences
  simp only [finalRef_value b P rr roots unit hr]

/-- Actual Newton table references, not a full-bank or matrix-action premise. -/
structure NewtonReferences {r N o : ℕ} (b : State r N o) (roots : Fin r → ℂ) (omega : ℂ) where
  H : Fin N → Fin o
  scale : Fin N → Fin o
  inverseDiagonal : Fin N → Fin o
  H_value : ∀ j,b.program.eval roots (b.original (H j))=NewtonFourier.H omega j.val
  scale_value : ∀ j,b.program.eval roots (b.original (scale j))=NewtonFourier.scale omega j.val
  inverseDiagonal_value : ∀ j,b.program.eval roots (b.original (inverseDiagonal j))=
    (UniformNewton.diagonalValue omega j.val)⁻¹

/-- One-bank Newton factor schedule, retaining the full balanced layer topology. -/
noncomputable def newtonSchedule {r N o : ℕ} (b : State r N o) (P : Plan N) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) : List (UniformLocalFourierLayers.Layer N) :=
  [diagonalReferences b P rr roots unit hr tab.scale
    (fun j => by rw [tab.scale_value];exact UniformNewton.scaleValue_ne_zero hn hroot j)] ++
  balancedSchedule b P rr roots unit hr (NewtonFourier.invH omega) hi (by simp) ++
  [diagonalReferences b P rr roots unit hr tab.H
    (fun j => by rw [tab.H_value];exact UniformNewton.Hvalue_ne_zero hroot j)]

theorem newtonSchedule_eq {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    newtonSchedule b (plan N) rr roots unit hr hn hroot tab hi=UniformLocalFourierLayers.Nschedule hn hroot := by
  unfold newtonSchedule UniformLocalFourierLayers.Nschedule UniformLocalFourierLayers.sandwich
  rw [balancedSchedule_eq b (plan N) rr roots unit hr _ hi hc ha (by simp)]
  simp only [diagonalReferences_eq,tab.scale_value,tab.H_value]
  rfl

/-- Transposition is the actual reversed layer list and uses the same bank.
All scalar inputs to the Newton diagonals are explicit finite seed refs. -/
noncomputable def fourierSchedule {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) : List (UniformLocalFourierLayers.Layer N) :=
  let S := newtonSchedule b (plan N) rr roots unit hr hn hroot tab hi
  UniformLocalFourierLayers.transpose S ++
  [diagonalReferences b (plan N) rr roots unit hr tab.inverseDiagonal
    (fun j => by rw [tab.inverseDiagonal_value];exact inv_ne_zero (UniformNewton.diagonalValue_ne_zero hn hroot j))] ++ S

theorem fourierSchedule_eq {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    fourierSchedule b rr roots unit hr hn hroot tab hi=UniformLocalFourierLayers.schedule hn hroot := by
  unfold fourierSchedule UniformLocalFourierLayers.schedule UniformLocalFourierLayers.symmetric
  rw [newtonSchedule_eq b rr roots unit hr hn hroot tab hi hc ha]
  simp only [diagonalReferences_eq,tab.inverseDiagonal_value]

/-- Exact Fourier action from finite register/seed facts only. No circuit action
or complete-preparation hypothesis occurs in this statement. -/
theorem fourierSchedule_matrix {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    UniformLocalFourierLayers.matrix (fourierSchedule b rr roots unit hr hn hroot tab hi)=RadixTwo.dft N omega := by
  rw [fourierSchedule_eq b rr roots unit hr hn hroot tab hi hc ha,UniformLocalFourierLayers.schedule_matrix]

theorem fourierSchedule_calls {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    UniformLocalFourierLayers.calls (fourierSchedule b rr roots unit hr hn hroot tab hi)=
      wordCalls (UniformLocalFourierWord.word hn hroot) := by
  rw [fourierSchedule_eq b rr roots unit hr hn hroot tab hi hc ha,UniformLocalFourierLayers.schedule_calls]

theorem fourierSchedule_length {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    (fourierSchedule b rr roots unit hr hn hroot tab hi).length≤UniformLocalFourierWord.sufficientSlots N := by
  rw [fourierSchedule_eq b rr roots unit hr hn hroot tab hi hc ha]
  exact UniformLocalFourierLayers.schedule_length hn hroot


/-- The literal finite scale addresses for an occurrence, including zero μ. -/
def scaleReferences {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (t : Atom b.length) (ht : t.literals=[]) : Fin 6 → Fin (finish b rr).env.length :=
  (finish b rr).rows (finishIndex b (scalarIndex t ht).1 (scalarIndex t ht).2)

theorem scaleReferences_value {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1) (hr : ∀ j,b.program.eval roots (rr j)=roots j)
    (t : Atom b.length) (ht : t.literals=[]) (q : Fin 6) :
    (finish b rr).env.program.eval roots (scaleReferences b rr t ht q)=
      rowExpected (t.value (b.program.eval roots)) q := by
  rw [scaleReferences,finish_scales _ _ _ unit hr,scalarIndex_value]

theorem scaleReferences_nonzero {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1) (hr : ∀ j,b.program.eval roots (rr j)=roots j)
    (t : Atom b.length) (ht : t.literals=[]) (q : Fin 6) :
    (finish b rr).env.program.eval roots (scaleReferences b rr t ht q)≠0 :=
  finish_scales_ne_zero b rr roots unit hr _ _ q

theorem canonicalRoot {N : ℕ} (hn : 0<N) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)

/-- Canonical positive Fourier action; root extraction remains an explicit
seed adapter, as it is in the supplied shared preparation module. -/
theorem canonical_fourier_action {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) (tab : NewtonReferences b roots (zeta N))
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH (zeta N)))
      (PowerSeries.coeff · (NewtonFourier.invH (zeta N))⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH (zeta N)))
      (PowerSeries.coeff · (NewtonFourier.invH (zeta N))⁻¹)) (ha : b.program.Admissible roots)
    (x : Fin N → ℂ) :
    (UniformLocalFourierLayers.matrix (fourierSchedule b rr roots unit hr hn
      (canonicalRoot hn) tab hi)).mulVec x=(fourierMatrix N).mulVec x := by
  rw [fourierSchedule_matrix b rr roots unit hr hn (canonicalRoot hn) tab hi hc ha]
  rfl

theorem fourierSchedule_call_bound {r N o : ℕ} (b : State r N o) (rr : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j,‖roots j‖=1)
    (hr : ∀ j,b.program.eval roots (b.original (rr j))=roots j)
    (hn : 0<N) {omega : ℂ} (hroot : IsPrimitiveRoot omega N)
    (tab : NewtonReferences b roots omega)
    (hi : b.Inputs roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹))
    (hc : b.CachesGood roots (PowerSeries.coeff · (NewtonFourier.invH omega))
      (PowerSeries.coeff · (NewtonFourier.invH omega)⁻¹)) (ha : b.program.Admissible roots) :
    UniformLocalFourierLayers.calls (fourierSchedule b rr roots unit hr hn hroot tab hi)≤32*N^3 := by
  rw [fourierSchedule_calls b rr roots unit hr hn hroot tab hi hc ha]
  exact UniformLocalFourierWord.word_call_bound hn hroot

/-! Remaining boundary: the supplied seed must provide canonical FFT roots,
Newton H/scale/inverse-diagonal refs, and the fixed C-constant prepared bank.
This file proves occurrence substitution and literal program admissibility;
it does not claim fixed-RAM printing of the program or of layer metadata. -/
end ExactFourierCircuits.UniformLocalPreparationReferences
