import UniformCRTTraversalMachine

/-!
Paper: An explicit power saving for the exact discrete Fourier transform, OpenAI math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. §5.2, CRT tables and linear index traversal surrounding (5.5),
PDF p.22 (`eq:crt-fourier`), using the prefix bound (4.1), PDF p.18.

Literal integer/table/traversal bookkeeping refines that argument. The paper
does not specify this register layout or these frames; semantic and charged
execution obligations are separate declarations below.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCRTTraversalCycle
open UniformMachine UniformAssembly UniformCRTTraversalMachine
open scoped BigOperators

/-- The least significant axis is zero; this is the actual integer radix place. -/
def place {a : ℕ} (r : Fin a→ℕ) (i : ℕ) : ℕ := ((List.ofFn r).take i).prod

def decoded {a : ℕ} (r : Fin a→ℕ) (k : ℕ) (i : Fin a) : ℕ := (k/place r i.val)%r i

theorem place_zero {a : ℕ} (r : Fin a→ℕ) : place r 0=1 := rfl

theorem place_succ {a : ℕ} (r : Fin a→ℕ) (i : Fin a) :
    place r (i.val+1)=place r i.val*r i := by
  unfold place
  rw [List.take_succ_eq_append_getElem (by simp),List.prod_append]
  simp

theorem place_all {a : ℕ} (r : Fin a→ℕ) : place r a=∏i,r i := by
  simp [place,List.take_of_length_le, List.prod_ofFn]

theorem place_pos {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (j : ℕ) :
    0<place r j := by
  apply List.prod_pos
  intro v hv
  have hm:=List.mem_of_mem_take hv
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hm
  exact hr i

theorem place_dvd_all {a : ℕ} (r : Fin a→ℕ) (i : ℕ) :
    place r i∣∏j,r j := by
  refine ⟨((List.ofFn r).drop i).prod,?_⟩
  simp [place,List.prod_ofFn,List.prod_take_mul_prod_drop]

theorem place_dvd {a : ℕ} (r : Fin a→ℕ) {i j : ℕ} (hij:i≤j) :
    place r i∣place r j := by
  have ht:((List.ofFn r).take j).take i=(List.ofFn r).take i:=by
    rw [List.take_take,Nat.min_eq_left hij]
  refine ⟨(((List.ofFn r).take j).drop i).prod,?_⟩
  simpa only [←ht,place] using (List.prod_take_mul_prod_drop ((List.ofFn r).take j) i).symm

theorem div_pred_of_dvd (P t : ℕ) (hP:0<P) (ht:0<t) (hd:P∣t) :
    (t-1)/P=t/P-1 := by
  have ht1:=Nat.sub_add_cancel (show 1≤t by omega)
  have he:=Nat.div_mul_cancel hd
  have hv:0<t/P:=by nlinarith
  apply Nat.div_eq_of_lt_le
  · have hsub:=Nat.sub_add_cancel (show 1≤t/P by omega)
    nlinarith
  · have hsub:=Nat.sub_add_cancel (show 1≤t/P by omega)
    nlinarith

theorem div_pred_of_not_dvd (P t : ℕ) (hP:0<P) (ht:0<t) (hd:¬P∣t) :
    (t-1)/P=t/P := by
  have ht1:=Nat.sub_add_cancel (show 1≤t by omega)
  have he:=Nat.mod_add_div t P
  have hm:=Nat.mod_lt t hP
  have hz:0<t%P:=by
    by_contra hh
    exact hd (Nat.dvd_of_mod_eq_zero (by omega))
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem mod_pred_step (q v : ℕ) (_hq:0<q) (hv:0<v) :
    ((v-1)%q+1)%q=v%q := by
  have he:=Nat.sub_add_cancel (show 1≤v by omega)
  simpa only [Nat.add_mod,Nat.mod_mod] using congrArg (fun x:ℕ=>x%q) he

theorem decoded_step {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (t : ℕ)
    (ht:0<t) (i : Fin a) (hd:place r i.val∣t) :
    (decoded r (t-1) i+1)%r i=decoded r t i := by
  have hP:=place_pos r hr i.val
  have he:=Nat.div_mul_cancel hd
  have hv:0<t/place r i.val:=by nlinarith
  unfold decoded
  rw [div_pred_of_dvd _ _ hP ht hd]
  exact mod_pred_step _ _ (hr i) hv

theorem decoded_unchanged {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (t : ℕ) (ht:0<t) (i : Fin a) (hd:¬place r i.val∣t) :
    decoded r (t-1) i=decoded r t i := by
  unfold decoded
  rw [div_pred_of_not_dvd _ _ (place_pos r hr _) ht hd]

theorem decoded_bound {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (k : ℕ) (i : Fin a) :
    decoded r k i<r i := Nat.mod_lt _ (hr i)

theorem decoded_zero {a : ℕ} (r : Fin a→ℕ) (i : Fin a) : decoded r 0 i=0 := by
  simp [decoded]


theorem next_place_dvd_iff {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (t : ℕ) (i : Fin a) (hd:place r i.val∣t) :
    place r (i.val+1)∣t ↔ decoded r t i=0 := by
  rw [place_succ]
  have he:=Nat.div_mul_cancel hd
  change place r i.val*r i∣t ↔ (t/place r i.val)%r i=0
  nth_rw 1 [←he]
  rw [Nat.mul_comm (t/place r i.val),Nat.mul_dvd_mul_iff_left (place_pos r hr _)]
  exact Nat.dvd_iff_mod_eq_zero

theorem success_iff {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (t : ℕ) (ht:0<t) (i : Fin a) (hd:place r i.val∣t) :
    decoded r (t-1) i+1<r i ↔ ¬place r (i.val+1)∣t := by
  have hb:=decoded_bound r hr (t-1) i
  have he:=decoded_step r hr t ht i hd
  rw [next_place_dvd_iff r hr t i hd]
  by_cases hs:decoded r (t-1) i+1<r i
  · rw [Nat.mod_eq_of_lt hs] at he
    omega
  · have hh:decoded r (t-1) i+1=r i:=by omega
    rw [hh,Nat.mod_self] at he
    omega

def frontDigits {a : ℕ} (r : Fin a→ℕ) (t i : ℕ) (j : Fin a) : ℕ :=
  if j.val < i then decoded r t j else decoded r (t-1) j

theorem front_initial {a : ℕ} (r : Fin a→ℕ) (t : ℕ) :
    frontDigits r t 0=decoded r (t-1) := by funext j;simp [frontDigits]

theorem front_final {a : ℕ} (r : Fin a→ℕ) (t : ℕ) :
    frontDigits r t a=decoded r t := by funext j;simp [frontDigits,j.isLt]

theorem front_update {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (t : ℕ) (ht:0<t) (i : Fin a) (hd:place r i.val∣t) :
    Function.update (frontDigits r t i.val) i
      (if decoded r (t-1) i+1<r i then decoded r (t-1) i+1 else 0)=
        frontDigits r t (i.val+1) := by
  funext j
  by_cases hj:j=i
  · subst j
    rw [Function.update_self]
    simp only [frontDigits,Nat.lt_succ_self,ite_true]
    have he:=decoded_step r hr t ht i hd
    by_cases hs:decoded r (t-1) i+1<r i
    · simpa only [hs,ite_true,Nat.mod_eq_of_lt hs] using he
    · have hh:decoded r (t-1) i+1=r i:=by have hb:=decoded_bound r hr (t-1) i;omega
      simpa only [hh,Nat.lt_irrefl,ite_false,Nat.mod_self] using he
  · rw [Function.update_of_ne hj]
    have hjv:j.val≠i.val:=by intro he;exact hj (Fin.ext he)
    unfold frontDigits
    split_ifs <;> omega

theorem front_success {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (t : ℕ) (ht:0<t) (i : Fin a) (hd:¬place r (i.val+1)∣t) :
    frontDigits r t (i.val+1)=decoded r t := by
  funext j
  unfold frontDigits
  split_ifs with hj
  · rfl
  · apply decoded_unchanged r hr t ht j
    intro hh
    exact hd ((place_dvd r (by omega)).trans hh)

/-- Integer weighted address of a digit vector. -/
def weightedAddress {a : ℕ} (L : ℕ) (w ds : Fin a→ℕ) : ℕ := (∑j,w j*ds j)%L

theorem weightedAddress_bound {a : ℕ} (L : ℕ) (hL:0<L) (w ds : Fin a→ℕ) :
    weightedAddress L w ds<L := Nat.mod_lt _ hL

theorem weightedAddress_update {a : ℕ} (L : ℕ) (w ds : Fin a→ℕ) (i : Fin a)
    (q : ℕ) (_hq:0<q) (hd:ds i<q) (hw:L∣q*w i) :
    weightedAddress L w (Function.update ds i (if ds i+1<q then ds i+1 else 0))=
      (weightedAddress L w ds+w i)%L := by
  have hs:∑j,w j*Function.update ds i (if ds i+1<q then ds i+1 else 0) j=
      w i*(if ds i+1<q then ds i+1 else 0)+∑j∈Finset.univ.erase i,w j*ds j:=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    have hh:∑j∈Finset.univ.erase i,w j*Function.update ds i
        (if ds i+1<q then ds i+1 else 0) j=∑j∈Finset.univ.erase i,w j*ds j:=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hh,Nat.add_comm]
  have ho:=Finset.sum_erase_add Finset.univ (fun j=>w j*ds j) (Finset.mem_univ i)
  unfold weightedAddress
  rw [hs,←ho,Nat.mod_add_mod]
  by_cases hh:ds i+1<q
  · simp only [hh,ite_true]
    congr 1
    ring
  · have he:ds i+1=q:=by omega
    rw [ite_eq_right hh,Nat.mul_zero,Nat.zero_add]
    have hz:(w i*ds i+w i)%L=0:=by
      have he':w i*ds i+w i=q*w i:=by nlinarith
      rw [he'];exact Nat.mod_eq_zero_of_dvd hw
    rw [Nat.add_assoc,Nat.add_mod,hz,Nat.add_zero,Nat.mod_mod]


/-- The actual axes visited when advancing ordinal t-1 to t. -/
def visitsFrom {a : ℕ} (r : Fin a→ℕ) (t i : ℕ) : ℕ :=
  ∑j:Fin a,if i≤j.val ∧ place r j.val∣t then 1 else 0

theorem visits_end {a : ℕ} (r : Fin a→ℕ) (t : ℕ) : visitsFrom r t a=0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [show ¬a≤j.val by omega]

theorem visits_step {a : ℕ} (r : Fin a→ℕ) (t : ℕ) (i : Fin a)
    (hd:place r i.val∣t) : visitsFrom r t i.val=1+visitsFrom r t (i.val+1) := by
  have hpoint (j:Fin a):
      (if i.val≤j.val ∧ place r j.val∣t then 1 else 0)=
        (if j=i then 1 else 0)+(if i.val+1≤j.val ∧ place r j.val∣t then 1 else 0):=by
    by_cases hj:j=i
    · subst j;simp [hd]
    · have hjv:j.val≠i.val:=by intro hh;exact hj (Fin.ext hh)
      split_ifs <;> omega
  unfold visitsFrom
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem visits_stop {a : ℕ} (r : Fin a→ℕ) (t : ℕ) (i : ℕ)
    (hd:¬place r i∣t) : visitsFrom r t i=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hh:¬(i≤j.val ∧ place r j.val∣t):=by
    intro h
    exact hd ((place_dvd r h.1).trans h.2)
  simp [hh]

/-- Count multiples with charged integer recurrence, rather than an asymptotic model. -/
def multiples (P : ℕ) : ℕ→ℕ
  | 0 => 0
  | k+1 => multiples P k+if P∣k+1 then 1 else 0

theorem multiples_eq (P : ℕ) (hP:0<P) (k : ℕ) : multiples P k=k/P := by
  induction k with
  | zero => simp [multiples]
  | succ k ih =>
      rw [multiples,ih]
      by_cases hd:P∣k+1
      · have he:=div_pred_of_dvd P (k+1) hP (by omega) hd
        have hp:0<(k+1)/P:=by
          have hh:=Nat.div_mul_cancel hd
          nlinarith
        simp only [Nat.add_sub_cancel] at he
        simp only [hd,ite_true]
        omega
      · have he:=div_pred_of_not_dvd P (k+1) hP (by omega) hd
        simpa only [hd,ite_false,Nat.add_zero,Nat.add_sub_cancel] using he

def totalVisits {a : ℕ} (r : Fin a→ℕ) (k : ℕ) : ℕ := ∑i:Fin a,multiples (place r i.val) k

theorem totalVisits_zero {a : ℕ} (r : Fin a→ℕ) : totalVisits r 0=0 := by
  simp [totalVisits,multiples]

theorem totalVisits_succ {a : ℕ} (r : Fin a→ℕ) (k : ℕ) :
    totalVisits r (k+1)=totalVisits r k+visitsFrom r (k+1) 0 := by
  simp [totalVisits,multiples,visitsFrom,Finset.sum_add_distrib]


abbrev ell (n : ℕ) := UniformWorkingLength.axisCount n
abbrev len (n : ℕ) := UniformWorkingLength.workingLength n
abbrev radices (n : ℕ) := UniformSelectedCRT.radices n
abbrev alphaWeights (n : ℕ) := UniformCRT.idempotent (radices n)
abbrev betaWeights (n : ℕ) := UniformCRT.cofactor (radices n)

/-- A carry modifies only its digit and private registers. -/
theorem carry_frame (ell L i q wa wb d : ℕ) (s : State) :
    Frame ell s (carry ell L i q wa wb d s) := by
  obtain ⟨hS,hH,hO,hR⟩:=carry_scalar_frame ell L i q wa wb d s
  exact ⟨hS,hH,hO,hR,fun r hr=>carry_static ell L i q wa wb d s r (by omega),
    fun addr ha=>carry_preserves_low_heap ell L i q wa wb d s addr ha⟩

theorem carry_preserves_tables (ell L i q wa wb d : ℕ) (s : State)
    (hi:i<ell+1) (addr : ℕ) (ha:alphaBase ell≤addr) :
    (carry ell L i q wa wb d s).natHeap addr=s.natHeap addr := by
  rw [carry_heap,Function.update_of_ne (by unfold alphaBase at ha;omega)]

theorem emit_frame (ell L : ℕ) (s : State) (hg:Geometry ell L s) : Frame ell s (emit s) := by
  obtain ⟨hS,hH,hO,hR⟩:=emit_scalar_frame s
  exact ⟨hS,hH,hO,hR,fun r hr=>emit_static s r (by omega) (by omega) (by omega),
    fun addr ha=>emit_preserves_low_heap ell L s hg addr (by unfold alphaBase;omega)⟩

def Digits (n : ℕ) (ds : Fin (ell n+1)→ℕ) (s : State) : Prop :=
  ∀i,s.natHeap (digitBase (ell n)+i.val)=some (ds i)

def Addresses (n : ℕ) (ds : Fin (ell n+1)→ℕ) (s : State) : Prop :=
  s.natReg 55=weightedAddress (len n) (alphaWeights n) ds ∧
  s.natReg 56=weightedAddress (len n) (betaWeights n) ds

structure Sweep (n t i : ℕ) (s : State) : Prop where
  geometry : Geometry (ell n) (len n) s
  crt : UniformCRTHeaderMachine.CRTTable n s
  pc : s.pc=25
  index : s.natReg 57=i
  ordinal : s.natReg 54=t
  digits : Digits n (frontDigits (radices n) t i) s
  addresses : Addresses n (frontDigits (radices n) t i) s

structure Done (n t : ℕ) (s : State) : Prop where
  geometry : Geometry (ell n) (len n) s
  crt : UniformCRTHeaderMachine.CRTTable n s
  pc : s.pc=(if t=len n then 25 else 19)
  index : t=len n → s.natReg 57=ell n+1
  ordinal : s.natReg 54=t
  digits : Digits n (decoded (radices n) t) s
  addresses : Addresses n (decoded (radices n) t) s

def carryNext (n t : ℕ) (i : Fin (ell n+1)) (s : State) : State :=
  carry (ell n) (len n) i.val (radices n i) (alphaWeights n i) (betaWeights n i)
    (decoded (radices n) (t-1) i) s

theorem carryNext_digits (n t : ℕ) (ht:0<t) (i : Fin (ell n+1)) (s : State)
    (hs:Digits n (frontDigits (radices n) t i.val) s)
    (hd:place (radices n) i.val∣t) :
    Digits n (frontDigits (radices n) t (i.val+1)) (carryNext n t i s) := by
  rw [←front_update (radices n) (UniformSelectedCRT.radix_pos n) t ht i hd]
  intro j
  unfold carryNext
  rw [carry_heap]
  by_cases hj:j=i
  · subst j
    simp [Function.update_self]
  · rw [Function.update_of_ne (by intro hh;exact hj (Fin.ext (by omega))),
      Function.update_of_ne hj]
    exact hs j

theorem carryNext_addresses (n t : ℕ) (ht:0<t) (i : Fin (ell n+1)) (s : State)
    (hs:Addresses n (frontDigits (radices n) t i.val) s)
    (hd:place (radices n) i.val∣t) :
    Addresses n (frontDigits (radices n) t (i.val+1)) (carryNext n t i s) := by
  have hf:frontDigits (radices n) t i.val i=decoded (radices n) (t-1) i:=by
    simp [frontDigits]
  have hbound:=decoded_bound (radices n) (UniformSelectedCRT.radix_pos n) (t-1) i
  have hA:=weightedAddress_update (len n) (alphaWeights n) (frontDigits (radices n) t i.val)
    i (radices n i) (UniformSelectedCRT.radix_pos n i) (by rw [hf];exact hbound)
    (by simpa only [UniformSelectedCRT.radices_product] using idempotent_weight_divides (radices n) i)
  have hD:=weightedAddress_update (len n) (betaWeights n) (frontDigits (radices n) t i.val)
    i (radices n i) (UniformSelectedCRT.radix_pos n i) (by rw [hf];exact hbound)
    (by simpa only [UniformSelectedCRT.radices_product] using cofactor_weight_divides (radices n) i)
  rw [hf,front_update (radices n) (UniformSelectedCRT.radix_pos n) t ht i hd] at hA hD
  constructor
  · exact (carry_alpha _ _ _ _ _ _ _ s).trans ((congrArg (fun v=> (v+alphaWeights n i)%len n) hs.1).trans hA.symm)
  · exact (carry_beta _ _ _ _ _ _ _ s).trans ((congrArg (fun v=> (v+betaWeights n i)%len n) hs.2).trans hD.symm)


theorem carryNext_bounded {n : ℕ} (hn:0<n) (B t : ℕ) (x : Fin n→ℂ)
    (i : Fin (ell n+1)) (s : State) (hi:Sweep n t i.val s) (hs:WordBound B s)
    (hB:128+10*ell n+4*len n≤B) :
    BoundedRuns program n x B s
      (if decoded (radices n) (t-1) i+1<radices n i then 19 else 20) (carryNext n t i s) := by
  have hd:s.natHeap (digitBase (ell n)+i.val)=some (decoded (radices n) (t-1) i):=by
    simpa only [frontDigits,Nat.lt_irrefl,ite_false] using hi.digits i
  have hready:=actual_carry_ready n i.val (decoded (radices n) (t-1) i) s hi.geometry hi.crt
    i.isLt hi.pc hi.index hd
  have hL:=UniformWorkingLength.workingLength_pos hn
  have hbound:=actual_carry_bounds hn B i.val (decoded (radices n) (t-1) i) s i.isLt
    (by rw [hi.addresses.1];exact weightedAddress_bound _ hL _ _)
    (by rw [hi.addresses.2];exact weightedAddress_bound _ hL _ _)
    (decoded_bound (radices n) (UniformSelectedCRT.radix_pos n) (t-1) i) hB
  exact carry_bounded n B x _ _ _ _ _ _ _ s hready hL (by omega) hs hbound

theorem sweep_bounded {n : ℕ} (hn:0<n) (B t fuel i : ℕ) (x : Fin n→ℂ)
    (s : State) (ht:0<t) (htL:t≤len n) (hf:i+fuel=ell n+1)
    (hd:place (radices n) i∣t) (hi:Sweep n t i s) (hs:WordBound B s)
    (hB:128+10*ell n+4*len n≤B) : ∃c u,
    BoundedRuns program n x B s c u ∧ c≤20*visitsFrom (radices n) t i ∧ Done n t u ∧
    Frame (ell n) s u ∧ ∀addr,alphaBase (ell n)≤addr → u.natHeap addr=s.natHeap addr := by
  induction fuel generalizing i s with
  | zero =>
      have hie:i=ell n+1:=by omega
      have hLt:len n∣t:=by simpa only [hie,place_all,UniformSelectedCRT.radices_product] using hd
      have hte:t=len n:=by have hh:=Nat.le_of_dvd ht hLt;omega
      refine ⟨0,s,.refl hs,by omega,?_,frame_refl _ _,fun _ _=>rfl⟩
      constructor
      · exact hi.geometry
      · exact hi.crt
      · simpa only [hte,ite_true] using hi.pc
      · intro _;simpa only [hie] using hi.index
      · exact hi.ordinal
      · simpa only [hie,front_final] using hi.digits
      · simpa only [hie,front_final] using hi.addresses
  | succ fuel ih =>
      have hil:i<ell n+1:=by omega
      let ip:Fin (ell n+1):=⟨i,hil⟩
      let u:=carryNext n t ip s
      have hr:=carryNext_bounded hn B t x ip s hi hs hB
      have hfr:Frame (ell n) s u:=carry_frame _ _ _ _ _ _ _ s
      have hg:Geometry (ell n) (len n) u:=carry_geometry _ _ _ _ _ _ _ s hi.geometry
      have hc:UniformCRTHeaderMachine.CRTTable n u:=hfr.crt hi.crt
      have hds:=carryNext_digits n t ht ip s hi.digits hd
      have has:=carryNext_addresses n t ht ip s hi.addresses hd
      have hctrl:=carry_control (ell n) (len n) i (radices n ip) (alphaWeights n ip)
        (betaWeights n ip) (decoded (radices n) (t-1) ip) s hi.index
      have hheap:∀addr,alphaBase (ell n)≤addr → u.natHeap addr=s.natHeap addr:=
        fun addr ha=>carry_preserves_tables _ _ _ _ _ _ _ s hil addr ha
      have hvs:=visits_step (radices n) t ip hd
      by_cases hsuccess:decoded (radices n) (t-1) ip+1<radices n ip
      · have hnd:=((success_iff (radices n) (UniformSelectedCRT.radix_pos n) t ht ip hd).1 hsuccess)
        have hne:t≠len n:=by
          intro he;exact hnd (he ▸ (by simpa only [UniformSelectedCRT.radices_product] using place_dvd_all (radices n) (i+1)))
        have hdigit:frontDigits (radices n) t (i+1)=decoded (radices n) t:=
          front_success (radices n) (UniformSelectedCRT.radix_pos n) t ht ip hnd
        refine ⟨19,u,?_,?_,?_,hfr,hheap⟩
        · simpa only [hsuccess,ite_true] using hr
        · dsimp only [ip] at hvs;omega
        · constructor
          · exact hg
          · exact hc
          · simpa only [u,carryNext,ip,hsuccess,ite_true,hne,ite_false] using hctrl.1
          · intro he;exact (hne he).elim
          · exact hctrl.2.2.trans hi.ordinal
          · simpa only [u,ip,hdigit] using hds
          · simpa only [u,ip,hdigit] using has
      · have hnd:place (radices n) (i+1)∣t:=by
          by_contra hh
          exact hsuccess ((success_iff (radices n) (UniformSelectedCRT.radix_pos n) t ht ip hd).2 hh)
        have hnext:Sweep n t (i+1) u:=⟨hg,hc,by simpa only [u,carryNext,ip,hsuccess,ite_false] using hctrl.1,
          by simpa only [u,carryNext,ip,hsuccess,ite_false] using hctrl.2.1,hctrl.2.2.trans hi.ordinal,hds,has⟩
        obtain ⟨c,v,hv,hcv,hdone,hframe,htables⟩:=ih (i+1) u (by omega) hnd hnext hr.final_bound
        refine ⟨20+c,v,?_,?_,hdone,hfr.trans hframe,?_⟩
        · have hfirst:BoundedRuns program n x B s 20 u:=by simpa only [hsuccess,ite_false] using hr
          exact hfirst.trans hv
        · dsimp only [ip] at hvs;omega
        · intro addr ha;exact (htables addr ha).trans (hheap addr ha)


theorem carryVisits_sum (rs : List ℕ) :
    carryVisits rs=∑i∈Finset.range rs.length,(rs.drop i).prod := by
  induction rs with
  | nil => simp [carryVisits]
  | cons q qs ih =>
      simp only [carryVisits,List.length_cons,Finset.sum_range_succ',List.drop_succ_cons,List.drop_zero,List.prod_cons]
      rw [←ih,Nat.add_comm]

theorem totalVisits_cycle {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) :
    totalVisits r (∏i,r i)=carryVisits (List.ofFn r) := by
  unfold totalVisits
  have hterm (i:Fin a):multiples (place r i.val) (∏j,r j)=((List.ofFn r).drop i.val).prod:=by
    rw [multiples_eq _ (place_pos r hr _)]
    have he:=List.prod_take_mul_prod_drop (List.ofFn r) i.val
    have hp:(List.ofFn r).prod=∏j,r j:=List.prod_ofFn
    rw [←hp,←he]
    exact Nat.mul_div_cancel_left _ (place_pos r hr _)
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i=>((List.ofFn r).drop i).prod) a]
  simpa only [List.length_ofFn] using (carryVisits_sum (List.ofFn r)).symm

theorem selected_list (n : ℕ) : List.ofFn (radices n)=selectedRadices n := by
  unfold radices UniformSelectedCRT.radices selectedRadices
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem selected_totalVisits (n : ℕ) : totalVisits (radices n) (len n)=carryVisits (selectedRadices n) := by
  change totalVisits (UniformSelectedCRT.radices n) (UniformWorkingLength.workingLength n)=_
  rw [←UniformSelectedCRT.radices_product,totalVisits_cycle _ (UniformSelectedCRT.radix_pos n),selected_list]

/-- Both arrays store every emitted ordinal, not merely a final sampled value. -/
def Tables (n k : ℕ) (s : State) : Prop := ∀j,j<k →
  s.natHeap (alphaBase (ell n)+j)=some (weightedAddress (len n) (alphaWeights n) (decoded (radices n) j)) ∧
  s.natHeap (betaBase (ell n) (len n)+j)=some (weightedAddress (len n) (betaWeights n) (decoded (radices n) j))

theorem emit_tables (n k : ℕ) (s : State) (hk:k<len n)
    (hg:Geometry (ell n) (len n) s) (hp:s.pc=19) (ho:s.natReg 54=k)
    (haddr:Addresses n (decoded (radices n) k) s) (ht:Tables n k s) : Tables n (k+1) (emit s) := by
  intro j hj
  rw [(emit_values s hp).2.2.2.2.2,hg.alpha,hg.beta,ho]
  by_cases he:j=k
  · subst j
    rw [Function.update_of_ne (by unfold betaBase;omega),Function.update_self,Function.update_self]
    exact ⟨congrArg some haddr.1,congrArg some haddr.2⟩
  · have hjk:j<k:=by omega
    obtain ⟨hA,hD⟩:=ht j hjk
    constructor
    · rw [Function.update_of_ne (by unfold betaBase;omega),Function.update_of_ne (by omega)]
      exact hA
    · rw [Function.update_of_ne (by omega),Function.update_of_ne (by unfold betaBase;omega)]
      exact hD

theorem tables_preserved (n k : ℕ) (s u : State)
    (hh:∀addr,alphaBase (ell n)≤addr → u.natHeap addr=s.natHeap addr) (ht:Tables n k s) :
    Tables n k u := by
  intro j hj
  rw [hh _ (by omega),hh _ (by unfold betaBase;omega)]
  exact ht j hj

theorem emit_sweep (n k : ℕ) (s : State) (hp:s.pc=19)
    (hg:Geometry (ell n) (len n) s) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (ho:s.natReg 54=k) (hd:Digits n (decoded (radices n) k) s)
    (ha:Addresses n (decoded (radices n) k) s) : Sweep n (k+1) 0 (emit s) := by
  obtain ⟨hpc,hindex,hord,hA,hD,_⟩:=emit_values s hp
  constructor
  · exact emit_geometry _ _ s hg
  · exact (emit_frame _ _ s hg).crt hc
  · exact hpc
  · exact hindex
  · exact hord.trans (congrArg (·+1) ho)
  · intro j
    rw [emit_preserves_low_heap _ _ s hg _ (by unfold alphaBase;omega)]
    simpa only [front_initial,Nat.add_sub_cancel] using hd j
  · simpa only [front_initial,Nat.add_sub_cancel] using ⟨hA.trans ha.1,hD.trans ha.2⟩

theorem ordinal_bounded {n : ℕ} (hn:0<n) (B k : ℕ) (x : Fin n→ℂ) (s : State)
    (hk:k<len n) (hloop:Done n k s) (htables:Tables n k s) (hs:WordBound B s)
    (hB:128+10*ell n+4*len n≤B) : ∃c u,
    BoundedRuns program n x B s c u ∧ c≤6+20*visitsFrom (radices n) (k+1) 0 ∧
    Done n (k+1) u ∧ Tables n (k+1) u ∧ Frame (ell n) s u := by
  have hpc:s.pc=19:=by simpa only [show k≠len n by omega,ite_false] using hloop.pc
  have he:=emit_bounded n B x s hpc hloop.geometry.one (by omega) hs
    (by rw [hloop.geometry.alpha,hloop.ordinal];unfold alphaBase digitBase;omega)
    (by rw [hloop.geometry.beta,hloop.ordinal];unfold betaBase alphaBase digitBase;omega)
    (by rw [hloop.ordinal];omega)
  have hi:=emit_sweep n k s hpc hloop.geometry hloop.crt hloop.ordinal hloop.digits hloop.addresses
  have ht:=emit_tables n k s hk hloop.geometry hpc hloop.ordinal hloop.addresses htables
  obtain ⟨c,u,hu,hc,hDone,hframe,htab⟩:=sweep_bounded hn B (k+1) (ell n+1) 0 x
    (emit s) (by omega) (by omega) (by omega) (by simp [place_zero]) hi he.final_bound hB
  exact ⟨6+c,u,he.trans hu,by omega,hDone,tables_preserved n (k+1) (emit s) u htab ht,
    (emit_frame _ _ s hloop.geometry).trans hframe⟩


/-- Iterate the literal emit/carry blocks, charging every visited axis. -/
theorem complete_bounded {n : ℕ} (hn:0<n) (B k fuel : ℕ) (x : Fin n→ℂ) (s : State)
    (hf:k+fuel=len n) (hloop:Done n k s) (htables:Tables n k s) (hs:WordBound B s)
    (hB:128+10*ell n+4*len n≤B) : ∃c u,
    BoundedRuns program n x B s c u ∧
    c+6*k+20*totalVisits (radices n) k≤6*len n+20*totalVisits (radices n) (len n) ∧
    Done n (len n) u ∧ Tables n (len n) u ∧ Frame (ell n) s u := by
  induction fuel generalizing k s with
  | zero =>
      have hk:k=len n:=by omega
      subst k
      exact ⟨0,s,.refl hs,by omega,hloop,htables,frame_refl _ _⟩
  | succ fuel ih =>
      have hk:k<len n:=by omega
      obtain ⟨c,u,hu,hcu,hDone,hTables,hframe⟩:=ordinal_bounded hn B k x s hk hloop htables hs hB
      obtain ⟨d,v,hv,hdv,hfinal,hall,hfr⟩:=ih (k+1) u (by omega) hDone hTables hu.final_bound
      refine ⟨c+d,v,hu.trans hv,?_,hfinal,hall,hframe.trans hfr⟩
      rw [totalVisits_succ] at hdv
      omega

/-- Universal initialized execution of the actual fixed program. The complete
arrays and its amortized linear instruction bound are both conclusions. -/
theorem initialized_execution {n : ℕ} (hn:0<n) (B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hh:UniformCRTHeaderMachine.Header n s) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (hs:WordBound B s) (hB:128+10*ell n+4*len n≤B) : ∃t u,
    BoundedExecution program n x B s t u ∧
    t≤cycleBudget (ell n) (selectedRadices n) ∧
    Tables n (len n) u ∧ Frame (ell n) s u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    u.pc=47 ∧ u.natReg 54=len n ∧
    DigitsZero (ell n) (ell n+1) u ∧ u.natReg 55=0 ∧ u.natReg 56=0 := by
  have hL:0<len n:=UniformWorkingLength.workingLength_pos hn
  obtain ⟨v,hinit,hgeom,hpc,hzero,hheader,hcrt,hframe,hord,hA,hD⟩:=
    post_header_initialize n B x s hp hh hc hs hB
  have hstart:Done n 0 v:=by
    constructor
    · exact hgeom
    · exact hcrt
    · simpa only [show (0:ℕ)≠len n by omega,ite_false] using hpc
    · intro he;omega
    · exact hord
    · intro i;simpa only [decoded_zero] using hzero i.val i.isLt
    · simpa [Addresses,weightedAddress,decoded_zero] using ⟨hA,hD⟩
  obtain ⟨c,w,hrun,hcost,hDone,hTables,hfr⟩:=complete_bounded hn B 0 (len n) x v
    (by simp) hstart (by intro j hj;omega) hinit.final_bound hB
  have hhalt:=halt_bounded n B (ell n) (len n) x w (by simpa using hDone.pc)
    hDone.geometry (hDone.index rfl) (by omega) hrun.final_bound
  have hwhole:=hinit.trans hrun
  have hf:Frame (ell n) s (setPC w 47):=(hframe.trans hfr).trans (by
    exact ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩)
  have hdzero:∀i:Fin (ell n+1),decoded (radices n) (len n) i=0:=by
    intro i
    have hd:=place_dvd_all (radices n) (i.val+1)
    rw [UniformSelectedCRT.radices_product] at hd
    exact (next_place_dvd_iff (radices n) (UniformSelectedCRT.radix_pos n) (len n) i
      (by simpa only [UniformSelectedCRT.radices_product] using place_dvd_all (radices n) i.val)).1 hd
  refine ⟨14+5*(ell n+1)+c+2,setPC w 47,hwhole.executes hhalt,?_,hTables,hf,
    hf.header hh,hf.crt hc,rfl,hDone.ordinal,?_,?_,?_⟩
  · rw [totalVisits_zero] at hcost
    rw [selected_totalVisits] at hcost
    unfold cycleBudget
    rw [selected_radices_product]
    change 14+5*(ell n+1)+c+2≤14+5*(ell n+1)+6*len n+20*carryVisits (selectedRadices n)+2
    omega
  · intro i hi
    exact (hDone.digits ⟨i,hi⟩).trans (congrArg some (hdzero ⟨i,hi⟩))
  · simpa only [setPC,Addresses,weightedAddress,hdzero,Nat.mul_zero,Finset.sum_const_zero,Nat.zero_mod] using hDone.addresses.1
  · simpa only [setPC,Addresses,weightedAddress,hdzero,Nat.mul_zero,Finset.sum_const_zero,Nat.zero_mod] using hDone.addresses.2

theorem initialized_execution_linear {n : ℕ} (hn:0<n) (B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hh:UniformCRTHeaderMachine.Header n s) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (hs:WordBound B s) (hB:128+10*ell n+4*len n≤B) : ∃t u,
    BoundedExecution program n x B s t u ∧ t<46*len n+5*ell n+21 ∧
    Tables n (len n) u ∧ Frame (ell n) s u := by
  obtain ⟨t,u,hr,ht,hT,hF,_⟩:=initialized_execution hn B x s hp hh hc hs hB
  exact ⟨t,u,hr,ht.trans_lt (selected_cycleBudget_bound n),hT,hF⟩


/-- The concrete least-axis-first integer encoding, not a chosen permutation. -/
def encoded {a : ℕ} (r ds : Fin a→ℕ) : ℕ := ∑j,place r j.val*ds j

def prefixValue {a : ℕ} (r ds : Fin a→ℕ) (i : ℕ) : ℕ :=
  ∑j:Fin a,if j.val < i then place r j.val*ds j else 0

theorem prefix_zero {a : ℕ} (r ds : Fin a→ℕ) : prefixValue r ds 0=0 := by
  simp [prefixValue]

theorem prefix_all {a : ℕ} (r ds : Fin a→ℕ) : prefixValue r ds a=encoded r ds := by
  simp [prefixValue,encoded]

theorem prefix_succ {a : ℕ} (r ds : Fin a→ℕ) (i : Fin a) :
    prefixValue r ds (i.val+1)=prefixValue r ds i.val+place r i.val*ds i := by
  have hpoint (j:Fin a):
      (if j.val < i.val+1 then place r j.val*ds j else 0)=
        (if j.val < i.val then place r j.val*ds j else 0)+(if j=i then place r i.val*ds i else 0):=by
    by_cases hj:j=i
    · subst j;simp
    · have hjv:j.val≠i.val:=by intro he;exact hj (Fin.ext he)
      split_ifs <;> omega
  unfold prefixValue
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem prefix_decoded {a : ℕ} (r : Fin a→ℕ) (k i : ℕ) (hi:i≤a) :
    prefixValue r (decoded r k) i+place r i*(k/place r i)=k := by
  induction i with
  | zero => simp [prefix_zero,place_zero]
  | succ i ih =>
      have hia:i<a:=by omega
      let ip:Fin a:=⟨i,hia⟩
      have he:=ih (by omega)
      rw [prefix_succ r (decoded r k) ip,place_succ r ip]
      change prefixValue r (decoded r k) i+place r i*((k/place r i)%r ip)+
        (place r i*r ip)*(k/(place r i*r ip))=k
      rw [←Nat.div_div_eq_div_mul]
      calc
        _=prefixValue r (decoded r k) i+
            place r i*((k/place r i)%r ip+r ip*((k/place r i)/r ip)):=by ring
        _=prefixValue r (decoded r k) i+place r i*(k/place r i):=by rw [Nat.mod_add_div]
        _=k:=he

theorem encoded_decoded {a : ℕ} (r : Fin a→ℕ) (k : ℕ) (hk:k<∏i,r i) :
    encoded r (decoded r k)=k := by
  have he:=prefix_decoded r k a (by rfl)
  simpa only [prefix_all,place_all,Nat.div_eq_of_lt hk,Nat.mul_zero,Nat.add_zero] using he

theorem prefix_lt {a : ℕ} (r ds : Fin a→ℕ) (hr:∀i,0<r i) (hd:∀i,ds i<r i)
    (i : ℕ) (hi:i≤a) : prefixValue r ds i<place r i := by
  induction i with
  | zero => simp [prefix_zero,place_zero]
  | succ i ih =>
      have hia:i<a:=by omega
      let ip:Fin a:=⟨i,hia⟩
      have hprev:=ih (by omega)
      have hb:=hd ip
      have hp:=place_pos r hr i
      rw [prefix_succ r ds ip,place_succ r ip]
      dsimp only [ip] at *
      nlinarith

theorem encoded_lt {a : ℕ} (r ds : Fin a→ℕ) (hr:∀i,0<r i) (hd:∀i,ds i<r i) :
    encoded r ds<∏i,r i := by
  simpa only [prefix_all,place_all] using prefix_lt r ds hr hd a (by rfl)

/-- Decoding is a concrete bijection because its computed integer encoding is
its inverse and the two finite types have the same proved cardinality. -/
def decodeDigits {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (k : Fin (∏i,r i)) : ∀i,Fin (r i) :=
  fun i=>⟨decoded r k.val i,decoded_bound r hr k.val i⟩

theorem decodeDigits_injective {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) :
    Function.Injective (decodeDigits r hr) := by
  intro k l he
  apply Fin.ext
  have hv:(fun i=>(decodeDigits r hr k i).val)=(fun i=>(decodeDigits r hr l i).val):=by
    funext i;exact congrArg Fin.val (congrFun he i)
  have hh:=congrArg (encoded r) hv
  simpa only [decodeDigits,encoded_decoded r k.val k.isLt,encoded_decoded r l.val l.isLt] using hh

theorem decodeDigits_bijective {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) :
    Function.Bijective (decodeDigits r hr) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨decodeDigits_injective r hr,by simp [Fintype.card_pi]⟩


theorem decoded_encoded {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (ds : ∀i,Fin (r i)) :
    decoded r (encoded r (fun i=>(ds i).val))=(fun i=>(ds i).val) := by
  obtain ⟨k,hk⟩:=(decodeDigits_bijective r hr).2 ds
  have hv:(fun i=>(decodeDigits r hr k i).val)=(fun i=>(ds i).val):=by
    funext i;exact congrArg Fin.val (congrFun hk i)
  have he:=congrArg (encoded r) hv
  have henc:encoded r (fun i=>(ds i).val)=k.val:=by
    exact he.symm.trans (encoded_decoded r k.val k.isLt)
  rw [henc]
  exact hv

/-- Both directions are computed by the printed radix formulas. -/
def decodeEquiv {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) :
    Fin (∏i,r i) ≃ (∀i,Fin (r i)) where
  toFun := decodeDigits r hr
  invFun ds := ⟨encoded r (fun i=>(ds i).val),encoded_lt r _ hr (fun i=>(ds i).isLt)⟩
  left_inv k := Fin.ext (encoded_decoded r k.val k.isLt)
  right_inv ds := by
    funext i;apply Fin.ext
    exact congrFun (decoded_encoded r hr ds) i

def localInverse {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i) (ds : ∀i,Fin (r i)) : ∀i,Fin (r i) :=
  fun i=>⟨UniformCRT.localOutput r i (ds i).val,Nat.mod_lt _ (hr i)⟩

theorem localInverse_outputDigits {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (hc:Pairwise (fun i j=>Nat.Coprime (r i) (r j))) (ds : ∀i,Fin (r i)) :
    localInverse r hr (outputDigits r hr ds)=ds := by
  funext i;apply Fin.ext
  exact outputDigits_inverse_local r hr hc ds i

theorem outputDigits_bijective {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (hc:Pairwise (fun i j=>Nat.Coprime (r i) (r j))) : Function.Bijective (outputDigits r hr) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨fun x y h=>(localInverse_outputDigits r hr hc x).symm.trans
    ((congrArg (localInverse r hr) h).trans (localInverse_outputDigits r hr hc y)),rfl⟩

theorem outputDigits_localInverse {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (hc:Pairwise (fun i j=>Nat.Coprime (r i) (r j))) (ds : ∀i,Fin (r i)) :
    outputDigits r hr (localInverse r hr ds)=ds := by
  obtain ⟨x,rfl⟩:=(outputDigits_bijective r hr hc).2 ds
  rw [localInverse_outputDigits r hr hc x]

def outputEquiv {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (hc:Pairwise (fun i j=>Nat.Coprime (r i) (r j))) : (∀i,Fin (r i)) ≃ (∀i,Fin (r i)) where
  toFun := outputDigits r hr
  invFun := localInverse r hr
  left_inv := localInverse_outputDigits r hr hc
  right_inv := outputDigits_localInverse r hr hc

def ordinalEquiv (n : ℕ) : Fin (len n) ≃ (∀i,Fin (radices n i)) :=
  (finCongr (UniformSelectedCRT.radices_product n).symm).trans
    (decodeEquiv (radices n) (UniformSelectedCRT.radix_pos n))

def alphaPermutation (n : ℕ) : Fin (len n) ≃ Fin (len n) :=
  (ordinalEquiv n).trans (UniformSelectedCRT.permutation n)

def betaPermutation (n : ℕ) : Fin (len n) ≃ Fin (len n) :=
  ((ordinalEquiv n).trans (outputEquiv (radices n) (UniformSelectedCRT.radix_pos n)
    (UniformSelectedCRT.radices_pairwise n))).trans (UniformSelectedCRT.permutation n)

theorem alphaPermutation_value (n : ℕ) (k : Fin (len n)) :
    (alphaPermutation n k).val=weightedAddress (len n) (alphaWeights n) (decoded (radices n) k.val) := by
  change UniformCRT.address (radices n) (ordinalEquiv n k)=_
  unfold UniformCRT.address weightedAddress
  rw [UniformSelectedCRT.radices_product]
  rfl

theorem betaPermutation_value (n : ℕ) (k : Fin (len n)) :
    (betaPermutation n k).val=weightedAddress (len n) (betaWeights n) (decoded (radices n) k.val) := by
  change UniformCRT.address (radices n)
    (outputDigits (radices n) (UniformSelectedCRT.radix_pos n) (ordinalEquiv n k))=_
  rw [←betaAddress_crt (radices n) (UniformSelectedCRT.radix_pos n) (UniformSelectedCRT.radices_pairwise n)]
  unfold betaAddress weightedAddress
  rw [UniformSelectedCRT.radices_product]
  rfl

theorem tables_permutations (n : ℕ) (s : State) (ht:Tables n (len n) s) (k : Fin (len n)) :
    s.natHeap (alphaBase (ell n)+k.val)=some ((alphaPermutation n k).val) ∧
    s.natHeap (betaBase (ell n) (len n)+k.val)=some ((betaPermutation n k).val) := by
  simpa only [alphaPermutation_value,betaPermutation_value] using ht k.val k.isLt

/-- Actual execution produces two bijective address tables in the specified
integer digit order, while retaining arbitrary scalar/input banks. -/
theorem permutation_tables_execution {n : ℕ} (hn:0<n) (B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hh:UniformCRTHeaderMachine.Header n s) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (hs:WordBound B s) (hB:128+10*ell n+4*len n≤B) : ∃t u,
    BoundedExecution program n x B s t u ∧ t<46*len n+5*ell n+21 ∧
    (∀k:Fin (len n),u.natHeap (alphaBase (ell n)+k.val)=some ((alphaPermutation n k).val) ∧
      u.natHeap (betaBase (ell n) (len n)+k.val)=some ((betaPermutation n k).val)) ∧
    Frame (ell n) s u := by
  obtain ⟨t,u,hr,ht,hT,hF⟩:=initialized_execution_linear hn B x s hp hh hc hs hB
  exact ⟨t,u,hr,ht,fun k=>tables_permutations n u hT k,hF⟩


/-- The actual initial-state producer: master root, constants, CRT data and
axis roots, followed by this permutation generator, then one final halt. -/
def fullProgram : Program := UniformAssembly.embed
  (UniformRootTableMachine.fullProgram.map (relocate 0 185)) program [.halt] 233

theorem initial_code : CodeAt UniformRootTableMachine.fullProgram fullProgram 0 185 := by
  intro i hi
  simp only [fullProgram,UniformAssembly.embed,Nat.zero_add]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_map];omega)]
  rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map]

theorem traversal_code : CodeAt program fullProgram 185 233 := UniformAssembly.embed_code _ _ _ _

theorem fullProgram_length : fullProgram.length=234 := by
  rw [fullProgram,UniformAssembly.embed_length,List.length_map,
    UniformRootTableMachine.fullProgram_length,program_length]
  rfl

theorem full_finish_code : fullProgram[233]?=some .halt := by
  simp only [fullProgram,UniformAssembly.embed]
  rw [List.getElem?_append_right (by simp only [List.length_append,List.length_map,
    UniformRootTableMachine.fullProgram_length,program_length];omega)]
  simp only [List.length_append,List.length_map,UniformRootTableMachine.fullProgram_length,
    program_length,Nat.reduceAdd,Nat.sub_self]
  rfl

def preparationBudget (n : ℕ) : ℕ := UniformRootTableMachine.fullPreparationBudget n+
  cycleBudget (ell n) (selectedRadices n)+1

theorem full_word_bound_setup {n : ℕ} (hn:0<n) :
    (n+2)^16≤(n+2)^17 ∧ 234≤(n+2)^17 ∧ 128+10*ell n+4*len n≤(n+2)^17 := by
  have hell:ell n≤2*n:=by
    have h:=UniformWorkingLength.firstExceed_bound n
    unfold ell UniformWorkingLength.axisCount
    omega
  have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hn
  have hp:128≤(n+2)^16:=by
    have hh:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 16
    norm_num at hh
    omega
  have h234:234≤(n+2)^17:=by
    have hh:=Nat.pow_le_pow_left (show 3≤n+2 by omega) 17
    norm_num at hh
    omega
  refine ⟨Nat.pow_le_pow_right (by omega) (by decide),h234,?_⟩
  calc
    _≤128*(n+2):=by omega
    _≤(n+2)^16*(n+2):=Nat.mul_le_mul_right (n+2) hp
    _=(n+2)^17:=(pow_succ (n+2) 16).symm

/-- Closed, fixed finite-program execution from initial state; the only root
request is the original specified master root. Every permutation cell is produced
by charged instructions, with polynomial integer/address words. -/
theorem preparation_execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) : ∃t u,
    BoundedExecution fullProgram n x ((n+2)^17) initial t u ∧ t≤preparationBudget n ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    (∀k:Fin (len n),u.natHeap (alphaBase (ell n)+k.val)=some ((alphaPermutation n k).val) ∧
      u.natHeap (betaBase (ell n) (len n)+k.val)=some ((betaPermutation n k).val)) ∧
    (∀j:Fin 6,u.scalarHeap j.val=some (UniformPairMachine.prepared (UniformCConstantsMachine.bank n j))) ∧
    (∀j:Fin (ell n+1),u.scalarHeap (6+j.val)=
      some (UniformPairMachine.prepared (OAI.ExactFourier.zeta (radices n j)))) ∧
    u.rootOrders=[UniformMasterRootMachine.order n] ∧ u.outputs=initial.outputs ∧
    u.natReg 8=n ∧ u.natReg 24=UniformMasterRootMachine.order n ∧ u.pc=233 := by
  obtain ⟨hmono,hcode,hB⟩:=full_word_bound_setup hn
  obtain ⟨tc,v,hv,hheader,hcrt,horder,h8,hbank,haxes,hroots,hout,_hpc,hcost⟩:=
    UniformRootTableMachine.preparation_execution hn x
  let entry:State:={v with pc:=0}
  have heB:WordBound ((n+2)^17) entry:=changePC_bound _ v 0
    (UniformAssembly.wordBound_mono hmono hv.final_bound) (by omega)
  obtain ⟨tt,u,hu,htcost,hTables,hframe,hheader',hcrt',_hup,_hord,_hz,_hA,_hD⟩:=
    initialized_execution hn ((n+2)^17) x entry rfl hheader hcrt heB hB
  have hprefix:BoundedRuns fullProgram n x ((n+2)^17) initial tc {v with pc:=185}:=by
    have h:=UniformAssembly.BoundedExecution.placed initial_code
      (by omega : 0+(n+2)^16≤(n+2)^17) (by omega : 185≤(n+2)^17) hv
    simpa [placed,initial] using h
  have htail:BoundedRuns fullProgram n x ((n+2)^17) {v with pc:=185} tt {u with pc:=233}:=by
    have h:=UniformBoundedAssembly.boundedExecution_placed traversal_code
      (by rw [program_length];omega) (by omega) hu
    simpa [placed,entry] using h
  let final:State:={u with pc:=233}
  have hhalt:BoundedExecution fullProgram n x ((n+2)^17) final 1 final:=
    .halt htail.final_bound (by simp [step,final,full_finish_code])
  refine ⟨tc+tt+1,final,(hprefix.trans htail).executes hhalt,?_,hheader',hcrt',
    fun k=>tables_permutations n u hTables k,?_,?_,?_,?_,?_,?_,rfl⟩
  · unfold preparationBudget;omega
  · intro j;exact (congrFun hframe.2.1 j.val).trans (hbank j)
  · intro j;exact (congrFun hframe.2.1 (6+j.val)).trans (haxes j)
  · exact hframe.2.2.2.1.trans hroots
  · exact hframe.2.2.1.trans hout
  · exact (hframe.2.2.2.2.1 8 (by decide)).trans h8
  · exact (hframe.2.2.2.2.1 24 (by decide)).trans horder


theorem preparationBudget_isBigO_input :
    (fun n:ℕ=>(preparationBudget n:ℝ)) =O[Filter.atTop] (fun n:ℕ=>(n:ℝ)) := by
  have hcycle:(fun n:ℕ=>((cycleBudget (ell n) (selectedRadices n)+1:ℕ):ℝ))
      =O[Filter.atTop] (fun n:ℕ=>(n:ℝ)):=by
    apply Asymptotics.IsBigO.of_bound 217
    filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with n hn
    have hnpos:0<n:=by omega
    have hell:ell n≤2*n:=by
      have h:=UniformWorkingLength.firstExceed_bound n
      unfold ell UniformWorkingLength.axisCount
      omega
    have hL:len n<4*n:=UniformWorkingLength.workingLength_upper hnpos
    have hc:cycleBudget (ell n) (selectedRadices n)+1≤217*n:=by
      have hh:=selected_cycleBudget_bound n
      change cycleBudget (ell n) (selectedRadices n)<46*len n+5*ell n+21 at hh
      omega
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using
      (show ((cycleBudget (ell n) (selectedRadices n)+1:ℕ):ℝ)≤217*(n:ℝ) by exact_mod_cast hc)
  have h:=UniformRootTableMachine.fullPreparationBudget_isLittleO_input.isBigO.add hcycle
  simpa only [preparationBudget,Nat.cast_add,add_assoc] using h

noncomputable section

/-- The specified local phase, including the retained order-one factor. -/
theorem specifiedRoot_pow_mod (q : ℕ) (hq:0<q) (k : ℕ) :
    OAI.ExactFourier.zeta q^k=OAI.ExactFourier.zeta q^(k%q) := by
  let :NeZero q:=⟨hq.ne'⟩
  rw [←OAI.ExactFourier.FourierCRT.standard_root q,←OAI.ExactFourier.FourierCRT.char_nat,
    ←OAI.ExactFourier.FourierCRT.char_nat]
  simp only [ZMod.natCast_mod]

/-- The beta table cancels the local output inverse phase; each local transform
therefore uses the specified standard root, not an unspecified primitive root. -/
theorem crt_standard_phase {a : ℕ} (r : Fin a→ℕ) (hr:∀i,0<r i)
    (hc:Pairwise (fun i j=>Nat.Coprime (r i) (r j))) (j k : ∀i,Fin (r i)) :
    OAI.ExactFourier.zeta (∏i,r i)^
      ((UniformCRT.encode r hr j).val*(UniformCRT.encode r hr (outputDigits r hr k)).val)=
        ∏i,OAI.ExactFourier.zeta (r i)^((j i).val*(k i).val) := by
  rw [UniformCRT.fourier_phase r hr hc]
  apply Finset.prod_congr rfl
  intro i _
  have he:=outputDigits_inverse_local r hr hc k i
  change (UniformCRT.inverseDigit r i*(outputDigits r hr k i).val)%r i=(k i).val at he
  rw [specifiedRoot_pow_mod _ (hr i),specifiedRoot_pow_mod _ (hr i) ((j i).val*(k i).val)]
  apply congrArg (fun e:ℕ=>OAI.ExactFourier.zeta (r i)^e)
  rw [Nat.mul_right_comm,Nat.mul_mod,he,Nat.mod_eq_of_lt (j i).isLt,Nat.mul_comm]

/-- Exact factorization at the generated input and output addresses. -/
theorem permutation_fourier_entry (n : ℕ) (j k : Fin (len n)) :
    OAI.ExactFourier.fourierMatrix (len n) (alphaPermutation n j) (betaPermutation n k)=
      ∏i,OAI.ExactFourier.zeta (radices n i)^((ordinalEquiv n j i).val*(ordinalEquiv n k i).val) := by
  have h:=crt_standard_phase (radices n) (UniformSelectedCRT.radix_pos n)
    (UniformSelectedCRT.radices_pairwise n) (ordinalEquiv n j) (ordinalEquiv n k)
  change OAI.ExactFourier.zeta (len n)^(UniformCRT.address (radices n) (ordinalEquiv n j)*
    UniformCRT.address (radices n) (outputDigits (radices n) (UniformSelectedCRT.radix_pos n) (ordinalEquiv n k)))=_
  simpa only [UniformCRT.encode,UniformSelectedCRT.radices_product] using h


/-- Entire produced Nat prefix, suitable for a charged relocation copier. -/
def prefixSize (n : ℕ) : ℕ := 6*ell n+5+2*len n

def FilledPrefix (n : ℕ) (s : State) : Prop := ∀a,a<prefixSize n → ∃v,s.natHeap a=some v

theorem crt_present (n : ℕ) (s : State) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (i : Fin (ell n+1)) (field : Fin 4) :
    ∃v,s.natHeap (UniformCRTHeaderMachine.tableAddress (ell n) i.val field.val)=some v := by
  obtain ⟨hq,hc,hinv,hidem⟩:=hc i
  fin_cases field
  · exact ⟨radices n i,hq⟩
  · exact ⟨betaWeights n i,hc⟩
  · exact ⟨UniformCRT.inverseDigit (radices n) i,hinv⟩
  · exact ⟨alphaWeights n i,hidem⟩

theorem filled_prefix (n : ℕ) (s : State) (hh:UniformCRTHeaderMachine.Header n s)
    (hc:UniformCRTHeaderMachine.CRTTable n s) (hz:DigitsZero (ell n) (ell n+1) s)
    (ht:Tables n (len n) s) : FilledPrefix n s := by
  intro a ha
  obtain ⟨_h0,_h10,_h11,_h16,_h17,_h18,hprime⟩:=hh
  by_cases hp:a<ell n
  · exact ⟨UniformWorkingLength.oddPrime a,hprime a hp⟩
  · by_cases hcrt:a<digitBase (ell n)
    · let d:=a-ell n
      have hm:d%4<4:=Nat.mod_lt _ (by decide)
      have he:=Nat.mod_add_div d 4
      have had:a=ell n+d:=by dsimp [d];omega
      have hi:d/4<ell n+1:=by unfold digitBase at hcrt;omega
      obtain ⟨v,hv⟩:=crt_present n s hc ⟨d/4,hi⟩ ⟨d%4,hm⟩
      refine ⟨v,?_⟩
      have haddr:UniformCRTHeaderMachine.tableAddress (ell n) (d/4) (d%4)=a:=by
        unfold UniformCRTHeaderMachine.tableAddress;omega
      simpa only [haddr] using hv
    · by_cases hdigit:a<alphaBase (ell n)
      · have hi:a-digitBase (ell n)<ell n+1:=by unfold alphaBase at hdigit;omega
        refine ⟨0,?_⟩
        simpa only [Nat.add_sub_of_le (show digitBase (ell n)≤a by omega)] using hz (a-digitBase (ell n)) hi
      · by_cases hA:a<betaBase (ell n) (len n)
        · have hj:a-alphaBase (ell n)<len n:=by unfold betaBase at hA;omega
          obtain ⟨hv,_⟩:=ht (a-alphaBase (ell n)) hj
          refine ⟨weightedAddress (len n) (alphaWeights n) (decoded (radices n) (a-alphaBase (ell n))),?_⟩
          simpa only [Nat.add_sub_of_le (show alphaBase (ell n)≤a by omega)] using hv
        · have hj:a-betaBase (ell n) (len n)<len n:=by
            simp only [prefixSize,betaBase,alphaBase,digitBase] at hA ha ⊢
            omega
          obtain ⟨_,hv⟩:=ht (a-betaBase (ell n) (len n)) hj
          refine ⟨weightedAddress (len n) (betaWeights n) (decoded (radices n) (a-betaBase (ell n) (len n))),?_⟩
          simpa only [Nat.add_sub_of_le (show betaBase (ell n) (len n)≤a by omega)] using hv

/-- The initialized generator supplies the whole copier source, with the
original header and arbitrary scalar banks retained by actual execution. -/
theorem initialized_execution_source {n : ℕ} (hn:0<n) (B : ℕ) (x : Fin n→ℂ) (s : State)
    (hp:s.pc=0) (hh:UniformCRTHeaderMachine.Header n s) (hc:UniformCRTHeaderMachine.CRTTable n s)
    (hs:WordBound B s) (hB:128+10*ell n+4*len n≤B) : ∃t u,
    BoundedExecution program n x B s t u ∧ t<46*len n+5*ell n+21 ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    Tables n (len n) u ∧ FilledPrefix n u ∧ Frame (ell n) s u ∧ u.pc=47 := by
  obtain ⟨t,u,hr,ht,hT,hF,hheader,hcrt,hpc,_hord,hz,_hA,_hD⟩:=
    initialized_execution hn B x s hp hh hc hs hB
  exact ⟨t,u,hr,ht.trans_lt (selected_cycleBudget_bound n),hheader,hcrt,hT,
    filled_prefix n u hheader hcrt hz hT,hF,hpc⟩

end
end ExactFourierCircuits.UniformCRTTraversalCycle
