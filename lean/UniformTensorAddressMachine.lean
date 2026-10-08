import UniformCRTTraversalCycle

set_option autoImplicit false
namespace ExactFourierCircuits.UniformTensorAddressMachine
open UniformMachine UniformAssembly
open scoped BigOperators

/-- Least-axis-first integer address; the lower axes vary fastest. -/
def address (P r j t : ℕ) : ℕ := j%P+P*(t+r*(j/P))

/-- Explicit finite quotient/remainder coordinates, not a chosen permutation. -/
def fiberEquiv (P r Q : ℕ) : (Fin (P*Q) × Fin r) ≃ Fin (P*r*Q) :=
  (((((Equiv.prodCongr
    ((finCongr (Nat.mul_comm P Q)).trans finProdFinEquiv.symm) (Equiv.refl (Fin r))).trans
      (Equiv.prodAssoc (Fin Q) (Fin P) (Fin r))).trans
      (Equiv.prodCongr (Equiv.refl (Fin Q)) (Equiv.prodComm (Fin P) (Fin r)))).trans
      (Equiv.prodAssoc (Fin Q) (Fin r) (Fin P)).symm).trans
      (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin P)))).trans
      (finProdFinEquiv.trans (finCongr (by ac_rfl)))

theorem fiberEquiv_address (P r Q : ℕ) (j : Fin (P*Q)) (t : Fin r) :
    (fiberEquiv P r Q (j,t)).val=address P r j.val t.val := by
  rfl

theorem address_lt (P r Q j t : ℕ) (hj:j<P*Q) (ht:t<r) :
    address P r j t<P*r*Q := (fiberEquiv P r Q (⟨j,hj⟩,⟨t,ht⟩)).isLt

theorem address_bijective (P r Q : ℕ) : Function.Bijective (fiberEquiv P r Q) :=
  (fiberEquiv P r Q).bijective

theorem address_coverage (P r Q : ℕ) (a : Fin (P*r*Q)) :
    ∃!jt:Fin (P*Q)×Fin r,address P r jt.1.val jt.2.val=a.val := by
  refine ⟨(fiberEquiv P r Q).symm a,?_,?_⟩
  · exact congrArg Fin.val ((fiberEquiv P r Q).apply_symm_apply a)
  · intro jt h
    rcases jt with ⟨j,t⟩
    apply (fiberEquiv P r Q).injective
    apply Fin.ext
    simpa only [fiberEquiv_address,Equiv.apply_symm_apply] using h

/-- Nat70=P,71=radix,72=upper count,73=fiber,81=local digit.
Six literal arithmetic instructions produce Nat99, followed by a charged halt.
Only Nat89..93 and99 are written. -/
def program : Program := [
  .natBinary .mod 89 73 70,.natBinary .div 90 73 70,
  .natBinary .mul 91 71 90,.natBinary .add 92 81 91,
  .natBinary .mul 93 70 92,.natBinary .add 99 89 93,.halt]

theorem program_length : program.length=7 := rfl

noncomputable section

/-- All storage banks and saved global headers survive decoding. -/
def Frame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
  u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀r,(r<89 ∨ 99<r) → u.natReg r=s.natReg r

def remainderState (s : State) : State := writeNat s 89 (s.natReg 73%s.natReg 70)
def quotientState (s : State) : State := writeNat (remainderState s) 90 (s.natReg 73/s.natReg 70)
def strideState (s : State) : State := writeNat (quotientState s) 91 (s.natReg 71*(s.natReg 73/s.natReg 70))
def indexState (s : State) : State := writeNat (strideState s) 92 (s.natReg 81+s.natReg 71*(s.natReg 73/s.natReg 70))
def scaledState (s : State) : State := writeNat (indexState s) 93 (s.natReg 70*(s.natReg 81+s.natReg 71*(s.natReg 73/s.natReg 70)))
def decodedState (s : State) : State := writeNat (scaledState s) 99
  (address (s.natReg 70) (s.natReg 71) (s.natReg 73) (s.natReg 81))

theorem decoded_frame (s : State) : Frame s (decodedState s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r hr
  simp [decodedState,scaledState,indexState,strideState,quotientState,remainderState,writeNat,next,
    show r≠89 by omega,show r≠90 by omega,show r≠91 by omega,show r≠92 by omega,
    show r≠93 by omega,show r≠99 by omega]

/-- Every genuinely computed integer fits the same ambient word bound. -/
theorem intermediate_bounds (P r Q j t B : ℕ) (hP:0<P) (hj:j<P*Q) (ht:t<r)
    (hL:P*r*Q≤B) : j%P≤B ∧ j/P≤B ∧ r*(j/P)≤B ∧
    t+r*(j/P)≤B ∧ P*(t+r*(j/P))≤B ∧ address P r j t≤B := by
  have ha:=address_lt P r Q j t hj ht
  have hsplit:=Nat.mod_add_div j P
  have hPr:1≤r:=by omega
  have hQP:=hj
  have hinner:t+r*(j/P)≤P*(t+r*(j/P)):=by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (t+r*(j/P)) (show 1≤P by omega)
  have haddr:address P r j t≤B:=by omega
  unfold address at ha haddr
  have hjB:j≤B:=by nlinarith
  have hdiv:=Nat.div_le_self j P
  refine ⟨by omega,by omega,?_,?_,?_,haddr⟩ <;> omega

/-- Actual fixed RAM decoder; argument setup and iteration over fibers are
separate obligations. No address array or decoder-action premise is assumed. -/
theorem execution (n : ℕ) (x : Fin n→ℂ) (P r Q j t B : ℕ) (s : State)
    (hP:0<P) (hj:j<P*Q) (ht:t<r) (hL:P*r*Q≤B) (hcode:6≤B)
    (hpc:s.pc=0) (h70:s.natReg 70=P) (h71:s.natReg 71=r) (_h72:s.natReg 72=Q)
    (h73:s.natReg 73=j) (h81:s.natReg 81=t) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s 7 u ∧ u.natReg 99=address P r j t ∧
    u.natReg 99<P*r*Q ∧ Frame s u ∧ u.pc=6 := by
  obtain ⟨hb0,hb1,hb2,hb3,hb4,hb5⟩:=intermediate_bounds P r Q j t B hP hj ht hL
  have h0:WordBound B (remainderState s):=writeNat_bound B s 89 _ hs
    (by rw [hpc];omega) (by simpa [h70,h73] using hb0)
  have h1:WordBound B (quotientState s):=writeNat_bound B (remainderState s) 90 _ h0
    (by simp [remainderState,writeNat,next,hpc];omega) (by simpa [h70,h73] using hb1)
  have h2:WordBound B (strideState s):=writeNat_bound B (quotientState s) 91 _ h1
    (by simp [quotientState,remainderState,writeNat,next,hpc];omega) (by simpa [h70,h71,h73] using hb2)
  have h3:WordBound B (indexState s):=writeNat_bound B (strideState s) 92 _ h2
    (by simp [strideState,quotientState,remainderState,writeNat,next,hpc];omega)
    (by simpa [h70,h71,h73,h81] using hb3)
  have h4:WordBound B (scaledState s):=writeNat_bound B (indexState s) 93 _ h3
    (by simp [indexState,strideState,quotientState,remainderState,writeNat,next,hpc];omega)
    (by simpa [h70,h71,h73,h81] using hb4)
  have h5:WordBound B (decodedState s):=writeNat_bound B (scaledState s) 99 _ h4
    (by simp [scaledState,indexState,strideState,quotientState,remainderState,writeNat,next,hpc];omega)
    (by simpa [h70,h71,h73,h81] using hb5)
  have hPne:s.natReg 70≠0:=by omega
  have t0:step program n x s=.running (remainderState s):=by
    simp [step,program,remainderState,evalNat,hpc,hPne]
  have t1:step program n x (remainderState s)=.running (quotientState s):=by
    simp [step,program,quotientState,remainderState,writeNat,next,evalNat,hpc,hPne]
  have t2:step program n x (quotientState s)=.running (strideState s):=by
    simp [step,program,strideState,quotientState,remainderState,writeNat,next,evalNat,hpc]
  have t3:step program n x (strideState s)=.running (indexState s):=by
    simp [step,program,indexState,strideState,quotientState,remainderState,writeNat,next,evalNat,hpc]
  have t4:step program n x (indexState s)=.running (scaledState s):=by
    simp [step,program,scaledState,indexState,strideState,quotientState,remainderState,writeNat,next,evalNat,hpc]
  have t5:step program n x (scaledState s)=.running (decodedState s):=by
    simp [step,program,decodedState,scaledState,indexState,strideState,quotientState,remainderState,
      writeNat,next,evalNat,hpc,address]
  have t6:step program n x (decodedState s)=.halted (decodedState s):=by
    simp [step,program,decodedState,scaledState,indexState,strideState,quotientState,remainderState,writeNat,next,hpc]
  refine ⟨decodedState s,.next hs t0 (.next h0 t1 (.next h1 t2 (.next h2 t3
    (.next h3 t4 (.next h4 t5 (.halt h5 t6)))))),?_,?_,decoded_frame s,?_⟩
  · simp [decodedState,writeNat,next,h70,h71,h73,h81]
  · simpa [decodedState,writeNat,next,h70,h71,h73,h81] using address_lt P r Q j t hj ht
  · simp [decodedState,scaledState,indexState,strideState,quotientState,remainderState,writeNat,next,hpc]

theorem Frame.saved_headers {s u : State} (h:Frame s u) (a : ℕ) (ha:100≤a) :
    u.natReg a=s.natReg a := h.2.2.2.2.2 a (Or.inr (by omega))

def wordBudget (P r Q : ℕ) : ℕ := max (P*r*Q) 100

theorem wordBudget_polynomial (P r Q : ℕ) :
    wordBudget P r Q≤100*((P+1)*(r+1)*(Q+1)) := by
  have hprod:0<(P+1)*(r+1)*(Q+1):=Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hmul:P*r*Q≤(P+1)*(r+1)*(Q+1):=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
  unfold wordBudget;omega

theorem execution_budget (n : ℕ) (x : Fin n→ℂ) (P r Q j t : ℕ) (s : State)
    (hP:0<P) (hj:j<P*Q) (ht:t<r)
    (hpc:s.pc=0) (h70:s.natReg 70=P) (h71:s.natReg 71=r) (h72:s.natReg 72=Q)
    (h73:s.natReg 73=j) (h81:s.natReg 81=t) (hs:WordBound (wordBudget P r Q) s) : ∃u,
    BoundedExecution program n x (wordBudget P r Q) s 7 u ∧ u.natReg 99=address P r j t ∧
    u.natReg 99<P*r*Q ∧ Frame s u ∧ u.pc=6 :=
  execution n x P r Q j t _ s hP hj ht (by unfold wordBudget;omega)
    (by unfold wordBudget;omega) hpc h70 h71 h72 h73 h81 hs

theorem fiberEquiv_inverse_coordinates (P r Q : ℕ) (a : Fin (P*r*Q)) :
    ((fiberEquiv P r Q).symm a).1.val=a.val%P+P*((a.val/P)/r) ∧
    ((fiberEquiv P r Q).symm a).2.val=(a.val/P)%r := ⟨rfl,rfl⟩

theorem unit_radix (P j : ℕ) : address P 1 j 0=j := by
  simpa only [address,Nat.one_mul,Nat.zero_add] using Nat.mod_add_div j P

theorem unit_lower (r j t : ℕ) : address 1 r j t=t+r*j := by simp [address];omega

theorem unit_upper (P r j t : ℕ) (hj:j<P) : address P r j t=j+P*t := by
  simp [address,Nat.mod_eq_of_lt hj,Nat.div_eq_of_lt hj]

theorem address_quotient (P r j t : ℕ) (hP:0<P) :
    address P r j t/P=t+r*(j/P) := by
  rw [address,Nat.add_mul_div_left _ _ hP,Nat.div_eq_of_lt (Nat.mod_lt j hP),Nat.zero_add]

theorem address_digit (P r j t : ℕ) (hP:0<P) (ht:t<r) :
    (address P r j t/P)%r=t := by
  rw [address_quotient P r j t hP,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ht]

/-- A zero lower radix is rejected by the actual first modulo instruction. -/
theorem zero_lower_failure (n : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hzero:s.natReg 70=0) : step program n x s=.failed := by
  simp [step,program,evalNat,hpc,hzero]

/-- The upper-axis factor is an explicit product of the actual remaining radices. -/
def upperCount {a : ℕ} (r : Fin a→ℕ) (i : Fin a) : ℕ :=
  ((List.ofFn r).drop (i.val+1)).prod

theorem layout_product {a : ℕ} (r : Fin a→ℕ) (i : Fin a) :
    UniformCRTTraversalCycle.place r i.val*r i*upperCount r i=∏j,r j := by
  have h:=List.prod_take_mul_prod_drop (List.ofFn r) (i.val+1)
  change UniformCRTTraversalCycle.place r (i.val+1)*upperCount r i=(List.ofFn r).prod at h
  simpa only [UniformCRTTraversalCycle.place_succ,List.prod_ofFn] using h

theorem upperCount_pos {a : ℕ} (r : Fin a→ℕ) (hr:∀j,0<r j) (i : Fin a) :
    0<upperCount r i := by
  apply List.prod_pos
  intro v hv
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hv)
  exact hr j

theorem selected_layout (n : ℕ) (i : Fin (UniformCRTTraversalCycle.ell n+1)) :
    UniformCRTTraversalCycle.place (UniformCRTTraversalCycle.radices n) i.val*
      UniformCRTTraversalCycle.radices n i*upperCount (UniformCRTTraversalCycle.radices n) i=
        UniformCRTTraversalCycle.len n := by
  rw [layout_product]
  exact UniformSelectedCRT.radices_product n

theorem selected_digit (n : ℕ) (i : Fin (UniformCRTTraversalCycle.ell n+1)) (j t : ℕ)
    (ht:t<UniformCRTTraversalCycle.radices n i) :
    UniformCRTTraversalCycle.decoded (UniformCRTTraversalCycle.radices n)
      (address (UniformCRTTraversalCycle.place (UniformCRTTraversalCycle.radices n) i.val)
        (UniformCRTTraversalCycle.radices n i) j t) i=t :=
  address_digit _ _ j t
    (UniformCRTTraversalCycle.place_pos _ (UniformSelectedCRT.radix_pos n) _) ht

/-- Actual selected-axis place/radix factors instantiate this same literal
decoder. Computing and loading those parameters remains caller-charged. -/
theorem selected_execution (n : ℕ) (x : Fin n→ℂ) (i : Fin (UniformCRTTraversalCycle.ell n+1))
    (j t B : ℕ) (s : State)
    (hj:j<UniformCRTTraversalCycle.place (UniformCRTTraversalCycle.radices n) i.val*
      upperCount (UniformCRTTraversalCycle.radices n) i)
    (ht:t<UniformCRTTraversalCycle.radices n i) (hL:UniformCRTTraversalCycle.len n≤B) (hcode:6≤B)
    (hpc:s.pc=0) (h70:s.natReg 70=UniformCRTTraversalCycle.place (UniformCRTTraversalCycle.radices n) i.val)
    (h71:s.natReg 71=UniformCRTTraversalCycle.radices n i)
    (h72:s.natReg 72=upperCount (UniformCRTTraversalCycle.radices n) i)
    (h73:s.natReg 73=j) (h81:s.natReg 81=t) (hs:WordBound B s) : ∃u,
    BoundedExecution program n x B s 7 u ∧
    u.natReg 99=address (UniformCRTTraversalCycle.place (UniformCRTTraversalCycle.radices n) i.val)
      (UniformCRTTraversalCycle.radices n i) j t ∧
    u.natReg 99<UniformCRTTraversalCycle.len n ∧ Frame s u ∧ u.pc=6 := by
  obtain ⟨u,hu,ha,hbound,hframe,hpu⟩:=execution n x _ _ _ j t B s
    (UniformCRTTraversalCycle.place_pos _ (UniformSelectedCRT.radix_pos n) _)
    hj ht (by rw [selected_layout];exact hL) hcode hpc h70 h71 h72 h73 h81 hs
  exact ⟨u,hu,ha,by simpa only [selected_layout] using hbound,hframe,hpu⟩

end
end ExactFourierCircuits.UniformTensorAddressMachine
