import UniformRootTableMachine
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
namespace ExactFourierCircuits.UniformCRTTraversalMachine
open UniformMachine UniformAssembly
open scoped BigOperators

/-- Least-axis-first carry visits over one complete mixed-radix cycle. -/
def carryVisits : List ℕ → ℕ
  | [] => 0
  | q::qs => q*qs.prod+carryVisits qs

/-- Unit radices are allowed only at the final (most significant) axis. -/
def CarryRadices (rs : List ℕ) : Prop :=
  (∀ q∈rs,0<q) ∧ ∀ i,(hi:i+1<rs.length) → 2≤rs[i]' (by omega)

theorem carryVisits_bound (rs : List ℕ) (hr : CarryRadices rs) :
    carryVisits rs<2*rs.prod := by
  induction rs with
  | nil => simp [carryVisits]
  | cons q qs ih =>
      have hq:0<q:=hr.1 q (by simp)
      have htail:CarryRadices qs:=by
        refine ⟨fun v hv => hr.1 v (by simp [hv]),?_⟩
        intro i hi
        simpa using hr.2 (i+1) (by simp only [List.length_cons];omega)
      have hp:0<qs.prod:=List.prod_pos (fun v hv => htail.1 v hv)
      have ht:=ih htail
      by_cases he:qs=[]
      · subst qs;simp [carryVisits];omega
      · have hq2:2≤q:=by
          simpa using hr.2 0 (by have hl:0<qs.length:=List.length_pos_iff.mpr he;simp;omega)
        simp only [carryVisits,List.prod_cons]
        nlinarith

/-- A wrap is the same one modular addition as an ordinary increment. -/
theorem weighted_digit_mod (L q w d : ℕ) (_hq : 0<q) (hw : L∣q*w) :
    (w*(d%q))%L=(w*d)%L := by
  have he:w*(d%q)+q*w*(d/q)=w*d:=by
    have h:=Nat.mod_add_div d q
    nlinarith
  have hz:(q*w*(d/q))%L=0:=Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hw _)
  rw [←he,Nat.add_mod,hz,Nat.add_zero,Nat.mod_mod]

theorem weighted_wrap (L q w : ℕ) (hq : 0<q) (hw : L∣q*w) :
    (w*(q-1)+w)%L=0 := by
  have he:w*(q-1)+w=q*w:=by have h:=Nat.sub_add_cancel (show 1≤q by omega);nlinarith
  rw [he];exact Nat.mod_eq_zero_of_dvd hw

theorem cofactor_weight_divides {a : ℕ} (r : Fin a→ℕ) (i : Fin a) :
    (∏ j,r j)∣r i*UniformCRT.cofactor r i := by
  rw [Nat.mul_comm,UniformCRT.cofactor_mul]

theorem idempotent_weight_divides {a : ℕ} (r : Fin a→ℕ) (i : Fin a) :
    (∏ j,r j)∣r i*UniformCRT.idempotent r i := by
  rw [UniformCRT.idempotent]
  have he:r i*(UniformCRT.cofactor r i*UniformCRT.inverseDigit r i)=
      (∏ j,r j)*UniformCRT.inverseDigit r i:=by rw [←Nat.mul_assoc,Nat.mul_comm (r i),UniformCRT.cofactor_mul]
  rw [he]
  exact dvd_mul_right _ _

/-- Registers50..68 are private. New digit/alpha/beta regions begin strictly
above the prime and four-field CRT table. Each carried digit takes ≤20 fixed
instructions; no per-leaf axis scan or host permutation is used. -/
def program : Program := [
  .natLiteral 64 1,.natLiteral 65 0,.natLiteral 66 4,.natLiteral 67 5,
  .natBinary .add 50 10 64,.natBinary .mul 51 10 67,.natBinary .add 51 51 66,
  .natBinary .add 52 51 50,.natBinary .add 53 52 17,
  .natLiteral 54 0,.natLiteral 55 0,.natLiteral 56 0,.natLiteral 57 0,
  .branchLT 57 50 14 19,.natBinary .add 58 51 57,.storeNat 58 65,
  .natBinary .add 57 57 64,.jump 13,.jump 13,
  .natBinary .add 68 52 54,.storeNat 68 55,
  .natBinary .add 68 53 54,.storeNat 68 56,
  .natBinary .add 54 54 64,.natLiteral 57 0,
  .branchLT 57 50 26 47,
  .natBinary .add 58 51 57,.loadNat 59 58,
  .natBinary .mul 60 57 66,.natBinary .add 60 10 60,.loadNat 61 60,
  .natBinary .add 60 60 64,.loadNat 63 60,
  .natBinary .add 60 60 64,.natBinary .add 60 60 64,.loadNat 62 60,
  .natBinary .add 55 55 62,.natBinary .mod 55 55 17,
  .natBinary .add 56 56 63,.natBinary .mod 56 56 17,
  .natBinary .add 59 59 64,.branchLT 59 61 42 44,
  .storeNat 58 59,.jump 19,
  .storeNat 58 65,.natBinary .add 57 57 64,.jump 25,.halt]

theorem program_length : program.length=48 := rfl

def digitBase (ell : ℕ) : ℕ := 5*ell+4
def alphaBase (ell : ℕ) : ℕ := digitBase ell+ell+1
def betaBase (ell L : ℕ) : ℕ := alphaBase ell+L

theorem regions_disjoint (ell L i j : ℕ) (hi : i<ell+1) (hj : j<L) :
    5*ell+3<digitBase ell+i ∧ digitBase ell+i<alphaBase ell ∧
    alphaBase ell+j<betaBase ell L ∧ betaBase ell L+j<alphaBase ell+2*L := by
  simp only [digitBase,alphaBase,betaBase]
  omega


def selectedRadices (n : ℕ) : List ℕ :=
  List.ofFn (fun i:Fin (UniformWorkingLength.axisCount n) => UniformWorkingLength.oddPrime i.val) ++
    [UniformWorkingLength.binaryFactor n]

theorem selected_radices_valid (n : ℕ) : CarryRadices (selectedRadices n) := by
  refine ⟨?_,?_⟩
  · intro q hq
    simp only [selectedRadices,List.mem_append,List.mem_singleton,List.mem_ofFn] at hq
    rcases hq with ⟨i,rfl⟩ | rfl
    · exact (UniformWorkingLength.oddPrime_prime i.val).pos
    · exact Nat.two_pow_pos _
  · intro i hi
    have hi':i<UniformWorkingLength.axisCount n:=by
      simp only [selectedRadices,List.length_append,List.length_ofFn,List.length_singleton] at hi
      omega
    unfold selectedRadices
    rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hi')]
    simp only [List.getElem_ofFn]
    have h:=UniformWorkingLength.oddPrime_lower i
    omega

theorem selected_radices_product (n : ℕ) :
    (selectedRadices n).prod=UniformWorkingLength.workingLength n := by
  rw [selectedRadices,List.prod_append,List.prod_ofFn]
  simp only [List.prod_cons,List.prod_nil,Nat.mul_one]
  rw [Fin.prod_univ_eq_prod_range,←UniformWorkingLength.primeProduct_eq_prod]
  rfl

theorem selected_carryVisits_bound (n : ℕ) :
    carryVisits (selectedRadices n)<2*UniformWorkingLength.workingLength n := by
  simpa only [selected_radices_product] using carryVisits_bound (selectedRadices n) (selected_radices_valid n)

/-- Tensor output digits are sent through cofactor multiplication, the inverse
of the local output permutation. -/
def outputDigits {a : ℕ} (r : Fin a→ℕ) (hr : ∀i,0<r i)
    (ds : ∀i,Fin (r i)) : ∀i,Fin (r i) :=
  fun i => ⟨UniformCRT.cofactor r i*(ds i).val%r i,Nat.mod_lt _ (hr i)⟩

def betaAddress {a : ℕ} (r : Fin a→ℕ) (ds : ∀i,Fin (r i)) : ℕ :=
  (∑ i,UniformCRT.cofactor r i*(ds i).val)%(∏ i,r i)

theorem outputDigits_inverse_local {a : ℕ} (r : Fin a→ℕ) (hr : ∀i,0<r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (ds : ∀i,Fin (r i)) (i : Fin a) :
    UniformCRT.localOutput r i ((outputDigits r hr ds i).val)=(ds i).val :=
  UniformCRT.inverse_localOutput r hr hc i (ds i)

noncomputable section

theorem idempotent_cofactor {a : ℕ} (r : Fin a→ℕ)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (i : Fin a) :
    (UniformCRT.idempotent r i:ZMod (∏ j,r j))*UniformCRT.cofactor r i=
      (UniformCRT.cofactor r i:ZMod (∏ j,r j)) := by
  apply (ZMod.prodEquivPi r hc).injective
  rw [map_mul]
  funext j
  simp only [Pi.mul_apply,ZMod.prodEquivPi_apply,ZMod.castHom_apply,
    ZMod.cast_natCast (Finset.dvd_prod_of_mem r (Finset.mem_univ j))]
  by_cases he:j=i
  · subst j
    rw [UniformCRT.idempotent_self r hc i,one_mul]
  · have hd:r j∣UniformCRT.cofactor r i:=
      Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨he,Finset.mem_univ j⟩)
    rw [(ZMod.natCast_eq_zero_iff _ _).2 hd,mul_zero]

theorem betaAddress_crt {a : ℕ} (r : Fin a→ℕ) (hr : ∀i,0<r i)
    (hc : Pairwise (fun i j => Nat.Coprime (r i) (r j))) (ds : ∀i,Fin (r i)) :
    betaAddress r ds=UniformCRT.address r (outputDigits r hr ds) := by
  have hL:0<∏ i,r i:=Finset.prod_pos (fun i _ => hr i)
  let :NeZero (∏i,r i):=⟨hL.ne'⟩
  apply (Nat.mod_eq_of_lt (Nat.mod_lt _ hL)).symm.trans
  change (betaAddress r ds)%(∏i,r i)=_
  have hs:(∑i,UniformCRT.cofactor r i*(ds i).val)%(∏i,r i)=
      (∑i,UniformCRT.idempotent r i*((outputDigits r hr ds i).val))%(∏i,r i):=by
    have hterm (i:Fin a):
        ((UniformCRT.idempotent r i*((outputDigits r hr ds i).val):ℕ):ZMod (∏i,r i))=
        ((UniformCRT.cofactor r i*(ds i).val:ℕ):ZMod (∏i,r i)):=by
      have hm:=weighted_digit_mod (∏i,r i) (r i) (UniformCRT.idempotent r i)
        (UniformCRT.cofactor r i*(ds i).val) (hr i) (idempotent_weight_divides r i)
      have ht:=congrArg (fun x:ℕ => (x:ZMod (∏i,r i))) hm
      simp only [ZMod.natCast_mod] at ht
      change ((UniformCRT.idempotent r i*(UniformCRT.cofactor r i*(ds i).val%r i):ℕ):ZMod (∏i,r i))=_
      rw [ht,Nat.cast_mul,Nat.cast_mul,←mul_assoc,idempotent_cofactor r hc i]
    have he:(∑i,((UniformCRT.cofactor r i*(ds i).val:ℕ):ZMod (∏i,r i)))=
        ∑i,((UniformCRT.idempotent r i*((outputDigits r hr ds i).val):ℕ):ZMod (∏i,r i)):=
      Finset.sum_congr rfl (fun i _ => (hterm i).symm)
    have hv:=congrArg ZMod.val he
    simpa only [←Nat.cast_sum,ZMod.val_natCast] using hv
  simpa only [betaAddress,UniformCRT.address,Nat.mod_mod] using hs


def store (s : State) (address value : ℕ) : State :=
  {next s with natHeap:=Function.update s.natHeap address (some value)}
def setPC (s : State) (pc : ℕ) : State := {s with pc:=pc}

structure Geometry (ell L : ℕ) (s : State) : Prop where
  ellValue : s.natReg 10=ell
  length : s.natReg 17=L
  axes : s.natReg 50=ell+1
  digits : s.natReg 51=digitBase ell
  alpha : s.natReg 52=alphaBase ell
  beta : s.natReg 53=betaBase ell L
  one : s.natReg 64=1
  zero : s.natReg 65=0
  four : s.natReg 66=4
  five : s.natReg 67=5

def emit1 (s : State) : State := writeNat s 68 (s.natReg 52+s.natReg 54)
def emit2 (s : State) : State := store (emit1 s) (s.natReg 52+s.natReg 54) (s.natReg 55)
def emit3 (s : State) : State := writeNat (emit2 s) 68 (s.natReg 53+s.natReg 54)
def emit4 (s : State) : State := store (emit3 s) (s.natReg 53+s.natReg 54) (s.natReg 56)
def emit5 (s : State) : State := writeNat (emit4 s) 54 (s.natReg 54+1)
def emit (s : State) : State := writeNat (emit5 s) 57 0

theorem emit_runs (n : ℕ) (x : Fin n→ℂ) (s : State) (hpc:s.pc=19)
    (h1:s.natReg 64=1) : Runs program n x s 6 (emit s) := by
  refine .next (u:=emit1 s) ?_ (.next (u:=emit2 s) ?_ (.next (u:=emit3 s) ?_
    (.next (u:=emit4 s) ?_ (.next (u:=emit5 s) ?_ (.next (u:=emit s) ?_ (.refl _))))))
  all_goals simp [step,program,emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next,hpc,h1,evalNat]

structure CarryReady (ell L i q wa wb d : ℕ) (s : State) : Prop where
  pc : s.pc=25
  geometry : Geometry ell L s
  index : s.natReg 57=i
  axis : i<ell+1
  digit : s.natHeap (digitBase ell+i)=some d
  radix : s.natHeap (ell+4*i)=some q
  alphaWeight : s.natHeap (ell+4*i+3)=some wa
  betaWeight : s.natHeap (ell+4*i+1)=some wb

def carry0 (s : State) : State := setPC s 26
def carry1 (ell _L i _q _wa _wb _d : ℕ) (s : State) : State := writeNat (carry0 s) 58 (digitBase ell+i)
def carry2 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry1 ell L i q wa wb d s) 59 (d)
def carry3 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry2 ell L i q wa wb d s) 60 (4*i)
def carry4 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry3 ell L i q wa wb d s) 60 (ell+4*i)
def carry5 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry4 ell L i q wa wb d s) 61 (q)
def carry6 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry5 ell L i q wa wb d s) 60 (ell+4*i+1)
def carry7 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry6 ell L i q wa wb d s) 63 (wb)
def carry8 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry7 ell L i q wa wb d s) 60 (ell+4*i+2)
def carry9 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry8 ell L i q wa wb d s) 60 (ell+4*i+3)
def carry10 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry9 ell L i q wa wb d s) 62 (wa)
def carry11 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry10 ell L i q wa wb d s) 55 (s.natReg 55+wa)
def carry12 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry11 ell L i q wa wb d s) 55 ((s.natReg 55+wa)%L)
def carry13 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry12 ell L i q wa wb d s) 56 (s.natReg 56+wb)
def carry14 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry13 ell L i q wa wb d s) 56 ((s.natReg 56+wb)%L)
def carry15 (ell L i q wa wb d : ℕ) (s : State) : State := writeNat (carry14 ell L i q wa wb d s) 59 (d+1)

def carrySuccess (ell L i q wa wb d : ℕ) (s : State) : State :=
  setPC (store (setPC (carry15 ell L i q wa wb d s) 42) (digitBase ell+i) (d+1)) 19
def carryWrap (ell L i q wa wb d : ℕ) (s : State) : State :=
  setPC (writeNat (store (setPC (carry15 ell L i q wa wb d s) 44)
    (digitBase ell+i) 0) 57 (i+1)) 25

def carry (ell L i q wa wb d : ℕ) (s : State) : State :=
  if d+1<q then carrySuccess ell L i q wa wb d s else carryWrap ell L i q wa wb d s

theorem carry_runs (n : ℕ) (x : Fin n→ℂ) (ell L i q wa wb d : ℕ) (s : State)
    (h : CarryReady ell L i q wa wb d s) (hL:0<L) :
    Runs program n x s (if d+1<q then 19 else 20) (carry ell L i q wa wb d s) := by
  have hqr:s.natHeap (ell+i*4)=some q:=by simpa [Nat.mul_comm] using h.radix
  have har:s.natHeap (ell+(i*4+3))=some wa:=by simpa [Nat.mul_comm,Nat.add_assoc] using h.alphaWeight
  have hbr:s.natHeap (ell+(i*4+1))=some wb:=by simpa [Nat.mul_comm,Nat.add_assoc] using h.betaWeight
  have stem:Runs program n x s 16 (carry15 ell L i q wa wb d s):=by
    refine .next (u:=carry0 s) ?_ (.next (u:=carry1 ell L i q wa wb d s) ?_ (.next (u:=carry2 ell L i q wa wb d s) ?_ (.next (u:=carry3 ell L i q wa wb d s) ?_ (.next (u:=carry4 ell L i q wa wb d s) ?_ (.next (u:=carry5 ell L i q wa wb d s) ?_ (.next (u:=carry6 ell L i q wa wb d s) ?_ (.next (u:=carry7 ell L i q wa wb d s) ?_ (.next (u:=carry8 ell L i q wa wb d s) ?_ (.next (u:=carry9 ell L i q wa wb d s) ?_ (.next (u:=carry10 ell L i q wa wb d s) ?_ (.next (u:=carry11 ell L i q wa wb d s) ?_ (.next (u:=carry12 ell L i q wa wb d s) ?_ (.next (u:=carry13 ell L i q wa wb d s) ?_ (.next (u:=carry14 ell L i q wa wb d s) ?_ (.next (u:=carry15 ell L i q wa wb d s) ?_ (.refl _))))))))))))))))
    all_goals simp [step,program,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,writeNat,next,evalNat,h.pc,h.index,h.geometry.ellValue,h.geometry.length,h.geometry.axes,h.geometry.digits,h.geometry.one,h.geometry.four,h.axis,h.digit,hqr,har,hbr,hL.ne',Nat.mul_comm,Nat.add_assoc]
  by_cases hd:d+1<q
  · have tail:Runs program n x (carry15 ell L i q wa wb d s) 3 (carrySuccess ell L i q wa wb d s):=by
      refine .next (u:=setPC (carry15 ell L i q wa wb d s) 42) ?_
        (.next (u:=store (setPC (carry15 ell L i q wa wb d s) 42) (digitBase ell+i) (d+1)) ?_
          (.next ?_ (.refl _)))
      all_goals simp [step,program,carrySuccess,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,hd]
    simpa only [hd,ite_true,carry] using stem.trans tail
  · have tail:Runs program n x (carry15 ell L i q wa wb d s) 4 (carryWrap ell L i q wa wb d s):=by
      refine .next (u:=setPC (carry15 ell L i q wa wb d s) 44) ?_
        (.next (u:=store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0) ?_
          (.next (u:=writeNat (store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0) 57 (i+1)) ?_
            (.next ?_ (.refl _))))
      all_goals simp [step,program,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,evalNat,hd,h.index,h.geometry.one,h.geometry.zero]
    simpa only [hd,ite_false,carry] using stem.trans tail


theorem store_bound (B : ℕ) (s : State) (address value : ℕ)
    (hs:WordBound B s) (hp:s.pc+1≤B) (ha:address≤B) (hv:value≤B) :
    WordBound B (store s address value) :=
  UniformCRTHeaderMachine.stored_bound B s address value hs hp ha hv

theorem emit_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State) (hpc:s.pc=19)
    (h1:s.natReg 64=1) (hB:48≤B) (hs:WordBound B s)
    (hA:s.natReg 52+s.natReg 54≤B) (hD:s.natReg 53+s.natReg 54≤B)
    (hO:s.natReg 54+1≤B) : BoundedRuns program n x B s 6 (emit s) := by
  have b1:WordBound B (emit1 s):=writeNat_bound B s 68 _ hs (by rw [hpc];omega) hA
  have b2:WordBound B (emit2 s):=store_bound B (emit1 s) _ _ b1
    (by simp [emit1,writeNat,next,hpc];omega) hA (hs.2.1 _)
  have b3:WordBound B (emit3 s):=writeNat_bound B (emit2 s) 68 _ b2
    (by simp [emit2,emit1,store,writeNat,next,hpc];omega) hD
  have b4:WordBound B (emit4 s):=store_bound B (emit3 s) _ _ b3
    (by simp [emit3,emit2,emit1,store,writeNat,next,hpc];omega) hD (hs.2.1 _)
  have b5:WordBound B (emit5 s):=writeNat_bound B (emit4 s) 54 _ b4
    (by simp [emit4,emit3,emit2,emit1,store,writeNat,next,hpc];omega) hO
  have b6:WordBound B (emit s):=writeNat_bound B (emit5 s) 57 _ b5
    (by simp [emit5,emit4,emit3,emit2,emit1,store,writeNat,next,hpc];omega) (by omega)
  refine .next hs (u:=emit1 s) ?_ (.next b1 (u:=emit2 s) ?_ (.next b2 (u:=emit3 s) ?_
    (.next b3 (u:=emit4 s) ?_ (.next b4 (u:=emit5 s) ?_ (.next b5 (u:=emit s) ?_ (.refl b6))))))
  all_goals simp [step,program,emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next,hpc,h1,evalNat]

structure CarryBounds (B ell i q wa wb d : ℕ) (s : State) : Prop where
  digitAddress : digitBase ell+i≤B
  fourIndex : 4*i≤B
  crtAddress : ell+4*i+3≤B
  radix : q≤B
  alphaWeight : wa≤B
  betaWeight : wb≤B
  alphaSum : s.natReg 55+wa≤B
  betaSum : s.natReg 56+wb≤B
  nextDigit : d+1≤B
  nextAxis : i+1≤B

theorem carry_bounded (n B : ℕ) (x : Fin n→ℂ) (ell L i q wa wb d : ℕ) (s : State)
    (h:CarryReady ell L i q wa wb d s) (hL:0<L) (hB:48≤B)
    (hs:WordBound B s) (hb:CarryBounds B ell i q wa wb d s) :
    BoundedRuns program n x B s (if d+1<q then 19 else 20) (carry ell L i q wa wb d s) := by
  have hqr:s.natHeap (ell+i*4)=some q:=by simpa [Nat.mul_comm] using h.radix
  have har:s.natHeap (ell+(i*4+3))=some wa:=by simpa [Nat.mul_comm,Nat.add_assoc] using h.alphaWeight
  have hbr:s.natHeap (ell+(i*4+1))=some wb:=by simpa [Nat.mul_comm,Nat.add_assoc] using h.betaWeight
  have b0:WordBound B (carry0 s):=changePC_bound B s 26 hs (by omega)
  have b1:WordBound B (carry1 ell L i q wa wb d s):=writeNat_bound B (carry0 s) 58 (digitBase ell+i) b0
    (by simp [carry0,setPC];omega) (hb.digitAddress)
  have b2:WordBound B (carry2 ell L i q wa wb d s):=writeNat_bound B (carry1 ell L i q wa wb d s) 59 (d) b1
    (by simp [carry0, setPC, carry1,writeNat,next];omega) (by have h:=hb.nextDigit;omega)
  have b3:WordBound B (carry3 ell L i q wa wb d s):=writeNat_bound B (carry2 ell L i q wa wb d s) 60 (4*i) b2
    (by simp [carry0, setPC, carry1, carry2,writeNat,next];omega) (hb.fourIndex)
  have b4:WordBound B (carry4 ell L i q wa wb d s):=writeNat_bound B (carry3 ell L i q wa wb d s) 60 (ell+4*i) b3
    (by simp [carry0, setPC, carry1, carry2, carry3,writeNat,next];omega) (by have h:=hb.crtAddress;omega)
  have b5:WordBound B (carry5 ell L i q wa wb d s):=writeNat_bound B (carry4 ell L i q wa wb d s) 61 (q) b4
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4,writeNat,next];omega) (hb.radix)
  have b6:WordBound B (carry6 ell L i q wa wb d s):=writeNat_bound B (carry5 ell L i q wa wb d s) 60 (ell+4*i+1) b5
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5,writeNat,next];omega) (by have h:=hb.crtAddress;omega)
  have b7:WordBound B (carry7 ell L i q wa wb d s):=writeNat_bound B (carry6 ell L i q wa wb d s) 63 (wb) b6
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6,writeNat,next];omega) (hb.betaWeight)
  have b8:WordBound B (carry8 ell L i q wa wb d s):=writeNat_bound B (carry7 ell L i q wa wb d s) 60 (ell+4*i+2) b7
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7,writeNat,next];omega) (by have h:=hb.crtAddress;omega)
  have b9:WordBound B (carry9 ell L i q wa wb d s):=writeNat_bound B (carry8 ell L i q wa wb d s) 60 (ell+4*i+3) b8
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8,writeNat,next];omega) (hb.crtAddress)
  have b10:WordBound B (carry10 ell L i q wa wb d s):=writeNat_bound B (carry9 ell L i q wa wb d s) 62 (wa) b9
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9,writeNat,next];omega) (hb.alphaWeight)
  have b11:WordBound B (carry11 ell L i q wa wb d s):=writeNat_bound B (carry10 ell L i q wa wb d s) 55 (s.natReg 55+wa) b10
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10,writeNat,next];omega) (hb.alphaSum)
  have b12:WordBound B (carry12 ell L i q wa wb d s):=writeNat_bound B (carry11 ell L i q wa wb d s) 55 ((s.natReg 55+wa)%L) b11
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11,writeNat,next];omega) ((Nat.mod_le _ _).trans hb.alphaSum)
  have b13:WordBound B (carry13 ell L i q wa wb d s):=writeNat_bound B (carry12 ell L i q wa wb d s) 56 (s.natReg 56+wb) b12
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12,writeNat,next];omega) (hb.betaSum)
  have b14:WordBound B (carry14 ell L i q wa wb d s):=writeNat_bound B (carry13 ell L i q wa wb d s) 56 ((s.natReg 56+wb)%L) b13
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13,writeNat,next];omega) ((Nat.mod_le _ _).trans hb.betaSum)
  have b15:WordBound B (carry15 ell L i q wa wb d s):=writeNat_bound B (carry14 ell L i q wa wb d s) 59 (d+1) b14
    (by simp [carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14,writeNat,next];omega) (hb.nextDigit)
  have stem:BoundedRuns program n x B s 16 (carry15 ell L i q wa wb d s):=by
    refine .next hs (u:=carry0 s) ?_ (.next b0 (u:=carry1 ell L i q wa wb d s) ?_ (.next b1 (u:=carry2 ell L i q wa wb d s) ?_ (.next b2 (u:=carry3 ell L i q wa wb d s) ?_ (.next b3 (u:=carry4 ell L i q wa wb d s) ?_ (.next b4 (u:=carry5 ell L i q wa wb d s) ?_ (.next b5 (u:=carry6 ell L i q wa wb d s) ?_ (.next b6 (u:=carry7 ell L i q wa wb d s) ?_ (.next b7 (u:=carry8 ell L i q wa wb d s) ?_ (.next b8 (u:=carry9 ell L i q wa wb d s) ?_ (.next b9 (u:=carry10 ell L i q wa wb d s) ?_ (.next b10 (u:=carry11 ell L i q wa wb d s) ?_ (.next b11 (u:=carry12 ell L i q wa wb d s) ?_ (.next b12 (u:=carry13 ell L i q wa wb d s) ?_ (.next b13 (u:=carry14 ell L i q wa wb d s) ?_ (.next b14 (u:=carry15 ell L i q wa wb d s) ?_ (.refl b15))))))))))))))))
    all_goals simp [step,program,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,writeNat,next,evalNat,h.pc,h.index,h.geometry.ellValue,h.geometry.length,h.geometry.axes,h.geometry.digits,h.geometry.one,h.geometry.four,h.axis,h.digit,hqr,har,hbr,hL.ne',Nat.mul_comm,Nat.add_assoc]
  by_cases hd:d+1<q
  · have b16:WordBound B (setPC (carry15 ell L i q wa wb d s) 42):=
      changePC_bound B _ 42 b15 (by omega)
    have b17:WordBound B (store (setPC (carry15 ell L i q wa wb d s) 42) (digitBase ell+i) (d+1)):=
      store_bound B _ _ _ b16 (by change 42+1≤B;omega) hb.digitAddress hb.nextDigit
    have b18:WordBound B (carrySuccess ell L i q wa wb d s):=
      changePC_bound B _ 19 b17 (by omega)
    have tail:BoundedRuns program n x B (carry15 ell L i q wa wb d s) 3 (carrySuccess ell L i q wa wb d s):=by
      refine .next b15 (u:=setPC (carry15 ell L i q wa wb d s) 42) ?_
        (.next b16 (u:=store (setPC (carry15 ell L i q wa wb d s) 42) (digitBase ell+i) (d+1)) ?_
          (.next b17 ?_ (.refl b18)))
      all_goals simp [step,program,carrySuccess,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,hd]
    simpa only [hd,ite_true,carry] using stem.trans tail
  · have b16:WordBound B (setPC (carry15 ell L i q wa wb d s) 44):=
      changePC_bound B _ 44 b15 (by omega)
    have b17:WordBound B (store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0):=
      store_bound B _ _ _ b16 (by change 44+1≤B;omega) hb.digitAddress (by omega)
    have b18:WordBound B (writeNat (store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0) 57 (i+1)):=
      writeNat_bound B _ _ _ b17 (by change 45+1≤B;omega) hb.nextAxis
    have b19:WordBound B (carryWrap ell L i q wa wb d s):=
      changePC_bound B _ 25 b18 (by omega)
    have tail:BoundedRuns program n x B (carry15 ell L i q wa wb d s) 4 (carryWrap ell L i q wa wb d s):=by
      refine .next b15 (u:=setPC (carry15 ell L i q wa wb d s) 44) ?_
        (.next b16 (u:=store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0) ?_
          (.next b17 (u:=writeNat (store (setPC (carry15 ell L i q wa wb d s) 44) (digitBase ell+i) 0) 57 (i+1)) ?_
            (.next b18 ?_ (.refl b19))))
      all_goals simp [step,program,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,evalNat,hd,h.index,h.geometry.one,h.geometry.zero]
    simpa only [hd,ite_false,carry] using stem.trans tail


theorem carry_heap (ell L i q wa wb d : ℕ) (s : State) :
    (carry ell L i q wa wb d s).natHeap=Function.update s.natHeap (digitBase ell+i)
      (some (if d+1<q then d+1 else 0)) := by
  unfold carry
  split_ifs <;> rfl

theorem carry_alpha (ell L i q wa wb d : ℕ) (s : State) :
    (carry ell L i q wa wb d s).natReg 55=(s.natReg 55+wa)%L := by
  by_cases hd:d+1<q
  all_goals simp [carry,hd,carrySuccess,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next]

theorem carry_beta (ell L i q wa wb d : ℕ) (s : State) :
    (carry ell L i q wa wb d s).natReg 56=(s.natReg 56+wb)%L := by
  by_cases hd:d+1<q
  all_goals simp [carry,hd,carrySuccess,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next]

theorem carry_control (ell L i q wa wb d : ℕ) (s : State) (hi:s.natReg 57=i) :
    (carry ell L i q wa wb d s).pc=(if d+1<q then 19 else 25) ∧
    (carry ell L i q wa wb d s).natReg 57=(if d+1<q then i else i+1) ∧
    (carry ell L i q wa wb d s).natReg 54=s.natReg 54 := by
  by_cases hd:d+1<q
  all_goals simp [carry,hd,carrySuccess,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,hi]

theorem carry_static (ell L i q wa wb d : ℕ) (s : State) (r : ℕ)
    (hr:r<55 ∨ 63<r) : (carry ell L i q wa wb d s).natReg r=s.natReg r := by
  have h55:r≠55:=by omega
  have h56:r≠56:=by omega
  have h57:r≠57:=by omega
  have h58:r≠58:=by omega
  have h59:r≠59:=by omega
  have h60:r≠60:=by omega
  have h61:r≠61:=by omega
  have h62:r≠62:=by omega
  have h63:r≠63:=by omega
  by_cases hd:d+1<q
  all_goals simp [carry,hd,carrySuccess,carryWrap,carry0, setPC, carry1, carry2, carry3, carry4, carry5, carry6, carry7, carry8, carry9, carry10, carry11, carry12, carry13, carry14, carry15,store,writeNat,next,h55,h56,h57,h58,h59,h60,h61,h62,h63]

theorem carry_geometry (ell L i q wa wb d : ℕ) (s : State) (hg:Geometry ell L s) :
    Geometry ell L (carry ell L i q wa wb d s) := by
  constructor <;> rw [carry_static ell L i q wa wb d s _ (by omega)]
  · exact hg.ellValue
  · exact hg.length
  · exact hg.axes
  · exact hg.digits
  · exact hg.alpha
  · exact hg.beta
  · exact hg.one
  · exact hg.zero
  · exact hg.four
  · exact hg.five

theorem carry_scalar_frame (ell L i q wa wb d : ℕ) (s : State) :
    (carry ell L i q wa wb d s).scalarReg=s.scalarReg ∧
    (carry ell L i q wa wb d s).scalarHeap=s.scalarHeap ∧
    (carry ell L i q wa wb d s).outputs=s.outputs ∧
    (carry ell L i q wa wb d s).rootOrders=s.rootOrders := by
  unfold carry
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem emit_geometry (ell L : ℕ) (s : State) (hg:Geometry ell L s) :
    Geometry ell L (emit s) := by
  constructor <;>
    simp [emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next,
      hg.ellValue,hg.length,hg.axes,hg.digits,hg.alpha,hg.beta,hg.one,hg.zero,hg.four,hg.five]

theorem emit_values (s : State) (hpc:s.pc=19) :
    (emit s).pc=25 ∧ (emit s).natReg 57=0 ∧ (emit s).natReg 54=s.natReg 54+1 ∧
    (emit s).natReg 55=s.natReg 55 ∧ (emit s).natReg 56=s.natReg 56 ∧
    (emit s).natHeap=Function.update
      (Function.update s.natHeap (s.natReg 52+s.natReg 54) (some (s.natReg 55)))
      (s.natReg 53+s.natReg 54) (some (s.natReg 56)) := by
  simp [emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next,hpc]

theorem carry_preserves_low_heap (ell L i q wa wb d : ℕ) (s : State)
    (address : ℕ) (ha:address<digitBase ell) :
    (carry ell L i q wa wb d s).natHeap address=s.natHeap address := by
  rw [carry_heap,Function.update_of_ne (by omega)]

theorem emit_preserves_low_heap (ell L : ℕ) (s : State) (hg:Geometry ell L s)
    (address : ℕ) (ha:address<alphaBase ell) :
    (emit s).natHeap address=s.natHeap address := by
  simp only [emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next]
  rw [Function.update_of_ne (by rw [hg.beta];unfold betaBase;omega),
    Function.update_of_ne (by rw [hg.alpha];omega)]

theorem crt_address_low (ell i field : ℕ) (hi:i<ell+1) (hf:field≤3) :
    UniformCRTHeaderMachine.tableAddress ell i field<digitBase ell := by
  unfold UniformCRTHeaderMachine.tableAddress digitBase
  omega

theorem actual_carry_ready (n i d : ℕ) (s : State)
    (hg:Geometry (UniformWorkingLength.axisCount n) (UniformWorkingLength.workingLength n) s)
    (hc:UniformCRTHeaderMachine.CRTTable n s)
    (hi:i<UniformWorkingLength.axisCount n+1) (hpc:s.pc=25) (hindex:s.natReg 57=i)
    (hd:s.natHeap (digitBase (UniformWorkingLength.axisCount n)+i)=some d) :
    CarryReady (UniformWorkingLength.axisCount n) (UniformWorkingLength.workingLength n) i
      (UniformSelectedCRT.radices n ⟨i,hi⟩)
      (UniformCRT.idempotent (UniformSelectedCRT.radices n) ⟨i,hi⟩)
      (UniformCRT.cofactor (UniformSelectedCRT.radices n) ⟨i,hi⟩) d s := by
  obtain ⟨hq,hb,_hinv,ha⟩:=hc ⟨i,hi⟩
  exact ⟨hpc,hg,hindex,hi,hd,hq,ha,hb⟩


theorem actual_carry_bounds {n : ℕ} (hn:0<n) (B i d : ℕ) (s : State)
    (hi:i<UniformWorkingLength.axisCount n+1)
    (hA:s.natReg 55<UniformWorkingLength.workingLength n)
    (hD:s.natReg 56<UniformWorkingLength.workingLength n)
    (hd:d<UniformSelectedCRT.radices n ⟨i,hi⟩)
    (hB:128+10*UniformWorkingLength.axisCount n+4*UniformWorkingLength.workingLength n≤B) :
    CarryBounds B (UniformWorkingLength.axisCount n) i
      (UniformSelectedCRT.radices n ⟨i,hi⟩)
      (UniformCRT.idempotent (UniformSelectedCRT.radices n) ⟨i,hi⟩)
      (UniformCRT.cofactor (UniformSelectedCRT.radices n) ⟨i,hi⟩) d s := by
  have hL:=UniformWorkingLength.workingLength_pos hn
  have hq:UniformSelectedCRT.radices n ⟨i,hi⟩≤UniformWorkingLength.workingLength n:=by
    rw [←UniformSelectedCRT.radices_product] at hL ⊢
    exact Nat.le_of_dvd hL (Finset.dvd_prod_of_mem _ (Finset.mem_univ _))
  have ha:UniformCRT.idempotent (UniformSelectedCRT.radices n) ⟨i,hi⟩<
      UniformWorkingLength.workingLength n:=by
    simpa only [UniformSelectedCRT.radices_product] using UniformCRT.idempotent_lt
      (UniformSelectedCRT.radices n) (UniformSelectedCRT.radix_pos n) ⟨i,hi⟩
  have hb:UniformCRT.cofactor (UniformSelectedCRT.radices n) ⟨i,hi⟩≤
      UniformWorkingLength.workingLength n:=by
    rw [UniformCRT.cofactor_eq_div _ _ (UniformSelectedCRT.radix_pos n ⟨i,hi⟩),UniformSelectedCRT.radices_product]
    exact Nat.div_le_self _ _
  constructor <;> (try dsimp only [digitBase]) <;> omega

theorem emit_static (s : State) (r : ℕ) (h54:r≠54) (h57:r≠57) (h68:r≠68) :
    (emit s).natReg r=s.natReg r := by
  simp [emit,emit1,emit2,emit3,emit4,emit5,store,writeNat,next,h54,h57,h68]

theorem emit_scalar_frame (s : State) :
    (emit s).scalarReg=s.scalarReg ∧ (emit s).scalarHeap=s.scalarHeap ∧
    (emit s).outputs=s.outputs ∧ (emit s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl,rfl⟩

/-- This expression charges initialization, emissions and at most20 instructions
per carry. The complete-cycle execution/count connection is a separate proof. -/
def cycleBudget (ell : ℕ) (rs : List ℕ) : ℕ :=
  14+5*(ell+1)+6*rs.prod+20*carryVisits rs+2

theorem selected_cycleBudget_bound (n : ℕ) :
    cycleBudget (UniformWorkingLength.axisCount n) (selectedRadices n)<
      46*UniformWorkingLength.workingLength n+5*UniformWorkingLength.axisCount n+21 := by
  have h:=selected_carryVisits_bound n
  unfold cycleBudget
  rw [selected_radices_product]
  omega

def boot1 (_ell _L : ℕ) (s : State) : State := writeNat (s) 64 (1)
def boot2 (ell L : ℕ) (s : State) : State := writeNat (boot1 ell L s) 65 (0)
def boot3 (ell L : ℕ) (s : State) : State := writeNat (boot2 ell L s) 66 (4)
def boot4 (ell L : ℕ) (s : State) : State := writeNat (boot3 ell L s) 67 (5)
def boot5 (ell L : ℕ) (s : State) : State := writeNat (boot4 ell L s) 50 (ell+1)
def boot6 (ell L : ℕ) (s : State) : State := writeNat (boot5 ell L s) 51 (5*ell)
def boot7 (ell L : ℕ) (s : State) : State := writeNat (boot6 ell L s) 51 (digitBase ell)
def boot8 (ell L : ℕ) (s : State) : State := writeNat (boot7 ell L s) 52 (alphaBase ell)
def boot9 (ell L : ℕ) (s : State) : State := writeNat (boot8 ell L s) 53 (betaBase ell L)
def boot10 (ell L : ℕ) (s : State) : State := writeNat (boot9 ell L s) 54 (0)
def boot11 (ell L : ℕ) (s : State) : State := writeNat (boot10 ell L s) 55 (0)
def boot12 (ell L : ℕ) (s : State) : State := writeNat (boot11 ell L s) 56 (0)
def boot13 (ell L : ℕ) (s : State) : State := writeNat (boot12 ell L s) 57 (0)

theorem bootstrap_bounded (n B ell L : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hell:s.natReg 10=ell) (hL:s.natReg 17=L)
    (hB:128+10*ell+4*L≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 13 (boot13 ell L s) := by
  have b1:WordBound B (boot1 ell L s):=writeNat_bound B (s) 64 (1) hs
    (by omega) (by omega)
  have b2:WordBound B (boot2 ell L s):=writeNat_bound B (boot1 ell L s) 65 (0) b1
    (by simp [writeNat,next,hpc,boot1];omega) (by omega)
  have b3:WordBound B (boot3 ell L s):=writeNat_bound B (boot2 ell L s) 66 (4) b2
    (by simp [writeNat,next,hpc,boot1, boot2];omega) (by omega)
  have b4:WordBound B (boot4 ell L s):=writeNat_bound B (boot3 ell L s) 67 (5) b3
    (by simp [writeNat,next,hpc,boot1, boot2, boot3];omega) (by omega)
  have b5:WordBound B (boot5 ell L s):=writeNat_bound B (boot4 ell L s) 50 (ell+1) b4
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4];omega) (by omega)
  have b6:WordBound B (boot6 ell L s):=writeNat_bound B (boot5 ell L s) 51 (5*ell) b5
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5];omega) (by omega)
  have b7:WordBound B (boot7 ell L s):=writeNat_bound B (boot6 ell L s) 51 (digitBase ell) b6
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6];omega) (by dsimp only [digitBase,alphaBase,betaBase];omega)
  have b8:WordBound B (boot8 ell L s):=writeNat_bound B (boot7 ell L s) 52 (alphaBase ell) b7
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7];omega) (by dsimp only [digitBase,alphaBase,betaBase];omega)
  have b9:WordBound B (boot9 ell L s):=writeNat_bound B (boot8 ell L s) 53 (betaBase ell L) b8
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8];omega) (by dsimp only [digitBase,alphaBase,betaBase];omega)
  have b10:WordBound B (boot10 ell L s):=writeNat_bound B (boot9 ell L s) 54 (0) b9
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9];omega) (by omega)
  have b11:WordBound B (boot11 ell L s):=writeNat_bound B (boot10 ell L s) 55 (0) b10
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10];omega) (by omega)
  have b12:WordBound B (boot12 ell L s):=writeNat_bound B (boot11 ell L s) 56 (0) b11
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11];omega) (by omega)
  have b13:WordBound B (boot13 ell L s):=writeNat_bound B (boot12 ell L s) 57 (0) b12
    (by simp [writeNat,next,hpc,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12];omega) (by omega)
  refine .next hs (u:=boot1 ell L s) ?_ (.next b1 (u:=boot2 ell L s) ?_ (.next b2 (u:=boot3 ell L s) ?_ (.next b3 (u:=boot4 ell L s) ?_ (.next b4 (u:=boot5 ell L s) ?_ (.next b5 (u:=boot6 ell L s) ?_ (.next b6 (u:=boot7 ell L s) ?_ (.next b7 (u:=boot8 ell L s) ?_ (.next b8 (u:=boot9 ell L s) ?_ (.next b9 (u:=boot10 ell L s) ?_ (.next b10 (u:=boot11 ell L s) ?_ (.next b11 (u:=boot12 ell L s) ?_ (.next b12 (u:=boot13 ell L s) ?_ (.refl b13)))))))))))))
  all_goals simp [step,program,boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next,evalNat,hpc,hell,hL,digitBase,alphaBase,betaBase,Nat.mul_comm,Nat.add_assoc]

theorem bootstrap_geometry (ell L : ℕ) (s : State) (hell:s.natReg 10=ell) (hL:s.natReg 17=L) :
    Geometry ell L (boot13 ell L s) := by
  constructor <;> simp [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next,hell,hL]

def zero1 (_ell _j : ℕ) (s : State) : State := setPC s 14
def zero2 (ell j : ℕ) (s : State) : State := writeNat (zero1 ell j s) 58 (digitBase ell+j)
def zero3 (ell j : ℕ) (s : State) : State := store (zero2 ell j s) (digitBase ell+j) 0
def zero4 (ell j : ℕ) (s : State) : State := writeNat (zero3 ell j s) 57 (j+1)
def zero (ell j : ℕ) (s : State) : State := setPC (zero4 ell j s) 13

theorem zero_bounded (n B ell L j : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=13) (hg:Geometry ell L s) (hj:s.natReg 57=j) (hl:j<ell+1)
    (hB:128+10*ell+4*L≤B) (hs:WordBound B s) :
    BoundedRuns program n x B s 5 (zero ell j s) := by
  have b1:WordBound B (zero1 ell j s):=changePC_bound B s 14 hs (by omega)
  have b2:WordBound B (zero2 ell j s):=writeNat_bound B _ 58 _ b1 (by change 14+1≤B;omega)
    (by unfold digitBase;omega)
  have b3:WordBound B (zero3 ell j s):=store_bound B _ _ _ b2 (by change 15+1≤B;omega)
    (by unfold digitBase;omega) (by omega)
  have b4:WordBound B (zero4 ell j s):=writeNat_bound B _ 57 _ b3 (by change 16+1≤B;omega) (by omega)
  have b5:WordBound B (zero ell j s):=changePC_bound B _ 13 b4 (by omega)
  refine .next hs (u:=zero1 ell j s) ?_ (.next b1 (u:=zero2 ell j s) ?_
    (.next b2 (u:=zero3 ell j s) ?_ (.next b3 (u:=zero4 ell j s) ?_ (.next b4 ?_ (.refl b5)))))
  all_goals simp [step,program,zero,zero1,zero2,zero3,zero4,setPC,store,writeNat,next,evalNat,
    hpc,hg.axes,hg.digits,hg.one,hg.zero,hj,hl]

theorem zero_geometry (ell L j : ℕ) (s : State) (hg:Geometry ell L s) :
    Geometry ell L (zero ell j s) := by
  constructor <;> simp [zero,zero1,zero2,zero3,zero4,setPC,store,writeNat,next,
    hg.ellValue,hg.length,hg.axes,hg.digits,hg.alpha,hg.beta,hg.one,hg.zero,hg.four,hg.five]

theorem zero_values (ell j : ℕ) (s : State) :
    (zero ell j s).pc=13 ∧ (zero ell j s).natReg 57=j+1 ∧
    (zero ell j s).natHeap=Function.update s.natHeap (digitBase ell+j) (some 0) := by
  simp [zero,zero1,zero2,zero3,zero4,setPC,store,writeNat,next]

def DigitsZero (ell j : ℕ) (s : State) : Prop :=
  ∀ i,i<j → s.natHeap (digitBase ell+i)=some 0

theorem zero_next (ell j : ℕ) (s : State) (h:DigitsZero ell j s) :
    DigitsZero ell (j+1) (zero ell j s) := by
  intro i hi
  rw [(zero_values ell j s).2.2]
  by_cases he:i=j
  · subst i;simp
  · rw [Function.update_of_ne (by omega)]
    exact h i (by omega)

theorem zero_loop (n B ell L j fuel : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=13) (hg:Geometry ell L s) (hj:s.natReg 57=j)
    (hf:j+fuel=ell+1) (hz:DigitsZero ell j s)
    (hB:128+10*ell+4*L≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*fuel+1) u ∧ Geometry ell L u ∧
    u.pc=19 ∧ DigitsZero ell (ell+1) u ∧ u.natReg 57=ell+1 := by
  induction fuel generalizing j s with
  | zero =>
      have he:j=ell+1:=by omega
      refine ⟨setPC s 19,.next hs ?_ (.refl (changePC_bound B s 19 hs (by omega))),?_,rfl,?_,?_⟩
      · simp [step,program,hpc,hg.axes,hj,he,setPC]
      · exact ⟨hg.ellValue,hg.length,hg.axes,hg.digits,hg.alpha,hg.beta,hg.one,hg.zero,hg.four,hg.five⟩
      · simpa only [he,DigitsZero,setPC] using hz
      · exact hj.trans he
  | succ fuel ih =>
      have hjlt:j<ell+1:=by omega
      have hr:=zero_bounded n B ell L j x s hpc hg hj hjlt hB hs
      obtain ⟨u,hu,hgeom,hup,hzeros,hindex⟩:=ih (j+1) (zero ell j s)
        (zero_values ell j s).1 (zero_geometry ell L j s hg) (zero_values ell j s).2.1
        (by omega) (zero_next ell j s hz) hr.final_bound
      refine ⟨u,?_,hgeom,hup,hzeros,hindex⟩
      simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr.trans hu


theorem halt_bounded (n B ell L : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=25) (hg:Geometry ell L s) (hj:s.natReg 57=ell+1)
    (hB:48≤B) (hs:WordBound B s) :
    BoundedExecution program n x B s 2 (setPC s 47) := by
  refine .next hs ?_ (.halt (changePC_bound B s 47 hs (by omega)) ?_)
  · simp [step,program,hpc,hg.axes,hj,setPC]
  · simp [step,program,setPC]


def Frame (ell : ℕ) (s u : State) : Prop :=
  u.scalarReg=s.scalarReg ∧ u.scalarHeap=s.scalarHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀r,r<50 → u.natReg r=s.natReg r) ∧ ∀address,address<digitBase ell → u.natHeap address=s.natHeap address

theorem frame_refl (ell : ℕ) (s : State) : Frame ell s s :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem Frame.trans {ell : ℕ} {s u v : State} (h:Frame ell s u) (h':Frame ell u v) : Frame ell s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun r hr => (h'.2.2.2.2.1 r hr).trans (h.2.2.2.2.1 r hr),
    fun a ha => (h'.2.2.2.2.2 a ha).trans (h.2.2.2.2.2 a ha)⟩

theorem zero_static (ell j : ℕ) (s : State) (r : ℕ) (h57:r≠57) (h58:r≠58) :
    (zero ell j s).natReg r=s.natReg r := by
  simp [zero,zero1,zero2,zero3,zero4,setPC,store,writeNat,next,h57,h58]

theorem zero_frame (ell j : ℕ) (s : State) : Frame ell s (zero ell j s) := by
  refine ⟨rfl,rfl,rfl,rfl,fun r hr => zero_static ell j s r (by omega) (by omega),?_⟩
  intro a ha
  rw [(zero_values ell j s).2.2,Function.update_of_ne (by omega)]

theorem bootstrap_frame (ell L : ℕ) (s : State) : Frame ell s (boot13 ell L s) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,fun _ _ => rfl⟩
  intro r hr
  have h50:r≠50:=by omega
  have h51:r≠51:=by omega
  have h52:r≠52:=by omega
  have h53:r≠53:=by omega
  have h54:r≠54:=by omega
  have h55:r≠55:=by omega
  have h56:r≠56:=by omega
  have h57:r≠57:=by omega
  have h64:r≠64:=by omega
  have h65:r≠65:=by omega
  have h66:r≠66:=by omega
  have h67:r≠67:=by omega
  simp [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next,h50,h51,h52,h53,h54,h55,h56,h57,h64,h65,h66,h67]

theorem zero_loop_framed (n B ell L j fuel : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=13) (hg:Geometry ell L s) (hj:s.natReg 57=j)
    (hf:j+fuel=ell+1) (hz:DigitsZero ell j s)
    (hB:128+10*ell+4*L≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (5*fuel+1) u ∧ Geometry ell L u ∧
    u.pc=19 ∧ DigitsZero ell (ell+1) u ∧ Frame ell s u ∧
    ∀r,r≠57 → r≠58 → u.natReg r=s.natReg r := by
  induction fuel generalizing j s with
  | zero =>
      have he:j=ell+1:=by omega
      refine ⟨setPC s 19,.next hs ?_ (.refl (changePC_bound B s 19 hs (by omega))),?_,rfl,?_,?_,fun _ _ _ => rfl⟩
      · simp [step,program,hpc,hg.axes,hj,he,setPC]
      · exact ⟨hg.ellValue,hg.length,hg.axes,hg.digits,hg.alpha,hg.beta,hg.one,hg.zero,hg.four,hg.five⟩
      · simpa only [he,DigitsZero,setPC] using hz
      · exact frame_refl ell s
  | succ fuel ih =>
      have hjlt:j<ell+1:=by omega
      have hr:=zero_bounded n B ell L j x s hpc hg hj hjlt hB hs
      obtain ⟨u,hu,hgeom,hup,hzeros,hframe,hstatic⟩:=ih (j+1) (zero ell j s)
        (zero_values ell j s).1 (zero_geometry ell L j s hg) (zero_values ell j s).2.1
        (by omega) (zero_next ell j s hz) hr.final_bound
      refine ⟨u,?_,hgeom,hup,hzeros,(zero_frame ell j s).trans hframe,?_⟩
      · simpa only [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr.trans hu
      · intro r h57 h58
        exact (hstatic r h57 h58).trans (zero_static ell j s r h57 h58)

theorem initialize_bounded (n B ell L : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hell:s.natReg 10=ell) (hL:s.natReg 17=L)
    (hB:128+10*ell+4*L≤B) (hs:WordBound B s) : ∃u,
    BoundedRuns program n x B s (14+5*(ell+1)) u ∧ Geometry ell L u ∧
    u.pc=19 ∧ DigitsZero ell (ell+1) u ∧ Frame ell s u ∧
    u.natReg 54=0 ∧ u.natReg 55=0 ∧ u.natReg 56=0 := by
  have hb:=bootstrap_bounded n B ell L x s hpc hell hL hB hs
  have hg:=bootstrap_geometry ell L s hell hL
  obtain ⟨u,hu,hgeom,hup,hzeros,hframe,hstatic⟩:=zero_loop_framed n B ell L 0 (ell+1) x
    (boot13 ell L s) (by simp [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next,hpc]) hg
    (by simp [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next]) (by omega) (by intro i hi;omega) hB hb.final_bound
  refine ⟨u,?_,hgeom,hup,hzeros,(bootstrap_frame ell L s).trans hframe,?_,?_,?_⟩
  · convert hb.trans hu using 1;omega
  · simpa [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next] using hstatic 54 (by decide) (by decide)
  · simpa [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next] using hstatic 55 (by decide) (by decide)
  · simpa [boot1, boot2, boot3, boot4, boot5, boot6, boot7, boot8, boot9, boot10, boot11, boot12, boot13,writeNat,next] using hstatic 56 (by decide) (by decide)


theorem Frame.crt {n : ℕ} {s u : State}
    (hf:Frame (UniformWorkingLength.axisCount n) s u)
    (hc:UniformCRTHeaderMachine.CRTTable n s) : UniformCRTHeaderMachine.CRTTable n u := by
  intro i
  obtain ⟨hq,hb,hinv,ha⟩:=hc i
  refine ⟨?_,?_,?_,?_⟩
  · exact (hf.2.2.2.2.2 _ (crt_address_low _ _ _ i.isLt (by decide))).trans hq
  · exact (hf.2.2.2.2.2 _ (crt_address_low _ _ _ i.isLt (by decide))).trans hb
  · exact (hf.2.2.2.2.2 _ (crt_address_low _ _ _ i.isLt (by decide))).trans hinv
  · exact (hf.2.2.2.2.2 _ (crt_address_low _ _ _ i.isLt (by decide))).trans ha

theorem Frame.header {n : ℕ} {s u : State}
    (hf:Frame (UniformWorkingLength.axisCount n) s u)
    (hh:UniformCRTHeaderMachine.Header n s) : UniformCRTHeaderMachine.Header n u := by
  obtain ⟨h0,h10,h11,h16,h17,h18,hp⟩:=hh
  refine ⟨(hf.2.2.2.2.1 0 (by decide)).trans h0,
    (hf.2.2.2.2.1 10 (by decide)).trans h10,
    (hf.2.2.2.2.1 11 (by decide)).trans h11,
    (hf.2.2.2.2.1 16 (by decide)).trans h16,
    (hf.2.2.2.2.1 17 (by decide)).trans h17,
    (hf.2.2.2.2.1 18 (by decide)).trans h18,?_⟩
  intro i hi
  exact (hf.2.2.2.2.2 i (by unfold digitBase;omega)).trans (hp i hi)

theorem post_header_initialize (n B : ℕ) (x : Fin n→ℂ) (s : State)
    (hpc:s.pc=0) (hh:UniformCRTHeaderMachine.Header n s)
    (hc:UniformCRTHeaderMachine.CRTTable n s) (hs:WordBound B s)
    (hB:128+10*UniformWorkingLength.axisCount n+4*UniformWorkingLength.workingLength n≤B) : ∃u,
    BoundedRuns program n x B s (14+5*(UniformWorkingLength.axisCount n+1)) u ∧
    Geometry (UniformWorkingLength.axisCount n) (UniformWorkingLength.workingLength n) u ∧
    u.pc=19 ∧ DigitsZero (UniformWorkingLength.axisCount n) (UniformWorkingLength.axisCount n+1) u ∧
    UniformCRTHeaderMachine.Header n u ∧ UniformCRTHeaderMachine.CRTTable n u ∧
    Frame (UniformWorkingLength.axisCount n) s u ∧
    u.natReg 54=0 ∧ u.natReg 55=0 ∧ u.natReg 56=0 := by
  obtain ⟨u,hu,hgeom,hup,hzero,hframe,h54,h55,h56⟩:=initialize_bounded n B
    (UniformWorkingLength.axisCount n) (UniformWorkingLength.workingLength n) x s hpc
    hh.2.1 hh.2.2.2.2.1 hB hs
  exact ⟨u,hu,hgeom,hup,hzero,hframe.header hh,hframe.crt hc,hframe,h54,h55,h56⟩

end
end ExactFourierCircuits.UniformCRTTraversalMachine
