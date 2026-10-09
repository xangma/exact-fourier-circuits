import DFTModelCRTMetadataInverse

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCRTMetadata
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Actual working-length ABI: ell, volume, binary factor, prime table. -/
abbrev Input := p w (p w (p w (a w)))
abbrev Cell := p Input w
abbrev Inverted := p (p w w) w

def axisCount : Prog false Input w := nat .add (.atom .fst) (.atom (.lit 1))
def workingLength : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def oddCount : Prog false Cell w := .comp (.atom .fst) (.atom .fst)
def binary : Prog false Cell w :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .fst)))
def primes : Prog false Cell (a w) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))
def prime : Prog false Cell w := .comp (.fork primes (.atom .snd)) (.atom .look)
def radix : Prog false Cell w :=
  .ifz (nat .lt (.atom .snd) oddCount) binary prime
def cofactor : Prog false Cell w :=
  nat .div (.comp (.atom .fst) workingLength) radix

def finishRow : Prog false Inverted DFTModelCRT.Row :=
  .fork (.comp (.atom .fst) (.atom .fst))
    (.fork (nat .mul (.comp (.atom .fst) (.atom .snd)) (.atom .snd))
      (.comp (.atom .fst) (.atom .snd)))

def makeRow : Prog false (p w w) DFTModelCRT.Row :=
  .comp (.fork (.atom .id) (.comp (.fork (.atom .snd) (.atom .fst)) inverse)) finishRow

/-- A row is built by charged division, candidate search and multiplication. -/
def cell : Prog false Cell DFTModelCRT.Row := .comp (.fork radix cofactor) makeRow
def metadata : Prog false Input (a DFTModelCRT.Row) := .tab axisCount cell

def radixValue (x : Input.T) (i : ℕ) : ℕ :=
  if i<x.1 then x.2.2.2.look i 0 else x.2.2.1

theorem axisCount_run (x : Input.T) : Code.run axisCount () x=⟨x.1+1,5,x.1+1,True⟩ := by
  simp [axisCount,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem workingLength_run (x : Input.T) : Code.run workingLength () x=⟨x.2.1,3,0,True⟩ := by
  simp [workingLength,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem radix_run (x : Input.T) (i : ℕ) :
    Code.run radix () (x,i)=⟨radixValue x i,if i<x.1 then 19 else 15,
      if i<x.1 then 1 else 0,True⟩ := by
  by_cases hi : i<x.1 <;>
    simp [radix,nat,oddCount,binary,prime,primes,radixValue,hi,
      Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem cofactor_run (x : Input.T) (i : ℕ) :
    Code.run cofactor () (x,i)=⟨x.2.1/radixValue x i,
      (if i<x.1 then 19 else 15)+8,
      max (if i<x.1 then 1 else 0) (x.2.1/radixValue x i),True⟩ := by
  simp only [cofactor,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
  rw [radix_run,workingLength_run]
  simp only [max_zero,zero_max,true_and]
  congr 1
  omega

theorem finishRow_run (q a d : ℕ) :
    Code.run finishRow () ((q,a),d)=⟨(q,(a*d,a)),15,a*d,True⟩ := by
  simp [finishRow,nat,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem makeRow_value (q a : ℕ) :
    (Code.run makeRow () (q,a)).val=(q,(a*(Code.run inverse () (a,q)).val,a)) := by
  simp only [makeRow,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [finishRow_run]

theorem makeRow_work (q a : ℕ) :
    (Code.run makeRow () (q,a)).work=46*q+26 := by
  simp only [makeRow,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [finishRow_run,inverse_work]
  dsimp only [Bill.val,Bill.work]
  omega

theorem makeRow_peak (q a : ℕ) :
    (Code.run makeRow () (q,a)).peak≤ max q (a*q+1) := by
  have ip := inverse_peak a q
  have value := inverse_le a q
  have product := Nat.mul_le_mul_left a value
  simp only [makeRow,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [finishRow_run]
  simp only [max_le_iff]
  omega

theorem makeRow_valid (q a : ℕ) : (Code.run makeRow () (q,a)).valid := by
  simp only [makeRow,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [finishRow_run]
  simpa only [Bill.valid,and_true,true_and] using inverse_valid a q

theorem cell_value (x : Input.T) (i : ℕ) :
    (Code.run cell () (x,i)).val=
      (radixValue x i,
        ((x.2.1/radixValue x i)*(Code.run inverse () (x.2.1/radixValue x i,radixValue x i)).val,
          x.2.1/radixValue x i)) := by
  simp only [cell,Code.run,Bill.pass,Bill.pay,Bill.one]
  rw [radix_run,cofactor_run]
  exact makeRow_value _ _

theorem cell_work (x : Input.T) (i : ℕ) :
    (Code.run cell () (x,i)).work≤46*radixValue x i+74 := by
  simp only [cell,Code.run,Bill.pass,Bill.pay,Bill.one]
  rw [radix_run,cofactor_run,makeRow_work]
  dsimp only [Bill.val,Bill.work]
  split_ifs <;> omega

theorem cell_peak (x : Input.T) (i V : ℕ) (positive : 0<V)
    (volume : x.2.1=V) (radixBound : radixValue x i≤V) :
    (Code.run cell () (x,i)).peak≤(V+1)^2 := by
  have cb : V/radixValue x i≤V := Nat.div_le_self _ _
  have product : V/radixValue x i*radixValue x i≤V*V := Nat.mul_le_mul cb radixBound
  have mp := makeRow_peak (radixValue x i) (V/radixValue x i)
  have vv : V≤(V+1)^2 := by nlinarith
  have polynomial : V*V+1≤(V+1)^2 := by nlinarith
  simp only [cell,Code.run,Bill.pass,Bill.pay,Bill.one]
  rw [radix_run,cofactor_run,volume]
  split_ifs <;> simp only [max_le_iff] at mp ⊢ <;> omega

theorem cell_valid (x : Input.T) (i : ℕ) : (Code.run cell () (x,i)).valid := by
  simp only [cell,Code.run,Bill.pass,Bill.pay,Bill.one]
  rw [radix_run,cofactor_run]
  simpa only [Bill.valid,Bill.val,and_true,true_and] using makeRow_valid _ _

theorem metadata_value (x : Input.T) :
    (Code.run metadata () x).val=Tape.tab (x.1+1) (fun i => (Code.run cell () (x,i)).val) := by
  change (Bill.tab (Code.run axisCount () x).val DFTModelCRT.Row.blank
    (fun i => Code.run cell () (x,i))).val=_
  rw [axisCount_run,ModelEquivalenceInterpreter.tab_value]

theorem metadata_work (x : Input.T) :
    (Code.run metadata () x).work≤78*(x.1+1)+46*(∑i ∈ Finset.range (x.1+1),radixValue x i)+8 := by
  change (Code.run axisCount () x).work+
    (Bill.tab (Code.run axisCount () x).val DFTModelCRT.Row.blank
      (fun i => Code.run cell () (x,i))).work+1≤_
  rw [axisCount_run,ModelEquivalenceInterpreter.tab_work]
  change 5+(2+4*(x.1+1)+∑i ∈ Finset.range (x.1+1),(Code.run cell () (x,i)).work)+1≤_
  have h := Finset.sum_le_sum (s:=Finset.range (x.1+1)) (fun i _ => cell_work x i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,
    ← Finset.mul_sum] at h
  calc
    5+(2+4*(x.1+1)+∑i ∈ Finset.range (x.1+1),(Code.run cell () (x,i)).work)+1
      ≤5+(2+4*(x.1+1)+(46*(∑i ∈ Finset.range (x.1+1),radixValue x i)+(x.1+1)*74))+1 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_left h (2+4*(x.1+1))) 5) 1
    _=78*(x.1+1)+46*(∑i ∈ Finset.range (x.1+1),radixValue x i)+8 := by
      ring

theorem metadata_peak (x : Input.T) (V : ℕ) (positive : 0<V)
    (volume : x.2.1=V) (countBound : x.1+1≤V)
    (radixBound : ∀i<x.1+1,radixValue x i≤V) :
    (Code.run metadata () x).peak≤(V+1)^2 := by
  change max (max (Code.run axisCount () x).peak
    (Bill.tab (Code.run axisCount () x).val DFTModelCRT.Row.blank
      (fun i => Code.run cell () (x,i))).peak) 0≤_
  rw [axisCount_run,ModelEquivalenceInterpreter.tab_peak]
  dsimp only [Bill.peak,Bill.val]
  have vv : V≤(V+1)^2 := by nlinarith
  refine max_le (max_le (countBound.trans vv) (max_le (countBound.trans vv) ?_)) (by omega)
  apply Finset.sup_le
  intro i hi
  exact cell_peak x i V positive volume (radixBound i (Finset.mem_range.mp hi))

theorem metadata_valid (x : Input.T) : (Code.run metadata () x).valid := by
  change (Code.run axisCount () x).valid ∧
    (Bill.tab (Code.run axisCount () x).val DFTModelCRT.Row.blank
      (fun i => Code.run cell () (x,i))).valid
  rw [axisCount_run]
  exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun i _ => cell_valid x i)⟩

end
end ExactFourierCircuits.DFTModelCRTMetadata
