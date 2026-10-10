import DFTModelSectorMapBitsHigh

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapBits
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

def packed (m : Tape ℕ) (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => packed m s n + 2^n * flag (m.look (s+n) 0)

theorem packed_bound (m : Tape ℕ) (s n : ℕ) : packed m s n < 2^n := by
  induction n with
  | zero => simp [packed]
  | succ n ih =>
    rw [packed, Nat.pow_succ]
    have hf := flag_le (m.look (s+n) 0)
    have hp := Nat.two_pow_pos n
    nlinarith

abbrev Input := p w (p w (Ty.a w))
abbrev PackCellInput := p Input w
abbrev PackState := p w w
abbrev PackBodyInput := p PackCellInput (p w PackState)

def packParameters : Prog false PackBodyInput Input := .comp (.atom .fst) (.atom .fst)
def packB : Prog false PackBodyInput w := .comp packParameters (.atom .fst)
def packChunk : Prog false PackBodyInput w := .comp (.atom .fst) (.atom .snd)
def packIndex : Prog false PackBodyInput w := .comp (.atom .snd) (.atom .fst)
def packMarkers : Prog false PackBodyInput (Ty.a w) :=
  .comp packParameters (.comp (.atom .snd) (.atom .snd))
def packPower : Prog false PackBodyInput w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .fst))
def packWord : Prog false PackBodyInput w := .comp (.atom .snd) (.comp (.atom .snd) (.atom .snd))
def packAddress : Prog false PackBodyInput w := binary .add (binary .mul packChunk packB) packIndex
def packMarker : Prog false PackBodyInput w := .comp (.fork packMarkers packAddress) (.atom .look)
def packFlag : Prog false PackBodyInput w := binary .lt (.atom (.lit 0)) packMarker
def packBody : Prog false PackBodyInput PackState :=
  .fork (binary .mul packPower (.atom (.lit 2)))
    (binary .add packWord (binary .mul packPower packFlag))
def packLoop : Prog false PackCellInput PackState :=
  .loop (.comp (.atom .fst) (.atom .fst))
    (.fork (.atom (.lit 1)) (.atom (.lit 0))) packBody
def packCell : Prog false PackCellInput w := .comp packLoop (.atom .snd)
def chunks : Prog false Input w :=
  binary .add (binary .div (.comp (.atom .snd) (.atom .fst)) (.atom .fst)) (.atom (.lit 1))
def pack : Prog false Input (Ty.a w) := .tab chunks packCell

theorem packBody_run (b V : ℕ) (m : Tape ℕ) (c i q z : ℕ) :
    run packBody (((b,(V,m)),c),(i,(q,z))) =
      ⟨(q*2,z+q*flag (m.look (c*b+i) 0)),57,
        max 2 (max (c*b+i) (max (q*2) (z+q*flag (m.look (c*b+i) 0)))),True⟩ := by
  simp [packBody, packPower, packWord, packFlag, packMarker, packAddress,
    packMarkers, packParameters, packChunk, packB, packIndex, binary,
    flag, run, Code.run, Atom.run, NOp.run, Ty.blank,
    Bill.pass, Bill.pay, Bill.word, Bill.one]
  split <;> omega

def packSteps (b V : ℕ) (m : Tape ℕ) (c n : ℕ) : Bill (ℕ × ℕ) :=
  Bill.steps (1,0) (fun i s => run packBody (((b,(V,m)),c),(i,s))) n

theorem packSteps_value (b V : ℕ) (m : Tape ℕ) (c n : ℕ) :
    (packSteps b V m c n).val = (2^n,packed m (c*b) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (run packBody (((b,(V,m)),c),(n,(packSteps b V m c n).val))).val = _
    rw [packBody_run]
    change ((packSteps b V m c n).val.1*2,
      (packSteps b V m c n).val.2+(packSteps b V m c n).val.1*flag (m.look (c*b+n) 0)) = _
    rw [ih]
    simp only [packed, Nat.pow_succ]

theorem packSteps_work (b V : ℕ) (m : Tape ℕ) (c n : ℕ) :
    (packSteps b V m c n).work = 58*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (packSteps b V m c n).work + (run packBody (((b,(V,m)),c),(n,(packSteps b V m c n).val))).work + 1 = _
    rw [packBody_run, ih]
    dsimp only [Bill.work]
    omega

theorem packSteps_valid (b V : ℕ) (m : Tape ℕ) (c n : ℕ) :
    (packSteps b V m c n).valid := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change (packSteps b V m c n).valid ∧ (run packBody (((b,(V,m)),c),(n,(packSteps b V m c n).val))).valid
    rw [packBody_run]
    exact ⟨ih,trivial⟩

theorem packSteps_peak (b V : ℕ) (m : Tape ℕ) (c n : ℕ) :
    (packSteps b V m c n).peak ≤ max 2 (max (c*b+n) (2^n)) := by
  induction n with
  | zero => simp [packSteps, Bill.steps, Bill.one]
  | succ n ih =>
    change max (max (packSteps b V m c n).peak
      (run packBody (((b,(V,m)),c),(n,(packSteps b V m c n).val))).peak) (n+1) ≤ _
    rw [packBody_run]
    change max (max (packSteps b V m c n).peak
      (max 2 (max (c*b+n) (max ((packSteps b V m c n).val.1*2)
        ((packSteps b V m c n).val.2+(packSteps b V m c n).val.1*flag (m.look (c*b+n) 0)))))) (n+1) ≤ _
    rw [packSteps_value]
    have hp := packed_bound m (c*b) (n+1)
    have hn : 2^n ≤ 2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    change max (max (packSteps b V m c n).peak
      (max 2 (max (c*b+n) (max (2^n*2) (packed m (c*b) (n+1)))))) (n+1) ≤ _
    rw [← Nat.pow_succ]
    omega

theorem packCell_value (b V : ℕ) (m : Tape ℕ) (c : ℕ) :
    (run packCell ((b,(V,m)),c)).val = packed m (c*b) b := by
  change (packSteps b V m c b).val.2 = _
  rw [packSteps_value]

theorem packCell_work (b V : ℕ) (m : Tape ℕ) (c : ℕ) :
    (run packCell ((b,(V,m)),c)).work = 58*b+10 := by
  change 3+(3+(packSteps b V m c b).work)+1+1+1 = _
  rw [packSteps_work]
  omega

theorem packCell_valid (b V : ℕ) (m : Tape ℕ) (c : ℕ) :
    (run packCell ((b,(V,m)),c)).valid := by
  change ((True ∧ True) ∧ (True ∧ True ∧ True) ∧ (packSteps b V m c b).valid) ∧ True
  exact ⟨⟨⟨trivial,trivial⟩,⟨trivial,trivial,trivial⟩,packSteps_valid b V m c b⟩,trivial⟩

theorem packCell_peak (b V : ℕ) (m : Tape ℕ) (c : ℕ) :
    (run packCell ((b,(V,m)),c)).peak ≤ max 2 (max (c*b+b) (2^b)) := by
  have h := packSteps_peak b V m c b
  have hh : max 1 (packSteps b V m c b).peak ≤ max 2 (max (c*b+b) (2^b)) := by omega
  simpa only [packCell, packLoop, run, Code.run, Atom.run, Bill.pass, Bill.pay,
    Bill.word, Bill.one, packSteps, max_zero, zero_max] using hh

theorem chunks_run (b V : ℕ) (m : Tape ℕ) :
    run chunks (b,(V,m)) = ⟨V/b+1,11,V/b+1,True⟩ := by
  simp [chunks,binary,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem pack_value (b V : ℕ) (m : Tape ℕ) :
    (run pack (b,(V,m))).val = Tape.tab (V/b+1) (fun c => packed m (c*b) b) := by
  change (Bill.tab (run chunks (b,(V,m))).val 0 (fun c => run packCell ((b,(V,m)),c))).val = _
  rw [chunks_run, ModelEquivalenceInterpreter.tab_value]
  congr 1
  funext c
  exact packCell_value b V m c

theorem pack_work (b V : ℕ) (m : Tape ℕ) :
    (run pack (b,(V,m))).work = 14+(58*b+14)*(V/b+1) := by
  change (run chunks (b,(V,m))).work +
    (Bill.tab (run chunks (b,(V,m))).val 0 (fun c => run packCell ((b,(V,m)),c))).work + 1 = _
  rw [chunks_run, ModelEquivalenceInterpreter.tab_work]
  have hs : (∑ c ∈ Finset.range (V/b+1), (run packCell ((b,(V,m)),c)).work) = (V/b+1)*(58*b+10) := by
    calc
      _ = ∑ _c ∈ Finset.range (V/b+1), (58*b+10) := Finset.sum_congr rfl (fun c _ => packCell_work b V m c)
      _ = _ := by simp
  rw [hs]
  ring

theorem pack_valid (b V : ℕ) (m : Tape ℕ) : (run pack (b,(V,m))).valid := by
  change (run chunks (b,(V,m))).valid ∧
    (Bill.tab (run chunks (b,(V,m))).val 0 (fun c => run packCell ((b,(V,m)),c))).valid
  rw [chunks_run]
  exact ⟨trivial, (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun c _ => packCell_valid b V m c)⟩

theorem pack_peak (b V : ℕ) (m : Tape ℕ) (hb : 1 ≤ b) :
    (run pack (b,(V,m))).peak ≤ max 2 (max ((V/b+1)*b) (2^b)) := by
  change max (max (run chunks (b,(V,m))).peak
    (Bill.tab (run chunks (b,(V,m))).val 0 (fun c => run packCell ((b,(V,m)),c))).peak) 0 ≤ _
  rw [chunks_run, ModelEquivalenceInterpreter.tab_peak]
  dsimp only [Bill.peak, Bill.val]
  have hs : (Finset.range (V/b+1)).sup (fun c => (run packCell ((b,(V,m)),c)).peak) ≤
      max 2 (max ((V/b+1)*b) (2^b)) := by
    apply Finset.sup_le
    intro c hc
    have h := packCell_peak b V m c
    have hcb : c*b+b ≤ (V/b+1)*b := by
      have hc' := Finset.mem_range.mp hc
      simpa [Nat.add_mul] using Nat.mul_le_mul_right b (show c+1 ≤ V/b+1 by omega)
    omega
  have hc : V/b+1 ≤ (V/b+1)*b := Nat.le_mul_of_pos_right _ hb
  omega

end
end ExactFourierCircuits.DFTModelSectorMapBits
