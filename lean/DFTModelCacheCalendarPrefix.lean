import DFTModelCacheCalendarDuration

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming
open DFTModelCacheTraversal (ofList rectangleEncode tape_ext ofList_look)
noncomputable section
attribute [local irreducible] rowDuration DFTModelCacheDescriptor.logarithm

abbrev PrefixInput : Ty := p (Ty.a Row7) w
abbrev PrefixBody : Ty := p PrefixInput (p w w)
def prefixRow : Prog false PrefixBody Row7 :=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.comp (.atom .snd) (.atom .fst))) (.atom .look)
def prefixBody : Prog false PrefixBody w :=
  nat .add (.comp (.atom .snd) (.atom .snd)) (.comp prefixRow rowDuration)
def prefixProgram : Prog false PrefixInput w := .loop (.atom .snd) (.atom (.lit 0)) prefixBody

theorem prefixBody_run (L : List Row) (c i total : ℕ) (hi : i<L.length) :
    run prefixBody ((ofList (L.map rectangleEncode),c),(i,total))=
    ⟨total+(run rowDuration (rectangleEncode L[i])).val,
      (run rowDuration (rectangleEncode L[i])).work+16,
      max (run rowDuration (rectangleEncode L[i])).peak
        (total+(run rowDuration (rectangleEncode L[i])).val),
      (run rowDuration (rectangleEncode L[i])).valid⟩ := by
  have get:(ofList (L.map rectangleEncode)).look i Row7.blank=rectangleEncode L[i] := by
    simp [ofList,Tape.look,hi]
  simp [prefixBody,nat,prefixRow,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,get]
  omega

attribute [local irreducible] prefixBody prefixProgram

def prefixTicks (L : List Row) (count j : ℕ) : Bill ℕ :=
  Bill.steps 0 (fun i total=>run prefixBody ((ofList (L.map rectangleEncode),count),(i,total))) j

theorem prefixTicks_zero (L : List Row) (count : ℕ) : prefixTicks L count 0=⟨0,1,0,True⟩ := rfl

theorem prefixTicks_succ (L : List Row) (count j : ℕ) :
    prefixTicks L count (j+1)=((prefixTicks L count j).pass (fun total=>
      run prefixBody ((ofList (L.map rectangleEncode),count),(j,total)))).pay 1 (j+1) := rfl

attribute [local irreducible] Bill.steps prefixTicks

theorem rectanglesDuration_append (L R : List Row) :
    rectanglesDuration (L++R)=rectanglesDuration L+rectanglesDuration R := by
  simp [rectanglesDuration]

theorem duration_take_succ (L : List Row) (i : ℕ) (hi:i<L.length) :
    rectanglesDuration (L.take (i+1))=rectanglesDuration (L.take i)+rectangleDuration L[i] := by
  rw [List.take_succ_eq_append_getElem hi,rectanglesDuration_append]
  simp [rectanglesDuration]

theorem prefixTicks_value (L : List Row) (count j : ℕ) (hj:j≤L.length) :
    (prefixTicks L count j).val=rectanglesDuration (L.take j) := by
  induction j with
  | zero => rw [prefixTicks_zero];rfl
  | succ j ih =>
    rw [prefixTicks_succ]
    change (run prefixBody ((ofList (L.map rectangleEncode),count),(j,(prefixTicks L count j).val))).val=_
    rw [prefixBody_run L count j _ (by omega)]
    change (prefixTicks L count j).val+(run rowDuration (rectangleEncode L[j])).val=_
    rw [ih (by omega),rowDuration_value,duration_take_succ L j (by omega)]

theorem prefix_run (L : List Row) (j : ℕ) :
    run prefixProgram (ofList (L.map rectangleEncode),j)=(prefixTicks L j j).pay 3 0 := by
  rw [prefixProgram]
  change ((Bill.one j).pass (fun count => (Bill.word 0).pass (fun total=>
    Bill.steps total (fun i a=>run prefixBody ((ofList (L.map rectangleEncode),j),(i,a))) count))).pay 1 0=_
  simp only [Bill.one,Bill.word,Bill.pass,Bill.pay,prefixTicks,zero_max,max_zero,true_and]
  congr 1;omega

theorem prefix_value (L : List Row) (j : ℕ) (hj:j≤L.length) :
    (run prefixProgram (ofList (L.map rectangleEncode),j)).val=rectanglesDuration (L.take j) := by
  rw [prefix_run]
  exact prefixTicks_value L j j hj

theorem duration_list_bound (L : List Row) (D : ℕ)
    (h:∀q∈L,rectangleDuration q≤D) : rectanglesDuration L≤L.length*D := by
  induction L with
  | nil => simp [rectanglesDuration]
  | cons q L ih =>
    have one:=h q (by simp)
    have tail:=ih (by intro x hx;exact h x (by simp [hx]))
    change rectangleDuration q+rectanglesDuration L ≤ (L.length+1)*D
    nlinarith

theorem duration_prefix_bound (L : List Row) (D j : ℕ)
    (h:∀q∈L,rectangleDuration q≤D) : rectanglesDuration (L.take j)≤j*D := by
  have hb:=duration_list_bound (L.take j) D (by intro q hq;exact h q (List.mem_of_mem_take hq))
  exact hb.trans (Nat.mul_le_mul_right _ (List.length_take_le _ _))

theorem prefixTicks_spec (L : List Row) (r count j : ℕ) (hj:j≤L.length)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (prefixTicks L count j).valid ∧
    (prefixTicks L count j).work≤j*(1000*(2*r+1)+17)+1 ∧
    (prefixTicks L count j).peak≤j*(100000*(2*r+1)) := by
  induction j with
  | zero => rw [prefixTicks_zero];simp
  | succ j ih =>
    obtain ⟨iv,iw,ip⟩:=ih (by omega)
    have jq:=h L[j] (by simp)
    have qv:=rowDuration_value L[j]
    have qd:=rowDuration_valid L[j]
    have qw:=rowDuration_work L[j]
    have qp:=rowDuration_peak L[j]
    have db:∀q∈L,rectangleDuration q≤100000*(2*r+1) := by
      intro q hq
      exact (rectangleDuration_bound q).trans (Nat.mul_le_mul_left _ (by have :=h q hq;omega))
    have total:=duration_prefix_bound L (100000*(2*r+1)) (j+1) db
    rw [duration_take_succ L j (by omega)] at total
    rw [prefixTicks_succ]
    dsimp only [Bill.pass,Bill.pay,Bill.valid,Bill.work,Bill.peak]
    rw [prefixBody_run L count j _ (by omega)]
    rw [prefixTicks_value L count j (by omega),qv]
    dsimp only [Bill.valid,Bill.work,Bill.peak]
    refine ⟨⟨iv,qd⟩,?_,?_⟩
    · nlinarith
    · apply max_le
      · apply max_le (ip.trans (Nat.mul_le_mul_right _ (Nat.le_succ j)))
        exact max_le (by nlinarith) total
      · nlinarith

theorem prefix_valid (L : List Row) (j : ℕ) (hj:j≤L.length) :
    (run prefixProgram (ofList (L.map rectangleEncode),j)).valid := by
  rw [prefix_run]
  have h:∀q∈L,q.a+q.e≤2*((L.map (fun q=>q.a+q.e)).sum) := by
    intro q hq
    have one : q.a+q.e≤(L.map (fun q=>q.a+q.e)).sum :=
      List.single_le_sum (by intro x hx;exact Nat.zero_le _) (q.a+q.e) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    omega
  exact (prefixTicks_spec L _ j j hj h).1

theorem prefix_work (L : List Row) (r j : ℕ) (hj:j≤L.length)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run prefixProgram (ofList (L.map rectangleEncode),j)).work≤j*(1000*(2*r+1)+17)+4 := by
  rw [prefix_run]
  have hw:=(prefixTicks_spec L r j j hj h).2.1
  dsimp only [Bill.pay]
  omega

theorem prefix_peak (L : List Row) (r j : ℕ) (hj:j≤L.length)
    (h:∀q∈L,q.a+q.e≤2*r) :
    (run prefixProgram (ofList (L.map rectangleEncode),j)).peak≤j*(100000*(2*r+1)) := by
  rw [prefix_run]
  simpa only [Bill.pay,max_zero] using (prefixTicks_spec L r j j hj h).2.2

end
end ExactFourierCircuits.DFTModelCacheCalendar
