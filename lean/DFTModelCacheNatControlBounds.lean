import DFTModelCacheNatControlCore

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheNatControl
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] ModelEquivalenceInterpreter.update ModelEquivalenceNat.natCode ModelEquivalenceNat.branchCode

theorem write_work (d : ℕ) (f : Prog false Local w) (v : LocalValue) :
    (run (write d f) v).work=17+(run f v).work+
      (run (ModelEquivalenceInterpreter.update w) ((v.2.1,d),(run f v).val)).work := by
  simp only [write,nextPC,nat,pc,literal,heap,registers,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

theorem write_peak (d : ℕ) (f : Prog false Local w) (v : LocalValue) :
    (run (write d f) v).peak=max 1 (max (v.1+1)
      (max d (max (run f v).peak
        (run (ModelEquivalenceInterpreter.update w) ((v.2.1,d),(run f v).val)).peak))) := by
  simp only [write,nextPC,nat,pc,literal,heap,registers,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,max_zero,zero_max]
  omega

/-- Every instruction rebuilds at most one finite register or heap tape. -/
theorem instruction_work (i : Instruction) (v : LocalValue) :
    (run (instruction i) v).work ≤ 35*(v.2.1.len+v.2.2.len)+100 := by
  cases i with
  | literal d x =>
    have h:=ModelEquivalenceInterpreter.update_work_bounds w v.2.1 d x
    rw [instruction,write_work]
    change 17+1+(run (ModelEquivalenceInterpreter.update w) ((v.2.1,d),x)).work≤_
    omega
  | binary op d l r =>
    have h:=ModelEquivalenceInterpreter.update_work_bounds w v.2.1 d
      (run (.comp (.fork (read l) (read r)) (ModelEquivalenceNat.natCode op)) v).val
    have hc:=ModelEquivalenceNat.natCode_work_le op (reg v l) (reg v r)
    rw [instruction,binary,write_work]
    change 17+(15+(run (ModelEquivalenceNat.natCode op) (reg v l,reg v r)).work+1)+_≤_
    omega
  | load d addr =>
    by_cases hp:(cell v (reg v addr)).1=0
    · simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,hp,ite_true]
      change 15+7+1≤_
      omega
    · have h:=ModelEquivalenceInterpreter.update_work_bounds w v.2.1 d (cell v (reg v addr)).2
      simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,hp,ite_false]
      change 15+(run (write d (heapValue addr)) v).work+1≤_
      rw [write_work,heapValue_run]
      dsimp only [Bill.work,Bill.val]
      omega
  | store addr src =>
    have h:=ModelEquivalenceInterpreter.update_work_bounds Cell v.2.2 (reg v addr) (1,reg v src)
    simp only [instruction,store,nextPC,nat,pc,registers,heap,read,literal,run,Code.run,
      Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    dsimp only [reg,run,Ty.blank] at h
    simp only [Ty.blank]
    omega
  | branch l r y n =>
    change 15+(run (ModelEquivalenceNat.branchCode y n) (reg v l,reg v r)).work+1+1+1≤_
    rw [ModelEquivalenceNat.branchCode_run]
    change 21≤_
    omega
  | jump t => change 3≤_;omega
  | halt => change 1≤_;omega

def PeakBound (i : Instruction) (v : LocalValue) (B : ℕ) : Prop :=
  1≤B ∧ v.1+1≤B ∧ v.2.1.len≤B ∧ v.2.2.len≤B ∧
  match i with
  | .literal d x => d≤B ∧ x≤B
  | .binary op d l r => d≤B ∧ l≤B ∧ r≤B ∧
      ((ModelEquivalenceNat.toUpstream op).run (reg v l,reg v r)).val≤B
  | .load d addr => d≤B ∧ addr≤B
  | .store addr src => addr≤B ∧ src≤B ∧ reg v addr≤B
  | .branch l r y n => l≤B ∧ r≤B ∧ y≤B ∧ n≤B
  | .jump t => t≤B
  | .halt => True

theorem update_peak_le (t : Ty) (z : Tape t.T) (i : ℕ) (x : t.T) (B : ℕ)
    (hz : z.len≤B) (hi : i≤B) :
    (run (ModelEquivalenceInterpreter.update t) ((z,i),x)).peak≤B := by
  rw [ModelEquivalenceInterpreter.update_peak]
  split_ifs <;> omega

theorem write_peak_le (d B : ℕ) (f : Prog false Local w) (v : LocalValue)
    (_h1 : 1≤B) (hp : v.1+1≤B) (hr : v.2.1.len≤B) (hd : d≤B)
    (hf : (run f v).peak≤B) : (run (write d f) v).peak≤B := by
  rw [write_peak]
  have hu:=update_peak_le w v.2.1 d (run f v).val B hr hd
  omega

theorem instruction_peak (i : Instruction) (v : LocalValue) (B : ℕ)
    (h : PeakBound i v B) : (run (instruction i) v).peak≤B := by
  rcases h with ⟨h1,hpc,hr,hh,h⟩
  cases i with
  | literal d x =>
    apply write_peak_le d B (literal x) v h1 hpc hr h.1
    exact h.2
  | binary op d l r =>
    apply write_peak_le d B _ v h1 hpc hr h.1
    have hn:=ModelEquivalenceNat.natCode_peak op (reg v l) (reg v r)
    simp only [run,Code.run,Bill.pass,Bill.pay,read_run]
    simp only [Bill.one]
    change max (max (max l (max r 0)) (run (ModelEquivalenceNat.natCode op) (reg v l,reg v r)).peak) 0≤_
    rw [hn,ModelEquivalenceNat.natCode_value]
    omega
  | load d addr =>
    by_cases hp:(cell v (reg v addr)).1=0
    · simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,hp,ite_true]
      change max (max addr 0) 0≤_
      omega
    · have hw:=write_peak_le d B (heapValue addr) v h1 hpc hr h.1
        (by rw [heapValue_run];exact h.2)
      simp only [instruction,load,run,Code.run,Bill.pass,Bill.pay,heapPresence_run,hp,ite_false]
      change max (max addr (run (write d (heapValue addr)) v).peak) 0≤_
      omega
  | store addr src =>
    have hu:=update_peak_le Cell v.2.2 (reg v addr) (1,reg v src) B hh h.2.2
    dsimp only [instruction,store,nextPC,nat,pc,registers,heap,read,literal,run,Code.run,
      Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    dsimp only [reg,run,Ty.blank] at hu
    simp only [Ty.blank]
    omega
  | branch l r y n =>
    simp only [instruction,branch,jump,run,Code.run,Bill.pass,Bill.pay,read_run,Atom.run,Bill.one]
    change max (max (max (max l (max r 0))
      (run (ModelEquivalenceNat.branchCode y n) (reg v l,reg v r)).peak) 0) 0≤_
    rw [ModelEquivalenceNat.branchCode_run]
    dsimp only [Bill.peak]
    split_ifs <;> omega
  | jump t => change max t 0≤_;omega
  | halt => change 0≤_;omega

end
end ExactFourierCircuits.DFTModelCacheNatControl
