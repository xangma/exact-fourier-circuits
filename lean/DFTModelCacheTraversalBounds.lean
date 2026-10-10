import DFTModelCacheTraversalValid
import DFTModelCacheTraversalCharges
import DFTModelCacheDescriptorNodePeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node finish attach step body start Bill.tab

theorem attach_work (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run attach (encode ⟨t::ts,ns,rs⟩)).work=
      (run DFTModelCacheDescriptor.node (t.width,t.offset)).work+20 := by
  rw [attach,fork_work,fork_work,comp_work]
  have hv:(run headArg (encode ⟨t::ts,ns,rs⟩)).val=(t.width,t.offset) := rfl
  have hw:(run headArg (encode ⟨t::ts,ns,rs⟩)).work=11 := rfl
  have hh:(run head (encode ⟨t::ts,ns,rs⟩)).work=5 := rfl
  rw [hv,hw,hh]
  change 1+(5+(11+(run DFTModelCacheDescriptor.node (t.width,t.offset)).work+1)+1)+1=_
  omega

theorem ifz_work {s t : Ty} (q : Prog false s w) (f g : Prog false s t) (x : s.T) :
    (run (.ifz q f g) x).work=(run q x).work+
      (if (run q x).val=0 then (run f x).work else (run g x).work)+1 := by
  change (run q x).work+(if (run q x).val=0 then run f x else run g x).work+1=_
  split_ifs <;> rfl

theorem step_cons_work (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run step (encode ⟨t::ts,ns,rs⟩)).work=
      (run DFTModelCacheDescriptor.node (t.width,t.offset)).work+
        (run finish (frame ⟨t::ts,ns,rs⟩ t)).work+25 := by
  rw [step,ifz_work]
  change 3+(if (t::ts).length=0 then 1 else
    (run (.comp attach finish) (encode ⟨t::ts,ns,rs⟩)).work)+1=_
  rw [ite_eq_right (by simp:(t::ts).length≠0),comp_work,attach_work,attach_value]
  omega

theorem step_work (r o i : ℕ) (s : ListState) (h : Growth r o i s) (hi : i ≤ 2*r+1) :
    (run step (encode s)).work ≤ 20000*(r+1)^4 := by
  cases s with
  | mk tasks ns rs =>
    cases tasks with
    | nil =>
      have eq:(run step (encode ⟨[],ns,rs⟩)).work=5 := by
        rw [step,ifz_work]
        rfl
      rw [eq]
      have p:1 ≤ (r+1)^4 := Nat.one_le_pow 4 (r+1) (by omega)
      omega
    | cons t ts =>
      have ht:=h.tasks t (by simp)
      have node:=DFTModelCacheDescriptor.node_work t.width t.offset
      have four:(t.width+1)^4 ≤ (r+1)^4 := Nat.pow_le_pow_left (by omega) _
      have hlc:=finish_work t ts ns rs
      have rows:(currentRows t).length ≤ r^2 :=
        (currentRows_bound t).trans (Nat.pow_le_pow_left ht.1 2)
      have hn:=h.nodes
      have hr:=h.rectangles
      have hs:=h.stack
      change ns.length ≤ i at hn
      change rs.length ≤ i*r^2 at hr
      change (t::ts).length ≤ i+1 at hs
      rw [step_cons_work]
      have step:(run finish (frame ⟨t::ts,ns,rs⟩ t)).work ≤
          42*(i+1)+29*i+29*((i+1)*r^2)+1000 := by nlinarith
      have im : i*r^2 ≤ (2*r+1)*r^2 := Nat.mul_le_mul_right _ hi
      nlinarith [Nat.one_le_pow 4 (r+1) (by omega)]

theorem body_work (r o i : ℕ) (s : ListState) (h : Growth r o i s) (hi : i ≤ 2*r+1) :
    (run body ((r,o),(i,encode s))).work ≤ 20000*(r+1)^4+4 := by
  have hs:=step_work r o i s h hi
  rw [body,comp_work]
  change 3+(run step (encode s)).work+1 ≤ _
  omega

theorem ticks_zero (r o : ℕ) : ticks r o 0=Bill.one (run start (r,o)).val := rfl

theorem ticks_succ (r o j : ℕ) : ticks r o (j+1)=
    ((ticks r o j).pass (fun s=>run body ((r,o),(j,s)))).pay 1 (j+1) := rfl

attribute [local irreducible] ticks

theorem ticks_work (r o j : ℕ) (hj : j ≤ 2*r+1) :
    (ticks r o j).work ≤ j*(20000*(r+1)^4+5)+1 := by
  induction j with
  | zero =>
    rw [ticks_zero]
    simpa only [Bill.one,Nat.zero_mul,Nat.zero_add] using (Nat.le_refl 1)
  | succ j ih =>
    have old:=ih (by omega)
    have one:=body_work r o j (execute j (initial r o)) (execute_growth r o j) (by omega)
    rw [ticks_succ]
    change (ticks r o j).work+(run body ((r,o),(j,(ticks r o j).val))).work+1 ≤ _
    rw [ticks_value]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem start_work (r o : ℕ) : (run start (r,o)).work=27 := by
  rw [start,fork_work,fork_work,comp_work,singleton_run]
  have empty:(run emptyRecords (r,o)).work=4 := by
    change 1+(Bill.tab 0 Record7.blank (fun j=>run (zeroRecord (s:=p Input w)) ((r,o),j))).work+1=_
    rw [ModelEquivalenceInterpreter.tab_work]
    simp
  rw [empty]
  rfl

theorem loop_work {s t : Ty} (n : Prog false s w) (init : Prog false s t)
    (b : Prog false (p s (p w t)) t) (x : s.T) :
    (run (.loop n init b) x).work=(run n x).work+(run init x).work+
      (Bill.steps (run init x).val (fun i a=>run b (x,(i,a))) (run n x).val).work+1 := by
  simp only [run,Code.run,Bill.pay,Bill.pass]
  omega

theorem whole_work (r o : ℕ) : (run whole (r,o)).work=(run count (r,o)).work+
    (run start (r,o)).work+(ticks r o (run count (r,o)).val).work+1 := by
  rw [whole,loop_work,ticks]

theorem program_work (r o : ℕ) : (run program (r,o)).work ≤ 100000*(r+1)^5 := by
  have hw:=ticks_work r o (2*r+1) (le_refl _)
  rw [program,comp_work,whole_work]
  have ow:(run (.atom .snd : Prog false StateT Output) (run whole (r,o)).val).work=1 := rfl
  rw [ow]
  rw [count_value,start_work]
  have cw:(run count (r,o)).work=9 := rfl
  rw [cw]
  nlinarith [Nat.one_le_pow 4 (r+1) (by omega)]

end
end ExactFourierCircuits.DFTModelCacheTraversal
