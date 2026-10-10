import DFTModelCacheTraversalBounds
import DFTModelCacheTraversalFinishPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheTraversal
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalCacheTreeMachine UniformLocalCacheTreeCoverage
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node finish attach step body start count ticks Bill.tab

def peakBudget (r o : ℕ) : ℕ := 100000*(r+1)^4+o

theorem linear_peakBudget (r o : ℕ) : 2*r+2 ≤ peakBudget r o := by
  have h : r+1 ≤ (r+1)^4 := le_self_pow₀ (by omega) (by decide)
  unfold peakBudget
  omega

theorem attach_peak (t : Task) (ts : List Task) (ns : List Record7.T)
    (rs : List UniformLocalRectangleDescriptors.Row) :
    (run attach (encode ⟨t::ts,ns,rs⟩)).peak=
      (run DFTModelCacheDescriptor.node (t.width,t.offset)).peak := by
  rw [attach,fork_peak,fork_peak,comp_peak]
  have hv:(run headArg (encode ⟨t::ts,ns,rs⟩)).val=(t.width,t.offset) := rfl
  have hp:(run headArg (encode ⟨t::ts,ns,rs⟩)).peak=0 := rfl
  have hh:(run head (encode ⟨t::ts,ns,rs⟩)).peak=0 := rfl
  rw [hv,hp,hh]
  change max 0 (max 0 (max 0 (run DFTModelCacheDescriptor.node (t.width,t.offset)).peak))=_
  simp only [zero_max]

theorem ifz_peak {s t : Ty} (q : Prog false s w) (f g : Prog false s t) (x : s.T) :
    (run (.ifz q f g) x).peak=max (run q x).peak
      (if (run q x).val=0 then (run f x).peak else (run g x).peak) := by
  change max (max (run q x).peak (if (run q x).val=0 then run f x else run g x).peak) 0=_
  split_ifs <;> simp only [max_zero]

theorem step_peak (r o i : ℕ) (s : ListState) (h : Growth r o i s) (hi : i ≤ 2*r+1) :
    (run step (encode s)).peak ≤ peakBudget r o := by
  cases s with
  | mk tasks ns rs =>
    cases tasks with
    | nil =>
      rw [step,ifz_peak]
      change max 0 0 ≤ _
      exact Nat.zero_le _
    | cons t ts =>
      have ht:=h.tasks t (by simp)
      have hn:=h.nodes
      have hr:=h.rectangles
      have hs:=h.stack
      change ns.length ≤ i at hn
      change rs.length ≤ i*r^2 at hr
      change (t::ts).length ≤ i+1 at hs
      have rows:(currentRows t).length ≤ r^2 :=
        (currentRows_bound t).trans (Nat.pow_le_pow_left ht.1 2)
      have im:i*r^2 ≤ (2*r+1)*r^2 := Nat.mul_le_mul_right _ hi
      have pow:1 ≤ (r+1)^4 := Nat.one_le_pow 4 (r+1) (by omega)
      have hB:7 ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hOff:t.offset+t.width ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hStack:(t::ts).length+2 ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hNodes:ns.length+1 ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hRows:rs.length+(currentRows t).length ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hSeven:7*rs.length ≤ peakBudget r o := by unfold peakBudget;nlinarith
      have hlc:=finish_peak t ts ns rs (peakBudget r o) hB hOff hStack hNodes hRows hSeven
      have np:=DFTModelCacheDescriptor.node_peak t.width t.offset
      have squares:(t.width+1)^2 ≤ (r+1)^2 := Nat.pow_le_pow_left (by omega) _
      have node:(run DFTModelCacheDescriptor.node (t.width,t.offset)).peak ≤ peakBudget r o := by
        unfold peakBudget
        nlinarith
      rw [step,ifz_peak]
      have qv:(run (.comp (.atom .fst) (.atom .len) : Prog false StateT w)
          (encode ⟨t::ts,ns,rs⟩)).val=(t::ts).length := by
        simp [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,encode,ofList,List.length_map]
      have qp:(run (.comp (.atom .fst) (.atom .len) : Prog false StateT w)
          (encode ⟨t::ts,ns,rs⟩)).peak=(t::ts).length := by
        simp [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,encode,ofList,List.length_map]
      have ip:(run (.atom .id : Prog false StateT StateT) (encode ⟨t::ts,ns,rs⟩)).peak=0 := rfl
      rw [qv,qp,ip]
      rw [ite_eq_right (by simp:(t::ts).length≠0),comp_peak,attach_peak,attach_value]
      exact max_le (by omega) (max_le node hlc)

theorem body_peak (r o i : ℕ) (s : ListState) (h : Growth r o i s) (hi : i ≤ 2*r+1) :
    (run body ((r,o),(i,encode s))).peak ≤ peakBudget r o := by
  rw [body,comp_peak]
  change max 0 (run step (encode s)).peak ≤ _
  simpa only [zero_max] using step_peak r o i s h hi

theorem ticks_peak (r o j : ℕ) (hj : j ≤ 2*r+1) : (ticks r o j).peak ≤ peakBudget r o := by
  induction j with
  | zero => rw [ticks_zero];exact Nat.zero_le _
  | succ j ih =>
    have old:=ih (by omega)
    have one:=body_peak r o j (execute j (initial r o)) (execute_growth r o j) (by omega)
    rw [ticks_succ]
    change max (max (ticks r o j).peak (run body ((r,o),(j,(ticks r o j).val))).peak) (j+1) ≤ _
    rw [ticks_value]
    exact max_le (max_le old one) (by have := linear_peakBudget r o; omega)

theorem start_peak (r o : ℕ) : (run start (r,o)).peak=1 := by
  rw [start,fork_peak,fork_peak,comp_peak,singleton_run]
  have empty:(run emptyRecords (r,o)).peak=0 := by
    change max (max 0 (Bill.tab 0 Record7.blank (fun j=>run (zeroRecord (s:=p Input w)) ((r,o),j))).peak) 0=0
    rw [ModelEquivalenceInterpreter.tab_peak]
    simp
  rw [empty]
  rfl

theorem loop_peak {s t : Ty} (n : Prog false s w) (init : Prog false s t)
    (b : Prog false (p s (p w t)) t) (x : s.T) :
    (run (.loop n init b) x).peak=max (run n x).peak (max (run init x).peak
      (Bill.steps (run init x).val (fun i a=>run b (x,(i,a))) (run n x).val).peak) := by
  simp only [run,Code.run,Bill.pay,Bill.pass,max_zero]

theorem whole_peak (r o : ℕ) : (run whole (r,o)).peak=max (run count (r,o)).peak
    (max (run start (r,o)).peak (ticks r o (run count (r,o)).val).peak) := by
  rw [whole,loop_peak,ticks]

theorem program_peak (r o : ℕ) : (run program (r,o)).peak ≤ peakBudget r o := by
  have ht:=ticks_peak r o (2*r+1) (le_refl _)
  rw [program,comp_peak]
  have op:(run (.atom .snd : Prog false StateT Output) (run whole (r,o)).val).peak=0 := rfl
  rw [op,max_zero,whole_peak,count_value,start_peak]
  have cp:(run count (r,o)).peak ≤ 2*r+2 := by
    rw [count]
    simp [integer,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]
  exact max_le (cp.trans (linear_peakBudget r o))
    (max_le (by have := linear_peakBudget r o; omega) ht)

end
end ExactFourierCircuits.DFTModelCacheTraversal
