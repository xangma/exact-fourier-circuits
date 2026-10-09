import UniformAxisCacheWholeExecution
import UniformCacheRetentionBounds
set_option autoImplicit false
namespace ExactFourierCircuits.UniformCacheLowRetention
open UniformMachine UniformCacheRetentionRegions
abbrev z := UniformJointCacheWorkspace.stride
structure Frame (n:ℕ) (s u:State) : Prop where
 nat : ∀a,a<z n→u.natHeap a=s.natHeap a
 scalar : ∀a,a<z n→u.scalarHeap a=s.scalarHeap a
lemma Frame.refl (n:ℕ) (s:State) : Frame n s s := ⟨fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {n:ℕ} {s a u:State} (h:Frame n s a) (g:Frame n a u) : Frame n s u :=
 ⟨fun i hi=>(g.nat i hi).trans (h.nat i hi),fun i hi=>(g.scalar i hi).trans (h.scalar i hi)⟩
structure Below (L:ℕ) (c:Config) (p:Params) (dest A:ℕ)
 (v:UniformCrossHeightPreparationMachine.Parameters) : Prop where
 originalNat : ∀b∈[c.d,c.conv,c.tape,c.depth,c.order,c.directory,c.rows,c.colors,c.palette,c.heightDirectory],L≤b
 originalScalar : ∀b∈[c.S,c.A,c.C,c.negative,c.constants],L≤b
 conjugateNat : ∀b∈[p.d,p.conv,p.tape,p.depth],L≤b
 conjugateScalar : ∀b∈[p.S,p.A,p.C,dest],L≤b
 slots : L≤A
 disabled : ∀b∈[v.D,v.F,v.U,v.J],L≤b
lemma Below.frame {n:ℕ} {c:Config} {p:Params} {dest A:ℕ}
 {v:UniformCrossHeightPreparationMachine.Parameters} {s u:State}
 (below:Below (z n) c p dest A v) (frame:PhaseFrame c p dest A v s u) : Frame n s u := by
 constructor
 · intro a ha
   apply frame.1
   · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
     all_goals exact Or.inl (lt_of_lt_of_le ha (below.originalNat _ (by simp)))
   · refine ⟨?_,?_,?_,?_⟩
     all_goals exact Or.inl (lt_of_lt_of_le ha (below.conjugateNat _ (by simp)))
   · exact Or.inl (ha.trans_le below.slots)
   · refine ⟨?_,?_,?_,?_⟩
     all_goals exact Or.inl (lt_of_lt_of_le ha (below.disabled _ (by simp)))
 · intro a ha
   apply frame.2
   · refine ⟨?_,?_,?_,?_,?_⟩
     all_goals exact Or.inl (lt_of_lt_of_le ha (below.originalScalar _ (by simp)))
   · refine ⟨?_,?_,?_,?_⟩
     all_goals exact Or.inl (lt_of_lt_of_le ha (below.conjugateScalar _ (by simp)))
lemma workspace_below (n:ℕ) (j:Fin (UniformAllAxisSeedPreparation.axisCount n)) (q:UniformLocalRectangleDescriptors.Row) :
 Below (z n) (UniformLocalRectanglePhaseBanks.actual q (UniformJointCacheWorkspace.original n q))
 (UniformLocalRectanglePhaseBanks.nextParameters n j q (UniformJointCacheWorkspace.original n q)
  (UniformJointCacheWorkspace.work n)) (UniformJointCacheWorkspace.conjugate n)
 (UniformJointCacheWorkspace.control n)
 (UniformLocalDisabledHeightMachine.disabled
  (UniformLocalRectanglePhaseBanks.actual q (UniformJointCacheWorkspace.original n q)).height
  (UniformJointCacheWorkspace.falseRows n) (UniformJointCacheWorkspace.falseColors n)
  (UniformJointCacheWorkspace.falsePalette n) (UniformJointCacheWorkspace.falseDirectory n)) := by
 constructor
 · change ∀b∈[2*z n,3*z n,4*z n,5*z n,6*z n,7*z n,8*z n,9*z n,10*z n,11*z n],z n≤b
   intro b hb
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
   rcases hb with h|h|h|h|h|h|h|h|h|h <;> omega
 · change ∀b∈[2*z n,3*z n,4*z n,5*z n,6*z n],z n≤b
   intro b hb
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
   rcases hb with h|h|h|h|h <;> omega
 · change ∀b∈[13*z n,14*z n,15*z n,16*z n],z n≤b
   intro b hb
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
   rcases hb with h|h|h|h <;> omega
 · change ∀b∈[8*z n,9*z n,10*z n,11*z n],z n≤b
   intro b hb
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
   rcases hb with h|h|h|h <;> omega
 · change z n≤17*z n;omega
 · change ∀b∈[18*z n,19*z n,20*z n,21*z n],z n≤b
   intro b hb
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
   rcases hb with h|h|h|h <;> omega
end ExactFourierCircuits.UniformCacheLowRetention
