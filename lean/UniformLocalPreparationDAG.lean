import UniformLocalFourierLayers
import UniformRankKernelPreparation
import UniformShearPreparation

set_option autoImplicit false

/-! Append-only scalar preparation for the actual balanced partition.  Existing
coefficient, reciprocal and root references are retained.  This module does not
assert a RAM producer or an already complete local Fourier scalar bank. -/
namespace ExactFourierCircuits.UniformLocalPreparationDAG
open UniformScalarPreparation
open UniformBalancedToeplitz UniformWorkspacePlanner
open scoped BigOperators

/-- One literal ragged cross rectangle; all coefficient/root indices are finite. -/
structure Request (N : ℕ) where
  a : ℕ
  e : ℕ
  s : ℕ
  i₀ : ℕ
  j₀ : ℕ
  positive : 0 < a
  sourcePositive : 0 < e
  hBound : i₀ + a ≤ N
  gBound : s < N
  interior : s ≤ i₀
  sourceBound : j₀ + e ≤ s

def Request.k {N : ℕ} (q : Request N) : ℕ := exponent q.a q.e

theorem Request.a_le {N : ℕ} (q : Request N) : q.a ≤ N := by have := q.hBound; omega
theorem Request.e_le {N : ℕ} (q : Request N) : q.e ≤ N := by
  have := q.sourceBound; have := q.gBound; omega
theorem Request.k_le {N : ℕ} (q : Request N) : q.k ≤ Nat.clog 2 N + 2 :=
  exponent_bound q.a_le q.e_le
theorem Request.width_le {N : ℕ} (q : Request N) : 2^q.k ≤ 8*N := by
  have h := width_bound (by have := q.positive; omega : 0<q.a+q.e)
  have := q.a_le; have := q.e_le
  dsimp [Request.k]; omega

def pairRequest {n N : ℕ} (hn : 2≤n) (hv : 0<selected n) (hN : n≤N)
    (q : Fin (chunkCount (n-n/2) (selected n)) × Fin (chunkCount (n/2) (selected n))) : Request N where
  a := size (n-n/2) (selected n) q.1
  e := size (n/2) (selected n) q.2
  s := n/2
  i₀ := n/2+q.1.val*selected n
  j₀ := q.2.val*selected n
  positive := size_pos _ _ hv _
  sourcePositive := size_pos _ _ hv _
  hBound := by have := size_end (n-n/2) (selected n) hv q.1; omega
  gBound := by omega
  interior := by omega
  sourceBound := size_end (n/2) (selected n) hv q.2

/-- Depth-first order agrees with `render`: left, right, then every cross pair. -/
def requests {n : ℕ} (P : Plan n) {N : ℕ} (hN : n≤N) : List (Request N) :=
  match P with
  | .direct _ _ => []
  | .split n hn hv L R =>
    requests L (by omega) ++ requests R (by omega) ++
      (pairs n).map (pairRequest hn hv hN)

theorem requests_length {n N : ℕ} (P : Plan n) (hN : n≤N) :
    (requests P hN).length ≤ n^2 := by
  induction P with
  | direct n cap => simp [requests]
  | split n hn hv L R ihL ihR =>
    simp only [requests,List.length_append,List.length_map]
    have hL := ihL (by omega : n/2≤N)
    have hR := ihR (by omega : n-n/2≤N)
    have hc := pairs_length n
    have ha := chunkCount_le (n-n/2) (selected n) hv
    have hb := chunkCount_le (n/2) (selected n) hv
    have hp := Nat.mul_le_mul ha hb
    have hs : n/2+(n-n/2)=n := by omega
    nlinarith

structure Cached (N l : ℕ) where
  request : Request N
  refs : Fin (UniformToeplitzCrossDAG.bankSize request.k) → Fin l

/-- All persistent inputs and already emitted spectra live in the SAME program. -/
structure State (r N origin : ℕ) where
  length : ℕ
  program : Program r length
  original : Fin origin → Fin length
  h : Fin N → Fin length
  g : Fin N → Fin length
  omega : Fin (Nat.clog 2 N+3) → Fin length
  cache : List (Cached N length)

def State.dag {r N o : ℕ} (b : State r N o) : DAG r 0 :=
  ⟨b.length,b.program,Fin.elim0⟩

def State.sources {r N o : ℕ} (b : State r N o) (q : Request N) :
    UniformRankKernelPreparation.Sources b.length q.a q.e :=
  ⟨N,N,b.h,b.g,q.s,q.i₀,q.j₀,q.positive,q.hBound,q.gBound⟩

def State.root {r N o : ℕ} (b : State r N o) (q : Request N) : Fin b.length :=
  b.omega ⟨q.k,by have := q.k_le; omega⟩

def State.nextDAG {r N o : ℕ} (b : State r N o) (q : Request N) :=
  UniformRankKernelPreparation.spectrumBank q.k b.dag (b.sources q) (b.root q)

def State.retain {r N o : ℕ} (b : State r N o) (q : Request N) :
    Fin b.length → Fin (b.nextDAG q).length :=
  UniformRankKernelPreparation.spectrumRetained q.k b.dag (b.sources q) (b.root q)

def Cached.map {N l t : ℕ} (c : Cached N l) (f : Fin l → Fin t) : Cached N t :=
  ⟨c.request,f ∘ c.refs⟩

def State.extend {r N o : ℕ} (b : State r N o) (q : Request N) : State r N o where
  length := (b.nextDAG q).length
  program := (b.nextDAG q).program
  original := b.retain q ∘ b.original
  h := b.retain q ∘ b.h
  g := b.retain q ∘ b.g
  omega := b.retain q ∘ b.omega
  cache := b.cache.map (fun c => c.map (b.retain q)) ++ [⟨q,(b.nextDAG q).output⟩]

theorem State.retain_val {r N o : ℕ} (b : State r N o) (q : Request N) (j : Fin b.length) :
    (b.retain q j).val=j.val :=
  UniformRankKernelPreparation.spectrumRetained_val _ _ _ _ _

theorem State.extend_old {r N o : ℕ} (b : State r N o) (q : Request N)
    (roots : Fin r → ℂ) (j : Fin b.length) :
    (b.extend q).program.eval roots (b.retain q j)=b.program.eval roots j :=
  UniformRankKernelPreparation.spectrumBank_old _ _ _ _ _ _

theorem State.extend_admissible {r N o : ℕ} (b : State r N o) (q : Request N)
    (roots : Fin r → ℂ) (hb : b.program.Admissible roots) :
    (b.extend q).program.Admissible roots :=
  UniformRankKernelPreparation.spectrumBank_admissible _ _ _ _ _ hb

theorem State.extend_counts {r N o : ℕ} (b : State r N o) (q : Request N) :
    (b.extend q).program.rootReads=b.program.rootReads ∧
    (b.extend q).program.divisions=b.program.divisions :=
  UniformRankKernelPreparation.spectrumBank_counts _ _ _ _

def State.Inputs {r N o : ℕ} (b : State r N o) (roots : Fin r → ℂ) (h g : ℕ → ℂ) : Prop :=
  (∀ i, b.program.eval roots (b.h i)=h i.val) ∧
  (∀ i, b.program.eval roots (b.g i)=g i.val) ∧
  ∀ i, b.program.eval roots (b.omega i)=OAI.ExactFourier.zeta (UniformRadixTwoDAG.width i.val)

theorem State.extend_inputs {r N o : ℕ} (b : State r N o) (q : Request N)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) (hb : b.Inputs roots h g) :
    (b.extend q).Inputs roots h g := by
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_⟩
  · exact (b.extend_old q roots (b.h i)).trans (hb.1 i)
  · exact (b.extend_old q roots (b.g i)).trans (hb.2.1 i)
  · exact (b.extend_old q roots (b.omega i)).trans (hb.2.2 i)

noncomputable def Request.bank {N : ℕ} (q : Request N) (h g : ℕ → ℂ) :
    Fin (UniformToeplitzCrossDAG.bankSize q.k) → ℂ :=
  UniformToeplitzCrossDAG.sharedBank q.k
    (UniformToeplitzCrossDAG.rankKernels q.k q.a q.e
      (fun i j => OAI.ExactFourier.ToeplitzLayers.cross q.s h g (q.i₀+i) (q.j₀+j))
      (fun i => -h (q.i₀+i-q.s)) (fun j => g (q.s-(q.j₀+j))))

def Cached.Good {r N l : ℕ} (c : Cached N l) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) : Prop :=
  ∀ j, p.eval roots (c.refs j)=c.request.bank h g j

def State.CachesGood {r N o : ℕ} (b : State r N o) (roots : Fin r → ℂ) (h g : ℕ → ℂ) : Prop :=
  ∀ c ∈ b.cache, c.Good b.program roots h g

theorem State.extend_cache_good {r N o : ℕ} (b : State r N o) (q : Request N)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) (ha : b.program.Admissible roots)
    (hi : b.Inputs roots h g) (hc : b.CachesGood roots h g) :
    (b.extend q).CachesGood roots h g := by
  intro c hmem j
  change c ∈ b.cache.map (fun c => c.map (b.retain q)) ++ [⟨q,(b.nextDAG q).output⟩] at hmem
  rcases List.mem_append.mp hmem with hm|hm
  · obtain ⟨c',hmem',he⟩ := List.mem_map.mp hm
    subst c
    exact (b.extend_old q roots (c'.refs j)).trans (hc c' hmem' j)
  · have he : c=⟨q,(b.nextDAG q).output⟩ := by
      rcases List.mem_cons.mp hm with he|he
      · exact he
      · exact False.elim (List.not_mem_nil he)
    subst c
    have hbank := UniformRankKernelPreparation.spectrumBank_run q.k b.dag (b.sources q)
      (b.root q) roots ha h g hi.1 hi.2.1 (hi.2.2 ⟨q.k,by have := q.k_le; omega⟩)
    exact congrFun hbank j

def nodeUnit (N : ℕ) : ℕ := 1000*(N+1)^2

theorem State.extend_length {r N o : ℕ} (b : State r N o) (q : Request N) :
    (b.extend q).length ≤ b.length+nodeUnit N := by
  have hb := UniformRankKernelPreparation.spectrumBank_length_bound q.k b.dag
    (b.sources q) (b.root q)
  have hw := q.width_le
  have hk : q.k≤8*N := (Nat.lt_two_pow_self (n:=q.k)).le.trans hw
  have hs := q.gBound
  have hm := Nat.mul_le_mul hw (show 2*q.s+3≤2*N+3 by omega)
  have ht := Nat.mul_le_mul hk hw
  change (b.nextDAG q).length ≤ _
  change (b.nextDAG q).length≤b.length+2+6*2^q.k*(2*q.s+3)+(2^q.k+1)+9*q.k*2^q.k at hb
  dsimp [nodeUnit]
  nlinarith

/-- Concrete repeated append; no recursive ancestry is recompiled. -/
def compileRequests {r N o : ℕ} (b : State r N o) : List (Request N) → State r N o
  | [] => b
  | q::qs => compileRequests (b.extend q) qs

theorem compileRequests_length {r N o : ℕ} (b : State r N o) (qs : List (Request N)) :
    (compileRequests b qs).length ≤ b.length+qs.length*nodeUnit N := by
  induction qs generalizing b with
  | nil => simp [compileRequests]
  | cons q qs ih =>
    have h := ih (b.extend q)
    have hb := b.extend_length q
    simp only [compileRequests,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem compileRequests_admissible {r N o : ℕ} (b : State r N o) (qs : List (Request N))
    (roots : Fin r → ℂ) (hb : b.program.Admissible roots) :
    (compileRequests b qs).program.Admissible roots := by
  induction qs generalizing b with
  | nil => exact hb
  | cons q qs ih => exact ih _ (b.extend_admissible q roots hb)

theorem compileRequests_inputs {r N o : ℕ} (b : State r N o) (qs : List (Request N))
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) (hb : b.Inputs roots h g) :
    (compileRequests b qs).Inputs roots h g := by
  induction qs generalizing b with
  | nil => exact hb
  | cons q qs ih => exact ih _ (b.extend_inputs q roots h g hb)

theorem compileRequests_cache_good {r N o : ℕ} (b : State r N o) (qs : List (Request N))
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) (ha : b.program.Admissible roots)
    (hi : b.Inputs roots h g) (hc : b.CachesGood roots h g) :
    (compileRequests b qs).CachesGood roots h g := by
  induction qs generalizing b with
  | nil => exact hc
  | cons q qs ih =>
    exact ih (b.extend q) (b.extend_admissible q roots ha)
      (b.extend_inputs q roots h g hi) (b.extend_cache_good q roots h g ha hi hc)

theorem compileRequests_counts {r N o : ℕ} (b : State r N o) (qs : List (Request N)) :
    (compileRequests b qs).program.rootReads=b.program.rootReads ∧
    (compileRequests b qs).program.divisions=b.program.divisions := by
  induction qs generalizing b with
  | nil => exact ⟨rfl,rfl⟩
  | cons q qs ih =>
    exact ⟨(ih (b.extend q)).1.trans (b.extend_counts q).1,
      (ih (b.extend q)).2.trans (b.extend_counts q).2⟩

theorem compileRequests_original {r N o : ℕ} (b : State r N o) (qs : List (Request N))
    (roots : Fin r → ℂ) (j : Fin o) :
    (compileRequests b qs).program.eval roots ((compileRequests b qs).original j)=
      b.program.eval roots (b.original j) := by
  induction qs generalizing b with
  | nil => rfl
  | cons q qs ih => exact (ih (b.extend q)).trans (b.extend_old q roots (b.original j))

theorem compileRequests_original_val {r N o : ℕ} (b : State r N o)
    (qs : List (Request N)) (j : Fin o) :
    ((compileRequests b qs).original j).val=(b.original j).val := by
  induction qs generalizing b with
  | nil => rfl
  | cons q qs ih => exact (ih (b.extend q)).trans (b.retain_val q (b.original j))

theorem compileRequests_cache_requests {r N o : ℕ} (b : State r N o)
    (qs : List (Request N)) :
    (compileRequests b qs).cache.map Cached.request=b.cache.map Cached.request++qs := by
  induction qs generalizing b with
  | nil => simp [compileRequests]
  | cons q qs ih =>
    rw [compileRequests,ih]
    simp [State.extend,Cached.map,List.map_map,Function.comp_def,List.append_assoc]

def preparePlan {r N o : ℕ} (b : State r N o) (P : Plan N) : State r N o :=
  compileRequests b (requests P (le_refl _))

theorem preparePlan_length {r N o : ℕ} (b : State r N o) (P : Plan N) :
    (preparePlan b P).length ≤ b.length+1000*(N+1)^4 := by
  have h := compileRequests_length b (requests P (le_refl _))
  have hc := requests_length P (le_refl _)
  have hm := Nat.mul_le_mul_right (nodeUnit N) hc
  have hp : N^2*nodeUnit N≤1000*(N+1)^4 := by
    dsimp [nodeUnit]
    have ht := Nat.mul_le_mul_right (1000*(N+1)^2) (show N^2≤(N+1)^2 by simp only [pow_two]; nlinarith)
    nlinarith [sq_nonneg (N+1)]
  change (compileRequests b (requests P (le_refl _))).length ≤ _
  omega

/-! The final conjugate replay reads inverses of existing prepared root refs.
It never appends another `.root` instruction. -/
open UniformShearPreparation

structure RootEnv (r a : ℕ) where
  env : Env r a
  supplied : Fin r → Fin env.length

def RootEnv.Good {r a : ℕ} (b : RootEnv r a) (roots : Fin r → ℂ) : Prop :=
  ∀ j, b.env.program.eval roots (b.supplied j)=roots j

def rootInitial {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) : RootEnv r a :=
  ⟨initial d,fun j => (refs j).castAdd 4⟩

theorem rootInitial_good {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (hr : ∀ j, d.program.eval roots (refs j)=roots j) :
    (rootInitial d refs).Good roots := by
  intro j
  change (initial d).program.eval roots ((refs j).castSucc.castSucc.castSucc.castSucc)=_
  simpa [initial,Program.eval] using hr j

def rootAppend {r a : ℕ} (b : RootEnv r a) (j : Fin r) : RootEnv r a :=
  let p := b.env.push (.divide b.env.one (b.supplied j))
  ⟨{p with inverseRoots := Function.update p.inverseRoots j (Fin.last b.env.length)},
    fun l => (b.supplied l).castSucc⟩

theorem rootAppend_length {r a : ℕ} (b : RootEnv r a) (j : Fin r) :
    (rootAppend b j).env.length=b.env.length+1 := rfl

theorem rootAppend_good {r a : ℕ} (b : RootEnv r a) (j : Fin r)
    (roots : Fin r → ℂ) (hb : b.Good roots) : (rootAppend b j).Good roots := by
  intro l
  exact (Env.push_old _ _ _ _).trans (hb l)

theorem rootAppend_envGood {r a : ℕ} (b : RootEnv r a) (j : Fin r)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hb : b.env.Good roots mu) :
    (rootAppend b j).env.Good roots mu := Env.good_push _ _ _ _ hb

theorem rootAppend_inverse {r a : ℕ} (b : RootEnv r a) (j l : Fin r)
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hb : b.Good roots) (he : b.env.Good roots mu) :
    (rootAppend b j).env.program.eval roots ((rootAppend b j).env.inverseRoots l)=
      if l=j then (roots l)⁻¹ else b.env.program.eval roots (b.env.inverseRoots l) := by
  by_cases h : l=j
  · subst l
    have hj := hb j
    simp [rootAppend,Env.push,Instruction.eval,hj,he.2.2.1]
  · simp [rootAppend,Env.push,h]

theorem rootAppend_admissible {r a : ℕ} (b : RootEnv r a) (j : Fin r)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1) (hb : b.Good roots)
    (ha : b.env.program.Admissible roots) : (rootAppend b j).env.program.Admissible roots := by
  refine ⟨ha,?_⟩
  change b.env.program.eval roots (b.supplied j)≠0
  rw [hb j]
  exact unit_ne_zero roots unit j

def rootAppends {r a : ℕ} (b : RootEnv r a) : List (Fin r) → RootEnv r a
  | [] => b
  | j::js => rootAppends (rootAppend b j) js

theorem rootAppends_length {r a : ℕ} (b : RootEnv r a) (js : List (Fin r)) :
    (rootAppends b js).env.length=b.env.length+js.length := by
  induction js generalizing b with
  | nil => simp [rootAppends]
  | cons j js ih => rw [rootAppends,ih,rootAppend_length];simp;omega

theorem rootAppends_good {r a : ℕ} (b : RootEnv r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (hb : b.Good roots) : (rootAppends b js).Good roots := by
  induction js generalizing b with
  | nil => exact hb
  | cons j js ih => exact ih _ (rootAppend_good _ _ _ hb)

theorem rootAppends_envGood {r a : ℕ} (b : RootEnv r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (he : b.env.Good roots mu) :
    (rootAppends b js).env.Good roots mu := by
  induction js generalizing b with
  | nil => exact he
  | cons j js ih => exact ih _ (rootAppend_envGood _ _ _ _ he)

theorem rootAppends_inverse {r a : ℕ} (b : RootEnv r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (mu : Fin a → ℂ) (hb : b.Good roots) (he : b.env.Good roots mu)
    (l : Fin r) :
    (rootAppends b js).env.program.eval roots ((rootAppends b js).env.inverseRoots l)=
      if l∈js then (roots l)⁻¹ else b.env.program.eval roots (b.env.inverseRoots l) := by
  induction js generalizing b with
  | nil => simp [rootAppends]
  | cons j js ih =>
    rw [rootAppends,ih _ (rootAppend_good _ _ _ hb) (rootAppend_envGood _ _ _ _ he),
      rootAppend_inverse _ _ _ _ _ hb he]
    by_cases h : l=j <;> by_cases ht : l∈js <;> simp [List.mem_cons,h,ht]

theorem rootAppends_admissible {r a : ℕ} (b : RootEnv r a) (js : List (Fin r))
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1) (hb : b.Good roots)
    (ha : b.env.program.Admissible roots) : (rootAppends b js).env.program.Admissible roots := by
  induction js generalizing b with
  | nil => exact ha
  | cons j js ih =>
    exact ih _ (rootAppend_good _ _ _ hb) (rootAppend_admissible _ _ _ unit hb ha)

def suppliedBase {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) : Env r a :=
  (rootAppends (rootInitial d refs) (List.finRange r)).env

theorem suppliedBase_length {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) :
    (suppliedBase d refs).length=d.length+4+r := by
  simp [suppliedBase,rootAppends_length,rootInitial,initial]

theorem suppliedBase_good {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) : (suppliedBase d refs).Good roots (fun j => d.program.eval roots (d.output j)) :=
  rootAppends_envGood _ _ _ _ (initial_good _ _)

theorem suppliedBase_rootsGood {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (hr : ∀ j, d.program.eval roots (refs j)=roots j) :
    (suppliedBase d refs).RootsGood roots := by
  intro j
  simpa [suppliedBase] using rootAppends_inverse (rootInitial d refs) (List.finRange r)
    roots _ (rootInitial_good _ _ _ hr) (initial_good _ _) j

theorem suppliedBase_admissible {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) (hd : d.Admissible roots) :
    (suppliedBase d refs).program.Admissible roots :=
  rootAppends_admissible _ _ _ unit (rootInitial_good _ _ _ hr) (initial_admissible _ _ hd)

def suppliedInitialScale {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) : ScaleEnv r a :=
  let q := replay d.program (suppliedBase d refs)
  {env := q.env,conjugate := fun j => q.refs (d.output j),rows := fun _ _ => q.env.zero}

theorem suppliedInitialScale_good {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) :
    (suppliedInitialScale d refs).Good roots (fun j => d.program.eval roots (d.output j)) := by
  refine ⟨replay_good _ _ _ _ (suppliedBase_good _ _ _),?_⟩
  intro j
  change (replay d.program (suppliedBase d refs)).env.program.eval roots
    ((replay d.program (suppliedBase d refs)).refs (d.output j))=_
  rw [replay_eval _ _ roots _ (suppliedBase_good _ _ _) (suppliedBase_rootsGood _ _ _ hr),
    d.program.eval_inverse_roots roots unit]

theorem suppliedInitialScale_admissible {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) (hd : d.Admissible roots) :
    (suppliedInitialScale d refs).env.program.Admissible roots :=
  replay_admissible _ _ roots _ (suppliedBase_good _ _ _) (suppliedBase_rootsGood _ _ _ hr)
    (suppliedBase_admissible _ _ _ unit hr hd) ((d.admissible_inverse_roots roots unit).mpr hd)

def suppliedComplete {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) : ScaleEnv r a :=
  scaleSteps (suppliedInitialScale d refs) (List.finRange a)

theorem suppliedComplete_length {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) :
    (suppliedComplete d refs).env.length=2*d.length+r+7*a+4 := by
  rw [suppliedComplete,scaleSteps_length,List.length_finRange]
  change (replay d.program (suppliedBase d refs)).env.length+7*a=_
  rw [replay_length,suppliedBase_length]
  omega

theorem suppliedComplete_good {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) :
    (suppliedComplete d refs).Good roots (fun j => d.program.eval roots (d.output j)) :=
  scaleSteps_good _ _ _ _ (suppliedInitialScale_good _ _ _ unit hr)

theorem suppliedComplete_rows {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) (j : Fin a) (q : Fin 6) :
    (suppliedComplete d refs).env.program.eval roots ((suppliedComplete d refs).rows j q)=
      rowExpected (d.program.eval roots (d.output j)) q := by
  simpa [suppliedComplete] using scaleSteps_rows (suppliedInitialScale d refs) (List.finRange a)
    roots _ (suppliedInitialScale_good _ _ _ unit hr) j q

theorem suppliedComplete_admissible {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, d.program.eval roots (refs j)=roots j) (hd : d.Admissible roots) :
    (suppliedComplete d refs).env.program.Admissible roots :=
  scaleSteps_admissible _ _ _ _ (suppliedInitialScale_good _ _ _ unit hr)
    (suppliedInitialScale_admissible _ _ _ unit hr hd)

theorem rootAppend_count {r a : ℕ} (kind : CountKind) (b : RootEnv r a) (j : Fin r) :
    programCount kind (rootAppend b j).env.program=programCount kind b.env.program+
      if kind=.rootRead then 0 else 1 := by
  cases kind <;> simp [rootAppend,Env.push,programCount,instructionCount]

theorem rootAppends_count {r a : ℕ} (kind : CountKind) (b : RootEnv r a) (js : List (Fin r)) :
    programCount kind (rootAppends b js).env.program=programCount kind b.env.program+
      if kind=.rootRead then 0 else js.length := by
  induction js generalizing b with
  | nil => cases kind <;> simp [rootAppends]
  | cons j js ih =>
    rw [rootAppends,ih,rootAppend_count]
    cases kind <;> simp; omega

theorem suppliedComplete_rootReads {r a : ℕ} (d : DAG r a) (refs : Fin r → Fin d.length) :
    programCount .rootRead (suppliedComplete d refs).env.program=programCount .rootRead d.program := by
  rw [suppliedComplete,scaleSteps_count]
  change programCount .rootRead (replay d.program (suppliedBase d refs)).env.program+_=_
  rw [replay_count]
  change programCount .rootRead (rootAppends (rootInitial d refs) (List.finRange r)).env.program+_=_
  rw [rootAppends_count]
  change programCount .rootRead (initial d).program+_=_
  rw [initial_count]
  simp

open UniformRankKernelPreparation

/-- Both signs of all old registers, plus rational zero and one. No scalar test. -/
def signedExpr (l : ℕ) (j : Fin ((l+2)*2)) : Expr (l+2) :=
  let q := (finProdFinEquiv : Fin (l+2) × Fin 2 ≃ Fin ((l+2)*2)).symm j
  if q.2.val=0 then .ref q.1 else .sub (.ref (zeroRef l)) (.ref q.1)

def signedDAG {r l : ℕ} (p : Program r l) : DAG r ((l+2)*2) :=
  family (initialProgram p) id (signedExpr l)

def signedRef (l : ℕ) (j : Fin (l+2)) (sign : Fin 2) : Fin ((l+2)*2) :=
  finProdFinEquiv (j,sign)

def signedRetained {r l : ℕ} (p : Program r l) (j : Fin l) : Fin (signedDAG p).length :=
  (compileList (initialProgram p) id (List.ofFn (signedExpr l))).old (j.castAdd 2)

theorem signedRetained_val {r l : ℕ} (p : Program r l) (j : Fin l) :
    (signedRetained p j).val=j.val := compileList_old_val _ _ _ _

theorem signedDAG_old {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ) (j : Fin l) :
    (signedDAG p).program.eval roots (signedRetained p j)=p.eval roots j :=
  (compileList_old _ _ _ roots _).trans (initial_old _ _ _)

theorem signedDAG_value {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ)
    (j : Fin (l+2)) (sign : Fin 2) :
    (signedDAG p).program.eval roots ((signedDAG p).output (signedRef l j sign))=
      if sign.val=0 then (initialProgram p).eval roots j else -(initialProgram p).eval roots j := by
  rw [signedDAG,family_output]
  simp only [signedExpr,signedRef,Equiv.symm_apply_apply]
  by_cases hs : sign.val=0 <;> simp [hs,Expr.eval]

theorem signedDAG_admissible {r l : ℕ} (p : Program r l) (roots : Fin r → ℂ)
    (hp : p.Admissible roots) : (signedDAG p).Admissible roots :=
  compileList_admissible _ _ _ roots (initial_admissible _ _ hp)

theorem signedDAG_counts {r l : ℕ} (p : Program r l) :
    (signedDAG p).program.rootReads=p.rootReads ∧ (signedDAG p).program.divisions=p.divisions := by
  have hc := compileList_counts (List.ofFn (signedExpr l)) (initialProgram p) id
  have hi := UniformRankKernelPreparation.initial_counts p
  exact ⟨hc.1.trans hi.1,hc.2.trans hi.2⟩

theorem signedDAG_length {r l : ℕ} (p : Program r l) : (signedDAG p).length≤3*l+6 := by
  change (compileList (initialProgram p) id (List.ofFn (signedExpr l))).length≤_
  rw [compileList_length,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_def]
  have h : (∑ j : Fin ((l+2)*2), (signedExpr l j).work)≤∑ _j : Fin ((l+2)*2),1 := by
    apply Finset.sum_le_sum
    intro j _
    dsimp only [signedExpr]
    split_ifs <;> simp [Expr.work]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at h
  omega

theorem rootCount_eq {r l : ℕ} (p : Program r l) : programCount .rootRead p=p.rootReads := by
  induction p with
  | nil => rfl
  | step p i ih => cases i <;> simp [programCount,instructionCount,Program.rootReads,Instruction.rootReads,ih]

/-- One joint signed bank, one conjugate replay, one set of six-C scale rows. -/
def finish {r N o : ℕ} (b : State r N o) (roots : Fin r → Fin b.length) :
    ScaleEnv r ((b.length+2)*2) :=
  suppliedComplete (signedDAG b.program) (fun j => signedRetained b.program (roots j))

theorem finish_length {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length) :
    (finish b refs).env.length≤20*b.length+r+44 := by
  rw [finish,suppliedComplete_length]
  have h := signedDAG_length b.program
  omega

theorem finish_admissible {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1) (ha : b.program.Admissible roots)
    (hr : ∀ j, b.program.eval roots (refs j)=roots j) :
    (finish b refs).env.program.Admissible roots :=
  suppliedComplete_admissible _ _ roots unit (fun j => (signedDAG_old _ _ _).trans (hr j))
    (signedDAG_admissible _ _ ha)

theorem finish_rootReads {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length) :
    (finish b refs).env.program.rootReads=b.program.rootReads := by
  rw [←rootCount_eq,finish,suppliedComplete_rootReads,rootCount_eq]
  exact (signedDAG_counts _).1

def finishIndex {r N o : ℕ} (b : State r N o) (j : Fin b.length) (sign : Fin 2) :
    Fin ((b.length+2)*2) := signedRef b.length (j.castAdd 2) sign

theorem finish_value {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, b.program.eval roots (refs j)=roots j) (j : Fin b.length) (sign : Fin 2) :
    (finish b refs).env.program.eval roots ((finish b refs).env.mu (finishIndex b j sign))=
      if sign.val=0 then b.program.eval roots j else -b.program.eval roots j := by
  rw [finish]
  rw [(suppliedComplete_good (signedDAG b.program) _ roots unit
    (fun j => (signedDAG_old _ _ _).trans (hr j))).1.1]
  dsimp only [finishIndex]
  rw [signedDAG_value,initial_old]

theorem finish_scales {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, b.program.eval roots (refs j)=roots j) (j : Fin b.length) (sign : Fin 2) (q : Fin 6) :
    (finish b refs).env.program.eval roots ((finish b refs).rows (finishIndex b j sign) q)=
      rowExpected (if sign.val=0 then b.program.eval roots j else -b.program.eval roots j) q := by
  rw [finish,suppliedComplete_rows _ _ roots unit
    (fun j => (signedDAG_old _ _ _).trans (hr j))]
  dsimp only [finishIndex]
  rw [signedDAG_value,initial_old]

theorem finish_scales_ne_zero {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, b.program.eval roots (refs j)=roots j) (j : Fin b.length) (sign : Fin 2) (q : Fin 6) :
    (finish b refs).env.program.eval roots ((finish b refs).rows (finishIndex b j sign) q)≠0 := by
  rw [finish_scales _ _ _ unit hr]
  exact rowExpected_ne_zero _ _

def finishPlan {r N o : ℕ} (b : State r N o) (P : Plan N)
    (refs : Fin r → Fin o) : ScaleEnv r (((preparePlan b P).length+2)*2) :=
  finish (preparePlan b P) (fun j => (preparePlan b P).original (refs j))

theorem finishPlan_length {r N o : ℕ} (b : State r N o) (P : Plan N) (refs : Fin r → Fin o) :
    (finishPlan b P refs).env.length≤20*b.length+20000*(N+1)^4+r+44 := by
  have h := finish_length (preparePlan b P) (fun j => (preparePlan b P).original (refs j))
  have hp := preparePlan_length b P
  change (finish (preparePlan b P) _).env.length≤_
  omega

theorem finishPlan_rootReads {r N o : ℕ} (b : State r N o) (P : Plan N) (refs : Fin r → Fin o) :
    (finishPlan b P refs).env.program.rootReads=b.program.rootReads := by
  rw [finishPlan,finish_rootReads]
  exact (compileRequests_counts b _).1

theorem finishPlan_admissible {r N o : ℕ} (b : State r N o) (P : Plan N) (refs : Fin r → Fin o)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1) (ha : b.program.Admissible roots)
    (hr : ∀ j, b.program.eval roots (b.original (refs j))=roots j) :
    (finishPlan b P refs).env.program.Admissible roots :=
  finish_admissible _ _ roots unit (compileRequests_admissible b _ roots ha)
    (fun j => (compileRequests_original b _ roots (refs j)).trans (hr j))

theorem finish_cached_scale {r N o : ℕ} (b : State r N o) (refs : Fin r → Fin b.length)
    (roots : Fin r → ℂ) (unit : ∀ j, ‖roots j‖=1)
    (hr : ∀ j, b.program.eval roots (refs j)=roots j)
    (h g : ℕ → ℂ) (hc : b.CachesGood roots h g) (c : Cached N b.length) (hm : c∈b.cache)
    (j : Fin (UniformToeplitzCrossDAG.bankSize c.request.k)) (sign : Fin 2) (q : Fin 6) :
    (finish b refs).env.program.eval roots ((finish b refs).rows (finishIndex b (c.refs j) sign) q)=
      rowExpected (if sign.val=0 then c.request.bank h g j else -c.request.bank h g j) q := by
  rw [finish_scales _ _ _ unit hr,hc c hm j]

/-- An actual reciprocal-series build supplies BOTH coefficient banks. Existing
FFT root registers remain a finite, explicit caller table, not root leaves. -/
def seed {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length) :
    State r (n+1) (UniformReciprocalPreparation.build d n (le_refl _)).length :=
  let b := UniformReciprocalPreparation.build d n (le_refl _)
  ⟨b.length,b.program,id,b.h,b.g,omega,[]⟩

theorem seed_length {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length) :
    (seed d omega).length=d.length+n*n+3*n+3 := UniformReciprocalPreparation.build_length _ _ _

theorem seed_admissible {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length)
    (roots : Fin r → ℂ) (hd : d.Admissible roots)
    (hzero : d.program.eval roots (d.output 0)≠0) : (seed d omega).program.Admissible roots :=
  UniformReciprocalPreparation.build_admissible _ _ _ _ hd hzero

theorem seed_inputs {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length)
    (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (hd : ∀ j, d.program.eval roots (d.output j)=PowerSeries.coeff j.val f)
    (homega : ∀ j, (UniformReciprocalPreparation.build d n (le_refl _)).program.eval roots (omega j)=
      OAI.ExactFourier.zeta (UniformRadixTwoDAG.width j.val)) :
    (seed d omega).Inputs roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) := by
  have hb := UniformReciprocalPreparation.build_correct d n (le_refl _) roots f hd
  exact ⟨hb.1,hb.2.1,homega⟩

theorem seed_cachesGood {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) : (seed d omega).CachesGood roots h g := by
  intro c hc
  exact False.elim (List.not_mem_nil hc)

theorem prepared_seed_cachesGood {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length)
    (P : Plan (n+1)) (roots : Fin r → ℂ) (f : PowerSeries ℂ)
    (ha : d.Admissible roots) (hzero : d.program.eval roots (d.output 0)≠0)
    (hd : ∀ j, d.program.eval roots (d.output j)=PowerSeries.coeff j.val f)
    (homega : ∀ j, (UniformReciprocalPreparation.build d n (le_refl _)).program.eval roots (omega j)=
      OAI.ExactFourier.zeta (UniformRadixTwoDAG.width j.val)) :
    (preparePlan (seed d omega) P).CachesGood roots (PowerSeries.coeff · f) (PowerSeries.coeff · f⁻¹) :=
  compileRequests_cache_good _ _ _ _ _ (seed_admissible _ _ _ ha hzero)
    (seed_inputs _ _ _ _ hd homega) (seed_cachesGood _ _ _ _ _)

theorem cached_cross_action {r N l : ℕ} (c : Cached N l) (p : Program r l)
    (roots : Fin r → ℂ) (h g : ℕ → ℂ) (hc : c.Good p roots h g) (x : Fin c.request.e → ℂ) :
    (printedCross c.request.a c.request.e).eval (fun j => p.eval roots (c.refs j)) x=
      Matrix.mulVec (fun i : Fin c.request.a => fun j : Fin c.request.e =>
        OAI.ExactFourier.ToeplitzLayers.cross c.request.s h g
          (c.request.i₀+i.val) (c.request.j₀+j.val)) x := by
  change (UniformToeplitzCrossDAG.crossDAG c.request.k c.request.a c.request.e
    (by rw [UniformRadixTwoDAG.width_eq,Request.k]; have := no_alias c.request.a c.request.e; omega)
    (by rw [UniformRadixTwoDAG.width_eq,Request.k]; have := no_alias c.request.a c.request.e; omega)).eval
    (fun j => p.eval roots (c.refs j)) x=_
  rw [funext hc]
  exact UniformToeplitzCrossDAG.toeplitz_cross_eval c.request.k c.request.s
    c.request.a c.request.e c.request.i₀ c.request.j₀ c.request.positive
    c.request.sourcePositive (by rw [UniformRadixTwoDAG.width_eq,Request.k]; exact no_alias _ _)
    h g c.request.interior c.request.sourceBound x

theorem finishPlan_references {r N o : ℕ} (b : State r N o) (P : Plan N) (refs : Fin r → Fin o) :
    referencesBound (20*b.length+20000*(N+1)^4+r+44) (finishPlan b P refs).env.program :=
  referencesBound_of_length _ (by omega) (finishPlan_length _ _ _)

theorem finish_seed_length {r n : ℕ} (d : DAG r (n+1))
    (omega : Fin (Nat.clog 2 (n+1)+3) → Fin (UniformReciprocalPreparation.build d n (le_refl _)).length)
    (P : Plan (n+1)) (refs : Fin r → Fin (seed d omega).length) :
    (finishPlan (seed d omega) P refs).env.length≤
      20*(d.length+n*n+3*n+3)+20000*(n+2)^4+r+44 := by
  simpa only [seed_length,Nat.add_assoc] using finishPlan_length (seed d omega) P refs

/-- The Newton `1/H_j` table and its SERIES reciprocal share one actual prefix.
The FFT references below must already exist in that prefix; extracting them
from a larger master-root prefix is a separate adapter obligation. -/
def newtonSeed (n : ℕ)
    (omega : Fin (Nat.clog 2 (n+1)+3) →
      Fin (UniformReciprocalPreparation.build (UniformReciprocalPreparation.newtonInput n) n (le_refl _)).length) :=
  seed (UniformReciprocalPreparation.newtonInput n) omega

theorem newtonSeed_admissible (n : ℕ)
    (omega : Fin (Nat.clog 2 (n+1)+3) →
      Fin (UniformReciprocalPreparation.build (UniformReciprocalPreparation.newtonInput n) n (le_refl _)).length)
    (w : ℂ) (hw : IsPrimitiveRoot w (n+1)) :
    (newtonSeed n omega).program.Admissible (UniformNewton.Preparation.roots w) :=
  seed_admissible _ _ _ (UniformReciprocalPreparation.newtonInput_admissible hw)
    (UniformReciprocalPreparation.newtonInput_zero n w)

theorem newtonSeed_inputs (n : ℕ)
    (omega : Fin (Nat.clog 2 (n+1)+3) →
      Fin (UniformReciprocalPreparation.build (UniformReciprocalPreparation.newtonInput n) n (le_refl _)).length)
    (w : ℂ)
    (homega : ∀ j, (newtonSeed n omega).program.eval (UniformNewton.Preparation.roots w) (omega j)=
      OAI.ExactFourier.zeta (UniformRadixTwoDAG.width j.val)) :
    (newtonSeed n omega).Inputs (UniformNewton.Preparation.roots w)
      (PowerSeries.coeff · (OAI.ExactFourier.NewtonFourier.invH w))
      (PowerSeries.coeff · (OAI.ExactFourier.NewtonFourier.invH w)⁻¹) :=
  seed_inputs _ _ _ _ (UniformReciprocalPreparation.newtonInput_coeff n w) homega

end ExactFourierCircuits.UniformLocalPreparationDAG
