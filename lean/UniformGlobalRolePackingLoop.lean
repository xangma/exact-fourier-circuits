import UniformGlobalRolePackingMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalRolePackingMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformSectorPackingMachine (PhysicalAxis Rows Widths Permutations)
noncomputable section

lemma NatOutside.refl {W : ℕ} (g : Geometry W) (s : State) : NatOutside g s s := fun _ _ _ _ => rfl
lemma NatOutside.trans {W : ℕ} {g : Geometry W} {s t u : State}
 (h : NatOutside g s t) (k : NatOutside g t u) : NatOutside g s u :=
 fun q h0 h1 h2 => (k q h0 h1 h2).trans (h q h0 h1 h2)
lemma NatOutside.prefix {W : ℕ} {g : Geometry W} {s t : State} (h : NatOutside g s t) :
 ∀ q,q < g.suffix → t.natHeap q=s.natHeap q := by
 intro q hq
 exact h q (Or.inl hq) (Or.inl (by have := g.suffixBelow;omega))
  (Or.inl (by have := g.suffixBelow;have := g.stackBelow;omega))
lemma banks_transfer {W : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hlen : as.length=g.ell) {s t : State} (h : Banks g as s) (out : NatOutside g s t)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ g.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ g.suffix) : Banks g as t := by
 have low := out.prefix
 let scratchLayout : UniformSectorPackingMachine.Layout := {
  B := g.B,ell := g.ell,rows := g.rows,suffix := g.suffix,stack := g.stack,inverse := g.inverse,
  source := 0,destination := 0,total := 0,
  code := by have := g.code;omega,
  rowsBelow := g.rowsBelow,suffixBelow := g.suffixBelow,stackBelow := g.stackBelow,
  inverseBound := by have := g.inverseFit;omega,
  sourceBelow := by omega,destinationBound := by omega,volumeBound := by omega }
 refine ⟨UniformSectorPackingMachine.rows_transfer as 0 scratchLayout s t (by change 0+as.length ≤ g.ell;omega) h.1 low,
  UniformSectorPackingMachine.widths_transfer as scratchLayout s t h.2.1 widthsBelow low,?_⟩
 intro a ha j
 exact (low _ (by have := permutationsBelow a ha;have := j.isLt;omega)).trans (h.2.2 a ha j)

lemma source_transfer {W : ℕ} (g : Geometry W) {i : Fin W} {s t : State}
 {v : ℕ → Fin g.volume → Scalar} (h : Source g v s)
 (out : ∀ q,q < g.destination+i.val*g.volume ∨ g.destination+(i.val+1)*g.volume ≤ q →
  t.scalarHeap q=s.scalarHeap q) : Source g v t := by
 intro r hr j
 have rbound := Nat.mul_le_mul_right g.volume (show r+1 ≤ W by omega)
 have before : g.source+r*g.volume+j.val < g.destination+i.val*g.volume := by
  have := g.sourceBelow;have := j.isLt;nlinarith
 exact (out _ (Or.inl before)).trans (h r hr j)

lemma preserve_filled {W : ℕ} (g : Geometry W) (p : Equiv.Perm (Fin g.volume))
 (v : ℕ → Fin g.volume → Scalar) (i : Fin W) {s t : State}
 (old : Filled g p v i.val s)
 (fresh : ∀ j:Fin g.volume,t.scalarHeap (g.destination+i.val*g.volume+j.val)=some (v i.val (p j)))
 (out : ∀ q,q < g.destination+i.val*g.volume ∨ g.destination+(i.val+1)*g.volume ≤ q →
  t.scalarHeap q=s.scalarHeap q) : Filled g p v (i.val+1) t := by
 intro r hr j
 by_cases same : r=i.val
 · subst r;exact fresh j
 · have less : r < i.val := by omega
   have rb := Nat.mul_le_mul_right g.volume (show r+1 ≤ i.val by omega)
   exact (out _ (Or.inl (by have := j.isLt;nlinarith))).trans (old r less j)

lemma scalar_outside {W : ℕ} (g : Geometry W) (i : Fin W) {s t : State}
 (out : ∀ q,q < g.destination+i.val*g.volume ∨ g.destination+(i.val+1)*g.volume ≤ q →
  t.scalarHeap q=s.scalarHeap q) : ScalarOutside g s t := by
 intro q hq
 apply out q
 rcases hq with before|after
 · exact Or.inl (by omega)
 · have fit : (i.val+1)*g.volume ≤ W*g.volume := by
     simpa only [Nat.succ_eq_add_one] using Nat.mul_le_mul_right g.volume (Nat.succ_le_of_lt i.isLt)
   exact Or.inr (by omega)

/-- Every complete physical role uses the same literal137 inside the same
literal153. There is no host iteration, table callback, transform hypothesis,
or generated inverse-address bank premise. -/
theorem loop {W n : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hvolume : UniformSectorPackingMachine.physicalVolume as=g.volume) (hlen : as.length=g.ell)
 (v : ℕ → Fin g.volume → Scalar) (x : Fin n → ℂ)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ g.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ g.suffix)
 (remaining : ℕ) :
 ∀ i s,i ≤ W → W-i=remaining → s.pc=4 → WordBound g.B s → Cursor g i s → Banks g as s →
  Source g v s → Filled g (permutation g as hvolume) v i s →
 ∃ u ticks,BoundedExecution (programFor W) n x g.B s ticks u ∧
  ticks ≤ remaining*(213*g.volume+31)+2 ∧ u.pc=152 ∧
  Filled g (permutation g as hvolume) v W u ∧ Frame s u ∧ NatOutside g s u ∧ ScalarOutside g s u := by
 induction remaining with
 | zero =>
   intro i s le eq pc wb cursor banks source filled
   have equal : i=W := by omega
   let u := setPC s 152
   have ub := changePC_bound g.B s 152 wb (by have := g.code;omega)
   have first : BoundedRuns (programFor W) n x g.B s 1 u := .next wb
    (by simp [step,pc,branch_at,cursor.index,cursor.roles,equal,u,setPC]) (.refl ub)
   have stop : BoundedExecution (programFor W) n x g.B u 1 u :=
    .halt ub (by simp [step,u,setPC,halt_at])
   refine ⟨u,2,by simpa using first.executes stop,by omega,rfl,?_,Frame.refl s,NatOutside.refl g s,?_⟩
   · intro r hr j
     exact filled r (by omega) j
   · intro _ _;rfl
 | succ remaining ih =>
   intro i s le eq pc wb cursor banks source filled
   have lt : i < W := by omega
   let role : Fin W := ⟨i,lt⟩
   obtain ⟨t,ticks,first,cost,tp,fresh,next,frame,nat,out⟩ :=
    iteration g as hvolume hlen v x s role cursor banks widthsBelow permutationsBelow source pc wb
   have keptBanks := banks_transfer g as hlen banks nat widthsBelow permutationsBelow
   have keptSource := source_transfer g source out
   have nextFilled := preserve_filled g (permutation g as hvolume) v role filled fresh out
   obtain ⟨u,rest,last,lastCost,up,done,lastFrame,lastNat,lastOut⟩ := ih (i+1) t
    (by omega) (by omega) tp first.final_bound next keptBanks keptSource nextFilled
   refine ⟨u,ticks+rest,first.executes last,?_,up,done,frame.trans lastFrame,nat.trans lastNat,?_⟩
   · have total : (remaining+1)*(213*g.volume+31)+2 =
      (213*g.volume+31)+(remaining*(213*g.volume+31)+2) := by ring
     rw [total]
     omega
   · intro q hq
     exact (lastOut q hq).trans (scalar_outside g role out q hq)

lemma boot_cursor {W : ℕ} {g : Geometry W} {s : State} (h : Header g s) :
 Cursor g 0 (applyBlock (boot W) s) := by
 constructor
 · constructor <;> simp [boot,applyBlock,Op.apply,writeNat,next,h.volume,h.source,h.destination,
    h.axes,h.rows,h.suffix,h.stack,h.inverse]
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next]

theorem execution {W n : ℕ} (g : Geometry W) (as : List PhysicalAxis)
 (hvolume : UniformSectorPackingMachine.physicalVolume as=g.volume) (hlen : as.length=g.ell)
 (v : ℕ → Fin g.volume → Scalar) (x : Fin n → ℂ) (s : State)
 (header : Header g s) (banks : Banks g as s)
 (widthsBelow : ∀ a ∈ as,a.widthsBase+a.geometry.widths.length ≤ g.suffix)
 (permutationsBelow : ∀ a ∈ as,a.permutationBase+a.geometry.widths.sum ≤ g.suffix)
 (source : Source g v s) (pc : s.pc=0) (wb : WordBound g.B s) :
 ∃ u ticks,BoundedExecution (programFor W) n x g.B s ticks u ∧
  ticks ≤ W*(213*g.volume+31)+6 ∧ u.pc=152 ∧
  Filled g (permutation g as hvolume) v W u ∧ Frame s u ∧ NatOutside g s u ∧ ScalarOutside g s u := by
 have safe : readable (boot W) s ∧ peak (boot W) s ≤ g.B := by
  simp [boot,readable,peak,Op.readable,Op.peak]
  have := g.code;have := g.roles;omega
 have first := block_runs (boot W) (programFor W) 0 n g.B x s (boot_code W) pc wb
  (by rw [boot_length];have := g.code;omega) safe.1 safe.2
 let b := applyBlock (boot W) s
 have bp : b.pc=4 := by rw [applyBlock_pc,boot_length,pc]
 have lowBanks : Banks g as b := by
  have nat : NatOutside g s b := fun _ _ _ _ => rfl
  exact banks_transfer g as hlen banks nat widthsBelow permutationsBelow
 have lowSource : Source g v b := source
 obtain ⟨u,ticks,rest,cost,up,done,frame,nat,out⟩ := loop g as hvolume hlen v x widthsBelow permutationsBelow
  W 0 b (by omega) (by omega) bp first.final_bound (boot_cursor header) lowBanks lowSource
  (by intro i hi;omega)
 refine ⟨u,4+ticks,?_,by omega,up,done,(boot_frame W s).trans frame,nat,out⟩
 simpa only [boot_length] using first.executes rest

end
end ExactFourierCircuits.UniformGlobalRolePackingMachine
