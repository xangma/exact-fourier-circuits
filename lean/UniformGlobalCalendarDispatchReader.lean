import UniformGlobalCalendarDispatchPlacement

set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalCalendarDispatch
open UniformMachine
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak block_runs)
noncomputable section

structure Header (A N r O T used phaseBank j : ℕ) (s : State) : Prop where
 selected : s.natReg 6766=A
 count : s.natReg 6767=N
 radix : s.natReg 6768=r
 pool : s.natReg 6769=O
 rows : s.natReg 6770=T
 usedReg : s.natReg 6771=used
 phaseBankReg : s.natReg 6772=phaseBank
 index : s.natReg 6773=j
 one : s.natReg 6774=1
 two : s.natReg 6775=2
 zero : s.natReg 6776=0

structure Descriptor where
 address : ℕ
 elapsed : ℕ
 pool : ℕ
 widthCount : ℕ
 permutation : ℕ
 kind : ℕ

def Selected (A j : ℕ) (d : Descriptor) (s : State) : Prop :=
 s.natHeap (A+2*j)=some d.address ∧ s.natHeap (A+2*j+1)=some d.elapsed

def Stored (d : Descriptor) (s : State) : Prop :=
 s.natHeap (d.address+2)=some d.pool ∧ s.natHeap (d.address+3)=some d.widthCount ∧
 s.natHeap (d.address+5)=some d.permutation ∧ s.natHeap (d.address+6)=some d.kind

structure Loaded (r : ℕ) (d : Descriptor) (s : State) : Prop where
 address : s.natReg 6778=d.address
 elapsed : s.natReg 6779=d.elapsed
 pool : s.natReg 6781=d.pool
 widthCount : s.natReg 6784=d.widthCount
 permutation : s.natReg 6783=d.permutation
 kind : s.natReg 6780=d.kind
 pairs : s.natReg 6782=r-d.widthCount

lemma readEntry_header {A N r O T used phaseBank j : ℕ} {s : State}
 (h : Header A N r O T used phaseBank j s) :
 Header A N r O T used phaseBank j (applyBlock readEntry s) := by
 constructor <;> simp [readEntry,applyBlock,Op.apply,writeNat,next,
  h.selected,h.count,h.radix,h.pool,h.rows,h.usedReg,h.phaseBankReg,h.index,h.one,h.two,h.zero]

lemma readEntry_loaded {A N r O T used phaseBank j : ℕ} {s : State} (d : Descriptor)
 (h : Header A N r O T used phaseBank j s) (selected : Selected A j d s) (stored : Stored d s) :
 Loaded r d (applyBlock readEntry s) := by
 rcases selected with ⟨address,elapsed⟩
 rcases stored with ⟨pool,width,permutation,kind⟩
 simp only [Nat.mul_comm,Nat.add_assoc] at address elapsed
 constructor <;> simp [readEntry,applyBlock,Op.apply,writeNat,next,
  h.selected,h.radix,h.index,h.one,h.two,h.zero,address,elapsed,pool,width,permutation,kind,Nat.add_assoc]

/-- Seventeen actual bounded loads/arithmetic instructions decode one selected
entry's genuine ABI fields and ordered pair-bank size. No action is assumed. -/
theorem readEntry_execution {n A N r O T used phaseBank j B : ℕ} (x : Fin n→ℂ) (s : State)
 (d : Descriptor) (h : Header A N r O T used phaseBank j s)
 (selected : Selected A j d s) (stored : Stored d s) (pc : s.pc=11) (wb : WordBound B s)
 (code : 281 ≤ B) (index : j < N) (selectionFit : A+2*N ≤ B) (entryFit : d.address+7 ≤ B) :
 BoundedRuns program n x B s 17 (applyBlock readEntry s) := by
 rcases selected with ⟨address,elapsed⟩
 rcases stored with ⟨pool,width,permutation,kind⟩
 have ad:=(wb.2.2.1 _ _ address).2
 have el:=(wb.2.2.1 _ _ elapsed).2
 have po:=(wb.2.2.1 _ _ pool).2
 have wi:=(wb.2.2.1 _ _ width).2
 have pe:=(wb.2.2.1 _ _ permutation).2
 have ki:=(wb.2.2.1 _ _ kind).2
 have radix:=(wb.2.1 6768)
 rw [h.radix] at radix
 simp only [Nat.mul_comm,Nat.add_assoc] at address elapsed
 exact block_runs readEntry program 11 n B x s readEntry_code pc wb (by change 11+17 ≤ B;omega)
  (by simp [readEntry,readable,Op.readable,Op.apply,writeNat,next,h.selected,h.index,h.one,h.two,h.zero,
    address,elapsed,pool,width,permutation,kind,Nat.add_assoc])
  (by simp [readEntry,peak,Op.peak,Op.apply,writeNat,next,h.selected,h.radix,h.index,h.one,h.two,h.zero,
    address,elapsed,pool,width,permutation,kind,Nat.add_assoc];omega)

end
end ExactFourierCircuits.UniformGlobalCalendarDispatch
