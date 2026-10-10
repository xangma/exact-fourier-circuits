import DFTModelCacheCalendarLocalPeak

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheCalendar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformLocalRectangleDescriptors UniformLocalCacheTiming UniformLocalCacheTreeMachine UniformWorkspacePlanner
open UniformLocalCacheTreeCoverage (currentRows)
open DFTModelCacheTraversal (ofList rectangleEncode)
noncomputable section
attribute [local irreducible] DFTModelCacheDescriptor.node prepare direct finish leftInput rightInput

theorem code_comp_peak {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r t u)
    (h : Handler r) (x : s.T) : (Code.run (.comp f g) h x).peak=
      max (Code.run f h x).peak (Code.run g h (Code.run f h x).val).peak := by
  change max (max _ _) 0=_
  exact max_zero _

theorem code_fork_peak {r : Port} {s t u : Ty} (f : Code false r s t) (g : Code false r s u)
    (h : Handler r) (x : s.T) : (Code.run (.fork f g) h x).peak=
      max (Code.run f h x).peak (Code.run g h x).peak := by
  change max _ (max _ 0)=_
  rw [max_zero]

theorem code_ifz_peak {r : Port} {s t : Ty} (q : Code false r s w) (f g : Code false r s t)
    (h : Handler r) (x : s.T) : (Code.run (.ifz q f g) h x).peak=
      max (Code.run q h x).peak
      (if (Code.run q h x).val=0 then (Code.run f h x).peak else (Code.run g h x).peak) := by
  change max (max (Code.run q h x).peak (if (Code.run q h x).val=0 then Code.run f h x else Code.run g h x).peak) 0=_
  split_ifs <;>simp only [max_zero]

theorem leftInput_peak (nf : NodeFrame.T) : (run leftInput nf).peak ≤ max 2 (nf.1.2.1+nf.1.1) := by
  have div:=Nat.div_le_self nf.1.1 2
  simp only [leftInput,half,nat,nodeWidth,nodeOffset,nodeStart,width,offset,start,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_le_iff]
  omega

theorem rightInput_peak (nf : NodeFrame.T) : (run rightInput nf).peak ≤ max 2 (nf.1.2.1+nf.1.1) := by
  have div:=Nat.div_le_self nf.1.1 2
  simp only [rightInput,half,nat,nodeWidth,nodeOffset,nodeStart,width,offset,start,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_le_iff]
  omega

theorem splitCode_peak (h : Handler RecPort) (nf : NodeFrame.T) (B : ℕ)
    (hb:2 ≤ B) (he:nf.1.2.1+nf.1.1 ≤ B)
    (hl:(h (nf.1.1/2,(nf.1.2.1,nf.1.2.2))).peak ≤ B)
    (hr:(h (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2))).peak ≤ B)
    (hf:(run finish (nf,((h (nf.1.1/2,(nf.1.2.1,nf.1.2.2))).val,
      (h (nf.1.1-nf.1.1/2,(nf.1.2.1+nf.1.1/2,nf.1.2.2))).val))).peak ≤ B) :
    (splitCode.run h nf).peak ≤ B := by
  rw [splitCode,code_comp_peak,code_fork_peak,code_fork_peak,code_comp_peak,code_comp_peak]
  have lp:=leftInput_peak nf
  have rp:=rightInput_peak nf
  have lb:=lp.trans (max_le hb he)
  have rb:=rp.trans (max_le hb he)
  change max (max 0 (max (max (max (run leftInput nf).peak 0) (max (h (run leftInput nf).val).peak 0))
    (max (max (run rightInput nf).peak 0) (max (h (run rightInput nf).val).peak 0))))
    (max (run finish (nf,((h (run leftInput nf).val).val,(h (run rightInput nf).val).val))).peak 0) ≤ _
  rw [leftInput_value,rightInput_value]
  simp only [max_le_iff]
  omega

theorem branch_peak (h : Handler RecPort) (v o t b : ℕ) (L : Tape Row7.T) (B : ℕ)
    (hb:2 ≤ B) (hd:(run direct (v,(o,t))).peak ≤ B)
    (hs:¬(v<2 ∨ b=0)→(splitCode.run h ((v,(o,t)),(b,L))).peak ≤ B) :
    (branch.run h ((v,(o,t)),(b,L))).peak ≤ B := by
  rw [branch,code_ifz_peak]
  have cmp:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,L))).val=
    if v<2 then 1 else 0:=rfl
  have cp:(Code.run (.importClosed nodeSmall) h ((v,(o,t)),(b,L))).peak ≤ 2:=by
    have bit:(if v<2 then (1:ℕ) else 0) ≤ 2:=by split <;>omega
    simp only [nodeSmall,nat,nodeWidth,width,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,max_zero,zero_max]
    change max 2 (if v<2 then 1 else 0) ≤ 2
    exact max_le le_rfl bit
  have dp:(directCode.run h ((v,(o,t)),(b,L))).peak ≤ B:=by
    rw [directCode,code_comp_peak]
    change max 0 (max (run direct (v,(o,t))).peak 0) ≤ B
    omega
  refine max_le (cp.trans hb) ?_
  rw [cmp]
  by_cases hv:v<2
  · simp only [hv,ite_true,Nat.one_ne_zero,ite_false]
    exact dp
  · simp only [hv,ite_false,ite_true]
    rw [code_ifz_peak]
    change max 0 (if b=0 then _ else _) ≤ B
    by_cases hz:b=0
    · rw [ite_eq_left hz]
      exact max_le (by omega) dp
    · rw [ite_eq_right hz]
      exact max_le (by omega) (hs (by omega))

end
end ExactFourierCircuits.DFTModelCacheCalendar
