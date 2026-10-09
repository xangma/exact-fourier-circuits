import UniformResidualSpectators
import UniformResidualPermutationPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualSpectatorBankMachine
open UniformMachine
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section

def boot : List Op := [.literal 4101 0,.binary .mul 4102 4008 4069,.binary .mul 4103 4023 4069]
def body : List Op := [.binary .add 4104 4009 4102,.store 4104 4103,
 .binary .add 4102 4102 4069,.binary .add 4101 4101 4069,.binary .add 4103 4103 4103]
def tail : List Op := [.binary .mul 4008 4102 4069,.binary .add 4014 4014 4100]
/-- Append r ordinary unit images using a charged doubling loop. No bit
scan of a data address or supplied spectator-image bank is used. -/
def program : Program := boot.map Op.code++[.branchLT 4101 4100 4 10]++body.map Op.code++[.jump 3]++tail.map Op.code++[.halt]
theorem program_length : program.length=13 := rfl
theorem boot_code : BlockAt boot program 0 := by intro i hi;change i< 3 at hi;interval_cases i <;> rfl
theorem branch_at : program[3]?=some (.branchLT 4101 4100 4 10) := rfl
theorem body_code : BlockAt body program 4 := by intro i hi;change i< 5 at hi;interval_cases i <;> rfl
theorem jump_at : program[9]?=some (.jump 3) := rfl
theorem tail_code : BlockAt tail program 10 := by intro i hi;change i< 2 at hi;interval_cases i <;> rfl
theorem halt_at : program[12]?=some .halt := rfl

structure Cursor (k r A i : ℕ) (s:State) : Prop where
 pc : s.pc=3
 rest : s.natReg 4100=r
 base : s.natReg 4009=A
 one : s.natReg 4069=1
 index : s.natReg 4101=i
 length : s.natReg 4102=k+i
 power : s.natReg 4103=2^(k+i)

def round (s:State) : State := {applyBlock body {s with pc:=4} with pc:=3}

lemma round_cursor (k r A i:ℕ) (s:State) (c:Cursor k r A i s) : Cursor k r A (i+1) (round s) := by
 constructor <;> simp [round,body,applyBlock,Op.apply,evalNat,writeNat,next,c.rest,c.base,c.one,c.index,c.length,c.power,Nat.pow_succ]
 <;> ring
lemma round_write (k r A i:ℕ) (s:State) (c:Cursor k r A i s) :
 (round s).natHeap (A+k+i)=some (2^(k+i)) := by
 simp [round,body,applyBlock,Op.apply,evalNat,writeNat,next,c.base,c.length,c.power,Nat.add_assoc]
lemma round_outside (k r A i z:ℕ) (s:State) (c:Cursor k r A i s) (hz:z≠ A+k+i) :
 (round s).natHeap z=s.natHeap z := by
 have hz' : z≠ A+(k+i):=by simpa [Nat.add_assoc] using hz
 simp [round,body,applyBlock,Op.apply,evalNat,writeNat,next,c.base,c.length,hz']
lemma round_keep (s:State) (j:ℕ) (hj:j< 4101 ∨ 4104< j) : (round s).natReg j=s.natReg j := by
 simp (disch:=omega) [round,body,applyBlock,Op.apply,writeNat,next]
lemma round_scalar (s:State) : (round s).scalarHeap=s.scalarHeap ∧ (round s).scalarReg=s.scalarReg ∧
 (round s).outputs=s.outputs ∧ (round s).rootOrders=s.rootOrders := by exact ⟨rfl,rfl,rfl,rfl⟩

lemma round_runs (n B k r A i:ℕ) (x:Fin n→ℂ) (s:State) (c:Cursor k r A i s)
 (hi:i< r) (bound:WordBound B s) (code:13≤ B) (extent:A+k+r≤ B) (volume:2^(k+r)≤ B) :
 BoundedRuns program n x B s 7 (round s) := by
 let entry:State:={s with pc:=4}
 have first:BoundedRuns program n x B s 1 entry:=.next bound
  (by simp [step,c.pc,branch_at,c.index,c.rest,hi,entry])
  (.refl (changePC_bound B s 4 bound (by omega)))
 have power:2^(k+i+1)≤ B:=(Nat.pow_le_pow_right (by omega) (by omega)).trans volume
 have small:k+i+1≤ B:=by
  have h:k+i+1≤ A+k+r:=by omega
  exact h.trans extent
 have safe:readable body entry ∧ peak body entry≤ B:=by
  simp [body,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,entry,c.base,c.length,c.power,c.one,c.index]
  rw [Nat.pow_succ] at power
  omega
 have work:=block_runs body program 4 n B x entry body_code rfl first.final_bound (by change 9≤ B;omega) safe.1 safe.2
 let done:=applyBlock body entry
 have dp:done.pc=9:=by simp [done,body,applyBlock,Op.apply,writeNat,next,entry]
 have back:BoundedRuns program n x B done 1 {done with pc:=3}:=.next work.final_bound
  (by simp [step,dp,jump_at]) (.refl (changePC_bound B done 3 work.final_bound (by omega)))
 simpa [round,entry,done,body] using first.trans (work.trans back)

lemma loop (n B k r A i h:ℕ) (x:Fin n→ℂ) (s:State) (c:Cursor k r A i s)
 (fits:i+h≤ r) (bound:WordBound B s) (code:13≤ B) (extent:A+k+r≤ B) (volume:2^(k+r)≤ B) :
 ∃u,BoundedRuns program n x B s (7*h) u ∧ Cursor k r A (i+h) u ∧
 (∀j,i≤ j→ j< i+h→ u.natHeap (A+k+j)=some (2^(k+j))) ∧
 (∀z,z< A+k+i ∨ A+k+(i+h)≤ z→ u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,j< 4101 ∨ 4104< j→ u.natReg j=s.natReg j) := by
 induction h generalizing i s with
 | zero => exact ⟨s,.refl bound,by simpa using c,by intro j lo hi;omega,by intro z hz;rfl,rfl,rfl,rfl,rfl,by intro j hj;rfl⟩
 | succ h ih =>
  have hi:i< r:=by omega
  have run:=round_runs n B k r A i x s c hi bound code extent volume
  obtain ⟨u,ur,uc,written,outside,sh,sr,ou,ro,kept⟩:=ih (i+1) (round s) (round_cursor k r A i s c) (by omega) run.final_bound
  refine ⟨u,?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using uc,?_,?_,sh.trans (round_scalar s).1,
   sr.trans (round_scalar s).2.1,ou.trans (round_scalar s).2.2.1,ro.trans (round_scalar s).2.2.2,?_⟩
  · convert run.trans ur using 1 <;> ring
  · intro j lo hj
    by_cases ji:j=i
    · subst j
      exact (outside _ (by left;omega)).trans (round_write k r A i s c)
    · exact written j (by omega) (by omega)
  · intro z hz
    exact (outside z (by rcases hz with hz|hz <;> omega)).trans (round_outside k r A i z s c (by rcases hz with hz|hz <;> omega))
  · intro j hj
    exact (kept j hj).trans (round_keep s j hj)

/-- All appended images, sizing writes, loop tests and halt are charged.
Old image entries and arbitrary scalar values/flags are retained. -/
theorem execution (n B k r m A:ℕ) (x:Fin n→ℂ) (s:State)
 (pc:s.pc=0) (rest:s.natReg 4100=r) (size:s.natReg 4008=k) (base:s.natReg 4009=A)
 (one:s.natReg 4069=1) (power:s.natReg 4023=2^k) (width:s.natReg 4014=m)
 (bound:WordBound B s) (code:13≤ B) (extent:A+k+r≤ B) (volume:2^(k+r)≤ B) (widthBound:m+r≤ B) :
 ∃u,BoundedExecution program n x B s (7*r+7) u ∧ u.pc=12 ∧ u.natReg 4008=k+r ∧ u.natReg 4014=m+r ∧
 (∀j:Fin r,u.natHeap (A+k+j.val)=some (2^(k+j.val))) ∧
 (∀z,z< A+k ∨ A+k+r≤ z→ u.natHeap z=s.natHeap z) ∧
 u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀j,(j< 4101 ∨ 4104< j)→ j≠4008→ j≠4014→ u.natReg j=s.natReg j) := by
 have safe:readable boot s ∧ peak boot s≤ B:=by
  simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,size,power,one]
  exact ⟨(show k≤ B from by omega),(Nat.pow_le_pow_right (by omega) (by omega)).trans volume⟩
 have init:=block_runs boot program 0 n B x s boot_code pc bound (by change 3≤ B;omega) safe.1 safe.2
 let entered:=applyBlock boot s
 have cursor:Cursor k r A 0 entered:=by
  constructor <;> simp [entered,boot,applyBlock,Op.apply,evalNat,writeNat,next,pc,rest,base,one,size,power]
 obtain ⟨u,ur,uc,uw,uf,ush,usr,uo,uro,uk⟩:=loop n B k r A 0 r x entered cursor (by omega) init.final_bound code extent volume
 let tailEntry:State:={u with pc:=10}
 have exit:BoundedRuns program n x B u 1 tailEntry:=.next ur.final_bound
  (by simp [step,uc.pc,branch_at,uc.index,uc.rest,tailEntry])
  (.refl (changePC_bound B u 10 ur.final_bound (by omega)))
 have w:u.natReg 4014=m:=by
  have h:=uk 4014 (by omega)
  simpa [entered,boot,applyBlock,Op.apply,writeNat,next] using h.trans width
 have tailSafe:readable tail tailEntry ∧ peak tail tailEntry≤ B:=by
  simp [tail,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,tailEntry,uc.length,uc.one,uc.rest,w]
  omega
 have ending:=block_runs tail program 10 n B x tailEntry tail_code rfl exit.final_bound (by change 12≤ B;omega) tailSafe.1 tailSafe.2
 let final:=applyBlock tail tailEntry
 have fp:final.pc=12:=by simp [final,tail,applyBlock,Op.apply,writeNat,next,tailEntry]
 have halt:BoundedExecution program n x B final 1 final:=.halt ending.final_bound (by simp [step,fp,halt_at])
 refine ⟨final,?_,fp,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · convert (init.trans (ur.trans (exit.trans ending))).executes halt using 1
   simp [boot,tail];omega
 · simp [final,tail,applyBlock,Op.apply,evalNat,writeNat,next,tailEntry,uc.length,uc.one]
 · simp [final,tail,applyBlock,Op.apply,evalNat,writeNat,next,tailEntry,uc.rest,w]
 · intro j
   simpa [final,tail,applyBlock,Op.apply,writeNat,next,tailEntry] using uw j.val (by omega) (by simpa using j.isLt)
 · intro z hz
   simpa [final,tail,applyBlock,Op.apply,writeNat,next,tailEntry,entered,boot] using uf z (by simpa using hz)
 · exact ush
 · exact usr
 · exact uo
 · exact uro
 · intro j hj h8 h14
   have h:=uk j hj
   simpa (disch:=omega) [final,tail,applyBlock,Op.apply,writeNat,next,tailEntry,entered,boot] using h
end
end ExactFourierCircuits.UniformResidualSpectatorBankMachine
