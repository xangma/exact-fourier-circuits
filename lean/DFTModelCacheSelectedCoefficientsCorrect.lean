import DFTModelCacheSelectedCoefficientsProgram
import DFTModelCacheTraversalTape

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheSelectedCoefficients
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
open scoped BigOperators
noncomputable section
attribute [local irreducible] constants constantsBody constantSeed constantCell decode

def constantValues (K : ℕ) : Tape ℂ :=
  Tape.tab 6 (UniformReplayCoefficientMachine.constant K)

theorem constantsBody_run (K : ℕ) (z : ℂ) : run constantsBody (K,z)=
    (Bill.tab 6 sc.blank (fun j=>run constantCell ((K,z),j))).pay 2 6 := by
  simp [constantsBody,run,Code.run,Atom.run,Bill.word,Bill.pass,Bill.pay]
  omega

theorem constants_value (K : ℕ) : (run constants K).val=constantValues K := by
  rw [constants,comp_run,constantSeed_run]
  simp only [Bill.pass,Bill.pay]
  rw [constantsBody_run]
  change (Bill.tab _ _ _).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  apply DFTModelCacheTraversal.tape_ext _ _ 0
  · rfl
  intro j hj
  change j<6 at hj
  simpa [constantValues,Tape.tab,Tape.look,hj] using (constantCell_spec K j hj).1

theorem constants_bounds (K : ℕ) : (run constants K).valid ∧
    (run constants K).work≤40*(Nat.log2 (K+1)+1)+500 ∧
    (run constants K).peak≤K+6 := by
  have power:=DFTModelScalarPower.program_work K (2:ℂ)
  have peak:=DFTModelScalarPower.program_peak K (2:ℂ)
  have good:=fun j hj=>constantCell_spec K j hj
  rw [constants,comp_run,constantSeed_run]
  simp only [Bill.pass,Bill.pay]
  rw [constantsBody_run]
  constructor
  · change True ∧ (Bill.tab _ _ _).valid
    exact ⟨trivial,(ModelEquivalenceInterpreter.tab_valid _ _ _).mpr (fun j hj=>(good j hj).2.1)⟩
  constructor
  · change _+16+((Bill.tab _ _ _).work+2)+1≤_
    rw [ModelEquivalenceInterpreter.tab_work]
    have sum:(∑j∈Finset.range 6,(run constantCell ((K,((2:ℂ)^K)⁻¹),j)).work)≤73*6 := by
      calc
        _≤∑_j∈Finset.range 6,73:=Finset.sum_le_sum (fun j hj=>(good j (Finset.mem_range.mp hj)).2.2.1)
        _=73*6:=by norm_num
    omega
  · simp only [Bill.pay,max_zero]
    rw [ModelEquivalenceInterpreter.tab_peak]
    have sup:(Finset.range 6).sup (fun j=>(run constantCell ((K,((2:ℂ)^K)⁻¹),j)).peak)≤5 :=
      Finset.sup_le (fun j hj=>(good j (Finset.mem_range.mp hj)).2.2.2)
    omega

theorem decodeAt_run (neg : Bool) (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) :
    run (decodeAt neg) (argument C T P d b cs)=
      ⟨b.look (d-(if neg then T else C)) (0,0),if neg then 19 else 17,
        d-(if neg then T else C),True⟩ := by
  cases neg <;> simp [decodeAt,decodeBank,decodeIndex,decodeLabel,decodeBase,argument,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem decodeNegative_run (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) :
    run decodeNegative (argument C T P d b cs)=
      ⟨(-(b.look (d-T) (0,0)).1,-(b.look (d-T) (0,0)).2),31,d-T,True⟩ := by
  rw [decodeNegative,comp_run,decodeAt_run]
  simp [negatePair,negative,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem decodeConstant_run (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) :
    run decodeConstant (argument C T P d b cs)=
      ⟨(cs.look (d-P) 0,cs.look (d-P) 0),25,d-P,True⟩ := by
  simp [decodeConstant,decodeLabel,decodeConstantsBase,argument,
    run,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem isBelowNegative_run (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) :
    run isBelowNegative (argument C T P d b cs)=
      ⟨if d<T then 1 else 0,13,if d<T then 1 else 0,True⟩ := by
  simp [isBelowNegative,decodeLabel,decodeBase,argument,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem isBelowConstants_run (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) :
    run isBelowConstants (argument C T P d b cs)=
      ⟨if d<P then 1 else 0,13,if d<P then 1 else 0,True⟩ := by
  simp [isBelowConstants,decodeLabel,decodeConstantsBase,argument,run,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem decode_positive (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ) (h:d<T) :
    run decode (argument C T P d b cs)=
      ⟨b.look (d-C) (0,0),31,max 1 (d-C),True⟩ := by
  rw [decode,ifz_run,isBelowNegative_run,ite_eq_left h]
  simp only [Bill.pass,Bill.pay,one_ne_zero,ite_false]
  rw [decodeAt_run]
  simp

theorem decode_negative (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ)
    (ht:T≤d) (hp:d<P) : run decode (argument C T P d b cs)=
      ⟨(-(b.look (d-T) (0,0)).1,-(b.look (d-T) (0,0)).2),59,
        max 1 (d-T),True⟩ := by
  rw [decode,ifz_run,isBelowNegative_run,ite_eq_right (by omega)]
  simp only [Bill.pass,Bill.pay,ite_true]
  rw [ifz_run,isBelowConstants_run,ite_eq_left hp]
  simp only [Bill.pass,Bill.pay,one_ne_zero,ite_false]
  rw [decodeNegative_run]
  simp

theorem decode_constant (C T P d : ℕ) (b : Tape (ℂ × ℂ)) (cs : Tape ℂ)
    (ht:T≤d) (hp:P≤d) : run decode (argument C T P d b cs)=
      ⟨(cs.look (d-P) 0,cs.look (d-P) 0),53,d-P,True⟩ := by
  rw [decode,ifz_run,isBelowNegative_run,ite_eq_right (by omega)]
  simp only [Bill.pass,Bill.pay,ite_true]
  rw [ifz_run,isBelowConstants_run,ite_eq_right (by omega)]
  simp only [Bill.pass,Bill.pay,ite_true]
  rw [decodeConstant_run]
  simp

end
end ExactFourierCircuits.DFTModelCacheSelectedCoefficients
