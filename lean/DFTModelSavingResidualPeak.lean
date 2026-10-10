import DFTModelSavingResidualGeometry
import DFTModelResidualPeakPolynomial

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualOrientation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

theorem steps_peak (m:ℕ) (raw:Tape ℕ) (binary : ∀ j : ℕ, j  <  m → raw.look j 0  <  2)
  (i:ℕ) (fit:i ≤ m) : (steps m raw i).peak ≤ i + 4 := by
  induction i with
  | zero=>change 0 ≤ _;omega
  | succ i ih=>
    have prior:=ih (by omega)
    have bit:=binary i (by omega)
    have small:residue raw i < 4:=Nat.mod_lt _ (by decide)
    change max (max (steps m raw i).peak (run body ((m,raw),(i,(steps m raw i).val))).peak) (i + 1) ≤ _
    rw [steps_value,body_run]
    dsimp only [Bill.peak]
    omega

theorem scan_peak (m:ℕ) (raw:Tape ℕ) (binary : ∀ j : ℕ, j  <  m → raw.look j 0  <  2) :
  (run scan (m,raw)).peak ≤ m + 4 := by
  have bound:=steps_peak m raw binary m le_rfl
  simpa only [scan,steps,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.word,Bill.one,zero_max,max_zero]
    using bound

attribute [local irreducible] scan choice
theorem program_peak (m:ℕ) (raw:Tape ℕ) (flag:ℕ)
  (binary : ∀ j : ℕ, j  <  m → raw.look j 0  <  2) (small:flag < 2) :
  (run program ((m,raw),flag)).peak ≤ m + 4 := by
  have scanned:=scan_peak m raw binary
  have residueSmall:residue raw m < 4:=Nat.mod_lt _ (by decide)
  have last:(run choice ((run scan (m,raw)).val,flag)).peak ≤ 3:=by
    rw [scan_value,choice_run _ _ residueSmall]
    dsimp only [Bill.peak];split  <;>omega
  simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,
    zero_max,max_zero,max_le_iff] using And.intro scanned (last.trans (by omega))
end
end ExactFourierCircuits.DFTModelSavingResidualOrientation

namespace ExactFourierCircuits.DFTModelSavingResidualSetup
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
open DFTModelResidualClosedBasis (Meta)
noncomputable section
attribute [local irreducible] initial sizes power DFTModelResidualClosedRole.gather
  DFTModelSavingResidualOrientation.program UniformBatching.width

theorem peak (ctx:Meta.T) (a flag k:ℕ) (I:ℂ) (bank:Tape DFTModelAffine.Tagged.T)
  (binary : ∀ j : ℕ, j  <  ctx.2.1 → ctx.2.2.2.look j 0  <  2) (small:flag < 2) :
  (run program (ctx,(a,(flag,((k,I),bank))))).peak ≤
    (run DFTModelResidualClosedAddresses.program ctx).peak +
    a*(run DFTModelResidualClosedAddresses.program ctx).val.len +
    (run DFTModelResidualClosedAddresses.program ctx).val.len + ctx.2.1 +
    UniformBatching.width*2^ctx.1 + 5 := by
  have orient:=DFTModelSavingResidualOrientation.program_peak ctx.2.1 ctx.2.2.2 flag binary small
  have gather:=DFTModelResidualClosedRoleBounds.gather_peak DFTModelAffine.Tagged ctx a bank
  have first:(run initial (ctx,(a,(flag,((k,I),bank))))).peak ≤
      (run DFTModelResidualClosedAddresses.program ctx).peak +
      a*(run DFTModelResidualClosedAddresses.program ctx).val.len +
      (run DFTModelResidualClosedAddresses.program ctx).val.len + ctx.2.1 + 4 := by
    simp only [initial,orientationInput,roleInput,m,bits,metadata,inverse,role,node,
      run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
    change (Code.run DFTModelSavingResidualOrientation.program () ((ctx.2.1,ctx.2.2.2),flag)).peak ≤ _ at orient
    change (Code.run (DFTModelResidualClosedRole.gather DFTModelAffine.Tagged) () (ctx,(a,bank))).peak ≤
      (run DFTModelResidualClosedAddresses.program ctx).peak+
      a*(run DFTModelResidualClosedAddresses.program ctx).val.len+
      (run DFTModelResidualClosedAddresses.program ctx).val.len at gather
    dsimp only [run] at gather ⊢
    omega
  have wp:0 < UniformBatching.width:=by rw [UniformBatching.width_eq_pow];exact Nat.two_pow_pos _
  have np:=Nat.two_pow_pos ctx.1
  have one:2^ctx.1 ≤ UniformBatching.width*2^ctx.1:=Nat.le_mul_of_pos_left _ wp
  have two:UniformBatching.width ≤ UniformBatching.width*2^ctx.1:=Nat.le_mul_of_pos_right _ np
  have tail:(run sizes (run initial (ctx,(a,(flag,((k,I),bank))))).val).peak ≤
      UniformBatching.width*2^ctx.1:=by
    rw [sizes_run,initial_value]
    have pow:=power_peak ctx.1
    dsimp only [Bill.peak]
    exact max_le (pow.trans one) (max_le two le_rfl)
  rw [program,DFTModelResidualPeakSyntax.comp]
  omega
end
end ExactFourierCircuits.DFTModelSavingResidualSetup

namespace ExactFourierCircuits.DFTModelSavingResidualFinish
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelSavingResidualSetup
noncomputable section
attribute [local irreducible] DFTModelSavingResidualFlip.program DFTModelResidualClosedRole.scatter

theorem peak (f:First.T) (N T:ℕ) (child:Tape Tagged.T) (pos:0 < N) (multiple:N∣child.len) :
  (run program ((f,(N,T)),child)).peak ≤
    f.2.2.1.2.1*f.2.2.2.1.len + f.2.2.2.1.len + f.2.2.1.2.2.len + child.len + N + 1 := by
  have flip:=DFTModelSavingResidualFlip.peak Tagged N f.2.1 child pos multiple
  have scatter:=DFTModelResidualClosedRoleBounds.scatter_peak Tagged f.2.2.1.1 f.2.2.1.2.1 f.2.2.1.2.2
    f.2.2.2.1 (run (DFTModelSavingResidualFlip.program Tagged) (N,(f.2.1,child))).val
  change (Code.run (DFTModelSavingResidualFlip.program Tagged) () (N,(f.2.1,child))).peak ≤ _ at flip
  change (Code.run (DFTModelResidualClosedRole.scatter Tagged) ()
    (f.2.2.1,(f.2.2.2.1,(Code.run (DFTModelSavingResidualFlip.program Tagged) () (N,(f.2.1,child))).val))).peak ≤ _ at scatter
  simp only [program,scatterArgs,flipArgs,originalParams,context,node,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one,zero_max,max_zero]
  omega
end
end ExactFourierCircuits.DFTModelSavingResidualFinish
