import DFTModelCacheDisplacementProgram

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDisplacement
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.ExactFourier
noncomputable section

attribute [local irreducible] DFTModelCacheKernelBanks.program
  DFTModelCacheForest.inverseHBank rawProgram

abbrev Input := p Metadata sc
abbrev Produced := p Metadata DFTModelCacheKernelBanks.Output

def bankArgument : Prog false Input DFTModelCacheKernelBanks.Input :=
  .fork (.comp (.atom .fst) radix) (.atom .snd)
def produceBanks : Prog false Input Produced :=
  .fork (.atom .fst) (.comp bankArgument DFTModelCacheKernelBanks.program)
def finishEnv : Prog false Produced Env :=
  .fork (.atom .fst) (.fork
    (.comp (.comp (.atom .snd) (.atom .fst)) DFTModelCacheForest.inverseHBank)
    (.comp (.atom .snd) (.atom .snd)))
def prepare : Prog false Input Env := .comp produceBanks finishEnv
/-- Closed rectangle producer. Newton and reciprocal banks are generated once
from the radix root; six charged tabs then emit the actual padded kernels. -/
def program : Prog false Input (Ty.a (Ty.a sc)) := .comp prepare rawProgram

theorem bankArgument_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) :
    run bankArgument (metadata r p,omega)=⟨(r,omega),5,0,True⟩ := by
  simp [bankArgument,radix,metadata,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem produceBanks_run (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) :
    run produceBanks (metadata r p,omega)=
      ((run DFTModelCacheKernelBanks.program (r,omega)).pass
        (fun b=>Bill.one (metadata r p,b))).pay 7 0 := by
  change (Bill.one (metadata r p)).pass (fun m=>
    (((run bankArgument (metadata r p,omega)).pass
      (run DFTModelCacheKernelBanks.program)).pay 1 0).pass (fun b=>Bill.one (m,b)))=_
  rw [bankArgument_run]
  simp [Bill.one,Bill.pass,Bill.pay]
  omega

theorem finishEnv_run (m : Metadata.T) (t : Tape DFTModelCacheForest.Row.T) (g : Tape ℂ) :
    run finishEnv (m,(t,g))=
      ((run DFTModelCacheForest.inverseHBank t).pass
        (fun h=>Bill.one (m,(h,g)))).pay 9 0 := by
  simp [finishEnv,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  omega

attribute [local irreducible] produceBanks finishEnv

theorem prepare_value (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run prepare (metadata r p,omega)).val=
      (metadata r p,(DFTModelCacheKernelNewton.hValues r omega,
        DFTModelCacheKernelNewton.gValues r omega)) := by
  change (run finishEnv (run produceBanks (metadata r p,omega)).val).val=_
  rw [produceBanks_run]
  change (run finishEnv (metadata r p,(run DFTModelCacheKernelBanks.program (r,omega)).val)).val=_
  rw [DFTModelCacheKernelBanks.program_value r omega hr,finishEnv_run]
  change (metadata r p,((run DFTModelCacheForest.inverseHBank
    (DFTModelCacheForest.values r omega)).val,DFTModelCacheKernelNewton.gValues r omega))=_
  rw [DFTModelCacheKernelBanks.inverseH_value]

theorem prepare_valid {r : ℕ} (p : UniformRankKernelMachine.Parameters) (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) : (run prepare (metadata r p,omega)).valid := by
  change (run produceBanks (metadata r p,omega)).valid ∧
    (run finishEnv (run produceBanks (metadata r p,omega)).val).valid
  rw [produceBanks_run]
  change ((run DFTModelCacheKernelBanks.program (r,omega)).valid ∧ True) ∧ _
  refine ⟨⟨DFTModelCacheKernelBanks.program_valid hr primitive,trivial⟩,?_⟩
  change (run finishEnv (metadata r p,(run DFTModelCacheKernelBanks.program (r,omega)).val)).valid
  rw [DFTModelCacheKernelBanks.program_value r omega hr,finishEnv_run]
  exact ⟨DFTModelCacheForest.inverseHBank_valid _,trivial⟩

theorem prepare_work (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run prepare (metadata r p,omega)).work≤250*(r+1)^2+50 := by
  change (run produceBanks (metadata r p,omega)).work+
    (run finishEnv (run produceBanks (metadata r p,omega)).val).work+1≤_
  rw [produceBanks_run]
  change (run DFTModelCacheKernelBanks.program (r,omega)).work+8+
    (run finishEnv (metadata r p,(run DFTModelCacheKernelBanks.program (r,omega)).val)).work+1≤_
  rw [DFTModelCacheKernelBanks.program_value r omega hr,finishEnv_run]
  change (run DFTModelCacheKernelBanks.program (r,omega)).work+8+
    ((run DFTModelCacheForest.inverseHBank (DFTModelCacheForest.values r omega)).work+10)+1≤_
  rw [DFTModelCacheForest.inverseHBank_work]
  change (run DFTModelCacheKernelBanks.program (r,omega)).work+8+(15*r+4+10)+1≤_
  have h:=DFTModelCacheKernelBanks.program_work r omega
  nlinarith

theorem prepare_peak (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run prepare (metadata r p,omega)).peak≤r := by
  change max (max (run produceBanks (metadata r p,omega)).peak
    (run finishEnv (run produceBanks (metadata r p,omega)).val).peak) 0≤_
  rw [produceBanks_run]
  change max (max (max (max (run DFTModelCacheKernelBanks.program (r,omega)).peak 0) 0)
    (run finishEnv (metadata r p,(run DFTModelCacheKernelBanks.program (r,omega)).val)).peak) 0≤_
  rw [DFTModelCacheKernelBanks.program_value r omega hr,finishEnv_run]
  have h:=DFTModelCacheKernelBanks.program_peak r omega
  have t:=DFTModelCacheForest.inverseHBank_peak (DFTModelCacheForest.values r omega)
  change (run DFTModelCacheForest.inverseHBank (DFTModelCacheForest.values r omega)).peak≤r at t
  change max (max (max (max (run DFTModelCacheKernelBanks.program (r,omega)).peak 0) 0)
    (max (max (run DFTModelCacheForest.inverseHBank (DFTModelCacheForest.values r omega)).peak 0) 0)) 0≤_
  omega

attribute [local irreducible] prepare

theorem program_value (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run program (metadata r p,omega)).val=rawValues p
      (DFTModelCacheKernelNewton.hValues r omega) (DFTModelCacheKernelNewton.gValues r omega) := by
  change (run rawProgram (run prepare (metadata r p,omega)).val).val=_
  rw [prepare_value r p omega hr,rawProgram_value]

theorem program_valid {r : ℕ} (p : UniformRankKernelMachine.Parameters) (hr:0<r) {omega : ℂ}
    (primitive:IsPrimitiveRoot omega r) : (run program (metadata r p,omega)).valid := by
  change (run prepare (metadata r p,omega)).valid ∧
    (run rawProgram (run prepare (metadata r p,omega)).val).valid
  exact ⟨prepare_valid p hr primitive,by rw [prepare_value r p omega hr];exact rawProgram_valid _ _ _ _⟩

theorem program_work (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ) (hr:0<r) :
    (run program (metadata r p,omega)).work≤
      250*(r+1)^2+6*p.N*(52*p.split+300)+600 := by
  change (run prepare (metadata r p,omega)).work+
    (run rawProgram (run prepare (metadata r p,omega)).val).work+1≤_
  rw [prepare_value r p omega hr]
  have a:=prepare_work r p omega hr
  have b:=rawProgram_work r p (DFTModelCacheKernelNewton.hValues r omega)
    (DFTModelCacheKernelNewton.gValues r omega)
  omega

theorem program_peak (r : ℕ) (p : UniformRankKernelMachine.Parameters) (omega : ℂ)
    (shape:Shape p r) : (run program (metadata r p,omega)).peak≤r+p.N+6 := by
  have hr:0<r:=shape.positiveA.trans_le (by have h:=shape.hRows;omega)
  change max (max (run prepare (metadata r p,omega)).peak
    (run rawProgram (run prepare (metadata r p,omega)).val).peak) 0≤_
  rw [prepare_value r p omega hr]
  have a:=prepare_peak r p omega hr
  have b:=rawProgram_peak r p (DFTModelCacheKernelNewton.hValues r omega)
    (DFTModelCacheKernelNewton.gValues r omega) shape
  omega

end
end ExactFourierCircuits.DFTModelCacheDisplacement
