import UniformLocalCacheContextExecution
import UniformJointCacheWorkspace

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalRectangleWorkspaceHeaders
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformAllAxisSeedPreparation UniformLocalRectangleDescriptors
open UniformLocalCacheSlotHeaderMachine
namespace C
abbrev Safe:=UniformLocalCacheContextCopies.Safe
end C

/-- The real workspace bank, produced by67, supplies all reused addresses. -/
def copies:List (ℕ×ℕ):=[(1127,6401),(1128,6402),(1129,6401),(1130,6403),
 (1131,6402),(1132,6403),(1133,6404),(1134,6405),(1135,6406),(1136,6404),
 (1137,6405),(1220,6407),(1221,6408),(1222,6409),(1223,6410),(4201,6400),
 (4207,6407),(4208,6408),(4209,6412),(4210,6409),(4211,6413),(4212,6414),
 (4213,6415),(4214,6410),(4230,6416),(4232,6417),(4233,6418),(4234,6419),(4235,6420)]
def boot:List Op:=[.literal 6190 0,.literal 1224 1]
def operations:List Op:=boot++copyOps copies
def program:Program:=operations.map Op.code++[.halt]
lemma copies_length:copies.length=29:=rfl
lemma operations_length:operations.length=31:=rfl
lemma program_length:program.length=32:=rfl
lemma block_code:BlockAt operations program 0:=by intro i hi;change i<31 at hi;interval_cases i <;>rfl
lemma halt_at:program[31]?=some .halt:=rfl
lemma safe:C.Safe copies:=by
 have h:(copies.all fun p=>p.1!=6190 && copies.all fun q=>p.1!=q.2)=true:=by decide
 intro p hp
 have a:p.1 ≠ 6190  ∧ (copies.all fun q=>p.1!=q.2)=true:=by simpa using List.all_eq_true.mp h p hp
 exact ⟨a.1,fun q hq=>by simpa using List.all_eq_true.mp a.2 q hq⟩
lemma nodup:(copies.map Prod.fst).Nodup:=by decide

noncomputable section
abbrev z(n:ℕ):=UniformJointCacheWorkspace.stride n
def Bank(n:ℕ)(s:State):Prop:=∀i:Fin 32,s.natReg (6400+i.val)=(i.val+1)*z n

def copied(s:State):State:=applyBlock (copyOps copies) (applyBlock boot s)
lemma copied_eq(s:State):copied s=applyBlock (copyOps copies) (applyBlock boot s):=rfl
lemma copied_nat(s:State):(copied s).natReg=copyEnv copies s.natReg (applyBlock boot s).natReg:=by
 apply UniformLocalCacheContextCopies.copy_nat copies s.natReg (applyBlock boot s)
 · intro p hp
   have h:(copies.all fun p=>p.2!=6190 && p.2!=1224)=true:=by decide
   have a:p.2 ≠ 6190  ∧ p.2 ≠ 1224:=by simpa using List.all_eq_true.mp h p hp
   simp [boot,applyBlock,Op.apply,writeNat,next,a.1,a.2]
 · simp [boot,applyBlock,Op.apply,writeNat,next]
 · exact safe
lemma copied_output(s:State)(d r:ℕ)(mem:(d,r)∈copies):(copied s).natReg d=s.natReg r:=by
 rw [copied_nat,copy_env_output copies _ _ nodup d r mem]
lemma copied_keep(s:State)(q:ℕ)(keep:∀p∈copies,p.1 ≠ q)(a:q ≠ 6190)(b:q ≠ 1224):
 (copied s).natReg q=s.natReg q:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ q keep]
 simp [boot,applyBlock,Op.apply,writeNat,next,a,b]
lemma copied_one(s:State):(copied s).natReg 1224=1:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ 1224 (by
  intro p hp;have h:(copies.all fun p=>p.1!=1224)=true:=by decide
  simpa using List.all_eq_true.mp h p hp)]
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma copied_heap(s:State):(copied s).natHeap=s.natHeap  ∧ (copied s).scalarHeap=s.scalarHeap  ∧ 
 (copied s).scalarReg=s.scalarReg  ∧ (copied s).outputs=s.outputs  ∧ (copied s).rootOrders=s.rootOrders:=
 UniformLocalCacheContextCopies.copy_heaps copies (applyBlock boot s)

lemma output_bank {n:ℕ}{s:State}(bank:Bank n s)(d r:ℕ)(mem:(d,r)∈copies):
 (copied s).natReg d=(r-6400+1)*z n:=by
 rw [copied_output s d r mem]
 have range:6400 ≤ r  ∧ r<6432:=by
  have h:(copies.all fun p=>decide (6400 ≤ p.2  ∧ p.2<6432))=true:=by decide
  simpa using List.all_eq_true.mp h (d,r) mem
 have h:=bank ⟨r-6400,by omega⟩
 simpa only [Nat.add_sub_of_le range.1] using h

lemma args {n:ℕ}(j:Fin (axisCount n))(q:Row)(s:State)(bank:Bank n s)(axis:s.natReg 4200=j.val):
 UniformLocalRectangleBankMachine.Args j (z n) (UniformJointCacheWorkspace.original n q) (copied s):=by
 refine ⟨?_,?_,?_,?_⟩
 · exact (copied_keep s 4200 (by
    intro p hp;have h:(copies.all fun p=>p.1!=4200)=true:=by decide
    simpa using List.all_eq_true.mp h p hp) (by omega) (by omega)).trans axis
 · simpa using output_bank bank 4201 6400 (by simp[copies])
 · intro r lo hi
   interval_cases r
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1127 6401 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1128 6402 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1129 6401 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1130 6403 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1131 6402 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1132 6403 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1133 6404 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1134 6405 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1135 6406 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1136 6404 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1137 6405 (by decide)
 · intro r lo hi
   interval_cases r
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1220 6407 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1221 6408 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1222 6409 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register,
    UniformSeedHeightPreparation.Config.seed,UniformSeedRankCrossPreparation.Config.register] using output_bank bank 1223 6410 (by decide)
   · simpa [UniformJointCacheWorkspace.original,UniformSeedHeightPreparation.Config.register] using copied_one s

lemma nextArgs {n:ℕ}{s:State}(bank:Bank n s):
 UniformLocalRectangleCoefficientMachine.NextArgs (UniformJointCacheWorkspace.work n)
  (UniformJointCacheWorkspace.conjugate n) (copied s):=by
 intro r lo hi
 interval_cases r
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4207 6407 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4208 6408 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4209 6412 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4210 6409 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4211 6413 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4212 6414 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4213 6415 (by decide)
 · simpa [UniformJointCacheWorkspace.work,UniformLocalRectangleCoefficientMachine.addressRegister] using output_bank bank 4214 6410 (by decide)

lemma falseArgs {n:ℕ}{s:State}(bank:Bank n s):
 UniformLocalDisabledHeightMachine.Args (UniformJointCacheWorkspace.falseRows n)
  (UniformJointCacheWorkspace.falseColors n) (UniformJointCacheWorkspace.falsePalette n)
  (UniformJointCacheWorkspace.falseDirectory n) (copied s):=by
 refine ⟨?_,?_,?_,?_⟩
 · simpa [UniformJointCacheWorkspace.falseRows] using output_bank bank 4232 6417 (by decide)
 · simpa [UniformJointCacheWorkspace.falseColors] using output_bank bank 4233 6418 (by decide)
 · simpa [UniformJointCacheWorkspace.falsePalette] using output_bank bank 4234 6419 (by decide)
 · simpa [UniformJointCacheWorkspace.falseDirectory] using output_bank bank 4235 6420 (by decide)

lemma slotAddress {n:ℕ}{s:State}(bank:Bank n s):
 (copied s).natReg 4230=UniformJointCacheWorkspace.control n:=by
 simpa [UniformJointCacheWorkspace.control] using output_bank bank 4230 6416 (by decide)

lemma operations_eq(s:State):applyBlock operations s=copied s:=by
 rw [operations,applyBlock_append];rfl
lemma operations_safe {B:ℕ}{s:State}(wb:WordBound B s)(code:1 ≤ B):
 readable operations s  ∧ peak operations s ≤ B:=by
 have sources:UniformLocalCacheContextCopies.Sources copies s.natReg (applyBlock boot s):=by
  intro p hp
  have h:(copies.all fun p=>p.2!=6190 && p.2!=1224)=true:=by decide
  have a:p.2 ≠ 6190  ∧ p.2 ≠ 1224:=by simpa using List.all_eq_true.mp h p hp
  simp [boot,applyBlock,Op.apply,writeNat,next,a.1,a.2]
 have zero:(applyBlock boot s).natReg 6190=0:=by simp [boot,applyBlock,Op.apply,writeNat,next]
 have safe:=UniformLocalCacheContextCopies.copy_safe copies s.natReg _ B sources zero safe
  (fun p _=>wb.2.1 p.2)
 rw [operations,UniformLocalCacheContextMachine.readable_append,UniformLocalCacheContextMachine.peak_append]
 exact ⟨⟨by simp[boot,readable,Op.readable],safe.1⟩,
  max_le (by simpa [boot,peak,Op.peak] using code) safe.2⟩

/-- Literal32 installs every reused producer argument from the physically
computed workspace bank. All retained arrays and high outer-driver registers
are untouched; no ready Config/NextArgs/false-bank headers are inputs. -/
theorem execution {n B:ℕ}(j:Fin (axisCount n))(q:Row)(x:Fin n → ℂ)(s:State)
 (bank:Bank n s)(axis:s.natReg 4200=j.val)(code:32 ≤ B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution program n x B s 32 u  ∧ u.pc=31  ∧ 
 UniformLocalRectangleBankMachine.Args j (z n) (UniformJointCacheWorkspace.original n q) u  ∧ 
 UniformLocalRectangleCoefficientMachine.NextArgs (UniformJointCacheWorkspace.work n) (UniformJointCacheWorkspace.conjugate n) u  ∧ 
 UniformLocalDisabledHeightMachine.Args (UniformJointCacheWorkspace.falseRows n)
  (UniformJointCacheWorkspace.falseColors n) (UniformJointCacheWorkspace.falsePalette n)
  (UniformJointCacheWorkspace.falseDirectory n) u  ∧ u.natReg 4230=UniformJointCacheWorkspace.control n  ∧ 
 u.natHeap=s.natHeap  ∧ u.scalarHeap=s.scalarHeap  ∧ u.scalarReg=s.scalarReg  ∧ 
 u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧ 
 (∀r,4236 ≤ r → r ≠ 6190 → u.natReg r=s.natReg r):=by
 have safe:=operations_safe wb (by omega)
 have first:=block_runs operations program 0 n B x s block_code pc wb (by rw[operations_length];omega) safe.1 safe.2
 rw [operations_eq] at first
 have up:(copied s).pc=31:=by rw [←operations_eq,applyBlock_pc,operations_length,pc]
 have stop:BoundedExecution program n x B (copied s) 1 (copied s):=.halt first.final_bound
  (by simp[step,up,halt_at])
 obtain ⟨nh,sh,sr,out,roots⟩:=copied_heap s
 refine ⟨copied s,?_,up,args j q s bank axis,nextArgs bank,falseArgs bank,slotAddress bank,nh,sh,sr,out,roots,?_⟩
 · simpa only [operations_length] using first.executes stop
 · intro r lo zero
   apply copied_keep s r _ zero (by omega)
   intro p hp
   have h:(copies.all fun p=>decide (p.1<4236))=true:=by decide
   have b:p.1<4236:=by simpa using List.all_eq_true.mp h p hp
   omega

attribute [irreducible] copied
end
end ExactFourierCircuits.UniformLocalRectangleWorkspaceHeaders
