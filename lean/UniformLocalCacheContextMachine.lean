import UniformLocalCacheContextCopies

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine
namespace C
abbrev Safe:=UniformLocalCacheContextCopies.Safe
abbrev Sources:=UniformLocalCacheContextCopies.Sources
end C

/-- Inputs are retained producer registers and high cache-allocation registers.
The two heap reads obtain the real original radix and printed request time. -/
def copies:List (ℕ×ℕ):=[(6100,1050),(6101,1053),(6102,1054),(6103,1055),
 (6104,1060),(6105,1062),(6106,1072),(6107,6407),(6108,6408),(6109,6409),
 (6110,6410),(6111,6417),(6112,6418),(6113,6419),(6114,6420),(6115,6404),
 (6116,6410),(6117,6168),(6118,6169),(6119,6422),(6120,6423),(6121,6424),
 (6122,6425),(6123,6426),(6124,6427),(6125,6428),(6126,6429),(6127,6430),
 (6128,6160),(6130,6171),(6131,6172),(6133,6162),(6134,6163),(6135,6164),
 (6136,6165),(6137,6166),(6200,6170)]
def boot:List Op:=[.literal 6190 0,.literal 6191 1]
def tail:List Op:=[.add 6192 6167 6191,.getNat 6129 6192,
 .getNat 6132 6161,.literal 6138 0]
def operations:List Op:=boot++copyOps copies++tail
def program:Program:=operations.map Op.code++[.halt]
lemma copies_length:copies.length=37:=rfl
lemma operations_length:operations.length=43:=rfl
lemma program_length:program.length=44:=rfl
lemma block_code:BlockAt operations program 0:=by
 intro i hi
 change i<43 at hi
 interval_cases i <;>rfl
lemma halt_at:program[43]?=some .halt:=rfl

lemma safe:C.Safe copies:=by
 have h:(copies.all fun p=>p.1!=6190 && (copies.all fun q=>p.1!=q.2))=true:=by decide
 intro p hp
 have a:=List.all_eq_true.mp h p hp
 have a:p.1≠6190 ∧ (copies.all fun q=>p.1!=q.2)=true:=by simpa using a
 exact ⟨a.1,fun q hq=>by simpa using List.all_eq_true.mp a.2 q hq⟩
lemma nodup:(copies.map Prod.fst).Nodup:=by decide

noncomputable section
def value(c:Parameters)(I d:ℕ):ℕ:=if d=6200 then I else c.register d
structure Sources (c:Parameters)(I:ℕ)(s:State):Prop where
 registers:∀p∈copies,s.natReg p.2=value c I p.1
 radix:s.natHeap (s.natReg 6167+1)=some c.ambient
 time:s.natHeap (s.natReg 6161)=some c.time
 kind:c.kind=0

lemma boot_keep(s:State)(q:ℕ)(h:q≠6190)(h1:q≠6191):
 (applyBlock boot s).natReg q=s.natReg q:=by
 simp [boot,applyBlock,Op.apply,writeNat,next,h,h1]
lemma source_range(p:ℕ×ℕ)(hp:p∈copies):p.2≠6190 ∧p.2≠6191:=by
 have h:(copies.all fun p=>p.2!=6190 && p.2!=6191)=true:=by decide
 simpa using List.all_eq_true.mp h p hp
lemma boot_sources(s:State):C.Sources copies s.natReg (applyBlock boot s):=by
 intro p hp
 exact boot_keep s p.2 (source_range p hp).1 (source_range p hp).2
lemma boot_zero(s:State):(applyBlock boot s).natReg 6190=0:=by
 simp [boot,applyBlock,Op.apply,writeNat,next]
lemma boot_one(s:State):(applyBlock boot s).natReg 6191=1:=by
 simp [boot,applyBlock,Op.apply,writeNat,next]
def copied(s:State):State:=applyBlock (copyOps copies) (applyBlock boot s)
lemma copied_eq(s:State):copied s=applyBlock (copyOps copies) (applyBlock boot s):=rfl
lemma copied_nat(s:State):(copied s).natReg=copyEnv copies s.natReg (applyBlock boot s).natReg:=
 UniformLocalCacheContextCopies.copy_nat copies s.natReg _ (boot_sources s) (boot_zero s) safe
lemma copied_output {c:Parameters}{I:ℕ}{s:State}(h:Sources c I s)(d r:ℕ)(mem:(d,r)∈copies):
 (copied s).natReg d=value c I d:=by
 rw [copied_nat,copy_env_output copies _ _ nodup d r mem]
 exact h.registers (d,r) mem
lemma copied_keep(s:State)(q:ℕ)(keep:∀p∈copies,p.1≠q)(z:q≠6190)(o:q≠6191):
 (copied s).natReg q=s.natReg q:=
 (UniformLocalCacheContextCopies.copy_keeps copies _ q keep).trans (boot_keep s q z o)
lemma copied_one(s:State):(copied s).natReg 6191=1:=by
 rw [copied,UniformLocalCacheContextCopies.copy_keeps copies _ 6191 (by
  intro p hp;have h:(copies.all fun p=>p.1!=6191)=true:=by decide
  simpa using List.all_eq_true.mp h p hp)]
 exact boot_one s
lemma copied_heaps(s:State):(copied s).natHeap=s.natHeap ∧
 (copied s).scalarHeap=s.scalarHeap ∧(copied s).scalarReg=s.scalarReg ∧
 (copied s).outputs=s.outputs ∧(copied s).rootOrders=s.rootOrders:=
 UniformLocalCacheContextCopies.copy_heaps copies (applyBlock boot s)
lemma copied_readers(s:State):(copied s).natReg 6167=s.natReg 6167 ∧
 (copied s).natReg 6161=s.natReg 6161:=by
 constructor
 all_goals apply copied_keep <;>try omega
 all_goals intro p hp
 all_goals have h:(copies.all fun p=>p.1!=6167 && p.1!=6161)=true:=by decide
 all_goals have h:p.1≠6167 ∧p.1≠6161:=by simpa using List.all_eq_true.mp h p hp
 · exact h.1
 · exact h.2

lemma final_special {c:Parameters}{I:ℕ}{s:State}(h:Sources c I s):
 (applyBlock tail (copied s)).natReg 6129=c.ambient ∧
 (applyBlock tail (copied s)).natReg 6132=c.time ∧
 (applyBlock tail (copied s)).natReg 6138=c.kind:=by
 have nh:=(copied_heaps s).1
 have rs:=copied_readers s
 simp [tail,applyBlock,Op.apply,writeNat,next,copied_one,rs.1,rs.2,nh,h.radix,h.time,h.kind]

lemma final_args {c:Parameters}{I:ℕ}{s:State}(h:Sources c I s):
 Args c (applyBlock operations s):=by
 rw [operations,applyBlock_append,applyBlock_append]
 change Args c (applyBlock tail (copied s))
 intro q lo hi
 by_cases a:q=6129
 · subst q;exact (final_special h).1
 by_cases b:q=6132
 · subst q;exact (final_special h).2.1
 by_cases d:q=6138
 · subst q;exact (final_special h).2.2
 have keep:(applyBlock tail (copied s)).natReg q=(copied s).natReg q:=by
  apply block_keeps
  intro o ho
  simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl|rfl
  all_goals simp only [Op.code,UniformNewtonTableMachine.KeepsNat];omega
 rw [keep]
 have mem:∃r,(q,r)∈copies:=by
  interval_cases q <;>simp_all [copies]
 obtain ⟨r,mem⟩:=mem
 simpa only [value,ite_eq_right (show q≠6200 by omega)] using copied_output h q r mem

lemma final_inverse {c:Parameters}{I:ℕ}{s:State}(h:Sources c I s):
 (applyBlock operations s).natReg 6200=I:=by
 rw [operations,applyBlock_append,applyBlock_append]
 change (applyBlock tail (copied s)).natReg 6200=I
 have keep:(applyBlock tail (copied s)).natReg 6200=(copied s).natReg 6200:=by
  simp [tail,applyBlock,Op.apply,writeNat,next]
 rw [keep,copied_output h 6200 6170 (by simp[copies])]
 rfl

attribute [irreducible] copied

end
end ExactFourierCircuits.UniformLocalCacheContextMachine
