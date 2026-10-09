import UniformLocalCacheContextMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheContextMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine

lemma readable_append(a b:List Op)(s:State):readable (a++b) s ↔
 readable a s ∧readable b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>simp [readable,applyBlock]
 | cons o os ih=>simp only [List.cons_append,readable,applyBlock,ih,and_assoc]
lemma peak_append(a b:List Op)(s:State):peak (a++b) s=
 max (peak a s) (peak b (applyBlock a s)):=by
 induction a generalizing s with
 | nil=>simp [peak,applyBlock]
 | cons o os ih=>simp only [List.cons_append,peak,applyBlock,ih,max_assoc]

lemma tail_safe {c:Parameters}{I B:ℕ}{s:State}(h:Sources c I s)(wb:WordBound B s):
 readable tail (copied s) ∧peak tail (copied s)≤B:=by
 have nh:=(copied_heaps s).1
 have rs:=copied_readers s
 have address:=(wb.2.2.1 _ _ h.radix).1
 have radix:=(wb.2.2.1 _ _ h.radix).2
 have time:=(wb.2.2.1 _ _ h.time).2
 constructor
 · simp [tail,readable,Op.readable,Op.apply,writeNat,next,copied_one,rs.1,rs.2,nh,h.radix,h.time]
 · simp [tail,peak,Op.peak,Op.apply,writeNat,next,copied_one,rs.1,rs.2,nh,h.radix,h.time]
   exact ⟨address,radix,time⟩

lemma operations_safe {c:Parameters}{I B:ℕ}{s:State}(h:Sources c I s)
 (wb:WordBound B s)(code:1≤B):readable operations s ∧peak operations s≤B:=by
 have copy:=UniformLocalCacheContextCopies.copy_safe copies s.natReg (applyBlock boot s) B
  (boot_sources s) (boot_zero s) safe (fun p _=>wb.2.1 p.2)
 have tail:=tail_safe h wb
 rw [operations,readable_append,readable_append,peak_append,peak_append,applyBlock_append]
 simp only [←copied_eq]
 change ((readable boot s ∧readable (copyOps copies) (applyBlock boot s)) ∧
  readable UniformLocalCacheContextMachine.tail (copied s)) ∧
  max (max (peak boot s) (peak (copyOps copies) (applyBlock boot s)))
   (peak UniformLocalCacheContextMachine.tail (copied s))≤B
 refine ⟨⟨⟨?_,copy.1⟩,tail.1⟩,max_le (max_le ?_ copy.2) tail.2⟩
 · simp [boot,readable,Op.readable]
 · simpa [boot,peak,Op.peak] using code

lemma tail_heaps(s:State):(applyBlock tail s).natHeap=s.natHeap ∧
 (applyBlock tail s).scalarHeap=s.scalarHeap ∧
 (applyBlock tail s).scalarReg=s.scalarReg ∧
 (applyBlock tail s).outputs=s.outputs ∧
 (applyBlock tail s).rootOrders=s.rootOrders:=⟨rfl,rfl,rfl,rfl,rfl⟩
lemma final_heaps(s:State):(applyBlock operations s).natHeap=s.natHeap ∧
 (applyBlock operations s).scalarHeap=s.scalarHeap ∧
 (applyBlock operations s).scalarReg=s.scalarReg ∧
 (applyBlock operations s).outputs=s.outputs ∧
 (applyBlock operations s).rootOrders=s.rootOrders:=by
 rw [operations,applyBlock_append,applyBlock_append]
 simp only [←copied_eq]
 obtain ⟨nh,sh,sr,out,roots⟩:=tail_heaps (copied s)
 obtain ⟨n,s,r,o,d⟩:=copied_heaps s
 exact ⟨nh.trans n,sh.trans s,sr.trans r,out.trans o,roots.trans d⟩

lemma final_nat(s:State)(q:ℕ)(range:(q<6100∨6138<q) ∧
 q≠6190 ∧q≠6191 ∧q≠6192 ∧q≠6200):
 (applyBlock operations s).natReg q=s.natReg q:=by
 apply block_keeps
 intro op member
 simp only [operations,List.mem_append] at member
 rcases member with (member|member)|member
 · simp only [boot,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   all_goals simp only [Op.code,UniformNewtonTableMachine.KeepsNat];omega
 · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp member
   have bound:(p.1≤6138 ∧6100≤p.1) ∨p.1=6200:=by
    have h:(copies.all fun p=>decide ((p.1≤6138 ∧6100≤p.1) ∨p.1=6200))=true:=by decide
    simpa using List.all_eq_true.mp h p hp
   simp only [Op.code,UniformNewtonTableMachine.KeepsNat]
   omega
 · simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl
   all_goals simp only [Op.code,UniformNewtonTableMachine.KeepsNat];omega

/-- All copies, radix/time reads and the halt are charged. Sources contains
physical retained producer registers and two present heap cells, not ready
cache-controller headers or a supplied action. -/
theorem execution {c:Parameters}{I B n:ℕ}(x:Fin n→ℂ)(s:State)(h:Sources c I s)
 (code:44≤B)(pc:s.pc=0)(wb:WordBound B s):
 ∃u,BoundedExecution program n x B s 44 u ∧u.pc=43 ∧Args c u ∧u.natReg 6200=I ∧
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀q,(q<6100∨6138<q) →q≠6190 →q≠6191 →q≠6192 →q≠6200 →u.natReg q=s.natReg q):=by
 have safe:=operations_safe h wb (by omega)
 have run:=block_runs operations program 0 n B x s block_code pc wb
  (by rw [operations_length];omega) safe.1 safe.2
 have up:(applyBlock operations s).pc=43:=by rw [applyBlock_pc,pc,operations_length]
 have stop:BoundedExecution program n x B (applyBlock operations s) 1 (applyBlock operations s):=
  .halt run.final_bound (by simp [step,up,halt_at])
 obtain ⟨nh,sh,sr,out,roots⟩:=final_heaps s
 refine ⟨applyBlock operations s,?_,up,final_args h,final_inverse h,nh,sh,sr,out,roots,?_⟩
 · simpa only [operations_length] using run.executes stop
 · intro q lo a b d e;exact final_nat s q ⟨lo,a,b,d,e⟩

end ExactFourierCircuits.UniformLocalCacheContextMachine
