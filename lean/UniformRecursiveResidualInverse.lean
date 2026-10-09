import UniformRecursiveResidualFinish
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualInverse
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
namespace P
export UniformRecursiveSavingProgram (Part program piece address size part_child)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace N
export UniformResidualNativeTranslationMachine (program Header Frame volume translated execution)
end N
noncomputable section

def inverseOps:List Op:=[.binary .mul 3360 4091 4153,.binary .mul 3364 4090 4153,
 .binary .add 3361 4061 4127,.binary .mul 3362 4122 4153,
 .binary .sub 3363 4124 4153,.binary .mul 3353 4124 4153,
 .binary .mul 3354 4068 4153,.binary .mul 3421 4068 4153,
 .binary .mul 4069 4153 4153,.binary .mul 4015 4124 4153,
 .binary .mul 4023 4122 4153,.binary .mul 5300 4120 4153,
 .binary .mul 5301 4127 4153]
lemma inverseOps_length:inverseOps.length=13:=rfl
lemma inverse_setup_code:BlockAt inverseOps P.program (P.address .inverseSetup):=
 UniformRecursiveSavingExecution.part_block .inverseSetup _ _ rfl
lemma inverse_jump:P.program[P.address .inverseSetup+13]?=some (.jump (P.address .inverse)):=
 UniformRecursiveSavingExecution.part_at .inverseSetup 13 (by decide)
lemma inverse_code:CodeAt N.program P.program (P.address .inverse) (P.address .scatterSetup):=
 P.part_child rfl

def SetupChanged(i:ℕ):Prop:=i=3360∨i=3364∨i=3361∨i=3362∨i=3363∨i=3353∨i=3354∨
 i=3421∨i=4069∨i=4015∨i=4023∨i=5300∨i=5301
structure SetupFrame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 nativeBits:u.natReg 5300=s.natReg 4120*s.natReg 4153
 nativeRest:u.natReg 5301=s.natReg 4127*s.natReg 4153
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬SetupChanged i→u.natReg i=s.natReg i
lemma setup_frame(s:State):SetupFrame s (applyBlock inverseOps s):=by
 refine ⟨rfl,rfl,rfl,?_,?_,rfl,rfl,?_⟩
 · simp [inverseOps,applyBlock,Op.apply,evalNat,writeNat,next]
 · simp [inverseOps,applyBlock,Op.apply,evalNat,writeNat,next]
 intro i hi
 unfold SetupChanged at hi
 simp (disch:=omega) [inverseOps,applyBlock,Op.apply,evalNat,writeNat,next]

/-- Thirteen real Nat header operations and a charged continuation jump.
The mask is computed from the actual retained child-array size. -/
theorem setup_generic(main:Program)(start target n B k q m r D E table:ℕ)(x:Fin n→ℂ)(s:State)
 (atCode:BlockAt inverseOps main start)(jump:main[start+13]?=some (.jump target))
 (pc:s.pc=start)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (size:s.natReg 4124=2^q)(permutation:s.natReg 4068=table)(widthBound:m+r ≤ B)
 (bound:WordBound B s)(extent:start+14 ≤ B)(ret:target ≤ B):∃u,
 BoundedRuns main n x B s 14 u ∧ u.pc=target ∧
 N.Header q (m+r) k (2^q-1) D E u ∧ u.natReg 3421=table ∧ SetupFrame s u:=by
 have kb:k ≤ B:=by have h:=bound.2.1 4120;rwa [bits] at h
 have vb:2^k ≤ B:=by have h:=bound.2.1 4122;rwa [length] at h
 have sb:D ≤ B:=by have h:=bound.2.1 4091;rwa [src] at h
 have db:E ≤ B:=by have h:=bound.2.1 4090;rwa [dst] at h
 have tb:table ≤ B:=by have h:=bound.2.1 4068;rwa [permutation] at h
 have qb:2^q ≤ B:=by have h:=bound.2.1 4124;rwa [size] at h
 have rb:r ≤ B:=by have h:=bound.2.1 4127;rwa [rest] at h
 have ob:1 ≤ B:=by have h:=bound.2.1 4153;rwa [one] at h
 have subB:2^q-1 ≤ B:=by omega
 have safe:readable inverseOps s∧peak inverseOps s ≤ B:=by
  simp [inverseOps,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   one,bits,length,src,dst,width,rest,size,permutation,kb,vb,sb,db,tb,qb,rb,ob,widthBound]
 have run:=block_runs inverseOps main start n B x s atCode pc bound (by rw [inverseOps_length];omega) safe.1 safe.2
 let a:=applyBlock inverseOps s
 let u:State:={a with pc:=target}
 have ap:a.pc=start+13:=by rw [UniformRecursiveNodePreparation.block_pc,pc,inverseOps_length]
 have ub:=changePC_bound B a target run.final_bound ret
 have finish:BoundedRuns main n x B a 1 u:=.next run.final_bound (by simp [step,ap,jump,u]) (.refl ub)
 have header:N.Header q (m+r) k (2^q-1) D E u:=by
  constructor <;> simp [u,a,N.volume,inverseOps,applyBlock,Op.apply,evalNat,writeNat,next,
   one,bits,length,src,dst,width,rest,size,permutation]
 have base:u.natReg 3421=table:=by
  simp [u,a,inverseOps,applyBlock,Op.apply,evalNat,writeNat,next,one,permutation]
 have fr:=setup_frame s
 exact ⟨u,by simpa only [inverseOps_length] using run.trans finish,rfl,header,base,
  ⟨fr.natHeap,fr.scalarHeap,fr.scalarReg,fr.nativeBits,fr.nativeRest,fr.outputs,fr.roots,fr.natReg⟩⟩

/-- The existing fixed52 translator is embedded at its real site in the
same saving Program. It preserves all Scalar flags by physical copying. -/
theorem inverse_embedded(main:Program)(start exit n B k q w D E table mask:ℕ)(x:Fin n→ℂ)(s:State)
 (link:CodeAt N.program main start exit)(pc:s.pc=start)(header:N.Header q w k mask D E s)
 (hm:mask < 2^k)(f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (base:s.natReg 3421=table)(entries:UniformXorTableMachine.Entries q table (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(tableEnd:table+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(nativeWithin:k ≤ q*w)(padded:2^(q*w) ≤ B)
 (bound:WordBound B s)(extent:start+N.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s ((17*w+25)*2^k+13) u ∧ u.pc=exit ∧
 (∀j,u.scalarHeap (D+j.val)=some (N.translated q w k mask hm f j)) ∧ N.Frame D E (2^k) s u:=by
 let caller:State:={s with pc:=0}
 have cb:=changePC_bound B s 0 bound (by omega)
 have h:N.Header q w k mask D E caller:=
  ⟨header.data,header.width,header.volume,header.mask,header.buffer,header.size,header.table⟩
 have small:52 ≤ B:=by
  have h:N.program.length ≤ B:=(Nat.le_add_left _ _).trans extent
  simpa only [UniformXorTranslationMachine.program_length] using h
 obtain ⟨a,run,ap,values,fr,_⟩:=N.execution q w k mask D E table B n hm x f caller rfl h data base entries
  separate cb small tableEnd destEnd sourceEnd nativeWithin padded
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed link extent ret run
 have same:placed start caller=s:=by change {s with pc:=start}=s;rw [←pc]
 rw [same] at placedRun
 let u:State:={a with pc:=exit}
 exact ⟨u,placedRun,rfl,values,⟨fr.natHeap,fr.outputs,fr.roots,fr.natReg,fr.scalarReg,fr.scalarHeap⟩⟩

def InverseChanged(i:ℕ):Prop:=SetupChanged i∨UniformResidualNativeTranslationMachine.Changed i
structure InverseFrame(D E V:ℕ)(s u:State):Prop where
 nativeBits:u.natReg 5300=s.natReg 4120
 nativeRest:u.natReg 5301=s.natReg 4127
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀i,¬InverseChanged i→u.natReg i=s.natReg i
 scalarReg:∀i,i≠100→i≠114→u.scalarReg i=s.scalarReg i
 scalarHeap:∀z,(z < D∨D+V ≤ z)→(z < E∨E+V ≤ z)→u.scalarHeap z=s.scalarHeap z

/-- Real setup14 then translator52, with arithmetic readiness derived from
native k=q*m+r and the ordinary common square word envelope. -/
theorem inverse_execution(n B k q m r D E table:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .inverseSetup)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (size:s.natReg 4124=2^q)(permutation:s.natReg 4068=table)
 (geometry:k=q*m+r)(qp:1 ≤ q)(rp:r < m)(qk:q ≤ k)
 (f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (entries:UniformXorTableMachine.Entries q table (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(tableEnd:table+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(square:(2^k)^2 ≤ B)
 (bound:WordBound B s)(code:P.program.length ≤ B):∃u,
 BoundedRuns P.program n x B s ((17*(m+r)+25)*2^k+27) u ∧ u.pc=P.address .scatterSetup ∧
 (∀j,u.scalarHeap (D+j.val)=some (N.translated q (m+r) k (2^q-1)
  (by change 2^q-1 < 2^k;have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk;have p:=Nat.two_pow_pos q;omega) f j)) ∧
 InverseFrame D E (2^k) s u:=by
 have padded:2^(q*(m+r)) ≤ B:=UniformRecursiveResidualGatherRecordMachine.native_padded q m r B qp rp (by simpa only [←geometry] using square)
 have within:k ≤ q*(m+r):=by rw [geometry];nlinarith
 have widthB:m+r ≤ B:=by
  have w: m+r ≤ q*(m+r):=Nat.le_mul_of_pos_left _ (by omega)
  have exponent:q*(m+r) ≤ 2*k:=by rw [geometry];nlinarith
  have basic:2*k ≤ 2^(2*k):=by have h:=Nat.mul_le_pow (by omega:2≠1) (2*k);omega
  have powers:2^(2*k)=(2^k)^2:=by rw [mul_comm 2,Nat.pow_mul]
  rw [powers] at basic
  omega
 have hm:2^q-1 < 2^k:=by
  have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk
  have p:=Nat.two_pow_pos q
  omega
 obtain ⟨a,prep,ap,header,base,fr⟩:=setup_generic P.program (P.address .inverseSetup) (P.address .inverse)
  n B k q m r D E table x s inverse_setup_code inverse_jump pc one bits length src dst width rest size permutation widthB bound
  (R.code_bound .inverseSetup 14 B rfl code) (R.start_bound .inverse B code)
 have atData:∀j,a.scalarHeap (D+j.val)=some (f j):=by intro j;rw [fr.scalarHeap];exact data j
 have atEntries:UniformXorTableMachine.Entries q table (2^q*2^q) a:=by
  simpa only [UniformXorTableMachine.Entries,fr.natHeap] using entries
 obtain ⟨u,run,up,values,cf⟩:=inverse_embedded P.program (P.address .inverse) (P.address .scatterSetup)
  n B k q (m+r) D E table (2^q-1) x a inverse_code ap header hm f atData base atEntries
  separate tableEnd sourceEnd destEnd within padded prep.final_bound
  (R.code_bound .inverse N.program.length B rfl code) (R.start_bound .scatterSetup B code)
 have total:BoundedRuns P.program n x B s ((17*(m+r)+25)*2^k+27) u:=by
  convert prep.trans run using 1;omega
 have frame:InverseFrame D E (2^k) s u:=by
  refine ⟨?_,?_,cf.natHeap.trans fr.natHeap,cf.outputs.trans fr.outputs,cf.roots.trans fr.roots,?_,?_,?_⟩
  · rw [cf.natReg 5300 (by unfold UniformResidualNativeTranslationMachine.Changed;omega),fr.nativeBits,one,Nat.mul_one]
  · rw [cf.natReg 5301 (by unfold UniformResidualNativeTranslationMachine.Changed;omega),fr.nativeRest,one,Nat.mul_one]
  · intro i hi
    exact (cf.natReg i (fun h=>hi (Or.inr h))).trans (fr.natReg i (fun h=>hi (Or.inl h)))
  · intro i h100 h114;exact (cf.scalarReg i h100 h114).trans (congrFun fr.scalarReg i)
  · intro z hD hE;exact (cf.scalarHeap z hD hE).trans (congrFun fr.scalarHeap z)
 exact ⟨u,total,up,values,frame⟩


theorem inverse_generic(main:Program)(start next exit n B k q m r D E table:ℕ)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=start)(one:s.natReg 4153=1)(bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (size:s.natReg 4124=2^q)(permutation:s.natReg 4068=table)
 (geometry:k=q*m+r)(qp:1 ≤ q)(rp:r < m)(qk:q ≤ k)
 (f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (entries:UniformXorTableMachine.Entries q table (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(tableEnd:table+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(square:(2^k)^2 ≤ B)
 (bound:WordBound B s)(atCode:BlockAt inverseOps main start)
 (jump:main[start+13]?=some (.jump next))(link:CodeAt N.program main next exit)
 (setupExtent:start+14 ≤ B)(nextBound:next ≤ B)(extent:next+N.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s ((17*(m+r)+25)*2^k+27) u ∧ u.pc=exit ∧
 (∀j,u.scalarHeap (D+j.val)=some (N.translated q (m+r) k (2^q-1)
  (by change 2^q-1 < 2^k;have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk;have p:=Nat.two_pow_pos q;omega) f j)) ∧
 InverseFrame D E (2^k) s u:=by
 have padded:2^(q*(m+r)) ≤ B:=UniformRecursiveResidualGatherRecordMachine.native_padded q m r B qp rp (by simpa only [←geometry] using square)
 have within:k ≤ q*(m+r):=by rw [geometry];nlinarith
 have widthB:m+r ≤ B:=by
  have w: m+r ≤ q*(m+r):=Nat.le_mul_of_pos_left _ (by omega)
  have exponent:q*(m+r) ≤ 2*k:=by rw [geometry];nlinarith
  have basic:2*k ≤ 2^(2*k):=by have h:=Nat.mul_le_pow (by omega:2≠1) (2*k);omega
  have powers:2^(2*k)=(2^k)^2:=by rw [mul_comm 2,Nat.pow_mul]
  rw [powers] at basic
  omega
 have hm:2^q-1 < 2^k:=by
  have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk
  have p:=Nat.two_pow_pos q
  omega
 obtain ⟨a,prep,ap,header,base,fr⟩:=setup_generic main (start) (next)
  n B k q m r D E table x s atCode jump pc one bits length src dst width rest size permutation widthB bound
  setupExtent nextBound
 have atData:∀j,a.scalarHeap (D+j.val)=some (f j):=by intro j;rw [fr.scalarHeap];exact data j
 have atEntries:UniformXorTableMachine.Entries q table (2^q*2^q) a:=by
  simpa only [UniformXorTableMachine.Entries,fr.natHeap] using entries
 obtain ⟨u,run,up,values,cf⟩:=inverse_embedded main (next) (exit)
  n B k q (m+r) D E table (2^q-1) x a link ap header hm f atData base atEntries
  separate tableEnd sourceEnd destEnd within padded prep.final_bound
  extent ret
 have total:BoundedRuns main n x B s ((17*(m+r)+25)*2^k+27) u:=by
  convert prep.trans run using 1;omega
 have frame:InverseFrame D E (2^k) s u:=by
  refine ⟨?_,?_,cf.natHeap.trans fr.natHeap,cf.outputs.trans fr.outputs,cf.roots.trans fr.roots,?_,?_,?_⟩
  · rw [cf.natReg 5300 (by unfold UniformResidualNativeTranslationMachine.Changed;omega),fr.nativeBits,one,Nat.mul_one]
  · rw [cf.natReg 5301 (by unfold UniformResidualNativeTranslationMachine.Changed;omega),fr.nativeRest,one,Nat.mul_one]
  · intro i hi
    exact (cf.natReg i (fun h=>hi (Or.inr h))).trans (fr.natReg i (fun h=>hi (Or.inl h)))
  · intro i h100 h114;exact (cf.scalarReg i h100 h114).trans (congrFun fr.scalarReg i)
  · intro z hD hE;exact (cf.scalarHeap z hD hE).trans (congrFun fr.scalarHeap z)
 exact ⟨u,total,up,values,frame⟩

end
end ExactFourierCircuits.UniformRecursiveResidualInverse
