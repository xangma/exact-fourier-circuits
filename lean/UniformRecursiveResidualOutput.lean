import UniformRecursiveResidualInverse
import UniformRecursiveGroupBank
import UniformResidualOrientationBridge
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualOutput
open UniformMachine UniformAssembly
namespace P
export UniformRecursiveSavingProgram (Part program address)
end P
namespace R
export UniformRecursiveParentReturn (start_bound code_bound)
end R
namespace I
export UniformRecursiveResidualInverse (inverse_execution InverseFrame InverseChanged)
end I
namespace S
export UniformRecursiveResidualFinish (scatter_execution ScatterFrame ScatterChanged)
end S
noncomputable section

lemma jump_at:P.program[P.address .inverseTest]?=some (.jump (P.address .orientation)):=
 UniformRecursiveGroupExecution.zero_cell _ _ _ _
  (UniformRecursiveSavingExecution.part_at .inverseTest 0 (by decide)) rfl
lemma branch_at:P.program[P.address .orientation+19]?=
 some (.branchLT 4188 4153 (P.address .scatterSetup) (P.address .inverseSetup)):=
 UniformRecursiveSavingExecution.part_at .orientation 19 (by decide)

def selected(k q:ℕ)(qk:q ≤ k)(inv:Bool)(f:Fin (2^k)→Scalar)(j:Fin (2^k)):Scalar:=
 if inv then f ⟨j.val^^^(2^q-1),Nat.xor_lt_two_pow j.isLt (by
  have h:=Nat.pow_le_pow_right (by omega:1 ≤ 2) qk;have p:=Nat.two_pow_pos q;omega)⟩ else f j

structure TailFrame(D E V:ℕ)(s u:State):Prop where
 nativeBits:s.natReg 5300=s.natReg 4120→u.natReg 5300=s.natReg 4120
 nativeRest:s.natReg 5301=s.natReg 4127→u.natReg 5301=s.natReg 4127
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 scalarHeap:∀z,(z < D∨D+V ≤ z)→(z < E∨E+V ≤ z)→u.scalarHeap z=s.scalarHeap z
 natReg:∀i,¬I.InverseChanged i→¬S.ScatterChanged i→u.natReg i=s.natReg i

/-- The actual inverse flag branch, optional charged XOR translation and
scatter. Every readiness fact is supplied by the preceding physical gather
and completed group result, not by a semantic child callback. -/
theorem generic_execution(main:Program)(test iset inext scatter scnext exit flagRegister n B k q m r D E permTable xorTable:ℕ)(inv:Bool)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=test)(one:s.natReg 4153=1)
 (orientation:s.natReg flagRegister=if inv then 1 else 0)
 (bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)(size:s.natReg 4124=2^q)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (permutation:s.natReg 4067=permTable)(table:s.natReg 4068=xorTable)
 (geometry:k=q*m+r)(qp:1 ≤ q)(rp:r < m)(qk:q ≤ k)
 (perm:Fin (2^k)≃Fin (2^k))(physical:∀j,s.natHeap (permTable+j.val)=some (perm j).val)
 (f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (entries:UniformXorTableMachine.Entries q xorTable (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(permEnd:permTable+2^k ≤ B)(xorEnd:xorTable+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(square:(2^k)^2 ≤ B)
 (bound:WordBound B s)
 (testCode:main[test]?=some (.branchLT flagRegister 4153 scatter iset))
 (isCode:UniformNatBlockMachine.BlockAt UniformRecursiveResidualInverse.inverseOps main iset)
 (ijump:main[iset+13]?=some (.jump inext))
 (ilink:CodeAt UniformResidualNativeTranslationMachine.program main inext scatter)
 (ssCode:UniformNatBlockMachine.BlockAt UniformRecursiveResidualFinish.scatterOps main scatter)
 (sjump:main[scatter+6]?=some (.jump scnext))
 (slink:CodeAt UniformResidualArrayCopyMachine.program main scnext exit)
 (isetExtent:iset+14 ≤ B)(inextBound:inext ≤ B)(iExtent:inext+UniformResidualNativeTranslationMachine.program.length ≤ B)
 (scatterExtent:scatter+7 ≤ B)(scnextBound:scnext ≤ B)(sExtent:scnext+UniformResidualArrayCopyMachine.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s (if inv then (17*(m+r)+35)*2^k+39 else 10*2^k+12) u ∧
 u.pc=exit ∧
 (∀j,u.scalarHeap (E+(perm j).val)=some (selected k q qk inv f j)) ∧ TailFrame D E (2^k) s u:=by
 cases inv with
 | false=>
   let a:State:={s with pc:=scatter}
   have ab:=changePC_bound B s (scatter) bound (Nat.le_add_right scatter 7 |>.trans scatterExtent)
   have branch:BoundedRuns main n x B s 1 a:=.next bound
    (by simp [step,pc,testCode,orientation,one,a]) (.refl ab)
   have present:∀j:Fin (2^k),(a.scalarHeap (D+j.val)).isSome=true:=by intro j;rw [data j];rfl
   obtain ⟨u,run,up,values,fr⟩:=UniformRecursiveResidualFinish.scatter_generic main scatter scnext exit n B (2^k) permTable D E x a rfl one length src dst permutation
    perm physical present separate sourceEnd destEnd permEnd ab ssCode sjump slink scatterExtent scnextBound sExtent ret
   refine ⟨u,?_,up,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · convert branch.trans run using 1 <;> simp only [Bool.false_eq_true,ite_false] <;> omega
   · intro j;simpa only [selected,Bool.false_eq_true,ite_false] using (values j).trans (data j)
   · intro h;exact (fr.natReg 5300 (by unfold S.ScatterChanged UniformRecursiveResidualFinish.SetupChanged;omega)).trans h
   · intro h;exact (fr.natReg 5301 (by unfold S.ScatterChanged UniformRecursiveResidualFinish.SetupChanged;omega)).trans h
   · exact fr.natHeap
   · exact fr.outputs
   · exact fr.roots
   · intro z _ hE;exact fr.scalarHeap z hE
   · intro i _ hi;exact fr.natReg i hi
 | true=>
   let a:State:={s with pc:=iset}
   have ab:=changePC_bound B s (iset) bound (Nat.le_add_right iset 14 |>.trans isetExtent)
   have branch:BoundedRuns main n x B s 1 a:=.next bound
    (by simp [step,pc,testCode,orientation,one,a]) (.refl ab)
   obtain ⟨v,inverse,vp,values,fi⟩:=UniformRecursiveResidualInverse.inverse_generic main iset inext scatter n B k q m r D E xorTable x a rfl one bits length src dst width rest size table
    geometry qp rp qk f data entries separate xorEnd sourceEnd destEnd square ab isCode ijump ilink isetExtent inextBound iExtent (Nat.le_add_right scatter 7 |>.trans scatterExtent)
   have keep(i:ℕ)(hi:¬I.InverseChanged i):v.natReg i=s.natReg i:=fi.natReg i hi
   have vone:v.natReg 4153=1:=(keep _ (by unfold I.InverseChanged UniformRecursiveResidualInverse.SetupChanged UniformResidualNativeTranslationMachine.Changed;omega)).trans one
   have vl:v.natReg 4122=2^k:=(keep _ (by unfold I.InverseChanged UniformRecursiveResidualInverse.SetupChanged UniformResidualNativeTranslationMachine.Changed;omega)).trans length
   have vs:v.natReg 4091=D:=(keep _ (by unfold I.InverseChanged UniformRecursiveResidualInverse.SetupChanged UniformResidualNativeTranslationMachine.Changed;omega)).trans src
   have vd:v.natReg 4090=E:=(keep _ (by unfold I.InverseChanged UniformRecursiveResidualInverse.SetupChanged UniformResidualNativeTranslationMachine.Changed;omega)).trans dst
   have vt:v.natReg 4067=permTable:=(keep _ (by unfold I.InverseChanged UniformRecursiveResidualInverse.SetupChanged UniformResidualNativeTranslationMachine.Changed;omega)).trans permutation
   have pbank:∀j,v.natHeap (permTable+j.val)=some (perm j).val:=by intro j;rw [fi.natHeap];exact physical j
   have present:∀j:Fin (2^k),(v.scalarHeap (D+j.val)).isSome=true:=by intro j;rw [values j];rfl
   obtain ⟨u,scatter,up,result,fs⟩:=UniformRecursiveResidualFinish.scatter_generic main scatter scnext exit n B (2^k) permTable D E x v vp vone vl vs vd vt
    perm pbank present separate sourceEnd destEnd permEnd inverse.final_bound ssCode sjump slink scatterExtent scnextBound sExtent ret
   refine ⟨u,?_,up,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · convert branch.trans (inverse.trans scatter) using 1 <;> simp only [ite_true] <;> ring
   · intro j
     have h:=(result j).trans (values j)
     simp only [selected,ite_true,UniformResidualNativeTranslationMachine.translated,
      UniformResidualNativeTranslationMachine.partner] at h ⊢
     convert h using 1
     congr 2
   · intro _;exact (fs.natReg 5300 (by unfold S.ScatterChanged UniformRecursiveResidualFinish.SetupChanged;omega)).trans fi.nativeBits
   · intro _;exact (fs.natReg 5301 (by unfold S.ScatterChanged UniformRecursiveResidualFinish.SetupChanged;omega)).trans fi.nativeRest
   · exact fs.natHeap.trans fi.natHeap
   · exact fs.outputs.trans fi.outputs
   · exact fs.roots.trans fi.roots
   · intro z hD hE;exact (fs.scalarHeap z hE).trans (fi.scalarHeap z hD hE)
   · intro i hi hs;exact (fs.natReg i hs).trans (fi.natReg i hi)


structure Frame(D E V:ℕ)(s u:State):Prop where
 nativeBits:s.natReg 5300=s.natReg 4120→u.natReg 5300=s.natReg 4120
 nativeRest:s.natReg 5301=s.natReg 4127→u.natReg 5301=s.natReg 4127
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 scalarHeap:∀z,(z < D∨D+V ≤ z)→(z < E∨E+V ≤ z)→u.scalarHeap z=s.scalarHeap z
 natReg:∀i,¬I.InverseChanged i→¬S.ScatterChanged i→¬UniformResidualOrientationMachine.Changed i→u.natReg i=s.natReg i

/-- The original residual direction is scanned by real bytecode after all
returned children. Its weight-three phase is combined with the retained raw
geometric flag before the inverse/scatter branch. -/
theorem oriented_generic(main:Program)(test orient iset inext scatter scnext exit n B k q m r D E permTable xorTable U:ℕ)(decreasing:Bool)
 (v:BinaryFrames.Vec (Fin m))(hv:BinaryFrames.dot v v=1)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=test)(one:s.natReg 4153=1)
 (orientation:s.natReg 4131=if decreasing then 1 else 0)
 (direction:s.natReg 4062=U)(source:UniformRepeatedMaskMachine.Source U v s)(directionEnd:U+m ≤ B)
 (bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)(size:s.natReg 4124=2^q)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (permutation:s.natReg 4067=permTable)(table:s.natReg 4068=xorTable)
 (geometry:k=q*m+r)(qp:1 ≤ q)(rp:r < m)(qk:q ≤ k)
 (perm:Fin (2^k)≃Fin (2^k))(physical:∀j,s.natHeap (permTable+j.val)=some (perm j).val)
 (f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (entries:UniformXorTableMachine.Entries q xorTable (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(permEnd:permTable+2^k ≤ B)(xorEnd:xorTable+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(square:(2^k)^2 ≤ B)
 (bound:WordBound B s)
 (jumpCell:main[test]?=some (.jump orient))
 (scanLink:CodeAt UniformResidualOrientationMachine.program main orient (orient+19))
 (branchCell:main[orient+19]?=some (.branchLT 4188 4153 scatter iset))
 (isCode:UniformNatBlockMachine.BlockAt UniformRecursiveResidualInverse.inverseOps main iset)
 (ijump:main[iset+13]?=some (.jump inext))
 (ilink:CodeAt UniformResidualNativeTranslationMachine.program main inext scatter)
 (ssCode:UniformNatBlockMachine.BlockAt UniformRecursiveResidualFinish.scatterOps main scatter)
 (sjump:main[scatter+6]?=some (.jump scnext))
 (slink:CodeAt UniformResidualArrayCopyMachine.program main scnext exit)
 (scanExtent:orient+20 ≤ B)
 (isetExtent:iset+14 ≤ B)(inextBound:inext ≤ B)(iExtent:inext+UniformResidualNativeTranslationMachine.program.length ≤ B)
 (scatterExtent:scatter+7 ≤ B)(scnextBound:scnext ≤ B)(sExtent:scnext+UniformResidualArrayCopyMachine.program.length ≤ B)(ret:exit ≤ B):∃u,
 BoundedRuns main n x B s
  (1+UniformResidualOrientationMachine.ticks v+
   if UniformResidualFibers.inverseOrientation v decreasing then (17*(m+r)+35)*2^k+39 else 10*2^k+12) u ∧
 u.pc=exit ∧
 (∀j,u.scalarHeap (E+(perm j).val)=some (selected k q qk (UniformResidualFibers.inverseOrientation v decreasing) f j)) ∧
 Frame D E (2^k) s u:=by
 let a:State:={s with pc:=orient}
 have ab:=changePC_bound B s (orient) bound (by omega)
 have jump:BoundedRuns main n x B s 1 a:=.next bound
  (by simp only [step,pc,jumpCell];rfl) (.refl ab)
 let caller:State:={a with pc:=0}
 have cb:=changePC_bound B a 0 ab (by omega)
 have small:19 ≤ B:=by omega
 obtain ⟨done,scan,stop,value,fr⟩:=UniformResidualOrientationMachine.execution m U
  (if decreasing then 1 else 0) B n v x caller rfl width direction orientation
  (by cases decreasing <;> decide) source cb small directionEnd
 have placedScan:=UniformBoundedAssembly.boundedExecution_placed
  scanLink (by rw [UniformResidualOrientationMachine.program_length];omega)
  (by omega) scan
 have same:placed (orient) caller=a:=by
  change {a with pc:=orient}=a
  rfl
 rw [same] at placedScan
 let b:State:={done with pc:=orient+19}
 have bp:b.pc=orient+19:=rfl
 have keep(j:ℕ)(h:¬UniformResidualOrientationMachine.Changed j):b.natReg j=s.natReg j:=fr.natReg j h
 have bo:b.natReg 4153=1:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans one
 have bb:b.natReg 4120=k:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans bits
 have bl:b.natReg 4122=2^k:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans length
 have bz:b.natReg 4124=2^q:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans size
 have bs:b.natReg 4091=D:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans src
 have bd:b.natReg 4090=E:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans dst
 have bw:b.natReg 4061=m:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans width
 have br:b.natReg 4127=r:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans rest
 have bperm:b.natReg 4067=permTable:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans permutation
 have bt:b.natReg 4068=xorTable:=(keep _ (by unfold UniformResidualOrientationMachine.Changed;omega)).trans table
 have orientationB:b.natReg 4188=if UniformResidualFibers.inverseOrientation v decreasing then 1 else 0:=by
  exact value.trans (UniformResidualOrientationBridge.effective_orientation v hv decreasing)
 have physicalB:∀j,b.natHeap (permTable+j.val)=some (perm j).val:=by intro j;rw [fr.natHeap];exact physical j
 have dataB:∀j,b.scalarHeap (D+j.val)=some (f j):=by intro j;rw [fr.scalarHeap];exact data j
 have entriesB:UniformXorTableMachine.Entries q xorTable (2^q*2^q) b:=by
  intro j hj
  change done.natHeap (xorTable+j)=_
  rw [fr.natHeap]
  exact entries j hj
 obtain ⟨u,run,up,values,uf⟩:=generic_execution main (orient+19)
  (iset) (inext) (scatter) (scnext)
  (exit) 4188 n B k q m r D E permTable xorTable
  (UniformResidualFibers.inverseOrientation v decreasing) x b bp bo orientationB bb bl bz bs bd bw br bperm bt
  geometry qp rp qk perm physicalB f dataB entriesB separate permEnd xorEnd sourceEnd destEnd square
  placedScan.final_bound branchCell isCode ijump ilink ssCode sjump slink
  isetExtent inextBound iExtent scatterExtent scnextBound sExtent ret
 refine ⟨u,?_,up,values,?_,?_,?_,?_,?_,?_,?_⟩
 · exact (jump.trans placedScan).trans run
 · intro h
   have h0:b.natReg 5300=b.natReg 4120:=by rw [keep 5300 (by unfold UniformResidualOrientationMachine.Changed;omega),bb];exact h.trans bits
   exact (uf.nativeBits h0).trans (keep 4120 (by unfold UniformResidualOrientationMachine.Changed;omega))
 · intro h
   have h0:b.natReg 5301=b.natReg 4127:=by rw [keep 5301 (by unfold UniformResidualOrientationMachine.Changed;omega),br];exact h.trans rest
   exact (uf.nativeRest h0).trans (keep 4127 (by unfold UniformResidualOrientationMachine.Changed;omega))
 · exact uf.natHeap.trans fr.natHeap
 · exact uf.outputs.trans fr.outputs
 · exact uf.roots.trans fr.roots
 · intro z d e;exact (uf.scalarHeap z d e).trans (congrFun fr.scalarHeap z)
 · intro j hi hs hc;exact (uf.natReg j hi hs).trans (keep j hc)

theorem execution(n B k q m r D E permTable xorTable U:ℕ)(decreasing:Bool)
 (v:BinaryFrames.Vec (Fin m))(hv:BinaryFrames.dot v v=1)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=P.address .inverseTest)(one:s.natReg 4153=1)
 (orientation:s.natReg 4131=if decreasing then 1 else 0)
 (direction:s.natReg 4062=U)(source:UniformRepeatedMaskMachine.Source U v s)(directionEnd:U+m ≤ B)
 (bits:s.natReg 4120=k)(length:s.natReg 4122=2^k)(size:s.natReg 4124=2^q)
 (src:s.natReg 4091=D)(dst:s.natReg 4090=E)(width:s.natReg 4061=m)(rest:s.natReg 4127=r)
 (permutation:s.natReg 4067=permTable)(table:s.natReg 4068=xorTable)
 (geometry:k=q*m+r)(qp:1 ≤ q)(rp:r < m)(qk:q ≤ k)
 (perm:Fin (2^k)≃Fin (2^k))(physical:∀j,s.natHeap (permTable+j.val)=some (perm j).val)
 (f:Fin (2^k)→Scalar)(data:∀j,s.scalarHeap (D+j.val)=some (f j))
 (entries:UniformXorTableMachine.Entries q xorTable (2^q*2^q) s)
 (separate:D+2^k ≤ E∨E+2^k ≤ D)(permEnd:permTable+2^k ≤ B)(xorEnd:xorTable+2^q*2^q ≤ B)
 (sourceEnd:D+2^k ≤ B)(destEnd:E+2^k ≤ B)(square:(2^k)^2 ≤ B)
 (bound:WordBound B s)(code:P.program.length ≤ B):∃u,
 BoundedRuns P.program n x B s
  (1+UniformResidualOrientationMachine.ticks v+
   if UniformResidualFibers.inverseOrientation v decreasing then (17*(m+r)+35)*2^k+39 else 10*2^k+12) u ∧
 u.pc=P.address .directionNext ∧
 (∀j,u.scalarHeap (E+(perm j).val)=some (selected k q qk (UniformResidualFibers.inverseOrientation v decreasing) f j)) ∧
 Frame D E (2^k) s u :=by
 exact oriented_generic P.program (P.address .inverseTest) (P.address .orientation)
  (P.address .inverseSetup) (P.address .inverse) (P.address .scatterSetup) (P.address .scatter)
  (P.address .directionNext) n B k q m r D E permTable xorTable U decreasing v hv x s
  pc one orientation direction source directionEnd bits length size src dst width rest permutation table
  geometry qp rp qk perm physical f data entries separate permEnd xorEnd sourceEnd destEnd square bound
  jump_at UniformRecursiveSavingProgram.orientation_code branch_at
  UniformRecursiveResidualInverse.inverse_setup_code UniformRecursiveResidualInverse.inverse_jump
  UniformRecursiveResidualInverse.inverse_code UniformRecursiveResidualFinish.scatter_setup_code
  UniformRecursiveResidualFinish.scatter_jump UniformRecursiveResidualFinish.scatter_code
  (R.code_bound .orientation 20 B rfl code)
  (R.code_bound .inverseSetup 14 B rfl code) (R.start_bound .inverse B code)
  (R.code_bound .inverse UniformResidualNativeTranslationMachine.program.length B rfl code)
  (R.code_bound .scatterSetup 7 B rfl code) (R.start_bound .scatter B code)
  (R.code_bound .scatter UniformResidualArrayCopyMachine.program.length B rfl code) (R.start_bound .directionNext B code)

end
end ExactFourierCircuits.UniformRecursiveResidualOutput
