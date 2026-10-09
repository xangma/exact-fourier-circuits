import UniformDirectLeafOrientationsMachine
import UniformAllAxisSeedPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformStoredDirectLeafOrientations
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformDirectLeafDescriptorMachine (rows printCost)
open UniformTransposeDescriptorMachine (leafRecords Record Bank recordAt reverseWords)
open UniformDirectLeafOrientationsMachine
noncomputable section

/-- Strengthen the existing fixed68 result with its two-bank Nat heap frame. -/
theorem orientations_execution(n v o K D E B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:UniformDirectLeafDescriptorMachine.Header v o K D s)(dest:s.natReg 5404=E)
 (pc:s.pc=0)(hs:WordBound B s)(code:68≤B)(ob:o+v≤B)(kb:K+v≤B)
 (db:D+4*(leafRecords v o K).length≤B)(eb:E+4*(leafRecords v o K).length≤B)
 (apart:D+4*(leafRecords v o K).length≤E):
 ∃u,BoundedExecution program n x B s (34*(leafRecords v o K).length+23) u∧u.pc=67∧
 UniformFixedNetworkScheduleMachine.Printed D (rows o K v) u∧
 UniformFixedNetworkScheduleMachine.Printed E (reverseWords (recordAt (leafRecords v o K)) (leafRecords v o K).length) u∧
 u.natReg 5514=E+4*(leafRecords v o K).length∧Frame s u∧
 (∀a,(a<D∨D+4*(leafRecords v o K).length≤a)→
 (a<E∨E+4*(leafRecords v o K).length≤a)→u.natHeap a=s.natHeap a):=by
 let N:ℕ:=(leafRecords v o K).length
 have rowsLen:(rows o K v).length=4*N:=by
   rw [←UniformTransposeDescriptorMachine.leafRecords_words,UniformTransposeDescriptorMachine.flatWords_length]
 have cost:printCost v=14*N:=by
   rw [UniformDirectLeafDescriptorMachine.printCost_closed]
   unfold N;rw [UniformTransposeDescriptorMachine.leafRecords_length]
 obtain ⟨a,forward,ap,printed,ptr,outside,af⟩:=UniformDirectLeafDescriptorMachine.execution n v o K D B x s h pc hs
   (by omega) ob kb (by rw [rowsLen];exact db)
 have forwardPlaced:=UniformBoundedAssembly.boundedExecution_placed forward_code (by change 34≤B;omega) (by omega) forward
 have fr:BoundedRuns program n x B s (printCost v+8) (setPC a 34):=by
   simpa only [placed,Nat.zero_add,setPC] using forwardPlaced
 have ad:a.natReg 5403=D:=(af.natReg 5403 (by omega)).trans h.base
 have ae:a.natReg 5404=E:=(af.natReg 5404 (by omega)).trans dest
 have aPtr:a.natReg 5414=D+4*N:=by simpa only [rowsLen] using ptr
 obtain ⟨z,setupRun,zp,header,zHeap,zf⟩:=setup n D E N B x (setPC a 34) rfl fr.final_bound ad ae aPtr code db
 have bankA:Bank D N (recordAt (leafRecords v o K)) a:=
   UniformTransposeDescriptorMachine.bank_of_printed D (leafRecords v o K) a (by rw [UniformTransposeDescriptorMachine.leafRecords_words];exact printed)
 have bankZ:Bank D N (recordAt (leafRecords v o K)) (setPC z 0):=by
   intro i hi j
   change z.natHeap (D+4*i+j.val)=some ((recordAt (leafRecords v o K) i).words[j.val]'j.isLt)
   rw [zHeap];exact bankA i hi j
 obtain ⟨u,transposeRun,up,newBank,retained,endPtr,outsideTranspose,tf⟩:=UniformTransposeDescriptorMachine.execution n N D E B
   (recordAt (leafRecords v o K)) x (setPC z 0)
   ⟨header.count,header.source,header.dest⟩ rfl (changePC_bound B z 0 setupRun.final_bound (by omega)) bankZ (by omega) db eb apart
 have transPlaced:=UniformBoundedAssembly.boundedExecution_placed transpose_code (by change 67≤B;omega) (by omega) transposeRun
 have placedZ:placed 40 (setPC z 0)=z:=by cases z;simp_all [placed,setPC]
 have tr:BoundedRuns program n x B z (20*N+8) (setPC u 67):=by
   change BoundedRuns program n x B (placed 40 (setPC z 0)) (20*N+8) (setPC u 67) at transPlaced
   rw [placedZ] at transPlaced
   exact transPlaced
 have halt:BoundedExecution program n x B (setPC u 67) 1 (setPC u 67):=
   .halt tr.final_bound (by simp [step,setPC,halt_at])
 refine ⟨setPC u 67,?_,rfl,?_,newBank,endPtr,?_,?_⟩
 · convert fr.executes (setupRun.executes (tr.executes halt)) using 1
   change 34*N+23=(printCost v+8)+(6+((20*N+8)+1));rw [cost];omega
 · intro j hj
   have jB:j<4*N:=by rw [rowsLen] at hj;exact hj
   change u.natHeap (D+j)=some ((rows o K v)[j]'hj)
   rw [outsideTranspose (D+j) (Or.inl (by omega))]
   change z.natHeap (D+j)=some ((rows o K v)[j]'hj)
   rw [zHeap]
   exact printed j hj
 · refine ⟨tf.scalarHeap.trans (zf.scalarHeap.trans af.scalarHeap),
     tf.scalarReg.trans (zf.scalarReg.trans af.scalarReg),
     tf.outputs.trans (zf.outputs.trans af.outputs),tf.roots.trans (zf.roots.trans af.roots),?_⟩
   intro r hr
   exact (tf.natReg r (by omega)).trans ((zf.natReg r hr).trans (af.natReg r (by omega)))
 · intro a hD hE
   change u.natHeap a=s.natHeap a
   rw [outsideTranspose a hE]
   change z.natHeap a=s.natHeap a
   rw [zHeap]
   exact outside a (by simpa only [rowsLen] using hD)

/-- Actual node address, original [pool,radix] directory address and fresh banks
are the only raw register headers. The subtree offset never shifts kernel indices. -/
def reader:List Op:=[.getNat 5400 5600,.literal 5610 1,.add 5611 5600 5610,
 .getNat 5401 5611,.getNat 5613 5601,.add 5611 5601 5610,.getNat 5612 5611,
 .literal 5614 3,.mul 5614 5612 5614,.add 5402 5613 5614,
 .literal 5610 0,.add 5403 5602 5610,.add 5404 5603 5610]
def program:Program:=reader.map Op.code++
 UniformDirectLeafOrientationsMachine.program.map (relocate 13 81)++[.halt]
lemma program_length:program.length=82:=rfl
lemma reader_code:BlockAt reader program 0:=by
 intro i hi;change i<13 at hi;interval_cases i <;>rfl
lemma child_code:CodeAt UniformDirectLeafOrientationsMachine.program program 13 81:=by
 intro i hi;change i<68 at hi;interval_cases i <;>rfl
lemma halt_at:program[81]?=some .halt:=rfl

structure Header(P Q D E:ℕ)(s:State):Prop where
 node:s.natReg 5600=P
 directory:s.natReg 5601=Q
 forward:s.natReg 5602=D
 transpose:s.natReg 5603=E
structure Stored(v o A r P Q:ℕ)(s:State):Prop where
 width:s.natHeap P=some v
 offset:s.natHeap (P+1)=some o
 pool:s.natHeap Q=some A
 radix:s.natHeap (Q+1)=some r
structure Frame(s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,(j<5400∨5520≤j)→(j<5610∨5615≤j)→u.natReg j=s.natReg j
lemma reader_frame(s:State):Frame s (applyBlock reader s):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro j hj hx
 simp (disch:=omega) [reader,applyBlock,Op.apply,writeNat,next]
lemma reader_heap(s:State):(applyBlock reader s).natHeap=s.natHeap:=rfl
lemma reader_header {v o A r P Q D E:ℕ}(s:State)(h:Header P Q D E s)(b:Stored v o A r P Q s):
 UniformDirectLeafDescriptorMachine.Header v o (A+3*r) D (applyBlock reader s)∧
 (applyBlock reader s).natReg 5404=E:=by
 constructor
 · constructor <;>simp [reader,applyBlock,Op.apply,writeNat,next,h.node,h.directory,h.forward,
     b.width,b.offset,b.pool,b.radix,Nat.mul_comm]
 · simp [reader,applyBlock,Op.apply,writeNat,next,h.transpose]
lemma reader_run(n v o A r P Q D E B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Header P Q D E s)(b:Stored v o A r P Q s)(pc:s.pc=0)(hs:WordBound B s)
 (code:82≤B)(pb:P+1≤B)(qb:Q+1≤B)(ob:o+v≤B)(kb:A+3*r+v≤B):
 BoundedRuns program n x B s 13 (applyBlock reader s):=by
 have dB:D≤B:=by simpa only [h.forward] using hs.2.1 5602
 have eB:E≤B:=by simpa only [h.transpose] using hs.2.1 5603
 have rB:r≤B:=hs.2.2.1 (Q+1) r b.radix |>.2
 apply block_runs reader program 0 n B x s reader_code pc hs (by change 13≤B;omega)
 · simp [reader,readable,Op.readable,Op.apply,writeNat,next,h.node,h.directory,
     b.width,b.offset,b.pool,b.radix]
 · simp [reader,peak,Op.peak,Op.apply,writeNat,next,h.node,h.directory,h.forward,h.transpose,
     b.width,b.offset,b.pool,b.radix];omega

/-- Raw stored node and original directory cells produce both genuine words,
with charged header construction, retained coefficient heaps and outside frames. -/
theorem execution(n v o A r P Q D E B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:Header P Q D E s)(b:Stored v o A r P Q s)(pc:s.pc=0)(hs:WordBound B s)
 (code:82≤B)(pb:P+1≤B)(qb:Q+1≤B)(ob:o+v≤B)(kb:A+3*r+v≤B)
 (db:D+4*(leafRecords v o (A+3*r)).length≤B)
 (eb:E+4*(leafRecords v o (A+3*r)).length≤B)
 (apart:D+4*(leafRecords v o (A+3*r)).length≤E):
 ∃u,BoundedExecution program n x B s (34*(leafRecords v o (A+3*r)).length+37) u∧u.pc=81∧
 UniformFixedNetworkScheduleMachine.Printed D (rows o (A+3*r) v) u∧
 UniformFixedNetworkScheduleMachine.Printed E
   (reverseWords (recordAt (leafRecords v o (A+3*r))) (leafRecords v o (A+3*r)).length) u∧
 u.natReg 5514=E+4*(leafRecords v o (A+3*r)).length∧Frame s u∧
 (∀a,(a<D∨D+4*(leafRecords v o (A+3*r)).length≤a)→
 (a<E∨E+4*(leafRecords v o (A+3*r)).length≤a)→u.natHeap a=s.natHeap a):=by
 have ready:=reader_run n v o A r P Q D E B x s h b pc hs code pb qb ob kb
 let z:=applyBlock reader s
 have zp:z.pc=13:=by rw [applyBlock_pc,pc];rfl
 obtain ⟨head,ep⟩:=reader_header s h b
 have headPC:UniformDirectLeafDescriptorMachine.Header v o (A+3*r) D (setPC z 0):=
   ⟨head.width,head.offset,head.kernel,head.base⟩
 obtain ⟨u,child,up,forward,transpose,ptr,frame,outside⟩:=orientations_execution n v o (A+3*r) D E B x
   (setPC z 0) headPC ep rfl (changePC_bound B z 0 ready.final_bound (by omega))
   (by omega) ob kb db eb apart
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed child_code (by change 81≤B;omega) (by omega) child
 have placedZ:placed 13 (setPC z 0)=z:=by
   change setPC z 13=z
   rw [←zp]
   cases z;rfl
 have cr:BoundedRuns program n x B z (34*(leafRecords v o (A+3*r)).length+23) (setPC u 81):=by
   change BoundedRuns program n x B (placed 13 (setPC z 0)) _ _ at placedRun
   rw [placedZ] at placedRun;exact placedRun
 have halt:BoundedExecution program n x B (setPC u 81) 1 (setPC u 81):=
   .halt cr.final_bound (by simp [step,setPC,halt_at])
 refine ⟨setPC u 81,?_,rfl,forward,transpose,ptr,?_,?_⟩
 · convert ready.executes (cr.executes halt) using 1
   omega
 · have rf:=reader_frame s
   refine ⟨frame.scalarHeap.trans rf.scalarHeap,frame.scalarReg.trans rf.scalarReg,
     frame.outputs.trans rf.outputs,frame.roots.trans rf.roots,?_⟩
   intro j hj hx
   exact (frame.natReg j (by omega)).trans (rf.natReg j hj hx)
 · intro a ha hb
   exact (outside a ha hb).trans (congrFun (reader_heap s) a)
/-- The real retained original directory supplies the loaded pool/radix cells. -/
lemma stored_from_retained {n k v o P:ℕ} (j:Fin (UniformAllAxisSeedPreparation.axisCount n))
 (s:State)(ret:UniformAllAxisSeedPreparation.Retained n k s)(hj:j.val<k)
 (width:s.natHeap P=some v)(offset:s.natHeap (P+1)=some o):
 Stored v o (UniformAllAxisSeedPreparation.axisBase n j.val)
   (UniformAllAxisSeedPreparation.radix n j) P
   (UniformAllAxisSeedPreparation.directoryBase n+2*j.val) s:=
 ⟨width,offset,ret.address j hj,ret.width j hj⟩

/-- Every compact coefficient lane and original directory cell survives. -/
lemma retained_frame {n k D E:ℕ}{s u:State}(ret:UniformAllAxisSeedPreparation.Retained n k s)
 (frame:Frame s u)(de:D≤E)
 (before:UniformAllAxisSeedPreparation.directoryBase n+2*UniformAllAxisSeedPreparation.axisCount n≤D)
 (outside:∀a,a<D→a<E→u.natHeap a=s.natHeap a):
 UniformAllAxisSeedPreparation.Retained n k u:=by
 constructor
 · intro j hj q i
   rw [frame.scalarHeap]
   exact ret.coefficients j hj q i
 · intro j hj
   have ji:=j.isLt
   rw [outside _ (by omega) (by omega)]
   exact ret.address j hj
 · intro j hj
   have ji:=j.isLt
   rw [outside _ (by omega) (by omega)]
   exact ret.width j hj
end
end ExactFourierCircuits.UniformStoredDirectLeafOrientations
