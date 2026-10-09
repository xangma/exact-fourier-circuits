import UniformTransposeDescriptorMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafOrientationsMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformDirectLeafDescriptorMachine (rows printCost)
open UniformTransposeDescriptorMachine (leafRecords Record Bank recordAt reverseWords)
def beforeDiv:List Op:=[.sub 5500 5414 5403,.literal 5503 4]
def afterDiv:List Op:=[.literal 5504 0,.add 5501 5403 5504,.add 5502 5404 5504]
/-- Both literal orientations are produced from the genuine forward leaf bank.
Nat5404 is the fresh transposed-bank address; N is computed by charged division
of the forward printer's actual final cursor. -/
def program:Program:=UniformDirectLeafDescriptorMachine.program.map (relocate 0 34)++
 beforeDiv.map Op.code++[.natBinary .div 5500 5500 5503]++afterDiv.map Op.code++
 UniformTransposeDescriptorMachine.program.map (relocate 40 67)++[.halt]
lemma program_length:program.length=68:=rfl
lemma forward_code:CodeAt UniformDirectLeafDescriptorMachine.program program 0 34:=by
 intro i hi;change i<34 at hi;interval_cases i <;>rfl
lemma before_code:BlockAt beforeDiv program 34:=by intro i hi;change i<2 at hi;interval_cases i <;>rfl
lemma div_at:program[36]?=some (.natBinary .div 5500 5500 5503):=rfl
lemma after_code:BlockAt afterDiv program 37:=by intro i hi;change i<3 at hi;interval_cases i <;>rfl
lemma transpose_code:CodeAt UniformTransposeDescriptorMachine.program program 40 67:=by
 intro i hi;change i<27 at hi;interval_cases i <;>rfl
lemma halt_at:program[67]?=some .halt:=rfl
noncomputable section
structure Frame(s u:State):Prop where
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,r<5410∨5520≤r→u.natReg r=s.natReg r
lemma setup_frame(s:State)(N:ℕ):Frame s (applyBlock afterDiv (writeNat (applyBlock beforeDiv s) 5500 N)):=by
 refine ⟨rfl,rfl,rfl,rfl,?_⟩;intro r hr
 simp (disch:=omega) [beforeDiv,afterDiv,applyBlock,Op.apply,writeNat,next]

lemma setup(n D E N B:ℕ)(x:Fin n→ℂ)(s:State)(pc:s.pc=34)(hs:WordBound B s)
 (source:s.natReg 5403=D)(dest:s.natReg 5404=E)(ptr:s.natReg 5414=D+4*N)(code:68≤B)(extent:D+4*N≤B):
 ∃u,BoundedRuns program n x B s 6 u∧u.pc=40∧UniformTransposeDescriptorMachine.Header N D E u∧
 u.natHeap=s.natHeap∧Frame s u:=by
 have eb:=hs.2.1 5404;rw [dest] at eb
 have nb:N≤B:=by omega
 have safe:readable beforeDiv s∧peak beforeDiv s≤B:=by
   simp [beforeDiv,readable,peak,Op.readable,Op.peak,source,ptr];omega
 have aRun:=block_runs beforeDiv program 34 n B x s before_code pc hs (by change 36≤B;omega) safe.1 safe.2
 let a:=applyBlock beforeDiv s
 have ap:a.pc=36:=by rw [applyBlock_pc,pc];rfl
 have av:a.natReg 5500=4*N:=by simp [a,beforeDiv,applyBlock,Op.apply,writeNat,next,source,ptr]
 have four:a.natReg 5503=4:=by simp [a,beforeDiv,applyBlock,Op.apply,writeNat,next]
 have dStep:step program n x a=.running (writeNat a 5500 N):=by
   simp [step,ap,div_at,evalNat,av,four]
 let d:=writeNat a 5500 N
 have dBound:=writeNat_bound B a 5500 N aRun.final_bound (by rw [ap];omega) nb
 have dRun:BoundedRuns program n x B a 1 d:=.next aRun.final_bound dStep (.refl dBound)
 have dp:d.pc=37:=by simp [d,writeNat,next,ap]
 have sd:d.natReg 5403=D:=by simp [d,a,beforeDiv,applyBlock,Op.apply,writeNat,next,source]
 have ed:d.natReg 5404=E:=by simp [d,a,beforeDiv,applyBlock,Op.apply,writeNat,next,dest]
 have nReady:d.natReg 5500=N:=by simp [d,writeNat,next]
 have safeTail:readable afterDiv d∧peak afterDiv d≤B:=by
   simp [afterDiv,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,sd,ed];omega
 have zRun:=block_runs afterDiv program 37 n B x d after_code dp dBound (by change 40≤B;omega) safeTail.1 safeTail.2
 let u:=applyBlock afterDiv d
 refine ⟨u,?_,?_,?_,rfl,setup_frame s N⟩
 · convert aRun.trans (dRun.trans zRun) using 1;change 6=2+(1+3);rfl
 · rw [applyBlock_pc,dp];rfl
 · constructor
   · simp [u,afterDiv,applyBlock,Op.apply,writeNat,next,nReady]
   · simp [u,afterDiv,applyBlock,Op.apply,writeNat,next,sd]
   · simp [u,afterDiv,applyBlock,Op.apply,writeNat,next,ed]

/-- One fixed program physically produces both orientations; the transpose
count, source header and destination header are installed by its own bytecode. -/
theorem execution(n v o K D E B:ℕ)(x:Fin n→ℂ)(s:State)
 (h:UniformDirectLeafDescriptorMachine.Header v o K D s)(dest:s.natReg 5404=E)
 (pc:s.pc=0)(hs:WordBound B s)(code:68≤B)(ob:o+v≤B)(kb:K+v≤B)
 (db:D+4*(leafRecords v o K).length≤B)(eb:E+4*(leafRecords v o K).length≤B)
 (apart:D+4*(leafRecords v o K).length≤E):
 ∃u,BoundedExecution program n x B s (34*(leafRecords v o K).length+23) u∧u.pc=67∧
 UniformFixedNetworkScheduleMachine.Printed D (rows o K v) u∧
 UniformFixedNetworkScheduleMachine.Printed E (reverseWords (recordAt (leafRecords v o K)) (leafRecords v o K).length) u∧
 u.natReg 5514=E+4*(leafRecords v o K).length∧Frame s u:=by
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
 refine ⟨setPC u 67,?_,rfl,?_,newBank,endPtr,?_⟩
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
end
end ExactFourierCircuits.UniformDirectLeafOrientationsMachine
