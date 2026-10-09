import UniformScalarZeroFillMachine
import UniformPermutationMachine
import UniformNatBlockMachine
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRoleInputMachine
open UniformMachine UniformAssembly UniformBoundedAssembly
namespace F
export UniformScalarZeroFillMachine (program Frame)
end F
namespace C
export UniformScalarCopyMachine (program Source Outside Frame NatFrame)
end C
namespace P
export UniformPermutationMachine (program Source Outside Frame)
end P
namespace N
export UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
end N
open N

def copySetup:List Op:=[.binary .mul 147 6301 6311,.binary .mul 148 6303 6311,
 .binary .mul 149 6302 6311]
def kernelSetup:List Op:=[.binary .mul 70 6301 6311,.binary .mul 71 6304 6311,
 .binary .add 72 6302 6301,.binary .mul 73 6305 6311]
def program:Program:=F.program.map (relocate 0 10)++copySetup.map ExactFourierCircuits.UniformNatBlockMachine.Op.code++[.jump 14]++
 C.program.map (relocate 14 24)++kernelSetup.map ExactFourierCircuits.UniformNatBlockMachine.Op.code++[.jump 29]++
 P.program.map (relocate 29 41)++[.halt]
lemma program_length:program.length=42:=rfl
lemma fill_code:CodeAt F.program program 0 10:=by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma copy_setup_code:BlockAt copySetup program 10:=by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma copy_jump:program[13]?=some (.jump 14):=rfl
lemma copy_code:CodeAt C.program program 14 24:=by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma kernel_setup_code:BlockAt kernelSetup program 24:=by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma kernel_jump:program[28]?=some (.jump 29):=rfl
lemma kernel_code:CodeAt P.program program 29 41:=by
 intro i hi;change i<12 at hi;interval_cases i <;> rfl
lemma halt_at:program[41]?=some .halt:=rfl
noncomputable section

def Protected(j:ℕ):Prop:=(j<70∨81≤j)∧(j<147∨154≤j)∧(j<6310∨6314≤j)
structure Frame(s u:State):Prop where
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀j,Protected j→u.natReg j=s.natReg j
 scalarReg:∀j,j≠20→j≠32→j≠94→u.scalarReg j=s.scalarReg j
lemma Frame.trans{s t u:State}(a:Frame s t)(b:Frame t u):Frame s u:=
 ⟨b.natHeap.trans a.natHeap,b.outputs.trans a.outputs,b.roots.trans a.roots,
  fun j h=>(b.natReg j h).trans (a.natReg j h),
  fun j h20 h32 h94=>(b.scalarReg j h20 h32 h94).trans (a.scalarReg j h20 h32 h94)⟩
lemma Frame.withPC{s u:State}(h:Frame s u)(pc:ℕ):Frame s {u with pc:=pc}:=by
 cases h;constructor <;> assumption
lemma Frame.beforePC{s u:State}(h:Frame s u)(pc:ℕ):Frame {s with pc:=pc} u:=by
 cases h;constructor <;> assumption
lemma Frame.fill{s u:State}(h:F.Frame s u):Frame s u:=
 ⟨h.natHeap,h.outputs,h.roots,fun j hj=>h.natReg j hj.2.2,fun j _ _ hj=>h.scalarReg j hj⟩
lemma Frame.copy{s u:State}(h:C.Frame s u)(hn:C.NatFrame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,fun j hj=>hn j hj.2.1,fun j _ hj _=>h.2.2.2 j hj⟩
lemma Frame.kernel{s u:State}(h:P.Frame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,fun j hj=>h.2.2.2.2 j (by rcases hj.1 with lo|hi <;> omega),
  fun j hj _ _=>h.2.2.2.1 j hj⟩

lemma copy_setup_regs(s:State)(one:s.natReg 6311=1):
 (applyBlock copySetup s).natReg 147=s.natReg 6301∧
 (applyBlock copySetup s).natReg 148=s.natReg 6303∧
 (applyBlock copySetup s).natReg 149=s.natReg 6302:=by
 simp[copySetup,applyBlock,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,evalNat,one]
lemma copy_setup_frame(s:State):Frame s (applyBlock copySetup s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   have h:=hj.2.1
   simp[copySetup,applyBlock,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,show j≠147 by omega,
    show j≠148 by omega,show j≠149 by omega]
 · intro j _ _ _;rfl
lemma copy_setup_heap(s:State):(applyBlock copySetup s).scalarHeap=s.scalarHeap:=rfl
lemma copy_setup_peak(B:ℕ)(s:State)(one:s.natReg 6311=1)(bound:WordBound B s):
 peak copySetup s≤B:=by
 simp[peak,copySetup,ExactFourierCircuits.UniformNatBlockMachine.Op.peak,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,evalNat,one]
 exact ⟨bound.2.1 6301,bound.2.1 6303,bound.2.1 6302⟩
lemma kernel_setup_regs(s:State)(one:s.natReg 6311=1):
 (applyBlock kernelSetup s).natReg 70=s.natReg 6301∧
 (applyBlock kernelSetup s).natReg 71=s.natReg 6304∧
 (applyBlock kernelSetup s).natReg 72=s.natReg 6302+s.natReg 6301∧
 (applyBlock kernelSetup s).natReg 73=s.natReg 6305:=by
 simp[kernelSetup,applyBlock,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,evalNat,one]
lemma kernel_setup_frame(s:State):Frame s (applyBlock kernelSetup s):=by
 constructor
 · rfl
 · rfl
 · rfl
 · intro j hj
   have h:=hj.1
   simp[kernelSetup,applyBlock,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,show j≠70 by omega,
    show j≠71 by omega,show j≠72 by omega,show j≠73 by omega]
 · intro j _ _ _;rfl
lemma kernel_setup_peak(B:ℕ)(s:State)(one:s.natReg 6311=1)(bound:WordBound B s)
 (dest:s.natReg 6302+s.natReg 6301≤B):peak kernelSetup s≤B:=by
 simp[peak,kernelSetup,ExactFourierCircuits.UniformNatBlockMachine.Op.peak,ExactFourierCircuits.UniformNatBlockMachine.Op.apply,writeNat,next,evalNat,one]
 exact ⟨bound.2.1 6304,dest,bound.2.1 6305⟩
lemma block_pc(b:List Op)(s:State):(applyBlock b s).pc=s.pc+b.length:=by
 induction b generalizing s with
 | nil=>rfl
 | cons o b ih=>rw[applyBlock,ih,ExactFourierCircuits.UniformNatBlockMachine.Op.apply_pc,List.length_cons];omega

def roleValue{V:ℕ}(input kernel:Fin V→Scalar)(alpha:Fin V≃Fin V)(i:ℕ)(j:Fin V):Scalar:=
 if i=0 then input j else if i=1 then kernel (alpha j) else Scalar.zero
lemma jump_run(n B site ret:ℕ)(x:Fin n→ℂ)(s:State)(code:program[site]?=some (.jump ret))
 (pc:s.pc=site)(bound:WordBound B s)(fit:ret≤B):
 BoundedRuns program n x B s 1 {s with pc:=ret}:=by
 exact .next bound (by simp[step,pc,code]) (.refl (changePC_bound _ _ _ bound fit))

/-- Initialize arbitrary W role banks from the actually present alpha-input,
prepared-kernel source and physical alpha table. Helpers and all header installs
execute continuously; no role-output/table/action certificate is assumed. -/
theorem execution(n B W V S inputBase kernelBase alphaBase:ℕ)(x:Fin n→ℂ)
 (input kernel:Fin V→Scalar)(alpha:Fin V≃Fin V)(s:State)
 (pc:s.pc=0)(roles:2≤W)(hW:s.natReg 6300=W)(hV:s.natReg 6301=V)
 (hS:s.natReg 6302=S)(hI:s.natReg 6303=inputBase)(hK:s.natReg 6304=kernelBase)
 (hA:s.natReg 6305=alphaBase)(hInput:∀j,s.scalarHeap (inputBase+j.val)=some (input j))
 (hKernel:∀j,s.scalarHeap (kernelBase+j.val)=some (kernel j))
 (hAlpha:UniformGlobalNatPreparation.PermutationBank V alphaBase s.natHeap alpha)
 (inputBefore:inputBase+V≤S)(kernelBefore:kernelBase+V≤S)
 (extent:S+W*V≤B)(tableFit:alphaBase+V≤B)(code:42≤B)(bound:WordBound B s):∃u,
 BoundedExecution program n x B s (5*(W*V)+16*V+24) u∧u.pc=41∧
 (∀i:Fin W,∀j:Fin V,u.scalarHeap (S+i.val*V+j.val)=some (roleValue input kernel alpha i.val j))∧
 (∀a,a<S∨S+W*V≤a→u.scalarHeap a=s.scalarHeap a)∧Frame s u:=by
 have two:2*V≤W*V:=Nat.mul_le_mul_right V roles
 have sf:S+V+V≤B:=by omega
 obtain ⟨f,fill,pf,zeros,outF,frameF,_idx,one⟩:=UniformScalarZeroFillMachine.execution
  n B W V S x s pc hW hV hS extent (by omega) bound
 have fillPlaced:=boundedExecution_placed fill_code (by change 0+10≤B;omega) (by omega:10≤B) fill
 have fillRun:BoundedRuns program n x B s (5*(W*V)+6) {f with pc:=10}:=by
  simpa only[placed,Nat.zero_add] using fillPlaced
 let a:State:={f with pc:=10}
 have fa:Frame s a:=(Frame.fill frameF).withPC 10
 have original(j:ℕ)(h:Protected j):a.natReg j=s.natReg j:=fa.natReg j h
 have ac:(applyBlock copySetup a).natReg 147=V∧(applyBlock copySetup a).natReg 148=inputBase∧
  (applyBlock copySetup a).natReg 149=S:=by
  obtain ⟨l,i,d⟩:=copy_setup_regs a one
  exact ⟨l.trans ((original 6301 (by unfold Protected;omega)).trans hV),
   i.trans ((original 6303 (by unfold Protected;omega)).trans hI),
   d.trans ((original 6302 (by unfold Protected;omega)).trans hS)⟩
 have setupC:=block_runs copySetup program 10 n B x a copy_setup_code rfl fillRun.final_bound
  (by change 10+3≤B;omega) (by simp[readable,copySetup,ExactFourierCircuits.UniformNatBlockMachine.Op.readable,evalNat])
  (copy_setup_peak B a one fillRun.final_bound)
 let b:=applyBlock copySetup a
 have pb:b.pc=13:=by rw[block_pc];rfl
 have jc:=jump_run n B 13 14 x b copy_jump pb setupC.final_bound (by omega)
 let c:State:={b with pc:=14}
 let ce:State:={c with pc:=0}
 have fc:Frame s c:=(fa.trans (copy_setup_frame a)).withPC 14
 have srcI:C.Source V inputBase ce.scalarHeap:=by
  intro j hj;refine ⟨input ⟨j,hj⟩,?_⟩
  exact (outF (inputBase+j) (Or.inl (by omega))).trans (hInput ⟨j,hj⟩)
 obtain ⟨v,copy,copied,_source,outC,frameC,natC⟩:=UniformScalarCopyMachine.execution n x V inputBase S B ce
  srcI inputBefore (by omega) (by omega) rfl ac.1 ac.2.1 ac.2.2
  (changePC_bound _ c 0 jc.final_bound (by omega))
 have copyPlaced:=boundedExecution_placed copy_code (by change 14+10≤B;omega) (by omega:24≤B) copy
 have placeC:placed 14 ce=c:=rfl
 rw[placeC] at copyPlaced
 let d:State:={v with pc:=24}
 have fd:Frame s d:=(fc.trans ((Frame.copy frameC natC).beforePC 14)).withPC 24
 have dOne:d.natReg 6311=1:=(natC _ (by omega)).trans one
 have originalD(j:ℕ)(h:Protected j):d.natReg j=s.natReg j:=fd.natReg j h
 have kd:(applyBlock kernelSetup d).natReg 70=V∧(applyBlock kernelSetup d).natReg 71=kernelBase∧
  (applyBlock kernelSetup d).natReg 72=S+V∧(applyBlock kernelSetup d).natReg 73=alphaBase:=by
  obtain ⟨l,k,dst,a'⟩:=kernel_setup_regs d dOne
  refine ⟨l.trans ((originalD 6301 (by unfold Protected;omega)).trans hV),
   k.trans ((originalD 6304 (by unfold Protected;omega)).trans hK),?_,
   a'.trans ((originalD 6305 (by unfold Protected;omega)).trans hA)⟩
  rw[dst,originalD 6302 (by unfold Protected;omega),originalD 6301 (by unfold Protected;omega),hS,hV]
 have setupK:=block_runs kernelSetup program 24 n B x d kernel_setup_code rfl copyPlaced.final_bound
  (by change 24+4≤B;omega) (by simp[readable,kernelSetup,ExactFourierCircuits.UniformNatBlockMachine.Op.readable,evalNat])
  (kernel_setup_peak B d dOne copyPlaced.final_bound (by
   rw[originalD 6302 (by unfold Protected;omega),originalD 6301 (by unfold Protected;omega),hS,hV];omega))
 let e:=applyBlock kernelSetup d
 have pe:e.pc=28:=by rw[block_pc];rfl
 have jk:=jump_run n B 28 29 x e kernel_jump pe setupK.final_bound (by omega)
 let z:State:={e with pc:=29}
 let ze:State:={z with pc:=0}
 have fz:Frame s z:=(fd.trans (kernel_setup_frame d)).withPC 29
 have alphaZ:UniformGlobalNatPreparation.PermutationBank V alphaBase ze.natHeap alpha:=by
  rw[fz.natHeap];exact hAlpha
 have srcK:P.Source V kernelBase ze.scalarHeap:=by
  intro j;refine ⟨kernel j,?_⟩
  exact (outC (kernelBase+j.val) (Or.inl (by omega))).trans
   ((outF (kernelBase+j.val) (Or.inl (by have hj:=j.isLt;omega))).trans (hKernel j))
 obtain ⟨u,gather,gathered,_sourceK,outP,frameP,_pu,_index⟩:=UniformPermutationMachine.execution
  n x V kernelBase (S+V) alphaBase B alpha ze alphaZ srcK (Or.inl (by omega))
  (by omega) sf tableFit (by omega) rfl kd.1 kd.2.1 kd.2.2.1 kd.2.2.2
  (changePC_bound _ z 0 jk.final_bound (by omega))
 have gatherPlaced:=boundedExecution_placed kernel_code (by change 29+12≤B;omega) (by omega:41≤B) gather
 have placeK:placed 29 ze=z:=rfl
 rw[placeK] at gatherPlaced
 let final:State:={u with pc:=41}
 have halt:BoundedExecution program n x B final 1 final:=
  .halt gatherPlaced.final_bound (by simp[step,final,halt_at])
 have finalFrame:Frame s final:=(fz.trans ((Frame.kernel frameP).beforePC 29)).withPC 41
 refine ⟨final,?_,rfl,?_,?_,finalFrame⟩
 · convert (((((fillRun.trans setupC).trans jc).trans copyPlaced).trans setupK).trans jk).executes
    (gatherPlaced.executes halt) using 1
   simp only[copySetup,kernelSetup,List.length_cons,List.length_nil]
   omega
 · intro i j
   by_cases i0:i.val=0
   · simp only[roleValue,i0,Nat.zero_mul,Nat.add_zero]
     exact (outP (S+j.val) (Or.inl (by have hj:=j.isLt;omega))).trans
      ((copied j.val j.isLt).trans ((outF _ (Or.inl (by have hj:=j.isLt;omega))).trans (hInput j)))
   · by_cases i1:i.val=1
     · simp only[roleValue,i1,Nat.one_mul]
       exact (gathered j).trans ((outC _ (Or.inl (by have hj:=(alpha j).isLt;omega))).trans
        ((outF _ (Or.inl (by have hj:=(alpha j).isLt;omega))).trans (hKernel (alpha j))))
     · have larger : 2 * V ≤ i.val * V :=Nat.mul_le_mul_right V (by omega)
       have upper:(i.val+1)*V≤W*V:=Nat.mul_le_mul_right V (by have hi:=i.isLt;omega)
       have index:i.val*V+j.val<W*V:=by rw[Nat.add_mul] at upper;have hj:=j.isLt;omega
       simp only[roleValue,ite_eq_right i0,ite_eq_right i1]
       exact (outP _ (Or.inr (by omega))).trans ((outC _ (Or.inr (by omega))).trans
        (by
         have heap:ce.scalarHeap=f.scalarHeap:=copy_setup_heap a
         rw[heap]
         simpa only[Nat.add_assoc] using zeros _ index))
 · intro address ha
   exact (outP address (by rcases ha with lo|hi;exact Or.inl (by omega);exact Or.inr (by omega))).trans
    ((outC address (by rcases ha with lo|hi;exact Or.inl lo;exact Or.inr (by omega))).trans (outF address ha))

lemma role_one_prepared{V:ℕ}(input kernel:Fin V→Scalar)(alpha:Fin V≃Fin V)
 (prepared:∀j,(kernel j).dependent=false)(j:Fin V):
 (roleValue input kernel alpha 1 j).dependent=false:=by simpa[roleValue] using prepared (alpha j)
lemma all_prepared{V:ℕ}(input kernel:Fin V→Scalar)(alpha:Fin V≃Fin V)
 (a:∀j,(input j).dependent=false)(b:∀j,(kernel j).dependent=false)(i:ℕ)(j:Fin V):
 (roleValue input kernel alpha i j).dependent=false:=by
 by_cases h:i=0
 · simp[roleValue,h,a]
 · by_cases h':i=1
   · simp[roleValue,h',b]
   · simp[roleValue,h,h',Scalar.zero]
end
end ExactFourierCircuits.UniformRoleInputMachine
