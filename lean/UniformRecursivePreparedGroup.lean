import UniformRecursivePreparedValues
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveGroupExecution
open UniformMachine UniformBinaryTensorCoordinates
noncomputable section
def PreparedChildBody (n B k A F stack stackTop depth : ℕ) (cost:ℕ→ℕ) (x : Fin n→ℂ)
 (input : Fin S.W→Fin (2^k)→Scalar) (s : State) : Prop := ∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .returnSite ∧
 u.natReg 4150=stack ∧ u.natReg 4151=depth ∧
 (∀(i:Fin S.W) (j:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+j.val)).isSome=true) ∧
 (∀(i:Fin S.W) (j:Fin (2^k)),(u.scalarHeap (A+i.val*2^k+j.val)).map Scalar.value=
  some ((physicalMatrix k).mulVec (fun z=>(input i z).value) j)) ∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z) ∧
 (∀z,z<F→(z<A∨A+S.W*2^k≤z)→u.scalarHeap z=s.scalarHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ticks≤cost k ∧
 (UniformRecursivePreparedValues.Prepared2 input→∀(i:Fin S.W)(j:Fin (2^k)),
  (u.scalarHeap (A+i.val*2^k+j.val)).map Scalar.dependent=some false)

/-- Only the well-founded induction will discharge this proposition: every
smaller exponent executes this exact Program from its physically installed
headers. No arbitrary handler, matrix-action or returned-bank premise occurs
inside the child entry contract. -/
def PreparedSmallerBodies (parent n B reserve stack stackTop : ℕ) (cost:ℕ→ℕ) (x : Fin n→ℂ) : Prop :=
 ∀k,k<parent→∀(A F depth:ℕ) (input:Fin S.W→Fin (2^k)→Scalar) (s:State),
 s.pc=0→s.natReg 4120=k→s.natReg 4121=A→s.natReg 4122=2^k→s.natReg 4123=F→
 s.natReg 4150=stack→s.natReg 4151=depth→
 (∀(i:Fin S.W) (j:Fin (2^k)),s.scalarHeap (A+i.val*2^k+j.val)=some (input i j))→
 1≤depth→3≤A→A+S.W*2^k≤F→stack+34*(depth+k+1) ≤ stackTop→stackTop ≤ F→
 P.program.length≤B→F+reserve*(k+1)*2^k≤B→(2^k)^2≤B→
 UniformBinaryCStageMachine.Constants s→WordBound B s→PreparedChildBody n B k A F stack stackTop depth cost x input s

theorem one_group_prepared
 (k q m r n B reserve D V A i groups stack depth stackTop F:ℕ) (cost:ℕ→ℕ) (x:Fin n→ℂ)
 (s:State) (input:Fin S.W→Fin (2^q)→Scalar)
 (ih:PreparedSmallerBodies k n B reserve stack stackTop cost x) (smaller:q<k)
 (pc:s.pc=P.address .groupTest) (index:s.natReg 4125=i) (total:s.natReg 4126=groups)
 (columns:s.natReg 4060=q) (size:s.natReg 4015=2^q) (savedSize:s.natReg 4124=2^q)
 (base:s.natReg 4091=D) (fresh:s.natReg 4133=F) (sp:s.natReg 4150=stack) (dp:s.natReg 4151=depth)
 (bits:s.natReg 4120=k) (rest:s.natReg 4127=r) (original:s.natReg 4121=A)
 (volume:s.natReg 4122=V) (width:s.natReg 4061=m) (baseAlias:s.natReg 3300=A)
 (partition:groups*(S.W*2^q)=V) (hi:i<groups)
 (data:∀(j:Fin S.W) (t:Fin (2^q)),s.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)=some (input j t))
 (dataBase:3≤D) (dataEnd:D+V≤F) (stackRoom:stack+34*(depth+q+2)≤ stackTop) (stackEnd:stackTop≤F)
 (room:F+reserve*(q+1)*2^q≤B) (square:(2^q)^2≤B)
 (constants:UniformBinaryCStageMachine.Constants s) (bound:WordBound B s) (code:P.program.length≤B):∃u ticks,
 BoundedRuns P.program n x B s ticks u ∧ u.pc=P.address .groupTest ∧
 u.natReg 4125=i+1 ∧ u.natReg 4126=groups ∧ u.natReg 4150=stack ∧ u.natReg 4151=depth ∧ u.natReg 4153=1 ∧
 (∀j∈Stack.fields,u.natReg j=if j=4125 then s.natReg j+1 else s.natReg j) ∧
 u.natReg 4015=2^q ∧ u.natReg 4023=V ∧ u.natReg 4069=1 ∧ u.natReg 5300=k ∧ u.natReg 5301=r ∧
 (∀(j:Fin S.W) (t:Fin (2^q)),(u.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)).isSome=true) ∧
 (∀(j:Fin S.W) (t:Fin (2^q)),(u.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)).map Scalar.value=
  some ((physicalMatrix q).mulVec (fun z=>(input j z).value) t)) ∧
 (∀z,z<F→(z<D+i*(S.W*2^q)∨D+(i+1)*(S.W*2^q)≤z)→u.scalarHeap z=s.scalarHeap z) ∧
 (∀z,z<F→(z<stack+34*depth∨stackTop≤z)→u.natHeap z=s.natHeap z) ∧
 UniformBinaryCStageMachine.Constants u ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧ ticks≤cost q+169 ∧
 (UniformRecursivePreparedValues.Prepared2 input→∀(j:Fin S.W)(t:Fin (2^q)),
  (u.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)).map Scalar.dependent=some false):=by
 have fb:F≤B:=by omega
 have localStack:stack+34*(depth+1)≤B:=by nlinarith only [stackRoom,stackEnd,fb]
 obtain ⟨c,call,cp,ck,ca,ct,cf,csp,cdp,bank,nh,sh,sr,ou,ro⟩:=call_from_group
  n B q D V i groups stack depth F x s pc index total columns size base fresh sp dp partition hi
  bound code (dataEnd.trans fb) localStack
 have partEnd:(i+1)*(S.W*2^q)≤V:=
  (Nat.mul_le_mul_right (S.W*2^q) (Nat.succ_le_of_lt hi)).trans_eq partition
 have addEnd:D+i*(S.W*2^q)+S.W*2^q≤F:=by
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact Nat.add_le_add_left partEnd D |>.trans dataEnd
 have childData:∀(j:Fin S.W) (t:Fin (2^q)),c.scalarHeap (D+i*(S.W*2^q)+j.val*2^q+t.val)=some (input j t):=by
  intro j t;rw [sh];exact data j t
 have childConst:UniformBinaryCStageMachine.Constants c:=by
  simpa only [UniformBinaryCStageMachine.Constants,sh] using constants
 obtain ⟨v,ticks,child,vp,vsp,vdp,present,values,natFrame,scalarFrame,vc,vo,vr,timeBound,prepared⟩:=
  ih q smaller (D+i*(S.W*2^q)) F (depth+1) input c cp ck ca ct cf csp cdp childData (by omega)
   (by omega) addEnd (by convert stackRoom using 1; omega) stackEnd code room square childConst call.final_bound
 have savedBank:Stack.Bank Stack.fields (stack+34*depth) s.natReg v:=by
  intro j hj
  have jl:j<34:=by simpa only [UniformRecursiveReturnStackMachine.fields_length] using hj
  have below:stack+34*depth+j<F:=by nlinarith only [stackRoom,stackEnd,jl]
  rw [natFrame _ below (Or.inl (by omega))]
  exact bank j hj
 have next:i+1≤B:=by
  have gp:0<S.W*2^q:=Nat.mul_pos UniformRecursiveSelfCallMachine.W_positive (Nat.two_pow_pos _)
  have gb:groups≤V:=(Nat.le_mul_of_pos_right _ gp).trans_eq partition
  omega
 obtain ⟨u,ret,up,fields,usp,udp,globalOne,ut,uv,uone,uk,ur,uq,um,unh,ush,usr,uou,uro⟩:=
  UniformRecursiveParentReturn.resume_fields n B k q m r A V (2^q) stack depth s.natReg x v
   vp vsp vdp savedBank (fun j _=>bound.2.1 j) (by rwa [index]) savedSize volume bits rest original columns width baseAlias
   child.final_bound code localStack
 refine ⟨u,84+ticks+(76+P.size .restored),call.trans (child.trans ret),up,?_,?_,usp,udp,globalOne,fields,
  ut,uv,uone,uk,ur,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only [ite_true,index] using fields 4125 (by decide)
 · simpa only [show (4126:ℕ)≠4125 from by omega,ite_false,total] using fields 4126 (by decide)
 · intro j t;rw [ush];exact present j t
 · intro j t;rw [ush];exact values j t
 · intro z hz out
   rw [ush,scalarFrame z hz (by
    rcases out with out|out
    · exact Or.inl out
    · right;rw [Nat.add_assoc,←Nat.succ_mul];exact out),sh]
 · intro z hz out
   rw [unh,natFrame z hz (by rcases out with h|h;exact Or.inl (by omega);exact Or.inr h)]
   exact nh z (by rcases out with h|h;exact Or.inl h;right;nlinarith only [stackRoom,h])
 · simpa only [UniformBinaryCStageMachine.Constants,ush] using vc
 · exact uou.trans (vo.trans ou)
 · exact uro.trans (vr.trans ro)
 · change 84+ticks+(76+9)≤cost q+169
   omega

 · intro h j t;rw [ush];exact prepared h j t
end
end ExactFourierCircuits.UniformRecursiveGroupExecution
