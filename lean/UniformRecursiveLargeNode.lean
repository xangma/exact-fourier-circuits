import UniformRecursivePrintedBody
import UniformRecursiveNodeJoin

/-!
Paper correspondence: An explicit power saving for the exact discrete Fourier
transform, OpenAI math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§2.6, Theorem 2.6, PDF pp. 11–12 (net:tensor-bound).
The actual large-branch prologue prints both fixed tables and then executes the complete record body. Only strictly smaller executions of the identical program remain as an induction motive; root/child induction discharges it.
-/
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveLargeNode
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics
open UniformRecursiveTypedBody UniformRecursiveCoreSchedule UniformRecursiveNodePreparation
open UniformFixedNetworkShearChildMachine (Present)
open UniformNativeHandlerSemantics (arrayValues)
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord threshold seedPrinterLength unitPrinterLength size)
end P
namespace G
export UniformRecursiveSavingExecution (GeometryChanged geometry_execution)
end G
namespace N
export UniformRecursiveNodeJoin (Changed execution)
end N
noncomputable section

lemma quotient_remainder (q rest:ℕ)(rp:rest < m):
 (q*m+rest)/m=q ∧(q*m+rest)%m=rest:=by
 have pos:0 < m:=by norm_num [m,ExplicitSeedBudget.m]
 constructor
 · rw [Nat.mul_comm q m,Nat.mul_add_div pos,Nat.div_eq_of_lt rp,Nat.add_zero]
 · have zero:q*m%m=0:=Nat.mod_eq_zero_of_dvd ⟨q,Nat.mul_comm _ _⟩
   rw [Nat.add_mod,zero,Nat.mod_eq_of_lt rp,Nat.zero_add,Nat.mod_eq_of_lt rp]

/-- Real large-branch prologue and both physical printers feed the complete
proved record body. Only smaller executions of the identical Program remain
as an induction hypothesis; no produced tape or action is assumed. -/
/- Paper: §2.6, Theorem 2.6, PDF pp. 11–12 (net:tensor-bound). The actual large-branch prologue prints both fixed tables and then executes the complete record body. Only strictly smaller executions of the identical program remain as an induction motive; root/child induction discharges it. -/
theorem execution (n B F M l A q rest stack depth stackTop reserve H:ℕ)(cost:ℕ→ℕ)
 (x:Fin n→ℂ)(s:State)(f:Fin W→Fin (2^(q*m+rest))→Scalar)
 (eqM:M=P.seedLength)(eql:l=P.unitLength)
 (childIH:UniformRecursiveGroupExecution.SmallerBodies (q*m+rest) n B reserve stack stackTop cost x)
 (geometry:Geometry B A (workBase F M l) q rest stack depth stackTop reserve)
 (large:P.threshold ≤ q*m+rest)(thresholdBound:P.threshold ≤ B)
 (pc:s.pc=P.address .readyEntry)(bits:s.natReg 4120=q*m+rest)(base:s.natReg 4121=A)
 (volume:s.natReg 4122=2^(q*m+rest))(frontier:s.natReg 4123=F)
 (nativeBase:s.natReg 3300=A)(nativeBits:s.natReg 5300=q*m+rest)
 (sp:s.natReg 4150=stack)(dp:s.natReg 4151=depth)(one:s.natReg 4153=1)
 (data:Present A W (2^(q*m+rest)) f s)
 (stackEnd:stackTop ≤ F)(floor:H ≤ F)
 (literals:literalCap (serialize baseSchedule) ≤ B)
 (constants:UniformBinaryCStageMachine.Constants s)(bound:WordBound B s):
 ∃u time,∃g:Fin W→Fin (2^(q*m+rest))→Scalar,
 BoundedRuns P.program n x B s time u∧u.pc=(if depth=0 then P.address .halt else P.address .returnSite)∧
 Present A W (2^(q*m+rest)) g u∧
 (∀i,(fun z=> (g i z).value)=(UniformBinaryTensorCoordinates.physicalMatrix (q*m+rest)).mulVec (fun z=> (f i z).value))∧
 u.natReg 4150=stack∧u.natReg 4151=depth∧
 (∀z,z < H→(z < stack+34*depth∨stackTop ≤ z)→u.natHeap z=s.natHeap z)∧
 (∀z,z < H→(z < A∨A+W*2^(q*m+rest) ≤ z)→u.scalarHeap z=s.scalarHeap z)∧
 UniformBinaryCStageMachine.Constants u∧u.rootOrders=s.rootOrders∧u.outputs=s.outputs∧
 time ≤ 9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)+UniformRecursivePrintedBody.bodyTicks q rest cost:=by
 obtain ⟨qr,rr⟩:=quotient_remainder q rest geometry.remainder
 obtain ⟨a,boot,ap,aq,aw,ar,an,ac,af,av,gf⟩:=G.geometry_execution n B (q*m+rest) (2^(q*m+rest)) F x s
  pc bits volume frontier one large bound geometry.code thresholdBound
 rw [qr] at aq ac
 rw [rr] at ar an
 have keepG(j:ℕ)(hj:¬G.GeometryChanged j):a.natReg j=s.natReg j:=gf.natReg j hj
 have aVolume:a.natReg 4122=2^(q*m+rest):=(keepG _ (by unfold G.GeometryChanged;omega)).trans volume
 have cm:m ≤ B:=by have h:=geometry.width;omega
 obtain ⟨t,print,tp,ptr,work,table,buffer,unitPtr,storedMeta,main,unitBank,sources,nf⟩:=N.execution
  n B F M l q (2^(q*m+rest)) x a eqM eql ap af ac aq aVolume boot.final_bound geometry.code cm literals
  (by have h:=geometry.poolEnd;omega)
 have keepN(j:ℕ)(hj:¬N.Changed j):t.natReg j=a.natReg j:=nf.natReg j hj
 have keep(j:ℕ)(g:¬G.GeometryChanged j)(h:¬N.Changed j):t.natReg j=s.natReg j:=
  (keepN j h).trans (keepG j g)
 have widthEq:(q*m+rest-rest)/q=m:=by rw [Nat.add_sub_cancel_right];exact Nat.mul_div_right m (by have p:=geometry.positive;omega)
 have parent:UniformRecursiveResidualEdge.Parent (q*m+rest) q A (workBase F M l) F rest stack depth t:=by
  refine ⟨ptr,?_,?_,?_,?_,work,?_,?_,?_,?_,?_,?_,table,?_,?_⟩
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans nativeBase
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans base
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans bits
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans volume
  · exact (keepN _ (by unfold N.Changed;omega)).trans ar
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans sp
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans dp
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans one
  · exact (keep _ (by unfold G.GeometryChanged;omega) (by unfold N.Changed;omega)).trans nativeBits
  · exact (keepN _ (by unfold N.Changed;omega)).trans an
  · exact (keepN _ (by unfold N.Changed;omega)).trans aq
  · exact ((keepN _ (by unfold N.Changed;omega)).trans aw).trans widthEq.symm
 have present:Present A W (2^(q*m+rest)) f t:=by intro i z;rw [nf.scalarHeap,gf.scalarHeap];exact data i z
 have ct:UniformBinaryCStageMachine.Constants t:=by
  unfold UniformBinaryCStageMachine.Constants at constants ⊢
  rw [nf.scalarHeap,gf.scalarHeap];exact constants
 have unitCoord:unitBase F M=F+M:=rfl
 have workCoord:workBase F M l=unitBase F M+l+6:=rfl
 have mainEnd:F+P.seedLength ≤ workBase F M l-6:=by rw [←eqM,workCoord,unitCoord];omega
 have unitEnd:unitBase F M+P.unitLength ≤ workBase F M l-6:=by rw [←eql,workCoord];omega
 have metadata:t.natHeap (workBase F M l-1)=some (F+P.seedLength):=by
  rw [←eqM,←unitCoord];exact storedMeta
 obtain ⟨u,last,g,run,up,out,values,usp,udp,nh,sh,cu,roots,outputs,lastBound⟩:=UniformRecursivePrintedBody.execution
  n B F (unitBase F M) A (workBase F M l) H q rest stack depth stackTop reserve cost x t f childIH geometry
  tp parent metadata main present unitPtr unitBank mainEnd unitEnd stackEnd (by rw [unitCoord];omega)
  (by rw [unitCoord];omega) (by rw [workCoord,unitCoord];omega) ct print.final_bound
 refine ⟨u,9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)+last,g,
  (boot.trans print).trans run,up,out,values,usp,udp,?_,?_,cu,
  roots.trans (nf.roots.trans gf.roots),outputs.trans (nf.outputs.trans gf.outputs),Nat.add_le_add_left lastBound _⟩
 · intro z hz away;exact (nh z hz away).trans ((nf.natHeap z (Or.inl (by omega))).trans (congrFun gf.natHeap z))
 · intro z hz away
   exact (sh z (by rw [workCoord,unitCoord];omega) away).trans ((congrFun nf.scalarHeap z).trans (congrFun gf.scalarHeap z))
end
end ExactFourierCircuits.UniformRecursiveLargeNode
