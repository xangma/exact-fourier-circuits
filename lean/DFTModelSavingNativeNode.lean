import DFTModelSavingNativeControl
import UniformRecursiveNodeJoin
import UniformRecursiveTypedBody

set_option autoImplicit false

/-! Paper E (adc7f), §2.6, Theorem 2.6, pp. 11–12. The actual large
branch computes its quotient/remainder and prints both fixed tables. These
tables are outputs of the source run, not assumptions about a ready cache. -/
namespace ExactFourierCircuits.DFTModelSavingNativeNode
open UniformMachine BinaryFrames UniformFixedNetwork UniformFixedNetworkScheduleMachine
open UniformRecursiveTypedBody UniformRecursiveNodePreparation
open UniformRecursiveResidualEdge (Parent)
open DFTModelAdmissibilityControl DFTModelSavingNativeControl
namespace P
export UniformRecursiveSavingProgram (program address seedLength unitLength unitRecord
  threshold seedPrinterLength unitPrinterLength size)
end P
namespace G
export UniformRecursiveSavingExecution (GeometryChanged geometry_execution)
end G
namespace N
export UniformRecursiveNodeJoin (Changed execution)
end N
noncomputable section

attribute [local irreducible] P.program P.seedLength P.unitLength P.unitRecord
  P.threshold P.seedPrinterLength P.unitPrinterLength P.size

def ticks : ℕ := 9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)

lemma quotient_remainder (q rest : ℕ) (rp : rest < m) :
    (q*m+rest)/m=q ∧ (q*m+rest)%m=rest := by
  have pos : 0 < m := by norm_num [m,ExplicitSeedBudget.m]
  constructor
  · rw [Nat.mul_comm q m,Nat.mul_add_div pos,Nat.div_eq_of_lt rp,Nat.add_zero]
  · have zero : q*m%m=0 := Nat.mod_eq_zero_of_dvd ⟨q,Nat.mul_comm _ _⟩
    rw [Nat.add_mod,zero,Nat.mod_eq_of_lt rp,Nat.zero_add,Nat.mod_eq_of_lt rp]

structure Frame (F J : ℕ) (s u : State) : Prop where
  natHeap : ∀z,z<F∨J≤z→u.natHeap z=s.natHeap z
  scalarHeap : u.scalarHeap=s.scalarHeap
  scalarReg : u.scalarReg=s.scalarReg
  outputs : u.outputs=s.outputs
  roots : u.rootOrders=s.rootOrders
  natReg : ∀i,¬G.GeometryChanged i→¬N.Changed i→u.natReg i=s.natReg i

theorem single (n B F M l A q rest stack depth stackTop reserve : ℕ)
    (x : Fin n→ℂ) (s : State) (eqM : M=P.seedLength) (eql : l=P.unitLength)
    (geometry : Geometry B A (workBase F M l) q rest stack depth stackTop reserve)
    (large : P.threshold≤q*m+rest) (thresholdBound : P.threshold≤B)
    (pc : s.pc=P.address .readyEntry) (bits : s.natReg 4120=q*m+rest)
    (base : s.natReg 4121=A) (volume : s.natReg 4122=2^(q*m+rest))
    (frontier : s.natReg 4123=F) (nativeBase : s.natReg 3300=A)
    (nativeBits : s.natReg 5300=q*m+rest) (sp : s.natReg 4150=stack)
    (dp : s.natReg 4151=depth) (one : s.natReg 4153=1)
    (literals : literalCap (serialize baseSchedule)≤B) (bound : WordBound B s) :
    ∃t,BoundedRuns P.program n x B s
      (9+(P.seedPrinterLength+12+P.unitPrinterLength+P.size .nodeReady)) t ∧ t.pc=P.address .loop ∧
      Parent (q*m+rest) q A (workBase F M l) F rest stack depth t ∧
      t.natHeap (workBase F M l-2)=some (unitBase F M) ∧
      t.natHeap (workBase F M l-1)=some (unitBase F M) ∧
      PrintedRecords F (scheduleRecords q) t ∧
      Printed (unitBase F M) (P.unitRecord.withColumns q).data t ∧
      (∀j:Fin ExplicitSeedBudget.m,UniformRepeatedMaskMachine.Source
        (unitBase F M+8+j.val*ExplicitSeedBudget.m) (unit j) t) ∧
      Frame F (workBase F M l) s t := by
  obtain ⟨qr,rr⟩:=quotient_remainder q rest geometry.remainder
  obtain ⟨a,boot,ap,aq,aw,ar,an,ac,af,av,gf⟩:=G.geometry_execution
    n B (q*m+rest) (2^(q*m+rest)) F x s pc bits volume frontier one large
    bound geometry.code thresholdBound
  rw [qr] at aq ac
  rw [rr] at ar an
  have keepG (j : ℕ) (hj : ¬G.GeometryChanged j) : a.natReg j=s.natReg j := gf.natReg j hj
  have aVolume : a.natReg 4122=2^(q*m+rest) :=
    (keepG _ (by unfold G.GeometryChanged;omega)).trans volume
  have cm : m≤B := by have h:=geometry.width;omega
  obtain ⟨t,print,tp,ptr,work,table,buffer,unitPtr,storedMeta,main,unitBank,sources,nf⟩:=
    N.execution n B F M l q (2^(q*m+rest)) x a eqM eql ap af ac aq aVolume
      boot.final_bound geometry.code cm literals (by have h:=geometry.poolEnd;omega)
  have keepN (j : ℕ) (hj : ¬N.Changed j) : t.natReg j=a.natReg j := nf.natReg j hj
  have keep (j : ℕ) (g : ¬G.GeometryChanged j) (h : ¬N.Changed j) :
      t.natReg j=s.natReg j := (keepN j h).trans (keepG j g)
  have widthEq : (q*m+rest-rest)/q=m := by
    rw [Nat.add_sub_cancel_right]
    exact Nat.mul_div_right m (by have p:=geometry.positive;omega)
  have parent : Parent (q*m+rest) q A (workBase F M l) F rest stack depth t := by
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
  refine ⟨t,boot.trans print,tp,parent,unitPtr,storedMeta,main,unitBank,sources,?_⟩
  exact ⟨fun z hz=>(nf.natHeap z hz).trans (congrFun gf.natHeap z),
    nf.scalarHeap.trans gf.scalarHeap,nf.scalarReg.trans gf.scalarReg,
    nf.outputs.trans gf.outputs,nf.roots.trans gf.roots,keep⟩

end
end ExactFourierCircuits.DFTModelSavingNativeNode
