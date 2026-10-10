import DFTModelCacheDAGDepthBounds

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheDAGDepth
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

/-- Runtime input count, gate count, and the original flat five-field tape. -/
abbrev TopologyInput := p w (p w (Ty.a w))
abbrev TopologyCursor := p TopologyInput w

def topologyCount : Prog false TopologyInput w := .atom .fst
def topologyGates : Prog false TopologyInput w := .comp (.atom .snd) (.atom .fst)
def topologyTape : Prog false TopologyInput (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def topologyField (b : ℕ) : Prog false TopologyCursor w :=
  .comp (.fork (.comp (.atom .fst) topologyTape)
    (nat .add (nat .mul (.atom .snd) (.atom (.lit 5))) (.atom (.lit b)))) (.atom .look)
def topologyRow : Prog false TopologyCursor Row3 :=
  .fork (topologyField 0) (.fork (topologyField 1) (topologyField 2))
def decodeTopology : Prog false TopologyInput (Ty.a Row3) := .tab topologyGates topologyRow
/-- Only the first three of the genuine five fields affect DAG depth. -/
def fromTopology : Prog false TopologyInput (Ty.a w) :=
  .comp (.fork topologyCount decodeTopology) program

def decodedTopology (G : ℕ) (t : Tape ℕ) : Tape Row3.T :=
  Tape.tab G (fun j => (t.look (5*j) 0,(t.look (5*j+1) 0,t.look (5*j+2) 0)))

theorem topologyField_run (N G i b : ℕ) (t : Tape ℕ) :
    run (topologyField b) ((N,(G,t)),i)=
      ⟨t.look (5*i+b) 0,17,max (max 5 b) (5*i+b),True⟩ := by
  simp [topologyField,topologyTape,nat,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay,Nat.mul_comm]
  congr 1

theorem topologyRow_run (N G i : ℕ) (t : Tape ℕ) :
    run topologyRow ((N,(G,t)),i)=
      ⟨(t.look (5*i) 0,(t.look (5*i+1) 0,t.look (5*i+2) 0)),53,
        max 5 (5*i+2),True⟩ := by
  rw [topologyRow]
  change ((run (topologyField 0) ((N,(G,t)),i)).pass (fun x=>
    ((run (topologyField 1) ((N,(G,t)),i)).pass (fun y=>
      (run (topologyField 2) ((N,(G,t)),i)).pass (fun z=>Bill.one (y,z)))).pass
        (fun yz=>Bill.one (x,yz))))=_
  rw [topologyField_run,topologyField_run,topologyField_run]
  simp only [Bill.pass,Bill.one,true_and,max_zero,Nat.add_zero]
  congr 1
  omega

theorem topologyRow_run_code (N G i : ℕ) (t : Tape ℕ) :
    Code.run topologyRow () ((N,(G,t)),i)=
      ⟨(t.look (5*i) 0,(t.look (5*i+1) 0,t.look (5*i+2) 0)),53,
        max 5 (5*i+2),True⟩ := topologyRow_run N G i t

theorem decodeTopology_value (N G : ℕ) (t : Tape ℕ) :
    (run decodeTopology (N,(G,t))).val=decodedTopology G t := by
  simp only [decodeTopology,run,Code.run,topologyGates,Atom.run,Bill.one,
    Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_value]
  unfold decodedTopology
  congr 1
  funext i
  exact congrArg Bill.val (topologyRow_run N G i t)

theorem decodeTopology_valid (N G : ℕ) (t : Tape ℕ) :
    (run decodeTopology (N,(G,t))).valid := by
  simp only [decodeTopology,run,Code.run,topologyGates,Atom.run,Bill.one,
    Bill.pass,Bill.pay,true_and]
  rw [ModelEquivalenceInterpreter.tab_valid]
  intro i hi
  rw [topologyRow_run_code]
  trivial

theorem decodeTopology_work (N G : ℕ) (t : Tape ℕ) :
    (run decodeTopology (N,(G,t))).work=57*G+6 := by
  simp only [decodeTopology,run,Code.run,topologyGates,Atom.run,Bill.one,
    Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_work]
  change 3+(2+4*G+∑i∈Finset.range G,(run topologyRow ((N,(G,t)),i)).work)+1=_
  have hs:(∑i∈Finset.range G,(run topologyRow ((N,(G,t)),i)).work)=G*53 := by
    calc
      _=∑_i∈Finset.range G,53:=Finset.sum_congr rfl (fun i _=>congrArg Bill.work (topologyRow_run N G i t))
      _=G*53:=by simp
  rw [hs]
  omega

theorem decodeTopology_peak (N G : ℕ) (t : Tape ℕ) :
    (run decodeTopology (N,(G,t))).peak≤5*G+5 := by
  simp only [decodeTopology,run,Code.run,topologyGates,Atom.run,Bill.one,
    Bill.pass,Bill.pay]
  rw [ModelEquivalenceInterpreter.tab_peak]
  simp only [max_self,max_zero,zero_max]
  change max G ((Finset.range G).sup
    (fun i=>(run topologyRow ((N,(G,t)),i)).peak))≤_
  apply max_le (by omega)
  apply Finset.sup_le
  intro i hi
  have hi:=Finset.mem_range.mp hi
  have hp:=congrArg Bill.peak (topologyRow_run N G i t)
  change (run topologyRow ((N,(G,t)),i)).peak=max 5 (5*i+2) at hp
  rw [hp]
  omega

attribute [local irreducible] program decodeTopology

theorem fromTopology_run (N G : ℕ) (t : Tape ℕ) :
    run fromTopology (N,(G,t))=
      ⟨(run program (N,decodedTopology G t)).val,
        (run program (N,decodedTopology G t)).work+57*G+9,
        max (run decodeTopology (N,(G,t))).peak
          (run program (N,decodedTopology G t)).peak,
        (run program (N,decodedTopology G t)).valid⟩ := by
  rw [fromTopology]
  change (((run topologyCount (N,(G,t))).pass (fun x=>
    (run decodeTopology (N,(G,t))).pass (fun ys=>Bill.one (x,ys)))).pass
      (fun input=>run program input)).pay 1 0=_
  have hc : run topologyCount (N,(G,t))=⟨N,1,0,True⟩:=rfl
  have hd : run decodeTopology (N,(G,t))=
      ⟨decodedTopology G t,57*G+6,(run decodeTopology (N,(G,t))).peak,True⟩ := by
    have hv:=decodeTopology_value N G t
    have hw:=decodeTopology_work N G t
    have hb:=decodeTopology_valid N G t
    generalize hz:run decodeTopology (N,(G,t))=z at hv hw hb ⊢
    cases z
    simp_all
  rw [hc,hd]
  simp only [Bill.pass,Bill.one,Bill.pay,true_and,max_zero,zero_max]
  congr 1
  omega

/-- A concrete input-tape condition; all three operand fields must actually
exist in the original five-field topology tape. -/
def TopologyFields (qs : List UniformDAGDepthMachine.Row) (t : Tape ℕ) : Prop :=
  5*qs.length≤t.len ∧ ∀j:Fin qs.length,
    t.look (5*j.val) 0=qs[j].opcode ∧
    t.look (5*j.val+1) 0=qs[j].left ∧ t.look (5*j.val+2) 0=qs[j].right

theorem decodedTopology_eq (qs : List UniformDAGDepthMachine.Row) (t : Tape ℕ)
    (h : TopologyFields qs t) : decodedTopology qs.length t=rowsTape qs := by
  unfold decodedTopology rowsTape Tape.tab
  congr 1
  funext j
  have hv:=h.2 j
  exact Prod.ext hv.1 (Prod.ext hv.2.1 hv.2.2)

theorem fromTopology_specification (N : ℕ) (qs : List UniformDAGDepthMachine.Row)
    (t : Tape ℕ) (h : TopologyFields qs t) (ht : UniformDAGDepthMachine.Topological N qs) :
    (run fromTopology (N,(qs.length,t))).val=
      Tape.tab (N+1+qs.length) (UniformDAGDepthMachine.evaluate (N+1) qs (fun _=>0)) ∧
    (run fromTopology (N,(qs.length,t))).valid ∧
    (run fromTopology (N,(qs.length,t))).work≤workBudget N qs.length+57*qs.length+9 ∧
    (run fromTopology (N,(qs.length,t))).peak≤N+5*qs.length+5 := by
  have ds:=decodedTopology_eq qs t h
  have hp:=program_peak N (rowsTape qs)
  have hd:=decodeTopology_peak N qs.length t
  rw [fromTopology_run,ds]
  refine ⟨program_value N qs ht,program_valid N _,?_,?_⟩
  · have hw:=program_work N (rowsTape qs)
    exact Nat.add_le_add_right (Nat.add_le_add_right hw _) _
  · change max (run decodeTopology (N,(qs.length,t))).peak
      (run program (N,rowsTape qs)).peak ≤ _
    change (run program (N,rowsTape qs)).peak≤N+qs.length+2 at hp
    omega

end
end ExactFourierCircuits.DFTModelCacheDAGDepth
