import UniformRecursiveSelfCallMachine
import UniformResidualGeneralGatherPreparation
import UniformFixedNetworkOpcodeMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveResidualRecordPreparation
open UniformMachine UniformAssembly BinaryFrames
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
open UniformFixedNetworkScheduleMachine (Record Printed macroRecord)
open UniformFixedNetwork (edgeVectors edgeVectors_orthonormal)
open FramedScheduleWords (Label NestedEdge)
noncomputable section

/-- The direction index is a loop counter. All descriptor and workspace
headers are computed from actual loaded fields and the ordinary native bank. -/
def setup : List Op := [
 .binary .mul 4060 2852 2859,.binary .mul 4061 2853 2859,
 .binary .mul 4171 4134 2853,.binary .add 4135 2850 2860,
 .binary .add 4062 4135 4171,
 .binary .mul 4172 2854 4122,.binary .add 4090 3300 4172,
 .binary .mul 4130 2865 2859,.binary .mul 4131 2856 2859,
 .binary .mul 4132 2857 2859,
 .binary .mul 4063 4123 2859,.binary .add 4066 4063 4122,
 .binary .add 4067 4066 4122,.binary .add 4068 4067 4122,
 .binary .add 4091 4068 4122,.binary .add 4133 4091 4122,
 .binary .mul 4100 4127 2859]
def program : Program := UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++setup.map Op.code++[.halt]
lemma setup_length : setup.length=17:=rfl
lemma program_length : program.length=70:=by
 simp only [program,List.length_append,List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length,
  setup_length,List.length_cons,List.length_nil]
lemma reader_code : CodeAt UniformFixedNetworkOpcodeMachine.headProgram program 0 52:=by
 have h:=embed_code [] UniformFixedNetworkOpcodeMachine.headProgram (setup.map Op.code++[.halt]) 52
 simpa only [embed,List.length_nil,List.nil_append,program,List.append_assoc] using h
lemma setup_code : BlockAt setup program 52:=by
 intro i hi
 rw [show program=UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++(setup.map Op.code++[.halt]) from by simp only [program,List.append_assoc],
  List.getElem?_append_right (by simp only [List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length];omega)]
 simp only [List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length,Nat.add_sub_cancel_left]
 rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),List.getElem?_map]
 simp only [List.getElem?_eq_getElem hi,Option.map_some]
lemma halt_at : program[69]?=some .halt:=by
 have len:(UniformFixedNetworkOpcodeMachine.headProgram.map (relocate 0 52)++setup.map Op.code).length=69:=by
  simp only [List.length_append,List.length_map,UniformFixedNetworkOpcodeMachine.headProgram_length,setup_length]
 rw [program,List.getElem?_append_right (by omega),len];rfl

lemma role_bound (A R V d B:ℕ) (hd:d<R) (endptr:A+R*V≤B) : d*V≤B ∧ A+d*V≤B:=by
 have h:=Nat.mul_le_mul_right V (Nat.le_of_lt hd)
 constructor <;> omega
lemma direction_bound (T dimension m j F:ℕ) (hj:j<dimension) (extent:T+8+dimension*m≤F) :
 j*m≤F ∧ T+8+j*m≤F:=by
 have h:=Nat.mul_le_mul_right m (Nat.le_of_lt hj)
 constructor <;> omega

/-- Actual opcode reader plus charged physical role-offset, descriptor and
pool setup. No decoded Fields, ready direction bank or workspace headers are
entry assumptions. -/
theorem execution (n B T R A V F q m r dim d j:ℕ) (x:Fin n→ℂ) (s:State)
 (record:Record) (op:record.opcode=0) (columns:record.columns=q) (width:record.width=m)
 (dimension:record.dimension=dim) (dest:record.dest=d)
 (pc:s.pc=0) (cursor:s.natReg 2850=T) (printed:Printed T record.data s)
 (good:UniformFixedNetworkOpcodeMachine.WellFormed record)
 (index:s.natReg 4134=j) (hj:j<dim) (hd:d<R)
 (base:s.natReg 3300=A) (volume:s.natReg 4122=V)
 (frontier:s.natReg 4123=F) (rest:s.natReg 4127=r)
 (bound:WordBound B s) (code:70≤B) (recordEnd:T+record.data.length≤F)
 (widthBound:m+1≤B) (arrayEnd:A+R*V≤B) (poolEnd:F+5*V≤B) :
 ∃u,BoundedExecution program n x B s (UniformFixedNetworkOpcodeMachine.headCost record+18) u ∧ u.pc=69 ∧
 UniformResidualPermutationPreparation.Inputs q m (T+8+j*m) F (F+V) (F+2*V) (F+3*V) u ∧
 u.natReg 4090=A+d*V ∧ u.natReg 4091=F+4*V ∧ u.natReg 4100=r ∧
 u.natReg 4133=F+5*V ∧ u.natReg 4130=T+record.data.length ∧
 u.natReg 4131=record.inverse ∧ u.natReg 4132=dim ∧
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders := by
 have recordBound:T+record.data.length≤B:=recordEnd.trans (by omega)
 obtain ⟨read,rr,fields,body,nextptr,frame⟩:=UniformFixedNetworkOpcodeMachine.head_execution T B n record x s cursor pc bound printed good recordBound
  (by simpa [width] using widthBound) (by omega)
 have reader:=UniformBoundedAssembly.boundedExecution_placed reader_code (by change 52≤B;omega) (by omega) rr
 have zero:placed 0 s=s:=by simp [placed]
 rw [zero] at reader
 let ready:State:={read with pc:=52}
 have kept (i : ℕ) (hi : i < 2850 ∨ 2876 < i) :read.natReg i=s.natReg i:=frame.natReg i hi
 have idx:read.natReg 4134=j:=(kept _ (by omega)).trans index
 have a:read.natReg 3300=A:=(kept _ (by omega)).trans base
 have v:read.natReg 4122=V:=(kept _ (by omega)).trans volume
 have f:read.natReg 4123=F:=(kept _ (by omega)).trans frontier
 have rem:read.natReg 4127=r:=(kept _ (by omega)).trans rest
 have c:read.natReg 2852=q:=fields.columns.trans columns
 have w:read.natReg 2853=m:=fields.width.trans width
 have dst:read.natReg 2854=d:=fields.dest.trans dest
 have dm:read.natReg 2857=dim:=fields.dimension.trans dimension
 have recLen:record.data.length=8+dim*m:=by rw [Record.data_length,good.2];simp [UniformFixedNetworkOpcodeMachine.bodyLength,op,dimension,width]
 have db:=direction_bound T dim m j F hj (by simpa only [recLen,Nat.add_assoc] using recordEnd)
 have rb:=role_bound A R V d B hd arrayEnd
 have qb:q≤B:=by have h:=bound.2.2.1 (T+1) q (by simpa [Record.header,columns] using printed.header (1:Fin 8));exact h.2
 have mb:m≤B:=by omega
 have ib:record.inverse≤B:=by have h:=bound.2.2.1 (T+5) record.inverse (by simpa [Record.header] using printed.header (5:Fin 8));exact h.2
 have dimB:dim≤B:=by have h:=bound.2.2.1 (T+6) dim (by simpa [Record.header,dimension] using printed.header (6:Fin 8));exact h.2
 have rB:r≤B:=by have h:=bound.2.1 4127;rwa [rest] at h
 have safe:readable setup ready ∧ peak setup ready≤B:=by
  simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,ready,
   c,w,idx,fields.cursor,fields.eight,fields.one,dst,a,v,f,nextptr,fields.inverse,dm,rem,
   max_le_iff,qb,mb,ib,dimB,rB,rb.1,rb.2]
  omega
 have sr:=block_runs setup program 52 n B x ready setup_code rfl reader.final_bound (by rw [setup_length];omega) safe.1 safe.2
 let u:=applyBlock setup ready
 have up:u.pc=69:=by simp [u,setup,applyBlock,Op.apply,writeNat,next,ready]
 have stop:BoundedExecution program n x B u 1 u:=.halt sr.final_bound (by simp [step,up,halt_at])
 refine ⟨u,?_,up,?_,?_,?_,?_,?_,?_,?_,?_,frame.natHeap,frame.scalarHeap,frame.scalarReg,frame.outputs,frame.roots⟩
 · convert (reader.trans sr).executes stop using 1;simp only [setup_length]
 · constructor
   · constructor <;> simp [u,setup,applyBlock,Op.apply,evalNat,writeNat,next,ready,c,w,idx,fields.cursor,fields.eight,fields.one,f]
   all_goals simp [u,setup,applyBlock,Op.apply,evalNat,writeNat,next,ready,v,f,fields.one] <;> ring
 all_goals simp [u,setup,applyBlock,Op.apply,evalNat,writeNat,next,ready,idx,fields.cursor,fields.eight,
   fields.one,dst,a,v,f,nextptr,fields.inverse,dm,rem] <;> ring

/-- A genuine printed residual basis supplies the exact nonzero source vector;
this is not a pre-produced physical child direction. -/
theorem edge_direction {nRoles R m:ℕ} (q T:ℕ) (emb:Fin nRoles↪Fin R)
 {old new:Label m} (role:Fin nRoles) (edge:NestedEdge old new) (j:Fin edge.dimension) (s:State)
 (printed:Printed T (macroRecord q emb (.edge old new role edge)).data s) :
 UniformRepeatedMaskMachine.Source (T+8+j.val*m) (edgeVectors edge j) s ∧ edgeVectors edge j≠0:=by
 constructor
 · intro i
   have h:=(UniformFixedNetworkScheduleMachine.residual_descriptor q emb role edge T s printed).2.2.2 j i
   simpa [finProdFinEquiv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] using h
 · have h:=edgeVectors_orthonormal edge j j
   intro eq
   simp [eq, BinaryFrames.dot] at h
end
end ExactFourierCircuits.UniformRecursiveResidualRecordPreparation
