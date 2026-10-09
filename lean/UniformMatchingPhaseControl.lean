import UniformSameProgramSectorEntry
import UniformGlobalMatchingScaleMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingPhaseControl
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalMatchingScaleMachine (Phase phases)
noncomputable section

def lane:Phase→ℕ|.diagonal j=>j.val|.kernel=>0
def destination (d k:ℕ):Phase→ℕ|.diagonal _=>d|.kernel=>k
def oneDispatch (i:ℕ) (p:Phase) (d k:ℕ):Program:=
 [.natLiteral 5944 (i+1),.branchLT 5942 5944 (5+4*i) (7+4*i),
  .natLiteral 4582 (lane p),.jump (destination d k p)]
lemma oneDispatch_length (i:ℕ) (p:Phase) (d k:ℕ):(oneDispatch i p d k).length=4:=rfl
def dispatchFrom:List Phase→ℕ→ℕ→ℕ→Program
 | [], _, _, _ => []
 | p :: ps, i, d, k => oneDispatch i p d k++dispatchFrom ps (i+1) d k
def boot:List Op:=[.literal 5940 0,.literal 5941 1,.literal 5942 0]
def diagonalPC:ℕ:=116
def kernelPC (d:Program):ℕ:=116+d.length
def advancePC (d k:Program):ℕ:=116+d.length+k.length
/-- The actual28 phase list drives one fixed diagonal site and one fixed
kernel site. Its six kernel entries reuse the same physical C program.
This is control/static assembly; kernel restoration and data-bank headers
must still be joined before it is a complete global transform. -/
def controlFor (d k:Program):Program:=boot.map Op.code++
 dispatchFrom phases 0 diagonalPC (kernelPC d)++[.jump (advancePC d k+2)]++
 d.map (relocate diagonalPC (advancePC d k))++
 k.map (relocate (kernelPC d) (advancePC d k))++
 [.natBinary .add 5942 5942 5941,.jump 3,.halt]

lemma dispatch_length (ps:List Phase) (i d k:ℕ):(dispatchFrom ps i d k).length=4*ps.length:=by
 induction ps generalizing i with
 |nil=>rfl
 |cons p ps ih=>simp only[dispatchFrom,List.length_append,oneDispatch,List.length_cons,List.length_nil,ih];omega
lemma boot_length:boot.length=3:=rfl
lemma control_length (d k:Program):(controlFor d k).length=d.length+k.length+119:=by
 simp only[controlFor,List.length_append,List.length_map,boot_length,dispatch_length,
  UniformGlobalMatchingScaleMachine.phases_length,List.length_cons,List.length_nil];omega

lemma dispatch_get (ps:List Phase) (i d k j q:ℕ) (hj:j<ps.length) (hq:q<4):
 (dispatchFrom ps i d k)[4*j+q]?=(oneDispatch (i+j) (ps[j]'hj) d k)[q]?:=by
 induction ps generalizing i j with
 |nil=>simp at hj
 |cons p ps ih=>
  cases j with
  |zero=>
   simp only[Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero,Nat.add_zero,dispatchFrom]
   rw[List.getElem?_append_left (by simpa only[oneDispatch,List.length_cons,List.length_nil] using hq)]
  |succ j=>
   have bound:j<ps.length:=by simpa using hj
   rw[dispatchFrom,List.getElem?_append_right (by simp only[oneDispatch,List.length_cons,List.length_nil];omega)]
   simp only[oneDispatch_length,List.getElem_cons_succ]
   rw[show 4*(j+1)+q-4=4*j+q by omega]
   simpa only[Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) j bound

lemma dispatch_code (d k:Program) (i q:ℕ) (hi:i<28) (hq:q<4):
 (controlFor d k)[3+4*i+q]?=
 (oneDispatch i (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) diagonalPC (kernelPC d))[q]?:=by
 unfold controlFor
 have left:3+4*i+q<3+(dispatchFrom phases 0 diagonalPC (kernelPC d)).length:=by
  rw[dispatch_length,UniformGlobalMatchingScaleMachine.phases_length];omega
 repeat rw[List.getElem?_append_left (by simp only[List.length_append,List.length_map,boot_length,
  dispatch_length,UniformGlobalMatchingScaleMachine.phases_length,List.length_cons,List.length_nil];omega)]
 rw[List.getElem?_append_right (by rw[List.length_map,boot_length];omega)]
 simp only[List.length_map,boot_length]
 rw[show 3+4*i+q-3=4*i+q by omega]
 simpa only[Nat.zero_add] using dispatch_get phases 0 diagonalPC (kernelPC d) i q
  (by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi) hq

lemma diagonal_code (d k:Program):CodeAt d (controlFor d k) diagonalPC (advancePC d k):=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++dispatchFrom phases 0 diagonalPC (kernelPC d)++[.jump (advancePC d k+2)])
  (k.map (relocate (kernelPC d) (advancePC d k))++[.natBinary .add 5942 5942 5941,.jump 3,.halt])
  d diagonalPC (advancePC d k)
  (by simp only[List.length_append,List.length_map,boot_length,dispatch_length,
   UniformGlobalMatchingScaleMachine.phases_length,List.length_cons,List.length_nil];rfl)
 simpa only[controlFor,List.append_assoc] using h
lemma kernel_code (d k:Program):CodeAt k (controlFor d k) (kernelPC d) (advancePC d k):=by
 have h:=UniformRankCrossPreparationMachine.segment_code
  (boot.map Op.code++dispatchFrom phases 0 diagonalPC (kernelPC d)++[.jump (advancePC d k+2)]++
   d.map (relocate diagonalPC (advancePC d k)))
  [.natBinary .add 5942 5942 5941,.jump 3,.halt] k (kernelPC d) (advancePC d k)
  (by simp only[List.length_append,List.length_map,boot_length,dispatch_length,
   UniformGlobalMatchingScaleMachine.phases_length,List.length_cons,List.length_nil,kernelPC])
 simpa only[controlFor,List.append_assoc] using h

lemma lane_bound (p:Phase):lane p≤8:=by cases p with|diagonal j=>exact Nat.le_pred_of_lt j.isLt|kernel=>decide
lemma destination_bound (d k:Program) (p:Phase):destination diagonalPC (kernelPC d) p≤(controlFor d k).length:=by
 cases p <;>simp only[destination,diagonalPC,kernelPC,control_length] <;>omega

lemma selected_dispatch {n B i:ℕ} (d k:Program) (x:Fin n→ℂ) (s:State)
 (hi:i<28) (pc:s.pc=3+4*i) (index:s.natReg 5942=i)
 (code:(controlFor d k).length≤B) (wb:WordBound B s):
 ∃u,BoundedRuns (controlFor d k) n x B s 4 u ∧
 u.pc=destination diagonalPC (kernelPC d) (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 4582=lane (phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)) ∧
 u.natReg 5942=i ∧u.natReg 5941=s.natReg 5941 ∧u.natHeap=s.natHeap ∧
 u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let p:=phases[i]'(by rw[UniformGlobalMatchingScaleMachine.phases_length];exact hi)
 let a:=writeNat s 5944 (i+1)
 let b:=setPC a (5+4*i)
 let c:=writeNat b 4582 (lane p)
 let u:=setPC c (destination diagonalPC (kernelPC d) p)
 have c0:(controlFor d k)[3+4*i]?=some (.natLiteral 5944 (i+1)):=by
  simpa only[Nat.add_zero,oneDispatch,List.getElem?_cons_zero] using dispatch_code d k i 0 hi (by omega)
 have c1:(controlFor d k)[4+4*i]?=some (.branchLT 5942 5944 (5+4*i) (7+4*i)):=by
  have h:=dispatch_code d k i 1 hi (by omega)
  change (controlFor d k)[3+4*i+1]?=some (.branchLT 5942 5944 (5+4*i) (7+4*i)) at h
  simpa only[show 3+4*i+1=4+4*i by omega] using h
 have c2:(controlFor d k)[5+4*i]?=some (.natLiteral 4582 (lane p)):=by
  have h:=dispatch_code d k i 2 hi (by omega)
  change (controlFor d k)[3+4*i+2]?=some (.natLiteral 4582 (lane p)) at h
  simpa only[show 3+4*i+2=5+4*i by omega] using h
 have c3:(controlFor d k)[6+4*i]?=some (.jump (destination diagonalPC (kernelPC d) p)):=by
  have h:=dispatch_code d k i 3 hi (by omega)
  change (controlFor d k)[3+4*i+3]?=some (.jump (destination diagonalPC (kernelPC d) p)) at h
  simpa only[show 3+4*i+3=6+4*i by omega] using h
 have big:119≤B:=by rw[control_length] at code;omega
 have ab:WordBound B a:=writeNat_bound B s 5944 (i+1) wb (by omega) (by omega)
 have bb:WordBound B b:=changePC_bound B a (5+4*i) ab (by omega)
 have cb:WordBound B c:=writeNat_bound B b 4582 (lane p) bb (by change 5+4*i+1≤B;omega)
  (by have:=lane_bound p;omega)
 have ub:WordBound B u:=changePC_bound _ _ _ cb ((destination_bound d k p).trans code)
 have ap:a.pc=4+4*i:=by simp only[a,writeNat,next,pc];omega
 have bp:b.pc=5+4*i:=rfl
 have cp:c.pc=6+4*i:=by change b.pc+1=6+4*i;rw[bp];omega
 refine ⟨u,?_,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
 · refine .next wb ?_ (.next ab ?_ (.next bb ?_ (.next cb ?_ (.refl ub))))
   · simp only[step,pc,c0];rfl
   · rw[step,ap,c1]
     simp[a,writeNat,index,show i < i+1 by omega,b,setPC]
   · simp only[step,bp,c2];rfl
   · simp only[step,cp,c3];rfl
 · simp[u,c,writeNat,setPC,p]
 · simp[u,c,b,a,writeNat,setPC,index]
 · simp[u,c,b,a,writeNat,setPC]

/- Missing data/execution joins: the preceding diagonal's produced scalar
bank must become the next phase source by real charged headers/copies;
the fixed kernel must execute all sectors through unconditional actual C,
then actual scatter and inverse packing. The physical cache time/axis loop
and full charged finite28-phase composition are also still open. -/
end
end ExactFourierCircuits.UniformMatchingPhaseControl
