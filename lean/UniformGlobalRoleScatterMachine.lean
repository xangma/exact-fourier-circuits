import UniformScalarScatterMachine
import UniformGlobalSameChildEntry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalRoleScatterMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformGlobalNatPreparation (PermutationBank)
noncomputable section

def boot (W:ℕ):List Op:=[.literal 5970 W,.literal 5971 0,.literal 5972 1,.literal 5973 0]
def setup:List Op:=[.mul 5974 5973 5960,.add 1506 5960 5971,
 .add 1507 5961 5974,.add 1508 5962 5974,.add 1509 5963 5971]
def programFor (W:ℕ):Program:=(boot W).map Op.code++[.branchLT 5973 5970 5 24]++setup.map Op.code++
 UniformScalarScatterMachine.program.map (relocate 10 22)++
 [.natBinary .add 5973 5973 5972,.jump 4,.halt]
lemma boot_length (W:ℕ):(boot W).length=4:=rfl
lemma setup_length:setup.length=5:=rfl
lemma program_length (W:ℕ):(programFor W).length=25:=rfl
lemma boot_code (W:ℕ):BlockAt (boot W) (programFor W) 0:=by intro i hi;change i < 4 at hi;interval_cases i  <;>rfl
lemma setup_code (W:ℕ):BlockAt setup (programFor W) 5:=by intro i hi;change i < 5 at hi;interval_cases i  <;>rfl
lemma scatter_code (W:ℕ):CodeAt UniformScalarScatterMachine.program (programFor W) 10 22:=by
 exact UniformRankCrossPreparationMachine.segment_code
  ((boot W).map Op.code++[.branchLT 5973 5970 5 24]++setup.map Op.code)
  [.natBinary .add 5973 5973 5972,.jump 4,.halt] _ 10 22 rfl
lemma branch_at (W:ℕ):(programFor W)[4]?=some (.branchLT 5973 5970 5 24):=rfl
lemma advance_at (W:ℕ):(programFor W)[22]?=some (.natBinary .add 5973 5973 5972):=rfl
lemma jump_at (W:ℕ):(programFor W)[23]?=some (.jump 4):=rfl
lemma halt_at (W:ℕ):(programFor W)[24]?=some .halt:=rfl

structure Geometry (W:ℕ) where
 B:ℕ
 volume:ℕ
 source:ℕ
 destination:ℕ
 permutation:ℕ
 code:25 ≤ B
 roles:W ≤ B
 volumeFit:volume ≤ B
 sourceFit:source+W*volume ≤ B
 destinationFit:destination+W*volume ≤ B
 permutationFit:permutation+volume ≤ B
 disjoint:source+W*volume ≤ destination  ∨ destination+W*volume ≤ source
structure Header {W:ℕ} (g:Geometry W) (s:State):Prop where
 volume:s.natReg 5960=g.volume
 source:s.natReg 5961=g.source
 destination:s.natReg 5962=g.destination
 permutation:s.natReg 5963=g.permutation
structure Cursor {W:ℕ} (g:Geometry W) (i:ℕ) (s:State):Prop extends Header g s where
 roles:s.natReg 5970=W
 zero:s.natReg 5971=0
 one:s.natReg 5972=1
 index:s.natReg 5973=i
def Protected (q:ℕ):Prop:=(q < 1506  ∨ 1517 ≤ q)  ∧ (q < 5970  ∨ 5975 ≤ q)
def Frame (s u:State):Prop:=u.natHeap=s.natHeap  ∧ u.outputs=s.outputs  ∧ u.rootOrders=s.rootOrders  ∧ 
 (∀q,Protected q → u.natReg q=s.natReg q)  ∧ (∀q,q≠90 → u.scalarReg q=s.scalarReg q)
lemma Frame.refl (s:State):Frame s s:=⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {s t u:State} (a:Frame s t) (b:Frame t u):Frame s u:=
 ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,
  fun q h=>(b.2.2.2.1 q h).trans (a.2.2.2.1 q h),fun q h=>(b.2.2.2.2 q h).trans (a.2.2.2.2 q h)⟩
lemma boot_frame (W:ℕ) (s:State):Frame s (applyBlock (boot W) s):=by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro q h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next,Protected] at *
lemma setup_frame (s:State):Frame s (applyBlock setup s):=by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro q h;simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next,Protected] at *
lemma child_frame {s u:State} (h:UniformScalarScatterMachine.Frame s u):Frame s u:=
 ⟨h.1,h.2.1,h.2.2.1,fun q p=>h.2.2.2.2 q (by rcases p.1 with p|p  <;>omega),h.2.2.2.1⟩
lemma setup_cursor {W i:ℕ} {g:Geometry W} {s:State} (c:Cursor g i s):Cursor g i (applyBlock setup s):=by
 constructor
 · constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,c.volume,c.source,c.destination,c.permutation]
 all_goals simp[setup,applyBlock,Op.apply,writeNat,next,c.roles,c.zero,c.one,c.index]
lemma child_cursor {W i:ℕ} {g:Geometry W} {s u:State} (c:Cursor g i s)
 (h:UniformScalarScatterMachine.Frame s u):Cursor g i u:=by
 constructor
 · constructor
   · exact (h.2.2.2.2 5960 (by omega)).trans c.volume
   · exact (h.2.2.2.2 5961 (by omega)).trans c.source
   · exact (h.2.2.2.2 5962 (by omega)).trans c.destination
   · exact (h.2.2.2.2 5963 (by omega)).trans c.permutation
 · exact (h.2.2.2.2 5970 (by omega)).trans c.roles
 · exact (h.2.2.2.2 5971 (by omega)).trans c.zero
 · exact (h.2.2.2.2 5972 (by omega)).trans c.one
 · exact (h.2.2.2.2 5973 (by omega)).trans c.index

def Source {W:ℕ} (g:Geometry W) (v:ℕ → Fin g.volume → Scalar) (s:State):Prop:=
 ∀r,r < W → ∀j:Fin g.volume,s.scalarHeap (g.source+r*g.volume+j.val)=some (v r j)
def Filled {W:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ → Fin g.volume → Scalar) (done:ℕ) (s:State):Prop:=
 ∀r,r < done → ∀j:Fin g.volume,s.scalarHeap (g.destination+r*g.volume+(p j).val)=some (v r j)
def Outside {W:ℕ} (g:Geometry W) (s u:State):Prop:=
 ∀q,(q < g.destination  ∨ g.destination+W*g.volume ≤ q) → u.scalarHeap q=s.scalarHeap q

lemma setup_safe {W i:ℕ} {g:Geometry W} {s:State} (c:Cursor g i s) (hi:i < W):
 readable setup s  ∧ peak setup s ≤ g.B:=by
 simp[setup,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,c.index,c.volume,c.source,c.destination,
  c.permutation,c.zero]
 have a:=g.volumeFit;have b:=g.sourceFit;have d:=g.destinationFit;have p:=g.permutationFit
 have off:=Nat.mul_le_mul_right g.volume (Nat.le_of_lt hi)
 omega

/-- One real role-offset calculation and one real12-instruction scatter.
The table is shared; no host coordinate permutation is performed. -/
lemma iteration {W n:ℕ} (g:Geometry W) (p:Equiv.Perm (Fin g.volume)) (v:ℕ → Fin g.volume → Scalar)
 (x:Fin n → ℂ) (s:State) (i:Fin W) (c:Cursor g i.val s)
 (table:PermutationBank g.volume g.permutation s.natHeap p) (source:Source g v s)
 (pc:s.pc=4) (wb:WordBound g.B s):
 ∃u,BoundedRuns (programFor W) n x g.B s (9*g.volume+12) u  ∧ u.pc=4  ∧ 
 Cursor g (i.val+1) u  ∧ 
 (∀j:Fin g.volume,u.scalarHeap (g.destination+i.val*g.volume+(p j).val)=some (v i.val j))  ∧ 
 Frame s u  ∧ 
 (∀q,(q < g.destination+i.val*g.volume  ∨ g.destination+(i.val+1)*g.volume ≤ q) → u.scalarHeap q=s.scalarHeap q):=by
 let e:=setPC s 5
 have eb:=changePC_bound g.B s 5 wb (by have:=g.code;omega)
 have branch:BoundedRuns (programFor W) n x g.B s 1 e:=.next wb
  (by simp[step,pc,branch_at,c.index,c.roles,i.isLt,e,setPC]) (.refl eb)
 have safe:=setup_safe c i.isLt
 have first:=block_runs setup (programFor W) 5 n g.B x e (setup_code W) rfl eb
  (by rw[setup_length];have:=g.code;omega) safe.1 safe.2
 let b:=applyBlock setup e
 let ready:=setPC b 0
 have rb:=changePC_bound g.B b 0 first.final_bound (by omega)
 have header:(ready.natReg 1506=g.volume)  ∧ (ready.natReg 1507=g.source+i.val*g.volume)  ∧ 
  (ready.natReg 1508=g.destination+i.val*g.volume)  ∧ (ready.natReg 1509=g.permutation):=by
  simp[ready,b,e,setPC,setup,applyBlock,Op.apply,writeNat,next,c.index,c.volume,c.source,c.destination,c.permutation,c.zero]
 have input:UniformScalarScatterMachine.Source g.volume (g.source+i.val*g.volume) ready.scalarHeap:=by
  intro j;exact ⟨v i.val j,source i.val i.isLt j⟩
 have disjoint:UniformScalarScatterMachine.Disjoint (g.source+i.val*g.volume) (g.destination+i.val*g.volume) g.volume:=by
  rcases g.disjoint with h|h
  · left;have:=i.isLt;nlinarith
  · right;have:=i.isLt;nlinarith
 obtain ⟨t,run,values,_old,out,frame,_tp,_count⟩:=UniformScalarScatterMachine.execution n x g.volume
  (g.source+i.val*g.volume) (g.destination+i.val*g.volume) g.permutation g.B p ready table input disjoint
  (by have:=g.sourceFit;have:=i.isLt;nlinarith) (by have:=g.destinationFit;have:=i.isLt;nlinarith)
  g.permutationFit (by have:=g.code;omega) rfl header.1 header.2.1 header.2.2.1 header.2.2.2 rb
 have moved:=UniformBoundedAssembly.boundedExecution_placed (scatter_code W)
  (by rw[UniformScalarScatterMachine.program_length];have:=g.code;omega) (by have:=g.code;omega) run
 have bp:b.pc=10:=by rw[applyBlock_pc,setup_length];rfl
 rw[show placed 10 ready=b by change setPC b 10=b;rw[←bp];cases b;rfl] at moved
 have entryCursor:Cursor g i.val e:=⟨⟨c.volume,c.source,c.destination,c.permutation⟩,c.roles,c.zero,c.one,c.index⟩
 have afterSetup:=setup_cursor entryCursor
 have beforeChild:Cursor g i.val ready:=⟨⟨afterSetup.volume,afterSetup.source,afterSetup.destination,afterSetup.permutation⟩,
  afterSetup.roles,afterSetup.zero,afterSetup.one,afterSetup.index⟩
 have current:Cursor g i.val t:=child_cursor beforeChild frame
 let a:=writeNat (setPC t 22) 5973 (i.val+1)
 have ab:=writeNat_bound g.B (setPC t 22) 5973 (i.val+1) moved.final_bound
  (by have:=g.code;change 22+1 ≤ g.B;omega) ((Nat.succ_le_of_lt i.isLt).trans g.roles)
 have advance:BoundedRuns (programFor W) n x g.B (setPC t 22) 1 a:=.next moved.final_bound
  (by simp[step,setPC,advance_at,evalNat,current.index,current.one,a]) (.refl ab)
 let u:=setPC a 4
 have last:BoundedRuns (programFor W) n x g.B a 1 u:=.next ab
  (by simp[step,a,setPC,writeNat,next,jump_at,u]) (.refl (changePC_bound _ _ 4 ab (by have:=g.code;omega)))
 have tickFrame:Frame t u:=by
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
  intro q h;simp (disch:=omega) [u,a,setPC,writeNat,next,Protected] at *
 refine ⟨u,?_,rfl,?_,?_,(setup_frame e).trans ((child_frame frame).trans tickFrame),?_⟩
 · convert branch.trans (first.trans (moved.trans (advance.trans last))) using 1;simp only[setup_length];omega
 · constructor
   · exact ⟨current.volume,current.source,current.destination,current.permutation⟩
   · exact current.roles
   · exact current.zero
   · exact current.one
   · simp[u,a,writeNat,setPC]
 · intro j;exact (values j).trans (source i.val i.isLt j)
 · intro q h
   apply out q
   rcases h with h|h
   · exact Or.inl h
   · exact Or.inr (by nlinarith)
end
end ExactFourierCircuits.UniformGlobalRoleScatterMachine
