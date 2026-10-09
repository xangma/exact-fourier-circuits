import UniformDirectLeafCacheLoopAdvance
import UniformDirectLeafCacheSemanticRetention
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafHighStep
open UniformMachine UniformTensorMonomialMachine UniformAssembly
open UniformDirectLeafCacheReader UniformDirectLeafCacheExecution UniformDirectLeafCacheLoopData
open UniformDirectLeafCacheLoopAdvance
open UniformTransposeDescriptorMachine (Record)
noncomputable section

/-- One real loop iteration includes its branch, the actual264 helper, the
measured clock branch and every persistent-pointer increment. -/
theorem execution {c:Config} {r A C N i n B:ℕ} {q:Record} (mu:ℂ) (x:Fin n→ℂ) (s:State)
 (args:Args c s) (controls:Controls r N i s) (go:i<N)
 (src:Source c r A C q s)
 (values:UniformZeroFreePairShearMachine.Sources mu q.coefficient
  (C+3*r+(q.coefficient-(A+3*r))) s)
 (constants:UniformHadamardPairMachine.Constants s)
 (range:UniformDirectLeafCacheSource.InRange r (A+3*r) q) (legal:UniformDirectLeafCacheSource.Legal q)
 (positive:2≤r) (layout:Layout c r B) (fit:Fits (nextConfig c r q) B)
 (readonly:c.record+4≤c.rows ∨ c.entry+7≤c.record)
 (descriptor:c.record+3≤B) (directory:c.originalDirectory+1≤B)
 (conjugateDirectory:c.conjugateDirectory≤B) (original:A+4*r≤B) (conjugate:C+4*r≤B)
 (coefficient:q.coefficient<c.pool) (conjugateCoefficient:C+3*r+(q.coefficient-(A+3*r))<c.pool)
 (code:303≤B) (pc:s.pc=23) (wb:WordBound B s):∃u,
 BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s
  (62*r+(if q.kind=0 then 117 else 212)) u ∧u.pc=23 ∧
 Args (nextConfig c r q) u ∧Controls r N (i+1) u ∧Nonempty (UniformDirectLeafCacheSemanticExecution.SemanticResult c r q mu positive u) ∧
 (∀j,(j<c.pool∨c.pool+9*r≤j)→u.scalarHeap j=s.scalarHeap j) ∧
 (∀j,j<c.permutation→(j<c.rows∨c.rows+3≤j)→u.natHeap j=s.natHeap j) ∧
 (∀j,c.entry+7≤j→u.natHeap j=s.natHeap j) ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders:=by
 let start:=setPC s 0
 have sw:=changePC_bound B s 0 wb (by omega)
 have sa:Args c start:=UniformDirectLeafCacheSetup.Args.setPC args 0
 have sc:Controls r N i start:=controls.setPC 0
 have ss:Source c r A C q start:=⟨src.record,src.original,src.radix,src.conjugate⟩
 obtain ⟨b,body,bp,result,bsh,bnh,bhigh,bout,broot⟩:=UniformDirectLeafCacheSemanticExecution.execution
  mu x start sa ss values constants range legal positive layout descriptor directory conjugateDirectory
  original conjugate coefficient conjugateCoefficient (by omega) rfl sw
 have placed:=UniformBoundedAssembly.boundedExecution_placed UniformDirectLeafCacheLoopProgram.descriptor_code
  (by rw[UniformDirectLeafCacheProgram.program_length];omega) (by omega) body
 have branch:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 1 (setPC s 24):=
  .next wb (by simp [UniformMachine.step,pc,UniformDirectLeafCacheLoopProgram.branch_at,
   controls.index,controls.count,go,setPC]) (.refl (changePC_bound B s 24 wb (by omega)))
 have placedStart:UniformAssembly.placed 24 start=setPC s 24:=rfl
 rw[placedStart] at placed
 let z:=setPC b 288
 have za:Args c z:=UniformDirectLeafCacheSetup.Args.setPC (args_body sa body) 288
 have zc:Controls r N i z:=(controls_body sc body).setPC 288
 have record:z.natHeap c.record=some q.kind:=by
  have old:s.natHeap c.record=some q.kind:=by
   simpa [UniformTransposeDescriptorMachine.Record.words] using src.record (0:Fin 4)
  rcases readonly with low|high
  · exact (bnh c.record (by have:=layout.rows;omega) (Or.inl (by omega))).trans old
  · exact (bhigh c.record high).trans old
 obtain ⟨t,clock,tp,ta,tc,tnh,tsh,_tsr,tout,troot,_tnat⟩:=UniformDirectLeafCacheLoopAdvance.clock x z za zc record
  (by simpa only[nextConfig] using fit.time) rfl code placed.final_bound
 have countBound:i+1≤B:=by have:=wb.2.1 6628;rw[controls.count] at this;omega
 have adv:=advance_bounded x t ta tc fit countBound tp code clock.final_bound
 let u:=advanced t
 have up:u.pc=23:=rfl
 have ua:Args (nextConfig c r q) u:=advance_args ta tc
 have uc:Controls r N (i+1) u:=advance_controls tc
 have heap:u.natHeap=b.natHeap:=tnh
 have scalars:u.scalarHeap=b.scalarHeap:=tsh
 have out:u.outputs=b.outputs:=tout
 have roots:u.rootOrders=b.rootOrders:=troot
 rcases result with ⟨res⟩
 have res':UniformDirectLeafCacheSemanticExecution.SemanticResult c r q mu positive u:=UniformDirectLeafCacheSemanticRetention.result res layout range.1 range.2.1
  (fun j _ _=>congrFun scalars j) (fun j _ _=>congrFun heap j)
 refine ⟨u,?_,up,ua,uc,⟨res'⟩,?_,?_,?_,out.trans bout,roots.trans broot⟩
 · convert ((branch.trans placed).trans clock).trans adv using 1
   by_cases kind:q.kind=0 <;>simp only[kind,ite_true,ite_false] <;>omega
 · intro j hj;exact (congrFun scalars j).trans (bsh j hj)
 · intro j hj outside;exact (congrFun heap j).trans (bnh j hj outside)
 · intro j hj;exact (congrFun heap j).trans (bhigh j hj)
end
end ExactFourierCircuits.UniformDirectLeafHighStep
