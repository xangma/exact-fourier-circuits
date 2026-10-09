import UniformDirectLeafHighStep
import UniformDirectLeafHighGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafHighExecution
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheLoopData UniformDirectLeafHighGeometry
open UniformDirectLeafCacheLoopGeometry (slot slot_next Inputs)
open UniformTransposeDescriptorMachine (Record)
noncomputable section

structure Done (c:Config) (r A C:ℕ) (qs:List Record) (i:ℕ) (positive:2≤r) (s u:State):Prop where
 pc:u.pc=302
 args:Args (slot c r qs qs.length) u
 controls:Controls r qs.length qs.length u
 inputs:Inputs c r A C qs u
 events:∀(j:ℕ)(hj:j<qs.length),i≤j → Nonempty
  (UniformDirectLeafCacheSemanticExecution.SemanticResult (slot c r qs j) r qs[j]
   (UniformDirectLeafCacheSource.mu r (A+3*r) qs[j]) positive u)
 scalarOutside:∀j,(j<(slot c r qs i).pool∨(slot c r qs qs.length).pool≤j) → u.scalarHeap j=s.scalarHeap j
 natPrefix:∀j,j<(slot c r qs i).permutation → (j<c.rows∨c.rows+3≤j) → u.natHeap j=s.natHeap j
 natHigh:∀j,(slot c r qs qs.length).permutation≤j → u.natHeap j=s.natHeap j
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

/-- The complete fixed loop calls the actual264 producer at every real
ordinal and retains every earlier produced pool/partition/ABI slot. -/
theorem loop (remaining:ℕ) {c:Config} {r A C B:ℕ} {qs:List Record}
 (layout:UniformDirectLeafHighGeometry.Layout c r A C B qs)
 (valid:∀q∈qs,UniformDirectLeafCacheSource.InRange r (A+3*r) q ∧UniformDirectLeafCacheSource.Legal q)
 (positive:2≤r) : ∀{i n:ℕ}(x:Fin n → ℂ)(s:State),i+remaining=qs.length → 
 Args (slot c r qs i) s → Controls r qs.length i s → Inputs c r A C qs s → s.pc=23 → WordBound B s → 
 ∃u ticks,BoundedExecution UniformDirectLeafCacheLoopProgram.program n x B s ticks u ∧
 ticks≤(62*r+212)*remaining+2 ∧Done c r A C qs i positive s u:=by
 induction remaining with
 | zero=>
  intro i n x s finish args controls input pc wb
  have eq:i=qs.length:=by omega
  subst i
  let u:=setPC s 302
  have ub:=changePC_bound B s 302 wb (by have:=layout.code;omega)
  have endrun:BoundedExecution UniformDirectLeafCacheLoopProgram.program n x B s 2 u:=
   .next wb (by simp[UniformMachine.step,pc,UniformDirectLeafCacheLoopProgram.branch_at,
    controls.index,controls.count,u,setPC]) (.halt ub (by simp[UniformMachine.step,u,setPC,
     UniformDirectLeafCacheLoopProgram.halt_at]))
  refine ⟨u,2,endrun,by simp,?_,⟩
  exact ⟨rfl,UniformDirectLeafCacheSetup.Args.setPC args 302,controls.setPC 302,
   ⟨input.records,input.original,input.radix,input.conjugate,input.values,input.constants⟩,
   fun j hj impossible=>by omega,fun _ _=>rfl,fun _ _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
 | succ remaining ih=>
  intro i n x s finish args controls input pc wb
  have hi:i<qs.length:=by omega
  let q:=qs[i]
  have member:q∈qs:=List.getElem_mem hi
  have legal:=valid q member
  have lb:=slot_layout layout i hi
  have nb:=slot_bounds layout (i+1) (by omega)
  have nextEq:=slot_next c r qs i hi
  have ro:=slot_readonly layout i hi
  have sb:=slot_bounds layout i (by omega)
  have originalBound:A+4*r≤B:=by have:=layout.original;have:=layout.scalarEnd;omega
  have conjugateBound:C+4*r≤B:=by have:=layout.conjugate;have:=layout.scalarEnd;omega
  have src:Source (slot c r qs i) r A C q s:=
   ⟨input.records i hi,input.original,input.radix,input.conjugate⟩
  obtain ⟨a,one,ap,aa,ac,event,ash,anh,ahigh,aout,aroot⟩:=UniformDirectLeafHighStep.execution
   (UniformDirectLeafCacheSource.mu r (A+3*r) q) x s args controls hi src (input.values i hi)
   input.constants legal.1 legal.2 positive lb (by rw[nextEq];exact nb) (Or.inr ro)
   (by have:=layout.descriptors;change c.record+4*i+3≤B;omega)
   (by have:=layout.directory;have:=layout.rows;have:=layout.natEnd;change c.originalDirectory+1≤B;omega)
   (by have:=layout.conjugateDirectory;have:=layout.rows;have:=layout.natEnd;change c.conjugateDirectory≤B;omega)
   originalBound conjugateBound
   (by have:=layout.original;rcases legal.1 with ⟨_,_,_,_⟩;simp only[slot];omega)
   (by have:=layout.conjugate;rcases legal.1 with ⟨_,_,_,_⟩;simp only[slot];omega)
   layout.code pc wb
  have ain:Inputs c r A C qs a:=UniformDirectLeafHighGeometry.transport input layout (fun q h=>(valid q h).1)
   (fun j hj=>anh j (by have:=layout.rows;simp only[slot];omega) (Or.inl hj))
   (fun j hj=>ahigh j (by
    have endHigh:=layout.descriptorHigh
    have e:=layout.entry
    have mul:=Nat.mul_le_mul_left (3*r+11) (show i+1≤qs.length by omega)
    simp only[slot]
    nlinarith))
   (fun j hj=>ash j (Or.inl (by simp only[slot];omega)))
  rw[nextEq] at aa
  obtain ⟨u,ticks,rest,cost,done⟩:=ih x a (by omega) aa ac ain ap one.final_bound
  have run:=one.executes rest
  refine ⟨u,_,run,?_,?_,⟩
  · by_cases kind:q.kind=0
    · simp only[kind,ite_true]
      nlinarith
    · simp only[kind,ite_false]
      nlinarith
  · refine ⟨done.pc,done.args,done.controls,done.inputs,?_,?_,?_,?_,done.outputs.trans aout,done.roots.trans aroot⟩
    · intro j hj lower
      by_cases eq:j=i
      · subst j
        rcases event with ⟨event⟩
        have persist:=UniformDirectLeafCacheSemanticRetention.result event lb legal.1.1 legal.1.2.1
         (fun z _ upper=>done.scalarOutside z (Or.inl (by
          simp only[slot] at upper⊢;nlinarith)))
         (fun z lower upper=>done.natPrefix z (by
          have e:=layout.entry;simp only[slot] at lower upper⊢;nlinarith)
          (Or.inr (by have:=layout.rows;simp only[slot] at lower;omega)))
        exact ⟨persist⟩
      · exact done.events j hj (by omega)
    · intro j outside
      have monotone:(slot c r qs i).pool≤(slot c r qs (i+1)).pool:=by simp only[slot];nlinarith
      have endmonotone:(slot c r qs (i+1)).pool≤(slot c r qs qs.length).pool:=by
       simp only[slot];nlinarith
      have dframe:=done.scalarOutside j (by rcases outside with h|h;exact Or.inl (h.trans_le monotone);exact Or.inr h)
      exact dframe.trans (ash j (by rcases outside with h|h;exact Or.inl h;exact Or.inr (by
       simp only[slot] at h⊢;nlinarith)))
    · intro j below outside
      have mon:(slot c r qs i).permutation≤(slot c r qs (i+1)).permutation:=by simp only[slot];nlinarith
      exact (done.natPrefix j (below.trans_le mon) outside).trans (anh j below outside)
    · intro j high
      have currentEnd:(slot c r qs i).entry+7≤(slot c r qs qs.length).permutation:=by
       have:=layout.entry;simp only[slot];nlinarith
      exact (done.natHigh j high).trans (ahigh j (currentEnd.trans high))
end
end ExactFourierCircuits.UniformDirectLeafHighExecution
