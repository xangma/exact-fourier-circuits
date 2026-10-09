import UniformLocalRectangleReplayPreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalDisabledHeightMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformCrossHeightPreparationMachine

/-- A second physical height bank is generated for the disabled-input sweep.
The original tape and bucket order are reused; printed true rows are retained. -/
def disabled (v : Parameters) (D F U J : ℕ) : Parameters :=
 {v with D:=D,F:=F,U:=U,J:=J,enabled:=false}

def setup : List Op := [.literal 4236 0,.add 1056 4232 4236,
 .add 1057 4233 4236,.add 1058 4234 4236,.add 1059 4235 4236,.literal 1061 0]
lemma setup_length : setup.length=6 := rfl
def program : Program := setup.map Op.code++
 UniformCrossHeightPreparationMachine.program.map (relocate 6 192)++[.halt]
lemma program_length : program.length=193 := by
 simp only [program,List.length_append,List.length_map,setup_length,
  UniformCrossHeightPreparationMachine.program_length,List.length_singleton]
attribute [local irreducible] UniformCrossHeightPreparationMachine.program
lemma setup_code : BlockAt setup program 0 := by
 intro i hi
 have lookup:=UniformAllAxisSeedPreparation.lookup_segment [] (setup.map Op.code)
  (UniformCrossHeightPreparationMachine.program.map (relocate 6 192)++[.halt]) i (by simpa using hi)
 simpa only [program,List.nil_append,List.length_nil,List.append_assoc,List.getElem?_map,
  List.getElem?_eq_getElem hi,Option.map_some,Nat.zero_add] using lookup
lemma height_code : CodeAt UniformCrossHeightPreparationMachine.program program 6 192 :=
 UniformRankCrossPreparationMachine.segment_code (setup.map Op.code) [.halt] _ 6 192 (by
  simp only [List.length_map,setup_length])
lemma halt_at : program[192]?=some .halt := by
 let before:=setup.map Op.code++UniformCrossHeightPreparationMachine.program.map (relocate 6 192)
 have len:before.length=192:=by
  simp only [before,List.length_append,List.length_map,setup_length,
   UniformCrossHeightPreparationMachine.program_length]
 change (before++[.halt])[192]?=some .halt
 rw [List.getElem?_append_right (by omega),len];rfl

noncomputable section
structure Args (D F U J : ℕ) (s : State) : Prop where
 rows : s.natReg 4232=D
 colors : s.natReg 4233=F
 palette : s.natReg 4234=U
 directory : s.natReg 4235=J

lemma setup_safe (B : ℕ) (s : State) (hs:WordBound B s) :
 readable setup s ∧ peak setup s ≤ B := by
 constructor
 · simp [setup,readable,Op.readable]
 · simp only [setup,peak,Op.peak,Op.apply,writeNat,next];simp
   exact ⟨hs.2.1 4232,hs.2.1 4233,hs.2.1 4234,hs.2.1 4235⟩
lemma setup_heap (s:State) : (applyBlock setup s).natHeap=s.natHeap := by
 simp only [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_scalar (s:State) : (applyBlock setup s).scalarHeap=s.scalarHeap := by
 simp only [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_keeps (s:State) (q:ℕ) (keep:q ∉ [4236,1056,1057,1058,1059,1061]) :
 (applyBlock setup s).natReg q=s.natReg q := by
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at keep
 simp (disch:=omega) [setup,applyBlock,Op.apply,writeNat,next]
lemma setup_header (v:Parameters) (D F U J:ℕ) (s:State)
 (h:Header v s) (args:Args D F U J s) : Header (disabled v D F U J) (applyBlock setup s) := by
 constructor <;>
  simp [setup,applyBlock,Op.apply,writeNat,next,disabled,args.rows,args.colors,args.palette,args.directory,
   h.exponent,h.targets,h.inputs,h.tape,h.order,h.sourceDirectory,h.coefficients,h.constants]

lemma source_setup {G:ℕ} (v:Parameters) (D F U J:ℕ)
 (p:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize v.K) v.e G) (s:State)
 (h:Source v p s) : Source (disabled v D F U J) p (applyBlock setup s) := by
 refine ⟨?_,?_,?_⟩
 · simpa only [disabled,UniformDAGBucketMachine.Bank,setup_heap] using h.bank
 · simpa only [disabled,UniformDAGBucketMachine.Directory,setup_heap] using h.directory
 · simpa only [disabled,UniformToeplitzCrossTopologyMachine.RowTable,setup_heap] using h.tape

lemma prefix_retained (v:Parameters) (s u:State) (layout:Layout v)
 (outside:Outside v s u) : ∀q,q<v.D → u.natHeap q=s.natHeap q := by
 have df:v.D ≤ v.F:=by have:=layout.rows;unfold rowBase at this;omega
 have fu:v.F ≤ v.U:=by have:=layout.colors;unfold colorBase at this;omega
 have uj:v.U ≤ v.J:=by have:=layout.palette;omega
 intro q hq
 exact outside q (Or.inl hq) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

/-- The physical second bank is derived by executing Height186. No disabled
rows, colors, depth counts or matching-action certificate are inputs. -/
theorem execution (v:Parameters) (D F U J Z B m:ℕ)
 (ha:v.a ≤ widthOf v) (he:v.e ≤ widthOf v) (x:Fin m→ℂ) (s:State)
 (header:Header v s) (args:Args D F U J s)
 (source:Source v (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program s)
 (old:Processed v Z (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) s)
 (oldLayout:Layout v) (layout:Layout (disabled v D F U J))
 (before:recordBase v (height v) ≤ D)
 (budget:wordBudget (disabled v D F U J) ≤ B)
 (code:193 ≤ B) (pc:s.pc=0) (hs:WordBound B s) : ∃u ticks,
 BoundedExecution program m x B s ticks u ∧
 ticks ≤ 4*v.K+34+height v*(64*gates v+200*(2*gates v+1)^2+56) ∧ u.pc=192 ∧
 Cursor (disabled v D F U J) (height v) u ∧
 Source v (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program u ∧
 Processed v Z (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) u ∧
 Processed (disabled v D F U J) Z
  (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program (height v) u ∧
 (∀q,q<D → u.natHeap q=s.natHeap q) ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀q,100 ≤ q → q ≤ 106 → u.natReg q=s.natReg q) := by
 have safe:=setup_safe B s hs
 have first:=block_runs setup program 0 m B x s setup_code pc hs
  (by rw [setup_length];omega) safe.1 safe.2
 let z:=applyBlock setup s
 have zp:z.pc=6:=by rw [applyBlock_pc,pc,setup_length]
 let entry:=setPC z 0
 have eb:=changePC_bound B z 0 first.final_bound (by omega)
 let w:=disabled v D F U J
 have wsource:Source w (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program entry:=
  (source_setup v D F U J _ s source).withPC
 have wh:Header w entry:=(setup_header v D F U J s header args).withPC _
 have gEq:(UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size=gates v:=cross_size v ha he
 have wge:(UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size=gates w:=gEq
 have high:height w-1 ≤ (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).size:=by
  have h:=UniformCrossDepthReplayPreparation.cross_height_le_size v.K v.a v.e ha he
  dsimp only [w,disabled,height]
  omega
 obtain ⟨last,t,run,cost,lastPC,cursor,lastSource,done,outside,frame⟩:=
  UniformCrossHeightPreparationMachine.execution w Z B m
   (UniformToeplitzCrossDAG.crossDAG v.K v.a v.e ha he).program x entry wge layout
   (UniformCrossShearTableMachine.cross_good v.K v.a v.e ha he)
   (fun d _=>UniformCrossDepthReplayPreparation.cross_bucket_degree v.K v.a v.e d ha he false)
   high wh wsource rfl eb budget
 have call:=UniformBoundedAssembly.boundedExecution_placed height_code
  (by rw [UniformCrossHeightPreparationMachine.program_length];omega) (by omega) run
 rw [UniformSeedRankCrossPreparation.placed_zero z 6 zp] at call
 let u:=setPC last 192
 have stop:BoundedExecution program m x B u 1 u:=.halt call.final_bound (by simp [step,u,setPC,halt_at])
 have nat:∀q,q<D → u.natHeap q=s.natHeap q:=by
  intro q hq
  exact (prefix_retained w entry last layout outside q hq).trans (congrFun (setup_heap s) q)
 have rowBefore:v.D ≤ recordBase v (height v):=by
  have:=oldLayout.rows;have:=oldLayout.colors;have:=oldLayout.palette
  unfold rowBase colorBase recordBase at *;omega
 refine ⟨u,6+t+1,?_,?_,rfl,cursor.withPC,?_,?_,done,nat,
  frame.1.trans (setup_scalar s),frame.2.1,frame.2.2.1,frame.2.2.2.1,?_⟩
 · simpa only [setup_length,Nat.add_assoc] using first.executes (call.executes stop)
 · simpa only [w,disabled,height,gates,widthOf,iterationBudget] using (show 6+t+1 ≤
    4*w.K+34+height w*iterationBudget w by omega)
 · exact source.transport gEq oldLayout (fun q hq=>nat q (lt_of_lt_of_le hq (rowBefore.trans before)))
 · exact UniformLocalRectangleCoefficientMachine.processed_prefix v Z _ old gEq oldLayout
    (fun q hq=>nat q (lt_of_lt_of_le hq before))
 · intro q lo hi
   exact (saved_headers frame q ⟨lo,hi⟩).trans
    (setup_keeps s q (by simp only [List.mem_cons,List.not_mem_nil,or_false];omega))

end
end ExactFourierCircuits.UniformLocalDisabledHeightMachine
