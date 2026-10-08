import UniformScalarReplayMachine
import UniformBoundedAssembly

set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirtyReplayMachine
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInPlaceMachine (Row prepared)
open UniformRadixTwoDAG (width)

/-- Setup is real bytecode; no caller writes occur between the two scalar runs. -/
def forwardSetup : List Op := [.literal 1170 0,.add 1160 980 1170,.add 1161 981 1170]
def inverseSetup : List Op := [.add 1161 982 1170]
def program : Program := UniformInverseShearTableMachine.program.map (relocate 0 36) ++
  forwardSetup.map Op.code ++ UniformScalarReplayMachine.program.map (relocate 39 59) ++
  inverseSetup.map Op.code ++ UniformScalarReplayMachine.program.map (relocate 60 80) ++ [.halt]
lemma program_length : program.length=81 := by
  simp only [program,List.length_append,List.length_map,
    UniformInverseShearTableMachine.program_length,UniformScalarReplayMachine.program_length]
  rfl
lemma inverse_table_code : CodeAt UniformInverseShearTableMachine.program program 0 36 := by
  intro i hi;rw [UniformInverseShearTableMachine.program_length] at hi
  interval_cases i <;> rfl
lemma forward_setup_code : BlockAt forwardSetup program 36 := by intro i hi;change i<3 at hi;interval_cases i <;> rfl
lemma forward_code : CodeAt UniformScalarReplayMachine.program program 39 59 := by
  intro i hi;rw [UniformScalarReplayMachine.program_length] at hi
  interval_cases i <;> rfl
lemma inverse_setup_code : BlockAt inverseSetup program 59 := by intro i hi;change i<1 at hi;interval_cases i;rfl
lemma inverse_code : CodeAt UniformScalarReplayMachine.program program 60 80 := by
  intro i hi;rw [UniformScalarReplayMachine.program_length] at hi
  interval_cases i <;> rfl
lemma halt_at : program[80]?=some .halt := rfl

noncomputable section
abbrev Rows:=UniformInverseShearTableMachine.Rows
abbrev inverseRows:=UniformInverseShearTableMachine.inverseRows
abbrev Data:=UniformScalarReplayMachine.Data
abbrev numeric:=UniformScalarReplayMachine.numeric
abbrev action:=UniformScalarReplayMachine.action
abbrev valueOf:=UniformInverseShearTableMachine.heapCoefficient

/-- Nat inverse-table scratch990..1000, replay caller/scratch1160..1168 and
zero1170 may change. Scalar scratch90..93 may change. -/
def Protected (q : ℕ) : Prop := (q<990 ∨ 1001≤q) ∧ (q<1160 ∨ 1169≤q) ∧ q≠1170
def Frame (s u : State) : Prop := u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  (∀q,Protected q→u.natReg q=s.natReg q) ∧ (∀q,(q<90 ∨ 94≤q)→u.scalarReg q=s.scalarReg q)
lemma Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩
lemma Frame.trans {s u v : State} (h:Frame s u) (h':Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,
    fun q hq=>(h'.2.2.1 q hq).trans (h.2.2.1 q hq),
    fun q hq=>(h'.2.2.2 q hq).trans (h.2.2.2 q hq)⟩
lemma table_frame {s u : State} (h:UniformInverseShearTableMachine.Frame s u) : Frame s u :=
  ⟨h.2.2.1,h.2.2.2.1,fun q hq=>h.2.2.2.2 q hq.1,fun q _=>congrFun h.2.1 q⟩
lemma replay_frame {s u : State} (h:UniformScalarReplayMachine.Frame s u) : Frame s u :=
  ⟨h.2.1,h.2.2.1,fun q hq=>h.2.2.2.1 q (by unfold Protected at hq;omega),h.2.2.2.2⟩
lemma Frame.withPC {s u : State} (h:Frame s u) (pc : ℕ) : Frame s {u with pc:=pc} := h
lemma forward_setup_frame (s : State) : Frame s (applyBlock forwardSetup s) := by
  refine ⟨rfl,rfl,?_,fun _ _=>rfl⟩
  intro q hq
  unfold Protected at hq
  simp (disch:=omega) [forwardSetup,applyBlock,Op.apply,writeNat,next]
lemma inverse_setup_frame (s : State) : Frame s (applyBlock inverseSetup s) := by
  refine ⟨rfl,rfl,?_,fun _ _=>rfl⟩
  intro q hq
  unfold Protected at hq
  simp (disch:=omega) [inverseSetup,applyBlock,Op.apply,writeNat,next]
lemma forward_setup_heap (s : State) : (applyBlock forwardSetup s).natHeap=s.natHeap ∧
    (applyBlock forwardSetup s).scalarHeap=s.scalarHeap := ⟨rfl,rfl⟩
lemma inverse_setup_heap (s : State) : (applyBlock inverseSetup s).natHeap=s.natHeap ∧
    (applyBlock inverseSetup s).scalarHeap=s.scalarHeap := ⟨rfl,rfl⟩
lemma reset_placed (base : ℕ) (s : State) (h:s.pc=base) : placed base {s with pc:=0}=s := by
  cases s
  change _=base at h
  subst h
  rfl

lemma forward_setup_header (M F O C T P : ℕ) (s : State)
    (h:UniformInverseShearTableMachine.Header M F O C T P s) :
    UniformScalarReplayMachine.Header M F (applyBlock forwardSetup s) ∧
    (applyBlock forwardSetup s).natReg 1170=0 := by
  refine ⟨⟨?_,?_⟩,?_⟩
  all_goals simp [forwardSetup,applyBlock,Op.apply,writeNat,next,h.count,h.source]
lemma inverse_setup_header (M O : ℕ) (s : State)
    (hm:s.natReg 1160=M) (ho:s.natReg 982=O) (hz:s.natReg 1170=0) :
    UniformScalarReplayMachine.Header M O (applyBlock inverseSetup s) := by
  constructor <;> simp [inverseSetup,applyBlock,Op.apply,writeNat,next,hm,ho,hz]

lemma domain_lower (C P m q : ℕ) (hp:C≤P)
    (h:UniformInverseShearTableMachine.Domain C P m q) : C≤q := by
  rcases h with ⟨j,hj,rfl⟩|rfl|rfl|rfl <;> omega
lemma inverse_lower (C T P m q : ℕ) (hC:C+m≤T) (hT:T+m≤P)
    (h:UniformInverseShearTableMachine.Domain C P m q) :
    C≤UniformInverseShearTableMachine.inverseAddress C T P q := by
  rcases h with ⟨j,hj,rfl⟩|rfl|rfl|rfl
  · rw [UniformInverseShearTableMachine.inverseAddress_prepared C T P m j hj (by omega)];omega
  · rw [UniformInverseShearTableMachine.inverseAddress_unit];omega
  · rw [UniformInverseShearTableMachine.inverseAddress_negativeUnit];omega
  · rw [UniformInverseShearTableMachine.inverseAddress_normalization];omega
lemma inverse_member (C T P : ℕ) (rows : List Row) (r : Row) (h:r∈inverseRows C T P rows) :
    ∃q∈rows,r=UniformInverseShearTableMachine.inverseRow C T P q := by
  obtain ⟨q,hq,he⟩:=List.mem_map.mp h
  exact ⟨q,List.mem_reverse.mp hq,he.symm⟩

/-- Mere physical presence of a data cell is preserved by every scalar store. -/
lemma present_action (value : ℕ→ℂ) (rows : List Row) (heap : ℕ→Option Scalar) (q : ℕ)
    (h:∃a,heap q=some a) : ∃a,action value rows heap q=some a := by
  induction rows generalizing heap with
  | nil=>exact h
  | cons row rows ih=>
    exact ih _ (UniformScalarReplayMachine.present_update _ _ _ _ h)
lemma inverse_data (C T P : ℕ) (rows : List Row) (s : State) (h:Data rows s) :
    Data (inverseRows C T P rows) s := by
  intro row hr
  obtain ⟨q,hq,rfl⟩:=inverse_member C T P rows row hr
  exact h q hq
lemma data_after_action (value : ℕ→ℂ) (rows after : List Row) (s u : State)
    (h:Data after s) (hu:u.scalarHeap=action value rows s.scalarHeap) : Data after u := by
  intro row hr
  have hx:=h row hr
  rw [hu]
  exact ⟨present_action value rows _ _ hx.1,present_action value rows _ _ hx.2⟩

lemma separated_of_geometry (C : ℕ) (rows : List Row)
    (hd:∀row∈rows,row.dst<C) (hc:∀row∈rows,C≤row.coefficient) :
    UniformScalarReplayMachine.Separated rows := by
  intro row hr other ho
  have :=hd row hr
  have :=hc other ho
  omega
lemma retained_above (C : ℕ) (rows : List Row) (value : ℕ→ℂ) (s u : State)
    (hd:∀row∈rows,row.dst<C) (hu:u.scalarHeap=action value rows s.scalarHeap) :
    ∀q,C≤q→u.scalarHeap q=s.scalarHeap q := by
  intro q hq
  rw [hu]
  apply UniformScalarReplayMachine.action_outside
  intro row hr
  have :=hd row hr
  omega
lemma coefficients_transport (rows : List Row) (value : ℕ→ℂ) (s u : State) (C : ℕ)
    (h:UniformScalarReplayMachine.Coefficients rows value s)
    (hc:∀row∈rows,C≤row.coefficient) (eq:∀q,C≤q→u.scalarHeap q=s.scalarHeap q) :
    UniformScalarReplayMachine.Coefficients rows value u := by
  intro row hr
  rw [eq _ (hc row hr)]
  exact h row hr

lemma inverse_geometry (C T P : ℕ) (rows : List Row)
    (hd:∀row∈rows,row.dst<C) : ∀row∈inverseRows C T P rows,row.dst<C := by
  intro row hr
  obtain ⟨q,hq,rfl⟩:=inverse_member C T P rows row hr
  exact hd q hq
lemma inverse_coefficients_lower (C T P m : ℕ) (rows : List Row)
    (hC:C+m≤T) (hT:T+m≤P)
    (dom:∀row∈rows,UniformInverseShearTableMachine.Domain C P m row.coefficient) :
    ∀row∈inverseRows C T P rows,C≤row.coefficient := by
  intro row hr
  obtain ⟨q,hq,rfl⟩:=inverse_member C T P rows row hr
  exact inverse_lower C T P m q.coefficient hC hT (dom q hq)

lemma signed_banks_retained {K C T P : ℕ} {bank : ℕ→ℂ} {s u : State}
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (hC:C+7*width K≤T) (hT:T+7*width K≤P)
    (eq:∀q,C≤q→u.scalarHeap q=s.scalarHeap q) :
    UniformReplayCoefficientMachine.Source C (7*width K) bank u ∧
    UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank u ∧
    UniformReplayCoefficientMachine.Constants K P u := by
  refine ⟨?_,?_,?_⟩
  · intro j hj;rw [eq _ (by omega)];exact pos j hj
  · intro j hj;rw [eq _ (by omega)];exact neg j hj
  · intro j hj;rw [eq _ (by omega)];exact constants j hj

/-- Continuous inverse-table production, forward replay and inverse replay.
Every row/read/setup/branch/halt is charged. Data presence and signed physical
banks are inputs; no action, inverse table, Ready state or schedule is supplied.
The final scalar tags are the literal composition, not a restoration claim. -/
theorem execution (K M F O C T P B n : ℕ) (x : Fin n→ℂ)
    (rows : List Row) (bank : ℕ→ℂ) (s : State)
    (header:UniformInverseShearTableMachine.Header M F O C T P s)
    (pc:s.pc=0) (len:rows.length=M) (src:Rows F rows s) (data:Data rows s)
    (dom:∀row∈rows,UniformInverseShearTableMachine.Domain C P (7*width K) row.coefficient)
    (endpoints:∀row∈rows,row.dst<C ∧ row.src<C)
    (different:∀row∈rows,row.dst≠row.src)
    (pos:UniformReplayCoefficientMachine.Source C (7*width K) bank s)
    (neg:UniformReplayCoefficientMachine.NegativeBank T (7*width K) bank s)
    (constants:UniformReplayCoefficientMachine.Constants K P s)
    (hC:C+7*width K≤T) (hT:T+7*width K≤P) (hP:P+3≤B)
    (hF:F+3*M≤O) (hO:O+3*M≤B) (hB:81≤B) (hs:WordBound B s) :
    ∃u ticks,BoundedExecution program n x B s ticks u ∧ ticks≤57*M+21 ∧ u.pc=80 ∧
      u.scalarHeap=action (valueOf s) (inverseRows C T P rows)
        (action (valueOf s) rows s.scalarHeap) ∧ numeric u.scalarHeap=numeric s.scalarHeap ∧
      Rows F rows u ∧ Rows O (inverseRows C T P rows) u ∧
      UniformInverseShearTableMachine.Outside O M s u ∧ Frame s u ∧
      (∀q,(∀row∈rows,q≠row.dst)→u.scalarHeap q=s.scalarHeap q) ∧
      (∀q,C≤q→u.scalarHeap q=s.scalarHeap q) := by
  have sep:C+7*width K≤P := by omega
  have lower : ∀row∈rows,C≤row.coefficient := fun row hr=>domain_lower C P _ _ (by omega) (dom row hr)
  have ilower := inverse_coefficients_lower C T P (7*width K) rows hC hT dom
  have dstBound : ∀row∈rows,row.dst<C := fun row hr=>(endpoints row hr).1
  have idstBound := inverse_geometry C T P rows dstBound
  have separated:=separated_of_geometry C rows dstBound lower
  have iseparated:=separated_of_geometry C _ idstBound ilower
  have forwardCoefficients:=UniformScalarReplayMachine.coefficients_forward rows bank s pos neg constants sep dom
  have inverseCoefficients:=UniformScalarReplayMachine.coefficients_inverse rows bank s pos neg constants sep dom
  obtain ⟨steps,a,acost,arun,apc,aheader,atable,original,aoutside,aframe⟩:=
    UniformInverseShearTableMachine.execution M F O C T P (7*width K) B n x rows s
      header pc len src dom hC hT hP hF hO (by omega) hs
  have placedTable:=UniformBoundedAssembly.boundedExecution_placed inverse_table_code
    (by rw [UniformInverseShearTableMachine.program_length];omega) (by omega) arun
  rw [show placed 0 s=s by cases s;simp [placed]] at placedTable
  let b:State:={a with pc:=36}
  have setup:=block_runs forwardSetup program 36 n B x b forward_setup_code rfl placedTable.final_bound
    (by change 36+3≤B;omega) (by simp [readable,forwardSetup,Op.readable])
    (by simp [peak,forwardSetup,Op.peak,Op.apply,writeNat,next,b,aheader.count,aheader.source];omega)
  let c:=applyBlock forwardSetup b
  have cpc:c.pc=39 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  obtain ⟨ch,cz⟩:=forward_setup_header M F O C T P b ⟨aheader.count,aheader.source,aheader.output,aheader.positive,aheader.negative,aheader.constants⟩
  have cheader:UniformScalarReplayMachine.Header M F {c with pc:=0} := ⟨ch.count,ch.table⟩
  have cscalar:c.scalarHeap=s.scalarHeap := aframe.1
  have cdata:Data rows {c with pc:=0} := by intro row hr;simpa only [cscalar] using data row hr
  have ccoeff:UniformScalarReplayMachine.Coefficients rows (valueOf s) {c with pc:=0} := by
    intro row hr;simpa only [cscalar] using forwardCoefficients row hr
  have crows:Rows F rows {c with pc:=0} := original
  obtain ⟨d,drun,dpc,dheader,daction,dframe,doutside⟩:=UniformScalarReplayMachine.execution n B M F x rows (valueOf s) {c with pc:=0}
    cheader rfl len crows cdata ccoeff separated (by omega) (by omega)
    (changePC_bound B c 0 setup.final_bound (by omega))
  have placedForward:=UniformBoundedAssembly.boundedExecution_placed forward_code
    (by rw [UniformScalarReplayMachine.program_length];omega) (by omega) drun
  rw [reset_placed 39 c cpc] at placedForward
  let e:State:={d with pc:=59}
  have eaction:e.scalarHeap=action (valueOf s) rows s.scalarHeap := daction.trans (congrArg (action (valueOf s) rows) cscalar)
  have eo:e.natReg 982=O := (dframe.2.2.2.1 982 (by omega)).trans
    (by simp [c,forwardSetup,applyBlock,Op.apply,writeNat,next,b,aheader.output])
  have ez:e.natReg 1170=0 := (dframe.2.2.2.1 1170 (by omega)).trans cz
  have invSetup:=block_runs inverseSetup program 59 n B x e inverse_setup_code rfl placedForward.final_bound
    (by change 59+1≤B;omega) (by simp [readable,inverseSetup,Op.readable])
    (by simp [peak,inverseSetup,Op.peak,ez,eo];omega)
  let f:=applyBlock inverseSetup e
  have fpc:f.pc=60 := by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
  have fh:=inverse_setup_header M O e dheader.count eo ez
  have fheader:UniformScalarReplayMachine.Header M O {f with pc:=0} := ⟨fh.count,fh.table⟩
  have fheap:f.natHeap=a.natHeap := dframe.1
  have frows:Rows O (inverseRows C T P rows) {f with pc:=0} := by
    intro j hj
    change f.natHeap _=_ ∧ f.natHeap _=_ ∧ f.natHeap _=_
    rw [fheap];exact atable j hj
  have faction:f.scalarHeap=action (valueOf s) rows s.scalarHeap := eaction
  have fdata:Data (inverseRows C T P rows) {f with pc:=0} :=
    data_after_action (valueOf s) rows _ s {f with pc:=0} (inverse_data C T P rows s data) faction
  have fabove:∀q,C≤q→f.scalarHeap q=s.scalarHeap q := retained_above C rows (valueOf s) s f dstBound faction
  have fcoeff:UniformScalarReplayMachine.Coefficients (inverseRows C T P rows) (valueOf s) {f with pc:=0} :=
    coefficients_transport _ _ s {f with pc:=0} C inverseCoefficients ilower fabove
  obtain ⟨u,urun,upc,uheader,uaction,uframe,uoutside⟩:=UniformScalarReplayMachine.execution n B M O x
    (inverseRows C T P rows) (valueOf s) {f with pc:=0} fheader rfl
    (by rw [UniformInverseShearTableMachine.inverseRows_length,len]) frows fdata fcoeff iseparated
    (by omega) hO (changePC_bound B f 0 invSetup.final_bound (by omega))
  have placedInverse:=UniformBoundedAssembly.boundedExecution_placed inverse_code
    (by rw [UniformScalarReplayMachine.program_length];omega) (by omega) urun
  rw [reset_placed 60 f fpc] at placedInverse
  let v:State:={u with pc:=80}
  have stop:BoundedExecution program n x B v 1 v := .halt placedInverse.final_bound (by simp [step,v,halt_at])
  have whole:=(placedTable.trans (setup.trans (placedForward.trans (invSetup.trans placedInverse)))).executes stop
  have va:v.scalarHeap=action (valueOf s) (inverseRows C T P rows) (action (valueOf s) rows s.scalarHeap) :=
    uaction.trans (congrArg (action (valueOf s) (inverseRows C T P rows)) faction)
  have numericRestored:numeric v.scalarHeap=numeric s.scalarHeap := by
    rw [va]
    change UniformScalarReplayMachine.numeric (UniformScalarReplayMachine.action (valueOf s)
      (inverseRows C T P rows) (UniformScalarReplayMachine.action (valueOf s) rows s.scalarHeap)) = _
    rw [UniformScalarReplayMachine.action_numeric,UniformScalarReplayMachine.action_numeric]
    exact UniformInverseShearTableMachine.physical_inverse_action rows pos neg constants sep dom different _
  have vheap:v.natHeap=a.natHeap := uframe.1.trans fheap
  have frame:Frame s v := (table_frame aframe).trans ((forward_setup_frame b).trans
    ((replay_frame dframe).trans ((inverse_setup_frame e).trans (replay_frame uframe))))
  have outside:∀q,(∀row∈rows,q≠row.dst)→v.scalarHeap q=s.scalarHeap q := by
    intro q hq
    rw [va]
    change UniformScalarReplayMachine.action (valueOf s) (inverseRows C T P rows)
      (UniformScalarReplayMachine.action (valueOf s) rows s.scalarHeap) q = _
    rw [UniformScalarReplayMachine.action_outside (valueOf s) (inverseRows C T P rows) _ q (by
      intro row hr;obtain ⟨z,hz,rfl⟩:=inverse_member C T P rows row hr;exact hq z hz),
      UniformScalarReplayMachine.action_outside (valueOf s) rows _ q hq]
  refine ⟨v,steps+3+(16*M+5)+1+(16*M+5)+1,?_,?_,rfl,va,numericRestored,?_,?_,?_,frame,outside,?_⟩
  · convert whole using 1
    simp only [show forwardSetup.length=3 by rfl,show inverseSetup.length=1 by rfl]
    omega
  · unfold UniformInverseShearTableMachine.runtimeBudget at acost;omega
  · intro j hj;rw [vheap];exact original j hj
  · intro j hj;rw [vheap];exact atable j hj
  · intro j hj;rw [vheap];exact aoutside j hj
  · intro q hq
    apply outside q
    intro row hr
    have :=dstBound row hr
    omega

lemma saved_headers {s u : State} (h:Frame s u) (j : ℕ) (hj:100≤j ∧ j≤106) : u.natReg j=s.natReg j :=
  h.2.2.1 j (by unfold Protected;omega)

/-- Optional ordinary allocation geometry protects the master scalar and its
actual dependency tag, separately from the all-array numeric restoration. -/
lemma master_retained (rows : List Row) (s u : State)
    (outside:∀q,(∀row∈rows,q≠row.dst)→u.scalarHeap q=s.scalarHeap q)
    (geometry:∀row∈rows,row.dst≠0) : u.scalarHeap 0=s.scalarHeap 0 :=
  outside 0 (fun row hr=>(geometry row hr).symm)

end
end ExactFourierCircuits.UniformDirtyReplayMachine

