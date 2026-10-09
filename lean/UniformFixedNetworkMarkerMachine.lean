import UniformFixedNetworkOpcodeMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformFixedNetworkMarkerMachine
open UniformMachine UniformAssembly
open UniformFixedNetworkScheduleMachine (Record Printed)
open UniformFixedNetworkOpcodeMachine (Fields Frame WellFormed headCost headProgram head_execution)
noncomputable section
/-- Marker children read their physical headers/body geometry and advance the
record cursor. Global role indices are already printed in every macro. -/
def program : Program := headProgram.map (relocate 0 52)++
 [.natBinary .add 2850 2865 2866,.halt]
theorem program_length : program.length=54 := rfl
theorem reader_code : CodeAt headProgram program 0 52 := by
 intro i hi
 simp [program,List.getElem?_append_left,hi]
theorem advance_at : program[52]?=some (.natBinary .add 2850 2865 2866) := rfl
theorem halt_at : program[53]?=some .halt := rfl

theorem execution (A B n : ℕ) (r : Record) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (pointer : s.natReg 2850=A) (bound : WordBound B s)
 (bank : Printed A r.data s) (marker : r.opcode=2 ∨ r.opcode=6)
 (good : WellFormed r) (extent : A+r.data.length≤B)
 (width : r.width+1≤B) (code : 54≤B) : ∃u,
 BoundedExecution program n x B s (headCost r+2) u ∧ u.pc=53 ∧
 u.natReg 2850=A+r.data.length ∧ Frame s u := by
 obtain ⟨v,run,fields,body,nextptr,frame⟩:=head_execution A B n r x s pointer pc bound bank
  good extent width (by omega)
 have placedRun:=UniformBoundedAssembly.boundedExecution_placed reader_code
  (by rw [UniformFixedNetworkOpcodeMachine.headProgram_length];omega) (by omega) run
 have start : UniformAssembly.placed 0 s=s := by simp [UniformAssembly.placed]
 rw [start] at placedRun
 let ret:State:={v with pc:=52}
 let u:=writeNat ret 2850 (A+r.data.length)
 have ub : WordBound B u := writeNat_bound B ret 2850 _ placedRun.final_bound
  (by change 53≤B;omega) extent
 have stepAdvance : step program n x ret=.running u := by
  simp only [step,show ret.pc=52 from rfl,advance_at]
  rw [show ret.natReg 2865=A+r.data.length from nextptr,
   show ret.natReg 2866=0 from fields.zero]
  rfl
 have stop : BoundedExecution program n x B ret 2 u:=.next placedRun.final_bound
  stepAdvance (.halt ub (by simp [step,u,ret,writeNat,next,halt_at]))
 have updateFrame : Frame ret u := by
  have eq : u=(UniformTensorMonomialMachine.Op.add 2850 2865 2866).apply ret := by
   simp [u,ret,UniformTensorMonomialMachine.Op.apply,nextptr,fields.zero]
  rw [eq]
  exact UniformFixedNetworkOpcodeMachine.op_frame _ _ (by norm_num [UniformFixedNetworkOpcodeMachine.NatRange])
 refine ⟨u,placedRun.executes stop,rfl,by simp [u,writeNat],(frame.pc 52).trans updateFrame⟩

theorem boundary_execution (q A B n : ℕ) (i : UniformFixedNetworkScheduleMachine.Invocation)
 (x : Fin n→ℂ) (s : State) (pc : s.pc=0) (pointer : s.natReg 2850=A)
 (bound : WordBound B s)
 (bank : Printed A (UniformFixedNetworkScheduleMachine.blockBoundary q i).data s)
 (extent : A+(UniformFixedNetworkScheduleMachine.blockBoundary q i).data.length≤B)
 (width : UniformFixedNetworkScheduleMachine.seedWidth+1≤B) (code : 54≤B) : ∃u,
 BoundedExecution program n x B s 36 u ∧ u.pc=53 ∧
 u.natReg 2850=A+(UniformFixedNetworkScheduleMachine.blockBoundary q i).data.length ∧ Frame s u := by
 have run:=execution A B n (UniformFixedNetworkScheduleMachine.blockBoundary q i) x s pc pointer bound bank
  (Or.inl rfl) (UniformFixedNetworkOpcodeMachine.boundary_wellFormed q i) extent width code
 simpa [headCost,UniformFixedNetworkScheduleMachine.blockBoundary] using run

/-- Leading layout metadata consumes exactly40 steps. This does not assert
that an arbitrary differently laid-out data bank has been rearranged. -/
theorem layout_execution (q w actual W roleBits A B n : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (pointer : s.natReg 2850=A) (bound : WordBound B s)
 (bank : Printed A (Record.mk 6 q w actual W 0 roleBits 0 []).data s)
 (extent : A+8≤B) (width : w+1≤B) (code : 54≤B) : ∃u,
 BoundedExecution program n x B s 40 u ∧ u.pc=53 ∧
 u.natReg 2850=A+8 ∧ Frame s u := by
 have run:=execution A B n (Record.mk 6 q w actual W 0 roleBits 0 []) x s pc pointer bound bank
  (Or.inr rfl) (by simp [WellFormed,UniformFixedNetworkOpcodeMachine.bodyLength])
  (by simpa [Record.data_length] using extent) width code
 simpa [headCost,Record.data_length] using run
end
end ExactFourierCircuits.UniformFixedNetworkMarkerMachine
