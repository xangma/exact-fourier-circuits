import UniformRecursiveSavingProgram
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveNativeEntries
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (setPC)
open UniformFixedNetworkScheduleMachine (Record Printed)
open UniformFixedNetworkShearChildMachine (Present)
open UniformResidualNativeTranslationMachine (volume)
open UniformFixedNetworkOpcodeMachine (Frame headCost WellFormed)
noncomputable section

/- Actual helper entries in the same immutable recursive Program. Every theorem
executes raw printed records; no child-action or prepared decoded-field premise. -/
namespace UniformNativeScalarRecordMachine
open _root_.ExactFourierCircuits.UniformNativeScalarRecordMachine
theorem embedded (main:Program)(start exit:ℕ)
 (link:CodeAt _root_.ExactFourierCircuits.UniformNativeScalarRecordMachine.scalarProgram main start exit) {R:ℕ} (q w k A T B n:ℕ) (x:Fin n→ℂ)
 (d source:Fin R) (ne:d≠source) (c:Fin 5)
 (f:Fin R→Fin (2^(k))→Scalar) (s:State)
 (pc:s.pc=start) (ptr:s.natReg 2850=T) (base:s.natReg 3300=A) (native:s.natReg 5300=k)
 (bank:Printed T (shearRecord q w d source c).data s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(k)) f s)
 (hs:WordBound B s) (code:start+_root_.ExactFourierCircuits.UniformNativeScalarRecordMachine.scalarProgram.length≤B) (ret:exit≤B) (tableEnd:T+8≤B) (width:w+1≤B)
 (extent:A+R*2^(k)≤B) : ∃u,
 BoundedRuns main n x B s (10*2^(k)+4*(k)+c.val+62) u ∧ u.pc=exit ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(k))
  (UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode c) f) u ∧
 u.natReg 2850=T+8 ∧
 ScalarFrame (UniformFixedNetworkShearChildMachine.roleBase A (2^(k)) d.val) (2^(k)) s u := by
 have localCode:_root_.ExactFourierCircuits.UniformNativeScalarRecordMachine.scalarProgram.length≤B:=
   (Nat.le_add_left _ _).trans code
 have small:106≤B:=by
   simpa only [_root_.ExactFourierCircuits.UniformNativeScalarRecordMachine.scalarProgram_length] using localCode

 obtain ⟨u,run,present,done,fr⟩:=UniformNativeScalarRecordMachine.scalar_execution q w k A T B n x d source ne c f
   (setPC s 0) rfl ptr base native bank data (changePC_bound B s 0 hs (by omega))
   small tableEnd width extent
 have placed:=UniformBoundedAssembly.boundedExecution_placed link
   code ret run
 have start:UniformAssembly.placed (start) (setPC s 0)=s:=by
   change setPC s (start)=s
   rw [←pc];cases s;rfl
 rw [start] at placed
 refine ⟨setPC u (exit),placed,rfl,present,done,?_⟩
 exact ⟨fr.natHeap,fr.outputs,fr.roots,fr.natReg,fr.scalarReg,fr.scalarHeap⟩

theorem entry {R:ℕ} (q w k A T B n:ℕ) (x:Fin n→ℂ)
 (d source:Fin R) (ne:d≠source) (c:Fin 5)
 (f:Fin R→Fin (2^(k))→Scalar) (s:State)
 (pc:s.pc=UniformRecursiveSavingProgram.address .scalar) (ptr:s.natReg 2850=T) (base:s.natReg 3300=A) (native:s.natReg 5300=k)
 (bank:Printed T (shearRecord q w d source c).data s)
 (data:UniformFixedNetworkShearChildMachine.Present A R (2^(k)) f s)
 (hs:WordBound B s) (code:UniformRecursiveSavingProgram.address .scalar+_root_.ExactFourierCircuits.UniformNativeScalarRecordMachine.scalarProgram.length≤B) (ret:UniformRecursiveSavingProgram.address .loop≤B) (tableEnd:T+8≤B) (width:w+1≤B)
 (extent:A+R*2^(k)≤B) : ∃u,
 BoundedRuns UniformRecursiveSavingProgram.program n x B s (10*2^(k)+4*(k)+c.val+62) u ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
 UniformFixedNetworkShearChildMachine.Present A R (2^(k))
  (UniformFixedNetworkShearChildMachine.shearValues d source (UniformFixedCoefficientCodec.decode c) f) u ∧
 u.natReg 2850=T+8 ∧
 ScalarFrame (UniformFixedNetworkShearChildMachine.roleBase A (2^(k)) d.val) (2^(k)) s u := by
 exact embedded UniformRecursiveSavingProgram.program (UniformRecursiveSavingProgram.address .scalar)
   (UniformRecursiveSavingProgram.address .loop) UniformRecursiveSavingProgram.scalar_code
   q w k A T B n x d source ne c f s pc ptr base native bank data hs code ret tableEnd width extent

end UniformNativeScalarRecordMachine

namespace UniformNativeExchangeRecordMachine
open _root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine
theorem embedded (main:Program)(start exit:ℕ)
 (link:CodeAt _root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine.program main start exit) {R:ℕ} (q w k A T B n:ℕ) (x:Fin n→ℂ) (pairs:List (Pair R))
 (f:Fin R→Fin (2^(k))→Scalar) (s:State) (pc:s.pc=start) (ptr:s.natReg 2850=T)
 (base:s.natReg 3300=A) (native:s.natReg 5300=k) (bank:Printed T (record q w pairs).data s)
 (data:Present A R (2^(k)) f s) (hr:0<R) (hs:WordBound B s) (code:start+_root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine.program.length≤B) (ret:exit≤B)
 (extent:A+R*2^(k)≤B) (tableEnd:T+8+4*pairs.length≤B) (width:w+1≤B) :∃u,
 BoundedRuns main n x B s ((10*2^(k)+21)*pairs.length+4*(k)+50) u ∧ u.pc=exit ∧
 Present A R (2^(k)) (actions pairs f) u ∧ u.natReg 2850=T+8+4*pairs.length ∧
 FullFrame A (R*2^(k)) s u := by
 have localCode:_root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine.program.length≤B:=
   (Nat.le_add_left _ _).trans code
 have small:98≤B:=by
   simpa only [_root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine.program_length] using localCode

 obtain ⟨u,run,present,done,fr⟩:=UniformNativeExchangeRecordMachine.execution q w k A T B n x pairs f
   (setPC s 0) rfl ptr base native bank data hr (changePC_bound B s 0 hs (by omega))
   small extent tableEnd width
 have placed:=UniformBoundedAssembly.boundedExecution_placed link
   code ret run
 have start:UniformAssembly.placed (start) (setPC s 0)=s:=by
   change setPC s (start)=s
   rw [←pc];cases s;rfl
 rw [start] at placed
 refine ⟨setPC u (exit),placed,rfl,present,done,?_⟩
 exact ⟨fr.natHeap,fr.outputs,fr.roots,fr.natReg,fr.scalarReg,fr.scalarHeap⟩

theorem entry {R:ℕ} (q w k A T B n:ℕ) (x:Fin n→ℂ) (pairs:List (Pair R))
 (f:Fin R→Fin (2^(k))→Scalar) (s:State) (pc:s.pc=UniformRecursiveSavingProgram.address .exchange) (ptr:s.natReg 2850=T)
 (base:s.natReg 3300=A) (native:s.natReg 5300=k) (bank:Printed T (record q w pairs).data s)
 (data:Present A R (2^(k)) f s) (hr:0<R) (hs:WordBound B s) (code:UniformRecursiveSavingProgram.address .exchange+_root_.ExactFourierCircuits.UniformNativeExchangeRecordMachine.program.length≤B) (ret:UniformRecursiveSavingProgram.address .loop≤B)
 (extent:A+R*2^(k)≤B) (tableEnd:T+8+4*pairs.length≤B) (width:w+1≤B) :∃u,
 BoundedRuns UniformRecursiveSavingProgram.program n x B s ((10*2^(k)+21)*pairs.length+4*(k)+50) u ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
 Present A R (2^(k)) (actions pairs f) u ∧ u.natReg 2850=T+8+4*pairs.length ∧
 FullFrame A (R*2^(k)) s u := by
 exact embedded UniformRecursiveSavingProgram.program (UniformRecursiveSavingProgram.address .exchange)
   (UniformRecursiveSavingProgram.address .loop) UniformRecursiveSavingProgram.exchange_code
   q w k A T B n x pairs f s pc ptr base native bank data hr hs code ret extent tableEnd width

end UniformNativeExchangeRecordMachine

namespace UniformNativeYRecordMachine
open _root_.ExactFourierCircuits.UniformNativeYRecordMachine
theorem embedded (main:Program)(start exit:ℕ)
 (link:CodeAt _root_.ExactFourierCircuits.UniformNativeYRecordMachine.program main start exit) {R : ℕ} (q w rest k A E T P B n : ℕ) (x : Fin n→ℂ)
 (ds : List (Direction R w)) (f : Fin R→Fin (volume k)→Scalar) (s : State)
 (pc : s.pc=start) (ptr : s.natReg 2850=P) (base : s.natReg 3300=A)
 (native : s.natReg 5300=k) (restHeader : s.natReg 5301=rest)
 (shape : k=q*w+rest) (qp : 1≤q) (padded : 2^(q*(w+rest))≤B)
 (buffer : s.natReg 3364=E) (table : s.natReg 3389=T)
 (bank : Printed P (record q w ds).data s) (data : Present A R (volume k) f s)
 (bound : WordBound B s) (code : start+_root_.ExactFourierCircuits.UniformNativeYRecordMachine.program.length≤B) (ret : exit≤B) (sourceBeforeTable : P+(record q w ds).data.length≤T)
 (separate : A+R*volume k≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+volume k≤B)
 (width : w+1≤B) : ∃u,
 BoundedRuns main n x B s (runtime q w rest k ds.length) u ∧ u.pc=exit ∧
 Present A R (volume k) (actions q w k ds f) u ∧ u.natReg 2850=P+(record q w ds).data.length ∧
 FullFrame q A (R*volume k) E T w k s u := by
 have localCode:_root_.ExactFourierCircuits.UniformNativeYRecordMachine.program.length≤B:=
   (Nat.le_add_left _ _).trans code
 have small:197≤B:=by
   simpa only [_root_.ExactFourierCircuits.UniformNativeYRecordMachine.program_length] using localCode

 obtain ⟨u,run,present,done,fr⟩:=UniformNativeYRecordMachine.execution q w rest k A E T P B n x ds f
   (setPC s 0) rfl ptr base native restHeader shape qp padded buffer table bank data
   (changePC_bound B s 0 bound (by omega)) small sourceBeforeTable separate tableEnd extent width
 have placed:=UniformBoundedAssembly.boundedExecution_placed link
   code ret run
 have start:UniformAssembly.placed (start) (setPC s 0)=s:=by
   change setPC s (start)=s
   rw [←pc];cases s;rfl
 rw [start] at placed
 refine ⟨setPC u (exit),placed,rfl,present,done,?_⟩
 exact ⟨fr.natHeap,fr.outputs,fr.roots,fr.natReg,fr.scalarReg,fr.scalarHeap⟩

theorem entry {R : ℕ} (q w rest k A E T P B n : ℕ) (x : Fin n→ℂ)
 (ds : List (Direction R w)) (f : Fin R→Fin (volume k)→Scalar) (s : State)
 (pc : s.pc=UniformRecursiveSavingProgram.address .translation) (ptr : s.natReg 2850=P) (base : s.natReg 3300=A)
 (native : s.natReg 5300=k) (restHeader : s.natReg 5301=rest)
 (shape : k=q*w+rest) (qp : 1≤q) (padded : 2^(q*(w+rest))≤B)
 (buffer : s.natReg 3364=E) (table : s.natReg 3389=T)
 (bank : Printed P (record q w ds).data s) (data : Present A R (volume k) f s)
 (bound : WordBound B s) (code : UniformRecursiveSavingProgram.address .translation+_root_.ExactFourierCircuits.UniformNativeYRecordMachine.program.length≤B) (ret : UniformRecursiveSavingProgram.address .loop≤B) (sourceBeforeTable : P+(record q w ds).data.length≤T)
 (separate : A+R*volume k≤E) (tableEnd : T+2^q*2^q≤B) (extent : E+volume k≤B)
 (width : w+1≤B) : ∃u,
 BoundedRuns UniformRecursiveSavingProgram.program n x B s (runtime q w rest k ds.length) u ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
 Present A R (volume k) (actions q w k ds f) u ∧ u.natReg 2850=P+(record q w ds).data.length ∧
 FullFrame q A (R*volume k) E T w k s u := by
 exact embedded UniformRecursiveSavingProgram.program (UniformRecursiveSavingProgram.address .translation)
   (UniformRecursiveSavingProgram.address .loop) UniformRecursiveSavingProgram.translation_code
   q w rest k A E T P B n x ds f s pc ptr base native restHeader shape qp padded buffer table bank data bound code ret sourceBeforeTable separate tableEnd extent width

end UniformNativeYRecordMachine

namespace UniformFixedNetworkMarkerMachine
open _root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine
theorem embedded (main:Program)(start exit:ℕ)
 (link:CodeAt _root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program main start exit) (A B n : ℕ) (r : Record) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=start) (pointer : s.natReg 2850=A) (bound : WordBound B s)
 (bank : Printed A r.data s) (marker : r.opcode=2 ∨ r.opcode=6)
 (good : WellFormed r) (extent : A+r.data.length≤B)
 (width : r.width+1≤B) (code : start+_root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program.length≤B) (ret : exit≤B) : ∃u,
 BoundedRuns main n x B s (headCost r+2) u ∧ u.pc=exit ∧
 u.natReg 2850=A+r.data.length ∧ Frame s u := by
 have localCode:_root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program.length≤B:=
   (Nat.le_add_left _ _).trans code
 have small:54≤B:=by
   simpa only [_root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program_length] using localCode

 obtain ⟨u,run,up,done,fr⟩:=UniformFixedNetworkMarkerMachine.execution A B n r x (setPC s 0) rfl pointer
   (changePC_bound B s 0 bound (by omega)) bank marker good extent width small
 have placed:=UniformBoundedAssembly.boundedExecution_placed link
   code ret run
 have start:UniformAssembly.placed (start) (setPC s 0)=s:=by
   change setPC s (start)=s
   rw [←pc];cases s;rfl
 rw [start] at placed
 refine ⟨setPC u (exit),placed,rfl,done,?_⟩
 exact ⟨fr.natHeap,fr.scalarHeap,fr.scalarReg,fr.outputs,fr.roots,fr.natReg⟩

theorem entry (A B n : ℕ) (r : Record) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=UniformRecursiveSavingProgram.address .marker) (pointer : s.natReg 2850=A) (bound : WordBound B s)
 (bank : Printed A r.data s) (marker : r.opcode=2 ∨ r.opcode=6)
 (good : WellFormed r) (extent : A+r.data.length≤B)
 (width : r.width+1≤B) (code : UniformRecursiveSavingProgram.address .marker+_root_.ExactFourierCircuits.UniformFixedNetworkMarkerMachine.program.length≤B) (ret : UniformRecursiveSavingProgram.address .loop≤B) : ∃u,
 BoundedRuns UniformRecursiveSavingProgram.program n x B s (headCost r+2) u ∧ u.pc=UniformRecursiveSavingProgram.address .loop ∧
 u.natReg 2850=A+r.data.length ∧ Frame s u := by
 exact embedded UniformRecursiveSavingProgram.program (UniformRecursiveSavingProgram.address .marker)
   (UniformRecursiveSavingProgram.address .loop) UniformRecursiveSavingProgram.marker_code
   A B n r x s pc pointer bound bank marker good extent width code ret

end UniformFixedNetworkMarkerMachine

end
end ExactFourierCircuits.UniformRecursiveNativeEntries
