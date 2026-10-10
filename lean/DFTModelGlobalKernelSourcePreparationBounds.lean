import DFTModelGlobalKernelSourcePreparation
import DFTModelGlobalKernelSourceLower
set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelGlobalKernelSource
open UniformMachine UniformAssembly
noncomputable section

/-- Expose the lower bound for the SAME prefix witness, using deterministic
identification with the strengthened unchanged original constructor. -/
theorem Prefix.gather_lower {F n i ticks : ℕ} (c : Context F) (v : ℕ→Fin c.packing.volume→Scalar)
 (x : Fin n→ℂ) (s u : State) (h : UniformConditionalKernelLayout.Ready c i v s)
 (hi : i<(states c).length) (code : 372≤c.metadata.B) (pc : s.pc=0)
 (p : Prefix (i:=i) c v x s u ticks) : DFTModelGlobalKernelSourceLower.gatherCost W (states c)≤ticks := by
 have wb : WordBound c.metadata.B s := by
  cases p.actual with
  | halt b _=>exact b
  | next b _ _=>exact b
 obtain ⟨u',ticks',run,_cheap,_up,_child,_pow,_grouped,_filled,_table,_count,_dir,_fresh,
  _saved,_out,_roots,_scalar,_nat,_kept,lower⟩ := DFTModelGlobalKernelSourceLower.execution
  c.packing c.physical c.physicalVolume c.physicalLength c.metadata c.gather v x s
  c.packingB c.gatherB c.packingVolume c.gatherVolume c.gatherSource c.metadataLength
  h.packing h.banks c.widthsBelow c.permutationsBelow c.widthsMetadata c.rowsMetadata
  c.entry c.directory code h.count h.axes h.metadataRows h.suffix h.stack h.directory
  h.batchDirectory h.childBank h.native h.volume h.source hi h.ordinal h.frontier pc wb
 have equal := (run.executes.deterministic p.actual.executes).1
 subst ticks'
 exact lower
end
end ExactFourierCircuits.DFTModelGlobalKernelSource
