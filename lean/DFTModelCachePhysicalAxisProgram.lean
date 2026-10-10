import DFTModelCachePhysicalAxisWidths

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCachePhysicalAxis
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Axis := p w (p (Ty.a w) (Ty.a w))
abbrev Output := p Axis DFTModelGlobalCompactPools.Pool
abbrev Input := DFTModelCacheMatchingProduced.Input
abbrev Produced := DFTModelCacheMatchingProduced.Output

def original : Prog false Produced Input :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst)))
def radix : Prog false Produced w := .comp original (.atom .fst)
def count : Prog false Produced w :=
  .comp original (.comp DFTModelCacheMatchingProduced.rawRows (.atom .len))
def widthArgument : Prog false Produced WidthInput := .fork radix count
def permutation : Prog false Produced (Ty.a w) :=
  .comp (.atom .fst) DFTModelCacheMatchingProduced.permutation
def axis : Prog false Produced Axis :=
  .fork radix (.fork (.comp widthArgument widths) permutation)
def pool : Prog false Produced DFTModelGlobalCompactPools.Pool :=
  .fork radix (.atom .snd)
def publish : Prog false Produced Output := .fork axis pool
/-- The genuine matching/coefficient/factor producer occurs exactly once. -/
def program : Prog false Input Output := .comp DFTModelCacheMatchingProduced.program publish

attribute [local irreducible] widths DFTModelCacheMatchingProduced.program

theorem publish_run (z:Produced.T) : run publish z=
    ⟨((z.1.1.1.1.1,((run widths (z.1.1.1.1.1,z.1.1.1.1.2.2.2.len)).val,z.1.1.2.2)),
        (z.1.1.1.1.1,z.2)),
      (run widths (z.1.1.1.1.1,z.1.1.1.1.2.2.2.len)).work+56,
      max z.1.1.1.1.2.2.2.len (run widths (z.1.1.1.1.1,z.1.1.1.1.2.2.2.len)).peak,
      (run widths (z.1.1.1.1.1,z.1.1.1.1.2.2.2.len)).valid⟩ := by
  simp [publish,axis,pool,radix,count,widthArgument,permutation,original,
    DFTModelCacheMatchingProduced.rawRows,DFTModelCacheMatchingProduced.permutation,
    run,Code.run,Atom.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  omega

theorem program_run (x:Input.T) : run program x=
    ((run DFTModelCacheMatchingProduced.program x).pass (fun z=>run publish z)).pay 1 0 := rfl

theorem program_value (x:Input.T) : (run program x).val=
    ((x.1,((run widths (x.1,x.2.2.2.len)).val,
      (run DFTModelCacheMatchingNat.program (x.1,x.2.2.2)).val.2)),
      (x.1,(run DFTModelCacheMatchingProduced.program x).val.2)) := by
  rw [program_run]
  change (run publish (run DFTModelCacheMatchingProduced.program x).val).val=_
  rw [publish_run]
  simp only [DFTModelCacheMatchingProduced.retained,DFTModelCacheMatchingProduced.readyValue,
    DFTModelCacheMatchingProduced.matchedValue,DFTModelCacheMatchingProduced.seedValue]

theorem program_work (x:Input.T) : (run program x).work=
    (run DFTModelCacheMatchingProduced.program x).work+13*(x.1-x.2.2.2.len)+65 := by
  rw [program_run]
  change (run DFTModelCacheMatchingProduced.program x).work+
    (run publish (run DFTModelCacheMatchingProduced.program x).val).work+1=_
  rw [publish_run]
  simp only [DFTModelCacheMatchingProduced.retained,DFTModelCacheMatchingProduced.readyValue,
    DFTModelCacheMatchingProduced.matchedValue,DFTModelCacheMatchingProduced.seedValue]
  rw [widths_work]
  omega

theorem program_valid (x:Input.T) (valid:(run DFTModelCacheMatchingProduced.program x).valid) :
    (run program x).valid := by
  rw [program_run]
  change (run DFTModelCacheMatchingProduced.program x).valid ∧ _
  refine ⟨valid,?_⟩
  change (run publish (run DFTModelCacheMatchingProduced.program x).val).valid
  rw [publish_run]
  exact widths_valid _ _

theorem program_peak (x:Input.T) : (run program x).peak ≤
    max (run DFTModelCacheMatchingProduced.program x).peak
      (max x.2.2.2.len (max 2 (x.1-x.2.2.2.len))) := by
  rw [program_run]
  change max (max (run DFTModelCacheMatchingProduced.program x).peak
    (run publish (run DFTModelCacheMatchingProduced.program x).val).peak) 0≤_
  rw [publish_run]
  simp only [DFTModelCacheMatchingProduced.retained,DFTModelCacheMatchingProduced.readyValue,
    DFTModelCacheMatchingProduced.matchedValue,DFTModelCacheMatchingProduced.seedValue]
  exact max_le (max_le_max_left _ (max_le_max_left _ (widths_peak _ _)))
    (Nat.zero_le _)

end
end ExactFourierCircuits.DFTModelCachePhysicalAxis
