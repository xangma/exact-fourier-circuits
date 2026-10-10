import DFTModelCacheSpectrumForestProvenance

set_option autoImplicit false

/-! Paper E, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a,
§3.1–3.5, pp.13–18 (especially §3.12–3.14): one charged traversal
followed by actual preparation of every returned rectangle's seven-block
shared bank. This is a spectrum forest, not a factor or calendar cache. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumForest
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
attribute [local irreducible] DFTModelCacheTraversal.program
  DFTModelCacheRectanglePreparation.program

abbrev Input := p (p w w) (p w sc)
abbrev Seed := p Input DFTModelCacheTraversal.Output
abbrev Cell := p Seed w
abbrev Output := p (Ty.a DFTModelCacheTraversal.Record7)
  (Ty.a DFTModelCacheRectanglePreparation.Output)

def seed : Prog false Input Seed :=
  .fork (.atom .id) (.comp (.atom .fst) DFTModelCacheTraversal.program)
def rows : Prog false Seed (Ty.a DFTModelCacheDescriptor.Row7) :=
  .comp (.atom .snd) (.atom .snd)
def rowCount : Prog false Seed w := .comp rows (.atom .len)
def row : Prog false Cell DFTModelCacheDescriptor.Row7 :=
  .comp (.fork (.comp (.atom .fst) rows) (.atom .snd)) (.atom .look)
def radix : Prog false Cell w :=
  .comp (.atom .fst) (.comp (.atom .fst) (.comp (.atom .fst) (.atom .fst)))
def master : Prog false Cell (p w sc) :=
  .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def argument : Prog false Cell DFTModelCacheRectanglePreparation.Input :=
  .fork (.fork radix row) master
def cell : Prog false Cell DFTModelCacheRectanglePreparation.Output :=
  .comp argument DFTModelCacheRectanglePreparation.program
def banks : Prog false Seed (Ty.a DFTModelCacheRectanglePreparation.Output) :=
  .tab rowCount cell
def body : Prog false Seed Output :=
  .fork (.comp (.atom .snd) (.atom .fst)) banks
def program : Prog false Input Output := .comp seed body

theorem cell_run (r o D i : ℕ) (z : ℂ) (forest : DFTModelCacheTraversal.Output.T) :
    run cell ((((r,o),(D,z)),forest),i)=
      (run DFTModelCacheRectanglePreparation.program
        ((r,forest.2.look i DFTModelCacheDescriptor.Row7.blank),(D,z))).pay 24 0 := by
  simp [cell,argument,radix,row,master,rows,run,Code.run,Atom.run,
    Bill.one,Bill.pass,Bill.pay]
  omega

theorem program_run (r o D : ℕ) (z : ℂ) :
    run program ((r,o),(D,z))=
      ((run DFTModelCacheTraversal.program (r,o)).pass (fun forest=>
        (Bill.tab forest.2.len DFTModelCacheRectanglePreparation.Output.blank (fun i=>
          run cell ((((r,o),(D,z)),forest),i))).pass
            (fun bs=>Bill.one (forest.1,bs)) )).pay 14
              (run DFTModelCacheTraversal.program (r,o)).val.2.len := by
  simp [program,seed,body,banks,rowCount,rows,run,Code.run,Atom.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  constructor
  · omega
  · ac_rfl

end
end ExactFourierCircuits.DFTModelCacheSpectrumForest
