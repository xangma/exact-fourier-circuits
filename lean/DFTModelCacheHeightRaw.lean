import DFTModelCacheHeightSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeightRaw
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelRecursiveScalarCore
noncomputable section
abbrev Config := p w (p w (p w (p w w)))
abbrev Input := p Config (p w w)
abbrev Context := p DFTModelCacheHeight.Params DFTModelCacheBucketRaw.Output
abbrev Output := p DFTModelCacheBucketRaw.Output (Ty.a DFTModelCacheHeight.Row)

def prepare : Prog false Input Context :=
 .fork (.fork (.comp (.atom .snd) (.atom .snd)) (.atom .fst))
  (.comp (.atom .snd) DFTModelCacheBucketRaw.program)
def argument : Prog false Context DFTModelCacheHeight.Input :=
 .fork (.atom .fst)
  (.fork (.comp (.atom .snd) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))))
   (.comp (.atom .snd) (.atom .snd)))
def adapter : Prog false Context Output :=
 .fork (.atom .snd) (.comp argument DFTModelCacheHeight.program)
def program : Prog false Input Output := .comp prepare adapter
attribute [local irreducible] DFTModelCacheBucketRaw.program DFTModelCacheHeight.program

def selectedInput (config:Config.T) (e:ℕ) (v:DFTModelCacheBucketRaw.Output.T):
 DFTModelCacheHeight.Input.T := ((e,config),(v.1.2.2,v.2))

theorem argument_value (params:DFTModelCacheHeight.Params.T) (v:DFTModelCacheBucketRaw.Output.T):
 (run argument (params,v)).val=(params,(v.1.2.2,v.2)) := rfl

theorem adapter_run (params:DFTModelCacheHeight.Params.T) (v:DFTModelCacheBucketRaw.Output.T):
 run adapter (params,v)=
 let h:=run DFTModelCacheHeight.program (params,(v.1.2.2,v.2))
 ⟨(v,h.val),h.work+16,h.peak,h.valid⟩ := by
 simp only [adapter,argument,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,
  true_and,and_true,zero_max,max_zero]
 congr 1
 omega

theorem program_run (config:Config.T) (a e:ℕ):
 run program (config,(a,e))=
 let b:=run DFTModelCacheBucketRaw.program (a,e)
 let h:=run DFTModelCacheHeight.program (selectedInput config e b.val)
 ⟨(b.val,h.val),b.work+h.work+25,max b.peak h.peak,b.valid ∧ h.valid⟩ := by
 rw [program,comp_run]
 simp only [prepare,fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
   true_and,and_true,zero_max,max_zero]
 rw [adapter_run]
 dsimp only [selectedInput]
 congr 1
 omega

abbrev dag:=DFTModelCacheBucketRaw.dag

theorem source_fields (a e:ℕ) (u:UniformMachine.State) (ticks:ℕ)
 (source:DFTModelCacheTopology.Result a e u ticks):
 DFTModelCacheHeight.Fields (dag a e).size
  (UniformCrossShearTableMachine.rowAt (dag a e).program)
  (run DFTModelCacheTopology.program (a,e)).val.2.2 := by
 have size:(dag a e).size=DFTModelCacheBucketRaw.count a e:=DFTModelCacheTopology.typed_count _ _ _
  (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2
 have copied:DFTModelCacheDAGDepth.CopiedTopology (dag a e).size
  (DFTModelCacheTopology.D (DFTModelCacheTopology.exponent a e))
  (run DFTModelCacheTopology.program (a,e)).val.2.2 u:=by
  simpa only [size,DFTModelCacheBucketRaw.count,DFTModelCacheTopologyDepth.count] using source.copied
 exact DFTModelCacheHeight.fields_of_encoded (dag a e).program _ u source.encoded copied

/-- Raw rectangle extents internally generate topology, exact depths, stable
order and directory before selecting this requested height. -/
theorem program_value (a e A C Z P d:ℕ) (enabled:Bool)
 (height:d≤8*DFTModelCacheTopology.exponent a e+6):
 (run program ((A,(C,(P,(d,if enabled then 1 else 0)))),(a,e))).val.2=
 DFTModelCacheHeight.rowTape
  ((UniformCrossDepthReplayPreparation.bucket (dag a e).program enabled d).map
   (UniformCrossShearTableMachine.shiftedRow A
    (UniformCrossShearTableMachine.locations
     (UniformToeplitzCrossDAG.bankSize (DFTModelCacheTopology.exponent a e)) C Z P))) := by
 obtain ⟨u,ticks,source⟩:=DFTModelCacheTopology.execution_values a e
 rw [program_run]
 dsimp only
 rw [DFTModelCacheBucketRaw.program_value]
 change (run DFTModelCacheHeight.program
  (DFTModelCacheHeight.nativeInput (dag a e).program A C P d enabled
    (run DFTModelCacheTopology.program (a,e)).val.2.2)).val=_
 apply DFTModelCacheHeight.native_value
 · exact height.trans (UniformCrossDepthReplayPreparation.cross_height_le_size _ _ _
    (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2)
 · exact source_fields a e u ticks source
 · exact UniformCrossShearTableMachine.cross_good _ _ _
    (DFTModelCacheTopology.dimensions_fit a e).1 (DFTModelCacheTopology.dimensions_fit a e).2

end
end ExactFourierCircuits.DFTModelCacheHeightRaw
