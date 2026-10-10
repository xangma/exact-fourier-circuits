import DFTModelCacheColorRebaseClosed
import DFTModelCacheColorSelectionSource

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheColorRebaseSelected
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheColor (Row)
open DFTModelRecursiveScalarCore
open UniformColoring UniformMatchingAxisTableMachine
noncomputable section
abbrev Input := p w DFTModelCacheColorRebase.Input
abbrev Colored := p DFTModelCacheColorRebase.Input (p DFTModelCacheColor.Input DFTModelCacheColor.Output)
abbrev Ready := p w Colored

def start : Prog false Input Ready := .fork (.atom .fst)
 (.comp (.atom .snd) DFTModelCacheColorRebase.program)
def args : Prog false Ready DFTModelCacheColorSelection.Input := .fork (.atom .fst)
 (.fork (.comp (.atom .snd) (.comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))))
  (.comp (.atom .snd) (.comp (.atom .snd) (.comp (.atom .snd) (.atom .snd)))))
def finish : Prog false Ready (p Ready (Ty.a Row)) :=
 .fork (.atom .id) (.comp args DFTModelCacheColorSelection.program)
/-- Compute native colors once in local coordinates, then compact the ORIGINAL
physical rows. No initialized state, colors or selected rows are inputs. -/
def program : Prog false Input (p Ready (Ty.a Row)) := .comp start finish

def colored (A r:ℕ) (z:Tape Row.T) : Colored.T :=
 (run DFTModelCacheColorRebase.program (A,(r,z))).val
def selectionInput (c A r:ℕ) (z:Tape Row.T) : DFTModelCacheColorSelection.Input.T :=
 (c,(z,(colored A r z).2.2.2))

attribute [local irreducible] Code.run DFTModelCacheColorRebase.program
 DFTModelCacheColorSelection.program

theorem paired_comp_run {s t u:Ty} (g:Prog false t u) (a:s.T) (b:t.T) :
 run (.fork (.atom .fst) (.comp (.atom .snd) g)) (a,b)=
 ⟨(a,(run g b).val),(run g b).work+4,(run g b).peak,(run g b).valid⟩ := by
 simp only [fork_run,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay,
 zero_max,max_zero,true_and,and_true]
 congr 1
 omega

theorem start_run (c A r:ℕ) (z:Tape Row.T) : run start (c,(A,(r,z)))=
 ⟨(c,colored A r z),(run DFTModelCacheColorRebase.program (A,(r,z))).work+4,
 (run DFTModelCacheColorRebase.program (A,(r,z))).peak,
 (run DFTModelCacheColorRebase.program (A,(r,z))).valid⟩ :=
 paired_comp_run (s:=w) DFTModelCacheColorRebase.program c (A,(r,z))

theorem args_run (y:Ready.T) : run args y=
 ⟨(y.1,(y.2.1.2.2,y.2.2.2.2)),17,0,True⟩ := by
 simp [args,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

theorem args_value (c A r:ℕ) (z:Tape Row.T) :
 (run args (c,colored A r z)).val=selectionInput c A r z := by
 rw [args_run]
 have original:=congrArg (fun b=>b.val.1) (DFTModelCacheColorRebase.program_run A r z)
 change (colored A r z).1=(A,(r,z)) at original
 change (c,((colored A r z).1.2.2,(colored A r z).2.2.2))=_
 rw [original]
 rfl

theorem finish_run (y:Ready.T) : run finish y=
 ⟨(y,(run DFTModelCacheColorSelection.program (run args y).val).val),
 (run DFTModelCacheColorSelection.program (run args y).val).work+20,
 (run DFTModelCacheColorSelection.program (run args y).val).peak,
 (run DFTModelCacheColorSelection.program (run args y).val).valid⟩ := by
 rw [finish,DFTModelCacheColorRebase.retained_comp_run,args_run]
 simp only [zero_max,true_and]
 congr 1
 omega

attribute [local irreducible] start finish args program

theorem staged_runs {s t u:Ty} (f:Prog false s t) (g:Prog false t u) (x:s.T)
 (a:t.T) (b:u.T) (w1 w2 p1 p2:ℕ) (v1 v2:Prop)
 (hf:run f x=⟨a,w1+4,p1,v1⟩) (hg:run g a=⟨b,w2+20,p2,v2⟩) :
 run (.comp f g) x=⟨b,w1+w2+25,max p1 p2,v1∧v2⟩ := by
 rw [comp_run,hf]
 simp only [Bill.pass,Bill.pay]
 rw [hg]
 simp only [max_zero]
 congr 1
 omega

theorem program_run (c A r:ℕ) (z:Tape Row.T) : run program (c,(A,(r,z)))=
 ⟨((c,colored A r z),(run DFTModelCacheColorSelection.program (selectionInput c A r z)).val),
 (run DFTModelCacheColorRebase.program (A,(r,z))).work+
  (run DFTModelCacheColorSelection.program (selectionInput c A r z)).work+25,
 max (run DFTModelCacheColorRebase.program (A,(r,z))).peak
  (run DFTModelCacheColorSelection.program (selectionInput c A r z)).peak,
 (run DFTModelCacheColorRebase.program (A,(r,z))).valid ∧
  (run DFTModelCacheColorSelection.program (selectionInput c A r z)).valid⟩ := by
 rw [program]
 exact staged_runs start finish (c,(A,(r,z))) _ _ _ _ _ _ _ _ (start_run c A r z)
  (by
   have same:=args_value c A r z
   have h:=finish_run (c,colored A r z)
   rw [same] at h
   exact h)

def workBound (r M:ℕ) : ℕ := DFTModelCacheColorRebase.workBound r M+
 DFTModelCacheColorSelection.workBudget M+25

/-- Matching uses the physical radix R explicitly. It is not equated with the
local endpoint bound r. Each selected row retains its physical coefficient word. -/
theorem specification {M:ℕ} (c A r R n:ℕ) (x:Fin n→ℂ) (z:Tape Row.T)
 (E:Fin M→Edge) (physical:DFTModelCacheColor.Rows (DFTModelCacheColorRebase.shiftedEdges A E) z)
 (localRange:InRange r E) (physicalRange:InRange R (DFTModelCacheColorRebase.shiftedEdges A E))
 (degree:DegreeBound (DFTModelCacheColorRebase.shiftedEdges A E) 6) :
 let selected:=DFTModelCacheColorSelection.selectedEdges (selectionInput c A r z)
  (DFTModelCacheColorRebase.shiftedEdges A E) physical.length
 (run program (c,(A,(r,z)))).valid ∧
 (run program (c,(A,(r,z)))).work≤workBound r z.len ∧
 (run program (c,(A,(r,z)))).val.1.2.1=(A,(r,z)) ∧
 DFTModelCacheMatchingNat.Rows selected (run program (c,(A,(r,z)))).val.2 ∧
 Matching selected ∧ InRange R selected := by
 dsimp only
 have proper:=DFTModelCacheColorRebase.degree_six A r n x z E physical localRange degree
 have selected:=DFTModelCacheColorSelection.selected_matching c R z (colored A r z).2.2.2
  (DFTModelCacheColorRebase.shiftedEdges A E) physical physicalRange proper.2.2.2.2
 obtain ⟨_,_,_,_,_,_,original,_,_,work,_⟩:=
  DFTModelCacheColorRebase.execution A r n x z E physical localRange
 have choose:=DFTModelCacheColorSelection.program_work (selectionInput c A r z)
 rw [program_run]
 refine ⟨⟨proper.1,DFTModelCacheColorSelection.program_valid _⟩,?_,original,
  selected.1,selected.2.1,selected.2.2⟩
 change (run DFTModelCacheColorRebase.program (A,(r,z))).work+
  (run DFTModelCacheColorSelection.program (selectionInput c A r z)).work+25≤
  DFTModelCacheColorRebase.workBound r z.len+
  DFTModelCacheColorSelection.workBudget z.len+25
 change (run DFTModelCacheColorSelection.program (selectionInput c A r z)).work≤
  DFTModelCacheColorSelection.workBudget z.len at choose
 omega

/-- A fixed local polynomial; no term depends on physical base A or radix R. -/
theorem polynomial_work (r M:ℕ) : workBound r M≤50002000*(r+M+1)^3 := by
 have color:=DFTModelCacheColor.polynomial_work r M
 have select:=DFTModelCacheColorSelection.workBudget_polynomial M
 let extent:=r+M+1
 have positive:1≤extent := by dsimp [extent];omega
 have hm:M+1≤extent := by dsimp [extent];omega
 have square:(M+1)^2≤extent^2 := Nat.pow_le_pow_left hm 2
 have cube:extent^2≤extent^3 := by nlinarith [Nat.mul_le_mul_left (extent^2) positive]
 have linear:extent≤extent^2 := by nlinarith [Nat.mul_le_mul_left extent positive]
 change workBound r M≤50002000*extent^3
 change DFTModelCacheColor.workBound r M≤50000000*extent^3 at color
 unfold workBound DFTModelCacheColorRebase.workBound
 nlinarith

/-- Physical words may bound peaks but never dense allocations or work. -/
theorem peak {M:ℕ} (c A r n B:ℕ) (x:Fin n→ℂ) (z:Tape Row.T)
 (E:Fin M→Edge) (physical:DFTModelCacheColor.Rows (DFTModelCacheColorRebase.shiftedEdges A E) z)
 (localRange:InRange r E) (hB:5≤B)
 (words:DFTModelCacheHeight.Words DFTModelCacheColorSelection.Input B (selectionInput c A r z)) :
 (run program (c,(A,(r,z)))).peak≤ max (DFTModelCacheColorRebase.peakBound r z.len)
  (B^DFTModelCacheColorSelection.wordDegree) := by
 obtain ⟨_,_,_,_,_,_,_,_,_,_,bound⟩:=
  DFTModelCacheColorRebase.execution A r n x z E physical localRange
 have select:=DFTModelCacheColorSelection.program_bound (selectionInput c A r z) B hB words
 rw [program_run]
 exact max_le_max bound select.2.2

end
end ExactFourierCircuits.DFTModelCacheColorRebaseSelected
