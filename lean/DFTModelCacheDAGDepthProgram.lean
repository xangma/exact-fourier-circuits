import ModelEquivalenceInterpreter
import UniformDAGDepthMachine

set_option autoImplicit false

/-! Actual typed Code for the sequential depth recurrence of a runtime DAG.
Every update constructs and charges a fresh tape. -/
namespace ExactFourierCircuits.DFTModelCacheDAGDepth
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Row3 := p w (p w w)
abbrev Input := p w (Ty.a Row3)
abbrev Cursor := p Input (p w (Ty.a w))

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def inputCount : Prog false Input w := .atom .fst
def gateCount : Prog false Input w := .comp (.atom .snd) (.atom .len)
def span : Prog false Input w := nat .add (nat .add inputCount (.atom (.lit 1))) gateCount
def initialTape : Prog false Input (Ty.a w) := .tab span (.atom (.lit 0))
def old : Prog false Cursor (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def ordinal : Prog false Cursor w := .comp (.atom .snd) (.atom .fst)
def row : Prog false Cursor Row3 :=
  .comp (.fork (.comp (.atom .fst) (.atom .snd)) ordinal) (.atom .look)
def opcode : Prog false Cursor w := .comp row (.atom .fst)
def left : Prog false Cursor w := .comp row (.comp (.atom .snd) (.atom .fst))
def right : Prog false Cursor w := .comp row (.comp (.atom .snd) (.atom .snd))
def leftDepth : Prog false Cursor w := .comp (.fork old left) (.atom .look)
def rightDepth : Prog false Cursor w := .comp (.fork old right) (.atom .look)
def maximum : Prog false (p w w) w :=
  .ifz (.atom (.int .lt)) (.atom .fst) (.atom .snd)
def baseDepth : Prog false Cursor w :=
  .ifz (nat .lt opcode (.atom (.lit 2))) leftDepth
    (.comp (.fork leftDepth rightDepth) maximum)
def newDepth : Prog false Cursor w := nat .add baseDepth (.atom (.lit 1))
def target : Prog false Cursor w :=
  nat .add (nat .add (.comp (.atom .fst) inputCount) (.atom (.lit 1))) ordinal
def step : Prog false Cursor (Ty.a w) :=
  .comp (.fork (.fork old target) newDepth) (ModelEquivalenceInterpreter.update w)
def program : Prog false Input (Ty.a w) := .loop gateCount initialTape step

def rowValue (q : Row3.T) (d : Tape ℕ) : ℕ :=
  (if q.1 < 2 then max (d.look q.2.1 0) (d.look q.2.2 0) else d.look q.2.1 0)+1
def encode (q : UniformDAGDepthMachine.Row) : Row3.T := (q.opcode,(q.left,q.right))
def rowsTape (qs : List UniformDAGDepthMachine.Row) : Tape Row3.T :=
  ⟨qs.length,fun i => encode qs[i]⟩

theorem maximum_run (u v : ℕ) : run maximum (u,v)=
    ⟨max u v,3,(if u < v then 1 else 0),True⟩ := by
  by_cases h : u < v
  · simp [maximum,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,h,
      max_eq_right (by omega : u ≤ v)]
  · simp [maximum,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,h,
      max_eq_left (by omega : v ≤ u)]

theorem row_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run row ((N,qs),(i,d))=⟨qs.look i (0,(0,0)),9,0,True⟩ := by
  simp [row,ordinal,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem leftDepth_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run leftDepth ((N,qs),(i,d))=⟨d.look (qs.look i (0,(0,0))).2.1 0,19,0,True⟩ := by
  simp [leftDepth,old,left,row,ordinal,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem rightDepth_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run rightDepth ((N,qs),(i,d))=⟨d.look (qs.look i (0,(0,0))).2.2 0,19,0,True⟩ := by
  simp [rightDepth,old,right,row,ordinal,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Ty.blank]

theorem target_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run target ((N,qs),(i,d))=⟨N+1+i,13,N+1+i,True⟩ := by
  simp [target,nat,inputCount,ordinal,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem newDepth_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run newDepth ((N,qs),(i,d))=
      ⟨rowValue (qs.look i (0,(0,0))) d,
        if (qs.look i (0,(0,0))).1 < 2 then 63 else 39,
        max 2 (rowValue (qs.look i (0,(0,0))) d),True⟩ := by
  rw [newDepth]
  simp only [nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
  simp only [baseDepth,nat,opcode,row,ordinal,leftDepth,old,left,rightDepth,right,maximum,
    Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,Ty.blank]
  by_cases h : (qs.look i (0,(0,0))).1 < 2
  · by_cases hd : d.look (qs.look i (0,(0,0))).2.1 0 < d.look (qs.look i (0,(0,0))).2.2 0
    · simp [h,hd,rowValue,max_eq_right (by omega : d.look (qs.look i (0,(0,0))).2.1 0 ≤ d.look (qs.look i (0,(0,0))).2.2 0)]
    · simp [h,hd,rowValue,max_eq_left (by omega : d.look (qs.look i (0,(0,0))).2.2 0 ≤ d.look (qs.look i (0,(0,0))).2.1 0)]
  · simp [h,rowValue]

attribute [local irreducible] ModelEquivalenceInterpreter.update

theorem step_run (N i : ℕ) (qs : Tape Row3.T) (d : Tape ℕ) :
    run step ((N,qs),(i,d))=
      ⟨d.set (N+1+i) (rowValue (qs.look i (0,(0,0))) d),
        (run (ModelEquivalenceInterpreter.update w)
          ((d,N+1+i),rowValue (qs.look i (0,(0,0))) d)).work+
          (if (qs.look i (0,(0,0))).1 < 2 then 82 else 58),
        max (max (N+1+i) (max 2 (rowValue (qs.look i (0,(0,0))) d)))
          (run (ModelEquivalenceInterpreter.update w)
            ((d,N+1+i),rowValue (qs.look i (0,(0,0))) d)).peak,True⟩ := by
  rw [step]
  change ((run (.fork (.fork old target) newDepth) ((N,qs),(i,d))).pass
    (fun x=>run (ModelEquivalenceInterpreter.update w) x)).pay 1 0 = _
  simp only [run,Code.run]
  have ht:=target_run N i qs d
  have hn:=newDepth_run N i qs d
  dsimp only [run] at ht hn
  rw [ht,hn]
  simp only [old,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,max_zero,zero_max]
  have hv:=ModelEquivalenceInterpreter.update_value w d (N+1+i) (rowValue (qs.look i (0,(0,0))) d)
  have hb:=ModelEquivalenceInterpreter.update_valid w d (N+1+i) (rowValue (qs.look i (0,(0,0))) d)
  dsimp only [run] at hv hb
  rw [hv]
  simp only [hb,true_and]
  by_cases h:(qs.look i (0,(0,0))).1 < 2 <;> simp [h] <;> omega

end
end ExactFourierCircuits.DFTModelCacheDAGDepth
