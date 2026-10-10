import DFTModelCacheTraversalTape
import UniformSectorPacking

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelGlobalSectorPreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section

abbrev Axis := p w (p (Ty.a w) (Ty.a w))
abbrev Block := p w (p w w)
abbrev Digit := p w (p w (p w w))
abbrev PreparedAxis := p w (p (Ty.a Block) (Ty.a Digit))
abbrev FindNode := p w (p w (Ty.a w))
abbrev Found := p w w
abbrev SumNode := p w (Ty.a w)

def nat {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
 .comp (.fork f g) (.atom (.int op))

def sumNext : Prog false SumNode SumNode :=
 .fork (nat .add (.atom .fst) (.atom (.lit 1))) (.atom .snd)
def sumCurrent : Prog false SumNode w := .comp (.fork (.atom .snd) (.atom .fst)) (.atom .look)
def sumBody : Code false (some (SumNode,w)) SumNode w :=
 .comp (.fork (.importClosed sumCurrent) (.comp (.importClosed sumNext) .call)) (.atom (.int .add))
def sumProgram : Prog false (p w (Ty.a w)) w :=
 .comp (.fork (.atom .fst) (.fork (.atom (.lit 0)) (.atom .snd)))
   (.descend (.atom (.lit 0)) sumBody)

def sumValue : ℕ → ℕ → Tape ℕ → ℕ
 | 0,_,_ => 0
 | k+1,i,ws => ws.look i 0 + sumValue k (i+1) ws

theorem sumNext_run (i : ℕ) (ws : Tape ℕ) :
 run sumNext (i,ws)=⟨(i+1,ws),7,i+1,True⟩ := by
 simp [sumNext,nat,run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem sumBody_run (h : Handler (some (SumNode,w))) (i : ℕ) (ws : Tape ℕ) :
 sumBody.run h (i,ws)=
   ((h (i+1,ws)).pass (fun v=>Bill.word (ws.look i 0+v))).pay 18 (i+1) := by
 simp [sumBody,sumCurrent,sumNext,nat,Code.run,
   Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
; omega

attribute [local irreducible] sumBody

def sumPeak : ℕ → ℕ → Tape ℕ → ℕ
 | 0,_,_ => 0
 | k+1,i,ws => max (k+1) (max (i+1) (max (sumPeak k (i+1) ws) (sumValue (k+1) i ws)))

theorem sum_depth (k i : ℕ) (ws : Tape ℕ) :
 depthRun (run (.atom (.lit 0) : Prog false SumNode w)) sumBody.run k (i,ws)=
   ⟨sumValue k i ws,2+20*k,sumPeak k i ws,True⟩ := by
 induction k generalizing i with
 | zero => simp [depthRun,run,Code.run,Atom.run,Bill.word,Bill.pay,sumValue,sumPeak]
 | succ k ih =>
   rw [depthRun,sumBody_run,ih]
   simp only [Bill.pass,Bill.pay,Bill.word,sumValue,sumPeak,true_and]
   congr 1; omega

theorem sumProgram_run (k : ℕ) (ws : Tape ℕ) :
 run sumProgram (k,ws)=⟨sumValue k 0 ws,20*k+9,
   max k (sumPeak k 0 ws),True⟩ := by
 simp only [sumProgram,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
 rw [show depthRun (fun _ : SumNode.T=>⟨0,1,0,True⟩) sumBody.run k (0,ws)=_ from sum_depth k 0 ws]
 simp only [true_and]
 congr 1 <;> omega

def findWidth : Prog false FindNode w :=
 .comp (.fork (.comp (.atom .snd) (.atom .snd)) (.atom .fst)) (.atom .look)
def findLeft : Prog false FindNode w := .comp (.atom .snd) (.atom .fst)
def findNext : Prog false FindNode FindNode :=
 .fork (nat .add (.atom .fst) (.atom (.lit 1)))
   (.fork (nat .sub findLeft findWidth) (.comp (.atom .snd) (.atom .snd)))
def findBody : Code false (some (FindNode,Found)) FindNode Found :=
 .ifz (.importClosed (nat .lt findLeft findWidth))
   (.comp (.importClosed findNext) .call)
   (.importClosed (.fork findWidth findLeft))
def findProgram : Prog false (p w (Ty.a w)) Found :=
 .comp (.fork (.comp (.atom .snd) (.atom .len))
   (.fork (.atom (.lit 0)) (.atom .id)))
   (.descend (.fork (.atom (.lit 0)) (.atom (.lit 0))) findBody)

def findValue : ℕ → ℕ → ℕ → Tape ℕ → ℕ × ℕ
 | 0,_,_,_ => (0,0)
 | k+1,i,j,ws => if j<ws.look i 0 then (ws.look i 0,j)
   else findValue k (i+1) (j-ws.look i 0) ws

theorem findBody_run (h : Handler (some (FindNode,Found))) (i j : ℕ) (ws : Tape ℕ) :
 findBody.run h (i,(j,ws))=
   if j<ws.look i 0 then ⟨(ws.look i 0,j),27,1,True⟩
   else (h (i+1,(j-ws.look i 0,ws))).pay 41 (max (i+1) (j-ws.look i 0)) := by
 by_cases hlt:j<ws.look i 0 <;>
 simp [findBody,findNext,findLeft,findWidth,nat,Code.run,
   Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank,hlt]
; omega

attribute [local irreducible] findBody

theorem find_depth_value (k i j : ℕ) (ws : Tape ℕ) :
 (depthRun (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found))
   findBody.run k (i,(j,ws))).val=findValue k i j ws := by
 induction k generalizing i j with
 | zero => rfl
 | succ k ih =>
   rw [depthRun]
   rw [findBody_run]
   simp only [Bill.pay,findValue]
   split_ifs <;> simp_all

theorem find_depth_valid (k i j : ℕ) (ws : Tape ℕ) :
 (depthRun (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found))
   findBody.run k (i,(j,ws))).valid := by
 induction k generalizing i j with
 | zero => trivial
 | succ k ih =>
   rw [depthRun]
   rw [findBody_run]
   simp only [Bill.pay]
   split_ifs <;> simp_all

theorem find_depth_work (k i j : ℕ) (ws : Tape ℕ) :
 (depthRun (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found))
   findBody.run k (i,(j,ws))).work≤42*k+5 := by
 induction k generalizing i j with
 | zero => simp [depthRun,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Bill.word]
 | succ k ih =>
   rw [depthRun]
   rw [findBody_run]
   simp only [Bill.pay]
   split_ifs
   · norm_num
     omega
   · have hi:=ih (i+1) (j-ws.look i 0)
     simp only at *
     omega

theorem find_depth_peak (k i j : ℕ) (ws : Tape ℕ) :
 (depthRun (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found))
   findBody.run k (i,(j,ws))).peak≤ max (i+k) j := by
 induction k generalizing i j with
 | zero => simp [depthRun,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,Bill.word]
 | succ k ih =>
   rw [depthRun]
   rw [findBody_run]
   simp only [Bill.pay]
   split_ifs
   · dsimp only [Bill.peak]; omega
   · have hi:=ih (i+1) (j-ws.look i 0)
     dsimp only [Bill.peak] at *
     omega

theorem findBase_function :
 run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found)=
   fun _=>⟨(0,0),3,0,True⟩ := by
 funext x
 simp [run,Code.run,Atom.run,Bill.pass,Bill.one,Bill.word]

theorem findProgram_run (j : ℕ) (ws : Tape ℕ) :
 run findProgram (j,ws)=
  (depthRun (run (.fork (.atom (.lit 0)) (.atom (.lit 0)) : Prog false FindNode Found))
    findBody.run ws.len (0,(j,ws))).pay 9 ws.len := by
 rw [findBase_function]
 simp only [findProgram,run,Code.run,Atom.run]
 simp only [Bill.pass,Bill.pay,Bill.one,Bill.word]
 simp only [max_zero,max_self,zero_max,true_and]
 norm_num
 ac_rfl

end
end ExactFourierCircuits.DFTModelGlobalSectorPreparation
