import DFTModelCacheDescriptorLog

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorMapCarry
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

abbrev Row := p w w
abbrev Directory := Ty.a Row
abbrev SearchInput := p Directory w
abbrev SearchState := p SearchInput (p w w)
abbrev SearchPort : Port := some (SearchState,w)
abbrev MidState := p SearchState w
abbrev CarryInput := p w (p w Directory)

def num {s : Ty} {r : Port} (op : NOp)
    (f g : Code false r s w) : Code false r s w :=
  .comp (.fork f g) (.atom (.int op))
def lo {r : Port} : Code false r SearchState w := .comp (.atom .snd) (.atom .fst)
def hi {r : Port} : Code false r SearchState w := .comp (.atom .snd) (.atom .snd)
def width {r : Port} : Code false r SearchState w := num .sub hi lo
def midpoint {r : Port} : Code false r SearchState w :=
  num .add lo (num .div width (.atom (.lit 2)))
def midInput {r : Port} : Code false r MidState SearchInput :=
  .comp (.atom .fst) (.atom .fst)
def midLo {r : Port} : Code false r MidState w := .comp (.atom .fst) lo
def midHi {r : Port} : Code false r MidState w := .comp (.atom .fst) hi
def midTarget {r : Port} : Code false r MidState w := .comp midInput (.atom .snd)
def midDirectory {r : Port} : Code false r MidState Directory :=
  .comp midInput (.atom .fst)
def midStart {r : Port} : Code false r MidState w :=
  .comp (.comp (.fork midDirectory (.atom .snd)) (.atom .look)) (.atom .fst)
def leftState {r : Port} : Code false r MidState SearchState :=
  .fork midInput (.fork midLo (.atom .snd))
def rightState {r : Port} : Code false r MidState SearchState :=
  .fork midInput (.fork (num .add (.atom .snd) (.atom (.lit 1))) midHi)
def searchBase : Prog false SearchState w := lo
def searchBody : Code false SearchPort SearchState w :=
  .ifz width lo
    (.comp (.fork (.atom .id) midpoint)
      (.ifz (num .lt midTarget midStart)
        (.comp rightState .call) (.comp leftState .call)))

def searchAux (fuel : ℕ) (d : Tape (ℕ×ℕ)) (t l h : ℕ) : Bill ℕ :=
  depthRun (run searchBase) (Code.run searchBody) fuel ((d,t),(l,h))
def searchSeed : Prog false SearchInput (p w SearchState) :=
  .fork (num .add (.comp (.atom .fst) (.atom .len)) (.atom (.lit 1)))
    (.fork (.atom .id)
      (.fork (.atom (.lit 0)) (.comp (.atom .fst) (.atom .len))))
def closedSearch : Prog false SearchInput w := .comp searchSeed (.descend searchBase searchBody)

def start (d : Tape (ℕ×ℕ)) (i : ℕ) : ℕ := (d.look i (0,0)).1
def mid (l h : ℕ) : ℕ := l+(h-l)/2

theorem searchAux_stop (f : ℕ) (d : Tape (ℕ×ℕ)) (t l : ℕ) :
    searchAux (f+1) d t l l = ⟨l,14,f+1,True⟩ := by
  simp [searchAux,searchBase,searchBody,width,lo,hi,num,depthRun,
    Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay]

theorem lo_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h : ℕ) :
    Code.run lo handler ((d,t),(l,h))=⟨l,3,0,True⟩ := by
  simp [lo,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem hi_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h : ℕ) :
    Code.run hi handler ((d,t),(l,h))=⟨h,3,0,True⟩ := by
  simp [hi,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
attribute [local irreducible] lo hi

theorem width_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h : ℕ) :
    Code.run width handler ((d,t),(l,h))=⟨h-l,9,h-l,True⟩ := by
  unfold width num
  rw [Code.run,Code.run,hi_run,lo_run]
  simp [Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
attribute [local irreducible] width

theorem midpoint_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h : ℕ) :
    Code.run midpoint handler ((d,t),(l,h))=
      ⟨mid l h,19,max 2 (max (h-l) (mid l h)),True⟩ := by
  simp only [midpoint,num,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,(lo_run (r:=r)),(width_run (r:=r)),mid,max_zero,zero_max,true_and]
  congr 1; omega
attribute [local irreducible] midpoint

theorem midInput_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midInput handler (((d,t),(l,h)),m)=⟨(d,t),3,0,True⟩ := by
  simp [midInput,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
theorem midLo_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midLo handler (((d,t),(l,h)),m)=⟨l,5,0,True⟩ := by
  simp only [midLo,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,(lo_run (r:=r)),max_zero,true_and]
theorem midHi_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midHi handler (((d,t),(l,h)),m)=⟨h,5,0,True⟩ := by
  simp only [midHi,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,(hi_run (r:=r)),max_zero,true_and]
attribute [local irreducible] midInput midLo midHi

theorem midTarget_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midTarget handler (((d,t),(l,h)),m)=⟨t,5,0,True⟩ := by
  simp only [midTarget,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,(midInput_run (r:=r)),max_zero,true_and]
theorem midDirectory_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midDirectory handler (((d,t),(l,h)),m)=⟨d,5,0,True⟩ := by
  simp only [midDirectory,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,(midInput_run (r:=r)),max_zero,true_and]
attribute [local irreducible] midTarget midDirectory

theorem midStart_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run midStart handler (((d,t),(l,h)),m)=⟨start d m,11,0,True⟩ := by
  simp only [midStart,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay,(midDirectory_run (r:=r)),max_zero,true_and]
  rfl
attribute [local irreducible] midStart

theorem leftState_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run leftState handler (((d,t),(l,h)),m)=⟨((d,t),(l,m)),11,0,True⟩ := by
  simp only [leftState,Code.run,Atom.run,Bill.one,Bill.pass,(midInput_run (r:=r)),(midLo_run (r:=r)),max_zero,true_and]
theorem rightState_run {r : Port} (handler : Handler r) (d : Tape (ℕ×ℕ)) (t l h m : ℕ) :
    Code.run rightState handler (((d,t),(l,h)),m)=⟨((d,t),(m+1,h)),15,max 1 (m+1),True⟩ := by
  simp only [rightState,num,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,(midInput_run (r:=r)),(midHi_run (r:=r)),zero_max,max_zero,true_and]
attribute [local irreducible] leftState rightState

theorem searchBody_left (handler : SearchState.T → Bill ℕ)
    (d : Tape (ℕ×ℕ)) (t l h : ℕ)
    (hlh : l<h) (ht : t<start d (mid l h)) :
    Code.run searchBody handler ((d,t),(l,h)) =
      (handler ((d,t),(l,mid l h))).pay 65
        (max (max 2 (h-l)) (mid l h)) := by
  have hn : h-l≠0 := by omega
  simp only [searchBody,num,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,(width_run (r:=SearchPort)),(lo_run (r:=SearchPort)),(midpoint_run (r:=SearchPort)),(midTarget_run (r:=SearchPort)),(midStart_run (r:=SearchPort)),(leftState_run (r:=SearchPort)),(rightState_run (r:=SearchPort)),hn,ht,ite_false,ite_true,Nat.one_ne_zero,true_and,max_zero,zero_max]
  congr 1 <;> omega

theorem searchBody_right (handler : SearchState.T → Bill ℕ)
    (d : Tape (ℕ×ℕ)) (t l h : ℕ)
    (hlh : l<h) (ht : ¬t<start d (mid l h)) :
    Code.run searchBody handler ((d,t),(l,h)) =
      (handler ((d,t),(mid l h+1,h))).pay 69
        (max (max 2 (h-l)) (mid l h+1)) := by
  have hn : h-l≠0 := by omega
  simp only [searchBody,num,Code.run,Atom.run,NOp.run,Bill.word,Bill.one,Bill.pass,Bill.pay,(width_run (r:=SearchPort)),(lo_run (r:=SearchPort)),(midpoint_run (r:=SearchPort)),(midTarget_run (r:=SearchPort)),(midStart_run (r:=SearchPort)),(leftState_run (r:=SearchPort)),(rightState_run (r:=SearchPort)),hn,ht,ite_false,ite_true,true_and,max_zero,zero_max]
  congr 1 <;> omega
attribute [local irreducible] searchBody

theorem searchAux_left (f : ℕ) (d : Tape (ℕ×ℕ)) (t l h : ℕ)
    (hlh : l<h) (ht : t<start d (mid l h)) :
    searchAux (f+1) d t l h =
      (searchAux f d t l (mid l h)).pay 66
        (max (max 2 (h-l)) (max (mid l h) (f+1))) := by
  change ((Code.run searchBody (depthRun (run searchBase) (Code.run searchBody) f)
    ((d,t),(l,h))).pay 1 (f+1))=_
  rw [searchBody_left _ _ _ _ _ hlh ht]
  simp only [searchAux,Bill.pay]
  congr 1; omega

theorem searchAux_right (f : ℕ) (d : Tape (ℕ×ℕ)) (t l h : ℕ)
    (hlh : l<h) (ht : ¬t<start d (mid l h)) :
    searchAux (f+1) d t l h =
      (searchAux f d t (mid l h+1) h).pay 70
        (max (max 2 (h-l)) (max (mid l h+1) (f+1))) := by
  change ((Code.run searchBody (depthRun (run searchBase) (Code.run searchBody) f)
    ((d,t),(l,h))).pay 1 (f+1))=_
  rw [searchBody_right _ _ _ _ _ hlh ht]
  simp only [searchAux,Bill.pay]
  congr 1; omega

theorem searchSeed_run (d : Tape (ℕ×ℕ)) (t : ℕ) :
    run searchSeed (d,t)=⟨(d.len+1,((d,t),(0,d.len))),15,d.len+1,True⟩ := by
  simp only [searchSeed,num,Code.run,Atom.run,NOp.run,
    Bill.word,Bill.one,Bill.pass,Bill.pay,true_and,max_zero,zero_max]
  congr 1; omega
attribute [local irreducible] searchSeed

theorem closedSearch_run (d : Tape (ℕ×ℕ)) (t : ℕ) :
    run closedSearch (d,t)=(searchAux (d.len+1) d t 0 d.len).pay 17 (d.len+1) := by
  change ((run searchSeed (d,t)).pass (fun z=>
    (depthRun (run searchBase) (Code.run searchBody) z.1 z.2).pay 1 z.1)).pay 1 0=_
  rw [searchSeed_run]
  simp only [searchAux,Bill.pass,Bill.pay,true_and,max_zero]
  congr 1 <;> omega

end
end ExactFourierCircuits.DFTModelSectorMapCarry
