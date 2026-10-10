import DFTModelCacheDAGDepthSource
import UniformDAGBucketMachine

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheBucket
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section
abbrev Input:=p w (p w (Ty.a w))
abbrev State:=p w w
abbrev Request:=p Input (p w w)
abbrev Cursor:=p Request (p w State)
abbrev ScanInput:=p Request State
open DFTModelCacheDAGDepth (nat)

def equal : Prog false (p w w) w :=
  .ifz (.atom (.int .lt))
    (.ifz (nat .lt (.atom .snd) (.atom .fst)) (.atom (.lit 1)) (.atom (.lit 0)))
    (.atom (.lit 0))
def count : Prog false Input w := .comp (.atom .snd) (.atom .fst)
def labels : Prog false Input (Ty.a w) := .comp (.atom .snd) (.atom .snd)
def root : Prog false Cursor Input := .comp (.atom .fst) (.atom .fst)
def level : Prog false Cursor w := .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def query : Prog false Cursor w := .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def index : Prog false Cursor w := .comp (.atom .snd) (.atom .fst)
def current : Prog false Cursor State := .comp (.atom .snd) (.atom .snd)
def ordinal : Prog false Cursor w := .comp current (.atom .fst)
def value : Prog false Cursor w := .comp current (.atom .snd)
def depth : Prog false Cursor w :=
  .comp (.fork (.comp root labels)
    (nat .add (nat .add (.comp root (.atom .fst)) (.atom (.lit 1))) index)) (.atom .look)
def accepts : Prog false Cursor w := .comp (.fork depth level) equal
def replacement : Prog false Cursor w :=
  .ifz (.comp (.fork ordinal query) equal) value index
def step : Prog false Cursor State :=
  .ifz accepts current (.fork (nat .add ordinal (.atom (.lit 1))) replacement)
def scanCount :Prog false ScanInput w:=.comp (.atom .fst) (.comp (.atom .fst) count)
def scanBody :Prog false (p ScanInput (p w State)) State:=
  .comp (.fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)) step
def scan : Prog false ScanInput State := .loop scanCount (.atom .snd) scanBody
def next : Prog false Cursor State :=
  .comp (.fork (.fork root (.fork index query)) current) scan
def selectorCount :Prog false Request w:=.comp (.atom .snd) (.atom .fst)
def zeroState :Prog false Request State:=.fork (.atom (.lit 0)) (.atom (.lit 0))
def selector : Prog false Request State := .loop selectorCount zeroState next

def fullRequest : Prog false Input Request :=
  .fork (.atom .id) (.fork (nat .add count (.atom (.lit 1))) (.atom (.lit 0)))
def length : Prog false Input w := .comp (.comp fullRequest selector) (.atom .fst)
def orderCell : Prog false (p Input w) w :=
  .comp (.comp (.fork (.atom .fst)
    (.fork (.comp (.atom .fst) (nat .add count (.atom (.lit 1)))) (.atom .snd))) selector) (.atom .snd)
def directoryCell : Prog false (p Input w) w :=
  .comp (.comp (.fork (.atom .fst) (.fork (.atom .snd) (.atom (.lit 0)))) selector) (.atom .fst)
def order : Prog false Input (Ty.a w) := .tab length orderCell
def directory : Prog false Input (Ty.a w) :=
  .tab (nat .add count (.atom (.lit 2))) directoryCell
def program : Prog false Input (p (Ty.a w) (Ty.a w)) := .fork order directory

def depthValue (x:Input.T) (i:ℕ) : ℕ:=x.2.2.look (x.1+1+i) 0
def processed (G L:ℕ) (d:ℕ→ℕ):List ℕ:=
  (List.range L).flatMap (fun l=>UniformDAGBucketMachine.selected G l d)
def selected (d:ℕ→ℕ) (l i:ℕ):List ℕ:=
  (List.range i).filter (fun j=>decide (d j=l))
def choice (xs:List ℕ) (q:ℕ):State.T:=(xs.length,xs[q]?.getD 0)
def advance (d:ℕ→ℕ) (l q i:ℕ) (s:State.T):State.T:=
  if d i=l then (s.1+1,if s.1=q then i else s.2) else s

theorem equal_run (a b:ℕ) : run equal (a,b)=
    ⟨if a=b then 1 else 0,if a<b then 3 else 9,1,True⟩ := by
  by_cases h:a<b
  · have hn:a≠b:=by omega
    simp [equal,run,Code.run,Atom.run,NOp.run,Bill.word,Bill.pass,Bill.pay,h,hn]
  · by_cases hr:b<a
    · have hn:a≠b:=by omega
      simp [equal,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay,h,hr,hn]
    · have he:a=b:=by omega
      subst b
      simp [equal,nat,run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]

theorem equal_value (a b:ℕ) : (Code.run equal () (a,b)).val=(if a=b then 1 else 0) :=
  congrArg Bill.val (equal_run a b)

theorem depth_run (x:Input.T) (l q i:ℕ) (s:State.T):
    run depth ((x,(l,q)),(i,s))=⟨depthValue x i,25,x.1+1+i,True⟩ := by
  simp [depth,root,labels,index,nat,depthValue,run,Code.run,Atom.run,NOp.run,
    Bill.one,Bill.word,Bill.pass,Bill.pay]
  congr 1

theorem accepts_run (x:Input.T) (l q i:ℕ) (s:State.T):
    run accepts ((x,(l,q)),(i,s))=
      ⟨if depthValue x i=l then 1 else 0,
        32+(if depthValue x i<l then 3 else 9),x.1+1+i,True⟩ := by
  rw [accepts]
  change (((run depth ((x,(l,q)),(i,s))).pass (fun a=>
    (run level ((x,(l,q)),(i,s))).pass (fun b=>Bill.one (a,b)))).pass
      (run equal)).pay 1 0=_
  rw [depth_run]
  have hl:run level ((x,(l,q)),(i,s))=⟨l,5,0,True⟩:=by
    simp [level,run,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [hl]
  simp only [Bill.pass,Bill.pay,Bill.one,true_and,max_zero]
  rw [equal_run (depthValue x i) l]
  dsimp only [Bill.val,Bill.work,Bill.peak,Bill.valid]
  congr 1 <;>omega

theorem step_value (x:Input.T) (l q i:ℕ) (s:State.T):
    (run step ((x,(l,q)),(i,s))).val=advance (depthValue x) l q i s := by
  rw [step]
  change (((run accepts ((x,(l,q)),(i,s))).pass
    (fun z=>if z=0 then run current ((x,(l,q)),(i,s)) else
      run (.fork (nat .add ordinal (.atom (.lit 1))) replacement) ((x,(l,q)),(i,s)))).pay 1 0).val = _
  rw [accepts_run]
  by_cases h:depthValue x i=l
  · simp only [h,ite_true,one_ne_zero,ite_false,Bill.pass,Bill.pay]
    simp only [replacement,ordinal,current,query,index,value,nat,advance,h,
      run,Code.run,Atom.run,NOp.run,Bill.one,Bill.word,Bill.pass,Bill.pay]
    simp only [equal_value s.1 q]
    by_cases he:s.1=q <;> simp [he]
  · simp [h,advance,run,current,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]

end
end ExactFourierCircuits.DFTModelCacheBucket
