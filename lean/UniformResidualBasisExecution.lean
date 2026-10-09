import UniformResidualBasisMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformResidualBasisExecution
open UniformMachine UniformAssembly UniformResidualBasisMachine
open UniformNatBlockMachine (Op applyBlock readable peak block_runs)
noncomputable section

lemma rep_runs (n B q reduced A col adj value : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=20) (hq : s.natReg 4040=q) (hr : s.natReg 4051=reduced)
 (ha : s.natReg 4044=A) (hc : s.natReg 4052=col) (hi : s.natReg 4056=adj)
 (hv : s.natReg 4049=value) (bound : WordBound B s) (code : 29≤B)
 (extent : A+q+col*reduced+adj≤B) (vb : value≤B) :
 BoundedRuns program n x B s 5 (applyBlock representative s) := by
 have safe : readable representative s ∧ peak representative s≤B := by
  simp [representative,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   hq,hr,ha,hc,hi,hv]
  omega
 exact block_runs representative program 20 n B x s representative_code pc bound (by change 25≤B;omega) safe.1 safe.2

/-- Every branch of the literal image writer is charged; it never tests scalar
values. The mask is prepared by the original descriptor caller. -/
theorem round_runs (n B q w p mask A j : ℕ) (x : Fin n→ℂ) (s : State)
 (c : Control q w p mask A j s) (wp : 0<w) (pp : p<w) (small : mask<2^w)
 (jp : j<q*w) (bound : WordBound B s) (code : 29≤B)
 (extent : A+q*w≤B) (volume : 2^(q*w)≤B) :
 BoundedRuns program n x B s (roundCost w p j) (round s) := by
 have wn : w≠0:=by omega
 have jb : j≤B := by have h:=bound.2.1 4048;rw [c.index] at h;exact h
 have collt : j/w<q:=(Nat.div_lt_iff_lt_mul wp).2 jp
 have remSmall :=Nat.mod_lt j wp
 have predShape : q*(w-1)+q=q*w := by
  calc
   q*(w-1)+q=q*((w-1)+1) := by ring
   _=q*w := by congr 1;omega
 have qle : q≤q*w := by exact Nat.le_mul_of_pos_right _ wp
 have place : 2^j≤B := (Nat.pow_le_pow_right (by omega : 1≤2) jp.le).trans volume
 let start:State:={s with pc:=8}
 have branch : BoundedRuns program n x B s 1 start:=.next bound
  (by simp [step,c.pc,branch_at,c.index,c.length,jp,start])
  (.refl (changePC_bound B s 8 bound (by omega)))
 have safePos : readable positions start ∧ peak positions start≤B := by
  simp [positions,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,
   start,c.width,c.index,wn]
  exact ⟨(Nat.div_le_self _ _).trans jb,(Nat.mod_le _ _).trans jb⟩
 have posRun:=block_runs positions program 8 n B x start positions_code rfl branch.final_bound
  (by change 10≤B;omega) safePos.1 safePos.2
 let pos:=applyBlock positions start
 have posPC : pos.pc=10:=by simp [pos,positions,applyBlock,Op.apply,writeNat,next,start]
 have posCol : pos.natReg 4052=j/w:=by simp [pos,positions,applyBlock,Op.apply,evalNat,writeNat,next,start,c.width,c.index,wn]
 have posRem : pos.natReg 4053=j%w:=by simp [pos,positions,applyBlock,Op.apply,evalNat,writeNat,next,start,c.width,c.index,wn]
 have posKeep (r:ℕ) (hr:r<4052 ∨ 4053<r) : pos.natReg r=s.natReg r := by
  simp (disch:=omega) [pos,positions,applyBlock,Op.apply,writeNat,next,start]
 have posMask : pos.natReg 4043=mask := (posKeep _ (by omega)).trans c.mask
 have posPlace : pos.natReg 4049=2^j := (posKeep _ (by omega)).trans c.place
 have posBase : pos.natReg 4044=A := (posKeep _ (by omega)).trans c.base
 have posOne : pos.natReg 4045=1 := (posKeep _ (by omega)).trans c.one
 have pickRun : BoundedRuns program n x B pos (if j%w=0 then 5 else 1) (picked pos) := by
  by_cases zero:j%w=0
  · let entry:State:={pos with pc:=11}
    have sel : BoundedRuns program n x B pos 1 entry:=.next posRun.final_bound
     (by simp [step,posPC,selected_at,posRem,posOne,zero,entry])
     (.refl (changePC_bound B pos 11 posRun.final_bound (by omega)))
    have mb : 2^j*mask≤B := (selected_bounds q w mask j wp small jp zero).le.trans volume
    have safe : readable selected entry ∧ peak selected entry≤B := by
     simp [selected,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,entry,
      posPlace,posMask,posCol,posBase]
     omega
    have body:=block_runs selected program 11 n B x entry selected_code rfl sel.final_bound
     (by change 14≤B;omega) safe.1 safe.2
    let v:=applyBlock selected entry
    have vp:v.pc=14:=by simp [v,selected,applyBlock,Op.apply,writeNat,next,entry]
    have jump : BoundedRuns program n x B v 1 {v with pc:=15}:=.next body.final_bound
     (by simp [step,vp,selected_jump])
     (.refl (changePC_bound B v 15 body.final_bound (by omega)))
    simpa [picked,posRem,zero,selected,v,entry] using sel.trans (body.trans jump)
  · have no : ¬j%w<1:=by omega
    have move : BoundedRuns program n x B pos 1 {pos with pc:=15}:=.next posRun.final_bound
     (by simp [step,posPC,selected_at,posRem,posOne,no])
     (.refl (changePC_bound B pos 15 posRun.final_bound (by omega)))
    simpa [picked,posRem,zero] using move
 let pick:=picked pos
 have pickPC : pick.pc=15:=by simp [pick,picked];split_ifs <;> rfl
 have pickKeep (r:ℕ) (hr:r<4054 ∨ 4055<r) : pick.natReg r=pos.natReg r := by
  simp [pick,picked]
  split_ifs <;> simp (disch:=omega) [selected,applyBlock,Op.apply,writeNat,next]
 have pickRem : pick.natReg 4053=j%w := (pickKeep _ (by omega)).trans posRem
 have pickCol : pick.natReg 4052=j/w := (pickKeep _ (by omega)).trans posCol
 have pickPivot : pick.natReg 4042=p := (pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.pivot)
 have pickQ : pick.natReg 4040=q := (pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.columns)
 have pickReduced : pick.natReg 4051=w-1 := (pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.reduced)
 have pickBase : pick.natReg 4044=A := (pickKeep _ (by omega)).trans posBase
 have pickPlace : pick.natReg 4049=2^j := (pickKeep _ (by omega)).trans posPlace
 have pickOne : pick.natReg 4045=1 := (pickKeep _ (by omega)).trans posOne
 have pickZero : pick.natReg 4047=0 := (pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.zero)
 have repRun : BoundedRuns program n x B pick
  (if j%w<p then 7 else if p<j%w then 9 else 2) (represented pick) := by
  by_cases low:j%w<p
  · let entry:State:={pick with pc:=19}
    have first : BoundedRuns program n x B pick 1 entry:=.next pickRun.final_bound
     (by simp [step,pickPC,low_at,pickRem,pickPivot,low,entry])
     (.refl (changePC_bound B pick 19 pickRun.final_bound (by omega)))
    have safe : readable lower entry ∧ peak lower entry≤B := by
     simp [lower,readable,peak,Op.readable,Op.peak,evalNat,entry,pickRem,pickZero]
     exact (Nat.mod_le _ _).trans jb
    have adjust:=block_runs lower program 19 n B x entry lower_code rfl first.final_bound
     (by change 20≤B;omega) safe.1 safe.2
    let v:=applyBlock lower entry
    have vp:v.pc=20:=by simp [v,lower,applyBlock,Op.apply,writeNat,next,entry]
    have vb : A+q+(j/w)*(w-1)+j%w≤B := by
     have inrange:=slot_bounds q w p j wp pp jp (by omega)
     simpa [repSlot,omitted,low,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (show A+repSlot q w p j≤B by omega)
    have body:=rep_runs n B q (w-1) A (j/w) (j%w) (2^j) x v vp
     (by simpa [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry] using pickQ)
     (by simpa [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry] using pickReduced)
     (by simpa [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry] using pickBase)
     (by simpa [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry] using pickCol)
     (by simp [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry,pickRem,pickZero])
     (by simpa [v,lower,applyBlock,Op.apply,evalNat,writeNat,next,entry] using pickPlace)
     adjust.final_bound code vb place
    simpa [represented,pickRem,pickPivot,low,lower,v,entry] using first.trans (adjust.trans body)
  · let entry:State:={pick with pc:=16}
    have first : BoundedRuns program n x B pick 1 entry:=.next pickRun.final_bound
     (by simp [step,pickPC,low_at,pickRem,pickPivot,low,entry])
     (.refl (changePC_bound B pick 16 pickRun.final_bound (by omega)))
    by_cases high:p<j%w
    · let choose:State:={entry with pc:=17}
      have second : BoundedRuns program n x B entry 1 choose:=.next first.final_bound
       (by simp [step,entry,high_at,pickRem,pickPivot,high,choose])
       (.refl (changePC_bound B entry 17 first.final_bound (by omega)))
      have safe : readable upper choose ∧ peak upper choose≤B := by
       simp [upper,readable,peak,Op.readable,Op.peak,evalNat,choose,entry,pickRem,pickOne]
       have le: j%w≤B:=(Nat.mod_le _ _).trans jb
       omega
      have adjust:=block_runs upper program 17 n B x choose upper_code rfl second.final_bound
       (by change 18≤B;omega) safe.1 safe.2
      let v:=applyBlock upper choose
      have vp:v.pc=18:=by simp [v,upper,applyBlock,Op.apply,writeNat,next,choose]
      let moved:State:={v with pc:=20}
      have move : BoundedRuns program n x B v 1 moved:=.next adjust.final_bound
       (by simp [step,vp,high_jump,moved])
       (.refl (changePC_bound B v 20 adjust.final_bound (by omega)))
      have vb : A+q+(j/w)*(w-1)+(j%w-1)≤B := by
       have inrange:=slot_bounds q w p j wp pp jp (by omega)
       simpa [repSlot,omitted,low,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (show A+repSlot q w p j≤B by omega)
      have body:=rep_runs n B q (w-1) A (j/w) (j%w-1) (2^j) x moved rfl
       (by simpa [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry] using pickQ)
       (by simpa [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry] using pickReduced)
       (by simpa [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry] using pickBase)
       (by simpa [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry] using pickCol)
       (by simp [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry,pickRem,pickOne])
       (by simpa [moved,v,upper,applyBlock,Op.apply,evalNat,writeNat,next,choose,entry] using pickPlace)
       move.final_bound code vb place
      simpa [represented,pickRem,pickPivot,low,high,upper,entry,choose,moved,v] using first.trans (second.trans (adjust.trans (move.trans body)))
    · have move : BoundedRuns program n x B entry 1 {entry with pc:=25}:=.next first.final_bound
       (by simp [step,entry,high_at,pickRem,pickPivot,high])
       (.refl (changePC_bound B entry 25 first.final_bound (by omega)))
      simpa [represented,pickRem,pickPivot,low,high,entry] using first.trans move
 let rep:=represented pick
 have repPC : rep.pc=25 := by
  simp [rep,represented,pickRem,pickPivot]
  split_ifs <;> simp [lower,upper,representative,applyBlock,Op.apply,writeNat,next]
 have repKeep (r:ℕ) (hr:r<4055 ∨ 4056<r) : rep.natReg r=pick.natReg r := by
  simp [rep,represented]
  split_ifs <;> simp (disch:=omega) [lower,upper,representative,applyBlock,Op.apply,writeNat,next]
 have repOne : rep.natReg 4045=1 := (repKeep _ (by omega)).trans pickOne
 have repTwo : rep.natReg 4046=2 := (repKeep _ (by omega)).trans ((pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.two))
 have repIndex : rep.natReg 4048=j := (repKeep _ (by omega)).trans ((pickKeep _ (by omega)).trans ((posKeep _ (by omega)).trans c.index))
 have repPlace : rep.natReg 4049=2^j := (repKeep _ (by omega)).trans pickPlace
 have nextPlace : 2^j*2≤B := by
  rw [←Nat.pow_succ]
  exact (Nat.pow_le_pow_right (by omega : 1≤2) (show j+1≤q*w by omega)).trans volume
 have nextIndex : j+1≤B := by have b:q*w<2^(q*w):=Nat.lt_two_pow_self;omega
 have safeAdvance : readable advance rep ∧ peak advance rep≤B := by
  simp [advance,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,repPlace,repOne,repTwo,repIndex]
  exact ⟨nextPlace,nextIndex⟩
 have advanced:=block_runs advance program 25 n B x rep advance_code repPC repRun.final_bound
  (by change 27≤B;omega) safeAdvance.1 safeAdvance.2
 let last:=applyBlock advance rep
 have lastPC : last.pc=27 := by simp [last,advance,applyBlock,Op.apply,writeNat,next,repPC]
 have jump : BoundedRuns program n x B last 1 {last with pc:=7}:=.next advanced.final_bound
  (by simp [step,lastPC,loop_at]) (.refl (changePC_bound B last 7 advanced.final_bound (by omega)))
 convert branch.trans (posRun.trans (pickRun.trans (repRun.trans (advanced.trans jump)))) using 1
 · simp [roundCost,positions,advance]
   omega
 · rfl


/-- All original basis images are printed, including directions with zero
non-pivot bits. There is no per-leaf coordinate scan in this preparation. -/
theorem loop_execution (n B q w p mask A j fuel : ℕ) (x : Fin n→ℂ) (s : State)
 (c : Control q w p mask A j s) (wp : 0<w) (pp : p<w) (small : mask<2^w)
 (total : j+fuel=q*w) (part : Partial q w p mask A j s)
 (bound : WordBound B s) (code : 29≤B) (extent : A+q*w≤B) (volume : 2^(q*w)≤B) :
 ∃u steps,BoundedExecution program n x B s steps u ∧ steps≤20*fuel+2 ∧ u.pc=28 ∧ u.natReg 4050=q*w ∧
 Partial q w p mask A (q*w) u ∧ Frame A (q*w) s u := by
 induction fuel generalizing j s with
 | zero=>
   have eq:j=q*w:=by omega
   let u:State:={s with pc:=28}
   have run:BoundedExecution program n x B s 2 u:=.next bound
    (by simp [step,c.pc,branch_at,c.index,c.length,eq,u])
    (.halt (changePC_bound B s 28 bound (by omega)) (by simp [step,u,halt_at]))
   refine ⟨u,2,run,by omega,rfl,c.length,?_,?_⟩
   · simpa [u,eq,Partial] using part
   · exact ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
 | succ fuel ih=>
   have jp:j<q*w:=by omega
   have run:=round_runs n B q w p mask A j x s c wp pp small jp bound code extent volume
   have control:=round_control q w p mask A j s c wp pp
   have partReady:=round_partial q w p mask A j s c wp pp jp part
   have frame:=round_frame q w p mask A j s c wp pp jp
   obtain ⟨u,steps,tail,cost,pc,length,part,fr⟩:=ih (j+1) (round s) control (by omega) partReady run.final_bound
   refine ⟨u,roundCost w p j+steps,run.executes tail,?_,pc,length,part,frame.trans fr⟩
   have one:=roundCost_bound w p j
   omega

structure Inputs (q w p mask A : ℕ) (s : State) : Prop where
 columns : s.natReg 4040=q
 width : s.natReg 4041=w
 pivot : s.natReg 4042=p
 mask : s.natReg 4043=mask
 base : s.natReg 4044=A

/-- Complete physical image-bank producer with original scalar state and all
outside Natheap cells retained. Its q,m,pivot,mask inputs are header operands,
not an existing image-table premise. -/
theorem execution (n B q w p mask A : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (input : Inputs q w p mask A s) (wp : 0<w) (pp : p<w)
 (small : mask<2^w) (bound : WordBound B s) (code : 29≤B)
 (extent : A+q*w≤B) (volume : 2^(q*w)≤B) :
 ∃u steps,BoundedExecution program n x B s steps u ∧ steps≤20*(q*w)+9 ∧ u.pc=28 ∧ u.natReg 4050=q*w ∧
 (∀c, c<q → u.natHeap (A+c)=some (2^(c*w)*mask)) ∧
 (∀t, t<q*w → t%w≠p → u.natHeap (A+repSlot q w p t)=some (2^t)) ∧
 Frame A (q*w) s u := by
 have len : q*w≤B:=by have pow:q*w<2^(q*w):=Nat.lt_two_pow_self;omega
 have width : w≤B:=by have h:=bound.2.1 4041;rw [input.width] at h;exact h
 have safe : readable boot s ∧ peak boot s≤B := by
  simp [boot,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,input.columns,input.width]
  omega
 have start:=block_runs boot program 0 n B x s boot_code pc bound (by change 7≤B;omega) safe.1 safe.2
 let ready:=applyBlock boot s
 have control : Control q w p mask A 0 ready := by
  constructor <;> simp [ready,boot,applyBlock,Op.apply,evalNat,writeNat,next,pc,
   input.columns,input.width,input.pivot,input.mask,input.base]
 have partReady : Partial q w p mask A 0 ready := by constructor <;> intros <;> omega
 obtain ⟨u,ticks,run,cost,up,length,part,fr⟩:=loop_execution n B q w p mask A 0 (q*w) x ready control wp pp small
  (by omega) partReady start.final_bound code extent volume
 have initialFrame : Frame A (q*w) s ready := by
  refine ⟨fun _ _=>rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r keep
  simp (disch:=omega) [ready,boot,applyBlock,Op.apply,evalNat,writeNat,next]
 refine ⟨u,7+ticks,?_,by omega,up,length,?_,part.2,initialFrame.trans fr⟩
 · simpa [boot] using start.executes run
 · intro column cp
   have visit:column*w<q*w:=(Nat.mul_lt_mul_right wp).2 cp
   exact part.1 column cp visit

end
end ExactFourierCircuits.UniformResidualBasisExecution
