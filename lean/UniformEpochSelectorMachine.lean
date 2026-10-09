import UniformMachineRuns
set_option autoImplicit false
namespace ExactFourierCircuits.UniformEpochSelectorMachine
open UniformMachine
noncomputable section

/-- One fixed Nat-only selector; register6816 addresses the produced duration cell. -/
def program : Program := [
 .loadNat 7070 6816,
 .natLiteral 7071 0,
 .natLiteral 7072 1,
 .natLiteral 7073 2,
 .natLiteral 7074 3,
 .natLiteral 7075 4,
 .natLiteral 7076 5,
 .natBinary .add 7077 7070 7072,
 .natBinary .add 7078 7070 7075,
 .natBinary .mul 7079 7070 7073,
 .natBinary .add 7079 7079 7075,
 .branchLT 5920 7072 25 12,
 .branchLT 5920 7077 28 13,
 .branchLT 5920 7078 14 18,
 .natBinary .add 7077 7077 7072,
 .branchLT 5920 7077 31 16,
 .natBinary .add 7077 7077 7072,
 .branchLT 5920 7077 34 31,
 .branchLT 5920 7079 37 19,
 .natBinary .add 7079 7079 7072,
 .branchLT 5920 7079 25 21,
 .natLiteral 7080 2,
 .natLiteral 6702 0,
 .natLiteral 6705 0,
 .jump 40,
 .natLiteral 7080 1,
 .natLiteral 7001 0,
 .jump 40,
 .natLiteral 7080 0,
 .natBinary .sub 6703 7070 5920,
 .jump 40,
 .natLiteral 7080 1,
 .natLiteral 7001 1,
 .jump 40,
 .natLiteral 7080 1,
 .natLiteral 7001 2,
 .jump 40,
 .natLiteral 7080 0,
 .natBinary .sub 6703 5920 7078,
 .jump 40,
 .halt]
lemma program_length : program.length = 41 := rfl

def modified : List Nat := [7070,7071,7072,7073,7074,7075,7076,7077,7078,7079,7080,6702,6703,6705,7001]
structure Frame (s u : State) : Prop where
 natHeap : u.natHeap = s.natHeap
 scalarHeap : u.scalarHeap = s.scalarHeap
 scalarReg : u.scalarReg = s.scalarReg
 outputs : u.outputs = s.outputs
 roots : u.rootOrders = s.rootOrders
 natReg : ∀j, j ∉ modified → u.natReg j = s.natReg j
lemma Frame.trans {s t u:State}(a:Frame s t)(b:Frame t u):Frame s u :=
 ⟨b.natHeap.trans a.natHeap,b.scalarHeap.trans a.scalarHeap,b.scalarReg.trans a.scalarReg,
  b.outputs.trans a.outputs,b.roots.trans a.roots,fun j h=>(b.natReg j h).trans (a.natReg j h)⟩

structure Header (d g:Nat)(s:State):Prop where
 epoch : s.natReg 5920 = g
 duration : s.natReg 7070 = d
 zero : s.natReg 7071 = 0
 one : s.natReg 7072 = 1
 two : s.natReg 7073 = 2
 three : s.natReg 7074 = 3
 four : s.natReg 7075 = 4
 five : s.natReg 7076 = 5
 nextBoundary : s.natReg 7077 = d+1
 reverseStart : s.natReg 7078 = d+4
 finalBoundary : s.natReg 7079 = 2*d+4

/-- TREE is mode0; BOUNDARY mode1; INACTIVE mode2. The second tree stage
increases from zero, and is not reversed elapsed time. -/
def Selected (d g:Nat)(u:State):Prop :=
 ((g=0 ∨ g=2*d+4) ∧ u.natReg 7080=1 ∧ u.natReg 7001=0) ∨
 (1 ≤ g ∧ g ≤ d ∧ u.natReg 7080=0 ∧ u.natReg 6703=d-g) ∨
 ((g=d+1 ∨ g=d+3) ∧ u.natReg 7080=1 ∧ u.natReg 7001=1) ∨
 (g=d+2 ∧ u.natReg 7080=1 ∧ u.natReg 7001=2) ∨
 (d+4 ≤ g ∧ g < 2*d+4 ∧ u.natReg 7080=0 ∧ u.natReg 6703=g-d-4) ∨
 (2*d+5 ≤ g ∧ u.natReg 7080=2 ∧ u.natReg 6702=0 ∧ u.natReg 6705=0)

private lemma boot_execution (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(epoch:s.natReg 5920=g)(source:s.natHeap (s.natReg 6816)=some d)
 (bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B):
 ∃u, BoundedRuns program n x B s 11 u ∧ u.pc=11 ∧ Header d g u ∧ Frame s u := by
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := writeNat s 7070 (d)
 have b1:WordBound B t1:=writeNat_bound B s 7070 (d) bound
  (by simp only [   pc]; omega) (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,  writeNat, next, pc,  source]

 let t2:State := writeNat t1 7071 (0)
 have b2:WordBound B t2:=writeNat_bound B t1 7071 (0) b1
  (by simp only [t1,  writeNat, next, pc]; omega) (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,  writeNat, next, pc]

 let t3:State := writeNat t2 7072 (1)
 have b3:WordBound B t3:=writeNat_bound B t2 7072 (1) b2
  (by simp only [t1, t2,  writeNat, next, pc]; omega) (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,  writeNat, next, pc]

 let t4:State := writeNat t3 7073 (2)
 have b4:WordBound B t4:=writeNat_bound B t3 7073 (2) b3
  (by simp only [t1, t2, t3,  writeNat, next, pc]; omega) (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program,  writeNat, next, pc]

 let t5:State := writeNat t4 7074 (3)
 have b5:WordBound B t5:=writeNat_bound B t4 7074 (3) b4
  (by simp only [t1, t2, t3, t4,  writeNat, next, pc]; omega) (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next, pc]

 let t6:State := writeNat t5 7075 (4)
 have b6:WordBound B t6:=writeNat_bound B t5 7075 (4) b5
  (by simp only [t1, t2, t3, t4, t5,  writeNat, next, pc]; omega) (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program,  writeNat, next, pc]

 let t7:State := writeNat t6 7076 (5)
 have b7:WordBound B t7:=writeNat_bound B t6 7076 (5) b6
  (by simp only [t1, t2, t3, t4, t5, t6,  writeNat, next, pc]; omega) (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next, pc]

 let t8:State := writeNat t7 7077 ((d)+(1))
 have b8:WordBound B t8:=writeNat_bound B t7 7077 ((d)+(1)) b7
  (by simp only [t1, t2, t3, t4, t5, t6, t7,  writeNat, next, pc]; omega) (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program, evalNat, writeNat, next, pc]

 let t9:State := writeNat t8 7078 ((d)+(4))
 have b9:WordBound B t9:=writeNat_bound B t8 7078 ((d)+(4)) b8
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8,  writeNat, next, pc]; omega) (by omega)
 have e8:step program n x t8=.running t9:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program, evalNat, writeNat, next, pc]

 let t10:State := writeNat t9 7079 ((d)*(2))
 have b10:WordBound B t10:=writeNat_bound B t9 7079 ((d)*(2)) b9
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8, t9,  writeNat, next, pc]; omega) (by omega)
 have e9:step program n x t9=.running t10:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program, evalNat, writeNat, next, pc]

 let t11:State := writeNat t10 7079 (((d)*(2))+(4))
 have b11:WordBound B t11:=writeNat_bound B t10 7079 (((d)*(2))+(4)) b10
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,  writeNat, next, pc]; omega) (by omega)
 have e10:step program n x t10=.running t11:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, step, program, evalNat, writeNat, next, pc]

 have run:BoundedRuns program n x B s 11 t11:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.next b8 e8 (.next b9 e9 (.next b10 e10 (.refl b11)))))))))))
 refine ⟨t11,run,?_,?_,?_⟩
 · simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11,writeNat,next,pc]
 · constructor <;> simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11,writeNat,next,epoch]; omega
 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11,writeNat,next,h7070,h7071,h7072,h7073,h7074,h7075,h7076,h7077,h7078,h7079]

private lemma first (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (edge:g=0):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=25}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := writeNat t1 7080 (1)
 have b2:WordBound B t2:=writeNat_bound B t1 7080 (1) b1
  (by simp only [t1]; omega) (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,  writeNat, next]

 let t3:State := writeNat t2 7001 (0)
 have b3:WordBound B t3:=writeNat_bound B t2 7001 (0) b2
  (by simp only [t1, t2,  writeNat, next]; omega) (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,  writeNat, next]

 let t4:State := {t3 with pc:=40}
 have b4:WordBound B t4:=changePC_bound B t3 _ b3 (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program,  writeNat, next]

 have stop:step program n x t4=.halted t4:=by simp [t1, t2, t3, t4, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 5 t4:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.halt b4 stop))))
 refine ⟨t4,5,run,by omega,?_,?_⟩
 · exact Or.inl ⟨Or.inl edge,by simp [t1,t2,t3,t4,writeNat,next],by simp [t1,t2,t3,t4,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4,writeNat,next,h7080,h7001]

private lemma forward (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (lo:1 ≤ g)(hi:g ≤ d):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=28}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := writeNat t2 7080 (0)
 have b3:WordBound B t3:=writeNat_bound B t2 7080 (0) b2
  (by simp only [ t2]; omega) (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,  writeNat, next]

 let t4:State := writeNat t3 6703 ((d)-(g))
 have b4:WordBound B t4:=writeNat_bound B t3 6703 ((d)-(g)) b3
  (by simp only [t1, t2, t3,  writeNat, next]; omega) (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program, evalNat, writeNat, next,   epoch, duration]

 let t5:State := {t4 with pc:=40}
 have b5:WordBound B t5:=changePC_bound B t4 _ b4 (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next]

 have stop:step program n x t5=.halted t5:=by simp [t1, t2, t3, t4, t5, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 6 t5:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.halt b5 stop)))))
 refine ⟨t5,6,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inl; exact ⟨lo,hi,by simp [t1,t2,t3,t4,t5,writeNat,next],by simp [t1,t2,t3,t4,t5,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5,writeNat,next,h7080,h6703]

private lemma laneOneEarly (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (edge:g=d+1):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=14}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := writeNat t3 7077 ((d+1)+(1))
 have b4:WordBound B t4:=writeNat_bound B t3 7077 ((d+1)+(1)) b3
  (by simp only [  t3]; omega) (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program, evalNat, writeNat, next,      one,     nextBoundary]

 let t5:State := {t4 with pc:=31}
 have b5:WordBound B t5:=changePC_bound B t4 _ b4 (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next,   epoch]
  ; omega
 let t6:State := writeNat t5 7080 (1)
 have b6:WordBound B t6:=writeNat_bound B t5 7080 (1) b5
  (by simp only [    t5]; omega) (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program,  writeNat, next]

 let t7:State := writeNat t6 7001 (1)
 have b7:WordBound B t7:=writeNat_bound B t6 7001 (1) b6
  (by simp only [t1, t2, t3, t4, t5, t6,  writeNat, next]; omega) (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next]

 let t8:State := {t7 with pc:=40}
 have b8:WordBound B t8:=changePC_bound B t7 _ b7 (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program,  writeNat, next]

 have stop:step program n x t8=.halted t8:=by simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 9 t8:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.halt b8 stop))))))))
 refine ⟨t8,9,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inr; apply Or.inl; exact ⟨Or.inl edge,by simp [t1,t2,t3,t4,t5,t6,t7,t8,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8,writeNat,next,h7077,h7080,h7001]

private lemma laneTwo (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (edge:g=d+2):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=14}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := writeNat t3 7077 ((d+1)+(1))
 have b4:WordBound B t4:=writeNat_bound B t3 7077 ((d+1)+(1)) b3
  (by simp only [  t3]; omega) (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program, evalNat, writeNat, next,      one,     nextBoundary]

 let t5:State := {t4 with pc:=16}
 have b5:WordBound B t5:=changePC_bound B t4 _ b4 (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next,   epoch]
  ; omega
 let t6:State := writeNat t5 7077 (((d+1)+(1))+(1))
 have b6:WordBound B t6:=writeNat_bound B t5 7077 (((d+1)+(1))+(1)) b5
  (by simp only [    t5]; omega) (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program, evalNat, writeNat, next,      one]

 let t7:State := {t6 with pc:=34}
 have b7:WordBound B t7:=changePC_bound B t6 _ b6 (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next,   epoch]
  ; omega
 let t8:State := writeNat t7 7080 (1)
 have b8:WordBound B t8:=writeNat_bound B t7 7080 (1) b7
  (by simp only [      t7]; omega) (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program,  writeNat, next]

 let t9:State := writeNat t8 7001 (2)
 have b9:WordBound B t9:=writeNat_bound B t8 7001 (2) b8
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8,  writeNat, next]; omega) (by omega)
 have e8:step program n x t8=.running t9:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program,  writeNat, next]

 let t10:State := {t9 with pc:=40}
 have b10:WordBound B t10:=changePC_bound B t9 _ b9 (by omega)
 have e9:step program n x t9=.running t10:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program,  writeNat, next]

 have stop:step program n x t10=.halted t10:=by simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 11 t10:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.next b8 e8 (.next b9 e9 (.halt b10 stop))))))))))
 refine ⟨t10,11,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl; exact ⟨edge,by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,writeNat,next,h7077,h7080,h7001]

private lemma laneOneLate (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (edge:g=d+3):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=14}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := writeNat t3 7077 ((d+1)+(1))
 have b4:WordBound B t4:=writeNat_bound B t3 7077 ((d+1)+(1)) b3
  (by simp only [  t3]; omega) (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program, evalNat, writeNat, next,      one,     nextBoundary]

 let t5:State := {t4 with pc:=16}
 have b5:WordBound B t5:=changePC_bound B t4 _ b4 (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next,   epoch]
  ; omega
 let t6:State := writeNat t5 7077 (((d+1)+(1))+(1))
 have b6:WordBound B t6:=writeNat_bound B t5 7077 (((d+1)+(1))+(1)) b5
  (by simp only [    t5]; omega) (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program, evalNat, writeNat, next,      one]

 let t7:State := {t6 with pc:=31}
 have b7:WordBound B t7:=changePC_bound B t6 _ b6 (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next,   epoch]
  ; omega
 let t8:State := writeNat t7 7080 (1)
 have b8:WordBound B t8:=writeNat_bound B t7 7080 (1) b7
  (by simp only [      t7]; omega) (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program,  writeNat, next]

 let t9:State := writeNat t8 7001 (1)
 have b9:WordBound B t9:=writeNat_bound B t8 7001 (1) b8
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8,  writeNat, next]; omega) (by omega)
 have e8:step program n x t8=.running t9:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program,  writeNat, next]

 let t10:State := {t9 with pc:=40}
 have b10:WordBound B t10:=changePC_bound B t9 _ b9 (by omega)
 have e9:step program n x t9=.running t10:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program,  writeNat, next]

 have stop:step program n x t10=.halted t10:=by simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 11 t10:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.next b8 e8 (.next b9 e9 (.halt b10 stop))))))))))
 refine ⟨t10,11,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inr; apply Or.inl; exact ⟨Or.inr edge,by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,writeNat,next,h7077,h7080,h7001]

private lemma reverse (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (lo:d+4 ≤ g)(hi:g < 2*d+4):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=18}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := {t3 with pc:=37}
 have b4:WordBound B t4:=changePC_bound B t3 _ b3 (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program,      epoch,          finalBoundary]
  ; omega
 let t5:State := writeNat t4 7080 (0)
 have b5:WordBound B t5:=writeNat_bound B t4 7080 (0) b4
  (by simp only [   t4]; omega) (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program,  writeNat, next]

 let t6:State := writeNat t5 6703 ((g)-(d+4))
 have b6:WordBound B t6:=writeNat_bound B t5 6703 ((g)-(d+4)) b5
  (by simp only [t1, t2, t3, t4, t5,  writeNat, next]; omega) (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program, evalNat, writeNat, next,   epoch,         reverseStart]

 let t7:State := {t6 with pc:=40}
 have b7:WordBound B t7:=changePC_bound B t6 _ b6 (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next]

 have stop:step program n x t7=.halted t7:=by simp [t1, t2, t3, t4, t5, t6, t7, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 8 t7:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.halt b7 stop)))))))
 refine ⟨t7,8,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl; exact ⟨lo,hi,by simp [t1,t2,t3,t4,t5,t6,t7,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,writeNat,next,Nat.sub_sub]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7,writeNat,next,h7080,h6703]

private lemma last (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (edge:g=2*d+4):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=18}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := {t3 with pc:=19}
 have b4:WordBound B t4:=changePC_bound B t3 _ b3 (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program,      epoch,          finalBoundary]
  ; omega
 let t5:State := writeNat t4 7079 ((2*d+4)+(1))
 have b5:WordBound B t5:=writeNat_bound B t4 7079 ((2*d+4)+(1)) b4
  (by simp only [   t4]; omega) (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program, evalNat, writeNat, next,      one,       finalBoundary]

 let t6:State := {t5 with pc:=25}
 have b6:WordBound B t6:=changePC_bound B t5 _ b5 (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program,  writeNat, next,   epoch]
  ; omega
 let t7:State := writeNat t6 7080 (1)
 have b7:WordBound B t7:=writeNat_bound B t6 7080 (1) b6
  (by simp only [     t6]; omega) (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next]

 let t8:State := writeNat t7 7001 (0)
 have b8:WordBound B t8:=writeNat_bound B t7 7001 (0) b7
  (by simp only [t1, t2, t3, t4, t5, t6, t7,  writeNat, next]; omega) (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program,  writeNat, next]

 let t9:State := {t8 with pc:=40}
 have b9:WordBound B t9:=changePC_bound B t8 _ b8 (by omega)
 have e8:step program n x t8=.running t9:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program,  writeNat, next]

 have stop:step program n x t9=.halted t9:=by simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 10 t9:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.next b8 e8 (.halt b9 stop)))))))))
 refine ⟨t9,10,run,by omega,?_,?_⟩
 · exact Or.inl ⟨Or.inr edge,by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8, t9,writeNat,next,h7079,h7080,h7001]

private lemma inactive (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=11)(h:Header d g s)(bound:WordBound B s)(code:41 ≤ B)(_fit:2*d+5 ≤ B)
 (lo:2*d+5 ≤ g):
 ∃u t, BoundedExecution program n x B s t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame s u := by
 have epoch := h.epoch
 have duration := h.duration
 have zero := h.zero
 have one := h.one
 have two := h.two
 have three := h.three
 have four := h.four
 have five := h.five
 have nextBoundary := h.nextBoundary
 have reverseStart := h.reverseStart
 have finalBoundary := h.finalBoundary
 have gBound : g ≤ B := by simpa only [epoch] using bound.2.1 5920
 let t1:State := {s with pc:=12}
 have b1:WordBound B t1:=changePC_bound B s _ bound (by omega)
 have e0:step program n x s=.running t1:=by
  simp [t1, step, program,    pc,  epoch,   one]
  ; omega
 let t2:State := {t1 with pc:=13}
 have b2:WordBound B t2:=changePC_bound B t1 _ b1 (by omega)
 have e1:step program n x t1=.running t2:=by
  simp [t1, t2, step, program,      epoch,        nextBoundary]
  ; omega
 let t3:State := {t2 with pc:=18}
 have b3:WordBound B t3:=changePC_bound B t2 _ b2 (by omega)
 have e2:step program n x t2=.running t3:=by
  simp [t1, t2, t3, step, program,      epoch,         reverseStart]
  ; omega
 let t4:State := {t3 with pc:=19}
 have b4:WordBound B t4:=changePC_bound B t3 _ b3 (by omega)
 have e3:step program n x t3=.running t4:=by
  simp [t1, t2, t3, t4, step, program,      epoch,          finalBoundary]
  ; omega
 let t5:State := writeNat t4 7079 ((2*d+4)+(1))
 have b5:WordBound B t5:=writeNat_bound B t4 7079 ((2*d+4)+(1)) b4
  (by simp only [   t4]; omega) (by omega)
 have e4:step program n x t4=.running t5:=by
  simp [t1, t2, t3, t4, t5, step, program, evalNat, writeNat, next,      one,       finalBoundary]

 let t6:State := {t5 with pc:=21}
 have b6:WordBound B t6:=changePC_bound B t5 _ b5 (by omega)
 have e5:step program n x t5=.running t6:=by
  simp [t1, t2, t3, t4, t5, t6, step, program,  writeNat, next,   epoch]
  ; omega
 let t7:State := writeNat t6 7080 (2)
 have b7:WordBound B t7:=writeNat_bound B t6 7080 (2) b6
  (by simp only [     t6]; omega) (by omega)
 have e6:step program n x t6=.running t7:=by
  simp [t1, t2, t3, t4, t5, t6, t7, step, program,  writeNat, next]

 let t8:State := writeNat t7 6702 (0)
 have b8:WordBound B t8:=writeNat_bound B t7 6702 (0) b7
  (by simp only [t1, t2, t3, t4, t5, t6, t7,  writeNat, next]; omega) (by omega)
 have e7:step program n x t7=.running t8:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, step, program,  writeNat, next]

 let t9:State := writeNat t8 6705 (0)
 have b9:WordBound B t9:=writeNat_bound B t8 6705 (0) b8
  (by simp only [t1, t2, t3, t4, t5, t6, t7, t8,  writeNat, next]; omega) (by omega)
 have e8:step program n x t8=.running t9:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, step, program,  writeNat, next]

 let t10:State := {t9 with pc:=40}
 have b10:WordBound B t10:=changePC_bound B t9 _ b9 (by omega)
 have e9:step program n x t9=.running t10:=by
  simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program,  writeNat, next]

 have stop:step program n x t10=.halted t10:=by simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, step, program, writeNat, next]
 have run:BoundedExecution program n x B s 11 t10:=.next bound e0 (.next b1 e1 (.next b2 e2 (.next b3 e3 (.next b4 e4 (.next b5 e5 (.next b6 e6 (.next b7 e7 (.next b8 e8 (.next b9 e9 (.halt b10 stop))))))))))
 refine ⟨t10,11,run,by omega,?_,?_⟩
 · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; exact ⟨lo,by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next],by simp [t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,writeNat,next]⟩

 · refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
   intro j away
   have h7070:j ≠ 7070:=by intro eq; subst j; norm_num [modified] at away
   have h7071:j ≠ 7071:=by intro eq; subst j; norm_num [modified] at away
   have h7072:j ≠ 7072:=by intro eq; subst j; norm_num [modified] at away
   have h7073:j ≠ 7073:=by intro eq; subst j; norm_num [modified] at away
   have h7074:j ≠ 7074:=by intro eq; subst j; norm_num [modified] at away
   have h7075:j ≠ 7075:=by intro eq; subst j; norm_num [modified] at away
   have h7076:j ≠ 7076:=by intro eq; subst j; norm_num [modified] at away
   have h7077:j ≠ 7077:=by intro eq; subst j; norm_num [modified] at away
   have h7078:j ≠ 7078:=by intro eq; subst j; norm_num [modified] at away
   have h7079:j ≠ 7079:=by intro eq; subst j; norm_num [modified] at away
   have h7080:j ≠ 7080:=by intro eq; subst j; norm_num [modified] at away
   have h6702:j ≠ 6702:=by intro eq; subst j; norm_num [modified] at away
   have h6703:j ≠ 6703:=by intro eq; subst j; norm_num [modified] at away
   have h6705:j ≠ 6705:=by intro eq; subst j; norm_num [modified] at away
   have h7001:j ≠ 7001:=by intro eq; subst j; norm_num [modified] at away
   simp [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10,writeNat,next,h7079,h7080,h6702,h6705]


/-- Reads the real produced duration cell and charges every branch, arithmetic
instruction and the halt. No ready selector/phase output is assumed. -/
theorem execution (n B d g:Nat)(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(epoch:s.natReg 5920=g)(source:s.natHeap (s.natReg 6816)=some d)
 (bound:WordBound B s)(code:41 ≤ B)(fit:2*d+5 ≤ B):
 ∃u t,BoundedExecution program n x B s t u ∧ t ≤ 23 ∧ Selected d g u ∧ Frame s u:=by
 obtain ⟨a,boot,ap,h,frame⟩:=boot_execution n B d g x s pc epoch source bound code fit
 have finish : (∃u t,BoundedExecution program n x B a t u ∧ t ≤ 12 ∧ Selected d g u ∧ Frame a u) →
   ∃u t,BoundedExecution program n x B s t u ∧ t ≤ 23 ∧ Selected d g u ∧ Frame s u:=by
  rintro ⟨u,t,run,time,selected,af⟩
  exact ⟨u,11+t,boot.executes run,by omega,selected,frame.trans af⟩
 apply finish
 by_cases hfirst:g=0
 · exact first n B d g x a ap h boot.final_bound code fit hfirst
 by_cases hforward:g ≤ d
 · exact forward n B d g x a ap h boot.final_bound code fit (by omega) hforward
 by_cases early:g=d+1
 · exact laneOneEarly n B d g x a ap h boot.final_bound code fit early
 by_cases middle:g=d+2
 · exact laneTwo n B d g x a ap h boot.final_bound code fit middle
 by_cases late:g=d+3
 · exact laneOneLate n B d g x a ap h boot.final_bound code fit late
 by_cases hreverse:g < 2*d+4
 · exact reverse n B d g x a ap h boot.final_bound code fit (by omega) hreverse
 by_cases hlast:g=2*d+4
 · exact last n B d g x a ap h boot.final_bound code fit hlast
 · exact inactive n B d g x a ap h boot.final_bound code fit (by omega)

lemma Selected.tree_iff {d g:Nat}{u:State}(h:Selected d g u):
 u.natReg 7080=0 ↔ (1 ≤ g ∧ g ≤ d) ∨ (d+4 ≤ g ∧ g < 2*d+4):=by
 rcases h with h|h|h|h|h|h <;> rcases h with ⟨a,b,c⟩ <;> omega
lemma Selected.inactive_iff {d g:Nat}{u:State}(h:Selected d g u):
 u.natReg 7080=2 ↔ 2*d+5 ≤ g:=by
 rcases h with h|h|h|h|h|h <;> rcases h with ⟨a,b,c⟩ <;> omega
lemma Selected.boundary_iff {d g:Nat}{u:State}(h:Selected d g u):
 u.natReg 7080=1 ↔ g=0 ∨ g=d+1 ∨ g=d+2 ∨ g=d+3 ∨ g=2*d+4:=by
 rcases h with h|h|h|h|h|h <;> rcases h with ⟨a,b,c⟩ <;> omega
lemma Selected.forward_stage {d g:Nat}{u:State}(h:Selected d g u)(lo:1 ≤ g)(hi:g ≤ d):
 u.natReg 6703=d-g:=by
 rcases h with h|h|h|h|h|h <;> rcases h with ⟨a,b,c⟩ <;> omega
lemma Selected.reverse_stage {d g:Nat}{u:State}(h:Selected d g u)(lo:d+4 ≤ g)(hi:g < 2*d+4):
 u.natReg 6703=g-d-4:=by
 rcases h with h|h|h|h|h|h <;> rcases h with ⟨a,b,c⟩ <;> omega
lemma Frame.protected {s u:State}(h:Frame s u)(j:Nat)
 (region:(7050 ≤ j ∧ j < 7060) ∨ (5934 ≤ j ∧ j < 5940) ∨ j=7000):
 u.natReg j=s.natReg j:=by
 apply h.natReg
 simp [modified]
 omega

end
end ExactFourierCircuits.UniformEpochSelectorMachine
