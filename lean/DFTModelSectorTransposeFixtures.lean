import DFTModelSectorTransposeScatterSource
import DFTModelSectorTransposeCall

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelSectorTransposeFixtures
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelSectorTranspose
noncomputable section

def old : Tape ℕ := Tape.tab 16 (fun j => 100+j)
def child : Tape ℕ := Tape.tab 4 (fun j => 900+j)
example : (run (gather w) ((2,(8,(3,2))),old)).val.len=4 := by
 exact gather_length w 2 8 3 2 old
example : (run (gather w) ((2,(8,(3,2))),old)).val.look 3 0=112 := by
 rw [gather_value]
 rfl

example : (run (gather w) ((2,(8,(3,2))),old)).work=260 := by
 rw [gather_work]
example : (run (argument w) ((1,(0:ℂ)),((2,(8,3)),old))).val.2.2.len=4 := by
 exact argument_length w 1 2 8 3 0 old
example : (run (argument w) ((0,(0:ℂ)),((2,(8,7)),old))).val.2.2.len=2 := by
 exact argument_length w 0 2 8 7 0 old
example : (run (scatter w) (((2,(8,(3,2))),old),child)).val.2.look 2 0=902 := by
 rw [scatter_value]
 rfl

example : (run (scatter w) (((2,(8,(3,2))),old),child)).work=64 := by
 rw [scatter_work]
example : (run (reader w) ((((2,(8,(3,2))),old),child),11)).val=902 := by
 rw [reader_value]
 norm_num [overlay,old,child,Tape.look,Tape.tab,Ty.blank]; rfl
example : (run (reader w) ((((2,(8,(3,2))),old),child),10)).val=110 := by
 rw [reader_value]
 norm_num [overlay,old,child,Tape.look,Tape.tab,Ty.blank]; rfl
example : (run (reader w) ((((2,(8,(3,2))),old),child),13)).val=113 := by
 rw [reader_value]
 norm_num [overlay,old,child,Tape.look,Tape.tab,Ty.blank]; rfl
example : (run (reader w) ((((2,(8,(3,2))),old),child),11)).work≤133 := by
 exact reader_work w 2 8 3 2 11 old child
example : (run (gather w) ((0,(8,(3,2))),old)).val.len=0 := by
 exact gather_length w 0 8 3 2 old

end
end ExactFourierCircuits.DFTModelSectorTransposeFixtures
