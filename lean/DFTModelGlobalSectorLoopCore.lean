import DFTModelGlobalSectorSavingCallerFrame
set_option autoImplicit false
/-! Paired refinement of the original finite sector child loop. All gathers
precede this loop; inverse transposes and scatters follow it. No source op is added. -/
namespace ExactFourierCircuits.DFTModelGlobalSectorLoop
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformMachine UniformAssembly
open UniformTensorMonomialMachine (Op applyBlock applyBlock_pc readable peak BlockAt block_runs setPC)
open UniformSameProgramSectorLoop (Cursor boot setup finish assembly)
open DFTModelAdmissibilityControl DFTModelAffine DFTModelRecursiveScalarSource
noncomputable section
attribute [local irreducible] UniformSameProgramSectorLoop.program DFTModelSavingProgram.program
abbrev W := DFTModelSavingNativeRoot.W
abbrev reserve := DFTModelSavingNativeRoot.R.reserve
abbrev child := UniformRecursiveSavingProgram.program
structure Geometry (W B F reserve A E:ℕ) (xs:List UniformSectorPacking.BlockState) where
 volume:ℕ
 fits:UniformAllSectorPaddingMachine.Fits xs volume
 ordered:UniformAllSectorPaddingMachine.Ordered xs
 pow:∀i,∀hi:i < xs.length,(xs[i]'hi).width=2^(xs[i]'hi).pairs
 low:3 ≤ A
 bank:A+W*volume ≤ F
 directory:E+5*xs.length ≤ F
 frontier:F ≤ B
 room:∀i,∀hi:i < xs.length,F+34*((xs[i]'hi).pairs+1)+reserve*((xs[i]'hi).pairs+1)*2^(xs[i]'hi).pairs ≤ B
 square:∀i,∀hi:i < xs.length,(2^(xs[i]'hi).pairs)^2 ≤ B
 qBound:∀i,∀hi:i < xs.length,(xs[i]'hi).pairs ≤ B
 widthBound:∀i,∀hi:i < xs.length,(xs[i]'hi).width ≤ B

def Table (W E A:ℕ) (xs:List UniformSectorPacking.BlockState) (s:State):Prop:=
 ∀i,∀hi:i < xs.length,UniformSectorBatchDirectoryMachine.BatchCell W E A i (xs[i]'hi) s
lemma cursor_withPC {M E F i:ℕ} {s:State} (h:Cursor M E F i s) (pc:ℕ):Cursor M E F i (setPC s pc):=
 ⟨h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five⟩
lemma setup_cursor {M E F i:ℕ} {s:State} (h:Cursor M E F i s):Cursor M E F i (applyBlock setup s):=by
 constructor <;>simp[setup,applyBlock,Op.apply,writeNat,next,h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five]
lemma root_cursor {M E F i:ℕ} {s u:State} (h:Cursor M E F i s)
 (kept:∀z,z=464 ∨(5890 ≤ z ∧z ≤ 5910) → u.natReg z=s.natReg z):Cursor M E F i u:=by
 constructor
 · exact (kept 5890 (Or.inr ⟨by omega,by omega⟩)).trans h.count
 · exact (kept 5891 (Or.inr ⟨by omega,by omega⟩)).trans h.one
 · exact (kept 5892 (Or.inr ⟨by omega,by omega⟩)).trans h.index
 · exact (kept 5893 (Or.inr ⟨by omega,by omega⟩)).trans h.directory
 · exact (kept 5894 (Or.inr ⟨by omega,by omega⟩)).trans h.fresh
 · exact (kept 5895 (Or.inr ⟨by omega,by omega⟩)).trans h.zero
 · exact (kept 5896 (Or.inr ⟨by omega,by omega⟩)).trans h.five
lemma finish_code (child:Program):BlockAt finish (assembly child) (17+child.length):=by
 have h:=UniformRankCrossPreparationMachine.block_of_segment finish
  (boot.map Op.code++[.branchLT 5892 5890 8 (child.length+19)]++setup.map Op.code++
   child.map (relocate 17 (17+child.length))) [.jump 7,.halt] (17+child.length)
  (by simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
   UniformSameProgramSectorLoop.setup_length,List.length_cons,List.length_nil])
 simpa only[assembly,List.append_assoc] using h
lemma jump_at (child:Program):(assembly child)[18+child.length]?=some (.jump 7):=by
 unfold assembly
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSameProgramSectorLoop.boot_length,UniformSameProgramSectorLoop.setup_length,
  UniformSameProgramSectorLoop.finish_length,List.length_cons,List.length_nil];omega)]
 simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
  UniformSameProgramSectorLoop.setup_length,UniformSameProgramSectorLoop.finish_length,
  List.length_cons,List.length_nil,show 18+child.length-(7+1+9+child.length+1)=0 by omega];rfl
lemma halt_at (child:Program):(assembly child)[19+child.length]?=some .halt:=by
 unfold assembly
 rw[List.getElem?_append_right (by simp only[List.length_append,List.length_map,
  UniformSameProgramSectorLoop.boot_length,UniformSameProgramSectorLoop.setup_length,
  UniformSameProgramSectorLoop.finish_length,List.length_cons,List.length_nil];omega)]
 simp only[List.length_append,List.length_map,UniformSameProgramSectorLoop.boot_length,
  UniformSameProgramSectorLoop.setup_length,UniformSameProgramSectorLoop.finish_length,
  List.length_cons,List.length_nil,show 19+child.length-(7+1+9+child.length+1)=1 by omega];rfl
lemma address_fit {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (i:ℕ) (hi:i < xs.length) (r t:ℕ)
 (hr:r < W) (ht:t < (xs[i]'hi).width):A+W*(xs[i]'hi).start+r*(xs[i]'hi).width+t < F:=by
 have fit:=g.fits i hi
 have wfit:=Nat.mul_le_mul_left W fit
 have rfit:=Nat.mul_le_mul_right (xs[i]'hi).width (show r+1 ≤ W by omega)
 have bank:=g.bank;nlinarith
lemma separate {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (i j:ℕ) (hi:i < xs.length) (hj:j < xs.length) (ne:j≠i)
 (r t:ℕ) (hr:r < W) (ht:t < (xs[j]'hj).width):
 A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t < A+W*(xs[i]'hi).start ∨
 A+W*(xs[i]'hi).start+W*(xs[i]'hi).width ≤ A+W*(xs[j]'hj).start+r*(xs[j]'hj).width+t:=by
 rcases lt_or_gt_of_ne ne with before|after
 · have h:=g.ordered j i hj hi before
   have x:=Nat.mul_le_mul_left W h
   have y:=Nat.mul_le_mul_right (xs[j]'hj).width (show r+1 ≤ W by omega)
   left;nlinarith
 · have h:=g.ordered i j hi hj after
   have x:=Nat.mul_le_mul_left W h
   right;nlinarith
lemma table_transfer {W B F reserve A E:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (s u:State) (old:Table W E A xs s)
 (kept:∀z,z < F → u.natHeap z=s.natHeap z):Table W E A xs u:=by
 intro i hi
 rcases old i hi with ⟨h0,h1,h2,h3,h4⟩
 have bound:=g.directory
 exact ⟨(kept _ (by omega)).trans h0,(kept _ (by omega)).trans h1,
  (kept _ (by omega)).trans h2,(kept _ (by omega)).trans h3,(kept _ (by omega)).trans h4⟩
def tick (child:Program) (s:State):State:=setPC
 (writeNat (setPC s (17+child.length)) 5892 (s.natReg 5892+s.natReg 5891)) 7
lemma tick_cursor {M E F i:ℕ} (child:Program) (s:State) (h:Cursor M E F i s):
 Cursor M E F (i+1) (tick child s):=by
 constructor <;>simp[tick,setPC,writeNat,next,h.count,h.one,h.index,h.directory,h.fresh,h.zero,h.five]
lemma global_separate {W B F reserve A E i:ℕ} {xs:List UniformSectorPacking.BlockState}
 (g:Geometry W B F reserve A E xs) (hi:i < xs.length) (z:ℕ) (outside:z < A ∨A+W*g.volume ≤ z):
 z < A+W*(xs[i]'hi).start ∨A+W*(xs[i]'hi).start+W*(xs[i]'hi).width ≤ z:=by
 have fits:=Nat.mul_le_mul_left W (g.fits i hi)
 rcases outside with h|h
 · left;omega
 · right;nlinarith

lemma stop {B n M E F:ℕ} (child:Program) (x:Fin n → ℂ) (s:State)
 (h:Cursor M E F M s) (pc:s.pc=7) (wb:WordBound B s) (code:child.length+20 ≤ B):
 BoundedExecution (assembly child) n x B s 2 (setPC s (19+child.length)):=by
 let u:=setPC s (19+child.length)
 have ub:=changePC_bound B s (19+child.length) wb (by omega)
 have last:BoundedExecution (assembly child) n x B u 1 u:=.halt ub
  (by simp[step,u,setPC,halt_at])
 exact .next wb (by simp[step,pc,UniformSameProgramSectorLoop.branch_at,h.index,h.count,u,setPC,
  Nat.add_comm child.length 19]) last


def input (v : ℕ→ℕ→Scalar) (st : UniformSectorPacking.BlockState) :
 Fin W→Fin (2^st.pairs)→Scalar := fun r j=>v r.val (st.start+j.val)
def patch (v v0 : ℕ→ℕ→Scalar) (st : UniformSectorPacking.BlockState) : Tape Tagged.T :=
 (run DFTModelSavingProgram.program ((st.pairs,Complex.I),paired (input v st) (input v0 st))).val
def bill (v v0 : ℕ→ℕ→Scalar) (st : UniformSectorPacking.BlockState) : ℕ :=
 (run DFTModelSavingProgram.program ((st.pairs,Complex.I),paired (input v st) (input v0 st))).work
def Pending (A : ℕ) (xs : List UniformSectorPacking.BlockState) (v : ℕ→ℕ→Scalar)
 (i : ℕ) (s : State) : Prop := ∀j,∀hj:j<xs.length,i≤j→
 UniformFixedNetworkShearChildMachine.Present (A+W*(xs[j]'hj).start) W
   (2^(xs[j]'hj).pairs) (input v (xs[j]'hj)) s
def Completed (A : ℕ) (xs : List UniformSectorPacking.BlockState) (v v0 : ℕ→ℕ→Scalar)
 (i : ℕ) (s s0 : State) : Prop := ∀ j,∀ hj : j < xs.length,j < i →
 ∃out out0 : Fin W→Fin (2^(xs[j]'hj).pairs)→Scalar,
 UniformFixedNetworkShearChildMachine.Present (A+W*(xs[j]'hj).start) W (2^(xs[j]'hj).pairs) out s ∧
 UniformFixedNetworkShearChildMachine.Present (A+W*(xs[j]'hj).start) W (2^(xs[j]'hj).pairs) out0 s0 ∧
 patch v v0 (xs[j]'hj)=paired out out0

lemma pending_step {B F A E i : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : Geometry W B F reserve A E xs) (hi : i<xs.length) (v : ℕ→ℕ→Scalar) (s u : State)
 (old : Pending A xs v i s)
 (out : ∀z,z<F→(z<A+W*(xs[i]'hi).start∨A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs≤z)→
 u.scalarHeap z=s.scalarHeap z) : Pending A xs v (i+1) u := by
 intro j hj after r t
 have ht:t.val<(xs[j]'hj).width:=by rw[g.pow j hj];exact t.isLt
 have eq:=out _ (address_fit g j hj r.val t.val r.isLt ht)
  (by rw[←g.pow i hi];exact separate g i j hi hj (by omega) r.val t.val r.isLt ht)
 rw[g.pow j hj] at eq
 exact eq.trans (old j hj (by omega) r t)

lemma completed_step {B F A E i : ℕ} {xs : List UniformSectorPacking.BlockState}
 (g : Geometry W B F reserve A E xs) (hi : i<xs.length) (v v0 : ℕ→ℕ→Scalar) (s s0 u u0 : State)
 (old : Completed A xs v v0 i s s0)
 (fresh : ∃out out0 : Fin W→Fin (2^(xs[i]'hi).pairs)→Scalar,
 UniformFixedNetworkShearChildMachine.Present (A+W*(xs[i]'hi).start) W (2^(xs[i]'hi).pairs) out u ∧
 UniformFixedNetworkShearChildMachine.Present (A+W*(xs[i]'hi).start) W (2^(xs[i]'hi).pairs) out0 u0 ∧
 patch v v0 (xs[i]'hi)=paired out out0)
 (frame : ∀z,z<F→(z<A+W*(xs[i]'hi).start∨A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs≤z)→
 u.scalarHeap z=s.scalarHeap z)
 (frame0 : ∀z,z<F→(z<A+W*(xs[i]'hi).start∨A+W*(xs[i]'hi).start+W*2^(xs[i]'hi).pairs≤z)→
 u0.scalarHeap z=s0.scalarHeap z) : Completed A xs v v0 (i+1) u u0 := by
 intro j hj less
 by_cases eq:j=i
 · subst j;exact fresh
 · obtain ⟨a,a0,data,data0,value⟩:=old j hj (by omega)
   refine ⟨a,a0,?_,?_,value⟩
   · intro r t
     have ht:t.val<(xs[j]'hj).width:=by rw[g.pow j hj];exact t.isLt
     have same:=frame _ (address_fit g j hj r.val t.val r.isLt ht)
       (by rw[←g.pow i hi];exact separate g i j hi hj eq r.val t.val r.isLt ht)
     rw[g.pow j hj] at same
     exact same.trans (data r t)
   · intro r t
     have ht:t.val<(xs[j]'hj).width:=by rw[g.pow j hj];exact t.isLt
     have same:=frame0 _ (address_fit g j hj r.val t.val r.isLt ht)
       (by rw[←g.pow i hi];exact separate g i j hi hj eq r.val t.val r.isLt ht)
     rw[g.pow j hj] at same
     exact same.trans (data0 r t)

end
end ExactFourierCircuits.DFTModelGlobalSectorLoop
