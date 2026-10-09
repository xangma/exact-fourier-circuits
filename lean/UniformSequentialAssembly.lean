import UniformBoundedAssembly
import UniformNatBlockMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSequentialAssembly
open UniformMachine UniformAssembly
noncomputable section

/-- Every helper halt becomes one charged jump to the following helper. The
last cell is the only final halt. All branch targets are literal relocations. -/
def code (base:ℕ):List Program→Program
 | []=>[.halt]
 | p::ps=>p.map (relocate base (base+p.length))++code (base+p.length) ps
def size:List Program→ℕ
 | []=>0
 | p::ps=>p.length+size ps
def program(ps:List Program):Program:=code 0 ps

lemma code_length(base:ℕ)(ps:List Program):(code base ps).length=size ps+1:=by
 induction ps generalizing base with
 | nil=>rfl
 | cons p ps ih=>simp only[code,List.length_append,List.length_map,ih,size];omega
lemma program_length(ps:List Program):(program ps).length=size ps+1:=code_length 0 ps
lemma size_append(ps qs:List Program):size (ps++qs)=size ps+size qs:=by
 induction ps with
 | nil=>simp [size]
 | cons p ps ih=>simp only[List.cons_append,size,ih];omega

lemma get_stage(base:ℕ)(before:List Program)(p:Program)(after:List Program)(i:ℕ)(hi:i<p.length):
 (code base (before++p::after))[size before+i]?=
 (p[i]?).map (relocate (base+size before) (base+size before+p.length)):=by
 induction before generalizing base with
 | nil=>simp [code,size,List.getElem?_append_left,hi]
 | cons q before ih=>
  simp only[List.cons_append,code,size]
  rw [show q.length+size before+i=q.length+(size before+i) by omega]
  rw [List.getElem?_append_right (by simp)]
  simp only[List.length_map,Nat.add_sub_cancel_left]
  simpa only[Nat.add_assoc] using ih (base+q.length)

lemma stage_code(before:List Program)(p:Program)(after:List Program):
 CodeAt p (program (before++p::after)) (size before) (size before+p.length):=by
 intro i hi
 simpa only[program,Nat.zero_add] using get_stage 0 before p after i hi

lemma final_halt(base:ℕ)(ps:List Program):(code base ps)[size ps]?=some .halt:=by
 induction ps generalizing base with
 | nil=>rfl
 | cons p ps ih=>
  simp only[code,size]
  rw[List.getElem?_append_right (by simp)]
  simpa only[List.length_map,Nat.add_sub_cancel_left] using ih (base+p.length)
lemma halt_at(ps:List Program):(program ps)[size ps]?=some .halt:=final_halt 0 ps

/-- Small outer header blocks execute the existing Nat operations, followed by
one charged halt which the sequential assembler relocates to a jump. -/
def natProgram (ops:List UniformNatBlockMachine.Op):Program:=
 ops.map UniformNatBlockMachine.Op.code++[.halt]
lemma natProgram_length(ops:List UniformNatBlockMachine.Op):
 (natProgram ops).length=ops.length+1:=by simp[natProgram]
lemma natProgram_code(ops:List UniformNatBlockMachine.Op):
 UniformNatBlockMachine.BlockAt ops (natProgram ops) 0:=by
 intro i hi
 simp [natProgram,hi,List.getElem?_append_left]
lemma natProgram_halt(ops:List UniformNatBlockMachine.Op):
 (natProgram ops)[ops.length]?=some .halt:=by
 simp[natProgram]
lemma block_pc(ops:List UniformNatBlockMachine.Op)(s:State):
 (UniformNatBlockMachine.applyBlock ops s).pc=s.pc+ops.length:=by
 induction ops generalizing s with
 | nil=>simp[UniformNatBlockMachine.applyBlock]
 | cons o ops ih=>rw[UniformNatBlockMachine.applyBlock,ih,UniformNatBlockMachine.Op.apply_pc,List.length_cons];omega

theorem nat_execution(ops:List UniformNatBlockMachine.Op){n B:ℕ}(x:Fin n→ℂ)(s:State)
 (pc:s.pc=0)(wb:WordBound B s)(fit:ops.length≤B)
 (reads:UniformNatBlockMachine.readable ops s)(peak:UniformNatBlockMachine.peak ops s≤B):
 BoundedExecution (natProgram ops) n x B s (ops.length+1)
 (UniformNatBlockMachine.applyBlock ops s):=by
 have run:=UniformNatBlockMachine.block_runs ops (natProgram ops) 0 n B x s
  (natProgram_code ops) pc wb (by simpa using fit) reads peak
 have finalPc:(UniformNatBlockMachine.applyBlock ops s).pc=ops.length:=by rw[block_pc,pc,Nat.zero_add]
 exact run.executes (.halt run.final_bound (by simp only[step,finalPc,natProgram_halt]))

end
end ExactFourierCircuits.UniformSequentialAssembly
