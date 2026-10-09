import UniformDirectLeafCacheLoopBoot
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopChoice
open UniformMachine UniformTensorMonomialMachine UniformDirectLeafCacheReader
open UniformDirectLeafCacheLoopProgram UniformDirectLeafCacheLoopData
noncomputable section

def bank (flip D E:ℕ):ℕ:=if flip=0 then D else E
def chosen (s:State) (flip D E:ℕ):State:=setPC (writeNat s 6600 (bank flip D E)) 23
lemma chosen_args {c:Config} {s:State} (flip D E:ℕ) (a:Args c s):
 Args {c with record:=bank flip D E} (chosen s flip D E):=by
 constructor <;>simp [chosen,setPC,writeNat,next,a.originalDirectory,a.conjugateDirectory,
  a.pool,a.rows,a.permutation,a.widths,a.markers,a.axis,a.entry,a.time]
lemma chosen_controls {r N i:ℕ} {s:State} (flip D E:ℕ) (a:Controls r N i s):
 Controls r N i (chosen s flip D E):=
 ⟨a.zero,a.one,a.four,a.count,a.index,a.tick,a.scalarStride,a.natStride⟩
lemma chosen_nat (s:State) (flip D E j:ℕ) (ne:j≠6600):
 (chosen s flip D E).natReg j=s.natReg j:=by simp [chosen,setPC,writeNat,next,ne]

theorem execution {r N i n B:ℕ} (flip D E:ℕ) (x:Fin n→ℂ) (s:State)
 (controls:Controls r N i s) (flag:s.natReg 6611=flip)
 (forward:s.natReg 5602=D) (transpose:s.natReg 5603=E)
 (pc:s.pc=19) (code:303≤B) (wb:WordBound B s):
 BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s
  (if flip=0 then 3 else 2) (chosen s flip D E):=by
 by_cases zero:flip=0
 · let a:=setPC s 20
   have aw:=changePC_bound B s 20 wb (by omega)
   have br:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 1 a:=
    .next wb (by simp [UniformMachine.step,pc,choose_branch,flag,controls.one,zero,a,setPC]) (.refl aw)
   let b:=writeNat a 6600 D
   have bw:=writeNat_bound B a 6600 D aw (by change 21≤B;omega) (by rw[←forward];exact wb.2.1 5602)
   have body:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B a 1 b:=
    .next aw (by simp [UniformMachine.step,a,setPC,choose_forward,controls.zero,forward,evalNat,b]) (.refl bw)
   have uw:=changePC_bound B b 23 bw (by omega)
   have jump:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B b 1 (chosen s flip D E):=
    .next bw (by simp [UniformMachine.step,b,writeNat,next,a,setPC,choose_jump,chosen,bank,zero]) (.refl (by simpa [chosen,bank,zero,b,a,setPC,writeNat,next] using uw))
   simpa only[zero,ite_true] using (br.trans body).trans jump
 · let a:=setPC s 22
   have aw:=changePC_bound B s 22 wb (by omega)
   have br:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B s 1 a:=
    .next wb (by simp [UniformMachine.step,pc,choose_branch,flag,controls.one,
     show ¬flip<1 by omega,a,setPC]) (.refl aw)
   have uw:=writeNat_bound B a 6600 E aw (by change 23≤B;omega) (by rw[←transpose];exact wb.2.1 5603)
   have body:BoundedRuns UniformDirectLeafCacheLoopProgram.program n x B a 1 (chosen s flip D E):=
    .next aw (by simp [UniformMachine.step,a,setPC,choose_transpose,controls.zero,transpose,evalNat,
     chosen,bank,zero,writeNat,next]) (.refl (by simpa [chosen,bank,zero,a,setPC,writeNat,next] using uw))
   simpa only[zero,ite_false] using br.trans body
end
end ExactFourierCircuits.UniformDirectLeafCacheLoopChoice
