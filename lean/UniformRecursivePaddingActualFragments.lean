import UniformRecursivePaddingFragments
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursivePaddingFragments
open UniformMachine UniformRecursivePaddingFrames
noncomputable section

lemma init_bits (n B F saved role count:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=P.address .paddingInit)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (sp:s.natReg 2865=saved)(d:s.natReg 2854=role)(c:s.natReg 2855=count)
 (low:6≤F)(bound:WordBound B s)(code:P.program.length≤B)(endBound:role+count≤B)
 (run:BoundedRuns P.program n x B s 11 u):u.natReg 5300=s.natReg 5300:=
 init_bits_generic P.program (P.address .paddingInit) (P.address .paddingTest)
  UniformRecursivePaddingControl.init_code UniformRecursivePaddingControl.init_jump
  n B F saved role count x s u pc w one sp d c low bound
  (UniformRecursiveParentReturn.code_bound .paddingInit 11 B rfl code)
  (UniformRecursiveParentReturn.start_bound .paddingTest B code) endBound run

lemma test_bits (n B F role last:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=P.address .paddingTest)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (current:s.natHeap (F-4)=some role)(endpoint:s.natHeap (F-3)=some last)(low:6≤F)
 (bound:WordBound B s)(code:P.program.length≤B)
 (run:BoundedRuns P.program n x B s 6 u):u.natReg 5300=s.natReg 5300:=
 test_bits_generic P.program (P.address .paddingTest) (P.address .paddingPatch) (P.address .paddingFinish)
  UniformRecursivePaddingControl.test_code UniformRecursivePaddingControl.test_branch
  n B F role last x s u pc w one current endpoint low bound
  (UniformRecursiveParentReturn.code_bound .paddingTest 6 B rfl code)
  (UniformRecursiveParentReturn.start_bound .paddingPatch B code)
  (UniformRecursiveParentReturn.start_bound .paddingFinish B code) run

lemma next_bits (n B F role:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=P.address .paddingNext)(w:s.natReg 4123=F)(one:s.natReg 4153=1)
 (current:s.natHeap (F-4)=some role)(low:6≤F)(bound:WordBound B s)(code:P.program.length≤B)(increment:role+1≤B)
 (run:BoundedRuns P.program n x B s 6 u):u.natReg 5300=s.natReg 5300:=
 next_bits_generic P.program (P.address .paddingNext) (P.address .paddingTest)
  UniformRecursivePaddingControl.next_code UniformRecursivePaddingControl.next_jump
  n B F role x s u pc w one current low bound
  (UniformRecursiveParentReturn.code_bound .paddingNext 6 B rfl code)
  (UniformRecursiveParentReturn.start_bound .paddingTest B code) increment run

lemma finish_bits (n B F saved:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=P.address .paddingFinish)(w:s.natReg 4123=F)
 (stored:s.natHeap (F-5)=some saved)(low:6≤F)(bound:WordBound B s)(code:P.program.length≤B)
 (run:BoundedRuns P.program n x B s 4 u):u.natReg 5300=s.natReg 5300:=
 finish_bits_generic P.program (P.address .paddingFinish) (P.address .loop)
  UniformRecursivePaddingControl.finish_code UniformRecursivePaddingControl.finish_jump
  n B F saved x s u pc w stored low bound
  (UniformRecursiveParentReturn.code_bound .paddingFinish 4 B rfl code)
  (UniformRecursiveParentReturn.start_bound .loop B code) run

lemma residual_init_cursor (n B F dimension recordEnd inverse:ℕ)(x:Fin n→ℂ)(s u:State)
 (pc:s.pc=P.address .residualInit)(one:s.natReg 4153=1)(dim:s.natReg 2857=dimension)
 (endHeader:s.natReg 2865=recordEnd)(iv:s.natReg 2856=inverse)(bound:WordBound B s)(code:P.program.length≤B)
 (run:BoundedRuns P.program n x B s 5 u):u.natReg 2850=s.natReg 2850:=
 residual_init_cursor_generic P.program (P.address .residualInit) (P.address .directionTest)
  UniformRecursiveResidualControl.init_code UniformRecursiveResidualControl.init_jump
  n B F dimension recordEnd inverse x s u pc one dim endHeader iv bound
  (UniformRecursiveParentReturn.code_bound .residualInit 5 B rfl code)
  (UniformRecursiveParentReturn.start_bound .directionTest B code) run
end
end ExactFourierCircuits.UniformRecursivePaddingFragments
