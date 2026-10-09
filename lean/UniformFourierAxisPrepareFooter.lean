import UniformFourierAxisWorkspaceHeader

set_option autoImplicit false
namespace ExactFourierCircuits.UniformFourierAxisPrepareFooter
open UniformMachine UniformAssembly UniformNatBlockMachine
noncomputable section

/-- The common charged footer for tree, boundary and inactive epochs. -/
def block:List Op:=[.literal 7065 0,.literal 7067 4,
 .binary .add 6766 7050 7065,.binary .add 6767 6705 7065,
 .binary .add 6768 6800 7065,.binary .add 6769 7057 7065,
 .binary .add 6770 7053 7065,.binary .add 6772 7052 7065,
 .binary .add 5926 7054 7065,.binary .add 5927 7055 7065,
 .binary .add 5928 7056 7065,.binary .mul 5929 5922 7067,
 .binary .add 5929 5929 6028,.binary .add 5930 5923 7065,
 .binary .add 6801 6819 7065,.binary .add 6802 6821 7065,
 .binary .add 5934 7058 7065,.binary .add 5935 7059 7065]
lemma block_length:block.length=18:=rfl

structure Args(r N S count j physical directory cacheN cacheS:ℕ)(s:State):Prop where
 workspace:UniformFourierAxisWorkspaceHeader.Header r N S s
 count:s.natReg 6705=count
 radix:s.natReg 6800=r
 axis:s.natReg 5922=j
 physical:s.natReg 6028=physical
 directory:s.natReg 5923=directory
 cacheNat:s.natReg 6819=cacheN
 cacheScalar:s.natReg 6821=cacheS

structure Result(r N S count j physical directory cacheN cacheS:ℕ)(s:State):Prop where
 selected:s.natReg 6766=(UniformFourierAxisWorkspace.axisBank r N S).selected
 count:s.natReg 6767=count
 radix:s.natReg 6768=r
 pool:s.natReg 6769=(UniformFourierAxisWorkspace.axisBank r N S).pool
 rows:s.natReg 6770=(UniformFourierAxisWorkspace.axisBank r N S).rawRows
 phase:s.natReg 6772=(UniformFourierAxisWorkspace.axisBank r N S).phase
 permutation:s.natReg 5926=(UniformFourierAxisWorkspace.axisBank r N S).permutation
 widths:s.natReg 5927=(UniformFourierAxisWorkspace.axisBank r N S).widths
 markers:s.natReg 5928=(UniformFourierAxisWorkspace.axisBank r N S).markers
 physical:s.natReg 5929=physical+4*j
 directory:s.natReg 5930=directory
 cacheNat:s.natReg 6801=cacheN
 cacheScalar:s.natReg 6802=cacheS
 nextNat:s.natReg 5934=(UniformFourierAxisWorkspace.axisBank r N S).endNat
 nextScalar:s.natReg 5935=(UniformFourierAxisWorkspace.axisBank r N S).endScalar

lemma values{r N S count j physical directory cacheN cacheS:ℕ}{s:State}
 (a:Args r N S count j physical directory cacheN cacheS s):
 Result r N S count j physical directory cacheN cacheS (applyBlock block s):=by
 constructor <;>simp [block,applyBlock,Op.apply,evalNat,writeNat,next,
 a.workspace.selected,a.count,a.radix,a.workspace.pool,a.workspace.rows,a.workspace.phase,
 a.workspace.permutation,a.workspace.widths,a.workspace.markers,a.axis,a.physical,a.directory,
 a.cacheNat,a.cacheScalar,a.workspace.endNat,a.workspace.endScalar,Nat.mul_comm,Nat.add_comm]

lemma safe{B:ℕ}{s:State}(bound:WordBound B s)(code:4 ≤ B)
 (axisFit:s.natReg 6028+4*s.natReg 5922 ≤ B):
 readable block s ∧peak block s ≤ B:=by
 have s0:=bound.2.1 7050
 have s1:=bound.2.1 6705
 have s2:=bound.2.1 6800
 have s3:=bound.2.1 7057
 have s4:=bound.2.1 7053
 have s5:=bound.2.1 7052
 have s6:=bound.2.1 7054
 have s7:=bound.2.1 7055
 have s8:=bound.2.1 7056
 have s9:=bound.2.1 5923
 have s10:=bound.2.1 6819
 have s11:=bound.2.1 6821
 have s12:=bound.2.1 7058
 have s13:=bound.2.1 7059
 simp [block,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,Nat.mul_comm]
 omega

theorem execution{B n start r N S count j physical directory cacheN cacheS:ℕ}
 (program:Program)(x:Fin n→ℂ)(s:State)
 (args:Args r N S count j physical directory cacheN cacheS s)
 (code:BlockAt block program start)(pc:s.pc=start)(extent:start+18 ≤ B)
 (small:4 ≤ B)(physicalFit:physical+4*j ≤ B)(bound:WordBound B s):
 BoundedRuns program n x B s 18 (applyBlock block s) ∧
 Result r N S count j physical directory cacheN cacheS (applyBlock block s):=by
 have fit:s.natReg 6028+4*s.natReg 5922 ≤ B:=by rw [args.physical,args.axis];exact physicalFit
 have good:=safe bound small fit
 have run:=block_runs block program start n B x s code pc bound
  (by simpa only [block_length] using extent) good.1 good.2
 exact ⟨by simpa only [block_length] using run,values args⟩

lemma frame(s:State):
 (applyBlock block s).natHeap=s.natHeap ∧(applyBlock block s).scalarHeap=s.scalarHeap ∧
 (applyBlock block s).scalarReg=s.scalarReg ∧(applyBlock block s).outputs=s.outputs ∧
 (applyBlock block s).rootOrders=s.rootOrders ∧
 (∀j,(j<6766 ∨6772<j)→j≠7065→j≠7067→(j<5926 ∨5930<j)→
 j≠6801→j≠6802→j≠5934→j≠5935→(applyBlock block s).natReg j=s.natReg j):=by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro j a b c d e f g h
 simp(disch:=omega)[block,applyBlock,Op.apply,evalNat,writeNat,next]
end
end ExactFourierCircuits.UniformFourierAxisPrepareFooter
