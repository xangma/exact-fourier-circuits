import UniformDirectLeafForestIteration
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafForestFrame
open UniformMachine UniformDirectLeafForestData UniformDirectLeafForestModel UniformDirectLeafForestState
open UniformLocalCacheTreeMachine
noncomputable section

structure Frame(p:Parameters)(visits:List Visit)(s u:State):Prop where
 scalarOutside:∀a,(a<p.start.pool∨(position p visits visits.length).pool≤a)→u.scalarHeap a=s.scalarHeap a
 natBefore:∀a,a<p.start.permutation→(a<p.start.rows∨p.start.rows+3≤a)→
  (a<p.ranges∨p.ranges+2*visits.length≤a)→u.natHeap a=s.natHeap a
 natHigh:∀a,p.transpose+4*p.radix^2≤a→u.natHeap a=s.natHeap a
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders

lemma Frame.refl(p:Parameters)(visits:List Visit)(s:State):Frame p visits s s:=
 ⟨fun _ _=>rfl,fun _ _ _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
lemma Frame.trans {p:Parameters}{visits:List Visit}{s u v:State}
 (a:Frame p visits s u)(b:Frame p visits u v):Frame p visits s v:=
 ⟨fun j h=>(b.scalarOutside j h).trans (a.scalarOutside j h),
  fun j h h' h''=>(b.natBefore j h h' h'').trans (a.natBefore j h h' h''),
  fun j h=>(b.natHigh j h).trans (a.natHigh j h),b.outputs.trans a.outputs,b.roots.trans a.roots⟩
lemma of_step {p:Parameters}{visits:List Visit}{i:ℕ}{s u:State}(hi:i<visits.length)
 (f:UniformDirectLeafForestLeafStep.StepFrame p visits i s u):Frame p visits s u:=by
 have last:=UniformDirectLeafForestPrefix.before_mono visits (show i+1≤visits.length by omega)
 constructor
 · intro a h
   apply f.scalarOutside a
   simp only[position] at h ⊢
   rcases h with low|high
   · exact Or.inl (by omega)
   · have mul:=Nat.mul_le_mul_left (9*p.radix) last
     exact Or.inr (by omega)
 · intro a h rows ranges
   exact f.natBefore a (by simp only[position];omega) rows (by omega)
 · exact f.natHigh
 · exact f.outputs
 · exact f.roots
end
end ExactFourierCircuits.UniformDirectLeafForestFrame
