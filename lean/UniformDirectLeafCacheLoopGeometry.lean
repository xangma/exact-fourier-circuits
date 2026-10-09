import UniformDirectLeafCacheLoopData
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheLoopGeometry
open UniformMachine UniformDirectLeafCacheReader UniformDirectLeafCacheExecution UniformDirectLeafCacheLoopData
open UniformDirectLeafCacheChronology UniformTransposeDescriptorMachine
noncomputable section

def slot (c:Config) (r:ℕ) (qs:List Record) (i:ℕ):Config:=
 ⟨c.record+4*i,c.originalDirectory,c.conjugateDirectory,c.pool+9*r*i,c.rows,
  c.permutation+(3*r+11)*i,c.widths+(3*r+11)*i,c.markers+(3*r+11)*i,
  c.axis+(3*r+11)*i,c.entry+(3*r+11)*i,starts c.time qs i⟩
lemma slot_zero (c:Config) (r:ℕ) (qs:List Record):slot c r qs 0=c:=by
 cases c;simp [slot,starts,elapsed]
lemma slot_next (c:Config) (r:ℕ) (qs:List Record) (i:ℕ) (hi:i<qs.length):
 nextConfig (slot c r qs i) r qs[i]=slot c r qs (i+1):=by
 simp only[nextConfig,slot,starts_next _ _ _ hi]
 congr 1 <;>ring

structure Layout (c:Config) (r A C B:ℕ) (qs:List Record):Prop where
 rows:c.rows+3≤c.permutation
 widths:c.widths=c.permutation+r
 markers:c.markers=c.permutation+2*r
 axis:c.axis=c.permutation+3*r
 entry:c.entry=c.permutation+3*r+4
 natEnd:c.permutation+(3*r+11)*qs.length+3*r+4≤B
 scalarEnd:c.pool+9*r*qs.length≤B
 constants:6≤c.pool
 descriptors:c.record+4*qs.length≤c.rows
 directory:c.originalDirectory+2≤c.rows
 conjugateDirectory:c.conjugateDirectory+1≤c.rows
 original:A+4*r≤c.pool
 conjugate:C+4*r≤c.pool
 time:c.time+elapsed qs≤B
 code:303≤B

lemma elapsed_take_le (qs:List Record) (i:ℕ):elapsed (qs.take i)≤elapsed qs:=by
 have eq:=List.take_append_drop i qs
 have h:=elapsed_append (qs.take i) (qs.drop i)
 rw[eq] at h;omega
lemma slot_bounds {c:Config} {r A C B:ℕ} {qs:List Record}
 (l:Layout c r A C B qs) (i:ℕ) (hi:i≤qs.length):Fits (slot c r qs i) B:=by
 have n:=l.natEnd;have sh:=l.scalarEnd
 have m:=Nat.mul_le_mul_left (3*r+11) hi
 have sc:=Nat.mul_le_mul_left (9*r) hi
 have tim:=elapsed_take_le qs i
 have p:=l.rows;have d:=l.descriptors
 have w:=l.widths;have u:=l.markers;have a:=l.axis;have e:=l.entry
 constructor
 · simp only[slot];nlinarith
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot,starts];have:=l.time;omega
lemma slot_layout {c:Config} {r A C B:ℕ} {qs:List Record}
 (l:Layout c r A C B qs) (i:ℕ) (hi:i<qs.length):
 UniformDirectLeafCacheExecution.Layout (slot c r qs i) r B:=by
 have n:=l.natEnd;have sh:=l.scalarEnd
 have step:=Nat.mul_le_mul_left (3*r+11) (show i+1≤qs.length by omega)
 have sc:=Nat.mul_le_mul_left (9*r) (show i+1≤qs.length by omega)
 have p:=l.rows;have w:=l.widths;have u:=l.markers;have a:=l.axis;have e:=l.entry
 constructor
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];omega
 · simp only[slot];nlinarith
 · simp only[slot];nlinarith
 · simp only[slot];have:=l.constants;omega
lemma slot_readonly {c:Config} {r A C B:ℕ} {qs:List Record}
 (l:Layout c r A C B qs) (i:ℕ) (hi:i<qs.length):
 (slot c r qs i).record+4≤c.rows:=by
 have:=l.descriptors;simp only[slot];omega

structure Inputs (c:Config) (r A C:ℕ) (qs:List Record) (s:State):Prop where
 records:∀(i:ℕ)(hi:i<qs.length),UniformDirectLeafCacheSource.At (c.record+4*i) qs[i] s
 original:s.natHeap c.originalDirectory=some A
 radix:s.natHeap (c.originalDirectory+1)=some r
 conjugate:s.natHeap c.conjugateDirectory=some C
 values:∀(i:ℕ)(hi:i<qs.length),UniformZeroFreePairShearMachine.Sources
  (UniformDirectLeafCacheSource.mu r (A+3*r) qs[i]) qs[i].coefficient
  (C+3*r+(qs[i].coefficient-(A+3*r))) s
 constants:UniformHadamardPairMachine.Constants s

lemma Inputs.transport {c:Config} {r A C B:ℕ} {qs:List Record} {s u:State}
 (h:Inputs c r A C qs s) (l:Layout c r A C B qs)
 (valid:∀q∈qs,UniformDirectLeafCacheSource.InRange r (A+3*r) q)
 (nh:∀j,j<c.rows→u.natHeap j=s.natHeap j)
 (sh:∀j,j<c.pool→u.scalarHeap j=s.scalarHeap j):Inputs c r A C qs u:=by
 constructor
 · intro i hi j
   have ji:=j.isLt
   have old:=h.records i hi j
   rw[nh _ (by have:=l.descriptors;omega)]
   exact old
 · rw[nh _ (by have:=l.directory;omega)];exact h.original
 · rw[nh _ (by have:=l.directory;omega)];exact h.radix
 · rw[nh _ (by have:=l.conjugateDirectory;omega)];exact h.conjugate
 · intro i hi
   have range:=valid qs[i] (List.getElem_mem hi)
   rcases h.values i hi with ⟨a,b⟩
   constructor
   · rw[sh _ (by have:=l.original;rcases range with ⟨_,_,_,_⟩;omega)];exact a
   · rw[sh _ (by have:=l.conjugate;rcases range with ⟨_,_,_,_⟩;omega)];exact b
 · rcases h.constants with ⟨a,b,c',d,e⟩
   exact ⟨(sh _ (by have:=l.constants;omega)).trans a,(sh _ (by have:=l.constants;omega)).trans b,
    (sh _ (by have:=l.constants;omega)).trans c',(sh _ (by have:=l.constants;omega)).trans d,
    (sh _ (by have:=l.constants;omega)).trans e⟩

end
end ExactFourierCircuits.UniformDirectLeafCacheLoopGeometry
