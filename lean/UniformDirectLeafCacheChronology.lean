import UniformDirectLeafCacheSource
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafCacheChronology
open UniformTransposeDescriptorMachine UniformDirectLeafCacheSource
open scoped BigOperators

def duration (q : Record) : ℕ := if q.kind=0 then 1 else 28
def elapsed (qs : List Record) : ℕ := (qs.map duration).sum
def starts (t : ℕ) (qs : List Record) (j : ℕ) : ℕ := t+elapsed (qs.take j)
def cacheKind (q : Record) : ℕ := if q.kind=0 then 1 else 0
lemma elapsed_append (xs ys : List Record) : elapsed (xs++ys)=elapsed xs+elapsed ys := by
 simp [elapsed]
lemma elapsed_cons (q : Record) (qs : List Record) : elapsed (q::qs)=duration q+elapsed qs := by
 simp [elapsed]
lemma duration_transpose (q : Record) : duration q.transpose=duration q := rfl
lemma elapsed_transpose_reverse (qs : List Record) : elapsed (qs.reverse.map Record.transpose)=elapsed qs := by
 simp only [elapsed,List.map_map,Function.comp_def,duration_transpose,List.map_reverse,List.sum_reverse]
lemma starts_next (t : ℕ) (qs : List Record) (j : ℕ) (hj:j<qs.length) :
 starts t qs (j+1)=starts t qs j+duration qs[j] := by
 rw [starts,List.take_succ_eq_append_getElem hj,elapsed_append]
 simp [starts,elapsed,Nat.add_assoc]

lemma operation_valid {v : ℕ} (o K r : ℕ) (op : UniformDirectToeplitz.Operation v) (extent:o+v≤r) :
 InRange r K (ofOperation o K op) ∧ Legal (ofOperation o K op) := by
 cases op with
 | scale i =>
  have hi:=i.isLt
  simp only [ofOperation,InRange,Legal]
  constructor
  · omega
  · exact Or.inl ⟨trivial,trivial⟩
 | shear i j =>
  have hi:=i.isLt
  have hj:=j.isLt
  simp only [ofOperation,InRange,Legal]
  constructor
  · omega
  · exact Or.inr ⟨trivial,by omega⟩
lemma leaf_valid (v o K r : ℕ) (extent:o+v≤r) (q : Record) (hq:q∈leafRecords v o K) :
 InRange r K q ∧ Legal q := by
 obtain ⟨op,_hop,rfl⟩:=List.mem_map.mp hq
 exact operation_valid o K r op extent
lemma transpose_valid (r K : ℕ) (q : Record) (range:InRange r K q) (legal:Legal q) :
 InRange r K q.transpose ∧ Legal q.transpose := by
 rcases range with ⟨hd,he,hlo,hhi⟩
 constructor
 · exact ⟨he,hd,hlo,hhi⟩
 · rcases legal with ⟨kind,eq⟩|⟨kind,ne⟩
   · exact Or.inl ⟨kind,eq.symm⟩
   · exact Or.inr ⟨kind,Ne.symm ne⟩

lemma row_elapsed {v : ℕ} (o K : ℕ) (i : Fin v) :
 elapsed ((UniformDirectToeplitz.rowTopology i).map (ofOperation o K))=1+28*i.val := by
 simp [UniformDirectToeplitz.rowTopology,ofOperation,elapsed,duration,List.map_ofFn,List.sum_ofFn,Nat.mul_comm]
lemma partial_elapsed {v : ℕ} (o K k : ℕ) (hk:k≤v) :
 elapsed ((UniformDirectToeplitz.partialTopology k hk).map (ofOperation o K))=k+14*k*(k-1) := by
 induction k with
 | zero => rfl
 | succ k ih =>
  rw [UniformDirectToeplitz.partialTopology,List.map_append,elapsed_append,row_elapsed,ih]
  cases k with
  | zero => norm_num
  | succ k => simp only [Nat.succ_sub_one];ring
lemma leaf_elapsed (v o K : ℕ) : elapsed (leafRecords v o K)=v+14*v*(v-1) :=
 partial_elapsed o K v (le_refl _)
lemma transpose_elapsed (v o K : ℕ) :
 elapsed ((leafRecords v o K).reverse.map Record.transpose)=v+14*v*(v-1) := by
 rw [elapsed_transpose_reverse,leaf_elapsed]
end ExactFourierCircuits.UniformDirectLeafCacheChronology
