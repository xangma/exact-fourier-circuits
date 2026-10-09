import UniformMatchingKernelGeometry
set_option autoImplicit false
namespace ExactFourierCircuits.UniformMatchingKernelAmbient
open UniformSectorPacking UniformSectorTensor UniformMatchingKernelGeometry
open UniformMatchingAxisTableMachine
open UniformColoring (Edge)
open OAI.ExactFourier
noncomputable section

def coordinate {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r):
 Fin (geometry r E hm hr hp).widths.sum ≃ Fin r:=
 finCongr (widths_sum r M (matching_capacity r E hm hr))
def orderedPosition {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r):
 (Σ _:Fin M,Fin 2) ↪ Fin r:=
 (position r E hm hr hp).trans (coordinate r E hm hr hp).toEmbedding
lemma ordered_position_value {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r)
 (i:Fin M) (t:Fin 2):(orderedPosition r E hm hr hp ⟨i,t⟩).val=
 if t.val=0 then (E i).left else (E i).right:=position_value r E hm hr hp i t

theorem kernel {M:ℕ} (r:ℕ) (E:Fin M→Edge) (hm:Matching E) (hr:InRange r E) (hp:2 ≤ r):
 Matrix.reindex (coordinate r E hm hr hp) (coordinate r E hm hr hp) (localKernel (geometry r E hm hr hp))=
 Embedded.matrix (orderedPosition r E hm hr hp) (Matrix.blockDiagonal' (fun _:Fin M=>C)):=by
 let e:=coordinate r E hm hr hp
 let pos:=position r E hm hr hp
 let blocks:=Matrix.blockDiagonal' (fun _:Fin M=>C)
 calc
  Matrix.reindex e e (localKernel (geometry r E hm hr hp))=
   Embedded.matrix e.toEmbedding (localKernel (geometry r E hm hr hp)):=(Embedded.matrix_equiv e _).symm
  _=Embedded.matrix e.toEmbedding (Embedded.matrix pos blocks):=
   congrArg (Embedded.matrix e.toEmbedding) (kernel_matrix r E hm hr hp)
  _=Embedded.matrix (pos.trans e.toEmbedding) blocks:=Embedded.matrix_comp pos e.toEmbedding blocks

/-- Ordered endpoints of an actual disjoint call family, including unions
of simultaneously active matching and scalar phases. -/
def edges {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r):Fin M→Edge:=fun i=>
 ⟨(p ⟨i,0⟩).val,(p ⟨i,1⟩).val,by
  intro equal
  have h:((⟨i,0⟩:Σ _:Fin M,Fin 2))=⟨i,1⟩:=p.injective (Fin.ext equal)
  have side:((0:Fin 2))=1:=congrArg (fun z:Σ _:Fin M,Fin 2=>z.2) h
  exact (by decide : (0:Fin 2)≠1) side⟩
lemma range {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r):InRange r (edges p):=by
 intro i
 exact ⟨(p ⟨i,0⟩).isLt,(p ⟨i,1⟩).isLt⟩
lemma matching {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r):Matching (edges p):=by
 intro i j ne
 simp only[UniformColoring.Conflict,UniformColoring.Incident,edges]
 rintro ((h|h)|(h|h))
 all_goals apply ne
 all_goals exact (congrArg Sigma.fst (p.injective (Fin.ext h))).symm
lemma printed_position {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r) (hp:2 ≤ r):
 orderedPosition r (edges p) (matching p) (range p) hp=p:=by
 apply Function.Embedding.ext
 rintro ⟨i,t⟩
 apply Fin.ext
 rw[ordered_position_value]
 fin_cases t <;>rfl

/-- Real55 geometry for any ordered call union carries precisely that union
of C blocks, with identity on all actual unmatched singleton coordinates. -/
theorem union_kernel {M r:ℕ} (p:(Σ _:Fin M,Fin 2) ↪ Fin r) (hp:2 ≤ r):
 Matrix.reindex (coordinate r (edges p) (matching p) (range p) hp)
  (coordinate r (edges p) (matching p) (range p) hp)
  (localKernel (geometry r (edges p) (matching p) (range p) hp))=
 Embedded.matrix p (Matrix.blockDiagonal' (fun _:Fin M=>C)):=by
 rw[kernel,printed_position]
end
end ExactFourierCircuits.UniformMatchingKernelAmbient
