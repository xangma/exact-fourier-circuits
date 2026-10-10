import DFTModelCacheDescriptorFits
import UniformLocalCacheTimingRows

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheDescriptor
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformWorkspaceSearchMachine (targets sources targetSize sourceSize)
open UniformLocalRectangleDescriptors (row rows)
noncomputable section

abbrev Row7 := p w (p w (p w (p w (p w (p w w)))))
abbrev RowsInput := p Pair w
abbrev RowInput := p RowsInput w

def rowEncode (q : UniformLocalRectangleDescriptors.Row) : Row7.T :=
  (q.width,(q.offset,(q.a,(q.e,(q.split,(q.i0,q.j0))))))
def listTape {α : Type} (xs : List α) : Tape α := ⟨xs.length,fun i=>xs[i.val]'i.isLt⟩

theorem tape_ext {α : Type} {x y : Tape α} (h : x.len=y.len)
    (hp : ∀i j,i.val=j.val→x.pos i=y.pos j) : x=y := by
  cases x with
  | mk m f =>
    cases y with
    | mk n g =>
      dsimp only at h
      subst n
      congr 1
      funext i
      exact hp i i rfl

theorem listTape_ofFn {α : Type} {n : ℕ} (f : Fin n→α) :
    listTape (List.ofFn f)=(⟨n,f⟩ : Tape α) := by
  apply tape_ext (List.length_ofFn)
  intro i j hij
  change (List.ofFn f)[i.val]'_=f j
  rw [List.getElem_ofFn]
  congr 1
  exact Fin.ext hij


def rowsPair : Prog false RowsInput Pair :=
  .fork (.comp (.atom .fst) (.atom .fst)) (.atom .snd)
def rowCount : Prog false RowsInput w :=
  nat .mul (.comp rowsPair targetCount) (.comp rowsPair sourceCount)
def rowV : Prog false RowInput w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .fst))
def rowO : Prog false RowInput w := .comp (.atom .fst) (.comp (.atom .fst) (.atom .snd))
def rowB : Prog false RowInput w := .comp (.atom .fst) (.atom .snd)
def rowI : Prog false RowInput w :=
  nat .div (.atom .snd) (.comp (.atom .fst) (.comp rowsPair sourceCount))
def rowJ : Prog false RowInput w :=
  nat .mod (.atom .snd) (.comp (.atom .fst) (.comp rowsPair sourceCount))
def rowCoordinates : Prog false RowInput ChunkPair :=
  .fork (.fork rowV rowB) (.fork rowI rowJ)
def rowA : Prog false RowInput w := .comp rowCoordinates (.comp pairSizes (.atom .fst))
def rowE : Prog false RowInput w := .comp rowCoordinates (.comp pairSizes (.atom .snd))
def rowSplit : Prog false RowInput w := .comp rowV split
def rowI0 : Prog false RowInput w := nat .add rowSplit (nat .mul rowI rowB)
def rowJ0 : Prog false RowInput w := nat .mul rowJ rowB

def rowCell : Prog false RowInput Row7 :=
  .fork rowV (.fork rowO (.fork rowA (.fork rowE (.fork rowSplit (.fork rowI0 rowJ0)))))
def rectangleRows : Prog false RowsInput (Ty.a Row7) := .tab rowCount rowCell

attribute [local irreducible] pairSizes split targetCount sourceCount

theorem rowCount_value (v o b : ℕ) :
    (run rowCount ((v,o),b)).val=targets v b*sources v b := by
  change (run targetCount (v,b)).val*(run sourceCount (v,b)).val=_
  rw [targetCount_value,sourceCount_value]

theorem rowCell_value (v o b h : ℕ) :
    (run rowCell (((v,o),b),h)).val=
      rowEncode (row v o b (h/sources v b) (h%sources v b)) := by
  have count : (run (.comp (.atom .fst) (.comp rowsPair sourceCount) :
      Prog false RowInput w) (((v,o),b),h)).val=sources v b := sourceCount_value v b
  have coords : (run rowCoordinates (((v,o),b),h)).val=
      ((v,b),(h/sources v b,h%sources v b)) := by
    change ((v,b),((h/(run sourceCount (v,b)).val),(h%(run sourceCount (v,b)).val)))=_
    rw [sourceCount_value]
  have sizes := pairSizes_value v b (h/sources v b) (h%sources v b)
  change (v,(o,((run pairSizes (run rowCoordinates (((v,o),b),h)).val).val.1,
    ((run pairSizes (run rowCoordinates (((v,o),b),h)).val).val.2,
      ((run split v).val,((run rowI0 (((v,o),b),h)).val,
        (run rowJ0 (((v,o),b),h)).val))))))=_
  rw [coords,sizes,split_value]
  have hi0 : (run rowI0 (((v,o),b),h)).val=v/2+(h/sources v b)*b := by
    change (run split v).val+(h/(run sourceCount (v,b)).val)*b=_
    rw [split_value,sourceCount_value]
    rfl
  have hj0 : (run rowJ0 (((v,o),b),h)).val=(h%sources v b)*b := by
    change (h%(run sourceCount (v,b)).val)*b=_
    rw [sourceCount_value]
  rw [hi0,hj0]
  rfl

theorem rectangleRows_value (v o b : ℕ) :
    (run rectangleRows ((v,o),b)).val=listTape ((rows v o b).map rowEncode) := by
  change (Bill.tab (run rowCount ((v,o),b)).val Row7.blank
    (fun h=>run rowCell (((v,o),b),h))).val=_
  rw [ModelEquivalenceInterpreter.tab_value,rowCount_value]
  rw [UniformLocalCacheTimingRows.rows_ofFn,List.map_ofFn,listTape_ofFn]
  apply tape_ext
  · rfl
  intro h h' eqv
  change (run rowCell (((v,o),b),h.val)).val=
    rowEncode (UniformLocalCacheTimingRows.indexedRow v o b h')
  rw [rowCell_value,eqv]
  have hh : h'.val<targets v b*sources v b := h'.isLt
  have src : 0<sources v b := by nlinarith
  let p:=finProdFinEquiv.symm h'
  have eq : h'.val=p.1.val*sources v b+p.2.val :=
    UniformLocalCacheTimingRows.pair_index v b h'.val h'.isLt
  have pl : p.2.val<sources v b := p.2.isLt
  have jm : h'.val%sources v b=p.2.val := by
    rw [eq,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add]
    simp only [Nat.mod_eq_of_lt pl]
  have id : h'.val/sources v b=p.1.val := by
    rw [eq,Nat.mul_comm p.1.val (sources v b),Nat.mul_add_div src,Nat.div_eq_of_lt pl]
    omega
  rw [id,jm]
  rfl

end
end ExactFourierCircuits.DFTModelCacheDescriptor
