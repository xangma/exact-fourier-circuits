import UniformToeplitzCrossDAG
import UniformConvolutionTopologyMachine
import UniformBoundedAssembly
import UniformPreparationRowTableMachine

set_option autoImplicit false

namespace ExactFourierCircuits.UniformToeplitzCrossTopologyMachine
open UniformMachine OAI.ExactFourier
open UniformRadixTwoDAG (width width_pos)
open UniformConvolutionTopologyMachine (Row encode)

def G (K : ℕ) := UniformConvolutionDAG.total K

def coefficientRef (K slot c : ℕ) : ℕ :=
  if c < width K then c else width K+slot*width K+(c-width K)

/-- The odd slot consumes the preceding convolution's reversed output.
The even slot consumes reversed original inputs. Both use the physical zero port e. -/
def dataRef (K e slot r : ℕ) : ℕ :=
  if r < width K then
    if r < e then
      if slot%2=0 then e-1-r else e+1+slot*G K-width K+(e-1-r)
    else e
  else e+1+slot*G K+(r-width K)

def remapRow (K e slot : ℕ) (r : Row) : Row :=
  { r with
    left := dataRef K e slot r.left
    right := if r.opcode < 2 then dataRef K e slot r.right else 0
    payload := if r.kind=1 then coefficientRef K slot r.payload else r.payload }

def mapExpr {r s : ℕ} (c : Fin r → Fin s) (f : ℕ → ℕ) : UniformConvolutionDAG.Expr r ℕ → UniformConvolutionDAG.Expr s ℕ
  | .add a b=>.add (f a) (f b)
  | .sub a b=>.sub (f a) (f b)
  | .scale q a=>.scale (UniformToeplitzCrossDAG.mapCoefficient c q) (f a)

def remapExpr (K e : ℕ) (slot : Fin 6) :=
  mapExpr (UniformToeplitzCrossDAG.coefficientEmbedding K slot) (dataRef K e slot.val)

theorem embedding_val (K : ℕ) (slot : Fin 6) (i : Fin (width K+width K)) :
    (UniformToeplitzCrossDAG.coefficientEmbedding K slot i).val=coefficientRef K slot.val i.val := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp [UniformToeplitzCrossDAG.coefficientEmbedding,coefficientRef,j.isLt]
  · simp only [UniformToeplitzCrossDAG.coefficientEmbedding,Fin.addCases_right]
    simp [coefficientRef,finProdFinEquiv,Nat.mul_comm]
    omega

theorem encode_remap (K e : ℕ) (slot : Fin 6) (g : UniformConvolutionDAG.Expr (width K+width K) ℕ) :
    encode (remapExpr K e slot g)=remapRow K e slot.val (encode g) := by
  cases g with
  | add a b | sub a b=>simp [remapExpr,mapExpr,encode,remapRow]
  | scale c a=>
    cases c <;> simp [remapExpr,mapExpr,encode,remapRow,UniformToeplitzCrossDAG.mapCoefficient,embedding_val]

theorem encode_embedding (K e : ℕ) (slot : Fin 6) (g : UniformConvolutionDAG.Expr (width K+width K) ℕ) :
    encode (mapExpr (UniformToeplitzCrossDAG.coefficientEmbedding K slot) (dataRef K e slot.val) g)=remapRow K e slot.val (encode g) :=
  encode_remap K e slot g

def branchOutput (K e branch i : ℕ) : ℕ := e+1+(2*branch+2)*G K-width K+i

def slotRows (K e slot : ℕ) : List Row := (UniformConvolutionDAG.records K).map (fun g=>remapRow K e slot (encode g))
def firstAdds (K a e : ℕ) : List Row := List.ofFn (fun i : Fin a=>⟨0,branchOutput K e 0 i.val,branchOutput K e 1 i.val,0,0⟩)
def secondAdds (K a e : ℕ) : List Row := List.ofFn (fun i : Fin a=>⟨0,e+1+6*G K+i.val,branchOutput K e 2 i.val,0,0⟩)
def crossRows (K a e : ℕ) : List Row := (List.range 6).flatMap (slotRows K e)++firstAdds K a e++secondAdds K a e

theorem slotRows_length (K e slot : ℕ) : (slotRows K e slot).length=G K := by simp [slotRows,G]
theorem crossRows_length (K a e : ℕ) : (crossRows K a e).length=6*G K+2*a := by
  simp [crossRows,slotRows_length,firstAdds,secondAdds,List.range_succ]
  omega



theorem mapExpr_map {r s : ℕ} (c : Fin r → Fin s) (f g : ℕ → ℕ) (e : UniformConvolutionDAG.Expr r ℕ) :
    mapExpr c f (e.map g)=mapExpr c (f ∘ g) e := by cases e <;> rfl

theorem mapExpr_refs {r s : ℕ} (c : Fin r → Fin s) (f : ℕ → ℕ) (g : UniformConvolutionDAG.Expr r ℕ) :
    (mapExpr c f g).refs=g.refs.map f := by cases g <;> rfl

theorem mapExpr_id {r : ℕ} (f : ℕ → ℕ) (g : UniformConvolutionDAG.Expr r ℕ) : mapExpr id f g=g.map f := by
  cases g with
  | add a b | sub a b=>rfl
  | scale c a=>cases c <;> rfl

theorem mapExpr_then_map {r s : ℕ} (c : Fin r → Fin s) (f g : ℕ → ℕ) (e : UniformConvolutionDAG.Expr r ℕ) :
    (mapExpr c f e).map g=mapExpr c (g ∘ f) e := by cases e <;> rfl

theorem mapProgram_records {r s n t : ℕ} (f : Fin r → Fin s) (p : UniformReplayPrint.Program r n t) :
    UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.mapProgram f p)=
      (UniformToeplitzCrossDAG.programRecords p).map (mapExpr f id) := by
  induction p with
  | nil=>rfl
  | step p g ih=>
    simp only [UniformToeplitzCrossDAG.mapProgram,UniformToeplitzCrossDAG.programRecords,ih,List.map_append,List.map_singleton]
    congr 1
    cases g <;> rfl

def liftRef (e off r : ℕ) : ℕ := if r < e+1 then r else off+r

theorem appendWire_identity (e t r : ℕ) :
    UniformToeplitzCrossDAG.appendWire (fun i : Fin (e+1)=> (⟨i.val,by have h:=i.isLt;omega⟩ : Fin (e+1+t))) r=liftRef e t r := by
  unfold UniformToeplitzCrossDAG.appendWire liftRef
  by_cases h : r < e+1
  · simp only [dite_eq_left h,ite_eq_left h]
  · simp only [dite_eq_right h,ite_eq_right h];omega

def reverseWire (e r : ℕ) : ℕ := if r < e then e-1-r else r

theorem reverseWire_fin (e : ℕ) (i : Fin (e+1)) :
    ((Fin.snoc (fun j : Fin e=>j.rev.castSucc) (Fin.last e) : Fin (e+1) → Fin (e+1)) i).val=reverseWire e i.val := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [reverseWire]
  · simp [reverseWire,j.isLt,Fin.val_rev];omega

theorem reverse_appendWire (e r : ℕ) :
    UniformToeplitzCrossDAG.appendWire (n:=e) (m:=e) (t:=0) (Fin.snoc (fun j : Fin e=>j.rev.castSucc) (Fin.last e)) r=reverseWire e r := by
  unfold UniformToeplitzCrossDAG.appendWire
  split_ifs with h
  · exact reverseWire_fin e ⟨r,h⟩
  · simp [reverseWire,show ¬r < e by omega];omega

theorem first_dataRef (K e r : ℕ) :
    reverseWire e (UniformConvolutionDAG.wireAddress e (UniformConvolutionDAG.padInputs K e) r)=dataRef K e 0 r := by
  by_cases hN : r < width K
  · by_cases he : r < e
    · simp [UniformConvolutionDAG.wireAddress,UniformConvolutionDAG.padInputs,hN,he,reverseWire,dataRef]
    · simp [UniformConvolutionDAG.wireAddress,UniformConvolutionDAG.padInputs,hN,he,reverseWire,dataRef]
  · simp [UniformConvolutionDAG.wireAddress,hN,reverseWire,dataRef,show ¬e+1+(r-width K) < e by omega]

theorem convolution_output_val (K e : ℕ) (i : Fin (width K)) :
    (UniformConvolutionDAG.outputIndex K e i).val=e+1+G K-width K+i.val := by
  simp only [UniformConvolutionDAG.outputIndex,UniformConvolutionDAG.nodeFin_normalize,Fin.val_mk]
  unfold G UniformConvolutionDAG.total
  omega

theorem convolution_records (K e : ℕ) :
    UniformToeplitzCrossDAG.programRecords (UniformConvolutionDAG.paddedProgram K e)=
      (UniformConvolutionDAG.records K).map (fun g=>g.map (UniformConvolutionDAG.wireAddress e (UniformConvolutionDAG.padInputs K e))) := by
  simp only [UniformConvolutionDAG.paddedProgram,UniformConvolutionDAG.program,UniformToeplitzCrossDAG.convolutionPrefix_records,
    List.ofFn_eq_map,UniformConvolutionDAG.records,List.map_map,Function.comp_def]

theorem first_records (K e : ℕ) (he : e ≤ width K) (b : Fin 3) :
    UniformToeplitzCrossDAG.programRecords (((UniformToeplitzCrossDAG.convolutionDAG K e e he).reverseInputs.reverseOutputs).mapCoefficients
      (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.firstSlot b))).program=
      (UniformConvolutionDAG.records K).map (mapExpr (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.firstSlot b)) (dataRef K e 0)) := by
  simp only [UniformToeplitzCrossDAG.DAG.mapCoefficients,UniformToeplitzCrossDAG.DAG.reverseOutputs,
    UniformToeplitzCrossDAG.DAG.reverseInputs,UniformToeplitzCrossDAG.convolutionDAG,mapProgram_records,
    UniformToeplitzCrossDAG.appendProgram_records,UniformToeplitzCrossDAG.programRecords,List.nil_append,
    convolution_records,List.map_map,Function.comp_def,mapExpr_map,reverse_appendWire]
  congr 1
  funext g
  congr 1
  funext r
  exact first_dataRef K e r



def firstDAG (K e : ℕ) (he : e ≤ width K) (b : Fin 3) :=
  (((UniformToeplitzCrossDAG.convolutionDAG K e e he).reverseInputs.reverseOutputs).mapCoefficients
    (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.firstSlot b)))

theorem G_width (K : ℕ) : width K ≤ G K := by unfold G UniformConvolutionDAG.total;omega

theorem firstDAG_size (K e : ℕ) (he : e ≤ width K) (b : Fin 3) : (firstDAG K e he b).size=G K := by
  simp [firstDAG,UniformToeplitzCrossDAG.DAG.mapCoefficients,UniformToeplitzCrossDAG.DAG.reverseInputs,
    UniformToeplitzCrossDAG.DAG.reverseOutputs,UniformToeplitzCrossDAG.convolutionDAG,G]

theorem firstDAG_output (K e : ℕ) (he : e ≤ width K) (b : Fin 3) (i : Fin e) :
    ((firstDAG K e he b).outputs i).val=e+1+G K-width K+(e-1-i.val) := by
  have hg:=G_width K
  have hi:=i.isLt
  simp only [firstDAG,UniformToeplitzCrossDAG.DAG.mapCoefficients,UniformToeplitzCrossDAG.DAG.reverseOutputs,
    UniformToeplitzCrossDAG.DAG.reverseInputs,UniformToeplitzCrossDAG.convolutionDAG,Function.comp_apply,
    UniformToeplitzCrossDAG.appendIndex_val,convolution_output_val,Fin.val_rev]
  unfold UniformToeplitzCrossDAG.appendWire
  split_ifs <;> omega

theorem second_append_data (K e : ℕ) (he : e ≤ width K) (b : Fin 3) (r : ℕ) :
    UniformToeplitzCrossDAG.appendWire (Fin.snoc (firstDAG K e he b).outputs ⟨e,by omega⟩)
      (UniformConvolutionDAG.wireAddress e (UniformConvolutionDAG.padInputs K e) r)=dataRef K e 1 r := by
  have hg:=G_width K
  have hsize:=firstDAG_size K e he b
  by_cases hN : r < width K
  · by_cases hr : r < e
    · simp only [UniformConvolutionDAG.wireAddress,dite_eq_left hN,UniformConvolutionDAG.padInputs,dite_eq_left hr,Fin.val_mk]
      unfold UniformToeplitzCrossDAG.appendWire
      rw [dite_eq_left (show r < e+1 by omega)]
      rw [show (⟨r,by omega⟩ : Fin (e+1))=(⟨r,hr⟩ : Fin e).castSucc from rfl,Fin.snoc_castSucc,firstDAG_output]
      simp [dataRef,hN,hr]
    · simp only [UniformConvolutionDAG.wireAddress,dite_eq_left hN,UniformConvolutionDAG.padInputs,dite_eq_right hr,Fin.val_last]
      unfold UniformToeplitzCrossDAG.appendWire
      rw [dite_eq_left (show e < e+1 by omega)]
      change ((Fin.snoc (firstDAG K e he b).outputs (⟨e,by omega⟩ : Fin (e+1+(firstDAG K e he b).size)) : Fin (e+1) → Fin (e+1+(firstDAG K e he b).size)) (Fin.last e)).val=dataRef K e 1 r
      simp [dataRef,hN,hr]
  · simp only [UniformConvolutionDAG.wireAddress,dite_eq_right hN]
    unfold UniformToeplitzCrossDAG.appendWire
    rw [dite_eq_right (show ¬e+1+(r-width K) < e+1 by omega)]
    simp only [dataRef,ite_eq_right hN,hsize]
    omega

theorem kernel_records (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) (b : Fin 3) :
    UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.kernelDAG K a e ha he b).program=
      (UniformConvolutionDAG.records K).map (mapExpr (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.firstSlot b)) (dataRef K e 0)) ++
      (UniformConvolutionDAG.records K).map (mapExpr (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.secondSlot b)) (dataRef K e 1)) := by
  change UniformToeplitzCrossDAG.programRecords ((UniformToeplitzCrossDAG.convolutionDAG K e a ha).mapCoefficients
    (UniformToeplitzCrossDAG.coefficientEmbedding K (UniformToeplitzCrossDAG.secondSlot b)) |>.comp (firstDAG K e he b)).program=_
  simp only [UniformToeplitzCrossDAG.DAG.comp,UniformToeplitzCrossDAG.appendProgram_records]
  have hf:=first_records K e he b
  change UniformToeplitzCrossDAG.programRecords (firstDAG K e he b).program=_ at hf
  rw [hf]
  simp only [UniformToeplitzCrossDAG.DAG.mapCoefficients,UniformToeplitzCrossDAG.convolutionDAG,
    mapProgram_records,convolution_records,List.map_map,Function.comp_def,mapExpr_map,mapExpr_then_map]
  congr 1
  congr 1
  funext g
  congr 1
  funext r
  exact second_append_data K e he b r



theorem kernel_size (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) (b : Fin 3) :
    (UniformToeplitzCrossDAG.kernelDAG K a e ha he b).size=2*G K := by
  simp [UniformToeplitzCrossDAG.kernelDAG,UniformToeplitzCrossDAG.DAG.comp,
    UniformToeplitzCrossDAG.DAG.mapCoefficients,UniformToeplitzCrossDAG.DAG.reverseInputs,
    UniformToeplitzCrossDAG.DAG.reverseOutputs,UniformToeplitzCrossDAG.convolutionDAG,G];omega

theorem kernel_output (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) (b : Fin 3) (i : Fin a) :
    ((UniformToeplitzCrossDAG.kernelDAG K a e ha he b).outputs i).val=branchOutput K e 0 i.val := by
  have hG:=G_width K
  change (appendIndex (Fin.snoc (firstDAG K e he b).outputs ⟨e,by omega⟩)
    (UniformConvolutionDAG.outputIndex K e ⟨i.val,i.isLt.trans_le ha⟩)).val=_
  rw [UniformToeplitzCrossDAG.appendIndex_val,convolution_output_val]
  unfold UniformToeplitzCrossDAG.appendWire
  rw [dite_eq_right (show ¬e+1+G K-width K+i.val < e+1 by omega),firstDAG_size]
  unfold branchOutput
  simp only
  omega

theorem lift_first (K e b r : ℕ) : liftRef e (2*b*G K) (dataRef K e 0 r)=dataRef K e (2*b) r := by
  by_cases hN : r < width K
  · by_cases he : r < e
    · simp [dataRef,liftRef,hN,he,show e-1-r < e+1 by omega]
    · simp [dataRef,liftRef,hN,he]
  · simp [dataRef,liftRef,hN,show ¬e+1+(r-width K) < e+1 by omega]
    omega

theorem lift_second (K e b r : ℕ) : liftRef e (2*b*G K) (dataRef K e 1 r)=dataRef K e (2*b+1) r := by
  have hG:=G_width K
  have hm : (2*b+1)*G K=2*b*G K+G K := by ring
  by_cases hN : r < width K
  · by_cases he : r < e
    · simp [dataRef,liftRef,hN,he,hm,show ¬e+1+G K-width K+(e-1-r) < e+1 by omega]
      omega
    · simp [dataRef,liftRef,hN,he]
  · simp [dataRef,liftRef,hN,hm,show ¬e+1+G K+(r-width K) < e+1 by omega]
    omega

theorem lifted_kernel_rows (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) (b : Fin 3) :
    ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.kernelDAG K a e ha he b).program).map
      (fun g=>g.map (liftRef e (2*b.val*G K)))).map encode=
        slotRows K e (2*b.val)++slotRows K e (2*b.val+1) := by
  rw [kernel_records]
  simp only [List.map_append,List.map_map,Function.comp_def,mapExpr_then_map]
  have hf : (fun x=>liftRef e (2*b.val*G K) (dataRef K e 0 x))=dataRef K e (2*b.val) := funext (lift_first K e b.val)
  have hs : (fun x=>liftRef e (2*b.val*G K) (dataRef K e 1 x))=dataRef K e (2*b.val+1) := funext (lift_second K e b.val)
  rw [hf,hs]
  change (UniformConvolutionDAG.records K).map (fun g=>encode (remapExpr K e (UniformToeplitzCrossDAG.firstSlot b) g)) ++
    (UniformConvolutionDAG.records K).map (fun g=>encode (remapExpr K e (UniformToeplitzCrossDAG.secondSlot b) g))=_
  simp only [encode_remap,UniformToeplitzCrossDAG.firstSlot,UniformToeplitzCrossDAG.secondSlot,slotRows]

theorem appendWire_identity_function (e t : ℕ) :
    UniformToeplitzCrossDAG.appendWire (fun i : Fin (e+1)=> (⟨i.val,by have h:=i.isLt;omega⟩ : Fin (e+1+t)))=liftRef e t :=
  funext (appendWire_identity e t)

theorem sumThree_records {r e a : ℕ} (A B D : UniformToeplitzCrossDAG.DAG r e a) :
    UniformToeplitzCrossDAG.programRecords (A.sumThree B D).program=
      UniformToeplitzCrossDAG.programRecords A.program++
      (UniformToeplitzCrossDAG.programRecords B.program).map (fun g=>g.map (liftRef e A.size))++
      (UniformToeplitzCrossDAG.programRecords D.program).map (fun g=>g.map (liftRef e (A.size+B.size)))++
      List.ofFn (fun i : Fin a=>UniformConvolutionDAG.Expr.add (A.outputs i).val (liftRef e A.size (B.outputs i).val))++
      List.ofFn (fun i : Fin a=>UniformConvolutionDAG.Expr.add (e+1+(A.size+B.size+D.size)+i.val)
        (liftRef e (A.size+B.size) (D.outputs i).val)) := by
  simp only [UniformToeplitzCrossDAG.DAG.sumThree,UniformToeplitzCrossDAG.emitProgram_records,
    UniformToeplitzCrossDAG.appendProgram_records,appendWire_identity_function,appendWire_identity,UniformToeplitzCrossDAG.gateRecord,
    keepIndex,UniformToeplitzCrossDAG.appendIndex_val,gateIndex,
    List.append_assoc]

theorem lift_zero (e r : ℕ) : liftRef e 0 r=r := by unfold liftRef;split_ifs <;> omega

theorem expr_map_zero {r : ℕ} (e : ℕ) (g : UniformConvolutionDAG.Expr r ℕ) : g.map (liftRef e 0)=g := by
  cases g <;> simp [UniformConvolutionDAG.Expr.map,lift_zero]

theorem branchOutput_lift (K e b i : ℕ) :
    liftRef e (2*b*G K) (branchOutput K e 0 i)=branchOutput K e b i := by
  have hg:=G_width K
  have hm : (2*b+2)*G K=2*b*G K+2*G K := by ring
  unfold branchOutput liftRef
  simp only [Nat.mul_zero,Nat.zero_add,ite_eq_right (show ¬e+1+2*G K-width K+i < e+1 by omega),hm]
  omega

theorem crossRows_typed (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) :
    crossRows K a e=(UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG K a e ha he).program).map encode := by
  have h0:=lifted_kernel_rows K a e ha he 0
  have h1:=lifted_kernel_rows K a e ha he 1
  have h2:=lifted_kernel_rows K a e ha he 2
  simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_mul,List.map_map,Function.comp_def,expr_map_zero,Nat.zero_add] at h0
  norm_num at h1 h2
  unfold UniformToeplitzCrossDAG.crossDAG
  rw [sumThree_records]
  simp only [kernel_size,List.map_append,List.map_map]
  rw [h0,h1]
  have heq : 2*G K+2*G K=4*G K := by omega
  rw [heq,h2]
  simp only [List.map_ofFn,Function.comp_def,encode,kernel_output]
  have heq2 : 4*G K+2*G K=6*G K := by omega
  rw [heq2]
  have h1lift (i : ℕ) : liftRef e (2*G K) (branchOutput K e 0 i)=branchOutput K e 1 i := by simpa using branchOutput_lift K e 1 i
  have h2lift (i : ℕ) : liftRef e (4*G K) (branchOutput K e 0 i)=branchOutput K e 2 i := by simpa using branchOutput_lift K e 2 i
  simp [crossRows,firstAdds,secondAdds,List.range_succ,List.append_assoc,h1lift,h2lift]

/-- Caller Nat560=height,561=target count,562=source count,563=temporary
convolution tape,564=final tape. The imported producer is actually executed once. -/
def head : Program := [.natLiteral 580 0,.natBinary .add 400 560 580,.natBinary .add 401 563 580]

def tail : Program := [
  .natBinary .add 565 402 580,
  .natBinary .add 566 404 580,
  .natLiteral 581 1,
  .natLiteral 582 2,
  .natLiteral 583 5,
  .natLiteral 584 6,
  .natLiteral 567 0,
  .natBinary .add 570 564 580,
  .branchLT 567 584 166 235,
  .natBinary .mul 571 567 566,
  .natBinary .mod 572 567 582,
  .natBinary .add 573 562 581,
  .natBinary .add 573 573 571,
  .natBinary .sub 573 573 565,
  .natLiteral 568 0,
  .natBinary .add 569 563 580,
  .branchLT 568 566 174 233,
  .loadNat 574 569,
  .natBinary .add 569 569 581,
  .loadNat 575 569,
  .natBinary .add 569 569 581,
  .loadNat 576 569,
  .natBinary .add 569 569 581,
  .loadNat 577 569,
  .natBinary .add 569 569 581,
  .loadNat 578 569,
  .natBinary .add 569 569 581,
  .branchLT 575 565 185 193,
  .branchLT 575 562 186 191,
  .natBinary .sub 579 562 581,
  .natBinary .sub 575 579 575,
  .branchLT 572 581 198 189,
  .natBinary .add 575 575 573,
  .jump 198,
  .natBinary .add 575 562 580,
  .jump 198,
  .natBinary .sub 579 575 565,
  .natBinary .add 575 562 581,
  .natBinary .add 575 575 571,
  .natBinary .add 575 575 579,
  .jump 198,
  .branchLT 574 582 199 213,
  .branchLT 576 565 200 208,
  .branchLT 576 562 201 206,
  .natBinary .sub 579 562 581,
  .natBinary .sub 576 579 576,
  .branchLT 572 581 215 204,
  .natBinary .add 576 576 573,
  .jump 215,
  .natBinary .add 576 562 580,
  .jump 215,
  .natBinary .sub 579 576 565,
  .natBinary .add 576 562 581,
  .natBinary .add 576 576 571,
  .natBinary .add 576 576 579,
  .jump 215,
  .natLiteral 576 0,
  .jump 215,
  .branchLT 577 581 221 216,
  .branchLT 578 565 221 217,
  .natBinary .sub 578 578 565,
  .natBinary .mul 587 567 565,
  .natBinary .add 578 578 587,
  .natBinary .add 578 578 565,
  .storeNat 570 574,
  .natBinary .add 570 570 581,
  .storeNat 570 575,
  .natBinary .add 570 570 581,
  .storeNat 570 576,
  .natBinary .add 570 570 581,
  .storeNat 570 577,
  .natBinary .add 570 570 581,
  .storeNat 570 578,
  .natBinary .add 570 570 581,
  .natBinary .add 568 568 581,
  .jump 173,
  .natBinary .add 567 567 581,
  .jump 165,
  .natBinary .add 591 562 581,
  .natBinary .mul 597 582 566,
  .natBinary .add 591 591 597,
  .natBinary .sub 591 591 565,
  .natBinary .add 592 591 597,
  .natBinary .add 593 592 597,
  .natBinary .add 594 593 565,
  .natLiteral 590 0,
  .natLiteral 598 0,
  .branchLT 590 561 245 266,
  .natLiteral 574 0,
  .natLiteral 577 0,
  .natLiteral 578 0,
  .branchLT 598 581 249 252,
  .natBinary .add 575 591 590,
  .natBinary .add 576 592 590,
  .jump 254,
  .natBinary .add 575 594 590,
  .natBinary .add 576 593 590,
  .storeNat 570 574,
  .natBinary .add 570 570 581,
  .storeNat 570 575,
  .natBinary .add 570 570 581,
  .storeNat 570 576,
  .natBinary .add 570 570 581,
  .storeNat 570 577,
  .natBinary .add 570 570 581,
  .storeNat 570 578,
  .natBinary .add 570 570 581,
  .natBinary .add 590 590 581,
  .jump 244,
  .branchLT 598 581 267 270,
  .natLiteral 598 1,
  .natLiteral 590 0,
  .jump 244,
  .halt]

def program : Program := UniformAssembly.embed head UniformConvolutionTopologyMachine.program tail 157

theorem head_length : head.length=3 := rfl
theorem tail_length : tail.length=114 := rfl
theorem program_length : program.length=271 := by
  simp only [program,UniformAssembly.embed,List.length_append,List.length_map,head_length,tail_length,UniformConvolutionTopologyMachine.program_length]

theorem convolution_code : UniformAssembly.CodeAt UniformConvolutionTopologyMachine.program program 3 157 := by
  simpa only [head_length,program] using UniformAssembly.embed_code head UniformConvolutionTopologyMachine.program tail 157



noncomputable section
open UniformPreparationRowTableMachine (Op applyBlock readable peak block_runs applyBlock_pc)

def Params (K a e c d : ℕ) (s : State) : Prop :=
  s.natReg 560=K ∧ s.natReg 561=a ∧ s.natReg 562=e ∧ s.natReg 563=c ∧ s.natReg 564=d

def Frame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
  u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
  ∀ i,((i < 70 ∨ 96 < i) ∧ (i < 400 ∨ 419 < i) ∧ (i < 565 ∨ 599 < i)) → u.natReg i=s.natReg i

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
  ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
    fun i hi=>(h'.2.2.2.2 i hi).trans (h.2.2.2.2 i hi)⟩

def safe : Instruction → Prop
  | .natLiteral d _ | .natBinary _ d _ _ | .loadNat d _=>
      (70 ≤ d ∧ d ≤ 96) ∨ (400 ≤ d ∧ d ≤ 419) ∨ (565 ≤ d ∧ d ≤ 599)
  | .storeNat _ _ | .branchLT _ _ _ _ | .jump _ | .halt=>True
  | _=>False

theorem safe_relocate (base ret : ℕ) (q : Instruction) : safe (UniformAssembly.relocate base ret q)=safe q := by cases q <;> rfl

theorem safe_convolution (q : Instruction) (h : UniformConvolutionTopologyMachine.safe q) : safe q := by
  cases q <;> simp_all [safe,UniformConvolutionTopologyMachine.safe] <;> omega

theorem program_safe : ∀q∈program,safe q := by
  intro q hq
  simp only [program,UniformAssembly.embed,List.mem_append,List.mem_map] at hq
  rcases hq with (h|⟨a,ha,rfl⟩)|h
  · have hh : ∀q∈head,safe q := by simp [head,safe]
    exact hh q h
  · rw [safe_relocate];exact safe_convolution a (UniformConvolutionTopologyMachine.program_safe a ha)
  · have hh : ∀q∈tail,safe q := by simp [tail,safe]
    exact hh q h

theorem write_frame (s : State) (d v : ℕ)
    (hd : (70 ≤ d ∧ d ≤ 96) ∨ (400 ≤ d ∧ d ≤ 419) ∨ (565 ≤ d ∧ d ≤ 599)) : Frame s (writeNat s d v) := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  simp [writeNat,next,Function.update_of_ne (show i ≠ d by omega)]

theorem step_frame (n : ℕ) (x : Fin n → ℂ) (s u : State) (h : step program n x s=.running u) : Frame s u := by
  cases hc : program[s.pc]? with
  | none=>simp [step,hc] at h
  | some q=>
    have hq:=program_safe q (List.mem_of_getElem? hc)
    cases q <;> try {change False at hq;exact False.elim hq}
    case natLiteral d v=>
      simp only [step,hc,StepResult.running.injEq] at h;subst u;exact write_frame s d v hq
    case natBinary op d l r=>
      cases he : evalNat op (s.natReg l) (s.natReg r) with
      | none=>simp [step,hc,he] at h
      | some v=>simp only [step,hc,he,StepResult.running.injEq] at h;subst u;exact write_frame s d v hq
    case loadNat d a=>
      cases he : s.natHeap (s.natReg a) with
      | none=>simp [step,hc,he] at h
      | some v=>simp only [step,hc,he,StepResult.running.injEq] at h;subst u;exact write_frame s d v hq
    case storeNat a r=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case branchLT l r y n=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case jump pc=>simp only [step,hc,StepResult.running.injEq] at h;subst u;exact Frame.refl s
    case halt=>simp [step,hc] at h

theorem execution_frame {n t : ℕ} {x : Fin n → ℂ} {s u : State} (h : Executes program n x s t u) : Frame s u := by
  induction h with
  | halt _=>exact Frame.refl _
  | next hs _ ih=>exact (step_frame _ _ _ _ hs).trans ih

theorem runs_frame {n t : ℕ} {x : Fin n → ℂ} {s u : State} (h : Runs program n x s t u) : Frame s u := by
  induction h with
  | refl _=>exact Frame.refl _
  | next hs _ ih=>exact (step_frame _ _ _ _ hs).trans ih

theorem Params.frame {K a e c d : ℕ} {s u : State} (h : Params K a e c d s) (hf : Frame s u) : Params K a e c d u := by
  rcases h with ⟨hK,ha,he,hc,hd⟩
  exact ⟨(hf.2.2.2.2 560 (by omega)).trans hK,(hf.2.2.2.2 561 (by omega)).trans ha,
    (hf.2.2.2.2 562 (by omega)).trans he,(hf.2.2.2.2 563 (by omega)).trans hc,(hf.2.2.2.2 564 (by omega)).trans hd⟩

theorem saved_headers {s u : State} (h : Frame s u) (i : ℕ) (hi : 100 ≤ i ∧ i ≤ 106) : u.natReg i=s.natReg i :=
  h.2.2.2.2 i (by omega)

def budget (K a e c d : ℕ) : ℕ := c+d+5*(7*G K+2*a)+UniformRadixInstructionMachine.cap (width K) (UniformRadixTwoDAG.count K) K+
  10000*(width K+G K+a+e+K+1)^2

theorem budget_code (K a e c d : ℕ) : 1000 ≤ budget K a e c d := by
  have hN:=width_pos K
  have hsq : 1 ≤ (width K+G K+a+e+K+1)^2 := Nat.succ_le_iff.mpr (pow_pos (by omega) 2)
  unfold budget
  omega

theorem budget_convolution (K a e c d : ℕ) : UniformConvolutionTopologyMachine.allocation K c ≤ budget K a e c d := by
  have hN:=width_pos K
  have hsq : 1 ≤ (width K+G K+a+e+K+1)^2 := Nat.succ_le_iff.mpr (pow_pos (by omega) 2)
  unfold UniformConvolutionTopologyMachine.allocation budget
  change c+5*G K+UniformRadixInstructionMachine.cap (width K) (UniformRadixTwoDAG.count K) K+500 ≤ _
  omega

def boot : List Op := [.literal 580 0,.add 400 560 580,.add 401 563 580]
theorem boot_code : UniformPreparationRowTableMachine.BlockAt boot program 0 := by intro i hi;change i < 3 at hi;interval_cases i <;> rfl

theorem boot_spec {K a e c d : ℕ} {s : State} (h : Params K a e c d s) :
    (applyBlock boot s).natReg 400=K ∧ (applyBlock boot s).natReg 401=c ∧ (applyBlock boot s).natReg 580=0 ∧
    (applyBlock boot s).natHeap=s.natHeap := by
  rcases h with ⟨hK,ha,he,hc,hd⟩
  simp [applyBlock,boot,Op.apply,writeNat,next,hK,hc]

/-- Continuous startup invokes the actual producer, discharging its physical
source tape from ordinary caller sizes rather than assuming it exists. -/
theorem convolution_start (n K a e c d B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Params K a e c d s) (hp : s.pc=0) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 4*K+21+(19*K+80)*G K ∧ u.pc=157 ∧
    UniformConvolutionTopologyMachine.Tape K c u ∧ Params K a e c d u ∧ u.natReg 565=s.natReg 565 ∧
    u.natReg 402=width K ∧ u.natReg 404=G K ∧ u.natReg 580=0 ∧
    UniformConvolutionTopologyMachine.Outside c (5*G K) s.natHeap u := by
  have hc : 1000 ≤ B := (budget_code K a e c d).trans hB
  have hr:=block_runs boot program 0 n B x s boot_code hp hs (by change 0+3 ≤ B;omega)
    (by simp [readable,boot,Op.readable]) (by
      have h560:=hs.2.1 560;have h563:=hs.2.1 563
      simp [peak,boot,Op.peak,Op.apply,writeNat,next];omega)
  let v:=applyBlock boot s
  have hvp : v.pc=3 := by rw [applyBlock_pc,hp];rfl
  have hv:=boot_spec h
  let v0 : State := {v with pc:=0}
  obtain ⟨u,t,hu,ht,hup,huc,hprinted,houtside,hframe⟩:=UniformConvolutionTopologyMachine.execution n K c B x v0 rfl
    hv.1 hv.2.1 (changePC_bound B v 0 hr.final_bound (by omega)) ((budget_convolution K a e c d).trans hB)
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed convolution_code (by rw [UniformConvolutionTopologyMachine.program_length];omega) (by omega) hu
  have heplaced : UniformAssembly.placed 3 v0=v := by
    change {v with pc:=3}=v
    rw [←hvp]
  have hactual : BoundedRuns program n x B v t {u with pc:=157} := by
    rw [heplaced] at hplaced;exact hplaced
  have hrun:=hr.trans hactual
  have hparams:=h.frame (runs_frame hrun.runs)
  have h580 : u.natReg 580=0 := (hframe.2.2.2.2 580 (by omega)).trans hv.2.2.1
  refine ⟨{u with pc:=157},3+t,hrun,by unfold G;omega,rfl,UniformConvolutionTopologyMachine.printed_tape hprinted,hparams,
    ?_,huc.Nreg,huc.total,h580,?_⟩
  · exact (hframe.2.2.2.2 565 (by omega)).trans (by simp [v0,v,applyBlock,boot,Op.apply,writeNat,next])
  · have hheap : v0.natHeap=s.natHeap := hv.2.2.2
    change UniformConvolutionTopologyMachine.Outside c (5*G K) s.natHeap u
    simpa only [G,hheap] using houtside


/-- Tail lookups avoid unfolding the imported154 whenever a loop block is checked. -/
theorem tail_lookup (i : ℕ) : program[157+i]?=tail[i]? := by
  have hl : (head++UniformConvolutionTopologyMachine.program.map (UniformAssembly.relocate 3 157)).length=157 := by
    simp only [List.length_append,List.length_map,head_length,UniformConvolutionTopologyMachine.program_length]
  unfold program UniformAssembly.embed
  rw [show head.length=3 from head_length]
  rw [List.getElem?_append_right (by rw [hl];omega),hl]
  simp

structure Constants (s : State) : Prop where
  zero : s.natReg 580=0
  one : s.natReg 581=1
  two : s.natReg 582=2
  five : s.natReg 583=5
  six : s.natReg 584=6

structure Base (K a e c d : ℕ) (s : State) : Prop extends Constants s where
  params : Params K a e c d s
  Nreg : s.natReg 565=width K
  Greg : s.natReg 566=G K

structure RowState (K a e c d slot j advance : ℕ) (s : State) : Prop extends Base K a e c d s where
  slotreg : s.natReg 567=slot
  index : s.natReg 568=j
  source : s.natReg 569=c+5*(j+advance)
  target : s.natReg 570=d+5*(slot*G K+j)
  slotG : s.natReg 571=slot*G K
  parity : s.natReg 572=slot%2
  previous : s.natReg 573=e+1+slot*G K-width K

structure Fields (r : Row) (s : State) : Prop where
  opcode : s.natReg 574=r.opcode
  left : s.natReg 575=r.left
  right : s.natReg 576=r.right
  kind : s.natReg 577=r.kind
  payload : s.natReg 578=r.payload

theorem Base.withPC {K a e c d pc : ℕ} {s : State} (h : Base K a e c d s) : Base K a e c d {s with pc:=pc} := by
  rcases h with ⟨⟨hz,ho,ht,h5,h6⟩,hp,hN,hG⟩
  exact ⟨⟨hz,ho,ht,h5,h6⟩,hp,hN,hG⟩

theorem RowState.withPC {K a e c d slot j advance pc : ℕ} {s : State} (h : RowState K a e c d slot j advance s) :
    RowState K a e c d slot j advance {s with pc:=pc} := by
  rcases h with ⟨hb,hs,hj,hc,hd,hG,hp,hprev⟩
  exact ⟨hb.withPC,hs,hj,hc,hd,hG,hp,hprev⟩

theorem Fields.withPC {r : Row} {s : State} {pc : ℕ} (h : Fields r s) : Fields r {s with pc:=pc} := ⟨h.opcode,h.left,h.right,h.kind,h.payload⟩

/-- A generic exact register frame for fixed natural blocks. Stores change no Nat register. -/
theorem block_keeps (os : List Op) (s : State) (i : ℕ)
    (h : ∀o∈os,o.scratch≠i) : (applyBlock os s).natReg i=s.natReg i := by
  induction os generalizing s with
  | nil=>rfl
  | cons o os ih=>
    rw [applyBlock,ih (o.apply s) (fun t ht=>h t (by simp [ht]))]
    have ho:=h o (by simp)
    have hone : i≠o.scratch := Ne.symm ho
    cases o <;> simp_all [Op.apply,Op.scratch,writeNat,next,Function.update_of_ne]

def postBlock : List Op := [.add 565 402 580,.add 566 404 580,.literal 581 1,.literal 582 2,
  .literal 583 5,.literal 584 6,.literal 567 0,.add 570 564 580]

theorem postBlock_code : UniformPreparationRowTableMachine.BlockAt postBlock program 157 := by
  intro i hi
  rw [tail_lookup]
  change i<8 at hi
  interval_cases i <;> rfl

def reads : List Op := [.get 574 569,.add 569 569 581,.get 575 569,.add 569 569 581,
  .get 576 569,.add 569 569 581,.get 577 569,.add 569 569 581,.get 578 569,.add 569 569 581]

theorem reads_code : UniformPreparationRowTableMachine.BlockAt reads program 174 := by
  intro i hi
  rw [show 174+i=157+(17+i) by omega,tail_lookup]
  change i<10 at hi
  interval_cases i <;> rfl

/-- Proof notation for one existing charged Nat instruction, including a
chosen branch edge. A branch edge is usable only after its comparison is proved. -/
inductive Atom where
  | op (pc : ℕ) (o : Op)
  | jump (pc target : ℕ)
  | branch (pc left right yes no : ℕ) (take : Bool)
  | mod (pc dst left right : ℕ)

def Atom.pc : Atom → ℕ
  | .op pc _ | .jump pc _ | .branch pc _ _ _ _ _ | .mod pc _ _ _=>pc

def Atom.code : Atom → Instruction
  | .op _ o=>o.code
  | .jump _ t=>.jump t
  | .branch _ l r y n _=>.branchLT l r y n
  | .mod _ d l r=>.natBinary .mod d l r

def Atom.apply (o : Atom) (s : State) : State := match o with
  | .op _ o=>o.apply s
  | .jump _ t=>{s with pc:=t}
  | .branch _ _ _ y n b=>{s with pc:=if b then y else n}
  | .mod _ d l r=>writeNat s d (s.natReg l%s.natReg r)

def Atom.ready (o : Atom) (s : State) : Prop := s.pc=o.pc ∧ match o with
  | .op _ o=>o.readable s
  | .jump _ _=>True
  | .branch _ l r _ _ b=>(decide (s.natReg l < s.natReg r))=b
  | .mod _ _ _ r=>s.natReg r≠0

def Atom.peak (o : Atom) (s : State) : ℕ := match o with
  | .op pc o=>max (pc+1) (o.peak s)
  | .jump _ t=>t
  | .branch _ _ _ y n b=>if b then y else n
  | .mod pc _ l r=>max (pc+1) (s.natReg l%s.natReg r)

def trace : List Atom → State → State
  | [],s=>s
  | a::as,s=>trace as (a.apply s)

def traceReady : List Atom → State → Prop
  | [],_=>True
  | a::as,s=>a.ready s ∧ traceReady as (a.apply s)

def tracePeak : List Atom → State → ℕ
  | [],_=>0
  | a::as,s=>max (a.peak s) (tracePeak as (a.apply s))

def TraceCode (as : List Atom) : Prop := ∀ a∈as,program[a.pc]?=some a.code

theorem Atom.step (a : Atom) (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hc : program[a.pc]?=some a.code) (h : a.ready s) : step program n x s=.running (a.apply s) := by
  rcases h with ⟨hp,hr⟩
  cases a with
  | op pc o=>exact o.step program n x s (by simpa only [Atom.pc,Atom.code,hp] using hc) hr
  | jump pc t=>
    change s.pc=pc at hp
    change program[pc]?=some (.jump t) at hc
    simp only [UniformMachine.step,hp,hc,Atom.apply]
  | branch pc l r y no b=>
    have hb : (decide (s.natReg l < s.natReg r))=b := hr
    cases b <;> simp_all [UniformMachine.step,Atom.pc,Atom.code,Atom.apply]
  | mod pc d l r=>
    change s.pc=pc at hp
    change program[pc]?=some (.natBinary .mod d l r) at hc
    change s.natReg r≠0 at hr
    simp only [UniformMachine.step,hp,hc,evalNat,ite_eq_right hr,Atom.apply]

theorem Atom.bound (a : Atom) (B : ℕ) (s : State) (hs : WordBound B s)
    (hr : a.ready s) (hk : a.peak s ≤ B) : WordBound B (a.apply s) := by
  rcases hr with ⟨hp,_⟩
  cases a with
  | op pc o=>exact o.apply_bound B s hs (by change max (pc+1) _ ≤ B at hk;change s.pc=pc at hp;omega) ((le_max_right _ _).trans hk)
  | jump pc t=>exact changePC_bound B s t hs hk
  | branch pc l r y no b=>exact changePC_bound B s (if b then y else no) hs hk
  | mod pc d l r=>exact writeNat_bound B s d _ hs (by change s.pc=pc at hp;change max (pc+1) _ ≤ B at hk;omega) ((le_max_right _ _).trans hk)

theorem trace_runs (as : List Atom) (n B : ℕ) (x : Fin n → ℂ) (s : State)
    (hc : TraceCode as) (hs : WordBound B s) (hr : traceReady as s) (hk : tracePeak as s ≤ B) :
    BoundedRuns program n x B s as.length (trace as s) := by
  induction as generalizing s with
  | nil=>exact .refl hs
  | cons a as ih=>
    have ht:=ih (a.apply s) (fun b hb=>hc b (by simp [hb])) (a.bound B s hs hr.1 ((le_max_left _ _).trans hk)) hr.2 ((le_max_right _ _).trans hk)
    exact .next hs (a.step n x s (hc a (by simp)) hr.1) ht

def refTrace (base target r : ℕ) (N e slot q : ℕ) : List Atom :=
  if q < N then
    [.branch base r 565 (base+1) (base+9) true,.branch (base+1) r 562 (base+2) (base+7) (decide (q < e))]++
    (if q < e then
      [.op (base+2) (.sub 579 562 581),.op (base+3) (.sub r 579 r),
        .branch (base+4) 572 581 target (base+5) (decide (slot%2=0))]++
      (if slot%2=0 then [] else [.op (base+5) (.add r r 573),.jump (base+6) target])
    else [.op (base+7) (.add r 562 580),.jump (base+8) target])
  else [.branch base r 565 (base+1) (base+9) false,
    .op (base+9) (.sub 579 r 565),.op (base+10) (.add r 562 581),
    .op (base+11) (.add r r 571),.op (base+12) (.add r r 579),.jump (base+13) target]

theorem tail_absolute (i : ℕ) (h : 157 ≤ i) : program[i]?=tail[i-157]? := by
  simpa only [Nat.add_sub_of_le h] using tail_lookup (i-157)

theorem refTrace_code (base target r N e slot q : ℕ)
    (h : (base=184 ∧ target=198 ∧ r=575) ∨ (base=199 ∧ target=215 ∧ r=576)) :
    TraceCode (refTrace base target r N e slot q) := by
  rcases h with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  all_goals unfold refTrace;split_ifs
  all_goals intro a ha
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Atom.pc,Atom.code,Op.code]
  all_goals rw [tail_absolute _ (by omega)]
  all_goals rfl

theorem refTrace_length (base target r N e slot q : ℕ) : (refTrace base target r N e slot q).length ≤ 7 := by
  unfold refTrace;split_ifs <;> simp

/-- The same proof covers the two literal reference mappers. The returned
reference is the actual typed cross-DAG wiring, not a caller-supplied address. -/
theorem refTrace_spec (K a e c d slot j advance base target r q : ℕ) (s : State)
    (h : RowState K a e c d slot j advance s) (hp : s.pc=base) (hq : s.natReg r=q)
    (hr : r=575 ∨ r=576) :
    traceReady (refTrace base target r (width K) e slot q) s ∧
    (trace (refTrace base target r (width K) e slot q) s).pc=target ∧
    (trace (refTrace base target r (width K) e slot q) s).natReg r=dataRef K e slot q ∧
    (trace (refTrace base target r (width K) e slot q) s).natHeap=s.natHeap := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hj,hs,hdst,hoff,hpar,hprev⟩
  have hparlt : slot%2 < 1 ↔ slot%2=0 := by omega
  rcases hr with rfl|rfl
  all_goals unfold refTrace;split_ifs with hlt hei heven
  all_goals simp_all [traceReady,trace,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next,dataRef,Nat.add_comm]
  all_goals (try split_ifs) <;> omega


def Atom.scratch : Atom → ℕ
  | .op _ o=>o.scratch
  | .mod _ d _ _=>d
  | .jump _ _ | .branch _ _ _ _ _ _=>0

theorem trace_keeps (as : List Atom) (s : State) (i : ℕ)
    (h : ∀ a∈as,a.scratch≠i) : (trace as s).natReg i=s.natReg i := by
  induction as generalizing s with
  | nil=>rfl
  | cons a as ih=>
    rw [trace,ih (a.apply s) (fun b hb=>h b (by simp [hb]))]
    have ha:=h a (by simp)
    have hn : i≠a.scratch := Ne.symm ha
    cases a with
    | op pc o=>cases o <;> simp_all [Atom.apply,Atom.scratch,Op.apply,Op.scratch,writeNat,next]
    | jump pc t | branch pc l r y no b=>rfl
    | mod pc d l r=>simp_all [Atom.apply,Atom.scratch,writeNat,next]

def ControlSame (s u : State) : Prop := ∀ i,(560 ≤ i ∧ i ≤ 573) ∨ (580 ≤ i ∧ i ≤ 584) → u.natReg i=s.natReg i

theorem RowState.controls {K a e c d slot j advance : ℕ} {s u : State}
    (h : RowState K a e c d slot j advance s) (hf : ControlSame s u) : RowState K a e c d slot j advance u := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hj,hs,hdst,hoff,hpar,hprev⟩
  constructor
  · constructor
    · exact ⟨(hf 580 (by omega)).trans hz,(hf 581 (by omega)).trans ho,(hf 582 (by omega)).trans ht,
        (hf 583 (by omega)).trans h5,(hf 584 (by omega)).trans h6⟩
    · exact ⟨(hf 560 (by omega)).trans hK,(hf 561 (by omega)).trans ha,(hf 562 (by omega)).trans he,
        (hf 563 (by omega)).trans hc,(hf 564 (by omega)).trans hd⟩
    · exact (hf 565 (by omega)).trans hN
    · exact (hf 566 (by omega)).trans hG
  all_goals first
    | exact (hf 567 (by omega)).trans hslot
    | exact (hf 568 (by omega)).trans hj
    | exact (hf 569 (by omega)).trans hs
    | exact (hf 570 (by omega)).trans hdst
    | exact (hf 571 (by omega)).trans hoff
    | exact (hf 572 (by omega)).trans hpar
    | exact (hf 573 (by omega)).trans hprev

theorem refTrace_controls (base target r N e slot q : ℕ) (s : State) (hr : r=575 ∨ r=576) :
    ControlSame s (trace (refTrace base target r N e slot q) s) := by
  intro i hi
  apply trace_keeps
  unfold refTrace
  split_ifs
  all_goals intro a ha
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Atom.scratch,Op.scratch]
  all_goals rcases hr with rfl|rfl <;> omega

theorem budget_tail (K a e c d : ℕ) :
    c+d+20*(width K+G K+a+e+K+1)+1000 ≤ budget K a e c d := by
  have hp : width K+G K+a+e+K+1 ≤ (width K+G K+a+e+K+1)^2 := le_self_pow (by omega) (by decide)
  unfold budget
  omega

theorem refTrace_peak (K a e c d slot j advance base target r q B : ℕ) (s : State)
    (h : RowState K a e c d slot j advance s) (hq : s.natReg r=q) (hr : r=575 ∨ r=576)
    (hslot : slot < 6) (hval : q ≤ width K+G K)
    (hpc : base ≤ 200 ∧ target ≤ 215) (hB : budget K a e c d ≤ B) :
    tracePeak (refTrace base target r (width K) e slot q) s ≤ B := by
  have hN:=G_width K
  have hg : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
  have hb : 2*e+width K+7*G K+300 ≤ B := by have ht:=(budget_tail K a e c d).trans hB;omega
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hNr,hGr⟩,hslotr,hj,hs,hdst,hoff,hpar,hprev⟩
  rcases hr with rfl|rfl
  all_goals unfold refTrace;split_ifs
  all_goals simp_all [tracePeak,Atom.peak,Atom.apply,Op.peak,Op.apply,writeNat,next]
  all_goals (try split_ifs) <;> omega

theorem ref_run (n K a e c d slot j advance base target r q B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : RowState K a e c d slot j advance s) (hp : s.pc=base) (hq : s.natReg r=q)
    (hlayout : (base=184 ∧ target=198 ∧ r=575) ∨ (base=199 ∧ target=215 ∧ r=576))
    (hslot : slot < 6) (hval : q ≤ width K+G K) (hs : WordBound B s)
    (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 7 ∧ u.pc=target ∧
    RowState K a e c d slot j advance u ∧ u.natReg r=dataRef K e slot q ∧ u.natHeap=s.natHeap := by
  have hr : r=575 ∨ r=576 := by rcases hlayout with ⟨_,_,h⟩|⟨_,_,h⟩ <;> simp [h]
  have hpbound : base ≤ 200 ∧ target ≤ 215 := by rcases hlayout with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> omega
  obtain ⟨hready,hpc,href,hheap⟩:=refTrace_spec K a e c d slot j advance base target r q s h hp hq hr
  let path:=refTrace base target r (width K) e slot q
  have hrun:=trace_runs path n B x s (refTrace_code _ _ _ _ _ _ _ hlayout) hs hready
    (refTrace_peak _ _ _ _ _ _ _ _ _ _ _ _ _ s h hq hr hslot hval hpbound hB)
  exact ⟨trace path s,path.length,hrun,refTrace_length _ _ _ _ _ _ _,hpc,
    h.controls (refTrace_controls _ _ _ _ _ _ _ s hr),href,hheap⟩

/-- Five physical loads read the producer's actual five-field tape. -/
theorem reads_spec (K a e c d slot j : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 0 s)
    (h0 : s.natHeap (c+5*j)=some r.opcode) (h1 : s.natHeap (c+5*j+1)=some r.left)
    (h2 : s.natHeap (c+5*j+2)=some r.right) (h3 : s.natHeap (c+5*j+3)=some r.kind)
    (h4 : s.natHeap (c+5*j+4)=some r.payload) :
    RowState K a e c d slot j 1 (applyBlock reads s) ∧ Fields r (applyBlock reads s) ∧
    (applyBlock reads s).natHeap=s.natHeap ∧ readable reads s := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hj,hs,hdst,hoff,hpar,hprev⟩
  have h1' : s.natHeap (c+5*j+1+1)=some r.right := by simpa only [Nat.add_assoc] using h2
  have h2' : s.natHeap (c+5*j+1+1+1)=some r.kind := by simpa only [Nat.add_assoc] using h3
  have h3' : s.natHeap (c+5*j+1+1+1+1)=some r.payload := by simpa only [Nat.add_assoc] using h4
  refine ⟨?_,?_,rfl,?_⟩
  · constructor
    · constructor
      · exact ⟨by simp [applyBlock,reads,Op.apply,writeNat,next,hz],by simp [applyBlock,reads,Op.apply,writeNat,next,ho],
          by simp [applyBlock,reads,Op.apply,writeNat,next,ht],by simp [applyBlock,reads,Op.apply,writeNat,next,h5],
          by simp [applyBlock,reads,Op.apply,writeNat,next,h6]⟩
      · simpa [Params,applyBlock,reads,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
      all_goals simp [applyBlock,reads,Op.apply,writeNat,next,hN,hG]
    all_goals simp [applyBlock,reads,Op.apply,writeNat,next,hslot,hj,hs,ho,hdst,hoff,hpar,hprev]
    omega
  · constructor <;> simp [applyBlock,reads,Op.apply,writeNat,next,hs,ho,h0,h1,h1',h2',h3']
  · simp [readable,reads,Op.readable,Op.apply,writeNat,next,hs,ho,h0,h1,h1',h2',h3']



theorem trace_append (xs ys : List Atom) (s : State) : trace (xs++ys) s=trace ys (trace xs s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>exact ih (a.apply s)

theorem traceReady_append (xs ys : List Atom) (s : State) :
    traceReady (xs++ys) s ↔ traceReady xs s ∧ traceReady ys (trace xs s) := by
  induction xs generalizing s with
  | nil=>simp [traceReady,trace]
  | cons a xs ih=>simp only [List.cons_append,traceReady,trace,ih,and_assoc]

theorem tracePeak_append (xs ys : List Atom) (s : State) :
    tracePeak (xs++ys) s=max (tracePeak xs s) (tracePeak ys (trace xs s)) := by
  induction xs generalizing s with
  | nil=>simp [tracePeak,trace]
  | cons a xs ih=>simp only [List.cons_append,tracePeak,trace,ih,max_assoc]

theorem refTrace_keeps (base target r N e slot q : ℕ) (s : State) (i : ℕ)
    (hi : i≠r ∧ i≠579 ∧ i≠0) :
    (trace (refTrace base target r N e slot q) s).natReg i=s.natReg i := by
  apply trace_keeps
  unfold refTrace;split_ifs
  all_goals intro a ha
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Atom.scratch,Op.scratch]
  all_goals omega

theorem left_fields (K a e c d slot j advance : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s) (hp : s.pc=184) :
    Fields {r with left:=dataRef K e slot r.left}
      (trace (refTrace 184 198 575 (width K) e slot r.left) s) := by
  have hs:=refTrace_spec K a e c d slot j advance 184 198 575 r.left s h hp hf.left (by simp)
  exact ⟨(refTrace_keeps _ _ _ _ _ _ _ s 574 (by omega)).trans hf.opcode,hs.2.2.1,
    (refTrace_keeps _ _ _ _ _ _ _ s 576 (by omega)).trans hf.right,
    (refTrace_keeps _ _ _ _ _ _ _ s 577 (by omega)).trans hf.kind,
    (refTrace_keeps _ _ _ _ _ _ _ s 578 (by omega)).trans hf.payload⟩

theorem right_fields (K a e c d slot j advance : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s) (hp : s.pc=199) :
    Fields {r with right:=dataRef K e slot r.right}
      (trace (refTrace 199 215 576 (width K) e slot r.right) s) := by
  have hs:=refTrace_spec K a e c d slot j advance 199 215 576 r.right s h hp hf.right (by simp)
  exact ⟨(refTrace_keeps _ _ _ _ _ _ _ s 574 (by omega)).trans hf.opcode,
    (refTrace_keeps _ _ _ _ _ _ _ s 575 (by omega)).trans hf.left,hs.2.2.1,
    (refTrace_keeps _ _ _ _ _ _ _ s 577 (by omega)).trans hf.kind,
    (refTrace_keeps _ _ _ _ _ _ _ s 578 (by omega)).trans hf.payload⟩

def rightTrace (N e slot : ℕ) (r : Row) : List Atom :=
  if r.opcode < 2 then [.branch 198 574 582 199 213 true]++refTrace 199 215 576 N e slot r.right
  else [.branch 198 574 582 199 213 false,.op 213 (.literal 576 0),.jump 214 215]

theorem rightTrace_code (N e slot : ℕ) (r : Row) : TraceCode (rightTrace N e slot r) := by
  unfold rightTrace
  split_ifs
  · intro a ha
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with rfl|ha
    · rw [tail_absolute _ (by decide)];rfl
    · exact refTrace_code _ _ _ _ _ _ _ (Or.inr ⟨rfl,rfl,rfl⟩) a ha
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals rw [tail_absolute _ (by decide)];rfl

theorem rightTrace_spec (K a e c d slot j advance : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s) (hp : s.pc=198) :
    traceReady (rightTrace (width K) e slot r) s ∧
    (trace (rightTrace (width K) e slot r) s).pc=215 ∧
    Fields {r with right:=if r.opcode < 2 then dataRef K e slot r.right else 0}
      (trace (rightTrace (width K) e slot r) s) ∧
    (trace (rightTrace (width K) e slot r) s).natHeap=s.natHeap ∧
    ControlSame s (trace (rightTrace (width K) e slot r) s) := by
  unfold rightTrace
  split_ifs with hop
  · let v : State := {s with pc:=199}
    have hspec:=refTrace_spec K a e c d slot j advance 199 215 576 r.right v h.withPC rfl hf.right (by simp)
    rw [trace_append,traceReady_append]
    change _ ∧ _ ∧ Fields _ (trace _ v) ∧ _ ∧ _
    refine ⟨⟨?_,hspec.1⟩,hspec.2.1,right_fields _ _ _ _ _ _ _ _ r v h.withPC hf.withPC rfl,hspec.2.2.2,?_⟩
    · simp [traceReady,Atom.ready,Atom.pc,hp,hf.opcode,h.two,hop]
    · exact refTrace_controls _ _ _ _ _ _ _ v (by simp)
  · rcases hf with ⟨hopr,hl,hr,hkind,hpay⟩
    have htwo:=h.two
    refine ⟨?_,?_,?_,rfl,?_⟩
    · simp [traceReady,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next,hp,hopr,htwo,hop]
    · rfl
    · constructor <;> simp [trace,Atom.apply,Op.apply,writeNat,next,hopr,hl,hkind,hpay]
    · intro i hi
      simp [trace,Atom.apply,Op.apply,writeNat,next,show i≠576 by omega]

theorem rightTrace_peak (K a e c d slot j advance B : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s)
    (hslot : slot < 6) (hval : r.right ≤ width K+G K) (hB : budget K a e c d ≤ B) :
    tracePeak (rightTrace (width K) e slot r) s ≤ B := by
  have hb : 300 ≤ B := (by have hh:=(budget_code K a e c d).trans hB;omega)
  unfold rightTrace
  split_ifs
  · rw [tracePeak_append]
    exact max_le (by simp [tracePeak,Atom.peak];omega)
      (refTrace_peak K a e c d slot j advance 199 215 576 r.right B {s with pc:=199}
        h.withPC hf.right (by simp) hslot hval (by omega) hB)
  · simp [tracePeak,Atom.peak,Op.peak]
    omega

def coefficientTrace (N : ℕ) (r : Row) : List Atom :=
  if r.kind < 1 then [.branch 215 577 581 221 216 true]
  else [.branch 215 577 581 221 216 false,.branch 216 578 565 221 217 (decide (r.payload < N))]++
    (if r.payload < N then [] else [.op 217 (.sub 578 578 565),.op 218 (.mul 587 567 565),
      .op 219 (.add 578 578 587),.op 220 (.add 578 578 565)])

theorem coefficientTrace_code (N : ℕ) (r : Row) : TraceCode (coefficientTrace N r) := by
  unfold coefficientTrace;split_ifs
  all_goals intro a ha
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Atom.pc,Atom.code,Op.code]
  all_goals rw [tail_absolute _ (by omega)];rfl

theorem coefficientTrace_spec (K a e c d slot j advance : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s) (hp : s.pc=215) (hk : r.kind ≤ 1) :
    traceReady (coefficientTrace (width K) r) s ∧
    (trace (coefficientTrace (width K) r) s).pc=221 ∧
    Fields {r with payload:=if r.kind=1 then coefficientRef K slot r.payload else r.payload}
      (trace (coefficientTrace (width K) r) s) ∧
    (trace (coefficientTrace (width K) r) s).natHeap=s.natHeap ∧
    ControlSame s (trace (coefficientTrace (width K) r) s) := by
  have hone:=h.one;have hN:=h.Nreg;have hslot:=h.slotreg
  rcases hf with ⟨hop,hl,hr,hkind,hpay⟩
  unfold coefficientTrace;split_ifs with hlt hpaylt
  all_goals refine ⟨?_,?_,?_,rfl,?_⟩
  all_goals first
    | (apply Fields.mk <;> simp_all [trace,Atom.apply,Op.apply,writeNat,next,coefficientRef,Nat.add_comm,Nat.add_assoc])
    | (intro i hi;simp [trace,Atom.apply,Op.apply,writeNat,next,
        show i≠578 by omega,show i≠587 by omega])
    | (simp_all [traceReady,trace,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next])
  all_goals omega


theorem coefficientTrace_peak (K a e c d slot j advance B : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j advance s) (hf : Fields r s)
    (hslot : slot < 6) (hpay : r.payload ≤ 2*width K) (hB : budget K a e c d ≤ B) :
    tracePeak (coefficientTrace (width K) r) s ≤ B := by
  have hb : 8*width K+300 ≤ B := by have hh:=(budget_tail K a e c d).trans hB;omega
  have hmul : slot*width K ≤ 5*width K := Nat.mul_le_mul_right _ (by omega)
  have hN:=h.Nreg;have hs:=h.slotreg
  unfold coefficientTrace;split_ifs
  all_goals simp_all [tracePeak,Atom.peak,Atom.apply,Op.peak,Op.apply,writeNat,next,hf.payload]
  all_goals (try split_ifs) <;> omega



theorem rightTrace_length (N e slot : ℕ) (r : Row) : (rightTrace N e slot r).length ≤ 8 := by
  unfold rightTrace;split_ifs
  · simp only [List.length_append,List.length_singleton]
    have hh:=refTrace_length 199 215 576 N e slot r.right
    omega
  · simp

theorem coefficientTrace_length (N : ℕ) (r : Row) : (coefficientTrace N r).length ≤ 6 := by
  unfold coefficientTrace;split_ifs <;> simp

/-- The actual charged mapper reaches the five store instructions with exactly
the row prescribed by the typed cross-DAG coefficient and operand embeddings. -/
theorem mapper_run (n K a e c d slot j B : ℕ) (x : Fin n → ℂ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 1 s) (hf : Fields r s) (hp : s.pc=184)
    (hslot : slot < 6) (hl : r.left ≤ width K+G K) (hr : r.right ≤ width K+G K)
    (hk : r.kind ≤ 1) (hpay : r.payload ≤ 2*width K) (hs : WordBound B s)
    (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 21 ∧ u.pc=221 ∧
    RowState K a e c d slot j 1 u ∧ Fields (remapRow K e slot r) u ∧ u.natHeap=s.natHeap := by
  let lpath:=refTrace 184 198 575 (width K) e slot r.left
  let v:=trace lpath s
  have lspec:=refTrace_spec K a e c d slot j 1 184 198 575 r.left s h hp hf.left (by simp)
  have lv:=trace_runs lpath n B x s (refTrace_code _ _ _ _ _ _ _ (Or.inl ⟨rfl,rfl,rfl⟩)) hs lspec.1
    (refTrace_peak _ _ _ _ _ _ _ _ _ _ _ _ _ s h hf.left (by simp) hslot hl (by omega) hB)
  have hv : RowState K a e c d slot j 1 v := h.controls (refTrace_controls _ _ _ _ _ _ _ s (by simp))
  let rl : Row := {r with left:=dataRef K e slot r.left}
  have hlf : Fields rl v := left_fields K a e c d slot j 1 r s h hf hp
  let rpath:=rightTrace (width K) e slot rl
  let w:=trace rpath v
  have rspec:=rightTrace_spec K a e c d slot j 1 rl v hv hlf lspec.2.1
  have rv:=trace_runs rpath n B x v (rightTrace_code _ _ _ _) lv.final_bound rspec.1
    (rightTrace_peak K a e c d slot j 1 B rl v hv hlf hslot hr hB)
  have hw : RowState K a e c d slot j 1 w := hv.controls rspec.2.2.2.2
  let rr : Row := {rl with right:=if rl.opcode < 2 then dataRef K e slot rl.right else 0}
  have hrf : Fields rr w := rspec.2.2.1
  let cpath:=coefficientTrace (width K) rr
  let u:=trace cpath w
  have cspec:=coefficientTrace_spec K a e c d slot j 1 rr w hw hrf rspec.2.1 hk
  have cv:=trace_runs cpath n B x w (coefficientTrace_code _ _) rv.final_bound cspec.1
    (coefficientTrace_peak K a e c d slot j 1 B rr w hw hrf hslot hpay hB)
  refine ⟨u,lpath.length+rpath.length+cpath.length,(lv.trans rv).trans cv,?_,cspec.2.1,
    hw.controls cspec.2.2.2.2,cspec.2.2.1,cspec.2.2.2.1.trans (rspec.2.2.2.1.trans lspec.2.2.2)⟩
  have h1:=refTrace_length 184 198 575 (width K) e slot r.left
  have h2:=rightTrace_length (width K) e slot rl
  have h3:=coefficientTrace_length (width K) rr
  change lpath.length ≤ 7 at h1
  change rpath.length ≤ 8 at h2
  change cpath.length ≤ 6 at h3
  omega

theorem reads_peak (K a e c d slot j B : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 0 s) (hj : j < G K) (hs : WordBound B s)
    (h0 : s.natHeap (c+5*j)=some r.opcode) (h1 : s.natHeap (c+5*j+1)=some r.left)
    (h2 : s.natHeap (c+5*j+2)=some r.right) (h3 : s.natHeap (c+5*j+3)=some r.kind)
    (h4 : s.natHeap (c+5*j+4)=some r.payload) (hB : budget K a e c d ≤ B) : peak reads s ≤ B := by
  have hb : c+5*G K+1000 ≤ B := by have hh:=(budget_tail K a e c d).trans hB;omega
  have ho:=h.one;have hptr:=h.source
  have hval0:=(hs.2.2.1 _ _ h0).2
  have hval1:=(hs.2.2.1 _ _ h1).2
  have hval2:=(hs.2.2.1 _ _ h2).2
  have hval3:=(hs.2.2.1 _ _ h3).2
  have hval4:=(hs.2.2.1 _ _ h4).2
  have h1' : s.natHeap (c+5*j+1+1)=some r.right := by simpa only [Nat.add_assoc] using h2
  have h2' : s.natHeap (c+5*j+1+1+1)=some r.kind := by simpa only [Nat.add_assoc] using h3
  have h3' : s.natHeap (c+5*j+1+1+1+1)=some r.payload := by simpa only [Nat.add_assoc] using h4
  simp [peak,reads,Op.peak,Op.apply,writeNat,next,hptr,ho,h0,h1,h1',h2',h3']
  omega

/-- Actual source tape is an intermediate postcondition of startup. This
entry-to-store row theorem performs all five reads and every remap instruction. -/
theorem read_mapper_run (n K a e c d slot j B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : RowState K a e c d slot j 0 s) (ht : UniformConvolutionTopologyMachine.Tape K c s)
    (hp : s.pc=174) (hj : j < G K) (hslot : slot < 6) (hs : WordBound B s)
    (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 31 ∧ u.pc=221 ∧
    RowState K a e c d slot j 1 u ∧
    Fields (remapRow K e slot (encode (UniformConvolutionDAG.instruction K ⟨j,hj⟩))) u ∧ u.natHeap=s.natHeap := by
  let q : Fin (UniformConvolutionDAG.total K) := ⟨j,hj⟩
  let r:=encode (UniformConvolutionDAG.instruction K q)
  obtain ⟨h0,h1,h2,h3,h4⟩:=ht q
  have rs:=reads_spec K a e c d slot j r s h h0 h1 h2 h3 h4
  have rv:=block_runs reads program 174 n B x s reads_code hp hs
    (by have hh:=(budget_code K a e c d).trans hB;change 174+10 ≤ B;omega) rs.2.2.2
    (reads_peak K a e c d slot j B r s h hj hs h0 h1 h2 h3 h4 hB)
  have rvp : (applyBlock reads s).pc=184 := by rw [applyBlock_pc,hp];rfl
  have hb:=UniformConvolutionTopologyMachine.rowAt_data_bound K q
  rw [UniformConvolutionTopologyMachine.rowAt_instruction] at hb
  have hshape:=UniformConvolutionTopologyMachine.encode_shape (UniformConvolutionDAG.instruction K q)
  have hpay:=UniformConvolutionTopologyMachine.rowAt_payload_bound K q
  rw [UniformConvolutionTopologyMachine.rowAt_instruction] at hpay
  obtain ⟨u,t,hu,hcost,hpc,hrow,hf,hheap⟩:=mapper_run n K a e c d slot j B x r (applyBlock reads s)
    rs.1 rs.2.1 rvp hslot (Nat.le_of_lt hb.1) (Nat.le_of_lt hb.2) hshape.2 hpay rv.final_bound hB
  exact ⟨u,10+t,rv.trans hu,by omega,hpc,hrow,hf,hheap.trans rs.2.2.1⟩


open UniformConvolutionTopologyMachine (storeRow storeRow_fields storeRow_keeps)

def HeapFields (heap : ℕ → Option ℕ) (address : ℕ) (r : Row) : Prop :=
  heap address=some r.opcode ∧ heap (address+1)=some r.left ∧ heap (address+2)=some r.right ∧
  heap (address+3)=some r.kind ∧ heap (address+4)=some r.payload

def PrintedSlots (K e d count : ℕ) (s : State) : Prop := ∀ slot : Fin 6,∀ q : Fin (G K),
  slot.val*G K+q.val < count →
  HeapFields s.natHeap (d+5*(slot.val*G K+q.val))
    (remapRow K e slot.val (encode (UniformConvolutionDAG.instruction K q)))

def stores : List Op := [.put 570 574,.add 570 570 581,.put 570 575,.add 570 570 581,
  .put 570 576,.add 570 570 581,.put 570 577,.add 570 570 581,.put 570 578,.add 570 570 581,.add 568 568 581]

theorem stores_code : UniformPreparationRowTableMachine.BlockAt stores program 221 := by
  intro i hi
  rw [show 221+i=157+(64+i) by omega,tail_lookup]
  change i < 11 at hi
  interval_cases i <;> rfl

theorem stores_spec (K a e c d slot j : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 1 s) (hf : Fields r s) :
    RowState K a e c d slot (j+1) 0 (applyBlock stores s) ∧
    (applyBlock stores s).natHeap=storeRow s.natHeap (d+5*(slot*G K+j)) r := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hj,hs,hdst,hoff,hpar,hprev⟩
  refine ⟨?_,?_⟩
  · constructor
    · constructor
      · constructor <;> simp [applyBlock,stores,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
      · simpa [Params,applyBlock,stores,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
      all_goals simp [applyBlock,stores,Op.apply,writeNat,next,hN,hG]
    all_goals simp [applyBlock,stores,Op.apply,writeNat,next,hslot,hj,hs,hdst,hoff,hpar,hprev,ho]
    all_goals omega
  · simp [applyBlock,stores,Op.apply,writeNat,next,ho,hdst,hf.opcode,hf.left,hf.right,hf.kind,hf.payload,storeRow,Nat.add_assoc]

theorem dataRef_bound (K e slot q : ℕ) (hslot : slot < 6) (hq : q ≤ width K+G K) :
    dataRef K e slot q ≤ 2*e+7*G K+width K+2 := by
  have hmul : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
  unfold dataRef
  split_ifs <;> omega

theorem coefficientRef_bound (K slot q : ℕ) (hslot : slot < 6) (hq : q ≤ 2*width K) :
    coefficientRef K slot q ≤ 8*width K := by
  have hmul : slot*width K ≤ 5*width K := Nat.mul_le_mul_right _ (by omega)
  unfold coefficientRef;split_ifs <;> omega

theorem remapRow_bounds (K e slot : ℕ) (r : Row) (hslot : slot < 6)
    (hl : r.left ≤ width K+G K) (hr : r.right ≤ width K+G K)
    (ho : r.opcode ≤ 2) (hk : r.kind ≤ 1) (hpay : r.payload ≤ 2*width K) :
    (remapRow K e slot r).opcode ≤ 2 ∧ (remapRow K e slot r).left ≤ 2*e+7*G K+width K+2 ∧
    (remapRow K e slot r).right ≤ 2*e+7*G K+width K+2 ∧
    (remapRow K e slot r).kind ≤ 1 ∧ (remapRow K e slot r).payload ≤ 8*width K := by
  have hN:=width_pos K
  refine ⟨ho,dataRef_bound K e slot r.left hslot hl,?_,hk,?_⟩
  · change (if r.opcode < 2 then dataRef K e slot r.right else 0) ≤ _
    split_ifs
    · exact dataRef_bound K e slot r.right hslot hr
    · omega
  · change (if r.kind=1 then coefficientRef K slot r.payload else r.payload) ≤ _
    split_ifs
    · exact coefficientRef_bound K slot r.payload hslot hpay
    · omega

theorem budget_tape (K a e c d : ℕ) :
    d+5*(6*G K+2*a)+20*(width K+G K+a+e+K+1)+1000 ≤ budget K a e c d := by
  have hp : width K+G K+a+e+K+1 ≤ (width K+G K+a+e+K+1)^2 := le_self_pow (by omega) (by decide)
  unfold budget
  omega

theorem stores_peak (K a e c d slot j B : ℕ) (s : State)
    (h : RowState K a e c d slot j 1 s) (hj : j < G K)
    (hf : Fields (remapRow K e slot (encode (UniformConvolutionDAG.instruction K ⟨j,hj⟩))) s) (hslot : slot < 6) (hB : budget K a e c d ≤ B) : peak stores s ≤ B := by
  have hmul : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
  have hbound:=(budget_tape K a e c d).trans hB
  have hb:=UniformConvolutionTopologyMachine.rowAt_data_bound K ⟨j,hj⟩
  rw [UniformConvolutionTopologyMachine.rowAt_instruction] at hb
  have hs:=UniformConvolutionTopologyMachine.encode_shape (UniformConvolutionDAG.instruction K ⟨j,hj⟩)
  have hp:=UniformConvolutionTopologyMachine.rowAt_payload_bound K ⟨j,hj⟩
  rw [UniformConvolutionTopologyMachine.rowAt_instruction] at hp
  have hr:=remapRow_bounds K e slot (encode (UniformConvolutionDAG.instruction K ⟨j,hj⟩)) hslot
    (Nat.le_of_lt hb.1) (Nat.le_of_lt hb.2) hs.1 hs.2 hp
  have hptr:=h.target;have ho:=h.one;have hi:=h.index
  simp [peak,stores,Op.peak,Op.apply,writeNat,next,hptr,ho,hi,hf.opcode,hf.left,hf.right,hf.kind,hf.payload]
  omega

/-- Previously produced slots and rows remain intact after the five charged
stores. The current row is written at its chronological gate index. -/
theorem stores_printed (K a e c d slot j : ℕ) (s : State) (hj : j < G K) (_hslot : slot < 6)
    (h : RowState K a e c d slot j 1 s)
    (hf : Fields (remapRow K e slot (encode (UniformConvolutionDAG.instruction K ⟨j,hj⟩))) s)
    (hp : PrintedSlots K e d (slot*G K+j) s) :
    PrintedSlots K e d (slot*G K+j+1) (applyBlock stores s) := by
  intro b q hbq
  rw [(stores_spec K a e c d slot j _ s h hf).2]
  by_cases he : b.val*G K+q.val=slot*G K+j
  · have hq:=q.isLt
    have hs : b.val=slot ∧ q.val=j := by
      have hg:=width_pos K;have hw:=G_width K
      have hdiv1 : (b.val*G K+q.val)/(G K)=b.val := by rw [Nat.mul_comm b.val (G K),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hq,Nat.add_zero]
      have hdiv2 : (slot*G K+j)/(G K)=slot := by rw [Nat.mul_comm slot (G K),Nat.mul_add_div (by omega),Nat.div_eq_of_lt hj,Nat.add_zero]
      have hb : b.val=slot := by rw [he] at hdiv1;omega
      exact ⟨hb,by rw [hb] at he;omega⟩
    have hqe : q=⟨j,hj⟩ := Fin.ext hs.2
    rw [hqe,hs.1]
    exact storeRow_fields s.natHeap _ _
  · have hlt : b.val*G K+q.val < slot*G K+j := by omega
    have hold:=hp b q hlt
    unfold HeapFields
    rw [storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)) (by omega),
      storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+1) (by omega),
      storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+2) (by omega),
      storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+3) (by omega),
      storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+4) (by omega)]
    exact hold



theorem stores_source (K a e c d slot j : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 1 s) (hf : Fields r s)
    (ht : UniformConvolutionTopologyMachine.Tape K c s) (hd : c+5*G K ≤ d) :
    UniformConvolutionTopologyMachine.Tape K c (applyBlock stores s) := by
  intro q
  have hq : q.val < G K := q.isLt
  rw [(stores_spec K a e c d slot j r s h hf).2]
  rw [storeRow_keeps _ _ _ (c+5*q.val) (by omega),storeRow_keeps _ _ _ (c+5*q.val+1) (by omega),
    storeRow_keeps _ _ _ (c+5*q.val+2) (by omega),storeRow_keeps _ _ _ (c+5*q.val+3) (by omega),
    storeRow_keeps _ _ _ (c+5*q.val+4) (by omega)]
  exact ht q

theorem stores_outside (K a e c d slot j : ℕ) (r : Row) (s : State)
    (h : RowState K a e c d slot j 1 s) (hf : Fields r s) (hj : j < G K) (hslot : slot < 6)
    (heap : ℕ → Option ℕ) (ho : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap s) :
    UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap (applyBlock stores s) := by
  have hmul : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
  intro address ha
  rw [(stores_spec K a e c d slot j r s h hf).2,storeRow_keeps _ _ _ address (by omega)]
  exact ho address ha

structure RowInvariant (K a e c d slot j : ℕ) (heap : ℕ → Option ℕ) (s : State) : Prop where
  row : RowState K a e c d slot j 0 s
  source : UniformConvolutionTopologyMachine.Tape K c s
  printed : PrintedSlots K e d (slot*G K+j) s
  outside : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap s

theorem RowInvariant.withPC {K a e c d slot j pc : ℕ} {heap : ℕ → Option ℕ} {s : State}
    (h : RowInvariant K a e c d slot j heap s) : RowInvariant K a e c d slot j heap {s with pc:=pc} :=
  ⟨h.row.withPC,h.source,h.printed,h.outside⟩

theorem row_iteration (n K a e c d slot j B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : RowInvariant K a e c d slot j heap s) (hp : s.pc=173) (hj : j < G K)
    (hslot : slot < 6) (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 44 ∧ u.pc=173 ∧ RowInvariant K a e c d slot (j+1) heap u := by
  have hbound : 300 ≤ B := by have hc:=(budget_code K a e c d).trans hB;omega
  have hcode : program[173]?=some (.branchLT 568 566 174 233) := by rw [tail_absolute _ (by decide)];rfl
  have hstep : step program n x s=.running {s with pc:=174} := by
    simp only [UniformMachine.step,hp,hcode,h.row.index,h.row.Greg,ite_eq_left hj]
  have hb:=UniformPreparationRowTableMachine.control_run program n B 174 x s hs (by omega) hstep
  obtain ⟨v,t,hv,hcost,hvp,hrow,hfields,hheap⟩:=read_mapper_run n K a e c d slot j B x {s with pc:=174}
    h.row.withPC h.source rfl hj hslot hb.final_bound hB
  have hprinted : PrintedSlots K e d (slot*G K+j) v := by simpa only [PrintedSlots,hheap] using h.printed
  have hsource : UniformConvolutionTopologyMachine.Tape K c v := by simpa only [UniformConvolutionTopologyMachine.Tape,hheap] using h.source
  have houtside : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap v := by
    simpa only [UniformConvolutionTopologyMachine.Outside,hheap] using h.outside
  let r:=remapRow K e slot (encode (UniformConvolutionDAG.instruction K ⟨j,hj⟩))
  have hw:=block_runs stores program 221 n B x v stores_code hvp hv.final_bound
    (by change 221+11 ≤ B;omega) (by simp [readable,stores,Op.readable])
    (stores_peak K a e c d slot j B v hrow hj hfields hslot hB)
  let w:=applyBlock stores v
  have hwp : w.pc=232 := by rw [applyBlock_pc,hvp];rfl
  have hcode' : program[232]?=some (.jump 173) := by rw [tail_absolute _ (by decide)];rfl
  have hend : step program n x w=.running {w with pc:=173} := by simp only [UniformMachine.step,hwp,hcode']
  have hjump:=UniformPreparationRowTableMachine.control_run program n B 173 x w hw.final_bound (by omega) hend
  refine ⟨{w with pc:=173},1+t+11+1,((hb.trans hv).trans hw).trans hjump,by omega,rfl,?_⟩
  exact ⟨(stores_spec K a e c d slot j r v hrow hfields).1.withPC,
    stores_source K a e c d slot j r v hrow hfields hsource hd,
    stores_printed K a e c d slot j v hj hslot hrow hfields hprinted,
    stores_outside K a e c d slot j r v hrow hfields hj hslot heap houtside⟩

/-- The row sweep is an actual finite RAM loop, not a host list traversal. -/
theorem row_loop (n K a e c d slot j fuel B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : RowInvariant K a e c d slot j heap s) (hp : s.pc=173) (hj : j+fuel=G K)
    (hslot : slot < 6) (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 44*fuel ∧ u.pc=173 ∧ RowInvariant K a e c d slot (G K) heap u := by
  induction fuel generalizing j s with
  | zero=>
    have he : j=G K := by omega
    subst j
    exact ⟨s,0,.refl hs,by omega,hp,h⟩
  | succ fuel ih=>
    obtain ⟨u,t,hu,ht,hup,hui⟩:=row_iteration n K a e c d slot j B x heap s h hp (by omega) hslot hd hs hB
    obtain ⟨v,q,hv,hq,hvp,hvi⟩:=ih (j+1) u hui hup (by omega) hu.final_bound
    exact ⟨v,t+q,hu.trans hv,by omega,hvp,hvi⟩


structure SlotInvariant (K a e c d slot : ℕ) (heap : ℕ → Option ℕ) (s : State) : Prop where
  base : Base K a e c d s
  slotreg : s.natReg 567=slot
  target : s.natReg 570=d+5*(slot*G K)
  source : UniformConvolutionTopologyMachine.Tape K c s
  printed : PrintedSlots K e d (slot*G K) s
  outside : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap s

theorem SlotInvariant.withPC {K a e c d slot pc : ℕ} {heap : ℕ → Option ℕ} {s : State}
    (h : SlotInvariant K a e c d slot heap s) : SlotInvariant K a e c d slot heap {s with pc:=pc} :=
  ⟨h.base.withPC,h.slotreg,h.target,h.source,h.printed,h.outside⟩

def slotInit : List Atom := [.op 166 (.mul 571 567 566),.mod 167 572 567 582,
  .op 168 (.add 573 562 581),.op 169 (.add 573 573 571),.op 170 (.sub 573 573 565),
  .op 171 (.literal 568 0),.op 172 (.add 569 563 580)]

theorem slotInit_code : TraceCode slotInit := by
  intro a ha
  simp only [slotInit,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rw [tail_absolute _ (by decide)];rfl

theorem slotInit_spec (K a e c d slot : ℕ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d slot heap s) (hp : s.pc=166) :
    traceReady slotInit s ∧ (trace slotInit s).pc=173 ∧ RowInvariant K a e c d slot 0 heap (trace slotInit s) := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hptr,hsource,hprinted,houtside⟩
  refine ⟨?_,?_,?_⟩
  · simp [slotInit,traceReady,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next,hp,ht]
  · simp [trace,slotInit,Atom.apply,Op.apply,writeNat,next,hp]
  · constructor
    · constructor
      · constructor
        · constructor <;> simp [trace,slotInit,Atom.apply,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
        · simpa [Params,trace,slotInit,Atom.apply,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
        all_goals simp [trace,slotInit,Atom.apply,Op.apply,writeNat,next,hN,hG]
      all_goals simp [trace,slotInit,Atom.apply,Op.apply,writeNat,next,hslot,hptr,hc,hz,he,ho,hG,hN,ht]
    · exact hsource
    · change PrintedSlots K e d (slot*G K+0) s
      simpa only [Nat.add_zero] using hprinted
    · exact houtside

theorem slotInit_peak (K a e c d slot B : ℕ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d slot heap s) (hslot : slot < 6) (hB : budget K a e c d ≤ B) :
    tracePeak slotInit s ≤ B := by
  have hmul : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
  have hb:=(budget_tail K a e c d).trans hB
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslotr,hptr,hsource,hprinted,houtside⟩
  simp [slotInit,tracePeak,Atom.peak,Atom.apply,Op.peak,Op.apply,writeNat,next,hslotr,hG,ht,he,ho,hN,hc,hz]
  have hmod : slot%2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem slot_iteration (n K a e c d slot B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d slot heap s) (hp : s.pc=165) (hslot : slot < 6)
    (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 44*G K+11 ∧ u.pc=165 ∧ SlotInvariant K a e c d (slot+1) heap u := by
  have hbound : 300 ≤ B := by have hh:=(budget_code K a e c d).trans hB;omega
  have hc1 : program[165]?=some (.branchLT 567 584 166 235) := by rw [tail_absolute _ (by decide)];rfl
  have hstep : step program n x s=.running {s with pc:=166} := by
    simp only [UniformMachine.step,hp,hc1,h.slotreg,h.base.six,ite_eq_left hslot]
  have hfirst:=UniformPreparationRowTableMachine.control_run program n B 166 x s hs (by omega) hstep
  let v : State := {s with pc:=166}
  have hinit:=slotInit_spec K a e c d slot heap v h.withPC rfl
  have hi:=trace_runs slotInit n B x v slotInit_code hfirst.final_bound hinit.1
    (slotInit_peak K a e c d slot B heap v h.withPC hslot hB)
  obtain ⟨w,t,hw,ht,hwp,hwi⟩:=row_loop n K a e c d slot 0 (G K) B x heap (trace slotInit v)
    hinit.2.2 hinit.2.1 (by omega) hslot hd hi.final_bound hB
  have hc2 : program[173]?=some (.branchLT 568 566 174 233) := by rw [tail_absolute _ (by decide)];rfl
  have hs2 : step program n x w=.running {w with pc:=233} := by
    simp only [UniformMachine.step,hwp,hc2,hwi.row.index,hwi.row.Greg,lt_self_iff_false,ite_false]
  have hfalse:=UniformPreparationRowTableMachine.control_run program n B 233 x w hw.final_bound (by omega) hs2
  let incPath : List Atom := [.op 233 (.add 567 567 581),.jump 234 165]
  have hincReady : traceReady incPath {w with pc:=233} := by simp [incPath,traceReady,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next]
  have hincCode : TraceCode incPath := by
    intro a ha
    simp only [incPath,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals rw [tail_absolute _ (by decide)];rfl
  have hincPeak : tracePeak incPath {w with pc:=233} ≤ B := by
    simp [incPath,tracePeak,Atom.peak,Op.peak,hwi.row.slotreg,hwi.row.one]
    omega
  have hinc:=trace_runs incPath n B x {w with pc:=233} hincCode hfalse.final_bound hincReady hincPeak
  let u:=trace incPath {w with pc:=233}
  refine ⟨u,1+7+t+1+2,(((hfirst.trans hi).trans hw).trans hfalse).trans hinc,by omega,rfl,?_⟩
  constructor
  · rcases hwi.row.toBase with ⟨⟨hz,ho,ht,h5,h6⟩,hparams,hN,hG⟩
    constructor
    · constructor
      · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using hz
      · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using ho
      · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using ht
      · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using h5
      · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using h6
    · simpa [Params,u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using hparams
    · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using hN
    · simpa [u,incPath,trace,Atom.apply,Op.apply,writeNat,next] using hG
  · simp [u,incPath,trace,Atom.apply,Op.apply,writeNat,next,hwi.row.slotreg,hwi.row.one]
  · simp only [u,incPath,trace,Atom.apply,Op.apply,writeNat,next]
    simp [hwi.row.target,Nat.add_mul,Nat.mul_add]
  · exact hwi.source
  · change PrintedSlots K e d ((slot+1)*G K) w
    simpa only [Nat.add_mul,Nat.one_mul] using hwi.printed
  · exact hwi.outside

/-- Six chronological remap passes reuse the physically generated convolution
scratch tape. No host-side graph enumeration occurs between passes. -/
theorem slots_loop (n K a e c d slot fuel B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d slot heap s) (hp : s.pc=165) (hf : slot+fuel=6)
    (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ (44*G K+11)*fuel ∧ u.pc=165 ∧ SlotInvariant K a e c d 6 heap u := by
  induction fuel generalizing slot s with
  | zero=>
    have he : slot=6 := by omega
    subst slot
    exact ⟨s,0,.refl hs,by omega,hp,h⟩
  | succ fuel ih=>
    obtain ⟨u,t,hu,ht,hup,hui⟩:=slot_iteration n K a e c d slot B x heap s h hp (by omega) hd hs hB
    obtain ⟨v,q,hv,hq,hvp,hvi⟩:=ih (slot+1) u hui hup (by omega) hu.final_bound
    refine ⟨v,t+q,hu.trans hv,?_,hvp,hvi⟩
    rw [Nat.mul_succ]
    omega


def addRow (K e phase i : ℕ) : Row := if phase=0 then
  ⟨0,branchOutput K e 0 i,branchOutput K e 1 i,0,0⟩
  else ⟨0,e+1+6*G K+i,branchOutput K e 2 i,0,0⟩

def PrintedAdds (K a e d count : ℕ) (s : State) : Prop := ∀ phase : Fin 2,∀ i : Fin a,
  phase.val*a+i.val < count → HeapFields s.natHeap (d+5*(6*G K+phase.val*a+i.val)) (addRow K e phase.val i.val)

structure AddState (K a e c d phase i : ℕ) (s : State) : Prop extends Base K a e c d s where
  target : s.natReg 570=d+5*(6*G K+phase*a+i)
  index : s.natReg 590=i
  first : s.natReg 591=e+1+2*G K-width K
  second : s.natReg 592=e+1+4*G K-width K
  third : s.natReg 593=e+1+6*G K-width K
  prior : s.natReg 594=e+1+6*G K
  phase : s.natReg 598=phase

structure AddInvariant (K a e c d phase i : ℕ) (heap : ℕ → Option ℕ) (s : State) : Prop where
  state : AddState K a e c d phase i s
  slots : PrintedSlots K e d (6*G K) s
  adds : PrintedAdds K a e d (phase*a+i) s
  source : UniformConvolutionTopologyMachine.Tape K c s
  outside : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap s

theorem AddState.withPC {K a e c d phase i pc : ℕ} {s : State} (h : AddState K a e c d phase i s) :
    AddState K a e c d phase i {s with pc:=pc} := by
  rcases h with ⟨hb,ht,hi,h0,h1,h2,h3,hp⟩
  exact ⟨hb.withPC,ht,hi,h0,h1,h2,h3,hp⟩

theorem AddInvariant.withPC {K a e c d phase i pc : ℕ} {heap : ℕ → Option ℕ} {s : State}
    (h : AddInvariant K a e c d phase i heap s) : AddInvariant K a e c d phase i heap {s with pc:=pc} :=
  ⟨h.state.withPC,h.slots,h.adds,h.source,h.outside⟩

def addInit : List Op := [.add 591 562 581,.mul 597 582 566,.add 591 591 597,.sub 591 591 565,
  .add 592 591 597,.add 593 592 597,.add 594 593 565,.literal 590 0,.literal 598 0]

theorem addInit_code : UniformPreparationRowTableMachine.BlockAt addInit program 235 := by
  intro i hi
  rw [show 235+i=157+(78+i) by omega,tail_lookup]
  change i < 9 at hi
  interval_cases i <;> rfl

theorem addInit_spec (K a e c d : ℕ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d 6 heap s) : AddInvariant K a e c d 0 0 heap (applyBlock addInit s) := by
  have hn:=G_width K
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hslot,hptr,hsource,hprinted,houtside⟩
  constructor
  · constructor
    · constructor
      · constructor <;> simp [applyBlock,addInit,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
      · simpa [Params,applyBlock,addInit,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
      all_goals simp [applyBlock,addInit,Op.apply,writeNat,next,hN,hG]
    all_goals simp [applyBlock,addInit,Op.apply,writeNat,next,hptr,he,ho,ht,hG,hN]
    all_goals omega
  · exact hprinted
  · intro phase i hi;omega
  · exact hsource
  · exact houtside

theorem addInit_peak (K a e c d B : ℕ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d 6 heap s) (hB : budget K a e c d ≤ B) : peak addInit s ≤ B := by
  have hb:=(budget_tail K a e c d).trans hB
  have hn:=G_width K
  have hN:=h.base.Nreg;have hG:=h.base.Greg;have he:=h.base.params.2.2.1
  simp [peak,addInit,Op.peak,Op.apply,writeNat,next,he,h.base.one,h.base.two,hN,hG]
  omega

def addFieldsTrace (phase : ℕ) : List Atom := [.op 245 (.literal 574 0),.op 246 (.literal 577 0),
  .op 247 (.literal 578 0),.branch 248 598 581 249 252 (decide (phase=0))]++
  (if phase=0 then [.op 249 (.add 575 591 590),.op 250 (.add 576 592 590),.jump 251 254]
  else [.op 252 (.add 575 594 590),.op 253 (.add 576 593 590)])

theorem addFieldsTrace_code (phase : ℕ) : TraceCode (addFieldsTrace phase) := by
  unfold addFieldsTrace;split_ifs
  all_goals intro a ha
  all_goals simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Atom.pc,Atom.code,Op.code]
  all_goals rw [tail_absolute _ (by decide)];rfl

theorem addFieldsTrace_spec (K a e c d phase i : ℕ) (s : State)
    (h : AddState K a e c d phase i s) (hp : s.pc=245) (_hphase : phase < 2) :
    traceReady (addFieldsTrace phase) s ∧ (trace (addFieldsTrace phase) s).pc=254 ∧
    Fields (addRow K e phase i) (trace (addFieldsTrace phase) s) ∧
    AddState K a e c d phase i (trace (addFieldsTrace phase) s) ∧
    (trace (addFieldsTrace phase) s).natHeap=s.natHeap := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hptr,hi,h0,h1,h2,h3,hph⟩
  unfold addFieldsTrace;split_ifs with hzero
  all_goals refine ⟨?_,?_,?_,?_,rfl⟩
  all_goals first
    | (apply Fields.mk <;> simp_all [trace,Atom.apply,Op.apply,writeNat,next,addRow,branchOutput])
    | (apply AddState.mk
       · constructor
         · constructor <;> simp [trace,Atom.apply,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
         · simpa [Params,trace,Atom.apply,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
         all_goals simp [trace,Atom.apply,Op.apply,writeNat,next,hN,hG]
       all_goals simp [trace,Atom.apply,Op.apply,writeNat,next,hptr,hi,h0,h1,h2,h3,hph])
    | (simp_all [traceReady,trace,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next])

theorem addFieldsTrace_peak (K a e c d phase i B : ℕ) (s : State)
    (h : AddState K a e c d phase i s) (hi : i < a) (hB : budget K a e c d ≤ B) :
    tracePeak (addFieldsTrace phase) s ≤ B := by
  have hb:=(budget_tail K a e c d).trans hB
  unfold addFieldsTrace;split_ifs
  all_goals simp [tracePeak,Atom.peak,Atom.apply,Op.peak,Op.apply,writeNat,next,h.first,h.second,h.third,h.prior,h.index]
  all_goals split_ifs
  all_goals omega

def addStores : List Op := [.put 570 574,.add 570 570 581,.put 570 575,.add 570 570 581,
  .put 570 576,.add 570 570 581,.put 570 577,.add 570 570 581,.put 570 578,.add 570 570 581,.add 590 590 581]

theorem addStores_code : UniformPreparationRowTableMachine.BlockAt addStores program 254 := by
  intro i hi
  rw [show 254+i=157+(97+i) by omega,tail_lookup]
  change i < 11 at hi
  interval_cases i <;> rfl

theorem addStores_spec (K a e c d phase i : ℕ) (r : Row) (s : State)
    (h : AddState K a e c d phase i s) (hf : Fields r s) :
    AddState K a e c d phase (i+1) (applyBlock addStores s) ∧
    (applyBlock addStores s).natHeap=storeRow s.natHeap (d+5*(6*G K+phase*a+i)) r := by
  rcases h with ⟨⟨⟨hz,ho,ht,h5,h6⟩,⟨hK,ha,he,hc,hd⟩,hN,hG⟩,hptr,hi,h0,h1,h2,h3,hph⟩
  refine ⟨?_,?_⟩
  · constructor
    · constructor
      · constructor <;> simp [applyBlock,addStores,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
      · simpa [Params,applyBlock,addStores,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
      all_goals simp [applyBlock,addStores,Op.apply,writeNat,next,hN,hG]
    all_goals simp [applyBlock,addStores,Op.apply,writeNat,next,hptr,hi,h0,h1,h2,h3,hph,ho]
    all_goals omega
  · simp [applyBlock,addStores,Op.apply,writeNat,next,ho,hptr,hf.opcode,hf.left,hf.right,hf.kind,hf.payload,storeRow,Nat.add_assoc]

theorem addRow_bounds (K e phase i : ℕ) : (addRow K e phase i).opcode=0 ∧ (addRow K e phase i).kind=0 ∧
    (addRow K e phase i).payload=0 ∧ (addRow K e phase i).left ≤ e+1+6*G K+i ∧
    (addRow K e phase i).right ≤ e+1+6*G K+i := by
  unfold addRow branchOutput
  split_ifs
  all_goals simp
  all_goals omega

theorem addStores_peak (K a e c d phase i B : ℕ) (s : State) (h : AddState K a e c d phase i s)
    (hf : Fields (addRow K e phase i) s) (hphase : phase < 2) (hi : i < a)
    (hB : budget K a e c d ≤ B) : peak addStores s ≤ B := by
  have hb:=(budget_tape K a e c d).trans hB
  have hmul : phase*a ≤ a := by simpa using Nat.mul_le_mul_right a (show phase ≤ 1 by omega)
  have hr:=addRow_bounds K e phase i
  simp [peak,addStores,Op.peak,Op.apply,writeNat,next,h.target,h.index,h.one,hf.opcode,hf.left,hf.right,hf.kind,hf.payload]
  omega



theorem addStores_printed (K a e c d phase i : ℕ) (s : State) (hi : i < a) (hphase : phase < 2)
    (h : AddState K a e c d phase i s) (hf : Fields (addRow K e phase i) s)
    (hp : PrintedAdds K a e d (phase*a+i) s) : PrintedAdds K a e d (phase*a+i+1) (applyBlock addStores s) := by
  intro b q hbq
  rw [(addStores_spec K a e c d phase i _ s h hf).2]
  by_cases he : b.val*a+q.val=phase*a+i
  · have hq:=q.isLt
    have hs : b.val=phase ∧ q.val=i := by
      interval_cases phase <;> fin_cases b <;> simp_all <;> omega
    have hqe : q=⟨i,hi⟩ := Fin.ext hs.2
    rw [hqe,hs.1]
    exact storeRow_fields _ _ _
  · have hlt : b.val*a+q.val < phase*a+i := by omega
    have hold:=hp b q hlt
    unfold HeapFields
    rw [storeRow_keeps _ _ _ (d+5*(6*G K+b.val*a+q.val)) (by omega),
      storeRow_keeps _ _ _ (d+5*(6*G K+b.val*a+q.val)+1) (by omega),
      storeRow_keeps _ _ _ (d+5*(6*G K+b.val*a+q.val)+2) (by omega),
      storeRow_keeps _ _ _ (d+5*(6*G K+b.val*a+q.val)+3) (by omega),
      storeRow_keeps _ _ _ (d+5*(6*G K+b.val*a+q.val)+4) (by omega)]
    exact hold

theorem addStores_slots (K a e c d phase i : ℕ) (r : Row) (s : State)
    (h : AddState K a e c d phase i s) (hf : Fields r s) (hp : PrintedSlots K e d (6*G K) s) :
    PrintedSlots K e d (6*G K) (applyBlock addStores s) := by
  intro b q hq
  rw [(addStores_spec K a e c d phase i r s h hf).2]
  unfold HeapFields
  rw [storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)) (by omega),
    storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+1) (by omega),
    storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+2) (by omega),
    storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+3) (by omega),
    storeRow_keeps _ _ _ (d+5*(b.val*G K+q.val)+4) (by omega)]
  exact hp b q hq

theorem addStores_source (K a e c d phase i : ℕ) (r : Row) (s : State)
    (h : AddState K a e c d phase i s) (hf : Fields r s)
    (ht : UniformConvolutionTopologyMachine.Tape K c s) (hd : c+5*G K ≤ d) :
    UniformConvolutionTopologyMachine.Tape K c (applyBlock addStores s) := by
  intro q
  have hq : q.val < G K := q.isLt
  rw [(addStores_spec K a e c d phase i r s h hf).2]
  rw [storeRow_keeps _ _ _ (c+5*q.val) (by omega),storeRow_keeps _ _ _ (c+5*q.val+1) (by omega),
    storeRow_keeps _ _ _ (c+5*q.val+2) (by omega),storeRow_keeps _ _ _ (c+5*q.val+3) (by omega),
    storeRow_keeps _ _ _ (c+5*q.val+4) (by omega)]
  exact ht q

theorem addStores_outside (K a e c d phase i : ℕ) (r : Row) (s : State)
    (h : AddState K a e c d phase i s) (hf : Fields r s) (hi : i < a) (hphase : phase < 2)
    (heap : ℕ → Option ℕ) (ho : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap s) :
    UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap (applyBlock addStores s) := by
  have hmul : phase*a ≤ a := by simpa using Nat.mul_le_mul_right a (show phase ≤ 1 by omega)
  intro address ha
  rw [(addStores_spec K a e c d phase i r s h hf).2,storeRow_keeps _ _ _ address (by omega)]
  exact ho address ha

theorem addFieldsTrace_length (phase : ℕ) : (addFieldsTrace phase).length ≤ 7 := by unfold addFieldsTrace;split_ifs <;> simp

theorem add_iteration (n K a e c d phase i B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : AddInvariant K a e c d phase i heap s) (hp : s.pc=244) (hi : i < a)
    (hphase : phase < 2) (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 20 ∧ u.pc=244 ∧ AddInvariant K a e c d phase (i+1) heap u := by
  have hbound : 300 ≤ B := by have hh:=(budget_code K a e c d).trans hB;omega
  have hc1 : program[244]?=some (.branchLT 590 561 245 266) := by rw [tail_absolute _ (by decide)];rfl
  have hs1 : step program n x s=.running {s with pc:=245} := by
    simp only [UniformMachine.step,hp,hc1,h.state.index,h.state.params.2.1,ite_eq_left hi]
  have hb:=UniformPreparationRowTableMachine.control_run program n B 245 x s hs (by omega) hs1
  let v : State := {s with pc:=245}
  have hf:=addFieldsTrace_spec K a e c d phase i v h.state.withPC rfl hphase
  have hv:=trace_runs (addFieldsTrace phase) n B x v (addFieldsTrace_code _) hb.final_bound hf.1
    (addFieldsTrace_peak K a e c d phase i B v h.state.withPC hi hB)
  let w:=trace (addFieldsTrace phase) v
  have hheap : w.natHeap=s.natHeap := hf.2.2.2.2
  have hslots : PrintedSlots K e d (6*G K) w := by simpa only [PrintedSlots,hheap] using h.slots
  have hadds : PrintedAdds K a e d (phase*a+i) w := by simpa only [PrintedAdds,hheap] using h.adds
  have hsource : UniformConvolutionTopologyMachine.Tape K c w := by simpa only [UniformConvolutionTopologyMachine.Tape,hheap] using h.source
  have houtside : UniformConvolutionTopologyMachine.Outside d (5*(6*G K+2*a)) heap w := by
    simpa only [UniformConvolutionTopologyMachine.Outside,hheap] using h.outside
  have hw:=block_runs addStores program 254 n B x w addStores_code hf.2.1 hv.final_bound
    (by change 254+11 ≤ B;omega) (by simp [readable,addStores,Op.readable])
    (addStores_peak K a e c d phase i B w hf.2.2.2.1 hf.2.2.1 hphase hi hB)
  let z:=applyBlock addStores w
  have hzp : z.pc=265 := by rw [applyBlock_pc,hf.2.1];rfl
  have hc2 : program[265]?=some (.jump 244) := by rw [tail_absolute _ (by decide)];rfl
  have hs2 : step program n x z=.running {z with pc:=244} := by simp only [UniformMachine.step,hzp,hc2]
  have hlast:=UniformPreparationRowTableMachine.control_run program n B 244 x z hw.final_bound (by omega) hs2
  refine ⟨{z with pc:=244},1+(addFieldsTrace phase).length+11+1,((hb.trans hv).trans hw).trans hlast,
    by have hh:=addFieldsTrace_length phase;omega,rfl,?_⟩
  exact ⟨(addStores_spec K a e c d phase i _ w hf.2.2.2.1 hf.2.2.1).1.withPC,
    addStores_slots K a e c d phase i _ w hf.2.2.2.1 hf.2.2.1 hslots,
    addStores_printed K a e c d phase i w hi hphase hf.2.2.2.1 hf.2.2.1 hadds,
    addStores_source K a e c d phase i _ w hf.2.2.2.1 hf.2.2.1 hsource hd,
    addStores_outside K a e c d phase i _ w hf.2.2.2.1 hf.2.2.1 hi hphase heap houtside⟩

theorem add_loop (n K a e c d phase i fuel B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : AddInvariant K a e c d phase i heap s) (hp : s.pc=244) (hi : i+fuel=a)
    (hphase : phase < 2) (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedRuns program n x B s t u ∧ t ≤ 20*fuel ∧ u.pc=244 ∧ AddInvariant K a e c d phase a heap u := by
  induction fuel generalizing i s with
  | zero=>
    have he : i=a := by omega
    subst i
    exact ⟨s,0,.refl hs,by omega,hp,h⟩
  | succ fuel ih=>
    obtain ⟨u,t,hu,ht,hup,hui⟩:=add_iteration n K a e c d phase i B x heap s h hp (by omega) hphase hd hs hB
    obtain ⟨v,q,hv,hq,hvp,hvi⟩:=ih (i+1) u hui hup (by omega) hu.final_bound
    exact ⟨v,t+q,hu.trans hv,by omega,hvp,hvi⟩


theorem postBlock_spec (K a e c d : ℕ) (s : State) (h : Params K a e c d s)
    (hN : s.natReg 402=width K) (hG : s.natReg 404=G K) (hz : s.natReg 580=0) :
    Base K a e c d (applyBlock postBlock s) ∧ (applyBlock postBlock s).natReg 567=0 ∧
    (applyBlock postBlock s).natReg 570=d ∧ (applyBlock postBlock s).natHeap=s.natHeap := by
  rcases h with ⟨hK,ha,he,hc,hd⟩
  refine ⟨?_,?_,?_,rfl⟩
  · constructor
    · constructor <;> simp [applyBlock,postBlock,Op.apply,writeNat,next,hz]
    · simpa [Params,applyBlock,postBlock,Op.apply,writeNat,next] using ⟨hK,ha,he,hc,hd⟩
    all_goals simp [applyBlock,postBlock,Op.apply,writeNat,next,hN,hG,hz]
  all_goals simp [applyBlock,postBlock,Op.apply,writeNat,next,hd,hz]

/-- From ordinary caller arguments through the actual convolution producer and
all six reuse/remap loops, in one continuous program execution. -/
theorem slots_execution (n K a e c d B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Params K a e c d s) (hp : s.pc=0) (hd : c+5*G K ≤ d) (hs : WordBound B s)
    (hB : budget K a e c d ≤ B) : ∃u t heap,
    BoundedRuns program n x B s t u ∧ t ≤ 4*K+95+(19*K+344)*G K ∧ u.pc=165 ∧
    SlotInvariant K a e c d 6 heap u ∧
    ∀ address,(address < c ∨ c+5*G K ≤ address) → heap address=s.natHeap address := by
  obtain ⟨v,t,hv,ht,hvp,htape,hparams,_h565,hN,hG,hzero,hOutside⟩:=convolution_start n K a e c d B x s h hp hs hB
  have hc : 300 ≤ B := by have hh:=(budget_code K a e c d).trans hB;omega
  have hb:=block_runs postBlock program 157 n B x v postBlock_code hvp hv.final_bound
    (by change 157+8 ≤ B;omega) (by simp [readable,postBlock,Op.readable]) (by
      have hh:=(budget_tail K a e c d).trans hB
      simp [peak,postBlock,Op.peak,Op.apply,writeNat,next,hN,hG,hzero,hparams.2.2.2.2]
      omega)
  let w:=applyBlock postBlock v
  have hspec:=postBlock_spec K a e c d v hparams hN hG hzero
  have hwp : w.pc=165 := by rw [applyBlock_pc,hvp];rfl
  have hi : SlotInvariant K a e c d 0 w.natHeap w := by
    refine ⟨hspec.1,hspec.2.1,?_,htape,?_,?_⟩
    · simpa using hspec.2.2.1
    · intro b q hlt;omega
    · intro address _;rfl
  obtain ⟨u,q,hu,hq,hup,hui⟩:=slots_loop n K a e c d 0 6 B x w.natHeap w hi hwp (by omega) hd hb.final_bound hB
  refine ⟨u,t+8+q,w.natHeap,(hv.trans hb).trans hu,by nlinarith,hup,hui,?_⟩
  exact hOutside


theorem add_phase_exit (n K a e c d phase B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : AddInvariant K a e c d phase a heap s) (hp : s.pc=244) (hs : WordBound B s) (hc : 300 ≤ B) :
    BoundedRuns program n x B s 2 {s with pc:=if phase=0 then 267 else 270} := by
  have hc1 : program[244]?=some (.branchLT 590 561 245 266) := by rw [tail_absolute _ (by decide)];rfl
  have hs1 : step program n x s=.running {s with pc:=266} := by
    simp only [UniformMachine.step,hp,hc1,h.state.index,h.state.params.2.1,lt_self_iff_false,ite_false]
  have hb:=UniformPreparationRowTableMachine.control_run program n B 266 x s hs (by omega) hs1
  have hc2 : program[266]?=some (.branchLT 598 581 267 270) := by rw [tail_absolute _ (by decide)];rfl
  have hs2 : step program n x {s with pc:=266}=.running {s with pc:=if phase=0 then 267 else 270} := by
    simp only [UniformMachine.step,hc2,h.state.phase,h.state.one]
    congr 2
    split_ifs <;> omega
  exact hb.trans (UniformPreparationRowTableMachine.control_run program n B (if phase=0 then 267 else 270) x {s with pc:=266}
    hb.final_bound (by split_ifs <;> omega) hs2)

def phaseSwitch : List Atom := [.op 267 (.literal 598 1),.op 268 (.literal 590 0),.jump 269 244]

theorem phaseSwitch_code : TraceCode phaseSwitch := by
  intro a ha
  simp only [phaseSwitch,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  all_goals rw [tail_absolute _ (by decide)];rfl

theorem phaseSwitch_spec (K a e c d : ℕ) (heap : ℕ → Option ℕ) (s : State)
    (h : AddInvariant K a e c d 0 a heap s) (hp : s.pc=267) :
    traceReady phaseSwitch s ∧ (trace phaseSwitch s).pc=244 ∧ AddInvariant K a e c d 1 0 heap (trace phaseSwitch s) := by
  refine ⟨?_,rfl,?_⟩
  · simp [traceReady,phaseSwitch,Atom.ready,Atom.pc,Atom.apply,Op.readable,Op.apply,writeNat,next,hp]
  · constructor
    · rcases h.state with ⟨⟨⟨hz,ho,ht,h5,h6⟩,hparams,hN,hG⟩,hptr,hi,h0,h1,h2,h3,hphase⟩
      constructor
      · constructor
        · constructor <;> simp [trace,phaseSwitch,Atom.apply,Op.apply,writeNat,next,hz,ho,ht,h5,h6]
        · simpa [Params,trace,phaseSwitch,Atom.apply,Op.apply,writeNat,next] using hparams
        all_goals simp [trace,phaseSwitch,Atom.apply,Op.apply,writeNat,next,hN,hG]
      all_goals simp [trace,phaseSwitch,Atom.apply,Op.apply,writeNat,next,hptr,h0,h1,h2,h3]
    · exact h.slots
    · change PrintedAdds K a e d (1*a+0) s
      simpa using h.adds
    · exact h.source
    · exact h.outside

/-- Both addition blocks are literal charged loops, following all six remap
passes. This closes the physical sumThree chronology, including zero-sized a. -/
theorem adds_execution (n K a e c d B : ℕ) (x : Fin n → ℂ) (heap : ℕ → Option ℕ) (s : State)
    (h : SlotInvariant K a e c d 6 heap s) (hp : s.pc=165) (hd : c+5*G K ≤ d)
    (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 40*a+18 ∧ u.pc=270 ∧ AddInvariant K a e c d 1 a heap u := by
  have hc : 300 ≤ B := by have hh:=(budget_code K a e c d).trans hB;omega
  have hc1 : program[165]?=some (.branchLT 567 584 166 235) := by rw [tail_absolute _ (by decide)];rfl
  have hs1 : step program n x s=.running {s with pc:=235} := by
    simp only [UniformMachine.step,hp,hc1,h.slotreg,h.base.six,lt_self_iff_false,ite_false]
  have hb:=UniformPreparationRowTableMachine.control_run program n B 235 x s hs (by omega) hs1
  let v : State := {s with pc:=235}
  have hi:=block_runs addInit program 235 n B x v addInit_code rfl hb.final_bound
    (by change 235+9 ≤ B;omega) (by simp [readable,addInit,Op.readable]) (addInit_peak K a e c d B heap v h.withPC hB)
  let w:=applyBlock addInit v
  have hwp : w.pc=244 := by rw [applyBlock_pc];rfl
  have hw:=addInit_spec K a e c d heap v h.withPC
  obtain ⟨z,t0,hz,ht0,hzp,hzi⟩:=add_loop n K a e c d 0 0 a B x heap w hw hwp (by omega) (by omega) hd hi.final_bound hB
  have hexit0:=add_phase_exit n K a e c d 0 B x heap z hzi hzp hz.final_bound hc
  have hswitchReady:=phaseSwitch_spec K a e c d heap {z with pc:=267} hzi.withPC rfl
  have hswitch:=trace_runs phaseSwitch n B x {z with pc:=267} phaseSwitch_code hexit0.final_bound hswitchReady.1
    (by simp [phaseSwitch,tracePeak,Atom.peak,Op.peak];omega)
  let q:=trace phaseSwitch {z with pc:=267}
  obtain ⟨u,t1,hu,ht1,hup,hui⟩:=add_loop n K a e c d 1 0 a B x heap q hswitchReady.2.2 hswitchReady.2.1
    (by omega) (by omega) hd hswitch.final_bound hB
  have hexit1:=add_phase_exit n K a e c d 1 B x heap u hui hup hu.final_bound hc
  have hcStop : program[270]?=some .halt := by rw [tail_absolute _ (by decide)];rfl
  have hstop : BoundedExecution program n x B {u with pc:=270} 1 {u with pc:=270} :=
    .halt hexit1.final_bound (by simp only [UniformMachine.step,hcStop])
  refine ⟨{u with pc:=270},1+9+t0+2+3+t1+2+1,?_,by omega,rfl,hui.withPC⟩
  exact (((((hb.trans hi).trans hz).trans hexit0).trans hswitch).trans hu).executes (hexit1.executes hstop)


/-- The actual producer writes a contiguous five-field table in list order. -/
def RowTable (rows : List Row) (d : ℕ) (s : State) : Prop :=
  ∀ j r,rows[j]?=some r → HeapFields s.natHeap (d+5*j) r

theorem RowTable.append {xs ys : List Row} {d : ℕ} {s : State}
    (h : RowTable xs d s) (hy : RowTable ys (d+5*xs.length) s) : RowTable (xs++ys) d s := by
  intro j r hj
  by_cases hlt : j < xs.length
  · rw [List.getElem?_append_left hlt] at hj
    exact h j r hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have hv:=hy (j-xs.length) r hj
    rw [show d+5*j=d+5*xs.length+5*(j-xs.length) by omega]
    exact hv

theorem RowTable.ofFn {m : ℕ} {f : Fin m → Row} {d : ℕ} {s : State}
    (h : ∀ i,HeapFields s.natHeap (d+5*i.val) (f i)) : RowTable (List.ofFn f) d s := by
  intro j r hj
  have hlt : j < m := by
    have hv:=List.getElem?_eq_some_iff.mp hj
    obtain ⟨hv,_⟩:=hv
    simpa only [List.length_ofFn] using hv
  have he : f ⟨j,hlt⟩=r := by simpa only [List.getElem?_ofFn,Option.some.injEq,dite_eq_left hlt] using hj
  simpa only [he] using h ⟨j,hlt⟩

theorem slotRows_ofFn (K e slot : ℕ) : slotRows K e slot=
    List.ofFn (fun q : Fin (G K)=>remapRow K e slot (encode (UniformConvolutionDAG.instruction K q))) := by
  simp only [slotRows,UniformConvolutionDAG.records,List.map_map,Function.comp_def]
  exact List.ofFn_eq_map.symm

theorem slotPrefix_length (K e count : ℕ) : ((List.range count).flatMap (slotRows K e)).length=count*G K := by
  induction count with
  | zero=>simp
  | succ count ih=>simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.length_append,ih,slotRows_length];ring

theorem slotPrefix_table (K e d count : ℕ) (s : State)
    (h : ∀slot,slot < count → RowTable (slotRows K e slot) (d+5*(slot*G K)) s) :
    RowTable ((List.range count).flatMap (slotRows K e)) d s := by
  induction count with
  | zero=>intro j r hj;simp at hj
  | succ count ih=>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    apply RowTable.append (ih (fun b hb=>h b (by omega)))
    simpa only [slotPrefix_length] using h count (by omega)

theorem printed_rowTable (K a e d : ℕ) (s : State)
    (hslots : PrintedSlots K e d (6*G K) s) (hadds : PrintedAdds K a e d (2*a) s) :
    RowTable (crossRows K a e) d s := by
  have hSlot : ∀slot,slot < 6 → RowTable (slotRows K e slot) (d+5*(slot*G K)) s := by
    intro slot hs
    rw [slotRows_ofFn]
    apply RowTable.ofFn
    intro q
    have hm : slot*G K ≤ 5*G K := Nat.mul_le_mul_right _ (by omega)
    have hq:=q.isLt
    have hv:=hslots ⟨slot,hs⟩ q (by change slot*G K+q.val < 6*G K;omega)
    simpa only [Fin.val_mk,Nat.mul_add,Nat.add_assoc] using hv
  have hFirst : RowTable (firstAdds K a e) (d+5*(6*G K)) s := by
    apply RowTable.ofFn
    intro q
    have hq:=q.isLt
    have hv:=hadds 0 q (by simp;omega)
    simpa [addRow,Nat.mul_add,Nat.add_assoc] using hv
  have hSecond : RowTable (secondAdds K a e) (d+5*(6*G K+a)) s := by
    apply RowTable.ofFn
    intro q
    have hq:=q.isLt
    have hv:=hadds 1 q (by simp;omega)
    simpa [addRow,Nat.mul_add,Nat.add_assoc] using hv
  unfold crossRows
  have hp:=slotPrefix_table K e d 6 s hSlot
  have hf:=hp.append (by simpa only [slotPrefix_length] using hFirst)
  apply hf.append
  simpa only [List.length_append,slotPrefix_length,firstAdds,List.length_ofFn] using hSecond

/-- One literal271 program prepares all six convolution branches and the two
sumThree add blocks. All source readiness is produced internally from K. -/
theorem execution (n K a e c d B : ℕ) (x : Fin n → ℂ) (s : State)
    (h : Params K a e c d s) (hp : s.pc=0) (hd : c+5*G K ≤ d) (hs : WordBound B s)
    (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 4*K+113+(19*K+344)*G K+40*a ∧
    u.pc=270 ∧ RowTable (crossRows K a e) d u ∧ Params K a e c d u ∧ Frame s u ∧
    UniformConvolutionTopologyMachine.Tape K c u ∧
    ∀ address,(address < c ∨ c+5*G K ≤ address) → (address < d ∨ d+5*(6*G K+2*a) ≤ address) →
      u.natHeap address=s.natHeap address := by
  obtain ⟨v,t,heap,hv,ht,hvp,hvi,hheap⟩:=slots_execution n K a e c d B x s h hp hd hs hB
  obtain ⟨u,q,hu,hq,hup,hui⟩:=adds_execution n K a e c d B x heap v hvi hvp hd hv.final_bound hB
  have he:=hv.executes hu
  have hf:=execution_frame he.executes
  have hSlots : PrintedSlots K e d (6*G K) u := hui.slots
  have hAdds : PrintedAdds K a e d (2*a) u := by simpa only [Nat.one_mul,←two_mul] using hui.adds
  refine ⟨u,t+q,he,by omega,hup,printed_rowTable K a e d u hSlots hAdds,h.frame hf,hf,hui.source,?_⟩
  intro address hc hd'
  exact (hui.outside address hd').trans (hheap address hc)

/-- The contiguous physical tape is exactly the original typed crossDAG
program, with shared prepared-index slots and reciprocal1/N left literal. -/
theorem typed_execution (n K a e c d B : ℕ) (x : Fin n → ℂ) (s : State)
    (ha : a ≤ width K) (he : e ≤ width K) (h : Params K a e c d s)
    (hp : s.pc=0) (hd : c+5*G K ≤ d) (hs : WordBound B s) (hB : budget K a e c d ≤ B) : ∃u t,
    BoundedExecution program n x B s t u ∧ t ≤ 4*K+113+(19*K+344)*G K+40*a ∧
    RowTable ((UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG K a e ha he).program).map encode) d u ∧
    Frame s u ∧ Params K a e c d u ∧ UniformConvolutionTopologyMachine.Tape K c u ∧ u.pc=270 ∧
    ∀ address,(address < c ∨ c+5*G K ≤ address) → (address < d ∨ d+5*(6*G K+2*a) ≤ address) →
      u.natHeap address=s.natHeap address := by
  obtain ⟨u,t,hu,ht,hup,htable,hparams,hf,hTape,hOutside⟩:=execution n K a e c d B x s h hp hd hs hB
  rw [crossRows_typed K a e ha he] at htable
  exact ⟨u,t,hu,ht,htable,hf,hparams,hTape,hup,hOutside⟩



/-- Lossless decoder for the shared seven-N prepared bank. The physical
producer never discards a sign or a non-unit rational numerator. -/
def decodeCrossRow (K : ℕ) (r : Row) : UniformConvolutionDAG.Expr (width K+6*width K) ℕ :=
  if r.opcode=0 then .add r.left r.right
  else if r.opcode=1 then .sub r.left r.right
  else if r.kind=1 then .scale (.prepared ⟨r.payload%(width K+6*width K),Nat.mod_lt _ (by have h:=width_pos K;omega)⟩ false) r.left
  else .scale (.rational ((r.payload : ℚ)⁻¹)) r.left

theorem mapped_encoding_lossless (K e : ℕ) (slot : Fin 6)
    (g : UniformConvolutionDAG.Expr (width K+width K) ℕ)
    (h : UniformConvolutionTopologyMachine.decodeRow K (encode g)=g) :
    decodeCrossRow K (encode (remapExpr K e slot g))=remapExpr K e slot g := by
  cases g with
  | add a b | sub a b=>simp [decodeCrossRow,encode,remapExpr,mapExpr]
  | scale c a=>
    cases c with
    | prepared i sign=>
      cases sign
      · have hcp : (UniformToeplitzCrossDAG.coefficientEmbedding K slot i).val < width K+6*width K :=
          (UniformToeplitzCrossDAG.coefficientEmbedding K slot i).isLt
        simp [decodeCrossRow,encode,remapExpr,mapExpr,UniformToeplitzCrossDAG.mapCoefficient,Nat.mod_eq_of_lt hcp]
      · simp [UniformConvolutionTopologyMachine.decodeRow,encode] at h
    | rational q=>
      have hq : ((q.den : ℚ)⁻¹)=q := by simpa [UniformConvolutionTopologyMachine.decodeRow,encode] using h
      simp [decodeCrossRow,encode,remapExpr,mapExpr,UniformToeplitzCrossDAG.mapCoefficient,hq]

theorem slot_encoding_lossless (K e : ℕ) (slot : Fin 6) :
    (slotRows K e slot.val).map (decodeCrossRow K)=
      (UniformConvolutionDAG.records K).map (remapExpr K e slot) := by
  simp only [slotRows,UniformConvolutionDAG.records,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro q _
  rw [←encode_remap]
  exact mapped_encoding_lossless K e slot _ (UniformConvolutionTopologyMachine.instruction_encoding_lossless K q)

theorem lifted_kernel_exprs (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) (b : Fin 3) :
    (UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.kernelDAG K a e ha he b).program).map
      (fun g=>g.map (liftRef e (2*b.val*G K)))=
      (UniformConvolutionDAG.records K).map (remapExpr K e (UniformToeplitzCrossDAG.firstSlot b))++
      (UniformConvolutionDAG.records K).map (remapExpr K e (UniformToeplitzCrossDAG.secondSlot b)) := by
  rw [kernel_records]
  simp only [List.map_append,List.map_map,Function.comp_def,mapExpr_then_map]
  have hf : (fun x=>liftRef e (2*b.val*G K) (dataRef K e 0 x))=dataRef K e (2*b.val) := funext (lift_first K e b.val)
  have hs : (fun x=>liftRef e (2*b.val*G K) (dataRef K e 1 x))=dataRef K e (2*b.val+1) := funext (lift_second K e b.val)
  rw [hf,hs]
  rfl

theorem cross_encoding_lossless (K a e : ℕ) (ha : a ≤ width K) (he : e ≤ width K) :
    (crossRows K a e).map (decodeCrossRow K)=
      UniformToeplitzCrossDAG.programRecords (UniformToeplitzCrossDAG.crossDAG K a e ha he).program := by
  have h0:=lifted_kernel_exprs K a e ha he 0
  have h1:=lifted_kernel_exprs K a e ha he 1
  have h2:=lifted_kernel_exprs K a e ha he 2
  simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_mul,expr_map_zero] at h0
  change List.map id _=_ at h0
  rw [List.map_id] at h0
  norm_num at h1 h2
  unfold UniformToeplitzCrossDAG.crossDAG
  rw [sumThree_records]
  simp only [kernel_size]
  rw [h0,h1]
  have heq : 2*G K+2*G K=4*G K := by omega
  rw [heq,h2]
  have heq2 : 4*G K+2*G K=6*G K := by omega
  rw [heq2]
  simp only [kernel_output]
  have h1lift (i : ℕ) : liftRef e (2*G K) (branchOutput K e 0 i)=branchOutput K e 1 i := by simpa using branchOutput_lift K e 1 i
  have h2lift (i : ℕ) : liftRef e (4*G K) (branchOutput K e 0 i)=branchOutput K e 2 i := by simpa using branchOutput_lift K e 2 i
  unfold crossRows
  simp only [List.range_succ,List.range_zero,List.flatMap_append,List.flatMap_singleton,List.flatMap_nil,List.map_append]
  have hd0:=slot_encoding_lossless K e 0
  have hd1:=slot_encoding_lossless K e 1
  have hd2:=slot_encoding_lossless K e 2
  have hd3:=slot_encoding_lossless K e 3
  have hd4:=slot_encoding_lossless K e 4
  have hd5:=slot_encoding_lossless K e 5
  norm_num at hd0 hd1 hd2 hd3 hd4 hd5
  rw [hd0,hd1,hd2,hd3,hd4,hd5]
  simp [firstAdds,secondAdds,List.map_ofFn,Function.comp_def,decodeCrossRow,List.append_assoc,h1lift,h2lift,
    UniformToeplitzCrossDAG.firstSlot,UniformToeplitzCrossDAG.secondSlot]

/-- Typed operand occurrences point only to original inputs, the literal zero
port, or previously printed gates. Repeated operands are retained. -/
theorem programRecords_before {r n t : ℕ} (p : UniformReplayPrint.Program r n t) (j : ℕ)
    (g : UniformConvolutionDAG.Expr r ℕ) (hj : (UniformToeplitzCrossDAG.programRecords p)[j]?=some g)
    (a : ℕ) (ha : a∈g.refs) : a < n+1+j := by
  induction p with
  | nil=>simp [UniformToeplitzCrossDAG.programRecords] at hj
  | @step t p gate ih=>
    have hlen:=UniformToeplitzCrossDAG.programRecords_length p
    change (UniformToeplitzCrossDAG.programRecords p++[UniformToeplitzCrossDAG.gateRecord gate])[j]?=some g at hj
    by_cases hlt : j < t
    · rw [List.getElem?_append_left (by omega)] at hj
      exact ih hj
    · have hjlt : j < t+1 := by
        obtain ⟨hv,_⟩:=List.getElem?_eq_some_iff.mp hj
        simpa only [List.length_append,hlen,List.length_singleton] using hv
      have he : j=t := by omega
      subst j
      rw [List.getElem?_append_right (by omega),hlen,Nat.sub_self] at hj
      have hg : UniformToeplitzCrossDAG.gateRecord gate=g := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hj
      rw [←hg] at ha
      exact UniformToeplitzCrossDAG.gateRecord_refs_bound gate a ha

/-- All five fields, including physically meaningful zero fields, are present. -/
theorem rowTable_present {rows : List Row} {d : ℕ} {s : State} (h : RowTable rows d s) :
    ∀ i,i < 5*rows.length → ∃v,s.natHeap (d+i)=some v := by
  intro i hi
  have hq : i/5 < rows.length := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  let j:=i/5
  have ht:=h j (rows[j]'hq) (List.getElem?_eq_getElem hq)
  have hr : i%5 < 5 := Nat.mod_lt _ (by decide)
  have he : i%5+5*(i/5)=i := Nat.mod_add_div i 5
  interval_cases hrem : i%5
  all_goals unfold HeapFields at ht
  · rw [show d+i=d+5*j by omega];exact ⟨_,ht.1⟩
  · rw [show d+i=d+5*j+1 by omega];exact ⟨_,ht.2.1⟩
  · rw [show d+i=d+5*j+2 by omega];exact ⟨_,ht.2.2.1⟩
  · rw [show d+i=d+5*j+3 by omega];exact ⟨_,ht.2.2.2.1⟩
  · rw [show d+i=d+5*j+4 by omega];exact ⟨_,ht.2.2.2.2⟩



/-- Charged topology preparation is polynomial in its convolution width.
This bound concerns printing only; it is not the fast DFT recurrence. -/
theorem runtime_width (K a : ℕ) (ha : a ≤ width K) :
    4*K+113+(19*K+344)*G K+40*a ≤ 2000*(width K)^3 := by
  have hn:=width_pos K
  have hk:=UniformRadixTwoDAG.width_ge_height K
  have hc:=UniformRadixTwoDAG.count_exact K
  have htotal : G K ≤ 5*(width K)^2 := by
    unfold G UniformConvolutionDAG.total
    nlinarith
  have hcoef : 19*K+344 ≤ 363*width K := by omega
  have hm:=Nat.mul_le_mul hcoef htotal
  have hn3 : width K ≤ (width K)^3 := le_self_pow (by omega) (by decide)
  have hone : 1 ≤ (width K)^3 := Nat.succ_le_iff.mpr (pow_pos hn 3)
  nlinarith

theorem budget_width (K a e c d : ℕ) (ha : a ≤ width K) (he : e ≤ width K) :
    budget K a e c d ≤ c+d+2000000*(width K)^4 := by
  have hn:=width_pos K
  have hk:=UniformRadixTwoDAG.width_ge_height K
  have hN2 : width K ≤ (width K)^2 := le_self_pow (by omega) (by decide)
  have hN4 : (width K)^2 ≤ (width K)^4 := by nlinarith [sq_nonneg (width K)]
  have hone : 1 ≤ (width K)^4 := Nat.succ_le_iff.mpr (pow_pos hn 4)
  have hc:=UniformRadixTwoDAG.count_exact K
  have htotal : G K ≤ 5*(width K)^2 := by unfold G UniformConvolutionDAG.total;nlinarith
  have hcount : UniformRadixTwoDAG.count K ≤ 2*(width K)^2 := by nlinarith
  have hs : width K+G K+a+e+K+1 ≤ 10*(width K)^2 := by omega
  have hs2 : (width K+G K+a+e+K+1)^2 ≤ 100*(width K)^4 := by
    have hp:=Nat.pow_le_pow_left hs 2
    nlinarith
  have ht : width K+UniformRadixTwoDAG.count K+K+1 ≤ 5*(width K)^2 := by omega
  have ht2 : (width K+UniformRadixTwoDAG.count K+K+1)^2 ≤ 25*(width K)^4 := by
    have hp:=Nat.pow_le_pow_left ht 2
    nlinarith
  unfold budget UniformRadixInstructionMachine.cap
  omega

theorem program_zero_height : G 0=2 := rfl

theorem fixture_empty_cross : (crossRows 0 0 0).length=12 := by rw [crossRows_length,program_zero_height]

theorem fixture_unit_cross : (crossRows 0 1 1).length=14 := by rw [crossRows_length,program_zero_height]

theorem fixture_ragged_cross : (crossRows 2 3 2).length=198 := by rw [crossRows_length];decide

theorem missing_source_guard (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=174) (hh : s.natHeap (s.natReg 569)=none) : step program n x s=.failed := by
  have hc : program[174]?=some (.loadNat 574 569) := by rw [tail_absolute _ (by decide)];rfl
  simp only [UniformMachine.step,hp,hc,hh]

theorem modulo_zero_guard (n : ℕ) (x : Fin n → ℂ) (s : State)
    (hp : s.pc=167) (hh : s.natReg 582=0) : step program n x s=.failed := by
  have hc : program[167]?=some (.natBinary .mod 572 567 582) := by rw [tail_absolute _ (by decide)];rfl
  simp only [UniformMachine.step,hp,hc,evalNat,hh,ite_true]



end

end ExactFourierCircuits.UniformToeplitzCrossTopologyMachine
