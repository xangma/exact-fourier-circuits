import DFTModelCacheHeightRows
import DFTModelCacheBucketRaw

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelCacheHeight
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open UniformToeplitzCrossDAG
noncomputable section

abbrev nativeInput {r n G:ℕ} (p:UniformReplayPrint.Program r n G)
 (A C P d:ℕ) (enabled:Bool) (t:Tape ℕ):Input.T :=
 input n A C P d enabled t
  (Tape.tab G (fun j=>(UniformDAGBucketMachine.order G (UniformDAGBucketMachine.typedDepth p))[j]?.getD 0))
  (Tape.tab (G+2) (fun j=>UniformDAGBucketMachine.offset G j (UniformDAGBucketMachine.typedDepth p)))

def rowTape (xs:List ShearRow):Tape Row.T :=
 Tape.tab xs.length (fun j=>(xs.map row3)[j]?.getD Row.blank)

theorem fields_of_encoded {r n G T:ℕ} (p:UniformReplayPrint.Program r n G)
 (t:Tape ℕ) (s:UniformMachine.State)
 (encoded:UniformDAGDepthMachine.EncodedTape p T s)
 (copied:DFTModelCacheDAGDepth.CopiedTopology G T t s):
 Fields G (UniformCrossShearTableMachine.rowAt p) t := by
 have ht:=UniformCrossShearTableMachine.tape_of_typed p s encoded
 intro i hi
 have hs:=ht i hi
 have get (j:ℕ) (hj:j<5) := copied.2 (5*i+j) (by omega)
 refine ⟨?_,?_,?_,?_,?_⟩
 · have h0:s.natHeap (T+5*i)=some (t.look (5*i) 0):=by simpa using get 0 (by omega)
   exact Option.some.inj (h0.symm.trans hs.1)
 · exact Option.some.inj ((get 1 (by omega)).symm.trans hs.2.1)
 · exact Option.some.inj ((get 2 (by omega)).symm.trans hs.2.2.1)
 · exact Option.some.inj ((get 3 (by omega)).symm.trans hs.2.2.2.1)
 · exact Option.some.inj ((get 4 (by omega)).symm.trans hs.2.2.2.2)

theorem row_kind {r n G:ℕ} (p:UniformReplayPrint.Program r n G) (j:ℕ):
 (UniformCrossShearTableMachine.rowAt p j).kind≤1 := by
 unfold UniformCrossShearTableMachine.rowAt
 cases UniformCrossShearTableMachine.exprAt p j with
 | add a b=>simp [UniformConvolutionTopologyMachine.encode]
 | sub a b=>simp [UniformConvolutionTopologyMachine.encode]
 | scale c a=>cases c <;>simp [UniformConvolutionTopologyMachine.encode]

theorem native_rows {n G:ℕ} (K A C Z P d:ℕ)
 (p:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize K) n G)
 (enabled:Bool) (t:Tape ℕ) (hd:d≤G)
 (fields:Fields G (UniformCrossShearTableMachine.rowAt p) t)
 (good:∀g∈programRecords p,
   UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K) g):
 rowsPrefix (nativeInput p A C P d enabled t) (slotCount (nativeInput p A C P d enabled t))=
 ((UniformCrossDepthReplayPreparation.bucket p enabled d).map
  (UniformCrossShearTableMachine.shiftedRow A
   (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize K) C Z P))).map row3 := by
 rw [selected_rows n A C P G d enabled t (UniformCrossShearTableMachine.rowAt p)
  (UniformDAGBucketMachine.typedDepth p) hd (UniformDAGBucketMachine.typedDepth_bound p)
  fields (fun i _=>row_kind p i)]
 rw [UniformCrossDepthReplayPreparation.bucket_rows K A C Z P p enabled d good]

theorem native_value {n G:ℕ} (K A C Z P d:ℕ)
 (p:UniformReplayPrint.Program (UniformToeplitzCrossDAG.bankSize K) n G)
 (enabled:Bool) (t:Tape ℕ) (hd:d≤G)
 (fields:Fields G (UniformCrossShearTableMachine.rowAt p) t)
 (good:∀g∈programRecords p,
   UniformCrossShearTableMachine.GoodExpr (UniformRadixTwoDAG.width K) g):
 (run program (nativeInput p A C P d enabled t)).val=
 rowTape ((UniformCrossDepthReplayPreparation.bucket p enabled d).map
  (UniformCrossShearTableMachine.shiftedRow A
   (UniformCrossShearTableMachine.locations (UniformToeplitzCrossDAG.bankSize K) C Z P))) := by
 rw [program_value,native_rows K A C Z P d p enabled t hd fields good]
 simp only [rowTape,List.length_map]

/-- Indexed Row3 equality to a real source table, including duplicate occurrences. -/
def ProducedRows (D:ℕ) (v:Tape Row.T) (s:UniformMachine.State):Prop :=
 ∀j,j<v.len→s.natHeap (D+3*j)=some (v.look j Row.blank).1 ∧
 s.natHeap (D+3*j+1)=some (v.look j Row.blank).2.1 ∧
 s.natHeap (D+3*j+2)=some (v.look j Row.blank).2.2

theorem producedRows_table (D:ℕ) (xs:List ShearRow) (s:UniformMachine.State)
 (table:UniformCrossShearTableMachine.Table D xs s):ProducedRows D (rowTape xs) s := by
 intro j hj
 change j<xs.length at hj
 have h:=table j hj
 have value:(rowTape xs).look j Row.blank=row3 xs[j]:=by
   unfold rowTape Tape.look
   split
   · simp only [Tape.tab,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some]
   · contradiction
 rw [value]
 exact h

end
end ExactFourierCircuits.DFTModelCacheHeight
