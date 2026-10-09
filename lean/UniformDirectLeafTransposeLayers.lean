import UniformCalendarRenderDirect
import UniformDirectLeafCacheLeafFinal
set_option autoImplicit false
namespace ExactFourierCircuits.UniformDirectLeafTransposeLayers
open OAI.ExactFourier TypedKernelWords UniformLocalFourierLayers UniformDirectToeplitz
open UniformLayerRestriction UniformTransposeDescriptorMachine
noncomputable section

/-- Actual82 reverses the descriptor order and swaps shear endpoints. Each
swapped shear uses the standard28-phase word, not the reversed original phases. -/
def transposeRender {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 Operation v→List (WordStep C v)
 | .scale i=>[scaleStep i (h ⟨0,hv⟩) h0]
 | .shear i j=>shear ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩
  ⟨i,by intro eq;have val:=congrArg Fin.val eq;exact (ne_of_lt j.isLt) val.symm⟩
  (coefficient h i ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩)

lemma transposeRender_matrix {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0) (op:Operation v):
 wordMatrix (transposeRender h hv h0 op)=(wordMatrix (UniformDirectToeplitz.render h hv h0 op)).transpose:=by
 cases op with
 | scale i=>simp [transposeRender,UniformDirectToeplitz.render,scaleStep,scaleMatrix,WordStep.matrix]
 | shear i j=>
  simp only[transposeRender,UniformDirectToeplitz.render,shear_matrix]
  ext a b
  simp [Matrix.transpose_apply,Matrix.single_apply,Matrix.one_apply,and_comm,eq_comm]

lemma transposeRender_length {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0) (op:Operation v):
 (transposeRender h hv h0 op).length=(UniformDirectToeplitz.render h hv h0 op).length:=by
 cases op with
 | scale i=>rfl
 | shear i j=>simp only[transposeRender,UniformDirectToeplitz.render,shear_length]

lemma transposeRender_restricted {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0) (op:Operation v):
 WordRestricted (transposeRender h hv h0 op):=by
 cases op with
 | scale i=>intro s hs;simp only[transposeRender,List.mem_singleton] at hs;subst s;exact ⟨_,rfl⟩
 | shear i j=>exact direct_shear_restricted _ _ _

lemma reverse_macros_matrix {v:ℕ}{α:Type} (L:List α) (f g:α→List (WordStep C v))
 (same:∀a,wordMatrix (g a)=(wordMatrix (f a)).transpose):
 wordMatrix ((L.reverse.map g).flatten)=(wordMatrix ((L.map f).flatten)).transpose:=by
 induction L with
 | nil=>simp [wordMatrix]
 | cons a L ih=>
  simp only[List.reverse_cons,List.map_append,List.flatten_append,
   List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,wordMatrix_append,ih,same,Matrix.transpose_mul]

def transposeLeafWord {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):List (WordStep C v):=
 (((topology v).reverse).map (transposeRender h hv h0)).flatten

def transposeLeafLayers {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):List (Layer v):=
 serial (transposeLeafWord h hv h0)

/-- Endpoint equality only: no false internal-phase equality is asserted. -/
theorem transposeLeafWord_matrix {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 wordMatrix (transposeLeafWord h hv h0)=(wordMatrix (UniformDirectToeplitz.word h hv h0)).transpose:=by
 rw[transposeLeafWord,reverse_macros_matrix _ _ _ (transposeRender_matrix h hv h0),render_topology]

theorem transposeLeafLayers_matrix {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 UniformLocalFourierLayers.matrix (transposeLeafLayers h hv h0)=
  (UniformLocalFourierLayers.matrix (serial (UniformDirectToeplitz.word h hv h0))).transpose:=by
 simp only[transposeLeafLayers,serial_matrix,transposeLeafWord_matrix]

theorem transposeLeafWord_length {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 (transposeLeafWord h hv h0).length=(UniformDirectToeplitz.word h hv h0).length:=by
 rw[transposeLeafWord,←render_topology h hv h0]
 simp only[List.length_flatten,List.map_map,Function.comp_def,transposeRender_length,
  List.map_reverse,List.sum_reverse]

theorem transposeLeafLayers_length {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 (transposeLeafLayers h hv h0).length=v+14*v*(v-1):=by
 rw[transposeLeafLayers,serial_length,transposeLeafWord_length,word_length]

theorem transposeLeafLayers_restricted {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0):
 ScheduleRestricted (transposeLeafLayers h hv h0):=by
 apply serial_restricted
 intro s hs
 obtain ⟨W,hW,hs⟩:=List.mem_flatten.mp hs
 obtain ⟨op,_hop,rfl⟩:=List.mem_map.mp hW
 exact transposeRender_restricted h hv h0 op s hs

lemma transposeRender_duration {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0)
 (o K:ℕ) (op:Operation v):
 (serial (transposeRender h hv h0 op)).length=
  UniformDirectLeafCacheChronology.duration ((ofOperation o K op).transpose):=by
 rw[serial_length,transposeRender_length]
 simpa only[UniformCalendarRenderDirect.operationLayers,serial_length,
  UniformDirectLeafCacheChronology.duration_transpose] using
  UniformCalendarRenderDirect.operation_length h hv h0 o K op

/-- Actual reversed/swapped record-prefix clock, with the standard local
phases in their printed order. This does not identify reversed internal phases. -/
theorem transpose_leaf_tick {v:ℕ} (h:Fin v→ℂ) (hv:0<v) (h0:h ⟨0,hv⟩≠0)
 (o K:ℕ) (j:Fin (topology v).reverse.length) (p:ℕ)
 (hp:p<UniformDirectLeafCacheChronology.duration
  ((ofOperation o K ((topology v).reverse.get j)).transpose)):
 UniformCalendarRenderTick.tick (transposeLeafLayers h hv h0)
  (UniformDirectLeafCacheChronology.elapsed
   (((leafRecords v o K).reverse.map Record.transpose).take j.val)+p)=
 UniformCalendarRenderTick.tick (serial (transposeRender h hv h0 ((topology v).reverse.get j))) p:=by
 have flat:(((topology v).reverse.map (fun op=>serial (transposeRender h hv h0 op))).flatten)=
  transposeLeafLayers h hv h0:=by
  simp only[transposeLeafLayers,transposeLeafWord,serial,List.map_flatten,List.map_map,Function.comp_def]
 have durationEq:UniformDirectLeafCacheChronology.elapsed
   (((leafRecords v o K).reverse.map Record.transpose).take j.val)=
  (((topology v).reverse.take j.val).map (fun op=>(serial (transposeRender h hv h0 op)).length)).sum:=by
  simp only[leafRecords,←List.map_reverse,List.map_map,←List.map_take,
   UniformDirectLeafCacheChronology.elapsed,List.map_map,Function.comp_def,transposeRender_duration h hv h0 o K]
 rw[durationEq,←flat]
 exact UniformCalendarRenderDirect.flatten_tick (topology v).reverse
  (fun op=>serial (transposeRender h hv h0 op)) j p
  (by rw[transposeRender_duration h hv h0 o K];exact hp)
end
end ExactFourierCircuits.UniformDirectLeafTransposeLayers
