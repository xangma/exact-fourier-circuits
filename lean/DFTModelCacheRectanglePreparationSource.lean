import DFTModelCacheRectanglePreparationCorrect
import DFTModelCacheDescriptorNode
import DFTModelCacheAxisRootsCorrect

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelCacheRectanglePreparation
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelCacheDescriptor (Row7 rowEncode)
noncomputable section

theorem selected_master (n : ℕ) (hn : 0<n)
    (j : Fin (UniformAllAxisSeedPreparation.axisCount n)) :
    Master (UniformAllAxisSeedPreparation.radix n j) (UniformMasterRootMachine.order n) := by
  let r:=UniformAllAxisSeedPreparation.radix n j
  have hr:0<r:=UniformSelectedCRT.radix_pos n j
  have powBound:2^Nat.clog 2 r≤2*r := by
    by_cases small:r≤1
    · have eq:r=1:=by omega
      simp [eq]
    · have before:=Nat.pow_pred_clog_lt_self (by decide :1<2) (by omega :1<r)
      have positive:=Nat.clog_pos (by decide :1<2) (by omega :1<r)
      simp only [Nat.pred_eq_sub_one] at before
      have eq:Nat.clog 2 r=(Nat.clog 2 r-1)+1:=by omega
      rw [eq,pow_succ]
      omega
  refine ⟨(UniformMasterRootMachine.order_bounds hn).1,
    DFTModelCacheAxisRoots.selected_radix_dvd n j,?_⟩
  have cap:UniformRadixTwoDAG.width (Nat.clog 2 r+2)≤8*r := by
    rw [UniformRadixTwoDAG.width_eq,pow_add]
    norm_num
    omega
  have result:=UniformSeedRankCrossPreparation.selected_divisor n j (Nat.clog 2 r+2) cap
  rw [UniformRadixTwoDAG.width_eq] at result
  exact result

/-- Any row actually returned by the charged node producer has the provenance
used above; the native cutoff, ragged sizes and ordering are not premises. -/
theorem node_produced (r v o : ℕ) (vr : v≤r)
    (i : Fin (run DFTModelCacheDescriptor.node (v,o)).val.2.len) :
    ∃q,ProducedRow r q ∧
      (run DFTModelCacheDescriptor.node (v,o)).val.2.pos i=rowEncode q := by
  have produced:=DFTModelCacheDescriptor.node_value v o
  have bound : i.val<(UniformLocalCacheTreeCoverage.currentRows
      (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)).length := by
    have h:=i.isLt
    have length:=congrArg (fun x=>x.2.len) produced
    simp only [DFTModelCacheDescriptor.listTape,List.length_map] at length
    omega
  let q:=(UniformLocalCacheTreeCoverage.currentRows
    (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task))[i.val]'bound
  refine ⟨q,⟨v,o,vr,List.getElem_mem bound⟩,?_⟩
  have eqv : (run DFTModelCacheDescriptor.node (v,o)).val.2=
    DFTModelCacheDescriptor.listTape ((UniformLocalCacheTreeCoverage.currentRows
      (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)).map rowEncode) :=
    congrArg Prod.snd produced
  have cell:=congrArg (fun t:Tape Row7.T=>t.look i.val Row7.blank) eqv
  rw [Tape.look_of_lt _ _ i.isLt] at cell
  refine cell.trans ?_
  have hmap:i.val<(DFTModelCacheDescriptor.listTape
      ((UniformLocalCacheTreeCoverage.currentRows
        (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)).map rowEncode)).len := by
    simpa only [DFTModelCacheDescriptor.listTape,List.length_map] using bound
  rw [Tape.look_of_lt _ _ hmap]
  change ((UniformLocalCacheTreeCoverage.currentRows
    (⟨v,o,0,0⟩ : UniformLocalCacheTreeMachine.Task)).map rowEncode)[i.val]'_=rowEncode q
  rw [List.getElem_map]

/-- A true node row plus the original master root gives the actual original
seven-block bank. All FFT sizing and scalar preparation occur in `program`. -/
theorem node_specification (r v o D : ℕ) (vr : v≤r) (master : Master r D)
    (i : Fin (run DFTModelCacheDescriptor.node (v,o)).val.2.len) :
    ∃q,ProducedRow r q ∧
      (run DFTModelCacheDescriptor.node (v,o)).val.2.pos i=rowEncode q ∧
      (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).val.1=rowEncode q ∧
      (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).val.2.1=height q ∧
      (∀k:Fin (UniformToeplitzCrossDAG.bankSize (height q)),
        (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).val.2.2.look k.val 0=
          UniformToeplitzCrossDAG.sharedBank (height q)
            (DFTModelCacheSpectrum.rankKernels r (parameters r q) (height q)
              (OAI.ExactFourier.zeta r)) k) ∧
      (run program ((r,rowEncode q),(D,OAI.ExactFourier.zeta D))).valid := by
  obtain ⟨q,source,eq⟩:=node_produced r v o vr i
  refine ⟨q,source,eq,?_,?_,program_sharedBank source master,program_valid source master⟩
  · rw [program_value]
  · rw [program_value]

end
end ExactFourierCircuits.DFTModelCacheRectanglePreparation
