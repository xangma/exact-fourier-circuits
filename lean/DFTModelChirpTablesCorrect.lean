import DFTModelChirpTables

set_option autoImplicit false

namespace ExactFourierCircuits.DFTModelChirpTables
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
noncomputable section

attribute [local irreducible] count width outputTable inputTable kernelTable normalization
  publish setup DFTModelChirp.program DFTModelIntegerScalar.reciprocal

theorem count_run (n L : ℕ) (v : Tape ℂ) : run count ((n,L),v)=⟨n,3,0,True⟩ := by
  simp [count,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem width_run (n L : ℕ) (v : Tape ℂ) : run width ((n,L),v)=⟨L,3,0,True⟩ := by
  simp [width,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

private theorem tab_run (len : Prog false Full w) (body : Prog false Cell sc)
    (f : Full.T) (k : ℕ) (hlen : run len f=⟨k,3,0,True⟩) :
    run (.tab len body) f = (Bill.tab k sc.blank (fun i => run body (f,i))).pay 4 0 := by
  change ((run len f).pass (fun k => Bill.tab k sc.blank (fun i => run body (f,i)))).pay 1 0 = _
  rw [hlen]
  simp [Bill.pass,Bill.pay]
  omega

theorem outputTable_run (n L : ℕ) (v : Tape ℂ) :
    run outputTable ((n,L),v)=
      (Bill.tab n sc.blank (fun i => run forwardCell (((n,L),v),i))).pay 4 0 := by
  unfold outputTable
  exact tab_run _ _ _ _ (count_run n L v)

theorem inputTable_run (n L : ℕ) (v : Tape ℂ) :
    run inputTable ((n,L),v)=
      (Bill.tab L sc.blank (fun i => run inputCell (((n,L),v),i))).pay 4 0 := by
  unfold inputTable
  exact tab_run _ _ _ _ (width_run n L v)

theorem kernelTable_run (n L : ℕ) (v : Tape ℂ) :
    run kernelTable ((n,L),v)=
      (Bill.tab L sc.blank (fun i => run kernelCell (((n,L),v),i))).pay 4 0 := by
  unfold kernelTable
  exact tab_run _ _ _ _ (width_run n L v)

theorem normalization_run (n L : ℕ) (v : Tape ℂ) :
    run normalization ((n,L),v)=⟨(L:ℂ)⁻¹,8*L+10,L,L≠0⟩ := by
  unfold normalization
  change ((run width ((n,L),v)).pass (run DFTModelIntegerScalar.reciprocal)).pay 1 0 = _
  rw [width_run]
  simp only [Bill.pass]
  rw [DFTModelIntegerScalar.reciprocal_run]
  simp [Bill.pay]
  omega

def values (n L : ℕ) (v : Tape ℂ) : Output.T :=
  (v,(Tape.tab n (forward v),(Tape.tab L (inputValue n v),(Tape.tab L (kernelValue n L v),(L:ℂ)⁻¹))))

theorem table_values (n L : ℕ) (v : Tape ℂ) :
    (run outputTable ((n,L),v)).val=Tape.tab n (forward v) ∧
    (run inputTable ((n,L),v)).val=Tape.tab L (inputValue n v) ∧
    (run kernelTable ((n,L),v)).val=Tape.tab L (kernelValue n L v) := by
  refine ⟨?_,?_,?_⟩
  · rw [outputTable_run]
    change (Bill.tab n sc.blank (fun i => run forwardCell (((n,L),v),i))).val = _
    rw [ModelEquivalenceInterpreter.tab_value]
    congr 1
    funext i
    exact congrArg Bill.val (forwardCell_run n L i v)
  · rw [inputTable_run]
    change (Bill.tab L sc.blank (fun i => run inputCell (((n,L),v),i))).val = _
    rw [ModelEquivalenceInterpreter.tab_value]
    congr 1
    funext i
    exact (inputCell_spec n L i v).1
  · rw [kernelTable_run]
    change (Bill.tab L sc.blank (fun i => run kernelCell (((n,L),v),i))).val = _
    rw [ModelEquivalenceInterpreter.tab_value]
    congr 1
    funext i
    exact (kernelCell_spec n L i v).1

private theorem tab_work_bound (k K : ℕ) (f : ℕ → Bill ℂ)
    (hf : ∀i<k,(f i).work≤K) : (Bill.tab k sc.blank f).work+4≤(K+4)*k+6 := by
  rw [ModelEquivalenceInterpreter.tab_work]
  have hs : (∑i∈Finset.range k,(f i).work)≤K*k := by
    calc
      _ ≤ ∑_i∈Finset.range k,K := Finset.sum_le_sum (fun i hi => hf i (Finset.mem_range.mp hi))
      _ = _ := by simp [Nat.mul_comm]
  nlinarith

theorem table_work (n L : ℕ) (v : Tape ℂ) :
    (run outputTable ((n,L),v)).work≤15*n+6 ∧
    (run inputTable ((n,L),v)).work≤34*L+6 ∧
    (run kernelTable ((n,L),v)).work≤64*L+6 := by
  refine ⟨?_,?_,?_⟩
  · rw [outputTable_run]
    apply tab_work_bound n 11
    intro i _
    rw [forwardCell_run]
  · rw [inputTable_run]
    exact tab_work_bound L 30 _ (fun i _ => (inputCell_spec n L i v).2.1)
  · rw [kernelTable_run]
    exact tab_work_bound L 60 _ (fun i _ => (kernelCell_spec n L i v).2.1)

private theorem tab_peak_bound (k K : ℕ) (f : ℕ → Bill ℂ) (hk : k≤K)
    (hf : ∀i<k,(f i).peak≤K) : ((Bill.tab k sc.blank f).pay 4 0).peak≤K := by
  change max (Bill.tab k sc.blank f).peak 0≤K
  rw [ModelEquivalenceInterpreter.tab_peak]
  have hs : (Finset.range k).sup (fun i => (f i).peak)≤K :=
    Finset.sup_le (fun i hi => hf i (Finset.mem_range.mp hi))
  omega

theorem table_peak (n L : ℕ) (v : Tape ℂ) :
    (run outputTable ((n,L),v)).peak≤4*(n+L)+2 ∧
    (run inputTable ((n,L),v)).peak≤4*(n+L)+2 ∧
    (run kernelTable ((n,L),v)).peak≤4*(n+L)+2 := by
  refine ⟨?_,?_,?_⟩
  · rw [outputTable_run]
    apply tab_peak_bound n _ _ (by omega)
    intro i hi
    rw [forwardCell_run]
    dsimp only [Bill.peak]
    omega
  · rw [inputTable_run]
    apply tab_peak_bound L _ _ (by omega)
    intro i hi
    have h := (inputCell_spec n L i v).2.2.1
    omega
  · rw [kernelTable_run]
    apply tab_peak_bound L _ _ (by omega)
    intro i hi
    have h := (kernelCell_spec n L i v).2.2.1
    omega

theorem table_valid (n L : ℕ) (v : Tape ℂ) :
    (run outputTable ((n,L),v)).valid ∧
    (run inputTable ((n,L),v)).valid ∧
    (run kernelTable ((n,L),v)).valid := by
  refine ⟨?_,?_,?_⟩
  · rw [outputTable_run]
    apply (ModelEquivalenceInterpreter.tab_valid _ _ _).2
    intro i _
    rw [forwardCell_run]
    trivial
  · rw [inputTable_run]
    exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun i _ => (inputCell_spec n L i v).2.2.2)
  · rw [kernelTable_run]
    exact (ModelEquivalenceInterpreter.tab_valid _ _ _).2 (fun i _ => (kernelCell_spec n L i v).2.2.2)

theorem publish_value (n L : ℕ) (v : Tape ℂ) :
    (run publish ((n,L),v)).val=values n L v := by
  have hv := table_values n L v
  simp only [publish,Code.run,Atom.run,Bill.one,Bill.pass]
  change (v,((run outputTable ((n,L),v)).val,((run inputTable ((n,L),v)).val,
    ((run kernelTable ((n,L),v)).val,(run normalization ((n,L),v)).val)))) = _
  rw [hv.1,hv.2.1,hv.2.2,normalization_run]
  rfl

theorem publish_work (n L : ℕ) (v : Tape ℂ) :
    (run publish ((n,L),v)).work≤15*n+106*L+33 := by
  obtain ⟨ho,hi,hk⟩ := table_work n L v
  have hn : Code.run normalization () ((n,L),v)=⟨(L:ℂ)⁻¹,8*L+10,L,L≠0⟩ :=
    normalization_run n L v
  simp only [publish,Code.run,Atom.run,Bill.one,Bill.pass,hn]
  dsimp only [run] at ho hi hk
  omega

theorem publish_peak (n L : ℕ) (v : Tape ℂ) :
    (run publish ((n,L),v)).peak≤4*(n+L)+2 := by
  obtain ⟨ho,hi,hk⟩ := table_peak n L v
  have hn : Code.run normalization () ((n,L),v)=⟨(L:ℂ)⁻¹,8*L+10,L,L≠0⟩ :=
    normalization_run n L v
  simp only [publish,Code.run,Atom.run,Bill.one,Bill.pass,hn]
  dsimp only [run] at ho hi hk
  omega

theorem publish_valid (n L : ℕ) (v : Tape ℂ) (hL : 0<L) :
    (run publish ((n,L),v)).valid := by
  obtain ⟨ho,hi,hk⟩ := table_valid n L v
  have hn : Code.run normalization () ((n,L),v)=⟨(L:ℂ)⁻¹,8*L+10,L,L≠0⟩ :=
    normalization_run n L v
  simp only [publish,Code.run,Atom.run,Bill.one,Bill.pass,hn,true_and,and_true]
  exact ⟨ho,hi,hk,hL.ne'⟩

theorem setup_run (n L : ℕ) (z : ℂ) :
    run setup ((n,L),z) =
      ((run DFTModelChirp.program (n,z)).pass (fun v => Bill.one ((n,L),v))).pay 7 0 := by
  simp only [setup,Code.run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  simp only [true_and,and_true,zero_max,max_zero]
  dsimp only [run]
  congr 1
  omega

theorem program_run (n L : ℕ) (z : ℂ) :
    run program ((n,L),z) =
      ((run DFTModelChirp.program (n,z)).pass
        (fun v => run publish ((n,L),v))).pay 9 0 := by
  change ((run setup ((n,L),z)).pass (run publish)).pay 1 0 = _
  rw [setup_run]
  simp [Bill.pass,Bill.one,Bill.pay]
  omega

/-- No coefficient, normalization scalar, or table is supplied as an input. -/
theorem program_value (n L : ℕ) (z : ℂ) (hn : 0<n) (hz : z^(2*n)=1) :
    (run program ((n,L),z)).val=values n L (DFTModelChirp.bank n z) := by
  rw [program_run]
  change (run publish ((n,L),(run DFTModelChirp.program (n,z)).val)).val = _
  rw [DFTModelChirp.program_value n z hn hz,publish_value]

theorem program_valid (n L : ℕ) (z : ℂ) (hL : 0<L) :
    (run program ((n,L),z)).valid := by
  rw [program_run]
  exact ⟨DFTModelChirp.program_valid n z,publish_valid n L _ hL⟩

theorem program_work (n L : ℕ) (z : ℂ) :
    (run program ((n,L),z)).work≤600*(n+L+1) := by
  rw [program_run]
  change (run DFTModelChirp.program (n,z)).work+
    (run publish ((n,L),(run DFTModelChirp.program (n,z)).val)).work+9≤_
  have hc := DFTModelChirp.program_work n z
  have hp := publish_work n L (run DFTModelChirp.program (n,z)).val
  omega

theorem program_peak (n L : ℕ) (z : ℂ) :
    (run program ((n,L),z)).peak≤(n+L+2)^2 := by
  rw [program_run]
  change max (max (run DFTModelChirp.program (n,z)).peak
    (run publish ((n,L),(run DFTModelChirp.program (n,z)).val)).peak) 0≤_
  have hc := DFTModelChirp.program_peak n z
  have hp := publish_peak n L (run DFTModelChirp.program (n,z)).val
  have hm : (n+2)^2≤(n+L+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hl : 4*(n+L)+2≤(n+L+2)^2 := by nlinarith
  omega

end
end ExactFourierCircuits.DFTModelChirpTables
