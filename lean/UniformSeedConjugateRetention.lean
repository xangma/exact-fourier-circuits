import UniformSeedConjugatePreparation

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSeedConjugateRetention
open UniformMachine UniformAssembly UniformSeedConjugatePreparation
open UniformPairMachine (prepared)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
noncomputable section

theorem keeps_driver (i : ℕ) (hi : 1250 ≤ i) :
    ∀ins ∈ UniformSeedConjugatePreparation.program,UniformNewtonTableMachine.KeepsNat i ins := by
  have hb : ∀ins ∈ boot,UniformNewtonTableMachine.KeepsNat i ins := by
    simp [boot,bootPrefix,bootMiddle,bootSuffix,UniformNewtonTableMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat]
    omega
  have he : ∀ins ∈ emitHead,UniformNewtonTableMachine.KeepsNat i ins := by
    simp [emitHead,UniformLocalSeedTableMachine.globalHead,UniformLocalSeedTableMachine.globalPointer,
      UniformLocalSeedTableMachine.globalSetup,override,UniformReciprocalMachine.Op.code,
      UniformNewtonTableMachine.KeepsNat]
    omega
  have hl := UniformReciprocalMachine.keeps_relocate i 15 316 (local_keeps_driver i (by omega))
  have hc := UniformReciprocalMachine.keeps_relocate i 345 465
    (UniformAllAxisSeedPreparation.compact_keeps_driver i (by omega))
  have ht : ∀ins ∈ ([.halt] : Program),UniformNewtonTableMachine.KeepsNat i ins := by
    simp [UniformNewtonTableMachine.KeepsNat]
  unfold UniformSeedConjugatePreparation.program
  exact UniformReciprocalMachine.keeps_append i
    (UniformReciprocalMachine.keeps_append i
      (UniformReciprocalMachine.keeps_append i
        (UniformReciprocalMachine.keeps_append i hb hl) he) hc) ht

theorem driver_frame {n B t : ℕ} {x : Fin n → ℂ} {s u : State}
    (h : BoundedExecution UniformSeedConjugatePreparation.program n x B s t u)
    (i : ℕ) (hi : 1250 ≤ i) : u.natReg i=s.natReg i :=
  UniformNewtonTableMachine.Executes.keeps_nat h.executes (keeps_driver i hi)

/-- Strengthen the physical compact copier frame to both sides of its five
lanes. Higher future conjugate banks may therefore survive subsequent calls. -/
theorem copy_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hp:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) s)
    (hpc:s.pc=345) (h117:s.natReg 117=radix n j)
    (h118:s.natReg 118=UniformGlobalLocalPreparation.resultBase n (radix n j))
    (h119:s.natReg 119=UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
    (h120:s.natReg 120=destination n) (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (40*radix n j+71) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    UniformLocalSeedTableMachine.Strided.Outside (destination n) (5*radix n j) s.scalarHeap u ∧ u.natHeap=s.natHeap ∧
    (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.pc=465 := by
  let B:=(n+2)^19
  let r:=radix n j
  let e:State:={s with pc:=0}
  obtain ⟨hcode,hpool,_⟩:=word_setup hn j
  obtain ⟨ha,hG⟩:=UniformLocalSeedTableMachine.selected_source_bounds n j
  change UniformGlobalLocalPreparation.resultBase n r+8*r+5 ≤ UniformLocalSeedTableMachine.poolBase n at ha
  change UniformGlobalLocalPreparation.rootSource n r+1+r ≤ UniformLocalSeedTableMachine.poolBase n at hG
  obtain ⟨u,hu,hcompact,houtside,hframe,_⟩:=UniformLocalSeedTableMachine.execution_from_local n x r
    (UniformGlobalLocalPreparation.resultBase n r) (UniformGlobalLocalPreparation.rootSource n r+1)
    (destination n) B (axisRoot r) e (UniformGlobalLocalPreparation.radix_pos n j)
    (ha.trans (pool_before_destination n)) (hG.trans (pool_before_destination n)) hpool (by omega)
    hp hg rfl h117 h118 h119 h120 (changePC_bound B s 0 hs (by omega))
  have hplaced:=UniformBoundedAssembly.boundedExecution_placed compact_code
    (by rw [UniformLocalSeedTableMachine.program_length];omega :345+UniformLocalSeedTableMachine.program.length ≤ B)
    (by omega :465 ≤ B) hu
  have heq:placed 345 e=s:=by change {s with pc:=345}=s;rw [←hpc]
  rw [heq] at hplaced
  refine ⟨{u with pc:=465},hplaced,hcompact,?_,hframe.1.1,?_,hframe.1.2.1,hframe.1.2.2.1,rfl⟩
  · exact houtside
  · intro i hi hj;exact hframe.2 i (Or.inl (by omega)) (by omega)

theorem emit_execution {n : ℕ} (hn:0<n) (x : Fin n → ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s)
    (hp:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) s)
    (hg:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) s)
    (hpc:s.pc=316) (h110:s.natReg 110=j.val)
    (hd:s.natReg 1247=destination n) (hz:s.natReg 1240=0)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedRuns program n x ((n+2)^19) s (40*radix n j+100) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    UniformLocalSeedTableMachine.Strided.Outside (destination n) (5*radix n j) s.scalarHeap u ∧ u.natHeap=s.natHeap ∧
    (∀i,100 ≤ i → i ≤ 106 → u.natReg i=s.natReg i) ∧ u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧u.pc=465 := by
  obtain ⟨hinit,hinitPC⟩:=emit_initialize hn x j s hm hpc h110 hd hz hs
  obtain ⟨h117,h118,h119,h120⟩:=emittedHeader_registers j s hm hd hz
  have hh:=(emittedHeader_heap s (radix n j)).1
  have hpe:UniformNewtonTableMachine.PreparedOutputs (radix n j) (axisRoot (radix n j))
      (UniformGlobalLocalPreparation.resultBase n (radix n j)) (emittedHeader s (radix n j)):=by
    intro i q;exact (congrFun hh _).trans (hp i q)
  have hge:UniformReciprocalMachine.GPrefix (radix n j) (UniformGlobalLocalPreparation.rootSource n (radix n j)+1)
      (OAI.ExactFourier.NewtonFourier.invH (axisRoot (radix n j))) (emittedHeader s (radix n j)):=by
    intro i hi;exact (congrFun hh _).trans (hg i hi)
  obtain ⟨u,hu,hcompact,houtside,hNat,hsaved,hout,hroot,hupc⟩:=copy_execution hn x j
    (emittedHeader s (radix n j)) hpe hge hinitPC h117 h118 h119 h120 hinit.final_bound
  refine ⟨u,?_,hcompact,?_,?_,?_,?_,?_,hupc⟩
  · convert hinit.trans hu using 1
    omega
  · intro i hi;exact (houtside i hi).trans (congrFun hh i)
  · exact hNat.trans (emittedHeader_heap s (radix n j)).2.1
  · intro i hi hj;exact (hsaved i hi hj).trans (emittedHeader_saved s (radix n j) i hi hj)
  · exact hout.trans (emittedHeader_heap s (radix n j)).2.2.1
  · exact hroot.trans (emittedHeader_heap s (radix n j)).2.2.2

theorem execution {n : ℕ} (hn:0<n) (x : Fin n→ℂ) (j : Fin (O.axisCount n)) (s : State)
    (hm:Metadata n s) (ho:UniformInitialPreparation.Operands n x s)
    (hr:O.Retained n (O.axisCount n) s) (hpc:s.pc=0) (hj:s.natReg 110=j.val)
    (hs:WordBound ((n+2)^19) s) : ∃u,
    BoundedExecution program n x ((n+2)^19) s
      (UniformReciprocalMachine.completeRuntime (radix n j)+40*radix n j+148) u ∧
    UniformLocalSeedTableMachine.Compact (radix n j) (destination n) (axisRoot (radix n j)) u ∧
    ConjugateCompact (radix n j) (destination n) u ∧
    Metadata n u ∧ UniformInitialPreparation.Operands n x u ∧ O.Retained n (O.axisCount n) u ∧
    (UniformSeedConjugatePreparation.Frame n s u) ∧
    (∀i,destination n + 5*radix n j ≤ i → u.scalarHeap i=s.scalarHeap i) ∧ u.pc=465 := by
  let B:=(n+2)^19
  let b:=bootState n s
  let e:State:={b with pc:=0}
  obtain ⟨hc,_,_⟩:=word_setup hn j
  have hboot:=boot_execution hn x j s hm hr hpc hs
  have hbf:=boot_protected n s
  have hme:Metadata n e:=(hbf.metadata hm).transport (fun _ _=>rfl) (fun _ _=>rfl)
  have hoe:UniformInitialPreparation.Operands n x e:=(hbf.operands ho).transport rfl
  have hre:O.Retained n (O.axisCount n) e:=hr.transport_high
    (fun i _=>congrFun (boot_frames n s).1 i) (fun i _=>congrFun (boot_frames n s).2.1 i)
  have hje:e.natReg 110=j.val:=((boot_frames n s).2.2.1 110 (by decide)).trans hj
  have heB:WordBound B e:=changePC_bound B b 0 hboot.final_bound (by omega)
  obtain ⟨v,hv,hmv,hov,hp,hg,_,hvf,hvpc,hvpool⟩:=
    UniformConjugateLocalPreparation.preparation_execution_budget hn x j e hme hoe rfl hje heB
  have hl:=UniformBoundedAssembly.boundedExecution_placed local_code
    (by rw [UniformConjugateLocalPreparation.program_length];omega :15+UniformConjugateLocalPreparation.program.length ≤ B)
    (by omega :316 ≤ B) hv
  have heq:placed 15 e=b:=by change {b with pc:=15}=b;rw [←boot_pc hpc]
  rw [heq] at hl
  let v':State:={v with pc:=316}
  have hvd:v'.natReg 1247=destination n:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes (local_keeps_driver 1247 (by decide))).trans
      (boot_registers s hm).1
  have hvz:v'.natReg 1240=0:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes (local_keeps_driver 1240 (by decide))).trans
      (boot_registers s hm).2
  have hvj:v'.natReg 110=j.val:=
    (UniformNewtonTableMachine.Executes.keeps_nat hv.executes local_keeps_index).trans hje
  obtain ⟨u,hu,hcompact,houtside,hNat,hsaved,hout,hroot,hupc⟩:=emit_execution hn x j v'
    (hmv.transport (fun _ _=>rfl) (fun _ _=>rfl)) hp hg rfl hvj hvd hvz hl.final_bound
  have hhalt:BoundedExecution program n x B u 1 u:=.halt hu.final_bound (by simp [step,hupc,halt_code])
  have hNatHigh:∀i,copyBase n ≤ i → u.natHeap i=s.natHeap i:=by
    intro i hi
    exact (congrFun hNat i).trans ((hvf.2.1 i hi).trans (congrFun (boot_frames n s).2.1 i))
  have hlow:∀i,i<UniformConjugateLocalPreparation.globalEnd n → u.scalarHeap i=s.scalarHeap i:=by
    intro i hi
    have hid:i<destination n:=by
      have hb:=pool_before_destination n
      unfold UniformLocalSeedTableMachine.poolBase at hb
      change UniformGlobalLocalPreparation.globalEnd n+17*len n+16 ≤ destination n at hb
      change i<UniformGlobalLocalPreparation.globalEnd n at hi
      omega
    exact (houtside i (Or.inl hid)).trans ((hvf.1 i hi).trans (congrFun (boot_frames n s).1 i))
  have hf:UniformConjugateLocalPreparation.Frame n s u:=by
    refine ⟨hlow,hNatHigh,?_,?_,?_⟩
    · intro i hi hjj
      exact (hsaved i hi hjj).trans ((hvf.2.2.1 i hi hjj).trans ((boot_frames n s).2.2.1 i (by omega)))
    · exact hout.trans (hvf.2.2.2.1.trans (boot_frames n s).2.2.2.1)
    · exact hroot.trans (hvf.2.2.2.2.trans (boot_frames n s).2.2.2.2)
  have hpoolFrame:∀i,UniformLocalSeedTableMachine.poolBase n ≤ i → i<destination n →
      u.scalarHeap i=s.scalarHeap i:=by
    intro i hi hid
    exact (houtside i (Or.inl hid)).trans ((hvpool i hi).trans (congrFun (boot_frames n s).1 i))
  have hrv:O.Retained n (O.axisCount n) v':=hre.transport_high hvpool hvf.2.1
  have hret:O.Retained n (O.axisCount n) u:=hrv.transport_before (fun i hi=>houtside i (Or.inl hi)) hNat
  have hpf:UniformAllAxisSeedPreparation.ProtectedFrame n s u:=
    ⟨fun i hi _=>hNatHigh i hi,hlow,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2⟩
  refine ⟨u,?_,hcompact,conjugateCompact_of_compact (UniformConjugateLocalPreparation.radix_pos n j) hcompact,
    hpf.metadata hm,hpf.operands ho,hret,⟨hf,hpoolFrame⟩,?_,hupc⟩
  · convert hboot.executes (hl.executes (hu.executes hhalt)) using 1
    dsimp only [radix]
    omega
  · intro i hi
    have hip:UniformLocalSeedTableMachine.poolBase n ≤ i:=by
      have hd:=pool_before_destination n
      omega
    exact (houtside i (Or.inr hi)).trans ((hvpool i hip).trans (congrFun (boot_frames n s).1 i))



end
end ExactFourierCircuits.UniformSeedConjugateRetention
