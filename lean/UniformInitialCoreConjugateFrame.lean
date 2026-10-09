import UniformAllAxisConjugatePreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformInitialCoreConjugateFrame
open UniformMachine UniformAssembly
open UniformNewtonTableMachine (KeepsNat)

lemma seed_boot_keeps (q:ℕ) (lo:200≤ q) (hi:q≤ 209):
 ∀ins∈UniformSeedConjugatePreparation.boot,KeepsNat q ins:=by
 simp [UniformSeedConjugatePreparation.boot,UniformSeedConjugatePreparation.bootPrefix,
  UniformSeedConjugatePreparation.bootMiddle,UniformSeedConjugatePreparation.bootSuffix,
  UniformNewtonTableMachine.Op.code,KeepsNat]
 omega

lemma seed_keeps (q:ℕ) (lo:200≤ q) (hi:q≤ 209):
 ∀ins∈UniformSeedConjugatePreparation.program,KeepsNat q ins:=by
 have hb:=seed_boot_keeps q lo hi
 have he:∀ins∈UniformSeedConjugatePreparation.emitHead,KeepsNat q ins:=by
  simp [UniformSeedConjugatePreparation.emitHead,UniformLocalSeedTableMachine.globalHead,
   UniformLocalSeedTableMachine.globalPointer,UniformLocalSeedTableMachine.globalSetup,
   UniformSeedConjugatePreparation.override,UniformReciprocalMachine.Op.code,KeepsNat]
  omega
 have hl:=UniformReciprocalMachine.keeps_relocate q 15 316
  (UniformSeedConjugatePreparation.local_keeps_driver q lo)
 have hc:=UniformReciprocalMachine.keeps_relocate q 345 465
  (UniformAllAxisSeedPreparation.compact_keeps_driver q (by omega))
 have ht:∀ins∈([.halt]:Program),KeepsNat q ins:=by simp [KeepsNat]
 unfold UniformSeedConjugatePreparation.program
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q hb hl) he) hc) ht

lemma program_keeps (q:ℕ) (lo:200≤ q) (hi:q≤ 209):
 ∀ins∈UniformAllAxisConjugatePreparation.program,KeepsNat q ins:=by
 have hb:=seed_boot_keeps q lo hi
 have hhead:∀ins∈UniformAllAxisConjugatePreparation.head,KeepsNat q ins:=by
  unfold UniformAllAxisConjugatePreparation.head
  apply UniformReciprocalMachine.keeps_append q
  · apply UniformReciprocalMachine.keeps_append q hb
    simp [UniformAllAxisConjugatePreparation.boot,UniformNewtonTableMachine.Op.code,KeepsNat]
    omega
  · simp [KeepsNat];omega
 have hs:=UniformReciprocalMachine.keeps_relocate q 29 495 (seed_keeps q lo hi)
 have hp:∀ins∈(UniformAllAxisConjugatePreparation.pointer.map UniformNewtonTableMachine.Op.code),KeepsNat q ins:=by
  simp [UniformAllAxisConjugatePreparation.pointer,UniformNewtonTableMachine.Op.code,KeepsNat];omega
 have hw:∀ins∈([.loadNat 1711 1710]:Program),KeepsNat q ins:=by simp [KeepsNat];omega
 have hc:∀ins∈(UniformAllAxisConjugatePreparation.copySetup.map UniformNewtonTableMachine.Op.code),KeepsNat q ins:=by
  simp [UniformAllAxisConjugatePreparation.copySetup,UniformNewtonTableMachine.Op.code,KeepsNat];omega
 have hcopy:=UniformReciprocalMachine.keeps_relocate q 505 515
  (show ∀ins∈UniformScalarCopyMachine.program,KeepsNat q ins from by
   simp [UniformScalarCopyMachine.program,KeepsNat];omega)
 have hpost:∀ins∈(UniformAllAxisConjugatePreparation.post.map UniformNewtonTableMachine.Op.code),KeepsNat q ins:=by
  simp [UniformAllAxisConjugatePreparation.post,UniformNewtonTableMachine.Op.code,KeepsNat];omega
 have hend:∀ins∈([.jump 27,.halt]:Program),KeepsNat q ins:=by simp [KeepsNat]
 unfold UniformAllAxisConjugatePreparation.program
 exact UniformReciprocalMachine.keeps_append q
  (UniformReciprocalMachine.keeps_append q
   (UniformReciprocalMachine.keeps_append q
    (UniformReciprocalMachine.keeps_append q
     (UniformReciprocalMachine.keeps_append q
      (UniformReciprocalMachine.keeps_append q
       (UniformReciprocalMachine.keeps_append q hhead hs) hp) hw) hc) hcopy) hpost) hend

lemma execution_header {n B t:ℕ} {x:Fin n→ ℂ} {s u:State}
 (run:BoundedExecution UniformAllAxisConjugatePreparation.program n x B s t u)
 (header:UniformAllAxisSeedPreparation.Header n (UniformAllAxisSeedPreparation.axisCount n) s):
 UniformAllAxisSeedPreparation.Header n (UniformAllAxisSeedPreparation.axisCount n) u:=by
 have frame:∀q,200≤ q→ q≤ 209→ u.natReg q=s.natReg q:=by
  intro q lo hi
  exact UniformNewtonTableMachine.Executes.keeps_nat run.executes (program_keeps q lo hi)
 exact ⟨(frame _ (by omega) (by omega)).trans header.index,
  (frame _ (by omega) (by omega)).trans header.offset,
  (frame _ (by omega) (by omega)).trans header.count,
  (frame _ (by omega) (by omega)).trans header.one,
  (frame _ (by omega) (by omega)).trans header.directory,
  (frame _ (by omega) (by omega)).trans header.zero⟩

end ExactFourierCircuits.UniformInitialCoreConjugateFrame
