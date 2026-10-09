import UniformFixedNetworkScheduleMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveRuntimeInventory
open UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformFixedCoefficientCodec
open scoped BigOperators

/-- Actual dimensions invoking the same q-child. Padding opcode5 executes m
unit-frame residuals on each of its source roles. There is no ordinary-q fallback. -/
def recursiveDirections (r : Record) : ℕ :=
 if r.opcode=0 then r.dimension else if r.opcode=5 then r.source*UniformFixedNetwork.m else 0

def directions (rs : List Record) : ℕ := (rs.map recursiveDirections).sum

lemma columns (q : ℕ) (r : Record) :
 recursiveDirections (r.withColumns q)=recursiveDirections r := rfl
lemma directions_columns (q : ℕ) (rs : List Record) :
 directions (rs.map (Record.withColumns q))=directions rs := by
 simp only [directions,List.map_map,Function.comp_def,columns]
lemma append (a b : List Record) : directions (a++b)=directions a+directions b := by
 simp [directions]
lemma flatten (rs : List (List Record)) :
 directions rs.flatten=(rs.map directions).sum := by
 induction rs with
 | nil=>rfl
 | cons r rs ih=>simp only [List.flatten_cons,append,List.map_cons,List.sum_cons,ih]
lemma macro_directions {r R n : ℕ} (q : ℕ) (e : Fin r↪Fin R) (a : EncodedMacro r n) :
 recursiveDirections (macroRecord q e a)=(decodeMacro a).residuals := by
 cases a <;> simp [recursiveDirections,macroRecord,decodeMacro,Macro.residuals]
lemma encoded_directions {r R n : ℕ} (q : ℕ) (embedding : Fin r↪Fin R)
 (tape : List (Macro r n)) (small : TapeSmall tape) :
 directions ((encodeTape tape small).map (macroRecord q embedding))=tapeResiduals tape := by
 unfold directions
 simp only [List.map_map,Function.comp_def,macro_directions]
 have h:=congrArg (fun l : List (Macro r n)=>(l.map Macro.residuals).sum) (decode_encodeTape tape small)
 simpa only [List.map_map,Function.comp_def,tapeResiduals] using h

lemma block (q : ℕ) (a : MasterBudget.Invocation ExplicitSeedBudget.h) :
 directions (blockRecords q a)=tapeResiduals (blockTape (fixedBlock a)) := by
 unfold blockRecords encodedBlock
 exact encoded_directions q (fixedBlock a).embedding (blockTape (fixedBlock a)) (fixed_block_small a)

lemma boundary (q : ℕ) (a : MasterBudget.Invocation ExplicitSeedBudget.h) : recursiveDirections (blockBoundary q a)=0 := rfl
lemma terminal_generic (q width roles padded rows pairs : ℕ) (ds ps : List ℕ) :
 directions [⟨3,q,width,0,0,0,rows,0,ds⟩,⟨4,q,width,0,0,0,pairs,0,ps⟩,
  ⟨5,q,width,roles,padded-roles,0,0,0,[]⟩]=(padded-roles)*UniformFixedNetwork.m := by
 simp [directions,recursiveDirections]
lemma terminal (q : ℕ) :
 directions (terminalRecords q)=(W-actualRoles)*UniformFixedNetwork.m := by
 unfold terminalRecords
 rw [directions_columns]
 exact terminal_generic 0 seedWidth actualRoles W bankPairs.length bankPairs.length _ _

lemma cons (r : Record) (rs : List Record) :
 directions (r::rs)=recursiveDirections r+directions rs := rfl

lemma fixedInvocation_sum (f : MasterBudget.Invocation ExplicitSeedBudget.h→ℕ) :
 (fixedInvocations.map f).sum=∑a:MasterBudget.Invocation ExplicitSeedBudget.h,f a := by
 classical
 have all:fixedInvocations.toFinset=Finset.univ :=
  Finset.eq_univ_iff_forall.mpr (fun a=>List.mem_toFinset.mpr (fixedInvocations_cover a))
 rw [←List.sum_toFinset f fixedInvocations_nodup,all]

lemma padding_transfer (total padded actual roles m S : ℕ)
 (eq : actual=roles) (h : total+(padded-roles)*m=S) : total+(padded-actual)*m=S := by
 rw [eq]
 exact h

/-- Exact recursive coefficient of the actual static record tape. -/
theorem schedule_directions (q : ℕ) : directions (scheduleRecords q)=UniformFixedNetwork.S := by
 rw [schedule_chronology,append,cons]
 have marker:recursiveDirections ⟨6,q,seedWidth,actualRoles,W,0,ExplicitSeedBudget.roleBits,0,[]⟩=0 := rfl
 rw [marker,Nat.zero_add,flatten]
 simp only [List.map_map,Function.comp_def,cons,boundary,block,Nat.zero_add]
 rw [fixedInvocation_sum,terminal]
 exact padding_transfer _ W actualRoles ExplicitSeedBudget.roles UniformFixedNetwork.m
  UniformFixedNetwork.S MasterBudget.seed_actual_size fixedMetadata_residual_total

end ExactFourierCircuits.UniformRecursiveRuntimeInventory
