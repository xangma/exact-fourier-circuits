import UniformMachineConjugation
open ExactFourierCircuits UniformMachine

def natCode : NatOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3 | .mod=>4

def fieldCode : FieldOp→ℕ
  | .add=>0 | .sub=>1 | .mul=>2 | .div=>3

def encodeInstruction : Instruction→String
  | .natLiteral d v=>s!"[0,{d},{v}]"
  | .natBinary op d a b=>s!"[1,{natCode op},{d},{a},{b}]"
  | .loadNat d a=>s!"[2,{d},{a}]"
  | .storeNat a r=>s!"[3,{a},{r}]"
  | .branchLT a b y n=>s!"[4,{a},{b},{y},{n}]"
  | .jump t=>s!"[5,{t}]"
  | .halt=>"[6]"
  | .loadScalar d a=>s!"[7,{d},{a}]"
  | .storeScalar a r=>s!"[8,{a},{r}]"
  | .scalarLiteral d v=>s!"[9,{d},{v.num},{v.den}]"
  | .fieldBinary op d a b=>s!"[10,{fieldCode op},{d},{a},{b}]"
  | .length d=>s!"[11,{d}]"
  | .root d q=>s!"[12,{d},{q}]"
  | .input d j=>s!"[13,{d},{j}]"
  | .output j s=>s!"[14,{j},{s}]"




open ExactFourierCircuits.UniformMachineConjugation
namespace Fresh
-- Includes every allowed constructor and all five Nat/four field operators.
def code : Program := [
 .length 3,.natLiteral 0 100,.loadScalar 0 0,.natLiteral 1 101,.loadScalar 1 1,
 .scalarLiteral 2 (3/2),.fieldBinary .mul 3 2 1,.fieldBinary .add 4 0 3,
 .fieldBinary .sub 5 4 0,.natLiteral 2 102,.storeScalar 2 5,.natLiteral 4 0,.output 4 5,
 .natLiteral 5 7,.natLiteral 6 3,.natBinary .mul 7 5 6,.natBinary .div 8 7 6,
 .natBinary .mod 9 7 5,.natLiteral 10 150,.storeNat 10 8,.loadNat 11 10,
 .branchLT 9 6 22 24,.jump 24,.halt,.scalarLiteral 6 1,.fieldBinary .div 7 6 0,
 .natLiteral 12 103,.storeScalar 12 7,.halt]
example : Allowed code := by simp [Allowed,code,instructionAllowed]
example : ¬Allowed [.input 0 0] := by simp [Allowed,instructionAllowed]
example : ¬Allowed [.root 0 0] := by simp [Allowed,instructionAllowed]
example (a b : ℂ) : evalField .div (conjScalar ⟨a,false⟩) (conjScalar ⟨b,false⟩)=
  (evalField .div ⟨a,false⟩ ⟨b,false⟩).map conjScalar := evalField_conjugate _ _ _
example : evalField .div (conjScalar ⟨1,false⟩) (conjScalar ⟨0,false⟩)=none := by
 simp [evalField,conjScalar]
example : (conjScalar ⟨0,true⟩).dependent=true := rfl
#eval IO.FS.writeFile "../logs/uniform-bytecode/machine-conjugation/program.json"
 ("["++String.intercalate "," (code.map encodeInstruction)++"]")
def instructions : List Instruction := [
 .natLiteral 0 11,.length 0,.natBinary .add 0 1 2,.natBinary .sub 0 1 2,
 .natBinary .mul 0 1 2,.natBinary .div 0 1 2,.natBinary .mod 0 1 2,
 .scalarLiteral 0 (-3/7),.fieldBinary .add 0 1 2,.fieldBinary .sub 0 1 2,
 .fieldBinary .mul 0 1 2,.fieldBinary .div 0 1 2,.loadNat 0 1,.storeNat 1 2,
 .loadScalar 0 1,.storeScalar 1 2,.output 1 2,.branchLT 1 2 0 1,.jump 0,.halt]
example : Allowed instructions := by simp [Allowed,instructions,instructionAllowed]
#eval IO.FS.writeFile "../logs/uniform-bytecode/machine-conjugation/instructions.json"
 ("["++String.intercalate "," (instructions.map encodeInstruction)++"]")
#eval IO.FS.writeFile "../logs/uniform-bytecode/machine-conjugation/allowed.json"
 (toString ((instructions++([.input 0 1,.root 0 1]:Program)).map instructionAllowed))
end Fresh
