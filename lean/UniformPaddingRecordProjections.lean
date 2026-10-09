import UniformNativeScheduleSemantics

set_option autoImplicit false
namespace ExactFourierCircuits.UniformPaddingRecordProjections
open UniformMachine UniformFixedNetwork UniformFixedNetworkScheduleMachine UniformNativeScheduleSemantics

/-- Project before specializing the astronomical fixed role cardinality. -/
lemma dest_of_eq {r:Record} {o q w R S i d c:ℕ} {bs:List ℕ}
 (h:r=⟨o,q,w,R,S,i,d,c,bs⟩):r.dest=R:=congrArg Record.dest h
lemma source_of_eq {r:Record} {o q w R S i d c:ℕ} {bs:List ℕ}
 (h:r=⟨o,q,w,R,S,i,d,c,bs⟩):r.source=S:=congrArg Record.source h
lemma opcode_of_eq {r:Record} {o q w R S i d c:ℕ} {bs:List ℕ}
 (h:r=⟨o,q,w,R,S,i,d,c,bs⟩):r.opcode=o:=congrArg Record.opcode h
lemma columns_of_eq {r:Record} {o q w R S i d c:ℕ} {bs:List ℕ}
 (h:r=⟨o,q,w,R,S,i,d,c,bs⟩):r.columns=q:=congrArg Record.columns h
lemma width_of_eq {r:Record} {o q w R S i d c:ℕ} {bs:List ℕ}
 (h:r=⟨o,q,w,R,S,i,d,c,bs⟩):r.width=w:=congrArg Record.width h
lemma length_of_padding_eq {r:Record} {q w R S:ℕ}
 (h:r=⟨5,q,w,R,S,0,0,0,[]⟩):r.data.length=8:=by
 rw [h,Record.data_length]
 rfl

/-- This is the actual third terminal descriptor, without enumerating seed tables. -/
lemma record(q:ℕ):Instruction.record q .padding=⟨5,q,seedWidth,actualRoles,W-actualRoles,0,0,0,[]⟩:=by
 exact Record.withColumns_literal q 5 seedWidth actualRoles (W-actualRoles) 0 0 0 []
lemma dest(q:ℕ):(Instruction.record q .padding).dest=actualRoles:=
 dest_of_eq (R:=actualRoles) (record q)
lemma source(q:ℕ):(Instruction.record q .padding).source=W-actualRoles:=
 source_of_eq (S:=W-actualRoles) (record q)
lemma opcode(q:ℕ):(Instruction.record q .padding).opcode=5:=
 opcode_of_eq (o:=5) (record q)
lemma columns(q:ℕ):(Instruction.record q .padding).columns=q:=
 columns_of_eq (q:=q) (record q)
lemma width(q:ℕ):(Instruction.record q .padding).width=seedWidth:=
 width_of_eq (w:=seedWidth) (record q)
lemma length(q:ℕ):(Instruction.record q .padding).data.length=8:=
 length_of_padding_eq (record q)
end ExactFourierCircuits.UniformPaddingRecordProjections
