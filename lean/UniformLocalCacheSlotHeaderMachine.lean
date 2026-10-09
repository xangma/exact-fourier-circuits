import UniformLocalBroadcastPoolMachine
import UniformForwardMatchingFactorHeaderPreparation
set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotHeaderMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalRectangleDescriptors UniformLocalCacheChronology

/-- Ordinary persistent addresses/context; row geometry and enabled bit are physically read. -/
structure Parameters where
 height : UniformCrossHeightPreparationMachine.Parameters
 falseRows : ℕ
 falseColors : ℕ
 falsePalette : ℕ
 falseDirectory : ℕ
 gates : ℕ
 negative : ℕ
 conjugates : ℕ
 rectangle : ℕ
 slot : ℕ
 borrowed : ℕ
 selected : ℕ
 ordinals : ℕ
 mapped : ℕ
 permutation : ℕ
 widths : ℕ
 markers : ℕ
 axis : ℕ
 translated : ℕ
 pool : ℕ
 ambient : ℕ
 mu : ℕ
 conjugateMu : ℕ
 time : ℕ
 cachePermutation : ℕ
 cacheWidths : ℕ
 cacheMarkers : ℕ
 cacheAxis : ℕ
 cacheDirectory : ℕ
 kind : ℕ

def Parameters.register (c:Parameters):ℕ→ℕ
 | 6100=>c.height.K
 | 6101=>c.height.T
 | 6102=>c.height.Q
 | 6103=>c.height.R
 | 6104=>c.height.C
 | 6105=>c.height.P
 | 6106=>c.gates
 | 6107=>c.height.D
 | 6108=>c.height.F
 | 6109=>c.height.U
 | 6110=>c.height.J
 | 6111=>c.falseRows
 | 6112=>c.falseColors
 | 6113=>c.falsePalette
 | 6114=>c.falseDirectory
 | 6115=>c.negative
 | 6116=>c.conjugates
 | 6117=>c.rectangle
 | 6118=>c.slot
 | 6119=>c.borrowed
 | 6120=>c.selected
 | 6121=>c.ordinals
 | 6122=>c.mapped
 | 6123=>c.permutation
 | 6124=>c.widths
 | 6125=>c.markers
 | 6126=>c.axis
 | 6127=>c.translated
 | 6128=>c.pool
 | 6129=>c.ambient
 | 6130=>c.mu
 | 6131=>c.conjugateMu
 | 6132=>c.time
 | 6133=>c.cachePermutation
 | 6134=>c.cacheWidths
 | 6135=>c.cacheMarkers
 | 6136=>c.cacheAxis
 | 6137=>c.cacheDirectory
 | 6138=>c.kind
 | _=>0

def reads : List Op := [.literal 6190 0,
 .literal 6191 1,
 .literal 6192 2,
 .add 6194 6117 6190,
 .getNat 4410 6194,
 .add 6194 6194 6191,
 .getNat 4423 6194,
 .add 6194 6194 6191,
 .getNat 4441 6194,
 .add 6194 6194 6191,
 .getNat 4442 6194,
 .add 6194 6194 6192,
 .getNat 4412 6194,
 .add 6194 6194 6191,
 .getNat 4411 6194,
 .add 6194 6118 6191,
 .getNat 4451 6194]
def copyOps (ps:List (ℕ×ℕ)):List Op:=ps.map (fun p=>.add p.1 p.2 6190)
def copies : List (ℕ×ℕ) := [(4440,6100),(4443,6101),(4444,6102),(4445,6103),(4450,6104),(4452,6105),(4413,6119),(4414,6120),(4415,6121),(4416,6122),(4417,6123),(4418,6124),(4419,6125),(4420,6126),(4421,6118),(4422,6127),(4424,6128),(4425,6129),(4426,6130),(4427,6131),(4428,6116),(4429,6115),(4237,6117),(4245,6118),(4238,6119),(4239,6122),(4240,6127),(4241,6128),(4242,6130),(4243,6131),(4246,6115),(4247,6116),(4248,6129),(1060,6104),(1062,6105),(1072,6106),(5840,6132),(5841,6129),(5842,6128),(5843,6133),(5844,6134),(5845,6135),(5846,6136),(5847,6127),(5848,6137),(5849,6138)]
def common:List Op:=reads++copyOps copies
def enabled:List Op := [.add 4446 6107 6190,.add 4447 6108 6190,.add 4448 6109 6190,.add 4449 6110 6190]
def disabled:List Op := [.add 4446 6111 6190,.add 4447 6112 6190,.add 4448 6113 6190,.add 4449 6114 6190]
lemma common_length:common.length=63:=rfl
lemma enabled_length:enabled.length=4:=rfl
lemma disabled_length:disabled.length=4:=rfl
/-- One charged branch chooses true/false height addresses, followed by an actual halt. -/
def program:Program:=common.map Op.code++[.branchLT 6190 4451 64 69]++enabled.map Op.code++[.jump 73]++disabled.map Op.code++[.halt]
lemma program_length:program.length=74:=rfl
lemma common_code:BlockAt common program 0:=by
 intro i hi;change i<63 at hi;interval_cases i <;>rfl
lemma enabled_code:BlockAt enabled program 64:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma disabled_code:BlockAt disabled program 69:=by
 intro i hi;change i<4 at hi;interval_cases i <;>rfl
lemma branch_at:program[63]?=some (.branchLT 6190 4451 64 69):=rfl
lemma jump_at:program[68]?=some (.jump 73):=rfl
lemma halt_at:program[73]?=some .halt:=rfl
noncomputable section
def Args (c:Parameters) (s:State):Prop:=∀q,6100≤q→q≤6138→s.natReg q=c.register q
lemma Args.get {c:Parameters}{s:State}(h:Args c s) (q:ℕ) (lo:6100≤q) (hi:q≤6138):s.natReg q=c.register q:=h q lo hi
def selectedHeight (c:Parameters) (q:Row) (slot:Slot):UniformCrossHeightPreparationMachine.Parameters:=
 { c.height with
   a := q.a
   e := q.e
   D := if slot.enabled then c.height.D else c.falseRows
   F := if slot.enabled then c.height.F else c.falseColors
   U := if slot.enabled then c.height.U else c.falsePalette
   J := if slot.enabled then c.height.J else c.falseDirectory
   enabled := slot.enabled }
def forward (c:Parameters) (q:Row) (slot:Slot):UniformForwardMatchingFactorPreparation.Config:=
 ⟨⟨selectedHeight c q slot,q.width,q.j0,q.i0,c.borrowed,c.selected,c.ordinals,c.mapped,
 c.permutation,c.widths,c.markers,c.axis,slot.depth,slot.color⟩,
 c.slot,c.translated,q.offset,c.pool,c.ambient,c.mu,c.conjugateMu,c.negative,c.conjugates⟩
def Prepared (c:Parameters) (q:Row) (slot:Slot) (s:State):Prop:=
 UniformForwardMatchingFactorHeaderPreparation.Args (forward c q slot) s ∧
 UniformLocalBroadcastPoolMachine.Args c.rectangle c.slot c.borrowed c.mapped c.translated c.pool
 c.mu c.conjugateMu c.height.C c.negative c.height.P c.conjugates c.ambient c.gates s ∧
 s.natReg 5840=c.time ∧s.natReg 5841=c.ambient ∧s.natReg 5842=c.pool ∧
 s.natReg 5843=c.cachePermutation ∧s.natReg 5844=c.cacheWidths ∧s.natReg 5845=c.cacheMarkers ∧
 s.natReg 5846=c.cacheAxis ∧s.natReg 5847=c.translated ∧s.natReg 5848=c.cacheDirectory ∧s.natReg 5849=c.kind
lemma op_keeps (o:Op) (s:State) (r:ℕ) (h:UniformNewtonTableMachine.KeepsNat r o.code):
 (o.apply s).natReg r=s.natReg r:=by
 cases o <;>simp_all [Op.code,UniformNewtonTableMachine.KeepsNat,Op.apply,writeNat,writeScalar,next,Function.update_apply] <;>aesop
lemma block_keeps (os:List Op) (s:State) (r:ℕ)
 (h:∀o∈os,UniformNewtonTableMachine.KeepsNat r o.code):
 (applyBlock os s).natReg r=s.natReg r:=by
 induction os generalizing s with
 | nil=>rfl
 | cons o os ih=>
  exact (ih (o.apply s) (fun z hz=>h z (by simp[hz]))).trans (op_keeps o s r (h o (by simp)))

lemma reads_length:reads.length=17:=rfl
lemma copies_length:copies.length=46:=rfl
lemma applyBlock_append (a b:List Op) (s:State):applyBlock (a++b) s=applyBlock b (applyBlock a s):=by
 induction a generalizing s with
 | nil=>rfl
 | cons a as ih=>exact ih (a.apply s)
def CopySafe (ps:List (ℕ×ℕ)):Prop:=∀p∈ps,(p.1<6100∨6138<p.1)∧p.1≠6190∧6100≤p.2∧p.2≤6138
lemma copies_safe:CopySafe copies:=by
 intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp
 rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals refine ⟨Or.inl (by omega),by omega,by omega,by omega⟩
lemma copyOp_args {c:Parameters}{s:State}{d r:ℕ}(args:Args c s)
 (outside:d<6100∨6138<d):Args c ((Op.add d r 6190).apply s):=by
 intro q lo hi
 simpa [Op.apply,writeNat,next,Function.update_apply,show q≠d by omega] using args q lo hi
lemma copyOp_zero {s:State}{d r:ℕ}(zero:s.natReg 6190=0) (different:d≠6190):
 ((Op.add d r 6190).apply s).natReg 6190=0:=by
 simpa [Op.apply,writeNat,next,Function.update_apply,Ne.symm different] using zero
/-- Pure environment update is used only to prove the real block's registers.
It is not a RAM instruction or an uncharged table producer. -/
def copyEnv (ps:List (ℕ×ℕ)) (values:ℕ→ℕ) (env:ℕ→ℕ):ℕ→ℕ:=
 ps.foldl (fun env p=>Function.update env p.1 (values p.2)) env
lemma copy_nat {c:Parameters}(ps:List (ℕ×ℕ)) (s:State) (args:Args c s)
 (zero:s.natReg 6190=0) (safe:CopySafe ps):
 (applyBlock (copyOps ps) s).natReg=copyEnv ps c.register s.natReg:=by
 induction ps generalizing s with
 | nil=>rfl
 | cons p ps ih=>
  have sp:=safe p (by simp)
  have tail:CopySafe ps:=fun q hq=>safe q (by simp[hq])
  have a:=copyOp_args (r:=p.2) args sp.1
  have z:=copyOp_zero (r:=p.2) zero sp.2.1
  have eq:((Op.add p.1 p.2 6190).apply s).natReg=
   Function.update s.natReg p.1 (c.register p.2):=by
   simp only[Op.apply,writeNat,next]
   rw[args.get p.2 sp.2.2.1 sp.2.2.2,zero,Nat.add_zero]
  change (applyBlock (copyOps ps) ((Op.add p.1 p.2 6190).apply s)).natReg=_
  rw[ih _ a z tail,eq];rfl
lemma copy_env_outside (ps:List (ℕ×ℕ)) (values env:ℕ→ℕ) (q:ℕ)
 (outside:∀p∈ps,p.1≠q):copyEnv ps values env q=env q:=by
 induction ps generalizing env with
 | nil=>rfl
 | cons p ps ih=>
  have ne:=outside p (by simp)
  exact (ih _ (fun x hx=>outside x (by simp[hx]))).trans
   (by simp[Ne.symm ne])
lemma copy_env_output (ps:List (ℕ×ℕ)) (values env:ℕ→ℕ)
 (unique:(ps.map Prod.fst).Nodup) (d r:ℕ) (mem:(d,r)∈ps):copyEnv ps values env d=values r:=by
 induction ps generalizing env with
 | nil=>simp at mem
 | cons p ps ih=>
  have nd:=List.nodup_cons.mp unique
  rcases List.mem_cons.mp mem with eq|mem
  · subst p
    exact (copy_env_outside ps values _ d (by
     intro p hp same;apply nd.1;exact List.mem_map.mpr ⟨p,hp,same⟩)).trans
     (by simp)
  · exact ih _ nd.2 mem
lemma copies_nodup:(copies.map Prod.fst).Nodup:=by decide
lemma reads_keeps (s:State) (r:ℕ) (lo:6100≤r) (hi:r≤6138):
 (applyBlock reads s).natReg r=s.natReg r:=by
 apply block_keeps
 intro o ho;simp only[reads,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp only[Op.code,UniformNewtonTableMachine.KeepsNat];omega
lemma reads_args {c:Parameters}{s:State}(args:Args c s):Args c (applyBlock reads s):=by
 intro q lo hi;rw[reads_keeps s q lo hi];exact args q lo hi
lemma reads_flag {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 (applyBlock reads s).natReg 6190=0∧(applyBlock reads s).natReg 4451=UniformLocalReplaySlotMachine.bit slot.enabled:=by
 have addr:s.natReg 6118=c.slot:=by simpa[Parameters.register] using args.get 6118 (by omega) (by omega)
 have flag:s.natHeap (c.slot+1)=some (UniformLocalReplaySlotMachine.bit slot.enabled):=by
  simpa[UniformLocalReplaySlotMachine.Slot.words] using record ⟨1,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,flag]
lemma common_nat {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 (applyBlock common s).natReg=copyEnv copies c.register (applyBlock reads s).natReg:=by
 rw[common,applyBlock_append]
 exact copy_nat copies _ (reads_args args) (reads_flag args record).1 copies_safe
lemma common_output {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s) (d r:ℕ) (mem:(d,r)∈copies):
 (applyBlock common s).natReg d=c.register r:=by
 rw[common_nat args record];exact copy_env_output copies _ _ copies_nodup d r mem
lemma common_unchanged {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s) (q:ℕ) (out:∀p∈copies,p.1≠q):
 (applyBlock common s).natReg q=(applyBlock reads s).natReg q:=by
 rw[common_nat args record];exact copy_env_outside copies _ _ q out
lemma common_args {c:Parameters}{slot:Slot}{s:State}(h:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):Args c (applyBlock common s):=by
 intro q lo hi
 rw[common_unchanged h record q (fun p hp=>by
  have sp:=copies_safe p hp;omega),reads_keeps s q lo hi]
 exact h q lo hi
lemma common_flags {c:Parameters}{slot:Slot}{s:State}(h:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 (applyBlock common s).natReg 6190=0∧(applyBlock common s).natReg 4451=UniformLocalReplaySlotMachine.bit slot.enabled:=by
 rw[common_unchanged h record 6190 (by intro p hp;exact (copies_safe p hp).2.1),
  common_unchanged h record 4451 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 exact reads_flag h record
lemma selector_keeps (b:Bool) (s:State) (r:ℕ) (hr:r<4446∨4450≤r):
 (applyBlock (if b then enabled else disabled) s).natReg r=s.natReg r:=by
 cases b <;>simp (disch:=omega)[enabled,disabled,applyBlock,Op.apply,writeNat,next]
attribute [local irreducible] common
lemma common_geom4410 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4410=q.width := by
 rw[common_unchanged args record 4410 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap c.rectangle=some q.width:=by simpa[Row.words] using source ⟨0,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma common_geom4423 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4423=q.offset := by
 rw[common_unchanged args record 4423 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap (c.rectangle+1)=some q.offset:=by simpa[Row.words] using source ⟨1,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma common_geom4441 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4441=q.a := by
 rw[common_unchanged args record 4441 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap (c.rectangle+2)=some q.a:=by simpa[Row.words] using source ⟨2,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma common_geom4442 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4442=q.e := by
 rw[common_unchanged args record 4442 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap (c.rectangle+3)=some q.e:=by simpa[Row.words] using source ⟨3,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma common_geom4412 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4412=q.i0 := by
 rw[common_unchanged args record 4412 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap (c.rectangle+5)=some q.i0:=by simpa[Row.words] using source ⟨5,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma common_geom4411 {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):(applyBlock common s).natReg 4411=q.j0 := by
 rw[common_unchanged args record 4411 (by intro p hp;simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl;all_goals omega)]
 have addr:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have leaf:s.natHeap (c.rectangle+6)=some q.j0:=by simpa[Row.words] using source ⟨6,by decide⟩
 simp[reads,applyBlock,Op.apply,writeNat,next,addr,leaf,Nat.add_assoc]

lemma selected_output {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s) (d r:ℕ) (mem:(d,r)∈copies)
 (outside:d<4446∨4450≤d):
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg d=c.register r:=by
 rw[selector_keeps slot.enabled _ d outside]
 exact common_output args record d r mem
lemma selected_flags {c:Parameters}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg 4451=
 UniformLocalReplaySlotMachine.bit slot.enabled:=by
 rw[selector_keeps slot.enabled _ 4451 (Or.inr (by omega))]
 exact (common_flags args record).2
lemma selected_banks {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg 4446=(selectedHeight c q slot).D ∧
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg 4447=(selectedHeight c q slot).F ∧
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg 4448=(selectedHeight c q slot).U ∧
 (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)).natReg 4449=(selectedHeight c q slot).J:=by
 have zero:=(common_flags args record).1
 have reg6107:(applyBlock common s).natReg 6107=c.register 6107:=common_args args record 6107 (by omega) (by omega)
 have reg6108:(applyBlock common s).natReg 6108=c.register 6108:=common_args args record 6108 (by omega) (by omega)
 have reg6109:(applyBlock common s).natReg 6109=c.register 6109:=common_args args record 6109 (by omega) (by omega)
 have reg6110:(applyBlock common s).natReg 6110=c.register 6110:=common_args args record 6110 (by omega) (by omega)
 have reg6111:(applyBlock common s).natReg 6111=c.register 6111:=common_args args record 6111 (by omega) (by omega)
 have reg6112:(applyBlock common s).natReg 6112=c.register 6112:=common_args args record 6112 (by omega) (by omega)
 have reg6113:(applyBlock common s).natReg 6113=c.register 6113:=common_args args record 6113 (by omega) (by omega)
 have reg6114:(applyBlock common s).natReg 6114=c.register 6114:=common_args args record 6114 (by omega) (by omega)
 cases flag:slot.enabled <;>
  simp[enabled,disabled,applyBlock,Op.apply,writeNat,next,selectedHeight,Parameters.register,flag,zero,
 reg6107,reg6108,reg6109,reg6110,reg6111,reg6112,reg6113,reg6114]
lemma selected_prepared {c:Parameters}{q:Row}{slot:Slot}{s:State}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s):
 Prepared c q slot (applyBlock (if slot.enabled then enabled else disabled) (applyBlock common s)):=by
 have selected (d r:ℕ) (mem:(d,r)∈copies) (outside:d<4446∨4450≤d):=
  selected_output args record d r mem outside
 have banks:=selected_banks (q:=q) args record
 refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,
   ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4440 6100 (by simp[copies]) (by omega)
 · rw[selector_keeps slot.enabled _ 4441 (by omega)]
   exact common_geom4441 args source record
 · rw[selector_keeps slot.enabled _ 4442 (by omega)]
   exact common_geom4442 args source record
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4443 6101 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4444 6102 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4445 6103 (by simp[copies]) (by omega)
 · exact banks.1
 · exact banks.2.1
 · exact banks.2.2.1
 · exact banks.2.2.2
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4450 6104 (by simp[copies]) (by omega)
 · change _ = if slot.enabled then 1 else 0
   cases h:slot.enabled <;>simpa only[h,UniformLocalReplaySlotMachine.bit] using selected_flags args record
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4452 6105 (by simp[copies]) (by omega)
 · rw[selector_keeps slot.enabled _ 4410 (by omega)]
   exact common_geom4410 args source record
 · rw[selector_keeps slot.enabled _ 4411 (by omega)]
   exact common_geom4411 args source record
 · rw[selector_keeps slot.enabled _ 4412 (by omega)]
   exact common_geom4412 args source record
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4413 6119 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4414 6120 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4415 6121 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4416 6122 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4417 6123 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4418 6124 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4419 6125 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4420 6126 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4421 6118 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4422 6127 (by simp[copies]) (by omega)
 · rw[selector_keeps slot.enabled _ 4423 (by omega)]
   exact common_geom4423 args source record
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4424 6128 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4425 6129 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4426 6130 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4427 6131 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4428 6116 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4429 6115 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4237 6117 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4245 6118 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4238 6119 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4239 6122 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4240 6127 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4241 6128 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4242 6130 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4243 6131 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4246 6115 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4247 6116 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 4248 6129 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 1060 6104 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 1062 6105 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 1072 6106 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5840 6132 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5841 6129 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5842 6128 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5843 6133 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5844 6134 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5845 6135 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5846 6136 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5847 6127 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5848 6137 (by simp[copies]) (by omega)
 · simpa only[forward,selectedHeight,Parameters.register] using selected 5849 6138 (by simp[copies]) (by omega)
/-- Every actual context copy reads a retained integer and writes a different
register; the word/read obligations are derived rather than supplied per copy. -/
lemma copy_peak {c:Parameters} (ps:List (ℕ×ℕ)) (s:State) (B:ℕ)
 (args:Args c s) (zero:s.natReg 6190=0) (safe:CopySafe ps)
 (fit:∀q,6100≤q→q≤6138→c.register q≤B):
 readable (copyOps ps) s ∧peak (copyOps ps) s≤B:=by
 induction ps generalizing s with
 | nil=>exact ⟨trivial,Nat.zero_le B⟩
 | cons p ps ih=>
  have sp:=safe p (by simp)
  have tail:CopySafe ps:=fun q hq=>safe q (by simp[hq])
  have nextArgs:=copyOp_args (r:=p.2) args sp.1
  have nextZero:=copyOp_zero (r:=p.2) zero sp.2.1
  have nextFit:=ih ((Op.add p.1 p.2 6190).apply s) nextArgs nextZero tail
  change (True∧_)∧max (s.natReg p.2+s.natReg 6190) _≤B
  refine ⟨⟨trivial,nextFit.1⟩,max_le ?_ nextFit.2⟩
  rw[args.get p.2 sp.2.2.1 sp.2.2.2,zero,Nat.add_zero]
  exact fit p.2 sp.2.2.1 sp.2.2.2
lemma reads_code:BlockAt reads program 0:=by
 unfold program common
 intro i hi;change i<17 at hi;interval_cases i <;>rfl
lemma copies_code:BlockAt (copyOps copies) program 17:=by
 unfold program common
 intro i hi;change i<46 at hi;interval_cases i <;>rfl
lemma reads_safe {c:Parameters}{q:Row}{slot:Slot}{s:State}{B:ℕ}(args:Args c s)
 (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (wb:WordBound B s) (row:c.rectangle+6≤B) (slotEnd:c.slot+1≤B) (_code:74≤B):
 readable reads s ∧peak reads s≤B:=by
 have da:s.natReg 6117=c.rectangle:=by simpa[Parameters.register] using args.get 6117 (by omega) (by omega)
 have sa:s.natReg 6118=c.slot:=by simpa[Parameters.register] using args.get 6118 (by omega) (by omega)
 have h0:s.natHeap c.rectangle=some q.width:=by simpa[Row.words] using source ⟨0,by decide⟩
 have h1:s.natHeap (c.rectangle+1)=some q.offset:=by simpa[Row.words] using source ⟨1,by decide⟩
 have h2:s.natHeap (c.rectangle+2)=some q.a:=by simpa[Row.words] using source ⟨2,by decide⟩
 have h3:s.natHeap (c.rectangle+3)=some q.e:=by simpa[Row.words] using source ⟨3,by decide⟩
 have h5:s.natHeap (c.rectangle+5)=some q.i0:=by simpa[Row.words] using source ⟨5,by decide⟩
 have h6:s.natHeap (c.rectangle+6)=some q.j0:=by simpa[Row.words] using source ⟨6,by decide⟩
 have en:s.natHeap (c.slot+1)=some (UniformLocalReplaySlotMachine.bit slot.enabled):=by
  simpa[UniformLocalReplaySlotMachine.Slot.words] using record ⟨1,by decide⟩
 have b0:=(wb.2.2.1 _ _ h0).2;have b1:=(wb.2.2.1 _ _ h1).2
 have b2:=(wb.2.2.1 _ _ h2).2;have b3:=(wb.2.2.1 _ _ h3).2
 have b5:=(wb.2.2.1 _ _ h5).2;have b6:=(wb.2.2.1 _ _ h6).2
 have be:=(wb.2.2.1 _ _ en).2
 simp[reads,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,
  da,sa,Nat.add_assoc,h0,h1,h2,h3,h5,h6,en]
 omega
lemma selector_safe (b:Bool) (s:State) (B:ℕ) (wb:WordBound B s) (zero:s.natReg 6190=0):
 readable (if b then enabled else disabled) s ∧peak (if b then enabled else disabled) s≤B:=by
 have a:=wb.2.1 6107;have b' :=wb.2.1 6108;have c:=wb.2.1 6109;have d:=wb.2.1 6110
 have e:=wb.2.1 6111;have f:=wb.2.1 6112;have g:=wb.2.1 6113;have h:=wb.2.1 6114
 cases b <;>simp[enabled,disabled,readable,peak,Op.readable,Op.peak,Op.apply,writeNat,next,zero] <;>omega

def NatOnly:Op→Bool
 | .literal _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .getNat _ _=>true
 | _=>false
lemma nat_only_frame (os:List Op) (s:State) (only:∀o∈os,NatOnly o=true):
 (applyBlock os s).natHeap=s.natHeap ∧(applyBlock os s).scalarHeap=s.scalarHeap ∧
 (applyBlock os s).scalarReg=s.scalarReg ∧(applyBlock os s).outputs=s.outputs ∧
 (applyBlock os s).rootOrders=s.rootOrders:=by
 induction os generalizing s with
 | nil=>exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons o os ih=>
  have head:=only o (by simp)
  have tail:=ih (o.apply s) (fun x hx=>only x (by simp[hx]))
  cases o <;>simp_all[NatOnly,applyBlock,Op.apply,writeNat,next]
lemma copy_only (ps:List (ℕ×ℕ)):∀o∈copyOps ps,NatOnly o=true:=by
 intro o ho;obtain ⟨p,_,rfl⟩:=List.mem_map.mp ho;rfl
lemma reads_only:∀o∈reads,NatOnly o=true:=by
 intro o ho;simp only[reads,List.mem_cons,List.not_mem_nil,or_false] at ho
 rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>rfl
lemma selector_only (b:Bool):∀o∈(if b then enabled else disabled),NatOnly o=true:=by
 cases b <;>intro o ho <;>simp only[enabled,disabled,Bool.false_eq_true,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false] at ho
 all_goals rcases ho with rfl|rfl|rfl|rfl <;>rfl
lemma op_setPC (o:Op) (s:State) (pc:ℕ):o.apply (setPC s pc)=setPC (o.apply s) (pc+1):=by
 cases o <;>rfl
lemma block_setPC (os:List Op) (s:State) (pc:ℕ):
 applyBlock os (setPC s pc)=setPC (applyBlock os s) (pc+os.length):=by
 induction os generalizing s pc with
 | nil=>simp only[applyBlock,List.length_nil,Nat.add_zero]
 | cons o os ih=>
  rw[applyBlock,op_setPC,ih]
  simp only[applyBlock,List.length_cons,Nat.add_assoc,Nat.add_comm 1]
lemma prepared_nat {c:Parameters}{q:Row}{slot:Slot}{s u:State}(h:Prepared c q slot s)
 (eq:u.natReg=s.natReg):Prepared c q slot u:=by
 rcases h with ⟨f,b,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩
 refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,
  ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · rw[eq];exact f.height.exponent
 · rw[eq];exact f.height.targets
 · rw[eq];exact f.height.inputs
 · rw[eq];exact f.height.tape
 · rw[eq];exact f.height.order
 · rw[eq];exact f.height.sourceDirectory
 · rw[eq];exact f.height.rows
 · rw[eq];exact f.height.colors
 · rw[eq];exact f.height.palette
 · rw[eq];exact f.height.directory
 · rw[eq];exact f.height.coefficients
 · rw[eq];exact f.height.enabled
 · rw[eq];exact f.height.constants
 · rw[eq];exact f.radix
 · rw[eq];exact f.source
 · rw[eq];exact f.target
 · rw[eq];exact f.borrowed
 · rw[eq];exact f.selected
 · rw[eq];exact f.ordinals
 · rw[eq];exact f.mapped
 · rw[eq];exact f.permutation
 · rw[eq];exact f.widths
 · rw[eq];exact f.markers
 · rw[eq];exact f.axis
 · rw[eq];exact f.slot
 · rw[eq];exact f.translated
 · rw[eq];exact f.offset
 · rw[eq];exact f.pool
 · rw[eq];exact f.ambient
 · rw[eq];exact f.mu
 · rw[eq];exact f.conjugate
 · rw[eq];exact f.conjugates
 · rw[eq];exact f.negative
 · rw[eq];exact b.rectangle
 · rw[eq];exact b.slot
 · rw[eq];exact b.borrowed
 · rw[eq];exact b.rawRows
 · rw[eq];exact b.translated
 · rw[eq];exact b.pool
 · rw[eq];exact b.mu
 · rw[eq];exact b.conjugateMu
 · rw[eq];exact b.negative
 · rw[eq];exact b.conjugates
 · rw[eq];exact b.radix
 · rw[eq];exact b.positive
 · rw[eq];exact b.constants
 · rw[eq];exact b.gates
 · rw[eq];exact a0
 · rw[eq];exact a1
 · rw[eq];exact a2
 · rw[eq];exact a3
 · rw[eq];exact a4
 · rw[eq];exact a5
 · rw[eq];exact a6
 · rw[eq];exact a7
 · rw[eq];exact a8
 · rw[eq];exact a9

/-- Actual prefix, with physical read safety and a shared word budget. -/
theorem common_execution {c:Parameters}{q:Row}{slot:Slot}{n B:ℕ}(x:Fin n→ℂ) (s:State)
 (args:Args c s) (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (wb:WordBound B s) (row:c.rectangle+6≤B) (slotEnd:c.slot+1≤B) (code:74≤B) (pc:s.pc=0):
 BoundedRuns program n x B s 63 (applyBlock common s):=by
 have safe:=reads_safe args source record wb row slotEnd code
 have first:=block_runs reads program 0 n B x s reads_code pc wb (by rw[reads_length];omega) safe.1 safe.2
 let b:=applyBlock reads s
 have bp:b.pc=17:=by rw[applyBlock_pc,pc,reads_length]
 have ba:Args c b:=reads_args args
 have bz:b.natReg 6190=0:=(reads_flag args record).1
 have fit:∀q,6100≤q→q≤6138→c.register q≤B:=by
  intro q lo hi;rw[←ba q lo hi];exact first.final_bound.2.1 q
 have secondSafe:=copy_peak copies b B ba bz copies_safe fit
 have second:=block_runs (copyOps copies) program 17 n B x b copies_code bp first.final_bound
  (by simp only[copyOps,List.length_map,copies_length];omega) secondSafe.1 secondSafe.2
 convert first.trans second using 1
 · simp only[copyOps,List.length_map,copies_length,reads_length]
 · rw[common];exact applyBlock_append reads (copyOps copies) s
/-- This actual74 program only prepares physical caller headers. Its entry
contains ordinary addresses and actual stored row/slot cells, not factor,
matching, count, or action certificates. Both branch costs include the halt. -/
theorem execution {c:Parameters}{q:Row}{slot:Slot}{n B:ℕ}(x:Fin n→ℂ) (s:State)
 (args:Args c s) (source:UniformLocalRectangleBankMachine.RowSource c.rectangle q s)
 (record:UniformLocalBroadcastPoolMachine.SlotSource c.slot slot s)
 (wb:WordBound B s) (row:c.rectangle+6≤B) (slotEnd:c.slot+1≤B) (code:74≤B) (pc:s.pc=0):∃u,
 BoundedExecution program n x B s (69+UniformLocalReplaySlotMachine.bit slot.enabled) u ∧
 u.pc=73 ∧Prepared c q slot u ∧
 u.natHeap=s.natHeap ∧u.scalarHeap=s.scalarHeap ∧u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧Args c u:=by
 have prefixRun:=common_execution x s args source record wb row slotEnd code pc
 let b:=applyBlock common s
 have bp:b.pc=63:=by rw[applyBlock_pc,pc,common_length]
 have flags:=common_flags args record
 have only:∀o∈common,NatOnly o=true:=by
  intro o ho;rw[common,List.mem_append] at ho
  rcases ho with left|right
  · exact reads_only o left
  · exact copy_only copies o right
 have firstFrame:=nat_only_frame common s only
 have prepared:=selected_prepared args source record
 cases enabledFlag:slot.enabled with
 | false=>
  let start:=setPC b 69
  have startBound:=changePC_bound B b 69 prefixRun.final_bound (by omega)
  have branch:BoundedRuns program n x B b 1 start:=.next prefixRun.final_bound
   (by simp[step,bp,branch_at,start,b,flags.1,flags.2,enabledFlag,UniformLocalReplaySlotMachine.bit,setPC]) (.refl startBound)
  have zero:start.natReg 6190=0:=flags.1
  have safe:=selector_safe false start B startBound zero
  have select:=block_runs disabled program 69 n B x start disabled_code rfl startBound
   (by rw[disabled_length];omega) safe.1 safe.2
  let u:=applyBlock disabled start
  have up:u.pc=73:=by rw[applyBlock_pc,disabled_length];rfl
  have done:BoundedExecution program n x B u 1 u:=.halt select.final_bound (by simp[step,up,halt_at])
  have selectedFrame:=nat_only_frame disabled start (by simpa using selector_only false)
  have selectedArgs:Args c u:=by
   intro r lo hi
   have kept:(applyBlock disabled start).natReg r=start.natReg r:=by
    simpa using selector_keeps false start r (Or.inr (by omega))
   exact kept.trans (common_args args record r lo hi)
  refine ⟨u,?_,up,?_,?_,?_,?_,?_,?_,selectedArgs⟩
  · convert prefixRun.executes (branch.executes (select.executes done)) using 1
    norm_num[disabled_length,UniformLocalReplaySlotMachine.bit]
  · apply prepared_nat prepared
    simp only[enabledFlag,Bool.false_eq_true,ite_false]
    rw[show u=applyBlock disabled (setPC b 69) from rfl,block_setPC];rfl
  · exact selectedFrame.1.trans firstFrame.1
  · exact selectedFrame.2.1.trans firstFrame.2.1
  · exact selectedFrame.2.2.1.trans firstFrame.2.2.1
  · exact selectedFrame.2.2.2.1.trans firstFrame.2.2.2.1
  · exact selectedFrame.2.2.2.2.trans firstFrame.2.2.2.2
 | true=>
  let start:=setPC b 64
  have startBound:=changePC_bound B b 64 prefixRun.final_bound (by omega)
  have branch:BoundedRuns program n x B b 1 start:=.next prefixRun.final_bound
   (by simp[step,bp,branch_at,start,b,flags.1,flags.2,enabledFlag,UniformLocalReplaySlotMachine.bit,setPC]) (.refl startBound)
  have zero:start.natReg 6190=0:=flags.1
  have safe:=selector_safe true start B startBound zero
  have select:=block_runs enabled program 64 n B x start enabled_code rfl startBound
   (by rw[enabled_length];omega) safe.1 safe.2
  let chosen:=applyBlock enabled start
  have cp:chosen.pc=68:=by rw[applyBlock_pc,enabled_length];rfl
  let u:=setPC chosen 73
  have finalBound:=changePC_bound B chosen 73 select.final_bound (by omega)
  have jump:BoundedRuns program n x B chosen 1 u:=.next select.final_bound
   (by simp[step,cp,jump_at,u,setPC]) (.refl finalBound)
  have done:BoundedExecution program n x B u 1 u:=.halt finalBound (by simp[step,u,setPC,halt_at])
  have selectedFrame:=nat_only_frame enabled start (by simpa using selector_only true)
  have selectedArgs:Args c u:=by
   intro r lo hi
   have kept:(applyBlock enabled start).natReg r=start.natReg r:=by
    simpa using selector_keeps true start r (Or.inr (by omega))
   exact kept.trans (common_args args record r lo hi)
  refine ⟨u,?_,rfl,?_,?_,?_,?_,?_,?_,selectedArgs⟩
  · convert prefixRun.executes (branch.executes (select.executes (jump.executes done))) using 1
    norm_num[enabled_length,UniformLocalReplaySlotMachine.bit]
  · apply prepared_nat prepared
    simp only[enabledFlag,ite_true]
    change (applyBlock enabled (setPC b 64)).natReg=(applyBlock enabled (applyBlock common s)).natReg
    rw[block_setPC];rfl
  · exact selectedFrame.1.trans firstFrame.1
  · exact selectedFrame.2.1.trans firstFrame.2.1
  · exact selectedFrame.2.2.1.trans firstFrame.2.2.1
  · exact selectedFrame.2.2.2.1.trans firstFrame.2.2.2.1
  · exact selectedFrame.2.2.2.2.trans firstFrame.2.2.2.2
lemma keeps_driver (r:ℕ) (keep:6100≤r∧r≤6189∨6195≤r):
 ∀i∈program,UniformNewtonTableMachine.KeepsNat r i:=by
 intro i hi
 rw[program] at hi
 simp only[List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with (((((⟨o,ho,rfl⟩|h)|⟨o,ho,rfl⟩)|h)|⟨o,ho,rfl⟩)|h)
 · rw[common,List.mem_append] at ho
   rcases ho with ho|ho
   · simp only[reads,List.mem_cons,List.not_mem_nil,or_false] at ho
     rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
     all_goals simp only[Op.code,UniformNewtonTableMachine.KeepsNat];omega
   · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ho
     have ps:=copies_safe p hp
     simp only[Op.code,UniformNewtonTableMachine.KeepsNat]
     have pl:p.1<6100:=by
      simp only[copies,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>omega
     omega
 · rcases h with rfl;simp[UniformNewtonTableMachine.KeepsNat]
 · simp only[enabled,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl <;>simp only[Op.code,UniformNewtonTableMachine.KeepsNat] <;>omega
 · rcases h with rfl;simp[UniformNewtonTableMachine.KeepsNat]
 · simp only[disabled,List.mem_cons,List.not_mem_nil,or_false] at ho
   rcases ho with rfl|rfl|rfl|rfl <;>simp only[Op.code,UniformNewtonTableMachine.KeepsNat] <;>omega
 · rcases h with rfl;simp[UniformNewtonTableMachine.KeepsNat]
lemma driver_frame {n B t:ℕ}{x:Fin n→ℂ}{s u:State}
 (run:BoundedExecution program n x B s t u) (r:ℕ) (keep:6100≤r∧r≤6189∨6195≤r):
 u.natReg r=s.natReg r:=UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_driver r keep)

end
end ExactFourierCircuits.UniformLocalCacheSlotHeaderMachine
