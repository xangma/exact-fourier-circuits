import UniformLocalCacheSlotHeaderMachine
import UniformLocalReplayStoredSlots

set_option autoImplicit false
namespace ExactFourierCircuits.UniformLocalCacheSlotCursorMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformLocalCacheSlotHeaderMachine

/-- The cursor advances real control, factor, partition and ABI addresses. -/
def cursorParameters (c:Parameters) (j:ℕ):Parameters :=
 { c with
   slot := c.slot + 5*j
   pool := c.pool + 9*c.ambient*j
   time := c.time + 28*j
   cachePermutation := c.cachePermutation+(3*c.ambient+11)*j
   cacheWidths := c.cacheWidths+(3*c.ambient+11)*j
   cacheMarkers := c.cacheMarkers+(3*c.ambient+11)*j
   cacheAxis := c.cacheAxis+(3*c.ambient+11)*j
   cacheDirectory := c.cacheDirectory+(3*c.ambient+11)*j }

/-- All sizing arithmetic is literal RAM work, including the actual slot count. -/
def boot:List Op := [.literal 6180 5,.literal 6181 9,.literal 6182 3,.literal 6183 11,
 .literal 6184 28,.literal 6185 1,.literal 6186 352,.literal 6187 330,
 .mul 6141 6100 6186,.add 6141 6141 6187,.literal 6140 0,
 .mul 6142 6129 6181,.mul 6143 6129 6182,.add 6143 6143 6183]
def advance:List Op := [.add 6118 6118 6180,.add 6128 6128 6142,.add 6132 6132 6184,
 .add 6133 6133 6143,.add 6134 6134 6143,.add 6135 6135 6143,
 .add 6136 6136 6143,.add 6137 6137 6143,.add 6140 6140 6185]
lemma boot_length:boot.length=14:=rfl
lemma advance_length:advance.length=9:=rfl

structure Control (c:Parameters) (j:ℕ) (s:State):Prop where
 args:Args (cursorParameters c j) s
 index:s.natReg 6140=j
 total:s.natReg 6141=352*c.height.K+330
 scalarStride:s.natReg 6142=9*c.ambient
 natStride:s.natReg 6143=3*c.ambient+11
 five:s.natReg 6180=5
 nine:s.natReg 6181=9
 three:s.natReg 6182=3
 eleven:s.natReg 6183=11
 duration:s.natReg 6184=28
 one:s.natReg 6185=1
 slope:s.natReg 6186=352
 intercept:s.natReg 6187=330

lemma at_zero(c:Parameters):cursorParameters c 0=c:=by cases c;rfl
lemma at_slot(c:Parameters)(j:ℕ):(cursorParameters c j).slot=c.slot+5*j:=rfl
lemma at_pool(c:Parameters)(j:ℕ):(cursorParameters c j).pool=c.pool+9*c.ambient*j:=rfl
lemma at_time(c:Parameters)(j:ℕ):(cursorParameters c j).time=c.time+28*j:=rfl
lemma at_ambient(c:Parameters)(j:ℕ):(cursorParameters c j).ambient=c.ambient:=rfl
lemma at_height(c:Parameters)(j:ℕ):(cursorParameters c j).height=c.height:=rfl

lemma Control.withPC {c:Parameters}{j:ℕ}{s:State}(h:Control c j s)(pc:ℕ):
 Control c j (setPC s pc):=
 ⟨h.args,h.index,h.total,h.scalarStride,h.natStride,h.five,h.nine,h.three,h.eleven,
  h.duration,h.one,h.slope,h.intercept⟩

lemma boot_args {c:Parameters}{s:State}(args:Args c s):Args c (applyBlock boot s):=by
 intro q lo hi
 have keep:=block_keeps boot s q (by
  intro o member
  simp only [boot,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Op.code,UniformNewtonTableMachine.KeepsNat];omega)
 exact keep.trans (args q lo hi)

lemma boot_control {c:Parameters}{s:State}(args:Args c s):Control c 0 (applyBlock boot s):=by
 have exponent:=args 6100 (by omega) (by omega)
 have ambient:=args 6129 (by omega) (by omega)
 change s.natReg 6100=c.height.K at exponent
 change s.natReg 6129=c.ambient at ambient
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · simpa only [at_zero] using boot_args args
 all_goals simp [boot,applyBlock,Op.apply,writeNat,next,exponent,ambient,Nat.mul_comm]

lemma boot_heaps(s:State):(applyBlock boot s).natHeap=s.natHeap ∧
 (applyBlock boot s).scalarHeap=s.scalarHeap ∧(applyBlock boot s).scalarReg=s.scalarReg ∧
 (applyBlock boot s).outputs=s.outputs ∧(applyBlock boot s).rootOrders=s.rootOrders:=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma advance_args {c:Parameters}{j:ℕ}{s:State}(h:Control c j s):
 Args (cursorParameters c (j+1)) (applyBlock advance s):=by
 intro q lo hi
 have old:=h.args q lo hi
 interval_cases q
 all_goals simp only [Parameters.register,cursorParameters] at old ⊢
 all_goals simp [advance,applyBlock,Op.apply,writeNat,next,h.scalarStride,h.natStride,h.five,h.duration,old]
 all_goals ring

lemma advance_control {c:Parameters}{j:ℕ}{s:State}(h:Control c j s):
 Control c (j+1) (applyBlock advance s):=by
 refine ⟨advance_args h,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals simp [advance,applyBlock,Op.apply,writeNat,next,h.index,h.total,h.scalarStride,
  h.natStride,h.five,h.nine,h.three,h.eleven,h.duration,h.one,h.slope,h.intercept]

lemma advance_heaps(s:State):(applyBlock advance s).natHeap=s.natHeap ∧
 (applyBlock advance s).scalarHeap=s.scalarHeap ∧(applyBlock advance s).scalarReg=s.scalarReg ∧
 (applyBlock advance s).outputs=s.outputs ∧(applyBlock advance s).rootOrders=s.rootOrders:=
 ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The live integer count is exactly the six-phase producer's slot count. -/
lemma control_count {c:Parameters}{j:ℕ}{s:State}(h:Control c j s):
 s.natReg 6141=11*UniformLocalReplayAssembly.phasePrefix (8*c.height.K+6) 6:=by
 rw [h.total,UniformLocalReplayStoredSlots.slot_count]

/-- Only actual preserved integer registers are needed to carry the cursor
through a concrete component execution. -/
lemma Control.transport {c:Parameters}{j:ℕ}{s u:State}(h:Control c j s)
 (keep:∀q,6100≤q→q≤6187→u.natReg q=s.natReg q):Control c j u:=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · intro q lo hi
   exact (keep q lo (by omega)).trans (h.args q lo hi)
 all_goals first
  | exact (keep _ (by omega) (by omega)).trans h.index
  | exact (keep _ (by omega) (by omega)).trans h.total
  | exact (keep _ (by omega) (by omega)).trans h.scalarStride
  | exact (keep _ (by omega) (by omega)).trans h.natStride
  | exact (keep _ (by omega) (by omega)).trans h.five
  | exact (keep _ (by omega) (by omega)).trans h.nine
  | exact (keep _ (by omega) (by omega)).trans h.three
  | exact (keep _ (by omega) (by omega)).trans h.eleven
  | exact (keep _ (by omega) (by omega)).trans h.duration
  | exact (keep _ (by omega) (by omega)).trans h.one
  | exact (keep _ (by omega) (by omega)).trans h.slope
  | exact (keep _ (by omega) (by omega)).trans h.intercept

lemma boot_safe {c:Parameters}{s:State}{B:ℕ}(args:Args c s)
 (code:352≤B)(total:352*c.height.K+330≤B)(scalar:9*c.ambient≤B)
 (natural:3*c.ambient+11≤B):readable boot s∧peak boot s≤B:=by
 have exponent:=args 6100 (by omega) (by omega)
 have ambient:=args 6129 (by omega) (by omega)
 change s.natReg 6100=c.height.K at exponent
 change s.natReg 6129=c.ambient at ambient
 constructor
 · simp [boot,readable,Op.readable]
 · simp [boot,peak,Op.peak,Op.apply,writeNat,next,exponent,ambient]
   omega

lemma advance_safe {c:Parameters}{j:ℕ}{s:State}{B:ℕ}(h:Control c j s)
 (slot:(cursorParameters c (j+1)).slot≤B)
 (pool:(cursorParameters c (j+1)).pool≤B)
 (time:(cursorParameters c (j+1)).time≤B)
 (permutation:(cursorParameters c (j+1)).cachePermutation≤B)
 (widths:(cursorParameters c (j+1)).cacheWidths≤B)
 (markers:(cursorParameters c (j+1)).cacheMarkers≤B)
 (axis:(cursorParameters c (j+1)).cacheAxis≤B)
 (directory:(cursorParameters c (j+1)).cacheDirectory≤B)
 (index:j+1≤B):readable advance s∧peak advance s≤B:=by
 have a:=h.args 6118 (by omega) (by omega)
 have b:=h.args 6128 (by omega) (by omega)
 have ctime:=h.args 6132 (by omega) (by omega)
 have d:=h.args 6133 (by omega) (by omega)
 have e:=h.args 6134 (by omega) (by omega)
 have f:=h.args 6135 (by omega) (by omega)
 have g:=h.args 6136 (by omega) (by omega)
 have i:=h.args 6137 (by omega) (by omega)
 simp only [Parameters.register,cursorParameters,Nat.mul_add,Nat.mul_one] at a b ctime d e f g i slot pool time permutation widths markers axis directory
 constructor
 · simp [advance,readable,Op.readable]
 · simp [advance,peak,Op.peak,Op.apply,writeNat,next,a,b,ctime,d,e,f,g,i,
    h.scalarStride,h.natStride,h.five,h.duration,h.index,h.one]
   constructor <;>omega

end ExactFourierCircuits.UniformLocalCacheSlotCursorMachine
