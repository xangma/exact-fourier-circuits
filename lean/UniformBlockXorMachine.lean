import UniformXorCallerInterface
import UniformBoundedAssembly
set_option autoImplicit false
namespace ExactFourierCircuits.UniformBlockXorMachine
open UniformMachine UniformAssembly
open UniformNatBlockMachine (Op applyBlock readable peak BlockAt block_runs)
noncomputable section
def setPC (s : State) (p : ℕ) : State := {s with pc := p}
open UniformXorTableMachine (Entries lookupProgram lookupLoaded lookupAddressed lookupOffset lookupMultiplied)

/-- One fixed block-address routine: width table lookups, independent of the
number q of bits per block. The actual table is produced once by fixed38. -/
def boot : List Op := [.literal 3359 1,.literal 3355 0,.literal 3356 1,.literal 3357 0]
def setup : List Op := [.binary .mod 3442 3350 3353,.binary .mod 3443 3351 3353,
 .binary .mul 3440 3354 3359,.binary .mul 3441 3353 3359]
def tail : List Op := [.binary .mul 3358 3446 3356,.binary .add 3357 3357 3358,
 .binary .div 3350 3350 3353,.binary .div 3351 3351 3353,
 .binary .mul 3356 3356 3353,.binary .add 3355 3355 3359]
def program : Program := boot.map Op.code++[.branchLT 3355 3352 5 21]++setup.map Op.code++
 lookupProgram.map (relocate 9 14)++tail.map Op.code++[.jump 4,.halt]
lemma program_length : program.length=22 := rfl
lemma boot_code : BlockAt boot program 0 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma setup_code : BlockAt setup program 5 := by intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma lookup_code : CodeAt lookupProgram program 9 14 := by intro i hi;change i<5 at hi;interval_cases i <;> rfl
lemma tail_code : BlockAt tail program 14 := by intro i hi;change i<6 at hi;interval_cases i <;> rfl
lemma branch_at : program[4]?=some (.branchLT 3355 3352 5 21) := rfl
lemma jump_at : program[20]?=some (.jump 4) := rfl
lemma halt_at : program[21]?=some .halt := rfl
lemma xor_split (q a b:ℕ) : a^^^b=(a%2^q^^^b%2^q)+2^q*(a/2^q^^^b/2^q) := by
 have h:=Nat.mod_add_div (a^^^b) (2^q)
 simpa only [Nat.xor_mod_two_pow,Nat.xor_div_two_pow] using h.symm
lemma divided_bound (q count a:ℕ) (ha:a<2^(q*(count+1))) : a/2^q<2^(q*count) := by
 apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).2
 simpa [Nat.mul_add,Nat.pow_add,Nat.mul_one] using ha

structure Control (q w base i remaining total:ℕ) (s:State) : Prop where
 pc:s.pc=4
 width:s.natReg 3352=w
 size:s.natReg 3353=2^q
 base:s.natReg 3354=base
 index:s.natReg 3355=i
 place:s.natReg 3356=2^(q*i)
 one:s.natReg 3359=1
 total:s.natReg 3357+2^(q*i)*(s.natReg 3350^^^s.natReg 3351)=total
 left:s.natReg 3350<2^(q*remaining)
 right:s.natReg 3351<2^(q*remaining)
def Changed (r:ℕ) : Prop := (3350≤r∧r<3352)∨(3355≤r∧r<3360)∨(3440≤r∧r<3447)
structure Frame (s u:State) : Prop where
 natHeap:u.natHeap=s.natHeap
 scalarHeap:u.scalarHeap=s.scalarHeap
 scalarReg:u.scalarReg=s.scalarReg
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 natReg:∀r,¬Changed r→u.natReg r=s.natReg r
lemma Frame.refl (s:State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _=>rfl⟩
lemma Frame.pc {s u:State} (f:Frame s u) (p:ℕ) : Frame s (setPC u p) :=
 ⟨f.natHeap,f.scalarHeap,f.scalarReg,f.outputs,f.roots,f.natReg⟩
lemma Frame.trans {s u t:State} (f:Frame s u) (g:Frame u t) : Frame s t :=
 ⟨g.natHeap.trans f.natHeap,g.scalarHeap.trans f.scalarHeap,g.scalarReg.trans f.scalarReg,
 g.outputs.trans f.outputs,g.roots.trans f.roots,fun r h=>(g.natReg r h).trans (f.natReg r h)⟩
lemma frame_boot (s:State) : Frame s (applyBlock boot s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [boot,applyBlock,Op.apply,writeNat,next]
lemma frame_setup (s:State) : Frame s (applyBlock setup s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [setup,applyBlock,Op.apply,evalNat,writeNat,next]
lemma frame_lookup (s:State) (value:ℕ) : Frame s (lookupLoaded s value) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [lookupLoaded,lookupAddressed,lookupOffset,lookupMultiplied,writeNat,next]
lemma frame_tail (s:State) : Frame s (applyBlock tail s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r h;unfold Changed at h;simp (disch:=omega) [tail,applyBlock,Op.apply,evalNat,writeNat,next]

/-- Each digit pair is read from the real produced table, not calculated by a
bitwise instruction or oracle. The interpreter only uses add/mul/div/mod. -/
lemma round_execution (q w base i remaining total B n:ℕ) (x:Fin n→ℂ) (s:State)
 (h:Control q w base i (remaining+1) total s) (eq:i+(remaining+1)=w)
 (entries:Entries q base (2^q*2^q) s) (hs:WordBound B s) (code:22≤B)
 (capacity:base+2^q*2^q≤B) (volume:2^(q*w)≤B) (resultBound:total<2^(q*w)) : ∃u,
 BoundedRuns program n x B s 17 u ∧ Control q w base (i+1) remaining total u ∧ Frame s u := by
 let a:=s.natReg 3350
 let b:=s.natReg 3351
 let digit:=a%2^q^^^b%2^q
 let entry:=setPC s 5
 have eb:=changePC_bound B s 5 hs (by omega)
 have enter:BoundedRuns program n x B s 1 entry:=.next hs
   (by simp [step,h.pc,branch_at,h.index,h.width,show i<w by omega,entry,setPC]) (.refl eb)
 have np:0<2^q:=Nat.two_pow_pos q
 have nb:2^q≤B:=by
   have pn:=Nat.two_pow_pos q
   have ll:2^q≤2^q*2^q:=Nat.le_mul_of_pos_right _ pn
   omega
 have safe:readable setup entry∧peak setup entry≤B:=by
   have ab:=Nat.mod_lt a np
   have bb:=Nat.mod_lt b np
   simp [setup,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,entry,setPC,h.size,h.base,h.one]
   omega
 have caller:=block_runs setup program 5 n B x entry setup_code rfl eb (by change 9≤B;omega) safe.1 safe.2
 let ready:=applyBlock setup entry
 let ce:=setPC ready 0
 have cb:=changePC_bound B ready 0 caller.final_bound (by omega)
 have c0:ce.natReg 3440=base:=by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next,h.base,h.one]
 have c1:ce.natReg 3441=2^q:=by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next,h.size,h.one]
 have c2:ce.natReg 3442=a%2^q:=by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next,h.size,a]
 have c3:ce.natReg 3443=b%2^q:=by simp [ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next,h.size,b]
 have table:Entries q base (2^q*2^q) ce:=entries
 have lookup:=UniformXorWordBounds.lookup_execution_bounded n q base (a%2^q) (b%2^q) B x ce rfl c0 c1 c2 c3 table
   (Nat.mod_lt a np) (Nat.mod_lt b np) cb (by omega) capacity
 have placed:=UniformBoundedAssembly.boundedExecution_placed lookup_code (by change 14≤B;omega) (by omega) lookup
 have same:UniformAssembly.placed 9 ce=ready:=by simp [UniformAssembly.placed,ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next]
 rw [same] at placed
 let ret:=setPC (lookupLoaded ce digit) 14
 have keep (r:ℕ) (hr:r<3440∨3447≤r) : ret.natReg r=s.natReg r := by
   simp (disch:=omega) [ret,lookupLoaded,lookupAddressed,lookupOffset,lookupMultiplied,ce,ready,entry,setPC,setup,applyBlock,Op.apply,evalNat,writeNat,next]
 have ld:ret.natReg 3446=digit:=by simp [ret,setPC,lookupLoaded,writeNat,next]
 have l:ret.natReg 3350=a:=(keep 3350 (by decide))
 have r:ret.natReg 3351=b:=(keep 3351 (by decide))
 have sz:ret.natReg 3353=2^q:=(keep 3353 (by decide)).trans h.size
 have pl:ret.natReg 3356=2^(q*i):=(keep 3356 (by decide)).trans h.place
 have acc:ret.natReg 3357=s.natReg 3357:=keep 3357 (by decide)
 have idx:ret.natReg 3355=i:=(keep 3355 (by decide)).trans h.index
 have one:ret.natReg 3359=1:=(keep 3359 (by decide)).trans h.one
 have low:digit≤a^^^b:=by simpa [digit,Nat.xor_mod_two_pow] using Nat.mod_le (a^^^b) (2^q)
 have oldTotal:s.natReg 3357+2^(q*i)*(a^^^b)=total:=h.total
 have prod:2^(q*i)*digit≤total:=by
   have le:=Nat.mul_le_mul_left (2^(q*i)) low
   omega
 have newAcc:s.natReg 3357+digit*2^(q*i)≤total:=by
   have le:=Nat.mul_le_mul_left (2^(q*i)) low
   rw [Nat.mul_comm digit] ; omega
 have newPlace:2^(q*i)*2^q≤2^(q*w):=by
   rw [←Nat.pow_add]
   apply Nat.pow_le_pow_right (by decide)
   have ij:i+1≤w:=by omega
   have mm:=Nat.mul_le_mul_left q ij
   simpa only [Nat.mul_add,Nat.mul_one] using mm
 have wb:w≤B:=by have le:=hs.2.1 3352;rw [h.width] at le;exact le
 have safeTail:readable tail ret∧peak tail ret≤B:=by
   have left:=Nat.div_le_self a (2^q)
   have right:=Nat.div_le_self b (2^q)
   change s.natReg 3350/2^q≤ s.natReg 3350 at left
   change s.natReg 3351/2^q≤ s.natReg 3351 at right
   have ab:=hs.2.1 3350
   have bb:=hs.2.1 3351
   simp [tail,readable,peak,Op.readable,Op.peak,Op.apply,evalNat,writeNat,next,ld,l,r,sz,pl,acc,idx,one,a,b]
   rw [Nat.mul_comm (2^(q*i))] at prod
   omega
 have tr:=block_runs tail program 14 n B x ret tail_code rfl placed.final_bound (by change 20≤B;omega) safeTail.1 safeTail.2
 let advanced:=applyBlock tail ret
 let u:=setPC advanced 4
 have ub:=changePC_bound B advanced 4 tr.final_bound (by omega)
 have jump:BoundedRuns program n x B advanced 1 u:=.next tr.final_bound
   (by simp [step,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next,ret,setPC,jump_at,u]) (.refl ub)
 have control:Control q w base (i+1) remaining total u:=by
   constructor
   · rfl
   · change ret.natReg 3352=w
     rw [keep 3352 (by decide)];exact h.width
   · exact sz
   · change ret.natReg 3354=base
     rw [keep 3354 (by decide)];exact h.base
   · simp [u,setPC,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next,idx,one]
   · simp [u,setPC,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next,pl,sz,Nat.mul_add,Nat.pow_add]
   · exact one
   · simp only [u,setPC,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next]
     simp only [Function.update_of_ne (by decide:3357≠3355),Function.update_of_ne (by decide:3357≠3356),Function.update_of_ne (by decide:3350≠3355),Function.update_of_ne (by decide:3350≠3356),Function.update_of_ne (by decide:3350≠3351),Function.update_of_ne (by decide:3351≠3355),Function.update_of_ne (by decide:3351≠3356)]
     simp [ld,l,r,sz,pl,acc,Nat.mul_add,Nat.pow_add]
     rw [←oldTotal,xor_split q a b]
     ring
   · simpa [u,setPC,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next,l,sz] using divided_bound q remaining a h.left
   · simpa [u,setPC,advanced,tail,applyBlock,Op.apply,evalNat,writeNat,next,r,sz] using divided_bound q remaining b h.right
 have frame:Frame s u:=((Frame.refl s).pc 5 |>.trans (frame_setup entry) |>.pc 0)
   |>.trans (frame_lookup ce digit) |>.pc 14 |>.trans (frame_tail ret) |>.pc 4
 refine ⟨u,?_,control,frame⟩
 convert enter.trans (caller.trans (placed.trans (tr.trans jump))) using 1
 simp only [setup,tail,List.length_cons,List.length_nil]
/-- Width-many physical table calls form one complete address XOR. -/
theorem loop_execution (q w base i remaining total B n : ℕ) (x : Fin n→ℂ) (s : State)
 (h : Control q w base i remaining total s) (eq : i+remaining=w)
 (entries : Entries q base (2^q*2^q) s) (hs : WordBound B s) (code : 22≤B)
 (capacity : base+2^q*2^q≤B) (volume : 2^(q*w)≤B) (resultBound : total<2^(q*w)) :
 ∃u,BoundedExecution program n x B s (17*remaining+2) u ∧
 u.pc=21 ∧ u.natReg 3357=total ∧ Frame s u := by
 induction remaining generalizing i s with
 | zero =>
   have hi : i=w := by omega
   have la : s.natReg 3350=0 := by simpa using h.left
   have lb : s.natReg 3351=0 := by simpa using h.right
   have value : s.natReg 3357=total := by simpa [la,lb] using h.total
   let u := setPC s 21
   have ub:=changePC_bound B s 21 hs (by omega)
   have run : BoundedExecution program n x B s 2 u := .next hs
    (by simp [step,h.pc,branch_at,h.index,h.width,hi,u,setPC])
    (.halt ub (by simp [step,u,setPC,halt_at]))
   exact ⟨u,run,rfl,value,(Frame.refl s).pc 21⟩
 | succ remaining ih =>
   obtain ⟨v,rv,cv,fv⟩:=round_execution q w base i remaining total B n x s h eq entries hs code capacity volume resultBound
   have ev : Entries q base (2^q*2^q) v := by
    simpa only [Entries,fv.natHeap] using entries
   obtain ⟨u,ru,pc,value,fu⟩:=ih (i+1) v cv (by omega) ev rv.final_bound
   refine ⟨u,?_,pc,value,fv.trans fu⟩
   convert rv.executes ru using 1
   ring

/-- Actual fixed22 entry: inputs are natural addresses and the physical table.
The next join produces that table from scratch before calling this routine. -/
theorem execution (q w base a b B n : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (left : s.natReg 3350=a) (right : s.natReg 3351=b)
 (width : s.natReg 3352=w) (size : s.natReg 3353=2^q) (address : s.natReg 3354=base)
 (ha : a<2^(q*w)) (hb : b<2^(q*w))
 (entries : Entries q base (2^q*2^q) s) (hs : WordBound B s) (code : 22≤B)
 (capacity : base+2^q*2^q≤B) (volume : 2^(q*w)≤B) :
 ∃u,BoundedExecution program n x B s (17*w+6) u ∧
 u.pc=21 ∧ u.natReg 3357=a^^^b ∧ Frame s u := by
 have bootRun:=block_runs boot program 0 n B x s boot_code pc hs (by change 4≤B;omega)
  (by simp [boot,readable,Op.readable]) (by simp [boot,peak,Op.peak];omega)
 let v := applyBlock boot s
 have c : Control q w base 0 w (a^^^b) v := by
  constructor <;> simp [v,boot,applyBlock,Op.apply,writeNat,next,pc,width,size,address,left,right,ha,hb]
 have ev : Entries q base (2^q*2^q) v := entries
 obtain ⟨u,ru,pu,value,frame⟩:=loop_execution q w base 0 w (a^^^b) B n x v c (by omega) ev
  bootRun.final_bound code capacity volume (Nat.xor_lt_two_pow ha hb)
 refine ⟨u,?_,pu,value,(frame_boot s).trans frame⟩
 convert bootRun.executes ru using 1
 simp only [boot,List.length_cons,List.length_nil]
 omega

end
end ExactFourierCircuits.UniformBlockXorMachine
