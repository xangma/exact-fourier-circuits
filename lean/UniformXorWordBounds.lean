import UniformXorTableMachine
import UniformNatBlockMachine

set_option autoImplicit false
namespace ExactFourierCircuits.UniformXorWordBounds
open UniformMachine UniformNatBlockMachine UniformXorTableMachine
noncomputable section

def bitBoot : List Op := [
 .literal 3403 0,.literal 3404 1,.literal 3405 0,.literal 3406 1,.literal 3407 2]
def bitBody : List Op := [
 .binary .mod 3409 3401 3407,.binary .mod 3410 3402 3407,
 .binary .add 3411 3409 3410,.binary .mod 3411 3411 3407,
 .binary .mul 3411 3411 3404,.binary .add 3403 3403 3411,
 .binary .div 3401 3401 3407,.binary .div 3402 3402 3407,
 .binary .mul 3404 3404 3407,.binary .add 3405 3405 3406]

theorem boot_code : BlockAt bitBoot bitProgram 0 := by
 intro i hi
 change i<5 at hi
 interval_cases i <;> rfl

theorem body_code : BlockAt bitBody bitProgram 6 := by
 intro i hi
 change i<10 at hi
 interval_cases i <;> rfl

theorem boot_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (bound : WordBound B s) (extent : 18≤B) :
 BoundedRuns bitProgram n x B s 5 (initialized s) := by
 exact block_runs bitBoot bitProgram 0 n B x s boot_code pc bound (by change 0+5≤B;omega)
  (by simp [bitBoot,readable,Op.readable]) (by simp [bitBoot,peak,Op.peak];omega)

theorem body_post (q j : ℕ) (s : State) (c : Control q j s) :
 applyBlock bitBody (entered s)=advanced s := by
 simp [applyBlock,bitBody,Op.apply,evalNat,advanced,doubled,secondHalf,firstHalf,accumulated,
  term,reduced,summed,secondBit,firstBit,entered,writeNat,next,parity,c.two,c.one]

theorem body_readable (q j : ℕ) (s : State) (c : Control q j s) :
 readable bitBody (entered s) := by
 simp [readable,bitBody,Op.readable,Op.apply,evalNat,entered,writeNat,next,c.two]

theorem body_peak (q j B : ℕ) (s : State) (c : Control q j s)
 (bound : WordBound B s) (extent : 18≤B) (small : j<q)
 (acc : s.natReg 3403+parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404≤B)
 (weight : s.natReg 3404*2≤B) : peak bitBody (entered s)≤B := by
 have pa := Nat.mod_lt (s.natReg 3401) (by decide : 0<2)
 have pb := Nat.mod_lt (s.natReg 3402) (by decide : 0<2)
 have pp := Nat.mod_lt (s.natReg 3401%2+s.natReg 3402%2) (by decide : 0<2)
 have ah := (Nat.div_le_self (s.natReg 3401) 2).trans (bound.2.1 3401)
 have bh := (Nat.div_le_self (s.natReg 3402) 2).trans (bound.2.1 3402)
 have qbound : q≤B := by simpa only [c.length] using bound.2.1 3400
 have termBound : parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404≤B := by omega
 unfold parity at acc termBound
 rw [←Nat.add_mod] at acc termBound
 simp [peak,bitBody,Op.peak,Op.apply,evalNat,entered,writeNat,next,c.two,c.one,c.index]
 omega

theorem round_bounded (n q j B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : Control q j s) (small : j<q) (bound : WordBound B s) (extent : 18≤B)
 (acc : s.natReg 3403+parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404≤B)
 (weight : s.natReg 3404*2≤B) : BoundedRuns bitProgram n x B s 12 (UniformXorTableMachine.round s) := by
 have enteredBound : WordBound B (entered s) := changePC_bound B s 6 bound (by omega)
 have body:=block_runs bitBody bitProgram 6 n B x (entered s) body_code rfl enteredBound
  (by change 6+10≤B;omega) (body_readable q j s c) (body_peak q j B s c bound extent small acc weight)
 rw [body_post q j s c] at body
 have finish : BoundedRuns bitProgram n x B (advanced s) 1 (UniformXorTableMachine.round s) := by
  refine .next body.final_bound ?_ (.refl (changePC_bound B (advanced s) 5 body.final_bound (by omega)))
  simp [step,bitProgram,advanced,doubled,secondHalf,firstHalf,accumulated,term,reduced,summed,
   secondBit,firstBit,entered,writeNat,next,UniformXorTableMachine.round]
 have first : BoundedRuns bitProgram n x B s 1 (entered s) := by
  refine .next bound ?_ (.refl enteredBound)
  simp [step,bitProgram,entered,c.pc,c.index,c.length,small]
 convert (first.trans body).trans finish using 1; rfl

theorem round_weight (s : State) : (UniformXorTableMachine.round s).natReg 3404=s.natReg 3404*2 := by
 simp [UniformXorTableMachine.round,advanced,doubled,writeNat,next]

theorem weighted_parity (s : State) :
 s.natReg 3403+parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404≤
 s.natReg 3403+s.natReg 3404*(s.natReg 3401^^^s.natReg 3402) := by
 conv_rhs => rw [xor_decompose]
 nlinarith

theorem bit_loop_bounded (n q j fuel B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : Control q j s) (total : j+fuel=q)
 (a : s.natReg 3401<2^fuel) (b : s.natReg 3402<2^fuel)
 (bound : WordBound B s) (extent : 18≤B)
 (metric : s.natReg 3403+s.natReg 3404*(s.natReg 3401^^^s.natReg 3402)≤B)
 (weight : s.natReg 3404*2^fuel≤B) :
 ∃u,BoundedExecution bitProgram n x B s (12*fuel+2) u := by
 induction fuel generalizing j s with
 | zero =>
   have same : j=q := by omega
   let u : State := {s with pc:=17}
   refine ⟨u,.next bound ?_ (.halt (changePC_bound B s 17 bound (by omega)) ?_)⟩
   · simp [step,bitProgram,c.pc,c.index,c.length,same,u]
   · rfl
 | succ fuel ih =>
   have small : j<q := by omega
   have weight2 : s.natReg 3404*2≤B := by
    have positive := Nat.two_pow_pos fuel
    rw [pow_succ] at weight
    nlinarith
   have first:=round_bounded n q j B x s c small bound extent
     ((weighted_parity s).trans metric) weight2
   obtain ⟨u,last⟩:=ih (j+1) (UniformXorTableMachine.round s) (round_control q j s c) (by omega)
    (by rw [(round_halves s).1];exact half_bound _ _ a)
    (by rw [(round_halves s).2];exact half_bound _ _ b) first.final_bound
    (by rw [round_numeric];exact metric)
    (by rw [round_weight];simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using weight)
   refine ⟨u,?_⟩
   convert first.executes last using 1; omega

theorem bit_execution_bounded (n q a b B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3400=q) (ha : s.natReg 3401=a)
 (hb : s.natReg 3402=b) (abound : a<2^q) (bbound : b<2^q)
 (bound : WordBound B s) (extent : 18≤B) (size : 2^q≤B) :
 ∃u,BoundedExecution bitProgram n x B s (12*q+7) u ∧ u.pc=17 ∧
 u.natReg 3403=a^^^b ∧ UniformXorTableMachine.Frame s u := by
 have boot:=boot_bounded n B x s pc bound extent
 have c : Control q 0 (initialized s) := by
  constructor <;> simp [initialized,writeNat,next,pc,hq]
 obtain ⟨u,run⟩:=bit_loop_bounded n q 0 q B x (initialized s) c (by omega)
  (by simpa [initialized,writeNat,next,ha] using abound)
  (by simpa [initialized,writeNat,next,hb] using bbound) boot.final_bound extent
  (by simpa [initialized,writeNat,next,ha,hb] using (Nat.le_of_lt (Nat.xor_lt_two_pow abound bbound)).trans size)
  (by simpa [initialized,writeNat,next] using size)
 have all : BoundedExecution bitProgram n x B s (12*q+7) u := by
  convert boot.executes run using 1; omega
 obtain ⟨v,rv,pv,nv,fv⟩:=bit_execution n x q a b s pc hq ha hb abound bbound
 have eq: u=v := (Executes.deterministic all.executes rv).2
 subst v
 exact ⟨u,all,pv,nv,fv⟩


theorem runs_same_end {p : Program} {n t : ℕ} {x : Fin n→ℂ} {s u v : State}
 (h : Runs p n x s t u) (h' : Runs p n x s t v) : u=v := by
 induction h generalizing v with
 | refl s => cases h';rfl
 | next hs tail ih =>
   cases h' with
   | next hv tv =>
     rw [hs] at hv
     cases hv
     exact ih tv

def powerBoot : List Op := [.literal 3422 0,.literal 3423 1,.literal 3424 1,.literal 3425 2,.literal 3426 0]
def powerBody : List Op := [.binary .mul 3423 3423 3425,.binary .add 3422 3422 3424]

theorem power_boot_code : BlockAt powerBoot tableProgram 0 := by
 intro i hi;change i<5 at hi;interval_cases i <;> rfl

theorem power_body_code : BlockAt powerBody tableProgram 6 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl

theorem power_boot_bounded (n B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (bound : WordBound B s) (extent : 38≤B) :
 BoundedRuns tableProgram n x B s 5 (powerInitialized s) :=
 block_runs powerBoot tableProgram 0 n B x s power_boot_code pc bound (by change 0+5≤B;omega)
  (by simp [powerBoot,readable,Op.readable]) (by simp [powerBoot,peak,Op.peak];omega)

theorem power_round_bounded (n q base j B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : PowerControl q base j s) (small : j<q) (bound : WordBound B s) (extent : 38≤B)
 (size : 2^q≤B) : BoundedRuns tableProgram n x B s 4 (powerRound s) := by
 have qBound : q≤B := by simpa only [c.length] using bound.2.1 3420
 have nextSize : 2^(j+1)≤2^q := by gcongr;omega
 have weight : s.natReg 3423*2≤B := by rw [c.value,←pow_succ];exact nextSize.trans size
 have enteredBound:=changePC_bound B s 6 bound (by omega)
 have body:=block_runs powerBody tableProgram 6 n B x (powerEntered s) power_body_code rfl enteredBound
  (by change 6+2≤B;omega)
  (by simp [powerBody,readable,Op.readable,Op.apply,evalNat])
  (by simp [powerBody,peak,Op.peak,Op.apply,evalNat,powerEntered,writeNat,next,c.two,c.one,c.index];omega)
 have post : applyBlock powerBody (powerEntered s)=powerAdvanced s := by
  simp [powerBody,applyBlock,Op.apply,evalNat,powerAdvanced,powerDoubled,powerEntered,
   writeNat,next,c.two,c.one]
 rw [post] at body
 have first : BoundedRuns tableProgram n x B s 1 (powerEntered s) := by
  refine .next bound ?_ (.refl enteredBound)
  simp [step,tableProgram,tablePrefix,powerEntered,c.pc,c.index,c.length,small]
 have last : BoundedRuns tableProgram n x B (powerAdvanced s) 1 (powerRound s) := by
  refine .next body.final_bound ?_ (.refl (changePC_bound B _ 5 body.final_bound (by omega)))
  simp [step,tableProgram,tablePrefix,powerRound,powerAdvanced,powerDoubled,powerEntered,writeNat,next]
 convert (first.trans body).trans last using 1; rfl

theorem power_loop_bounded (n q base j fuel B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : PowerControl q base j s) (total : j+fuel=q) (bound : WordBound B s)
 (extent : 38≤B) (size : 2^q≤B) :
 ∃u,BoundedRuns tableProgram n x B s (4*fuel+1) u ∧ u.pc=9 ∧
 PowerControl q base q {u with pc:=5} ∧ DataFrame s u := by
 have bounded : ∃u,BoundedRuns tableProgram n x B s (4*fuel+1) u := by
  induction fuel generalizing j s with
  | zero =>
    have same : j=q := by omega
    refine ⟨{s with pc:=9},.next bound ?_ (.refl (changePC_bound B s 9 bound (by omega)))⟩
    simp [step,tableProgram,tablePrefix,c.pc,c.index,c.length,same]
  | succ fuel ih =>
    have first:=power_round_bounded n q base j B x s c (by omega) bound extent size
    obtain ⟨u,last⟩:=ih (j+1) (powerRound s) (power_round_control q base j s c)
      (by omega) first.final_bound
    refine ⟨u,?_⟩
    convert first.trans last using 1; omega
 obtain ⟨u,run⟩:=bounded
 obtain ⟨v,rv,pc,cv,fv⟩:=power_loop n x q base j fuel s c total
 have eq:u=v:=runs_same_end run.runs rv
 subst v
 exact ⟨u,run,pc,cv,fv⟩


def headerBody : List Op := [.binary .add 3400 3420 3426,
 .binary .div 3401 3428 3423,.binary .mod 3402 3428 3423]
def tailBody : List Op := [.binary .add 3430 3421 3428,.store 3430 3403,.binary .add 3428 3428 3424]
def sizeBody : List Op := [.binary .mul 3427 3423 3423,.literal 3428 0]

theorem header_code : BlockAt headerBody tableProgram 12 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl

theorem tail_code : BlockAt tailBody tableProgram 33 := by
 intro i hi;change i<3 at hi;interval_cases i <;> rfl

theorem size_code : BlockAt sizeBody tableProgram 9 := by
 intro i hi;change i<2 at hi;interval_cases i <;> rfl

theorem table_iteration_bounded (n q base k B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : TableControl q base k s) (small : k<2^q*2^q) (bound : WordBound B s)
 (extent : 38≤B) (capacity : base+2^q*2^q≤B) :
 ∃u,BoundedRuns tableProgram n x B s (12*q+15) u ∧ TableControl q base (k+1) u ∧
 u.natHeap=Function.update s.natHeap (base+k) (some ((k/2^q)^^^(k%2^q))) ∧ TableFrame s u := by
 have positive:=Nat.two_pow_pos q
 have size : 2^q≤B := by nlinarith
 have qBound : q≤B := by simpa only [c.length] using bound.2.1 3420
 have kBound : k≤B := by omega
 have ah: k/2^q≤B := (Nat.div_le_self _ _).trans kBound
 have bh: k%2^q≤B := (Nat.le_of_lt (Nat.mod_lt _ positive)).trans size
 let start : State := {s with pc:=12}
 have startBound:=changePC_bound B s 12 bound (by omega)
 have headers:=block_runs headerBody tableProgram 12 n B x start header_code rfl startBound
   (by change 12+3≤B;omega)
   (by simp [headerBody,readable,Op.readable,Op.apply,evalNat,start,writeNat,next,c.size])
   (by simp [headerBody,peak,Op.peak,Op.apply,evalNat,start,writeNat,next,c.length,c.zero,
      c.index,c.size];omega)
 have post : applyBlock headerBody start=tableEntry s := by
   simp [applyBlock,headerBody,Op.apply,evalNat,start,tableEntry,writeNat,next,c.zero,c.size]
 rw [post] at headers
 have first : BoundedRuns tableProgram n x B s 1 start := by
  refine .next bound ?_ (.refl startBound)
  simp [step,tableProgram,tablePrefix,start,c.pc,c.index,c.total,small]
 let entry:=tableEntry s
 let bitEntry : State := {entry with pc:=0}
 have bitBound:=changePC_bound B entry 0 headers.final_bound (by omega)
 have argq : bitEntry.natReg 3400=q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.length]
 have arga : bitEntry.natReg 3401=k/2^q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.index,c.size]
 have argb : bitEntry.natReg 3402=k%2^q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.index,c.size]
 have apos : k/2^q<2^q := (Nat.div_lt_iff_lt_mul positive).2 small
 have bpos : k%2^q<2^q := Nat.mod_lt _ positive
 obtain ⟨out,bits,pout,vout,fout⟩:=bit_execution_bounded n q (k/2^q) (k%2^q) B x bitEntry rfl
   argq arga argb apos bpos bitBound (by omega) size
 have moved:=UniformBoundedAssembly.boundedExecution_placed bit_code
   (by rw [bitProgram_length];omega) (by omega : 33≤B) bits
 have entryPC : entry.pc=15 := by simp [entry,tableEntry,writeNat,next]
 have putback : UniformAssembly.placed 15 bitEntry=entry := by
  change {entry with pc:=15}=entry
  rw [←entryPC]
 rw [putback] at moved
 let done : State := {out with pc:=33}
 have same : ∀r,3412≤r→done.natReg r=s.natReg r := by
  intro r hr
  have keep:=fout.2.2.2.2.2 r (Or.inr hr)
  simpa (disch:=omega) [done,bitEntry,entry,tableEntry,writeNat,next] using keep
 have db : done.natReg 3421=base := (same _ (by omega)).trans c.base
 have dk : done.natReg 3428=k := (same _ (by omega)).trans c.index
 have d1 : done.natReg 3424=1 := (same _ (by omega)).trans c.one
 have dv : done.natReg 3403=(k/2^q)^^^(k%2^q) := vout
 have valueBound : done.natReg 3403≤B := by
  rw [dv];exact (Nat.le_of_lt (Nat.xor_lt_two_pow apos bpos)).trans size
 have tail:=block_runs tailBody tableProgram 33 n B x done tail_code rfl moved.final_bound
  (by change 33+3≤B;omega)
  (by simp [tailBody,readable,Op.readable,Op.apply,evalNat])
  (by simp [tailBody,peak,Op.peak,Op.apply,evalNat,writeNat,next,db,dk,d1];omega)
 have tailPost : applyBlock tailBody done=tableAdvanced done := by
  simp [tailBody,applyBlock,Op.apply,evalNat,tableAdvanced,tableStored,tableAddressed,writeNat,next,d1]
 rw [tailPost] at tail
 have last : BoundedRuns tableProgram n x B (tableAdvanced done) 1 (tableRound done) := by
  refine .next tail.final_bound ?_ (.refl (changePC_bound B _ 11 tail.final_bound (by omega)))
  simp [step,tableProgram,tablePrefix,bitProgram,tableRound,tableAdvanced,tableStored,
   tableAddressed,writeNat,next,done]
 have all : BoundedRuns tableProgram n x B s (12*q+15) (tableRound done) := by
  convert (((first.trans headers).trans moved).trans tail).trans last using 1
  simp only [headerBody,tailBody,List.length_cons,List.length_nil]
  omega
 obtain ⟨v,rv,cv,hv,fv⟩:=table_iteration n x q base k s c small
 have eq:tableRound done=v:=runs_same_end all.runs rv
 subst v
 exact ⟨tableRound done,all,cv,hv,fv⟩


theorem table_loop_bounded (n q base k fuel B : ℕ) (x : Fin n→ℂ) (s : State)
 (c : TableControl q base k s) (total : k+fuel=2^q*2^q) (bound : WordBound B s)
 (extent : 38≤B) (capacity : base+2^q*2^q≤B) :
 ∃u,BoundedExecution tableProgram n x B s ((12*q+15)*fuel+2) u := by
 induction fuel generalizing k s with
 | zero =>
   have same : k=2^q*2^q := by omega
   let u : State := {s with pc:=37}
   refine ⟨u,.next bound ?_ (.halt (changePC_bound B s 37 bound (by omega)) ?_)⟩
   · simp [step,tableProgram,tablePrefix,c.pc,c.index,c.total,same,u]
   · simp [step,tableProgram,tablePrefix,bitProgram,u]
 | succ fuel ih =>
   obtain ⟨v,first,cv,_,_⟩:=table_iteration_bounded n q base k B x s c (by omega) bound extent capacity
   obtain ⟨u,last⟩:=ih (k+1) v cv (by omega) first.final_bound
   refine ⟨u,?_⟩
   convert first.executes last using 1; ring

/-- The complete physical XOR producer stays in one supplied common word
budget, including all loop counters, intermediate words and heap addresses. -/
theorem table_execution_bounded (n q base B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3420=q) (hb : s.natReg 3421=base)
 (bound : WordBound B s) (extent : 38≤B) (capacity : base+2^q*2^q≤B) :
 ∃u,BoundedExecution tableProgram n x B s (4*q+10+(12*q+15)*(2^q*2^q)) u ∧ u.pc=37 ∧
 Entries q base (2^q*2^q) u ∧ Outside q base s.natHeap u ∧ TableFrame s u := by
 have positive:=Nat.two_pow_pos q
 have size : 2^q≤B := by nlinarith
 have boot:=power_boot_bounded n B x s pc bound extent
 let start:=powerInitialized s
 have control : PowerControl q base 0 start := by
  constructor <;> simp [start,powerInitialized,writeNat,next,pc,hq,hb]
 obtain ⟨v,power,pv,cv,_⟩:=power_loop_bounded n q base 0 q B x start control (by omega) boot.final_bound extent size
 have vl : v.natReg 3420=q := cv.length
 have vb : v.natReg 3421=base := cv.base
 have vv : v.natReg 3423=2^q := cv.value
 have vo : v.natReg 3424=1 := cv.one
 have vz : v.natReg 3426=0 := cv.zero
 have sizes:=block_runs sizeBody tableProgram 9 n B x v size_code pv power.final_bound
   (by change 9+2≤B;omega) (by simp [sizeBody,readable,Op.readable,evalNat])
   (by simp [sizeBody,peak,Op.peak,evalNat,vv];omega)
 have sizePost : applyBlock sizeBody v=tableSized v := by
  simp [applyBlock,sizeBody,Op.apply,evalNat,tableSized]
 rw [sizePost] at sizes
 let sized:=tableSized v
 have cs : TableControl q base 0 sized := by
  constructor <;> simp [sized,tableSized,writeNat,next,pv,vl,vb,vv,vo,vz]
 obtain ⟨u,last⟩:=table_loop_bounded n q base 0 (2^q*2^q) B x sized cs (by omega) sizes.final_bound extent capacity
 have all : BoundedExecution tableProgram n x B s (4*q+10+(12*q+15)*(2^q*2^q)) u := by
  convert ((boot.trans power).trans sizes).executes last using 1
  simp only [sizeBody,List.length_cons,List.length_nil]
  ring
 obtain ⟨v,rv,pv,ev,ov,fv⟩:=table_execution n x q base s pc hq hb
 have eq:u=v:=(Executes.deterministic all.executes rv).2
 subst v
 exact ⟨u,all,pv,ev,ov,fv⟩


def lookupBody : List Op := [.binary .mul 3444 3442 3441,.binary .add 3444 3444 3443,
 .binary .add 3445 3440 3444,.load 3446 3445]

theorem lookup_code : BlockAt lookupBody lookupProgram 0 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl

theorem lookup_execution_bounded (n q base a b B : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=0) (h0 : s.natReg 3440=base) (h1 : s.natReg 3441=2^q)
 (h2 : s.natReg 3442=a) (h3 : s.natReg 3443=b)
 (entries : Entries q base (2^q*2^q) s) (ha : a<2^q) (hb : b<2^q)
 (bound : WordBound B s) (extent : 5≤B) (capacity : base+2^q*2^q≤B) :
 BoundedExecution lookupProgram n x B s 5 (lookupLoaded s (a^^^b)) := by
 have load:=Entries.lookup q base s entries a b ha hb
 rw [Nat.add_assoc] at load
 have positive:=Nat.two_pow_pos q
 have address : base+(a*2^q+b)≤B := by nlinarith
 have offset : a*2^q+b≤B := by omega
 have product : a*2^q≤B := by omega
 have value : a^^^b≤B := (Nat.le_of_lt (Nat.xor_lt_two_pow ha hb)).trans (by nlinarith)
 have body:=block_runs lookupBody lookupProgram 0 n B x s lookup_code pc bound
   (by change 0+4≤B;omega)
   (by simp [lookupBody,readable,Op.readable,Op.apply,evalNat,writeNat,next,h0,h1,h2,h3,load])
   (by simp [lookupBody,peak,Op.peak,Op.apply,evalNat,writeNat,next,h0,h1,h2,h3,load];omega)
 have post : applyBlock lookupBody s=lookupLoaded s (a^^^b) := by
   simp [applyBlock,lookupBody,Op.apply,evalNat,lookupLoaded,lookupAddressed,lookupOffset,
    lookupMultiplied,writeNat,next,h0,h1,h2,h3,load,Nat.add_assoc]
 rw [post] at body
 have last : BoundedExecution lookupProgram n x B (lookupLoaded s (a^^^b)) 1 (lookupLoaded s (a^^^b)) := by
  refine .halt body.final_bound ?_
  simp [step,lookupProgram,lookupLoaded,lookupAddressed,lookupOffset,lookupMultiplied,writeNat,next,pc]
 convert body.executes last using 1; rfl

/-- Even the table preparation has a linear allowance in its surrounding
2^k array when the fixed saving radix has at least three coordinate blocks. -/
theorem table_cost_array_bound (q k : ℕ) (fit : 3*q≤k) :
 4*q+10+(12*q+15)*(2^q*2^q)≤25*2^k := by
 have positive:=Nat.two_pow_pos q
 have growth : q+1≤2^q := Nat.lt_two_pow_self
 have first : 4*q+10+(12*q+15)*(2^q*2^q)≤25*(q+1)*(2^q*2^q) := by nlinarith
 have second : 25*(q+1)*(2^q*2^q)≤25*2^q*(2^q*2^q) := by nlinarith
 have power : 25*2^q*(2^q*2^q)=25*2^(3*q) := by
  rw [show 3*q=q+(q+q) by ring,pow_add,pow_add]
  ring
 have monotone : 2^(3*q)≤2^k := by gcongr
 exact first.trans (second.trans (power.le.trans (Nat.mul_le_mul_left 25 monotone)))

end
end ExactFourierCircuits.UniformXorWordBounds
