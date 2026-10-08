import UniformMachineRuns
import UniformBoundedAssembly
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
namespace ExactFourierCircuits.UniformXorTableMachine
open UniformMachine
noncomputable section

/-- The bytecode has no XOR primitive. A bit costs twelve actual RAM steps. -/
def bitProgram : Program := [
 .natLiteral 3403 0,.natLiteral 3404 1,.natLiteral 3405 0,
 .natLiteral 3406 1,.natLiteral 3407 2,
 .branchLT 3405 3400 6 17,
 .natBinary .mod 3409 3401 3407,.natBinary .mod 3410 3402 3407,
 .natBinary .add 3411 3409 3410,.natBinary .mod 3411 3411 3407,
 .natBinary .mul 3411 3411 3404,.natBinary .add 3403 3403 3411,
 .natBinary .div 3401 3401 3407,.natBinary .div 3402 3402 3407,
 .natBinary .mul 3404 3404 3407,.natBinary .add 3405 3405 3406,
 .jump 5,.halt]

theorem bitProgram_length : bitProgram.length=18 := rfl

def parity (a b : ℕ) : ℕ := (a%2+b%2)%2

theorem xor_decompose (a b : ℕ) : a^^^b = parity a b+2*((a/2)^^^(b/2)) := by
 have h:=Nat.mod_add_div (a^^^b) 2
 rw [Nat.xor_mod_two_eq,Nat.xor_div_two] at h
 simpa [parity,Nat.add_mod] using h.symm

def initialized (s : State) : State :=
 writeNat (writeNat (writeNat (writeNat (writeNat s 3403 0) 3404 1) 3405 0) 3406 1) 3407 2

def entered (s : State) : State := {s with pc:=6}
def firstBit (s : State) : State := writeNat (entered s) 3409 (s.natReg 3401%2)
def secondBit (s : State) : State := writeNat (firstBit s) 3410 (s.natReg 3402%2)
def summed (s : State) : State := writeNat (secondBit s) 3411 (s.natReg 3401%2+s.natReg 3402%2)
def reduced (s : State) : State := writeNat (summed s) 3411 (parity (s.natReg 3401) (s.natReg 3402))
def term (s : State) : State := writeNat (reduced s) 3411 (parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404)
def accumulated (s : State) : State := writeNat (term s) 3403 (s.natReg 3403+parity (s.natReg 3401) (s.natReg 3402)*s.natReg 3404)
def firstHalf (s : State) : State := writeNat (accumulated s) 3401 (s.natReg 3401/2)
def secondHalf (s : State) : State := writeNat (firstHalf s) 3402 (s.natReg 3402/2)
def doubled (s : State) : State := writeNat (secondHalf s) 3404 (s.natReg 3404*2)
def advanced (s : State) : State := writeNat (doubled s) 3405 (s.natReg 3405+1)
def round (s : State) : State := {advanced s with pc:=5}

structure Control (q j : ℕ) (s : State) : Prop where
 pc : s.pc=5
 length : s.natReg 3400=q
 index : s.natReg 3405=j
 one : s.natReg 3406=1
 two : s.natReg 3407=2

theorem initializes (n : ℕ) (x : Fin n→ℂ) (s : State) (pc : s.pc=0) :
 Runs bitProgram n x s 5 (initialized s) := by
 refine .next (u:=writeNat s 3403 0) ?_ (.next (u:=writeNat (writeNat s 3403 0) 3404 1) ?_
  (.next (u:=writeNat (writeNat (writeNat s 3403 0) 3404 1) 3405 0) ?_
   (.next (u:=writeNat (writeNat (writeNat (writeNat s 3403 0) 3404 1) 3405 0) 3406 1) ?_
    (.next (u:=initialized s) ?_ (.refl _)))))
 all_goals simp [step,bitProgram,initialized,writeNat,next,pc]

theorem round_runs (n : ℕ) (x : Fin n→ℂ) (q j : ℕ) (s : State)
 (c : Control q j s) (small : j<q) : Runs bitProgram n x s 12 (round s) := by
 refine .next (u:=entered s) ?_ (.next (u:=firstBit s) ?_ (.next (u:=secondBit s) ?_
  (.next (u:=summed s) ?_ (.next (u:=reduced s) ?_ (.next (u:=term s) ?_
   (.next (u:=accumulated s) ?_ (.next (u:=firstHalf s) ?_ (.next (u:=secondHalf s) ?_
    (.next (u:=doubled s) ?_ (.next (u:=advanced s) ?_ (.next (u:=round s) ?_ (.refl _))))))))))))
 all_goals simp [step,bitProgram,evalNat,round,advanced,doubled,secondHalf,firstHalf,
  accumulated,term,reduced,summed,secondBit,firstBit,entered,writeNat,next,parity,
  c.pc,c.length,c.index,c.one,c.two,small]

theorem round_control (q j : ℕ) (s : State) (c : Control q j s) : Control q (j+1) (round s) := by
 constructor <;> simp [round,advanced,doubled,secondHalf,firstHalf,accumulated,
  term,reduced,summed,secondBit,firstBit,entered,writeNat,next,c.length,c.index,c.one,c.two]

theorem round_numeric (s : State) :
 (round s).natReg 3403+(round s).natReg 3404*((round s).natReg 3401^^^(round s).natReg 3402) =
 s.natReg 3403+s.natReg 3404*(s.natReg 3401^^^s.natReg 3402) := by
 simp only [round,advanced,doubled,secondHalf,firstHalf,accumulated,term,reduced,summed,
  secondBit,firstBit,entered,writeNat,next]
 simp only [Function.update_apply]
 simp
 conv_rhs => rw [xor_decompose]
 ring


def Frame (s u : State) : Prop :=
 u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ r,r<3401 ∨ 3412≤r→u.natReg r=s.natReg r)

theorem Frame.trans {s u v : State} (h : Frame s u) (h' : Frame u v) : Frame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
  h'.2.2.2.1.trans h.2.2.2.1,h'.2.2.2.2.1.trans h.2.2.2.2.1,
  fun r bound => (h'.2.2.2.2.2 r bound).trans (h.2.2.2.2.2 r bound)⟩

theorem initialized_frame (s : State) : Frame s (initialized s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r bound
 simp (disch:=omega) [initialized,writeNat,next]

theorem round_frame (s : State) : Frame s (round s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r bound
 simp (disch:=omega) [round,advanced,doubled,secondHalf,firstHalf,accumulated,term,reduced,
  summed,secondBit,firstBit,entered,writeNat,next]

theorem round_halves (s : State) :
 (round s).natReg 3401=s.natReg 3401/2 ∧
 (round s).natReg 3402=s.natReg 3402/2 := by
 simp [round,advanced,doubled,secondHalf,firstHalf,writeNat,next]

theorem half_bound (a f : ℕ) (h : a<2^(f+1)) : a/2<2^f := by
 apply (Nat.div_lt_iff_lt_mul (by decide : 0<2)).2
 simpa only [pow_succ] using h

/-- Executes every bit with charged control and proves the actual arithmetic
output, rather than assuming a host-computed XOR table. -/
theorem bit_loop (n : ℕ) (x : Fin n→ℂ) (q j fuel : ℕ) (s : State)
 (c : Control q j s) (total : j+fuel=q)
 (a : s.natReg 3401<2^fuel) (b : s.natReg 3402<2^fuel) :
 ∃ u,Executes bitProgram n x s (12*fuel+2) u ∧ u.pc=17 ∧
 u.natReg 3403=s.natReg 3403+s.natReg 3404*(s.natReg 3401^^^s.natReg 3402) ∧ Frame s u := by
 induction fuel generalizing j s with
 | zero =>
   have ha : s.natReg 3401=0 := by simpa using a
   have hb : s.natReg 3402=0 := by simpa using b
   have same : j=q := by omega
   let u : State := {s with pc:=17}
   refine ⟨u,?_,rfl,?_,?_⟩
   · refine .next (u:=u) ?_ (.halt ?_)
     · simp [step,bitProgram,c.pc,c.index,c.length,same,u]
     · rfl
   · simp [u,ha,hb]
   · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
 | succ fuel ih =>
   have small : j<q := by omega
   obtain ⟨u,run,pc,value,frame⟩ := ih (j+1) (round s) (round_control q j s c)
     (by omega) (by rw [(round_halves s).1];exact half_bound _ _ a)
     (by rw [(round_halves s).2];exact half_bound _ _ b)
   refine ⟨u,?_,pc,value.trans (round_numeric s),(round_frame s).trans frame⟩
   simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    (round_runs n x q j s c small).executes run

theorem bit_execution (n : ℕ) (x : Fin n→ℂ) (q a b : ℕ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3400=q) (ha : s.natReg 3401=a)
 (hb : s.natReg 3402=b) (abound : a<2^q) (bbound : b<2^q) :
 ∃u,Executes bitProgram n x s (12*q+7) u ∧ u.pc=17 ∧
 u.natReg 3403=a^^^b ∧ Frame s u := by
 have c : Control q 0 (initialized s) := by
  constructor <;> simp [initialized,writeNat,next,pc,hq]
 obtain ⟨u,run,last,value,frame⟩ := bit_loop n x q 0 q (initialized s) c (by omega)
   (by simpa [initialized,writeNat,next,ha] using abound)
   (by simpa [initialized,writeNat,next,hb] using bbound)
 refine ⟨u,?_,last,?_,(initialized_frame s).trans frame⟩
 · convert (initializes n x s pc).executes run using 1; omega
 · simpa [initialized,writeNat,next,ha,hb] using value

open UniformAssembly

/-- The complete producer computes2^q from q, enumerates every ordered pair,
executes bitProgram, and physically stores every result. Nat3420=q,3421=base. -/
def tablePrefix : Program := [
 .natLiteral 3422 0,.natLiteral 3423 1,.natLiteral 3424 1,.natLiteral 3425 2,.natLiteral 3426 0,
 .branchLT 3422 3420 6 9,.natBinary .mul 3423 3423 3425,
 .natBinary .add 3422 3422 3424,.jump 5,
 .natBinary .mul 3427 3423 3423,.natLiteral 3428 0,
 .branchLT 3428 3427 12 37,.natBinary .add 3400 3420 3426,
 .natBinary .div 3401 3428 3423,.natBinary .mod 3402 3428 3423]

def tableProgram : Program := tablePrefix++bitProgram.map (relocate 15 33)++[
 .natBinary .add 3430 3421 3428,.storeNat 3430 3403,
 .natBinary .add 3428 3428 3424,.jump 11,.halt]

theorem tableProgram_length : tableProgram.length=38 := rfl

theorem bit_code : CodeAt bitProgram tableProgram 15 33 := by
 intro i hi
 change i<18 at hi
 interval_cases i <;> rfl

def powerInitialized (s : State) : State :=
 writeNat (writeNat (writeNat (writeNat (writeNat s 3422 0) 3423 1) 3424 1) 3425 2) 3426 0

def powerEntered (s : State) : State := {s with pc:=6}
def powerDoubled (s : State) : State := writeNat (powerEntered s) 3423 (s.natReg 3423*2)
def powerAdvanced (s : State) : State := writeNat (powerDoubled s) 3422 (s.natReg 3422+1)
def powerRound (s : State) : State := {powerAdvanced s with pc:=5}

structure PowerControl (q base j : ℕ) (s : State) : Prop where
 pc : s.pc=5
 length : s.natReg 3420=q
 base : s.natReg 3421=base
 index : s.natReg 3422=j
 value : s.natReg 3423=2^j
 one : s.natReg 3424=1
 two : s.natReg 3425=2
 zero : s.natReg 3426=0

def DataFrame (s u : State) : Prop := u.natHeap=s.natHeap ∧ u.scalarHeap=s.scalarHeap ∧
 u.scalarReg=s.scalarReg ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,r<3400 ∨ 3431≤r→u.natReg r=s.natReg r)

theorem DataFrame.trans {s u v : State} (h : DataFrame s u) (h' : DataFrame u v) : DataFrame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,h'.2.2.2.1.trans h.2.2.2.1,
 h'.2.2.2.2.1.trans h.2.2.2.2.1,fun r hr => (h'.2.2.2.2.2 r hr).trans (h.2.2.2.2.2 r hr)⟩

theorem power_initializes (n : ℕ) (x : Fin n→ℂ) (s : State) (pc : s.pc=0) :
 Runs tableProgram n x s 5 (powerInitialized s) := by
 refine .next (u:=writeNat s 3422 0) ?_ (.next (u:=writeNat (writeNat s 3422 0) 3423 1) ?_
  (.next (u:=writeNat (writeNat (writeNat s 3422 0) 3423 1) 3424 1) ?_
   (.next (u:=writeNat (writeNat (writeNat (writeNat s 3422 0) 3423 1) 3424 1) 3425 2) ?_
    (.next (u:=powerInitialized s) ?_ (.refl _)))))
 all_goals simp [step,tableProgram,tablePrefix,powerInitialized,writeNat,next,pc]

theorem power_round_runs (n : ℕ) (x : Fin n→ℂ) (q base j : ℕ) (s : State)
 (c : PowerControl q base j s) (small : j<q) : Runs tableProgram n x s 4 (powerRound s) := by
 refine .next (u:=powerEntered s) ?_ (.next (u:=powerDoubled s) ?_
  (.next (u:=powerAdvanced s) ?_ (.next (u:=powerRound s) ?_ (.refl _))))
 all_goals simp [step,tableProgram,tablePrefix,evalNat,powerRound,powerAdvanced,powerDoubled,
  powerEntered,writeNat,next,c.pc,c.length,c.index,c.two,c.one,small]

theorem power_round_control (q base j : ℕ) (s : State) (c : PowerControl q base j s) :
 PowerControl q base (j+1) (powerRound s) := by
 constructor <;> simp [powerRound,powerAdvanced,powerDoubled,powerEntered,writeNat,next,
  c.length,c.base,c.index,c.value,c.one,c.two,c.zero,pow_succ]

theorem power_round_frame (s : State) : DataFrame s (powerRound s) := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
 intro r hr
 simp (disch:=omega) [powerRound,powerAdvanced,powerDoubled,powerEntered,writeNat,next]

theorem power_loop (n : ℕ) (x : Fin n→ℂ) (q base j fuel : ℕ) (s : State)
 (c : PowerControl q base j s) (total : j+fuel=q) :
 ∃u,Runs tableProgram n x s (4*fuel+1) u ∧ u.pc=9 ∧
 PowerControl q base q {u with pc:=5} ∧ DataFrame s u := by
 induction fuel generalizing j s with
 | zero =>
   have same : j=q := by omega
   let u : State := {s with pc:=9}
   refine ⟨u,.next ?_ (.refl _),rfl,?_,?_⟩
   · simp [step,tableProgram,tablePrefix,c.pc,c.index,c.length,same,u]
   · exact ⟨rfl,c.length,c.base,by simpa [same] using c.index,by simpa [same] using c.value,c.one,c.two,c.zero⟩
   · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
 | succ fuel ih =>
   obtain ⟨u,run,pc,last,frame⟩ := ih (j+1) (powerRound s)
     (power_round_control q base j s c) (by omega)
   refine ⟨u,?_,pc,last,(power_round_frame s).trans frame⟩
   convert (power_round_runs n x q base j s c (by omega)).trans run using 1; omega

structure TableControl (q base k : ℕ) (s : State) : Prop where
 pc : s.pc=11
 length : s.natReg 3420=q
 base : s.natReg 3421=base
 size : s.natReg 3423=2^q
 one : s.natReg 3424=1
 zero : s.natReg 3426=0
 total : s.natReg 3427=2^q*2^q
 index : s.natReg 3428=k

def tableEntry (s : State) : State :=
 let a : State := {s with pc:=12}
 let b := writeNat a 3400 (s.natReg 3420)
 let c := writeNat b 3401 (s.natReg 3428/s.natReg 3423)
 writeNat c 3402 (s.natReg 3428%s.natReg 3423)

theorem table_entry_runs (n : ℕ) (x : Fin n→ℂ) (q base k : ℕ) (s : State)
 (c : TableControl q base k s) (small : k<2^q*2^q) :
 Runs tableProgram n x s 4 (tableEntry s) := by
 refine .next (u:={s with pc:=12}) ?_
  (.next (u:=writeNat {s with pc:=12} 3400 q) ?_
   (.next (u:=writeNat (writeNat {s with pc:=12} 3400 q) 3401 (k/2^q)) ?_
    (.next (u:=tableEntry s) ?_ (.refl _))))
 all_goals simp [step,tableProgram,tablePrefix,tableEntry,writeNat,next,evalNat,
  c.pc,c.length,c.zero,c.index,c.size,c.total,small]

def tableAddressed (s : State) : State := writeNat s 3430 (s.natReg 3421+s.natReg 3428)
def tableStored (s : State) : State := {next (tableAddressed s) with natHeap:=
   (Function.update s.natHeap (s.natReg 3421+s.natReg 3428) (some (s.natReg 3403)))}
def tableAdvanced (s : State) : State := writeNat (tableStored s) 3428 (s.natReg 3428+1)
def tableRound (s : State) : State := {tableAdvanced s with pc:=11}

theorem table_tail_runs (n : ℕ) (x : Fin n→ℂ) (s : State)
 (pc : s.pc=33) (one : s.natReg 3424=1) :
 Runs tableProgram n x s 4 (tableRound s) := by
 refine .next (u:=tableAddressed s) ?_ (.next (u:=tableStored s) ?_
  (.next (u:=tableAdvanced s) ?_ (.next (u:=tableRound s) ?_ (.refl _))))
 all_goals simp [step,tableProgram,tablePrefix,bitProgram,tableAddressed,tableStored,tableAdvanced,
  tableRound,writeNat,next,evalNat,pc,one]


def TableFrame (s u : State) : Prop := u.scalarHeap=s.scalarHeap ∧ u.scalarReg=s.scalarReg ∧
 u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀r,r<3400 ∨ 3431≤r→u.natReg r=s.natReg r)

theorem TableFrame.trans {s u v : State} (h : TableFrame s u) (h' : TableFrame u v) : TableFrame s v :=
 ⟨h'.1.trans h.1,h'.2.1.trans h.2.1,h'.2.2.1.trans h.2.2.1,
  h'.2.2.2.1.trans h.2.2.2.1,fun r hr => (h'.2.2.2.2 r hr).trans (h.2.2.2.2 r hr)⟩

theorem table_iteration (n : ℕ) (x : Fin n→ℂ) (q base k : ℕ) (s : State)
 (c : TableControl q base k s) (small : k<2^q*2^q) :
 ∃u,Runs tableProgram n x s (12*q+15) u ∧ TableControl q base (k+1) u ∧
 u.natHeap=Function.update s.natHeap (base+k) (some ((k/2^q)^^^(k%2^q))) ∧ TableFrame s u := by
 let entry:=tableEntry s
 let bitEntry : State := {entry with pc:=0}
 have argq : bitEntry.natReg 3400=q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.length]
 have arga : bitEntry.natReg 3401=k/2^q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.index,c.size]
 have argb : bitEntry.natReg 3402=k%2^q := by simp [bitEntry,entry,tableEntry,writeNat,next,c.index,c.size]
 have apos : k/2^q<2^q := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).2 small
 have bpos : k%2^q<2^q := Nat.mod_lt _ (Nat.two_pow_pos q)
 obtain ⟨out,run,pc,value,frame⟩:=bit_execution n x q (k/2^q) (k%2^q) bitEntry rfl argq arga argb apos bpos
 have epc : entry.pc=15 := by simp [entry,tableEntry,writeNat,next]
 have placedEntry : placed 15 bitEntry=entry := by
  change {entry with pc:=15}=entry
  rw [←epc]
 have moved:=UniformAssembly.Executes.placed bit_code run
 rw [placedEntry] at moved
 let done : State := {out with pc:=33}
 have same : ∀r,3412≤r→done.natReg r=s.natReg r := by
  intro r hr
  have keep:=frame.2.2.2.2.2 r (Or.inr hr)
  simpa (disch:=omega) [done,bitEntry,entry,tableEntry,writeNat,next] using keep
 have cd : TableControl q base k {done with pc:=11} :=
  ⟨rfl,(same _ (by omega)).trans c.length,(same _ (by omega)).trans c.base,
   (same _ (by omega)).trans c.size,(same _ (by omega)).trans c.one,
   (same _ (by omega)).trans c.zero,(same _ (by omega)).trans c.total,
   (same _ (by omega)).trans c.index⟩
 let u:=tableRound done
 refine ⟨u,?_,?_,?_,?_⟩
 · convert ((table_entry_runs n x q base k s c small).trans moved).trans
    (table_tail_runs n x done rfl ((same _ (by omega)).trans c.one)) using 1; omega
 · constructor <;> simp (disch:=omega) [u,tableRound,tableAdvanced,tableStored,tableAddressed,writeNat,next,
    same,c.length,c.base,c.size,c.one,c.zero,c.total,c.index]
 · change Function.update done.natHeap (done.natReg 3421+done.natReg 3428)
     (some (done.natReg 3403))=Function.update s.natHeap (base+k) (some ((k/2^q)^^^(k%2^q)))
   rw [show done.natHeap=s.natHeap from frame.1,cd.base,cd.index,value]
 · refine ⟨frame.2.1,frame.2.2.1,frame.2.2.2.1,frame.2.2.2.2.1,?_⟩
   intro r hr
   have keep:=frame.2.2.2.2.2 r (by omega)
   simpa (disch:=omega) [u,tableRound,tableAdvanced,tableStored,tableAddressed,done,bitEntry,
    entry,tableEntry,writeNat,next] using keep

/-- Every entry is now a physical heap value, not a supplied table certificate. -/
def Entries (q base k : ℕ) (s : State) : Prop :=
 ∀j,j<k→s.natHeap (base+j)=some ((j/2^q)^^^(j%2^q))

def Outside (q base : ℕ) (heap : ℕ→Option ℕ) (s : State) : Prop :=
 ∀a,a<base ∨ base+2^q*2^q≤a→s.natHeap a=heap a

theorem table_loop (n : ℕ) (x : Fin n→ℂ) (q base k fuel : ℕ) (s : State)
 (c : TableControl q base k s) (total : k+fuel=2^q*2^q) (entries : Entries q base k s)
 (heap : ℕ→Option ℕ) (outside : Outside q base heap s) :
 ∃u,Executes tableProgram n x s ((12*q+15)*fuel+2) u ∧ u.pc=37 ∧
 Entries q base (2^q*2^q) u ∧ Outside q base heap u ∧ TableFrame s u := by
 induction fuel generalizing k s with
 | zero =>
   have same : k=2^q*2^q := by omega
   let u : State := {s with pc:=37}
   refine ⟨u,?_,rfl,?_,outside,⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩⟩
   · refine .next (u:=u) ?_ (.halt ?_)
     · simp [step,tableProgram,tablePrefix,c.pc,c.index,c.total,same,u]
     · simp [step,tableProgram,tablePrefix,bitProgram,u]
   · simpa only [Entries,u,same] using entries
 | succ fuel ih =>
   have small : k<2^q*2^q := by omega
   obtain ⟨v,run,cv,hv,fr⟩:=table_iteration n x q base k s c small
   have ev : Entries q base (k+1) v := by
    intro j hj
    rw [hv]
    by_cases eq : j=k
    · subst j;simp
    · rw [Function.update_of_ne (by omega)]
      exact entries j (by omega)
   have ov : Outside q base heap v := by
    intro a ha
    rw [hv,Function.update_of_ne (by omega)]
    exact outside a ha
   obtain ⟨u,last,pc,eu,ou,fu⟩:=ih (k+1) v cv (by omega) ev ov
   refine ⟨u,?_,pc,eu,ou,fr.trans fu⟩
   convert run.executes last using 1; ring


def tableSized (s : State) : State :=
 writeNat (writeNat s 3427 (s.natReg 3423*s.natReg 3423)) 3428 0

theorem table_size_runs (n : ℕ) (x : Fin n→ℂ) (s : State) (pc : s.pc=9) :
 Runs tableProgram n x s 2 (tableSized s) := by
 refine .next (u:=writeNat s 3427 (s.natReg 3423*s.natReg 3423)) ?_
  (.next (u:=tableSized s) ?_ (.refl _))
 all_goals simp [step,tableProgram,tablePrefix,evalNat,tableSized,writeNat,next,pc]

/-- One literal program and no table or function oracle: actual q determines
both dimensions, and all entries have an observed charged physical producer. -/
theorem table_execution (n : ℕ) (x : Fin n→ℂ) (q base : ℕ) (s : State)
 (pc : s.pc=0) (hq : s.natReg 3420=q) (hb : s.natReg 3421=base) :
 ∃u,Executes tableProgram n x s (4*q+10+(12*q+15)*(2^q*2^q)) u ∧ u.pc=37 ∧
 Entries q base (2^q*2^q) u ∧ Outside q base s.natHeap u ∧ TableFrame s u := by
 let start:=powerInitialized s
 have control : PowerControl q base 0 start := by
  constructor <;> simp [start,powerInitialized,writeNat,next,pc,hq,hb]
 obtain ⟨v,run,pv,cv,fv⟩:=power_loop n x q base 0 q start control (by omega)
 let sized:=tableSized v
 have vl : v.natReg 3420=q := cv.length
 have vb : v.natReg 3421=base := cv.base
 have vv : v.natReg 3423=2^q := cv.value
 have vo : v.natReg 3424=1 := cv.one
 have vz : v.natReg 3426=0 := cv.zero
 have cs : TableControl q base 0 sized := by
  constructor <;> simp [sized,tableSized,writeNat,next,pv,vl,vb,vv,vo,vz]
 have sizeframe : DataFrame s sized := by
  refine ⟨fv.1,fv.2.1,fv.2.2.1,fv.2.2.2.1,fv.2.2.2.2.1,?_⟩
  intro r hr
  have keep:=fv.2.2.2.2.2 r hr
  simpa (disch:=omega) [sized,tableSized,start,powerInitialized,writeNat,next] using keep
 obtain ⟨u,last,pu,eu,ou,fu⟩:=table_loop n x q base 0 (2^q*2^q) sized cs (by omega)
   (by intro j hj;omega) s.natHeap (by intro a ha;exact congrArg (fun h => h a) sizeframe.1)
 refine ⟨u,?_,pu,eu,ou,?_⟩
 · convert (((power_initializes n x s pc).trans run).trans (table_size_runs n x v pv)).executes last using 1; ring
 · exact (show TableFrame s sized from ⟨sizeframe.2.1,sizeframe.2.2.1,sizeframe.2.2.2.1,
    sizeframe.2.2.2.2.1,sizeframe.2.2.2.2.2⟩).trans fu

theorem Entries.lookup (q base : ℕ) (s : State) (h : Entries q base (2^q*2^q) s)
 (a b : ℕ) (ha : a<2^q) (hb : b<2^q) : s.natHeap (base+a*2^q+b)=some (a^^^b) := by
 have bound : a*2^q+b<2^q*2^q := by nlinarith
 have got:=h (a*2^q+b) bound
 simpa [Nat.add_assoc,Nat.add_div,Nat.add_mod,Nat.mul_div_right,
  Nat.div_eq_of_lt hb,Nat.mod_eq_of_lt hb,Nat.not_le.mpr hb] using got

/-- Four actual RAM operations and a halt implement one table lookup. -/
def lookupProgram : Program := [
 .natBinary .mul 3444 3442 3441,.natBinary .add 3444 3444 3443,
 .natBinary .add 3445 3440 3444,.loadNat 3446 3445,.halt]

def lookupMultiplied (s : State) : State := writeNat s 3444 (s.natReg 3442*s.natReg 3441)
def lookupOffset (s : State) : State := writeNat (lookupMultiplied s) 3444 (s.natReg 3442*s.natReg 3441+s.natReg 3443)
def lookupAddressed (s : State) : State := writeNat (lookupOffset s) 3445 (s.natReg 3440+s.natReg 3442*s.natReg 3441+s.natReg 3443)
def lookupLoaded (s : State) (value : ℕ) : State := writeNat (lookupAddressed s) 3446 value

theorem lookup_execution (n : ℕ) (x : Fin n→ℂ) (q base a b : ℕ) (s : State)
 (pc : s.pc=0) (h0 : s.natReg 3440=base) (h1 : s.natReg 3441=2^q)
 (h2 : s.natReg 3442=a) (h3 : s.natReg 3443=b)
 (entries : Entries q base (2^q*2^q) s) (ha : a<2^q) (hb : b<2^q) :
 Executes lookupProgram n x s 5 (lookupLoaded s (a^^^b)) ∧
 (lookupLoaded s (a^^^b)).natReg 3446=a^^^b := by
 have load:=Entries.lookup q base s entries a b ha hb
 rw [Nat.add_assoc] at load
 constructor
 · refine .next (u:=lookupMultiplied s) ?_ (.next (u:=lookupOffset s) ?_
   (.next (u:=lookupAddressed s) ?_ (.next (u:=lookupLoaded s (a^^^b)) ?_ (.halt ?_))))
   all_goals simp [step,lookupProgram,lookupLoaded,lookupAddressed,lookupOffset,lookupMultiplied,
     writeNat,next,evalNat,pc,h0,h1,h2,h3,load,Nat.add_assoc]
 · simp [lookupLoaded,writeNat]

end
end ExactFourierCircuits.UniformXorTableMachine
