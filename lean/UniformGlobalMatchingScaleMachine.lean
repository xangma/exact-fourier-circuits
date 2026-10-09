import UniformMatchingConjugateLoadMachine
import UniformZeroFreePairShearMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformGlobalMatchingScaleMachine
open UniformMachine UniformAssembly UniformTensorMonomialMachine
open UniformPairMachine (prepared)
noncomputable section

/-- Nine actual coordinate-diagonal banks. The first four vary with the
coefficient; the remaining five are constants already provided by startup.
Unused matching coordinates have factor1. -/
def factor (mu : ℂ) (lane : Fin 9) (side : Fin 2) : ℂ :=
 if side=0 then
  if lane=0 then (5/4)/UniformLocalShear.kappa mu else
  if lane=1 then (4/5)*UniformLocalShear.kappa mu else
  if lane=2 then (5/4)/(mu-UniformLocalShear.kappa mu) else
  if lane=3 then (4/5)*(mu-UniformLocalShear.kappa mu) else
  if lane=4 then -3 else if lane=5 then 2 else if lane=6 then -1/8 else
  if lane=7 then 1 else ExactFourierCircuits.a⁻¹
 else if lane=6 then -1/6 else if lane=7 then Complex.I else
  if lane=8 then Complex.I*ExactFourierCircuits.a⁻¹ else 1

/-- A C slot uses the actual matched pair tensor, with singleton identity.
All other slots are tensor diagonals read from one of the nine physical banks. -/
inductive Phase where
 | diagonal (lane : Fin 9)
 | kernel
 deriving DecidableEq

def blockPhases (front back : Fin 9) : List Phase :=
 [.diagonal front,.diagonal 7,.kernel,.diagonal 8,
  .diagonal 4,.diagonal 7,.kernel,.diagonal 8,
  .diagonal 5,.diagonal 7,.kernel,.diagonal 8,
  .diagonal 6,.diagonal back]
def phases : List Phase := blockPhases 0 1++blockPhases 2 3
lemma phases_length : phases.length=28 := rfl
lemma six_kernel_slots : phases.count .kernel=6 := by decide

/-- Nat4330=the fresh contiguous nine-lane pool,4331=radix. Coefficient source
and row headers are those of the real25-instruction decoder; no scales enter. -/
def scaleSetup : List Op := [.literal 1620 0,.literal 1621 0,
 .add 1622 2106 1620,.add 1623 2107 1620]
def constantSetup : List Op := [.literalScalar 118 (-3),.literalScalar 119 2,
 .literalScalar 120 (-1/8),.literalScalar 121 (-1/6),
 .literal 4350 3,.getScalar 122 4350,.literal 4350 4,.getScalar 123 4350,
 .literal 4350 5,.getScalar 124 4350]
def readEndpoints : List Op := [.literal 4350 3,.mul 4351 2141 4350,
 .add 4351 2140 4351,.getNat 4352 4351,.literal 4354 1,
 .add 4351 4351 4354,.getNat 4353 4351]
/-- lane,actual endpoint register,prepared coefficient register. Values1
need no overwrite after the charged full-pool initialization. -/
def writes : List (ℕ×ℕ×ℕ) :=
 [(0,4352,104),(1,4352,105),(2,4352,108),(3,4352,109),
  (4,4352,118),(5,4352,119),(6,4352,120),(6,4353,121),
  (7,4353,123),(8,4352,122),(8,4353,124)]
def oneStore (w : ℕ×ℕ×ℕ) : List Op :=
 [.literal 4354 w.1,.mul 4355 4331 4354,.add 4355 4330 4355,
  .add 4355 4355 w.2.1,.putScalar 4355 w.2.2]
def stores : List Op := writes.flatMap oneStore

def beforePrep : Program := scaleSetup.map Op.code++
 UniformMatchingConjugateLoadMachine.rowProgram.map (relocate 4 29)
def beforeConstants : Program := beforePrep++
 UniformZeroFreePairShearMachine.prep.map UniformReciprocalMachine.Op.code
def beforeStores : Program := beforeConstants++constantSetup.map Op.code++readEndpoints.map Op.code
def rowProgram : Program := beforeStores++stores.map Op.code++[.halt]
lemma scaleSetup_length : scaleSetup.length=4 := rfl
lemma constantSetup_length : constantSetup.length=10 := rfl
lemma readEndpoints_length : readEndpoints.length=7 := rfl
lemma stores_length : stores.length=55 := rfl
lemma rowProgram_length : rowProgram.length=120 := rfl
lemma decoder_code : CodeAt UniformMatchingConjugateLoadMachine.rowProgram rowProgram 4 29 := by
 intro i hi;change i<25 at hi;interval_cases i <;> rfl
lemma scaleSetup_code : BlockAt scaleSetup rowProgram 0 := by
 intro i hi;change i<4 at hi;interval_cases i <;> rfl
lemma prep_code : UniformReciprocalMachine.BlockAt UniformZeroFreePairShearMachine.prep rowProgram 29 := by
 intro i hi;change i<18 at hi;interval_cases i <;> rfl
lemma constantSetup_code : BlockAt constantSetup rowProgram 47 := by
 intro i hi;change i<10 at hi;interval_cases i <;> rfl
lemma endpoints_code : BlockAt readEndpoints rowProgram 57 := by
 intro i hi;change i<7 at hi;interval_cases i <;> rfl
lemma stores_code : BlockAt stores rowProgram 64 := by
 intro i hi;change i<55 at hi;interval_cases i <;> rfl
lemma row_halt : rowProgram[119]?=some .halt := rfl

/-- The only coefficient identities needed by the writer come from the
actual18-op zero-free preparation, including mu0. -/
lemma factor_variable (mu : ℂ) (s : State) (ready : UniformZeroFreePairShearMachine.Scales mu s) :
 s.scalarReg 104=prepared (factor mu 0 0) ∧
 s.scalarReg 105=prepared (factor mu 1 0) ∧
 s.scalarReg 108=prepared (factor mu 2 0) ∧
 s.scalarReg 109=prepared (factor mu 3 0) := by
 simpa [factor] using ⟨ready.1,ready.2.1,ready.2.2.1,ready.2.2.2.1⟩
structure StoreReady (pool r d e : ℕ) (mu : ℂ) (s : State) : Prop where
 pool : s.natReg 4330=pool
 radix : s.natReg 4331=r
 left : s.natReg 4352=d
 right : s.natReg 4353=e
 frontK : s.scalarReg 104=prepared (factor mu 0 0)
 backK : s.scalarReg 105=prepared (factor mu 1 0)
 frontR : s.scalarReg 108=prepared (factor mu 2 0)
 backR : s.scalarReg 109=prepared (factor mu 3 0)
 minusThree : s.scalarReg 118=prepared (factor mu 4 0)
 two : s.scalarReg 119=prepared (factor mu 5 0)
 finalLeft : s.scalarReg 120=prepared (factor mu 6 0)
 finalRight : s.scalarReg 121=prepared (factor mu 6 1)
 postLeft : s.scalarReg 122=prepared (factor mu 8 0)
 preRight : s.scalarReg 123=prepared (factor mu 7 1)
 postRight : s.scalarReg 124=prepared (factor mu 8 1)
def active (lane : Fin 9) (side : Fin 2) : Prop :=
 (side=0 ∧ lane≠7) ∨ (side=1 ∧ 6≤lane.val)
def address (pool r d e : ℕ) (lane : Fin 9) (side : Fin 2) : ℕ :=
 pool+lane.val*r+(if side=0 then d else e)
def FactorTable (pool r d e : ℕ) (mu : ℂ) (s : State) : Prop :=
 ∀lane side,active lane side → s.scalarHeap (address pool r d e lane side)=some (prepared (factor mu lane side))

/-- Each five-op write is proved separately; the eleven writes are then
composed without expanding a55-op state expression. -/
def storeAddress (w : ℕ×ℕ×ℕ) (s : State) : ℕ :=
 s.natReg 4330+w.1*s.natReg 4331+s.natReg w.2.1

lemma applyBlock_append (xs ys : List Op) (s : State) :
 applyBlock (xs++ys) s=applyBlock ys (applyBlock xs s) := by
 induction xs generalizing s with
 | nil => rfl
 | cons x xs ih => exact ih (x.apply s)

lemma oneStore_nat (w : ℕ×ℕ×ℕ) (s : State) (q : ℕ)
 (h4:q≠4354) (h5:q≠4355) :
 (applyBlock (oneStore w) s).natReg q=s.natReg q := by
 simp [oneStore,applyBlock,Op.apply,writeNat,next,h4,h5]
lemma oneStore_scalars (w : ℕ×ℕ×ℕ) (s : State) :
 (applyBlock (oneStore w) s).scalarReg=s.scalarReg := rfl
lemma oneStore_heap (w : ℕ×ℕ×ℕ) (s : State)
 (h4:w.2.1≠4354) (h5:w.2.1≠4355) :
 (applyBlock (oneStore w) s).scalarHeap=
 Function.update s.scalarHeap (storeAddress w s) (some (s.scalarReg w.2.2)) := by
 simp [oneStore,applyBlock,Op.apply,writeNat,next,storeAddress,h4,h5,
  Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]
lemma oneStore_frames (w : ℕ×ℕ×ℕ) (s : State) :
 (applyBlock (oneStore w) s).natHeap=s.natHeap ∧
 (applyBlock (oneStore w) s).outputs=s.outputs ∧
 (applyBlock (oneStore w) s).rootOrders=s.rootOrders := ⟨rfl,rfl,rfl⟩
lemma oneStore_ready (w : ℕ×ℕ×ℕ) (pool r d e : ℕ) (mu : ℂ)
 (s : State) (h:StoreReady pool r d e mu s) :
 StoreReady pool r d e mu (applyBlock (oneStore w) s) := by
 rcases h with ⟨p,rh,dv,ev,fk,bk,fr,br,m,t,fl,ft,al,sr,ar⟩
 exact ⟨(oneStore_nat w s 4330 (by decide) (by decide)).trans p,
  (oneStore_nat w s 4331 (by decide) (by decide)).trans rh,
  (oneStore_nat w s 4352 (by decide) (by decide)).trans dv,
  (oneStore_nat w s 4353 (by decide) (by decide)).trans ev,
  fk,bk,fr,br,m,t,fl,ft,al,sr,ar⟩
lemma writeList_ready (xs : List (ℕ×ℕ×ℕ)) (pool r d e : ℕ) (mu : ℂ)
 (s : State) (h:StoreReady pool r d e mu s) :
 StoreReady pool r d e mu (applyBlock (xs.flatMap oneStore) s) := by
 induction xs generalizing s with
 | nil => exact h
 | cons w xs ih =>
  rw [List.flatMap_cons,applyBlock_append]
  exact ih _ (oneStore_ready w pool r d e mu s h)
lemma stores_ready (pool r d e : ℕ) (mu : ℂ) (s : State) (h:StoreReady pool r d e mu s) :
 StoreReady pool r d e mu (applyBlock stores s) :=
 writeList_ready writes pool r d e mu s h

def storedHeap (xs : List (ℕ×ℕ×ℕ)) (s : State)
 (heap : ℕ→Option Scalar) : ℕ→Option Scalar := match xs with
 | [] => heap
 | w::xs => storedHeap xs s (Function.update heap (storeAddress w s) (some (s.scalarReg w.2.2)))
lemma storedHeap_eq (xs : List (ℕ×ℕ×ℕ)) (s t : State)
 (ha:∀w∈xs,storeAddress w s=storeAddress w t)
 (hv:∀w∈xs,s.scalarReg w.2.2=t.scalarReg w.2.2) (heap : ℕ→Option Scalar) :
 storedHeap xs s heap=storedHeap xs t heap := by
 induction xs generalizing heap with
 | nil => rfl
 | cons w xs ih =>
  simp only [storedHeap,ha w (List.mem_cons_self),hv w (List.mem_cons_self)]
  exact ih (by intro v h;exact ha v (List.mem_cons_of_mem w h))
   (by intro v h;exact hv v (List.mem_cons_of_mem w h)) _
lemma writeList_heap (xs : List (ℕ×ℕ×ℕ)) (s : State)
 (coords:∀w∈xs,w.2.1≠4354 ∧ w.2.1≠4355) :
 (applyBlock (xs.flatMap oneStore) s).scalarHeap=storedHeap xs s s.scalarHeap := by
 induction xs generalizing s with
 | nil => rfl
 | cons w xs ih =>
  rw [List.flatMap_cons,applyBlock_append,ih _ (by
   intro v hv;exact coords v (List.mem_cons_of_mem w hv))]
  have hw:=coords w (List.mem_cons_self)
  rw [oneStore_heap w s hw.1 hw.2]
  exact storedHeap_eq xs _ s (by
   intro v hv
   have hc:=coords v (List.mem_cons_of_mem w hv)
   simp only [storeAddress,oneStore_nat w s 4330 (by decide) (by decide),
    oneStore_nat w s 4331 (by decide) (by decide),oneStore_nat w s v.2.1 hc.1 hc.2])
   (by intro v hv;rfl) _
lemma writes_coords : ∀w∈writes,w.2.1≠4354 ∧ w.2.1≠4355 := by
 intro w hw
 simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hw
 rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw <;> subst w <;> decide
lemma stores_table (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (ne:d≠e) :
 FactorTable pool r d e mu (applyBlock stores s) := by
 intro lane side ha
 change (applyBlock (writes.flatMap oneStore) s).scalarHeap _=_
 rw [writeList_heap writes s writes_coords]
 rcases h with ⟨p,rh,dv,ev,fk,bk,fr,br,m,t,fl,ft,al,sr,ar⟩
 fin_cases lane <;> fin_cases side
 all_goals simp only [active] at ha
 all_goals first | contradiction | skip
 all_goals simp (disch:=omega) [storedHeap,writes,storeAddress,address,
  p,rh,dv,ev,fk,bk,fr,br,m,t,fl,ft,al,sr,ar]

def FullFactorTable (pool r d e : ℕ) (mu : ℂ) (s : State) : Prop :=
 ∀lane side,s.scalarHeap (address pool r d e lane side)=some (prepared (factor mu lane side))
def InactiveReady (pool r d e : ℕ) (s : State) : Prop :=
 ∀lane side,¬active lane side → s.scalarHeap (address pool r d e lane side)=some (prepared 1)
lemma inactive_factor (mu : ℂ) (lane : Fin 9) (side : Fin 2) (h:¬active lane side) :
 factor mu lane side=1 := by
 fin_cases lane <;> fin_cases side <;> simp_all [active,factor]
lemma stores_inactive (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (ne:d≠e)
 (lane:Fin 9) (side:Fin 2) (hn:¬active lane side) :
 (applyBlock stores s).scalarHeap (address pool r d e lane side)=
 s.scalarHeap (address pool r d e lane side) := by
 rw [show stores=writes.flatMap oneStore from rfl,writeList_heap writes s writes_coords]
 fin_cases lane <;> fin_cases side
 all_goals simp only [active] at hn
 all_goals first | contradiction | skip
 all_goals simp (disch:=omega) [storedHeap,writes,storeAddress,address,
  h.pool,h.radix,h.left,h.right]
lemma stores_complete (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (ne:d≠e)
 (init:InactiveReady pool r d e s) : FullFactorTable pool r d e mu (applyBlock stores s) := by
 intro lane side
 by_cases ha:active lane side
 · exact stores_table pool r d e mu s h hd he ne lane side ha
 · rw [stores_inactive pool r d e mu s h hd he ne lane side ha,init lane side ha,
    inactive_factor mu lane side ha]
def PairOutside (pool r d e q : ℕ) : Prop :=
 ∀lane:Fin 9,q≠address pool r d e lane 0 ∧ q≠address pool r d e lane 1
lemma storedHeap_other (xs : List (ℕ×ℕ×ℕ)) (s : State) (heap : ℕ→Option Scalar)
 (q : ℕ) (h:∀w∈xs,q≠storeAddress w s) : storedHeap xs s heap q=heap q := by
 induction xs generalizing heap with
 | nil => rfl
 | cons w xs ih =>
  simp only [storedHeap]
  rw [ih _ (by intro v hv;exact h v (List.mem_cons_of_mem w hv))]
  exact Function.update_of_ne (h w (List.mem_cons_self)) _ _
lemma stores_other_pair (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (q : ℕ) (hq:PairOutside pool r d e q) :
 (applyBlock stores s).scalarHeap q=s.scalarHeap q := by
 rw [show stores=writes.flatMap oneStore from rfl,writeList_heap writes s writes_coords]
 apply storedHeap_other
 intro w hw
 simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hw
 rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw <;> subst w
 all_goals simp only [storeAddress,h.pool,h.radix,h.left,h.right]
 all_goals first | exact (hq 0).1 | exact (hq 1).1 | exact (hq 2).1 |
  exact (hq 3).1 | exact (hq 4).1 | exact (hq 5).1 | exact (hq 6).1 |
  exact (hq 6).2 | exact (hq 7).2 | exact (hq 8).1 | exact (hq 8).2
lemma readable_append (xs ys : List Op) (s : State) :
 readable (xs++ys) s ↔ readable xs s ∧ readable ys (applyBlock xs s) := by
 induction xs generalizing s with
 | nil => simp [readable,applyBlock]
 | cons o xs ih => simp only [List.cons_append,readable,applyBlock,ih,and_assoc]
lemma peak_append (xs ys : List Op) (s : State) :
 peak (xs++ys) s=max (peak xs s) (peak ys (applyBlock xs s)) := by
 induction xs generalizing s with
 | nil => simp [peak,applyBlock]
 | cons o xs ih => simp only [List.cons_append,peak,applyBlock,ih,max_assoc]
lemma oneStore_readable (w : ℕ×ℕ×ℕ) (s : State) : readable (oneStore w) s := by
 simp [oneStore,readable,Op.readable]
lemma storeAddress_bound (w : ℕ×ℕ×ℕ) (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (hl:w.1<9)
 (hc:w.2.1=4352 ∨ w.2.1=4353) :
 pool ≤ storeAddress w s ∧ storeAddress w s < pool+9*r := by
 have hm:w.1*r≤8*r:=Nat.mul_le_mul_right r (by omega)
 rcases hc with hc|hc
 all_goals simp only [storeAddress,h.pool,h.radix,hc,h.left,h.right];constructor <;> omega
lemma oneStore_safe (w : ℕ×ℕ×ℕ) (pool r d e B : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (hl:w.1<9)
 (hc:w.2.1=4352 ∨ w.2.1=4353) (bound:pool+9*r≤B) (code:120≤B) :
 peak (oneStore w) s≤B := by
 have hm:w.1*r≤8*r:=Nat.mul_le_mul_right r (by omega)
 rcases hc with hc|hc
 all_goals simp [oneStore,peak,Op.peak,Op.apply,writeNat,next,
  hc,h.pool,h.radix,h.left,h.right,Nat.mul_comm r w.1];omega
lemma writes_bounds : ∀w∈writes,w.1<9 ∧ (w.2.1=4352 ∨ w.2.1=4353) := by
 intro w hw
 simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at hw
 rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw|hw <;> subst w <;> decide
lemma writeList_safe (xs : List (ℕ×ℕ×ℕ)) (pool r d e B : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r)
 (bounds:∀w∈xs,w.1<9 ∧ (w.2.1=4352 ∨ w.2.1=4353))
 (bound:pool+9*r≤B) (code:120≤B) :
 readable (xs.flatMap oneStore) s ∧ peak (xs.flatMap oneStore) s≤B := by
 induction xs generalizing s with
 | nil => simp [readable,peak]
 | cons w xs ih =>
  have hw:=bounds w (List.mem_cons_self)
  have ht:=ih _ (oneStore_ready w pool r d e mu s h) (by
   intro v hv;exact bounds v (List.mem_cons_of_mem w hv))
  rw [List.flatMap_cons,readable_append,peak_append]
  exact ⟨⟨oneStore_readable w s,ht.1⟩,max_le
   (oneStore_safe w pool r d e B mu s h hd he hw.1 hw.2 bound code) ht.2⟩
lemma stores_safe (pool r d e B : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r)
 (bound:pool+9*r≤B) (code:120≤B) : readable stores s ∧ peak stores s≤B :=
 writeList_safe writes pool r d e B mu s h hd he writes_bounds bound code
lemma writeList_other (xs : List (ℕ×ℕ×ℕ)) (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r)
 (bounds:∀w∈xs,w.1<9 ∧ (w.2.1=4352 ∨ w.2.1=4353))
 (coords:∀w∈xs,w.2.1≠4354 ∧ w.2.1≠4355) (q:ℕ)
 (hq:q<pool ∨ pool+9*r≤q) :
 (applyBlock (xs.flatMap oneStore) s).scalarHeap q=s.scalarHeap q := by
 induction xs generalizing s with
 | nil => rfl
 | cons w xs ih =>
  rw [List.flatMap_cons,applyBlock_append,ih _ (oneStore_ready w pool r d e mu s h)
   (by intro v hv;exact bounds v (List.mem_cons_of_mem w hv))
   (by intro v hv;exact coords v (List.mem_cons_of_mem w hv))]
  have hw:=bounds w (List.mem_cons_self)
  have hc:=coords w (List.mem_cons_self)
  rw [oneStore_heap w s hc.1 hc.2]
  have ha:=storeAddress_bound w pool r d e mu s h hd he hw.1 hw.2
  exact Function.update_of_ne (by omega) _ _
lemma stores_other (pool r d e : ℕ) (mu : ℂ) (s : State)
 (h:StoreReady pool r d e mu s) (hd:d<r) (he:e<r) (q:ℕ)
 (hq:q<pool ∨ pool+9*r≤q) : (applyBlock stores s).scalarHeap q=s.scalarHeap q :=
 writeList_other writes pool r d e mu s h hd he writes_bounds writes_coords q hq
lemma writeList_frames (xs : List (ℕ×ℕ×ℕ)) (s : State) :
 (applyBlock (xs.flatMap oneStore) s).natHeap=s.natHeap ∧
 (applyBlock (xs.flatMap oneStore) s).scalarReg=s.scalarReg ∧
 (applyBlock (xs.flatMap oneStore) s).outputs=s.outputs ∧
 (applyBlock (xs.flatMap oneStore) s).rootOrders=s.rootOrders ∧
 (∀q,q≠4354→q≠4355→(applyBlock (xs.flatMap oneStore) s).natReg q=s.natReg q) := by
 induction xs generalizing s with
 | nil => exact ⟨rfl,rfl,rfl,rfl,by intro q h4 h5;rfl⟩
 | cons w xs ih =>
  rw [List.flatMap_cons,applyBlock_append]
  have ht:=ih (applyBlock (oneStore w) s)
  have hf:=oneStore_frames w s
  exact ⟨ht.1.trans hf.1,ht.2.1.trans (oneStore_scalars w s),
   ht.2.2.1.trans hf.2.1,ht.2.2.2.1.trans hf.2.2,
   fun q h4 h5=>(ht.2.2.2.2 q h4 h5).trans (oneStore_nat w s q h4 h5)⟩
lemma stores_frames (s : State) : (applyBlock stores s).natHeap=s.natHeap ∧
 (applyBlock stores s).scalarReg=s.scalarReg ∧ (applyBlock stores s).outputs=s.outputs ∧
 (applyBlock stores s).rootOrders=s.rootOrders ∧
 (∀q,q≠4354→q≠4355→(applyBlock stores s).natReg q=s.natReg q) :=
 writeList_frames writes s

lemma prep_runs (n B : ℕ) (x : Fin n→ℂ) (mu : ℂ) (a b : ℕ) (s : State)
 (args:UniformZeroFreePairShearMachine.Args 0 0 a b s)
 (src:UniformZeroFreePairShearMachine.Sources mu a b s)
 (pc:s.pc=29) (hs:WordBound B s) (code:120≤B) :
 BoundedRuns rowProgram n x B s 18
 (UniformReciprocalMachine.applyBlock UniformZeroFreePairShearMachine.prep s) := by
 have hk:=UniformLocalShear.kappa_ne_zero mu
 have hr:=UniformLocalShear.second_ne_zero mu
 have reads:UniformReciprocalMachine.readable UniformZeroFreePairShearMachine.prep s:=by
  simpa [UniformReciprocalMachine.readable,UniformZeroFreePairShearMachine.prep,
   UniformReciprocalMachine.Op.readable,UniformReciprocalMachine.Op.apply,
   writeNat,writeScalar,next,evalField,prepared,args.coefficient,args.conjugateCoefficient,
   src.1,src.2,UniformLocalShear.kappa] using ⟨hk,hr⟩
 have peaks:UniformReciprocalMachine.peak UniformZeroFreePairShearMachine.prep s≤B:=by
  simp [UniformReciprocalMachine.peak,UniformZeroFreePairShearMachine.prep,
   UniformReciprocalMachine.Op.peak,UniformReciprocalMachine.Op.apply,writeNat,next,
   args.leftAddress,args.rightAddress]
 exact UniformReciprocalMachine.block_runs _ rowProgram 29 n B x s prep_code pc hs
  (by change 29+18≤B;omega) reads peaks
lemma block_outputs (xs : List Op) (s : State) :
 (applyBlock xs s).outputs=s.outputs ∧ (applyBlock xs s).rootOrders=s.rootOrders := by
 induction xs generalizing s with
 | nil => exact ⟨rfl,rfl⟩
 | cons o xs ih =>
  have h:=ih (o.apply s)
  cases o <;> exact ⟨h.1,h.2⟩
lemma constant_safe (s : State) (hc:UniformHadamardPairMachine.Constants s) :
 readable constantSetup s ∧ peak constantSetup s≤5 := by
 constructor
 · simp [constantSetup,readable,Op.readable,Op.apply,writeNat,writeScalar,next,
   hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2]
 · simp [constantSetup,peak,Op.peak]
lemma constant_frame (s : State) :
 (applyBlock constantSetup s).scalarHeap=s.scalarHeap ∧
 (applyBlock constantSetup s).natHeap=s.natHeap ∧
 (∀q,q≠4350→(applyBlock constantSetup s).natReg q=s.natReg q) := by
 refine ⟨rfl,rfl,?_⟩
 intro q hq;simp [constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next,hq]
lemma endpoints_frame (s : State) :
 (applyBlock readEndpoints s).scalarReg=s.scalarReg ∧
 (applyBlock readEndpoints s).scalarHeap=s.scalarHeap ∧
 (applyBlock readEndpoints s).natHeap=s.natHeap ∧
 (∀q,q≠4350→q≠4351→q≠4352→q≠4353→q≠4354→
 (applyBlock readEndpoints s).natReg q=s.natReg q) := by
 refine ⟨rfl,rfl,rfl,?_⟩
 intro q h0 h1 h2 h3 h4
 simp [readEndpoints,applyBlock,Op.apply,writeNat,next,h0,h1,h2,h3,h4]
lemma endpoints_safe (D i d e B : ℕ) (s : State)
 (hD:s.natReg 2140=D) (hi:s.natReg 2141=i)
 (hd:s.natHeap (D+3*i)=some d) (he:s.natHeap (D+3*i+1)=some e)
 (bound:D+3*i+1≤B) (db:d≤B) (eb:e≤B) (code:120≤B) :
 readable readEndpoints s ∧ peak readEndpoints s≤B := by
 constructor
 · simp [readEndpoints,readable,Op.readable,Op.apply,writeNat,next,hD,hi,
   Nat.mul_comm i 3,hd,he]
 · simp [readEndpoints,peak,Op.peak,Op.apply,writeNat,next,hD,hi,
   Nat.mul_comm i 3,hd,he];omega
lemma tail_ready (mu : ℂ) (pool r D i d e : ℕ) (s : State)
 (sc:UniformZeroFreePairShearMachine.Scales mu s)
 (hc:UniformHadamardPairMachine.Constants s)
 (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (hD:s.natReg 2140=D) (hi:s.natReg 2141=i)
 (hd:s.natHeap (D+3*i)=some d) (he:s.natHeap (D+3*i+1)=some e) :
 StoreReady pool r d e mu (applyBlock readEndpoints (applyBlock constantSetup s)) := by
 let c:=applyBlock constantSetup s
 have cf:=constant_frame s
 have ef:=endpoints_frame c
 have fv:=factor_variable mu s sc
 constructor
 · exact (ef.2.2.2 4330 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((cf.2.2 4330 (by decide)).trans hp)
 · exact (ef.2.2.2 4331 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((cf.2.2 4331 (by decide)).trans hr)
 · simp [readEndpoints,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next,
    hD,hi,Nat.mul_comm i 3,hd]
 · simp [readEndpoints,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next,
    hD,hi,Nat.mul_comm i 3,he]
 · change (applyBlock readEndpoints c).scalarReg 104=_
   rw [ef.1]
   simpa [c,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next] using fv.1
 · change (applyBlock readEndpoints c).scalarReg 105=_
   rw [ef.1]
   simpa [c,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next] using fv.2.1
 · change (applyBlock readEndpoints c).scalarReg 108=_
   rw [ef.1]
   simpa [c,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next] using fv.2.2.1
 · change (applyBlock readEndpoints c).scalarReg 109=_
   rw [ef.1]
   simpa [c,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next] using fv.2.2.2
 all_goals change (applyBlock readEndpoints c).scalarReg _=_
 all_goals rw [ef.1]
 all_goals simp [c,constantSetup,applyBlock,Op.apply,writeNat,writeScalar,next,
  factor,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,prepared]

lemma scaleSetup_nat (s : State) (q : ℕ)
 (h0:q≠1620) (h1:q≠1621) (h2:q≠1622) (h3:q≠1623) :
 (applyBlock scaleSetup s).natReg q=s.natReg q := by
 simp [scaleSetup,applyBlock,Op.apply,writeNat,next,h0,h1,h2,h3]

structure Loaded (a b pool r D i : ℕ) (mu : ℂ) (s u : State) : Prop where
 pc:u.pc=29
 source:UniformZeroFreePairShearMachine.Sources mu a b u
 args:UniformZeroFreePairShearMachine.Args 0 0 a b u
 pool:u.natReg 4330=pool
 radix:u.natReg 4331=r
 rows:u.natReg 2140=D
 index:u.natReg 2141=i
 natHeap:u.natHeap=s.natHeap
 outputs:u.outputs=s.outputs
 roots:u.rootOrders=s.rootOrders
 outside:∀q,q≠a→q≠b→u.scalarHeap q=s.scalarHeap q

lemma row_loaded {R K C T P V a b B pool r D n : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row) (i:Fin rows.length)
 (co:UniformMatchingConjugateLoadMachine.Coefficient R)
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (coefficient:(rows[i.val]'i.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P co)
 (poolHeader:s.natReg 4330=pool) (radixHeader:s.natReg 4331=r)
 (rowBound:D+3*rows.length≤B) (code:120≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃out,
 BoundedRuns rowProgram n x B s (UniformMatchingConjugateLoadMachine.runtime co+11) out ∧
 Loaded a b pool r D i.val (UniformMatchingConjugateLoadMachine.value K bank co) s out := by
 let h:=applyBlock scaleSetup s
 have safe:readable scaleSetup s ∧ peak scaleSetup s≤B:=by
  constructor
  · simp [scaleSetup,readable,Op.readable]
  · simp [scaleSetup,peak,Op.peak,Op.apply,writeNat,next,args.original,args.conjugate]
    exact ⟨layout.bound.trans' (Nat.le_of_lt layout.destinations),layout.bound⟩
 have head:=block_runs scaleSetup rowProgram 0 n B x s scaleSetup_code pc hs
  (by change 0+4≤B;omega) safe.1 safe.2
 have hpc:h.pc=4:=by rw [applyBlock_pc,pc];rfl
 let entry:State:={h with pc:=0}
 have eh:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val entry:=by
  constructor <;> simp [entry,h,scaleSetup,applyBlock,Op.apply,writeNat,next,
   args.positive,args.negative,args.constants,args.conjugates,args.original,args.conjugate,
   args.rows,args.index]
 have es:UniformMatchingConjugateLoadMachine.Sources K C T P V bank entry:=
  ⟨sources.positive,sources.negative,sources.conjugate,sources.constants⟩
 have et:UniformCrossShearTableMachine.Table D rows entry:=table
 obtain ⟨u,loaded,ua,ub,outside,nh,outs,roots,upc,frame⟩:=
  UniformMatchingConjugateLoadMachine.execution_from_row rows i co eh layout es et coefficient
   rowBound (by omega) x rfl (changePC_bound B h 0 head.final_bound (by omega))
 let v:State:={u with pc:=29}
 have load:BoundedRuns rowProgram n x B h
   (UniformMatchingConjugateLoadMachine.runtime co+7) v:=by
  have hh:=UniformBoundedAssembly.boundedExecution_placed decoder_code
   (by rw [UniformMatchingConjugateLoadMachine.rowProgram_length];omega) (by omega) loaded
  have eq:placed 4 entry=h:=by change {h with pc:=4}=h;rw [←hpc]
  simpa only [eq] using hh
 have stable : ∀q,q≠1620→q≠1621→q≠1622→q≠1623→q≠2105→q≠2110→q≠2111→q≠2112→
  v.natReg q=s.natReg q := by
  intro q h0 h1 h2 h3 h4 h5 h6 h7
  exact (frame.2.2.2.1 q h4 h5 h6 h7).trans (scaleSetup_nat s q h0 h1 h2 h3)
 have prepArgs:UniformZeroFreePairShearMachine.Args 0 0 a b v:=by
  constructor
  · exact (frame.2.2.2.1 1620 (by decide) (by decide) (by decide) (by decide)).trans
     (by simp [entry,h,scaleSetup,applyBlock,Op.apply,writeNat,next])
  · exact (frame.2.2.2.1 1621 (by decide) (by decide) (by decide) (by decide)).trans
     (by simp [entry,h,scaleSetup,applyBlock,Op.apply,writeNat,next])
  · exact (frame.2.2.2.1 1622 (by decide) (by decide) (by decide) (by decide)).trans
     (by simp [entry,h,scaleSetup,applyBlock,Op.apply,writeNat,next,args.original])
  · exact (frame.2.2.2.1 1623 (by decide) (by decide) (by decide) (by decide)).trans
     (by simp [entry,h,scaleSetup,applyBlock,Op.apply,writeNat,next,args.conjugate])
 refine ⟨v,?_,⟨rfl,⟨ua,ub⟩,prepArgs,?_,?_,?_,?_,nh,outs,roots,outside⟩⟩
 · convert head.trans load using 1
   simp only [scaleSetup_length];omega
 · exact (stable 4330 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans poolHeader
 · exact (stable 4331 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans radixHeader
 · exact (stable 2140 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans args.rows
 · exact (stable 2141 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans args.index

lemma prepared_tail (mu : ℂ) (a b pool r D i d e n B : ℕ) (x : Fin n→ℂ) (s : State)
 (args:UniformZeroFreePairShearMachine.Args 0 0 a b s)
 (source:UniformZeroFreePairShearMachine.Sources mu a b s)
 (constants:UniformHadamardPairMachine.Constants s)
 (hp:s.natReg 4330=pool) (hr:s.natReg 4331=r)
 (hD:s.natReg 2140=D) (hi:s.natReg 2141=i)
 (hd:s.natHeap (D+3*i)=some d) (he:s.natHeap (D+3*i+1)=some e)
 (rowBound:D+3*i+1≤B) (db:d≤B) (eb:e≤B)
 (pc:s.pc=29) (hs:WordBound B s) (code:120≤B) : ∃out,
 BoundedRuns rowProgram n x B s 35 out ∧ out.pc=64 ∧ StoreReady pool r d e mu out ∧
 out.scalarHeap=s.scalarHeap ∧ out.natHeap=s.natHeap ∧
 out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders := by
 let z:=UniformReciprocalMachine.applyBlock UniformZeroFreePairShearMachine.prep s
 have arith:=prep_runs n B x mu a b s args source pc hs code
 have scales:=UniformZeroFreePairShearMachine.prep_scales mu 0 0 a b s args source
 have pf:=UniformZeroFreePairShearMachine.prep_frame s
 have zpc:z.pc=47:=by rw [UniformReciprocalMachine.applyBlock_pc,pc];rfl
 have sh:z.scalarHeap=s.scalarHeap:=pf.scalarHeap
 have zc:UniformHadamardPairMachine.Constants z:=by
  simpa only [UniformHadamardPairMachine.Constants,sh] using constants
 have zh:z.natHeap=s.natHeap:=pf.natHeap
 have stable:∀q,q≠0→q≠1→q≠1624→z.natReg q=s.natReg q:=pf.natReg
 have zp:z.natReg 4330=pool:=(stable 4330 (by decide) (by decide) (by decide)).trans hp
 have zr:z.natReg 4331=r:=(stable 4331 (by decide) (by decide) (by decide)).trans hr
 have zd:z.natReg 2140=D:=(stable 2140 (by decide) (by decide) (by decide)).trans hD
 have zi:z.natReg 2141=i:=(stable 2141 (by decide) (by decide) (by decide)).trans hi
 have zhd:z.natHeap (D+3*i)=some d:=by rw [zh];exact hd
 have zhe:z.natHeap (D+3*i+1)=some e:=by rw [zh];exact he
 let cst:=applyBlock constantSetup z
 have csafe:=constant_safe z zc
 have constRun:=block_runs constantSetup rowProgram 47 n B x z constantSetup_code zpc arith.final_bound
  (by change 47+10≤B;omega) csafe.1 (csafe.2.trans (by omega))
 have cpc:cst.pc=57:=by rw [applyBlock_pc,zpc];rfl
 have cf:=constant_frame z
 have esafe:=endpoints_safe D i d e B cst
  ((cf.2.2 2140 (by decide)).trans zd) ((cf.2.2 2141 (by decide)).trans zi)
  zhd zhe rowBound db eb code
 let out:=applyBlock readEndpoints cst
 have endRun:=block_runs readEndpoints rowProgram 57 n B x cst endpoints_code cpc constRun.final_bound
  (by change 57+7≤B;omega) esafe.1 esafe.2
 have last:out.pc=64:=by rw [applyBlock_pc,cpc];rfl
 have ef:=endpoints_frame cst
 refine ⟨out,?_,last,tail_ready mu pool r D i d e z scales zc zp zr zd zi zhd zhe,
  ef.2.1.trans (cf.1.trans pf.scalarHeap),ef.2.2.1.trans (cf.2.1.trans pf.natHeap),?_,?_⟩
 · convert (arith.trans constRun).trans endRun using 1
   simp only [constantSetup_length,readEndpoints_length]
 · exact ((block_outputs readEndpoints cst).1.trans (block_outputs constantSetup z).1).trans
    (UniformReciprocalMachine.applyBlock_outputs _ s).1
 · exact ((block_outputs readEndpoints cst).2.trans (block_outputs constantSetup z).2).trans
    (UniformReciprocalMachine.applyBlock_outputs _ s).2

/-- All scales and physical factor cells are internally generated. The actual
coefficient and row tapes are entry data, rather than a factor/action oracle. -/
theorem row_execution {R K C T P V a b B pool r D n : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row) (i:Fin rows.length)
 (co:UniformMatchingConjugateLoadMachine.Coefficient R)
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (coefficient:(rows[i.val]'i.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P co)
 (constants:UniformHadamardPairMachine.Constants s)
 (poolHeader:s.natReg 4330=pool) (radixHeader:s.natReg 4331=r)
 (dst:(rows[i.val]'i.isLt).dst<r) (src:(rows[i.val]'i.isLt).src<r)
 (distinct:(rows[i.val]'i.isLt).dst≠(rows[i.val]'i.isLt).src)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B)
 (poolBound:pool+9*r≤B) (code:120≤B)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃out,
 BoundedExecution rowProgram n x B s
  (UniformMatchingConjugateLoadMachine.runtime co+102) out ∧ out.pc=119 ∧
 FactorTable pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src
  (UniformMatchingConjugateLoadMachine.value K bank co) out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q)→q≠a→q≠b → out.scalarHeap q=s.scalarHeap q) ∧
 (∀q,PairOutside pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src q →
  q≠a → q≠b → out.scalarHeap q=s.scalarHeap q) := by
 obtain ⟨u,run,loaded⟩:=row_loaded rows i co args layout sources table coefficient
  poolHeader radixHeader rowBound code x pc hs
 have cu:UniformHadamardPairMachine.Constants u:=by
  have keep:∀q,q<a→u.scalarHeap q=s.scalarHeap q:=by
   intro q hq;exact loaded.outside q (by omega) (by have:=layout.destinations;omega)
  exact ⟨(keep 1 (by omega)).trans constants.1,(keep 2 (by omega)).trans constants.2.1,
   (keep 3 (by omega)).trans constants.2.2.1,(keep 4 (by omega)).trans constants.2.2.2.1,
   (keep 5 (by omega)).trans constants.2.2.2.2⟩
 have hd:u.natHeap (D+3*i.val)=some (rows[i.val]'i.isLt).dst:=by
  rw [loaded.natHeap];exact (table _ i.isLt).1
 have he:u.natHeap (D+3*i.val+1)=some (rows[i.val]'i.isLt).src:=by
  rw [loaded.natHeap];exact (table _ i.isLt).2.1
 obtain ⟨v,tailRun,last,ready,heap,nh,outs,roots⟩:=prepared_tail
  (UniformMatchingConjugateLoadMachine.value K bank co) a b pool r D i.val _ _ n B x u
  loaded.args loaded.source cu loaded.pool loaded.radix loaded.rows loaded.index hd he
  (by have hi:=i.isLt;omega) (by omega) (by omega) loaded.pc run.final_bound code
 have safe:=stores_safe pool r _ _ B _ v ready dst src poolBound code
 let out:=applyBlock stores v
 have writeRun:=block_runs stores rowProgram 64 n B x v stores_code last tailRun.final_bound
  (by change 64+55≤B;omega) safe.1 safe.2
 have pcOut:out.pc=119:=by rw [applyBlock_pc,last];rfl
 have halt:BoundedExecution rowProgram n x B out 1 out:=.halt writeRun.final_bound
  (by simp only [step,pcOut,row_halt])
 have f:=stores_frames v
 refine ⟨out,?_,pcOut,stores_table pool r _ _ _ v ready dst src distinct,
  f.1.trans (nh.trans loaded.natHeap),f.2.2.1.trans (outs.trans loaded.outputs),
  f.2.2.2.1.trans (roots.trans loaded.roots),?_⟩
 · convert (run.trans (tailRun.trans writeRun)).executes halt using 1
   simp only [stores_length]
 · constructor
   · intro q hq qa qb
     exact (stores_other pool r _ _ _ v ready dst src q hq).trans
      ((congrFun heap q).trans (loaded.outside q qa qb))
   · intro q hq qa qb
     exact (stores_other_pair pool r _ _ _ v ready q hq).trans
      ((congrFun heap q).trans (loaded.outside q qa qb))

/-- All scales and physical factor cells are internally generated. The actual
coefficient and row tapes are entry data, rather than a factor/action oracle. -/
theorem row_complete_execution {R K C T P V a b B pool r D n : ℕ} {bank:Fin R→ℂ} {s:State}
 (rows:List UniformInPlaceMachine.Row) (i:Fin rows.length)
 (co:UniformMatchingConjugateLoadMachine.Coefficient R)
 (args:UniformMatchingConjugateLoadMachine.RowArgs C T P V a b D i.val s)
 (layout:UniformMatchingConjugateLoadMachine.Layout R C T P V a b B)
 (sources:UniformMatchingConjugateLoadMachine.Sources K C T P V bank s)
 (table:UniformCrossShearTableMachine.Table D rows s)
 (coefficient:(rows[i.val]'i.isLt).coefficient=
  UniformMatchingConjugateLoadMachine.address C T P co)
 (constants:UniformHadamardPairMachine.Constants s)
 (poolHeader:s.natReg 4330=pool) (radixHeader:s.natReg 4331=r)
 (dst:(rows[i.val]'i.isLt).dst<r) (src:(rows[i.val]'i.isLt).src<r)
 (distinct:(rows[i.val]'i.isLt).dst≠(rows[i.val]'i.isLt).src)
 (low:6≤a) (fresh:b<pool) (rowBound:D+3*rows.length≤B)
 (poolBound:pool+9*r≤B) (code:120≤B)
 (inactive:InactiveReady pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src s)
 (x:Fin n→ℂ) (pc:s.pc=0) (hs:WordBound B s) : ∃out,
 BoundedExecution rowProgram n x B s
  (UniformMatchingConjugateLoadMachine.runtime co+102) out ∧ out.pc=119 ∧
 FullFactorTable pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src
  (UniformMatchingConjugateLoadMachine.value K bank co) out ∧
 out.natHeap=s.natHeap ∧ out.outputs=s.outputs ∧ out.rootOrders=s.rootOrders ∧
 (∀q,(q<pool ∨ pool+9*r≤q)→q≠a→q≠b → out.scalarHeap q=s.scalarHeap q) ∧
 (∀q,PairOutside pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src q →
  q≠a → q≠b → out.scalarHeap q=s.scalarHeap q) := by
 obtain ⟨u,run,loaded⟩:=row_loaded rows i co args layout sources table coefficient
  poolHeader radixHeader rowBound code x pc hs
 have cu:UniformHadamardPairMachine.Constants u:=by
  have keep:∀q,q<a→u.scalarHeap q=s.scalarHeap q:=by
   intro q hq;exact loaded.outside q (by omega) (by have:=layout.destinations;omega)
  exact ⟨(keep 1 (by omega)).trans constants.1,(keep 2 (by omega)).trans constants.2.1,
   (keep 3 (by omega)).trans constants.2.2.1,(keep 4 (by omega)).trans constants.2.2.2.1,
   (keep 5 (by omega)).trans constants.2.2.2.2⟩
 have hd:u.natHeap (D+3*i.val)=some (rows[i.val]'i.isLt).dst:=by
  rw [loaded.natHeap];exact (table _ i.isLt).1
 have he:u.natHeap (D+3*i.val+1)=some (rows[i.val]'i.isLt).src:=by
  rw [loaded.natHeap];exact (table _ i.isLt).2.1
 obtain ⟨v,tailRun,last,ready,heap,nh,outs,roots⟩:=prepared_tail
  (UniformMatchingConjugateLoadMachine.value K bank co) a b pool r D i.val _ _ n B x u
  loaded.args loaded.source cu loaded.pool loaded.radix loaded.rows loaded.index hd he
  (by have hi:=i.isLt;omega) (by omega) (by omega) loaded.pc run.final_bound code
 have initial:InactiveReady pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src v:=by
  intro lane side ha
  have range:pool≤address pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src lane side:=by
   simp only [address];split <;> omega
  have neqA:address pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src lane side≠a:=by
   have:=layout.destinations;omega
  have neqB:address pool r (rows[i.val]'i.isLt).dst (rows[i.val]'i.isLt).src lane side≠b:=by omega
  exact (congrFun heap _).trans ((loaded.outside _ neqA neqB).trans (inactive lane side ha))
 have safe:=stores_safe pool r _ _ B _ v ready dst src poolBound code
 let out:=applyBlock stores v
 have writeRun:=block_runs stores rowProgram 64 n B x v stores_code last tailRun.final_bound
  (by change 64+55≤B;omega) safe.1 safe.2
 have pcOut:out.pc=119:=by rw [applyBlock_pc,last];rfl
 have halt:BoundedExecution rowProgram n x B out 1 out:=.halt writeRun.final_bound
  (by simp only [step,pcOut,row_halt])
 have f:=stores_frames v
 refine ⟨out,?_,pcOut,stores_complete pool r _ _ _ v ready dst src distinct initial,
  f.1.trans (nh.trans loaded.natHeap),f.2.2.1.trans (outs.trans loaded.outputs),
  f.2.2.2.1.trans (roots.trans loaded.roots),?_⟩
 · convert (run.trans (tailRun.trans writeRun)).executes halt using 1
   simp only [stores_length]
 · constructor
   · intro q hq qa qb
     exact (stores_other pool r _ _ _ v ready dst src q hq).trans
      ((congrFun heap q).trans (loaded.outside q qa qb))
   · intro q hq qa qb
     exact (stores_other_pair pool r _ _ _ v ready q hq).trans
      ((congrFun heap q).trans (loaded.outside q qa qb))

def natScratch : List ℕ :=
 [0,1,1620,1621,1622,1623,1624,2105,2110,2111,2112,4350,4351,4352,4353,4354,4355]
lemma row_keeps_nat (q : ℕ) (hq:q∉natScratch) :
 ∀ins∈rowProgram,UniformNewtonTableMachine.KeepsNat q ins := by
 simp only [natScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
 simp [rowProgram,beforeStores,beforeConstants,beforePrep,scaleSetup,constantSetup,
  readEndpoints,stores,writes,oneStore,Op.code,UniformMatchingConjugateLoadMachine.rowProgram,
  UniformAssembly.embed,UniformMatchingConjugateLoadMachine.rowLoad,
  UniformMatchingConjugateLoadMachine.program,UniformMatchingConjugateLoadMachine.boot,
  UniformMatchingConjugateLoadMachine.positive,UniformMatchingConjugateLoadMachine.negative,
  UniformMatchingConjugateLoadMachine.realConstant,UniformMatchingConjugateLoadMachine.store,
  UniformAssembly.relocate,UniformZeroFreePairShearMachine.prep,UniformReciprocalMachine.Op.code,
  UniformNewtonTableMachine.KeepsNat,ne_comm,hq]
lemma execution_nat {n B t q : ℕ} {x : Fin n→ℂ} {s u : State}
 (run:BoundedExecution rowProgram n x B s t u) (hq:q∉natScratch) :
 u.natReg q=s.natReg q := UniformNewtonTableMachine.Executes.keeps_nat run.executes (row_keeps_nat q hq)
lemma execution_saved {n B t : ℕ} {x : Fin n→ℂ} {s u : State}
 (run:BoundedExecution rowProgram n x B s t u) :
 ∀q,100≤q→q≤106→u.natReg q=s.natReg q := by
 intro q lo hi
 exact execution_nat run (by simp only [natScratch,List.mem_cons,List.not_mem_nil,or_false];omega)

end
end ExactFourierCircuits.UniformGlobalMatchingScaleMachine
