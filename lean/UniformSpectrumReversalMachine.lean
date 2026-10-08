import UniformScalarCopyMachine
import UniformConvolutionDAG

set_option autoImplicit false
namespace ExactFourierCircuits.UniformSpectrumReversalMachine
open UniformMachine

/-- Nat1800=N>0,1801=source,1802=destination; fresh seven-block reversal.
Only loads/stores move scalars, preserving their actual dependency tags. -/
def program : Program := [
 .natLiteral 1803 0,.natLiteral 1804 1,.natLiteral 1805 7,
 .natBinary .mul 1806 1800 1805,.branchLT 1803 1806 5 17,
 .natBinary .div 1807 1803 1800,.natBinary .mul 1807 1807 1800,
 .natBinary .mod 1808 1803 1800,.natBinary .sub 1808 1800 1808,
 .natBinary .mod 1808 1808 1800,.natBinary .add 1807 1807 1808,
 .natBinary .add 1807 1801 1807,.loadScalar 40 1807,
 .natBinary .add 1809 1802 1803,.storeScalar 1809 40,
 .natBinary .add 1803 1803 1804,.jump 4,.halt]
theorem program_length : program.length=18 := rfl
noncomputable section

def reverseNat (N i : ℕ) : ℕ := (i/N)*N+(N-i%N)%N

theorem index_lt {N i : ℕ} (hN:0<N) (hi:i<7*N) : reverseNat N i<7*N := by
 have hq:i/N<7:=(Nat.div_lt_iff_lt_mul hN).mpr (by omega)
 have hb:=Nat.mul_le_mul_right N (show i/N≤6 by omega)
 have hr:=Nat.mod_lt (N-i%N) hN
 unfold reverseNat;omega

def Bank (N a : ℕ) (v:Fin (7*N)→Scalar) (s:State) : Prop :=
 ∀i,s.scalarHeap (a+i.val)=some (v i)
def Outside (N d : ℕ) (s u:State) : Prop :=
 ∀ i, (i < d ∨ d+7*N ≤ i) → u.scalarHeap i=s.scalarHeap i

def Frame (s u:State) : Prop := u.natHeap=s.natHeap ∧ u.outputs=s.outputs ∧ u.rootOrders=s.rootOrders ∧
 (∀ i, (i < 1803 ∨ 1809 < i) → u.natReg i=s.natReg i) ∧ (∀ i, i≠40 → u.scalarReg i=s.scalarReg i)
theorem Frame.trans {s u w:State} (f:Frame s u) (g:Frame u w) : Frame s w :=
 ⟨g.1.trans f.1,g.2.1.trans f.2.1,g.2.2.1.trans f.2.2.1,
 fun i h=>(g.2.2.2.1 i h).trans (f.2.2.2.1 i h),fun i h=>(g.2.2.2.2 i h).trans (f.2.2.2.2 i h)⟩

structure Cursor (N a d k:ℕ) (v:Fin (7*N)→Scalar) (s:State) : Prop where
 positive:0<N
 width:s.natReg 1800=N
 source:s.natReg 1801=a
 destination:s.natReg 1802=d
 index:s.natReg 1803=k
 one:s.natReg 1804=1
 seven:s.natReg 1805=7
 count:s.natReg 1806=7*N
 bank:Bank N a v s
 copied:∀i:Fin (7*N),i.val<k→s.scalarHeap (d+i.val)=some (v ⟨reverseNat N i.val,index_lt positive i.isLt⟩)

def entered (s:State):={s with pc:=5}
def quotient (s:State) (N k:ℕ):=writeNat (entered s) 1807 (k/N)
def blockBase (s:State) (N k:ℕ):=writeNat (quotient s N k) 1807 ((k/N)*N)
def remainder (s:State) (N k:ℕ):=writeNat (blockBase s N k) 1808 (k%N)
def difference (s:State) (N k:ℕ):=writeNat (remainder s N k) 1808 (N-k%N)
def residue (s:State) (N k:ℕ):=writeNat (difference s N k) 1808 ((N-k%N)%N)
def offset (s:State) (N k:ℕ):=writeNat (residue s N k) 1807 (reverseNat N k)
def address (s:State) (N a k:ℕ):=writeNat (offset s N k) 1807 (a+reverseNat N k)
def loaded (s:State) (N a k:ℕ) (v:Scalar):=writeScalar (address s N a k) 40 v
def target (s:State) (N a d k:ℕ) (v:Scalar):=writeNat (loaded s N a k v) 1809 (d+k)
def stored (s:State) (N a d k:ℕ) (v:Scalar):=
 {next (target s N a d k v) with scalarHeap:=Function.update s.scalarHeap (d+k) (some v)}
def advanced (s:State) (N a d k:ℕ) (v:Scalar):=writeNat (stored s N a d k v) 1803 (k+1)
def rowEnd (s:State) (N a d k:ℕ) (v:Scalar):={advanced s N a d k v with pc:=4}

theorem row_heap (s:State) (N a d k:ℕ) (v:Scalar) :
 (rowEnd s N a d k v).scalarHeap=Function.update s.scalarHeap (d+k) (some v):=rfl

theorem row_frame (s:State) (N a d k:ℕ) (v:Scalar) : Frame s (rowEnd s N a d k v) := by
 refine ⟨rfl,rfl,rfl,?_,?_⟩
 · intro i hi
   simp (disch:=omega) [rowEnd,advanced,stored,target,loaded,address,offset,residue,difference,
     remainder,blockBase,quotient,entered,writeNat,writeScalar,next]
 · intro i hi
   simp [rowEnd,advanced,stored,target,loaded,address,offset,residue,difference,
     remainder,blockBase,quotient,entered,writeNat,writeScalar,next,hi]

theorem row_runs (n N a d k B:ℕ) (x:Fin n→ℂ) (v:Fin (7*N)→Scalar) (s:State)
 (cur:Cursor N a d k v s) (hk:k<7*N) (hd:a+7*N≤d) (hB:d+7*N≤B)
 (hc:18≤B) (hp:s.pc=4) (hs:WordBound B s) :
 BoundedRuns program n x B s 13 (rowEnd s N a d k (v ⟨reverseNat N k,index_lt cur.positive hk⟩)) := by
 let value:=v ⟨reverseNat N k,index_lt cur.positive hk⟩
 have hN:=cur.positive
 have hq:k/N<7:=(Nat.div_lt_iff_lt_mul hN).mpr (by omega)
 have hbase:=Nat.mul_le_mul_right N (show k/N≤6 by omega)
 have hv:=index_lt hN hk
 have hread:s.scalarHeap (a+reverseNat N k)=some value:=cur.bank ⟨reverseNat N k,index_lt cur.positive hk⟩
 dsimp [reverseNat,value] at hread
 have b0:=changePC_bound B s 5 hs (by omega)
 have b1:=writeNat_bound B (entered s) 1807 (k/N) b0 (by change 6≤B;omega) (by omega)
 have b2:=writeNat_bound B (quotient s N k) 1807 ((k/N)*N) b1
   (by simp [quotient,entered,writeNat,next];omega) (by omega)
 have b3:=writeNat_bound B (blockBase s N k) 1808 (k%N) b2
   (by simp [blockBase,quotient,entered,writeNat,next];omega) (by have h:=Nat.mod_lt k hN;omega)
 have b4:=writeNat_bound B (remainder s N k) 1808 (N-k%N) b3
   (by simp [remainder,blockBase,quotient,entered,writeNat,next];omega) (by omega)
 have b5:=writeNat_bound B (difference s N k) 1808 ((N-k%N)%N) b4
   (by simp [difference,remainder,blockBase,quotient,entered,writeNat,next];omega)
   (by have h:=Nat.mod_lt (N-k%N) hN;omega)
 have b6:=writeNat_bound B (residue s N k) 1807 (reverseNat N k) b5
   (by simp [residue,difference,remainder,blockBase,quotient,entered,writeNat,next];omega) (by omega)
 have b7:=writeNat_bound B (offset s N k) 1807 (a+reverseNat N k) b6
   (by simp [offset,residue,difference,remainder,blockBase,quotient,entered,writeNat,next];omega) (by omega)
 have b8:=writeScalar_bound B (address s N a k) 40 value b7
   (by simp [address,offset,residue,difference,remainder,blockBase,quotient,entered,writeNat,next];omega)
 have b9:=writeNat_bound B (loaded s N a k value) 1809 (d+k) b8
   (by simp [loaded,address,offset,residue,difference,remainder,blockBase,quotient,entered,writeNat,writeScalar,next];omega) (by omega)
 have b10:=UniformScalarCopyMachine.store_bound B (target s N a d k value) (d+k) value b9
   (by simp [target,loaded,address,offset,residue,difference,remainder,blockBase,quotient,entered,writeNat,writeScalar,next];omega) (by omega)
 have b11:=writeNat_bound B (stored s N a d k value) 1803 (k+1) b10
   (by simp [stored,target,loaded,address,offset,residue,difference,remainder,blockBase,quotient,entered,writeNat,writeScalar,next];omega) (by omega)
 have bf:=changePC_bound B (advanced s N a d k value) 4 b11 (by omega)
 refine .next hs (u:=entered s) ?_ (.next b0 (u:=quotient s N k) ?_
  (.next b1 (u:=blockBase s N k) ?_ (.next b2 (u:=remainder s N k) ?_
   (.next b3 (u:=difference s N k) ?_ (.next b4 (u:=residue s N k) ?_
    (.next b5 (u:=offset s N k) ?_ (.next b6 (u:=address s N a k) ?_
     (.next b7 (u:=loaded s N a k value) ?_ (.next b8 (u:=target s N a d k value) ?_
      (.next b9 (u:=stored s N a d k value) ?_ (.next b10 (u:=advanced s N a d k value) ?_
       (.next b11 ?_ (.refl bf)))))))))))))
 all_goals simp [step,program,rowEnd,advanced,stored,target,loaded,address,offset,residue,difference,
  remainder,blockBase,quotient,entered,writeNat,writeScalar,next,hp,cur.width,cur.source,cur.destination,
  cur.index,cur.count,cur.one,hk,evalNat,hN.ne',hread,reverseNat,value]


theorem row_outside (s:State) (N a d k:ℕ) (v:Scalar) (hk:k<7*N) :
 Outside N d s (rowEnd s N a d k v) := by
 intro i hi
 rw [row_heap,Function.update_of_ne (by omega)]

theorem row_cursor (N a d k:ℕ) (v:Fin (7*N)→Scalar) (s:State)
 (cur:Cursor N a d k v s) (hk:k<7*N) (hd:a+7*N≤d) :
 Cursor N a d (k+1) v (rowEnd s N a d k (v ⟨reverseNat N k,index_lt cur.positive hk⟩)) := by
 refine ⟨cur.positive,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 all_goals try {simp [rowEnd,advanced,stored,target,loaded,address,offset,residue,difference,
   remainder,blockBase,quotient,entered,writeNat,writeScalar,next,cur.width,cur.source,cur.destination,
   cur.one,cur.seven,cur.count]}
 · intro i
   rw [row_heap,Function.update_of_ne (by have hi:=i.isLt;omega)]
   exact cur.bank i
 · intro i hi
   rw [row_heap]
   by_cases he:i.val=k
   · subst k;simp
   · rw [Function.update_of_ne (by omega)]
     exact cur.copied i (by omega)

theorem loop_runs (n N a d k f B:ℕ) (x:Fin n→ℂ) (v:Fin (7*N)→Scalar) (s:State)
 (cur:Cursor N a d k v s) (hk:k+f=7*N) (hd:a+7*N≤d) (hB:d+7*N≤B)
 (hc:18≤B) (hp:s.pc=4) (hs:WordBound B s) : ∃u,
 BoundedRuns program n x B s (13*f) u ∧ Cursor N a d (7*N) v u ∧
 Frame s u ∧ Outside N d s u ∧ u.pc=4 := by
 induction f generalizing k s with
 | zero =>
   have he:k=7*N:=by omega
   subst k
   exact ⟨s,.refl hs,cur,⟨rfl,rfl,rfl,fun _ _=>rfl,fun _ _=>rfl⟩,fun _ _=>rfl,hp⟩
 | succ f ih =>
   have hlt:k<7*N:=by omega
   let w:=rowEnd s N a d k (v ⟨reverseNat N k,index_lt cur.positive hlt⟩)
   have runs:=row_runs n N a d k B x v s cur hlt hd hB hc hp hs
   have cw:=row_cursor N a d k v s cur hlt hd
   obtain ⟨u,ru,cu,fu,ou,up⟩:=ih (k+1) w cw (by omega) rfl runs.final_bound
   refine ⟨u,?_,cu,(row_frame s N a d k _).trans fu,?_,up⟩
   · convert runs.trans ru using 1; omega
   · intro i hi
     exact (ou i hi).trans (row_outside s N a d k _ hlt i hi)


def boot0 (s:State):=writeNat s 1803 0
def boot1 (s:State):=writeNat (boot0 s) 1804 1
def boot2 (s:State):=writeNat (boot1 s) 1805 7
def initialized (N:ℕ) (s:State):=writeNat (boot2 s) 1806 (7*N)

theorem boot_runs (n N B:ℕ) (x:Fin n→ℂ) (s:State) (hN:s.natReg 1800=N)
 (hpc:s.pc=0) (hcode:18≤B) (hwidth:7*N≤B) (hs:WordBound B s) :
 BoundedRuns program n x B s 4 (initialized N s) := by
 have b0:=writeNat_bound B s 1803 0 hs (by omega) (by omega)
 have b1:=writeNat_bound B (boot0 s) 1804 1 b0 (by simp [boot0,writeNat,next,hpc];omega) (by omega)
 have b2:=writeNat_bound B (boot1 s) 1805 7 b1 (by simp [boot1,boot0,writeNat,next,hpc];omega) (by omega)
 have b3:=writeNat_bound B (boot2 s) 1806 (7*N) b2
   (by simp [boot2,boot1,boot0,writeNat,next,hpc];omega) hwidth
 refine .next hs (u:=boot0 s) ?_ (.next b0 (u:=boot1 s) ?_
   (.next b1 (u:=boot2 s) ?_ (.next b2 ?_ (.refl b3))))
 all_goals simp [step,program,initialized,boot2,boot1,boot0,writeNat,next,hpc,hN,evalNat,Nat.mul_comm]

theorem boot_frame (N:ℕ) (s:State) : Frame s (initialized N s) := by
 refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl⟩
 intro i hi
 simp (disch:=omega) [initialized,boot2,boot1,boot0,writeNat,next]

theorem initialized_cursor (N a d:ℕ) (v:Fin (7*N)→Scalar) (s:State)
 (hN:0<N) (width:s.natReg 1800=N) (source:s.natReg 1801=a) (destination:s.natReg 1802=d)
 (bank:Bank N a v s) : Cursor N a d 0 v (initialized N s) := by
 refine ⟨hN,?_,?_,?_,?_,?_,?_,?_,bank,?_⟩
 all_goals simp [initialized,boot2,boot1,boot0,writeNat,next,width,source,destination]

def reversed (N:ℕ) (hN:0<N) (v:Fin (7*N)→Scalar) : Fin (7*N)→Scalar :=
 fun i=>v ⟨reverseNat N i.val,index_lt hN i.isLt⟩

/-- Literal eighteen-instruction copier: all seven blocks are reversed modulo N.
The actual Scalar, including its dependency tag, is copied unchanged. -/
theorem execution (n N a d B:ℕ) (x:Fin n→ℂ) (v:Fin (7*N)→Scalar) (s:State)
 (hN:0<N) (width:s.natReg 1800=N) (source:s.natReg 1801=a) (destination:s.natReg 1802=d)
 (bank:Bank N a v s) (fresh:a+7*N≤d) (endBound:d+7*N≤B) (code:18≤B)
 (pc:s.pc=0) (hs:WordBound B s) : ∃u,
 BoundedExecution program n x B s (91*N+6) u ∧ u.pc=17 ∧
 Bank N d (reversed N hN v) u ∧ Bank N a v u ∧ Outside N d s u ∧ Frame s u := by
 have start:=boot_runs n N B x s width pc code (by omega) hs
 have cur:=initialized_cursor N a d v s hN width source destination bank
 have sp:(initialized N s).pc=4:=by simp [initialized,boot2,boot1,boot0,writeNat,next,pc]
 obtain ⟨w,loop,cw,fw,ow,wp⟩:=loop_runs n N a d 0 (7*N) B x v (initialized N s)
   cur (by omega) fresh endBound code sp start.final_bound
 let u:State:={w with pc:=17}
 have ub:=changePC_bound B w 17 loop.final_bound (by omega)
 have stop:BoundedExecution program n x B w 2 u:=by
   refine .next loop.final_bound (u:=u) ?_ (.halt ub ?_)
   · simp [step,program,wp,cw.index,cw.count,u]
   · simp [step,program,u]
 refine ⟨u,?_,rfl,?_,cw.bank,?_,?_⟩
 · convert start.executes (loop.executes stop) using 1; omega
 · intro i
   exact cw.copied i i.isLt
 · intro i hi
   exact ow i hi
 · exact (boot_frame N s).trans fw

end
end ExactFourierCircuits.UniformSpectrumReversalMachine
