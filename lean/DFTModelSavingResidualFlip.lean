import DFTModelResidualPeakSyntax

set_option autoImplicit false
namespace ExactFourierCircuits.DFTModelSavingResidualFlip
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelResidualCore
noncomputable section

abbrev Input (t:Ty) := p w (p w (Ty.a t))
abbrev Cell (t:Ty) := p (Input t) w
def size (t:Ty) : Prog false (Cell t) w := .comp (.atom .fst) (.atom .fst)
def source (t:Ty) : Prog false (Cell t) (Ty.a t) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def address (t:Ty) : Prog false (Cell t) w := binary .add
  (binary .mul (binary .div (.atom .snd) (size t)) (size t))
  (binary .sub (binary .sub (size t) (.atom (.lit 1)))
    (binary .mod (.atom .snd) (size t)))
def cell (t:Ty) : Prog false (Cell t) t :=
  .comp (.fork (source t) (address t)) (.atom .look)
def flipped (t:Ty) : Prog false (Input t) (Ty.a t) :=
  .tab (.comp (.atom .snd) (.comp (.atom .snd) (.atom .len))) (cell t)
def program (t:Ty) : Prog false (Input t) (Ty.a t) :=
  .ifz (.comp (.atom .snd) (.atom .fst))
    (.comp (.atom .snd) (.atom .snd)) (flipped t)

def index (N j:ℕ) : ℕ := (j/N)*N+(N-1-j%N)

theorem cell_run (t:Ty) (N flag j:ℕ) (bank:Tape t.T) :
  run (cell t) ((N,(flag,bank)),j)=⟨bank.look (index N j) t.blank,41,
    max 1 (max (j/N) (max ((j/N)*N) (max (N-1) (max (j%N) (max (N-1-j%N) (index N j)))))),True⟩ := by
  simp [cell,address,size,source,binary,index,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,max_assoc,max_comm,max_left_comm]

theorem flipped_value (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (flipped t) (N,(flag,bank))).val=
    Tape.tab bank.len (fun j=>bank.look (index N j) t.blank) := by
  change (Bill.tab bank.len t.blank (fun j=>run (cell t) ((N,(flag,bank)),j))).val=_
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab bank.len) (funext (fun j=>congrArg Bill.val (cell_run t N flag j bank)))

theorem flipped_work (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (flipped t) (N,(flag,bank))).work=45*bank.len+8 := by
  change 5+(Bill.tab bank.len t.blank (fun j=>run (cell t) ((N,(flag,bank)),j))).work+1=_
  rw [ModelEquivalenceInterpreter.tab_work]
  have cells:(fun j=>(run (cell t) ((N,(flag,bank)),j)).work)=fun _=>41:=by
    funext j;exact congrArg Bill.work (cell_run t N flag j bank)
  rw [cells];simp only [Finset.sum_const,Finset.card_range,smul_eq_mul];omega

theorem program_value (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (program t) (N,(flag,bank))).val=
    if flag=0 then bank else Tape.tab bank.len (fun j=>bank.look (index N j) t.blank) := by
  by_cases h:flag=0 <;>simp [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h,
    show (run (flipped t) (N,(flag,bank))).val=_ from flipped_value t N flag bank]

theorem lookup (t:Ty) (N flag:ℕ) (bank:Tape t.T) (j:Fin bank.len) :
  (run (program t) (N,(flag,bank))).val.look j.val t.blank=
    bank.look (if flag=0 then j.val else index N j.val) t.blank := by
  rw [program_value]
  by_cases h:flag=0
  · simp only [h,↓reduceIte]
  · simp only [h,↓reduceIte]
    simp only [Tape.look,Tape.tab,j.isLt,↓reduceDIte]

theorem length (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (program t) (N,(flag,bank))).val.len=bank.len := by
  rw [program_value];split <;>rfl

theorem work (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (program t) (N,(flag,bank))).work≤45*bank.len+12 := by
  by_cases h:flag=0
  · simp [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h]
  · simp only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h,↓reduceIte]
    change 3+(run (flipped t) (N,(flag,bank))).work+1≤_
    rw [flipped_work];omega

theorem valid (t:Ty) (N flag:ℕ) (bank:Tape t.T) :
  (run (program t) (N,(flag,bank))).valid := by
  have good:(run (flipped t) (N,(flag,bank))).valid:=by
    change (True ∧ (True ∧ True)) ∧ (Bill.tab bank.len t.blank
      (fun j=>run (cell t) ((N,(flag,bank)),j))).valid
    refine ⟨⟨trivial,trivial,trivial⟩,(ModelEquivalenceInterpreter.tab_valid _ _ _).2 ?_⟩
    intro j _;rw [cell_run];trivial
  by_cases h:flag=0
  · simp [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h]
  · simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h,↓reduceIte,
      true_and] using good

theorem index_lt (N L j:ℕ) (pos:0<N) (multiple:N∣L) (live:j<L) : index N j<L := by
  obtain ⟨G,rfl⟩:=multiple
  have group:j/N<G:=Nat.div_lt_of_lt_mul live
  have rem:=Nat.mod_lt j pos
  have block: j/N*N+N≤N*G:=by nlinarith
  unfold index
  omega

theorem index_involution (N j:ℕ) (pos:0<N) : index N (index N j)=j := by
  have rem:=Nat.mod_lt j pos
  have complement:N-1-j%N<N:=by omega
  have div:index N j/N=j/N:=by
    unfold index
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ pos, Nat.div_eq_of_lt complement]
    omega
  have mod:index N j%N=N-1-j%N:=by
    unfold index
    rw [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt complement,Nat.mod_eq_of_lt complement]
  rw [index,div,mod]
  have parts:=Nat.mod_add_div j N
  rw [Nat.mul_comm (j/N) N]
  omega

theorem peak (t:Ty) (N flag:ℕ) (bank:Tape t.T) (pos:0<N) (multiple:N∣bank.len) :
  (run (program t) (N,(flag,bank))).peak≤bank.len+N+1 := by
  have cells:(Finset.range bank.len).sup
    (fun j=>(run (cell t) ((N,(flag,bank)),j)).peak)≤bank.len+N+1:=by
    apply Finset.sup_le
    intro j hj
    have live:=Finset.mem_range.mp hj
    have bound:=index_lt N bank.len j pos multiple live
    have product: j/N*N≤j:=Nat.div_mul_le_self _ _
    have div:=Nat.div_le_self j N
    have rem:=Nat.mod_lt j pos
    rw [cell_run];dsimp only [Bill.peak]
    omega
  have fp:(run (flipped t) (N,(flag,bank))).peak≤bank.len+N+1:=by
    rw [flipped,DFTModelResidualPeakSyntax.tab]
    simp only [run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word]
    simp only [zero_max,max_zero]
    change max bank.len (max bank.len ((Finset.range bank.len).sup
      (fun j=>(run (cell t) ((N,(flag,bank)),j)).peak)))≤_
    omega
  by_cases h:flag=0
  · simp [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h]
  · simpa only [program,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,h,↓reduceIte,
      zero_max,max_zero] using fp

end
end ExactFourierCircuits.DFTModelSavingResidualFlip
