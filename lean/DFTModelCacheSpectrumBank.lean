import DFTModelCacheSpectrumDFT

set_option autoImplicit false

/-! Fresh seven-block bank: powers followed by six prepared DFTs, in the
literal native shared-bank order. The final raw producer supplies the kernels. -/
namespace ExactFourierCircuits.DFTModelCacheSpectrumBank
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open scoped BigOperators
noncomputable section
attribute [local irreducible] DFTModelScalarPower.program DFTModelCacheSpectrumDFT.row

abbrev Input := p w (p sc (Ty.a (Ty.a sc)))
abbrev CellInput := p Input w
def integer {s : Ty} (op : NOp) (f g : Prog false s w) : Prog false s w :=
  .comp (.fork f g) (.atom (.int op))
def N : Prog false CellInput w := .comp (.atom .fst) (.atom .fst)
def root : Prog false CellInput sc :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .fst))
def kernels : Prog false CellInput (Ty.a (Ty.a sc)) :=
  .comp (.atom .fst) (.comp (.atom .snd) (.atom .snd))
def offset : Prog false CellInput w := integer .sub (.atom .snd) N
def slot : Prog false CellInput w := integer .div offset N
def frequency : Prog false CellInput w := integer .mod offset N
def kernel : Prog false CellInput (Ty.a sc) :=
  .comp (.fork kernels slot) (.atom .look)
def power : Prog false CellInput sc :=
  .comp (.fork (.atom .snd) root) DFTModelScalarPower.program
def argument : Prog false CellInput DFTModelCacheSpectrumDFT.RowInput :=
  .fork (.fork N (.fork root kernel)) frequency
def spectrum : Prog false CellInput sc := .comp argument DFTModelCacheSpectrumDFT.row
def test : Prog false CellInput w := integer .sub
  (integer .add (.atom .snd) (.atom (.lit 1))) N
def cell : Prog false CellInput sc := .ifz test power spectrum
def length : Prog false Input w := integer .mul (.atom .fst) (.atom (.lit 7))
def program : Prog false Input (Ty.a sc) := .tab length cell

theorem argument_run (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run argument ((n,(omega,ks)),j)=
      ⟨((n,(omega,ks.look ((j-n)/n) (Tape.empty ℂ))),(j-n)%n),
        45,j-n,True⟩ := by
  simp [argument,N,root,kernel,kernels,slot,offset,frequency,integer,
    run,Code.run,Atom.run,NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]
  have hd:=Nat.div_le_self (j-n) n
  have hm:=Nat.mod_le (j-n) n
  omega

theorem spectrum_run (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run spectrum ((n,(omega,ks)),j)=
      (run DFTModelCacheSpectrumDFT.row
        ((n,(omega,ks.look ((j-n)/n) (Tape.empty ℂ))),(j-n)%n)).pay 46 (j-n) := by
  change ((run argument ((n,(omega,ks)),j)).pass
    (run DFTModelCacheSpectrumDFT.row)).pay 1 0=_
  rw [argument_run]
  simp only [Bill.pass,Bill.pay]
  congr 1 <;> first | omega | simp

theorem power_run (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run power ((n,(omega,ks)),j)=
      (run DFTModelScalarPower.program (j,omega)).pay 8 0 := by
  simp [power,root,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  omega

attribute [local irreducible] power spectrum

theorem cell_run (n j : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run cell ((n,(omega,ks)),j)=
      (if j<n then run power ((n,(omega,ks)),j)
        else run spectrum ((n,(omega,ks)),j)).pay 12 (j+1) := by
  by_cases hj:j<n
  · have ht:j+1-n=0:=by omega
    simp [cell,test,integer,N,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,ht,hj,max_comm]
    omega
  · have ht:j+1-n≠0:=by omega
    simp [cell,test,integer,N,run,Code.run,Atom.run,NOp.run,
      Bill.pass,Bill.pay,Bill.one,Bill.word,ht,hj,max_comm]
    omega

theorem length_run (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run length (n,(omega,ks))=⟨7*n,5,max 7 (7*n),True⟩ := by
  simp [length,integer,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word,Nat.mul_comm]

theorem program_run (n : ℕ) (omega : ℂ) (ks : Tape (Tape ℂ)) :
    run program (n,(omega,ks))=
      (Bill.tab (7*n) (0:ℂ) (fun j=>run cell ((n,(omega,ks)),j))).pay 6 (max 7 (7*n)) := by
  change ((run length (n,(omega,ks))).pass (fun L=>
    Bill.tab L (0:ℂ) (fun j=>run cell ((n,(omega,ks)),j)))).pay 1 0=_
  rw [length_run]
  simp only [Bill.pass,Bill.pay]
  congr 1 <;> first | omega | simp

end
end ExactFourierCircuits.DFTModelCacheSpectrumBank
