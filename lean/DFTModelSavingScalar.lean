import DFTModelRecursiveScalarSource
import DFTModelRecursiveExchangeCore
import DFTModelResidualCore
import DFTModelRecursiveMetadata

set_option autoImplicit false

/-! Runtime decoding of the actual eight-field scalar record. Both affine
channels are updated by one fresh whole-bank tab, with original source reads. -/
namespace ExactFourierCircuits.DFTModelSavingScalar
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open DFTModelAffine DFTModelRecursiveScalarCore DFTModelClockControl
noncomputable section
namespace E
export DFTModelRecursiveExchange (Row Cell nat first second test readRole current)
end E

abbrev Input := p (Ty.a w) Node
abbrev Row := p sc E.Row
abbrev Cell := p Row w

def field (j : ℕ) : Prog false Input w :=
  .comp (.fork (.atom .fst) (.atom (.lit j))) (.atom .look)
def decodeTail : Prog false w sc :=
  .ifz (.atom .id) (.atom (.cz .scalar))
    (.comp DFTModelRecursiveMetadata.predecessor
      (.ifz (.atom .id) half (.atom .cone)))
def decode : Prog false w sc :=
  .ifz (.atom .id) (negative (.atom .cone))
    (.comp DFTModelRecursiveMetadata.predecessor
      (.ifz (.atom .id) (negative half)
        (.comp DFTModelRecursiveMetadata.predecessor decodeTail)))
def forget : Prog false Cell E.Cell :=
  .fork (.comp (.atom .fst) (.atom .snd)) (.atom .snd)
def coeff : Prog false Cell sc := .comp (.atom .fst) (.atom .fst)
def old : Prog false Cell Tagged := .comp forget E.current
def fromSource : Prog false Cell Tagged := .comp forget (E.readRole E.second)
def update : Prog false Cell Tagged := .comp (.fork coeff (.fork old fromSource)) operation
def cell : Prog false Cell Tagged :=
  .ifz (.comp forget (E.test E.first)) update old
def source : Prog false Row (Ty.a Tagged) :=
  .comp (.atom .snd) DFTModelRecursiveExchange.rowSource
def rows : Prog false Row (Ty.a Tagged) := .tab (.comp source (.atom .len)) cell
def bank : Prog false Input (Ty.a Tagged) := .comp (.atom .snd) (.atom .snd)
def setup (R : ℕ) : Prog false Input Row :=
  .fork (.comp (field 7) decode)
    (.fork (.fork (field 3) (field 4))
      (.fork (E.nat .div (.comp bank (.atom .len)) (.atom (.lit R))) bank))
def program (R : ℕ) : Prog false Input Node :=
  .fork (.comp (.atom .snd) (.atom .fst)) (.comp (setup R) rows)

theorem decode_value (c : Fin 5) :
    (run decode c.val).val=UniformFixedCoefficientCodec.decode c := by
  fin_cases c <;> norm_num [decode,decodeTail,DFTModelRecursiveMetadata.predecessor,
    half,two,negative,UniformFixedCoefficientCodec.decode,run,Code.run,Atom.run,NOp.run,
    Bill.pass,Bill.pay,Bill.one,Bill.word]

theorem field_run (j : ℕ) (raw : Tape ℕ) (node : Node.T) :
    run (field j) (raw,node)=⟨raw.look j 0,5,j,True⟩ := by
  simp [field,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem forget_run (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    run forget ((c,((d,s),(V,v))),j)=⟨(((d,s),(V,v)),j),5,0,True⟩ := by
  simp [forget,run,Code.run,Atom.run,Bill.pass,Bill.pay,Bill.one]

theorem old_run (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    run old ((c,((d,s),(V,v))),j)=⟨v.look j Tagged.blank,15,0,True⟩ := by
  rw [old,comp_run,forget_run]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelRecursiveExchange.current_run]
  simp

theorem fromSource_run (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    run fromSource ((c,((d,s),(V,v))),j)=
      ⟨v.look (s*V+j%V) Tagged.blank,39,s*V+j%V,True⟩ := by
  rw [fromSource,comp_run,forget_run]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelRecursiveExchange.readRole_run E.second d s V j s v
      (DFTModelRecursiveExchange.second_run _ _ _ _ _)]
  simp

theorem update_run (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    run update ((c,((d,s),(V,v))),j)=
      ⟨updated c (v.look j Tagged.blank) (v.look (s*V+j%V) Tagged.blank),
        if (v.look j Tagged.blank).1=0 then 131 else 129,
        max (s*V+j%V) (if (v.look j Tagged.blank).1=0 then 0 else 1),True⟩ := by
  rw [update,comp_run,fork_run,fork_run,old_run,fromSource_run]
  simp only [coeff,comp_run,atom_run,Atom.run,Bill.one,Bill.pass,Bill.pay]
  rw [operation_run]
  by_cases h:(v.look j Tagged.blank).1=0 <;> simp [h]

theorem test_run (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    run (.comp forget (E.test E.first)) ((c,((d,s),(V,v))),j)=
      ⟨j/V-d+(d-j/V),43,max (j/V) (j/V-d+(d-j/V)),True⟩ := by
  rw [comp_run,forget_run]
  simp only [Bill.pass,Bill.pay]
  rw [DFTModelRecursiveExchange.test_run E.first d s V j d v
    (DFTModelRecursiveExchange.first_run _ _ _ _ _)]
  simp

theorem cell_value (c : ℂ) (d s V j : ℕ) (v : Tape Tagged.T) :
    (run cell ((c,((d,s),(V,v))),j)).val=
      DFTModelRecursiveScalar.result d s V c v j := by
  rw [cell,ifz_run,test_run]
  have test:(j/V-d+(d-j/V)=0)↔j/V=d:=by omega
  simp only [Bill.pass,Bill.pay,test,DFTModelRecursiveScalar.result]
  split_ifs
  · rw [update_run]
  · rw [old_run]

theorem source_run (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    run source (c,((d,s),(V,v)))=⟨v,5,0,True⟩ := by
  simp [source,DFTModelRecursiveExchange.rowSource,run,Code.run,Atom.run,
    Bill.pass,Bill.pay,Bill.one]

attribute [local irreducible] cell

theorem rows_value (c : ℂ) (d s V : ℕ) (v : Tape Tagged.T) :
    (run rows (c,((d,s),(V,v)))).val=
      Tape.tab v.len (DFTModelRecursiveScalar.result d s V c v) := by
  rw [rows,DFTModelRecursiveScalar.tab_run,comp_run,source_run]
  simp only [atom_run,Atom.run,Bill.pass,Bill.pay,Bill.word]
  rw [ModelEquivalenceInterpreter.tab_value]
  exact congrArg (Tape.tab v.len) (funext (cell_value c d s V · v))

attribute [local irreducible] decode rows

theorem setup_value (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (setup R) (raw,((k,I),v))).val=
      ((run decode (raw.look 7 0)).val,((raw.look 3 0,raw.look 4 0),(v.len/R,v))) := by
  simp only [setup,comp_run,fork_run,field,bank,E.nat,atom_run,Atom.run,
    NOp.run,Bill.pass,Bill.pay,Bill.one,Bill.word,Ty.blank]

theorem program_value (R k : ℕ) (I : ℂ) (raw : Tape ℕ) (v : Tape Tagged.T) :
    (run (program R) (raw,((k,I),v))).val=
      ((k,I),Tape.tab v.len (DFTModelRecursiveScalar.result (raw.look 3 0)
        (raw.look 4 0) (v.len/R) (run decode (raw.look 7 0)).val v)) := by
  rw [program,fork_run]
  simp only [comp_run,atom_run,Atom.run,Bill.pass,Bill.pay,Bill.one]
  rw [setup_value,rows_value]

/-- Dynamic record fields are actually loaded before the frozen scalar
operation; they are not specialized host parameters. -/
theorem program_specialize (R k d src : ℕ) (I : ℂ) (raw : Tape ℕ)
    (v : Tape Tagged.T) (c : Fin 5)
    (dest:raw.look 3 0=d) (source:raw.look 4 0=src) (code:raw.look 7 0=c.val) :
    (run (program R) (raw,((k,I),v))).val=
      (run (DFTModelRecursiveScalar.program R d src c) ((k,I),v)).val := by
  rw [program_value,DFTModelRecursiveScalar.program_value,dest,source,code,decode_value]

/-- One actual/zero paired output identity after runtime header decoding. -/
theorem program_lookup {R V : ℕ} (d src : Fin R) (c : Fin 5)
    (positive:0<V) (f f0:Fin R→Fin V→UniformMachine.Scalar)
    (k:ℕ)(I:ℂ)(raw:Tape ℕ)
    (dest:raw.look 3 0=d.val)(source:raw.look 4 0=src.val)(code:raw.look 7 0=c.val)
    (i:Fin R)(j:Fin V) :
    (run (program R) (raw,((k,I),DFTModelRecursiveScalarSource.paired f f0))).val.2.look
      (i.val*V+j.val) Tagged.blank=
      encodePaired
        (UniformFixedNetworkShearChildMachine.shearValues d src
          (UniformFixedCoefficientCodec.decode c) f i j)
        (UniformFixedNetworkShearChildMachine.shearValues d src
          (UniformFixedCoefficientCodec.decode c) f0 i j) := by
  rw [program_specialize R k d.val src.val I raw _ c dest source code]
  exact DFTModelRecursiveScalarSource.program_lookup d src c positive f f0 k I i j


end
end ExactFourierCircuits.DFTModelSavingScalar
