import UniformSmallAxisFourierMachine
import UniformNewtonTableMachine
set_option autoImplicit false
namespace ExactFourierCircuits.UniformSmallAxisFourierPreservation
open UniformMachine UniformAssembly
open UniformPairMachine (prepared)
open UniformTensorMonomialMachine (Op applyBlock readable peak BlockAt block_runs setPC)
open UniformInitialPreparation (ell len copyBase)
open UniformPermutationInversePreparation (Metadata)
open UniformSelectedAxisFiberPreparation (radices)
open UniformSmallAxisFourierMachine
noncomputable section
/-- Gather every actual fiber, run the22-instruction direct Fourier kernel on
all contiguous fibers, and scatter every full tagged Scalar back. -/
theorem execution {n B:ℕ} (hn:0<n) (i:Fin (ell n+1)) (A D E root:ℕ)
 (x:Fin n→ℂ) (s:State) (metadata:Metadata n s) (args:Args i.val A D E root s)
 (eta:ℂ) (v:Fin (len n)→Scalar)
 (source:∀z:Fin (len n),s.scalarHeap (A+z.val)=some (v z))
 (rootVal:s.scalarHeap root=some (prepared eta))
 (rootD:root<D∨D+len n≤root) (rootE:root<E∨E+len n≤root)
 (sepAD:A+len n≤D) (sepDE:D+len n≤E)
 (aBound:A+2*len n≤B) (eBound:E+len n≤B)
 (code:161≤B) (pc:s.pc=0) (bound:WordBound B s) : ∃u,
 BoundedExecution program n x B s
  (2*UniformAllTensorFibersCopyMachine.runtime n i+
   UniformAllTensorFibersCopyMachine.fibers n i*UniformHeapDirectBatch.arrayCost (radices n i)+22) u ∧
 (∀j:Fin (UniformAllTensorFibersCopyMachine.fibers n i),∀k:Fin (radices n i),∃a,
   u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=some a ∧
   a.value=∑t:Fin (radices n i),eta^(k.val*t.val)*
    (v (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))).value) ∧
 Metadata n u ∧u.natHeap=s.natHeap ∧u.outputs=s.outputs ∧u.rootOrders=s.rootOrders ∧
 (∀z,z<A∨A+len n≤z→z<D∨D+len n≤z→z<E∨E+len n≤z→u.scalarHeap z=s.scalarHeap z) := by
 have fs:UniformAllTensorFibersCopyMachine.FullSource false n A D s.scalarHeap:=by
  intro z hz;exact ⟨v ⟨z,hz⟩,source ⟨z,hz⟩⟩
 obtain ⟨g,gr,pg,mg,ag,zg,ga,go,ng,og,rg⟩:=gather_execution hn i A D E root x s metadata args fs
  sepAD (by omega) (by omega) code pc bound
 obtain ⟨b,br,pb,mb,ab,zb,width,count,bsource,bdest,broot,bf⟩:=batchSetup_execution i A D E root
  x g mg ag zg code pg gr.final_bound
 let bank:Fin (UniformAllTensorFibersCopyMachine.fibers n i)→Fin (radices n i)→Scalar:=
  fun j t=>v (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))
 have bs:UniformHeapDirectBatch.Source (radices n i) D bank b:=by
  intro j t
  rw [bf.2.1]
  have eq:=ga j.val j.isLt t.val t.isLt
  change g.scalarHeap (D+(j.val*radices n i+t.val))=s.scalarHeap
   (A+UniformAllTensorFibersCopyMachine.native n i j.val t.val) at eq
  rw [show UniformHeapDirectBatch.arrayBase D (radices n i) j.val+t.val=
    D+(j.val*radices n i+t.val) by simp [UniformHeapDirectBatch.arrayBase,Nat.add_assoc],eq]
  exact source (UniformAllTensorFibersCopyMachine.nativeEquiv n i (j,t))
 have rb:b.scalarHeap root=some (prepared eta):=by rw [bf.2.1,go root rootD,rootVal]
 let be:=setPC b 0
 obtain ⟨c,cr,ca,_,cf,_,_⟩:=UniformHeapDirectBatch.execution n B (radices n i)
  (UniformAllTensorFibersCopyMachine.fibers n i) D E root x be eta bank rfl width count bsource bdest broot
  rb bs (by simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using rootE)
  (Or.inl (by simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using sepDE))
  (by omega) (by rw [UniformAllTensorFibersCopyMachine.fibers_product];omega)
  (by rw [UniformAllTensorFibersCopyMachine.fibers_product];exact eBound)
  (changePC_bound B b 0 br.final_bound (by omega))
 have moved:=UniformBoundedAssembly.boundedExecution_placed batch_code
  (by rw [UniformHeapDirectBatch.program_length];omega) (by omega :102≤B) cr
 have bpeq:UniformAssembly.placed 68 be=b:=by change setPC b 68=b;unfold setPC;rw [←pb]
 rw [bpeq] at moved
 let m:=setPC c 102
 have fm:UniformHeapDirectBatch.Frame E (len n) b m:=by
  have ff:=(UniformHeapDirectBatch.Frame.pc E _ b 0).trans
    (cf.trans (UniformHeapDirectBatch.Frame.pc E _ c 102))
  simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using ff
 have mm:Metadata n m:=batch_metadata fm mb
 have am:Args i.val A D E root m:=Args.batch_frame fm ab
 have zm:m.natReg 4974=0:=(fm.natReg 4974 (by unfold UniformHeapDirectBatch.Changed;omega)).trans zb
 have sr:=scatterSetup_runs x m am zm code rfl moved.final_bound
 let ss:=applyBlock scatterSetup m
 have sp:ss.pc=105:=by rw [UniformTensorMonomialMachine.applyBlock_pc];rfl
 have sm:Metadata n ss:=(scatterSetup_frame m).metadata mm
 let se:=setPC ss 0
 have ep:=UniformAllTensorFibersCopyMachine.Frame.pc ss 0
 have seMeta:Metadata n se:=ep.metadata sm
 have seArgs:UniformAllTensorFibersCopyMachine.Args i.val A E se:=⟨(scatterSetup_args am zm).axis,
  (scatterSetup_args am zm).array,(scatterSetup_args am zm).bank⟩
 have fse:UniformAllTensorFibersCopyMachine.FullSource true n A E se.scalarHeap:=by
  intro z hz
  let p:Fin (UniformAllTensorFibersCopyMachine.fibers n i)×Fin (radices n i):=
    (UniformAllTensorFibersCopyMachine.packedEquiv n i).symm ⟨z,hz⟩
  have pe:UniformAllTensorFibersCopyMachine.packedEquiv n i p=⟨z,hz⟩:=
   (UniformAllTensorFibersCopyMachine.packedEquiv n i).apply_symm_apply ⟨z,hz⟩
  have pv:=congrArg Fin.val pe
  rw [UniformAllTensorFibersCopyMachine.packedEquiv_val] at pv
  change p.1.val*radices n i+p.2.val=z at pv
  obtain ⟨a,ha,_⟩:=ca p.1 p.2
  refine ⟨a,?_⟩
  change c.scalarHeap (E+z)=some a
  simpa only [UniformHeapDirectBatch.arrayBase,Nat.add_assoc,pv] using ha
 obtain ⟨u,ur,_,ua,uo,uf,um⟩:=UniformAllTensorFibersCopyMachine.execution hn true i A E B x se seMeta
  seArgs fse (by omega) aBound eBound (by omega) rfl
  (changePC_bound B ss 0 sr.final_bound (by omega))
 have smoved:=UniformBoundedAssembly.boundedExecution_placed scatter_code
  (by rw [UniformAllTensorFibersCopyMachine.program_length];omega) (by omega :160≤B) ur
 have seq:UniformAssembly.placed 105 se=ss:=by change setPC ss 105=ss;unfold setPC;rw [←sp]
 rw [seq] at smoved
 let final:=setPC u 160
 have halt:BoundedExecution program n x B final 1 final:=.halt smoved.final_bound
  (by simp [step,final,setPC,halt_code])
 refine ⟨final,?_,?_,(UniformAllTensorFibersCopyMachine.Frame.pc u 160).metadata um,?_,?_,?_,?_⟩
 · convert (((gr.trans br).trans moved).trans sr).trans smoved |>.executes halt using 1
   ring
 · intro j k
   obtain ⟨a,ha,hv⟩:=ca j k
   refine ⟨a,?_,hv⟩
   have copy:=ua j.val j.isLt k.val k.isLt
   change u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=
    c.scalarHeap (E+UniformAllTensorFibersCopyMachine.packed n i j.val k.val) at copy
   change u.scalarHeap (A+UniformAllTensorFibersCopyMachine.native n i j.val k.val)=some a
   rw [copy]
   simpa only [UniformHeapDirectBatch.arrayBase,UniformAllTensorFibersCopyMachine.packed,Nat.add_assoc] using ha
 · exact uf.natHeap.trans (fm.natHeap.trans (bf.1.trans ng))
 · exact uf.outputs.trans (fm.outputs.trans (bf.2.2.2.1.trans og))
 · exact uf.roots.trans (fm.roots.trans (bf.2.2.2.2.1.trans rg))
 · intro z za zd ze
   change u.scalarHeap z=s.scalarHeap z
   rw [uo z za]
   change c.scalarHeap z=s.scalarHeap z
   rw [cf.scalarHeap z (by simpa only [UniformAllTensorFibersCopyMachine.fibers_product] using ze)]
   change b.scalarHeap z=s.scalarHeap z
   rw [bf.2.1,go z zd]

def writesBelow (i:Instruction) : Bool := match i with
 | .natLiteral d _ | .length d | .natBinary _ d _ _ | .loadNat d _=>d<5000
 | _=>true
lemma relocate_below (b r:ℕ) (i:Instruction) : writesBelow (relocate b r i)=writesBelow i := by
 cases i <;> rfl
lemma copy_below (scatter:Bool) : (UniformAllTensorFibersCopyMachine.program scatter).all writesBelow=true := by
 cases scatter <;> decide
lemma batch_below : UniformHeapDirectBatch.program.all writesBelow=true := by decide
lemma program_below : program.all writesBelow=true := by
 simp only [program,List.all_append,List.all_map,Function.comp_def,relocate_below,copy_below,batch_below,
  Bool.and_true,Bool.true_and]
 decide
lemma keeps_nat (q:ℕ) (high:5000≤q) : ∀i∈program,UniformNewtonTableMachine.KeepsNat q i := by
 intro i hi
 have hb:=List.all_eq_true.mp program_below i hi
 cases i <;> simp only [UniformNewtonTableMachine.KeepsNat]
 all_goals intro eq
 all_goals subst_vars
 all_goals simp [writesBelow] at hb
 all_goals omega
/-- The outer small-axis loop owns registers5100+, retained by the actual161. -/
theorem execution_nat {n B t q:ℕ} {x:Fin n→ℂ} {s u:State}
 (run:BoundedExecution program n x B s t u) (high:5000≤q) : u.natReg q=s.natReg q :=
 UniformNewtonTableMachine.Executes.keeps_nat run.executes (keeps_nat q high)
end
end ExactFourierCircuits.UniformSmallAxisFourierPreservation
