import UniformRecursiveSavingExecution
set_option autoImplicit false
namespace ExactFourierCircuits.UniformRecursiveAdjacent
open UniformRecursiveSavingProgram
lemma adjacent {α:Type*}[DecidableEq α](s:α→ℕ)(before:List α)(a b:α)(after:List α)
 (ha:a∉before)(hb:b∉before)(ne:a≠b):
 offset s (before++a::b::after) a+s a=offset s (before++a::b::after) b:=by
 induction before with
 | nil=>simp [offset,ne]
 | cons c cs ih=>
   have ac:c≠a:=by intro h;subst c;exact ha (by simp)
   have bc:c≠b:=by intro h;subst c;exact hb (by simp)
   have h:=ih (fun h=>ha (List.mem_cons_of_mem _ h)) (fun h=>hb (List.mem_cons_of_mem _ h))
   simp only [List.cons_append,offset,ac,bc,ite_false]
   omega

def pre:List Part:=[.entry,.rootAllocate,.readyEntry,.smallSetup,.base,.largeSetup,.seedPrinter,
 .unitSetup,.unitPrinter,.nodeReady,.loop,.reader,.dispatch,.residualMark,.residualInit,.gather]
def post:List Part:=[.call,.inverseTest,.inverseSetup,.inverse,.scatterSetup,.scatter,.directionNext,
 .directionTest,.edgeDone,.recordAdvance,.scalar,.translation,.exchange,.marker,
 .paddingInit,.paddingTest,.paddingPatch,.paddingReader,.paddingNext,.paddingFinish,
 .spectatorSetup,.spectator,.finish,.returnSite,.restored,.halt,.orientation,.yRestore]
lemma adjacent_function {α:Type*}[DecidableEq α](s:α→ℕ)(addr:α→ℕ)
 (ls before:List α)(a b:α)(after:List α)
 (link:∀z,addr z=offset s ls z) (ord:ls=before++a::b::after)
 (ha:a∉before)(hb:b∉before)(ne:a≠b):addr a+s a=addr b:=by
 rw [link a,link b,ord]
 exact adjacent s before a b after ha hb ne
lemma boot_after:address .bootGroups+5=address .groupTest:=by
 have h:=adjacent_function size address order pre .bootGroups .groupTest post
  (fun _=>rfl) rfl (by decide) (by decide) (by decide)
 simpa only [show size .bootGroups=5 from rfl] using h
end ExactFourierCircuits.UniformRecursiveAdjacent
