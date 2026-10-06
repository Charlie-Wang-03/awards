import JSP000404Research.RetainedCompletionCore

/-!
# Lightweight pair-local Boolean hole sets

These definitions are used by local flip / blocker arguments and should not
inherit the global Hall-accounting dependency graph.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def pairLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    (retainedCompletionWords C u ∪
      retainedCompletionWords C v)

noncomputable def vertexLocalHoles
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) :
    Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)) \
    retainedCompletionWords C v

end OrderedEdgeColoring
end JSP000404Research
