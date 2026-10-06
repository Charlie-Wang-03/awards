/-!
# Lightweight global-order extreme predicate

This file isolates the order-theoretic predicate used by the three-whole-cube
profile contradictions from the much heavier geometric theorem proving that
support-one projected-loss centres satisfy it.
-/

namespace JSP000404Research
namespace ProjectionOrdered

def GlobalOrderExtreme
    {V : Type*} [LinearOrder V]
    (i : V) : Prop :=
  (∀ w : V, w ≠ i → i < w) ∨
  (∀ w : V, w ≠ i → w < i)

end ProjectionOrdered
end JSP000404Research
