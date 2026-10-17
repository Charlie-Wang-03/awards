import JSP000404Research.ThreeCentreTerminal
import JSP000404Research.GenericTopExponentMultiplicity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Genuine three-centre lower-branch dyadic capacity for ANY finite order

No new geometry is assumed: top exponent uniqueness on the original
arbitrary finite type and the separately verified three-term dyadic bound
suffice. A Fin 3 equivalence enumerates only the SUM; centre cycles
remain the originally supplied ones.
-/

namespace JSP000404Research

theorem three_centre_card_three_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 3)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let e : Fin 3 ≃ V :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  let k : Fin 3 → ℕ := fun i => centreExponent (C (e i)) t
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : Fin 3, k i < n := by
    intro i
    exact centreExponent_lt_n
      (C (e i)) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have htopCard :
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 :=
    generic_topExponent_filter_card_le_one
      hp hcap (by omega : 3 ≤ Fintype.card V)
      hn hdelta0 hdeltaHalf ht hlam C
  have hpairs :
      ∀ {a b : Fin 3}, a ≠ b →
        ¬ (k a = n - 1 ∧ k b = n - 1) := by
    intro a b hab hboth
    have hEq : e a = e b :=
      Finset.card_le_one.mp htopCard (e a)
        (by simp [k] at hboth ⊢; exact hboth.1)
        (e b)
        (by simp [k] at hboth ⊢; exact hboth.2)
    exact hab (e.injective hEq)
  have hterms :=
    three_dyadic_terms_le_of_at_most_one_top
      hn (hk 0) (hk 1) (hk 2)
      (hpairs (by decide)) (hpairs (by decide))
      (hpairs (by decide))
  have hsum :
      (∑ i : Fin 3, 2 ^ k i) =
        (∑ v : V, 2 ^ centreExponent (C v) t) := by
    refine Fintype.sum_equiv e _ _ ?_
    intro i
    rfl
  rw [← hsum]
  simpa [k, Fin.sum_univ_succ, add_assoc] using hterms

#print axioms three_centre_card_three_dyadic_capacity

end JSP000404Research
