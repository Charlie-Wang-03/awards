import JSP000404Research.FourCentreCapacity
import JSP000404Research.GenericTopExponentMultiplicity
import JSP000404Research.NoTopTwoNextMultiplicity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Genuine four-centre capacity on arbitrary finite linearly ordered domains

The fixed Fin4 proof depends only on the actual top and next-layer geometric
exclusions and dyadic arithmetic. This theorem works directly with the
ORIGINAL actual cycles C : forall i : V, CentreProjectiveCycle hp i for any
four-element linear order V. A finite equivalence is used to enumerate
the sum only; cycles and geometric data are NOT redefined or re-sorted.
No auxiliary six-source payment premise is assumed.
-/

namespace JSP000404Research

theorem four_centre_card_four_dyadic_capacity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard : Fintype.card V = 4)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    (∑ i : V, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  classical
  let e : Fin 4 ≃ V :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  let k : Fin 4 → ℕ := fun i => centreExponent (C (e i)) t
  have hdelta1 : delta < 1 := by linarith
  have hk : ∀ i : Fin 4, k i < n := by
    intro i
    exact centreExponent_lt_n
      (C (e i)) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have htopCard :
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 1)).card ≤ 1 :=
    generic_topExponent_filter_card_le_one
      hp hcap (by omega : 3 ≤ Fintype.card V)
      (by omega : 2 ≤ n)
      hdelta0 hdeltaHalf ht hlam C
  have htop :
      ∀ {a b : Fin 4}, a ≠ b →
        ¬ (k a = n - 1 ∧ k b = n - 1) := by
    intro a b hab hboth
    have habE : e a = e b :=
      Finset.card_le_one.mp htopCard (e a)
        (by simp [k] at hboth ⊢; exact hboth.1)
        (e b)
        (by simp [k] at hboth ⊢; exact hboth.2)
    exact hab (e.injective habE)
  have hnext :
      ∀ {s a b : Fin 4},
        s ≠ a → s ≠ b → a ≠ b →
        k s = n - 1 →
        ¬ (k a = n - 2 ∧ k b = n - 2) := by
    intro s a b hsa hsb hab hs habnext
    obtain ⟨c, hcs, hca, hcb⟩ :=
      exists_fourth_fin_four s a b hsa hsb hab
    exact no_top_and_two_next_with_fourth
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      (e.injective.ne hsa)
      (e.injective.ne hsb)
      (e.injective.ne hcs.symm)
      (e.injective.ne hab)
      (e.injective.ne hca.symm)
      (e.injective.ne hcb.symm)
      (C (e s)) (C (e a)) (C (e b))
      (by simpa [k] using hs)
      (by simpa [k] using habnext.1)
      (by simpa [k] using habnext.2)
  have hfour :=
    four_dyadic_terms_le_of_sharp_structure
      hn k hk htop hnext
  have hsum :
      (∑ i : Fin 4, 2 ^ k i) =
        (∑ v : V, 2 ^ centreExponent (C v) t) := by
    refine Fintype.sum_equiv e _ _ ?_
    intro i
    rfl
  rw [← hsum]
  simpa [k, Fin.sum_univ_succ, add_assoc] using hfour

#print axioms four_centre_card_four_dyadic_capacity

end JSP000404Research
