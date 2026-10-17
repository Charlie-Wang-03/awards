import JSP000404Research.FourCentreArithmetic
import JSP000404Research.NoTopTwoNextMultiplicity
import JSP000404Research.GenericTopExponentMultiplicity
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Full genuine planar Fin4 lower-branch dyadic capacity

The four-centre theorem now depends only on the verified arbitrary-finite
top multiplicity, the actual top-plus-two-next exclusion, and the independently
verified four-term dyadic arithmetic bound. It no longer imports the legacy
inside/outside mixed terminal nor treats any conditional payment as available.

This is a REAL theorem for four original planar points, but is not the
unrestricted JSP-000404 global six-source proof.
-/

namespace JSP000404Research

open Real

theorem exists_fourth_fin_four
    (s a b : Fin 4)
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) :
    ∃ c : Fin 4, c ≠ s ∧ c ≠ a ∧ c ≠ b := by
  obtain ⟨c, hsc, hac, hbc⟩ :=
    exists_fourth_of_card_ge_four
      (by decide : 4 ≤ Fintype.card (Fin 4))
      hsa hsb hab
  exact ⟨c, hsc.symm, hac.symm, hbc.symm⟩

theorem four_centre_dyadic_capacity
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin 4, CentreProjectiveCycle hp i) :
    (∑ i : Fin 4, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  let k : Fin 4 → ℕ := fun i => centreExponent (C i) t
  have hk : ∀ i, k i < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t (by omega : 1 ≤ n)
      hdelta0 hdelta1 ht
  have htopCard :
      ((Finset.univ : Finset (Fin 4)).filter
        (fun i => k i = n - 1)).card ≤ 1 := by
    simpa only [k] using
      (generic_topExponent_filter_card_le_one
        hp hcap
        (by decide : 3 ≤ Fintype.card (Fin 4))
        (by omega : 2 ≤ n)
        hdelta0 hdeltaHalf ht hlam C)
  have htop :
      ∀ {a b : Fin 4}, a ≠ b →
        ¬ (k a = n - 1 ∧ k b = n - 1) := by
    intro a b hab hboth
    have habEq : a = b :=
      Finset.card_le_one.mp htopCard a
        (by simp [hboth.1])
        b (by simp [hboth.2])
    exact hab habEq
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
      hsa hsb hcs.symm hab hca.symm hcb.symm
      (C s) (C a) (C b)
      (by simpa [k] using hs)
      (by simpa [k] using habnext.1)
      (by simpa [k] using habnext.2)
  have hfour :=
    four_dyadic_terms_le_of_sharp_structure
      hn k hk htop hnext
  simpa [k, Fin.sum_univ_succ] using hfour

#print axioms exists_fourth_fin_four
#print axioms four_centre_dyadic_capacity

end JSP000404Research
