import JSP000404Research.FourCentreSharpTerminal
import JSP000404Research.FourCentreArithmetic
import JSP000404Research.CentreExponentBounds
import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

namespace JSP000404Research

open Real

theorem exists_fourth_fin_four
    (s a b : Fin 4)
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) :
    ∃ c : Fin 4, c ≠ s ∧ c ≠ a ∧ c ≠ b := by
  classical
  let S0 : Finset (Fin 4) := Finset.univ.erase s
  let S1 : Finset (Fin 4) := S0.erase a
  let S2 : Finset (Fin 4) := S1.erase b
  have hs : s ∈ (Finset.univ : Finset (Fin 4)) := by simp
  have ha0 : a ∈ S0 := by
    simp [S0, hsa.symm]
  have hb1 : b ∈ S1 := by
    simp [S1, S0, hsb.symm, hab.symm]
  have hcard0 : S0.card = 3 := by
    change ((Finset.univ : Finset (Fin 4)).erase s).card = 3
    rw [Finset.card_erase_of_mem hs]
    simp
  have hcard1 : S1.card = 2 := by
    change (S0.erase a).card = 2
    rw [Finset.card_erase_of_mem ha0, hcard0]
  have hcard2 : S2.card = 1 := by
    change (S1.erase b).card = 1
    rw [Finset.card_erase_of_mem hb1, hcard1]
  have hne : S2.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hne
  have hc' : c ≠ b ∧ c ≠ a ∧ c ≠ s := by
    simpa [S2, S1, S0] using hc
  exact ⟨c, hc'.2.2, hc'.2.1, hc'.1⟩

theorem four_centre_dyadic_capacity
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : Fin 4, CentreProjectiveCycle hp i) :
    (∑ i : Fin 4, 2 ^ centreExponent (C i) t) ≤ 2 ^ n := by
  have hdelta1 : delta < 1 := by linarith
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  let k : Fin 4 → ℕ := fun i => centreExponent (C i) t
  have hk : ∀ i, k i < n := by
    intro i
    exact centreExponent_lt_n
      (C i) n delta t (by omega) hdelta0 hdelta1 ht
  have htop :
      ∀ {a b : Fin 4}, a ≠ b →
        ¬ (k a = n - 1 ∧ k b = n - 1) := by
    intro a b hab hboth
    obtain ⟨c, hca, hcb⟩ :=
      Fin.exists_ne_and_ne_of_two_lt a b (by omega : 2 < 4)
    have haSharp :=
      concrete_unit_deficit_is_sharp
        hp hcap (by omega : 2 ≤ n)
        hdelta0 hdelta1 ht hlam
        a (C a) (by simpa [k] using hboth.1)
    have hbSharp :=
      concrete_unit_deficit_is_sharp
        hp hcap (by omega : 2 ≤ n)
        hdelta0 hdelta1 ht hlam
        b (C b) (by simpa [k] using hboth.2)
    exact two_sharp_no_third_small_delta
      hp hcap hdeltaHalf hlampos
      hab hca.symm hcb.symm
      haSharp hbSharp
  have hnext :
      ∀ {s a b : Fin 4},
        s ≠ a → s ≠ b → a ≠ b →
        k s = n - 1 →
        ¬ (k a = n - 2 ∧ k b = n - 2) := by
    intro s a b hsa hsb hab hs habnext
    obtain ⟨c, hcs, hca, hcb⟩ :=
      exists_fourth_fin_four s a b hsa hsb hab
    exact no_sharp_with_two_deficit_two_fin_four
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
