import JSP000404Research.CutMergedTwoBadOldPaletteRigidity
import Mathlib.Tactic

/-!
# Three common interior bands in the two-bad branch

Each bad minimum saturates the old one-layer bound.  Since its exponent is
n-3, its old cut palette has exactly four colours.

A saturation-bad palette never contains both boundary colours 0 and n, so
after deleting those two possible boundary representatives at least three
interior colours remain.

The old-palette pullback theorem shows that the two bad minima agree on every
interior colour.  Hence they possess one common interior palette of cardinality
at least three.
-/

namespace JSP000404Research

open BinaryEdgePartition

def interiorCutPalette
    {n : ℕ}
    (S : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  (S.erase (0 : Fin (n + 1))).erase (Fin.last n)

theorem mem_interiorCutPalette_iff
    {n : ℕ}
    (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1)))
    (a : Fin (n + 1)) :
    a ∈ interiorCutPalette S
      ↔
    a ∈ S ∧ 0 < a.val ∧ a.val < n := by
  classical
  unfold interiorCutPalette
  simp only [Finset.mem_erase]
  constructor
  · intro h
    rcases h with ⟨haLast, haZero, haS⟩
    refine ⟨haS, ?_, ?_⟩
    · by_contra h0
      have hav : a.val = 0 := by omega
      have ha : a = (0 : Fin (n + 1)) := Fin.ext hav
      exact haZero ha
    · by_contra hN
      have hale : a.val ≤ n := by omega
      have hav : a.val = n := by omega
      have ha : a = Fin.last n := by
        apply Fin.ext
        simpa using hav
      exact haLast ha
  · rintro ⟨haS, ha0, haN⟩
    refine ⟨?_, ?_, haS⟩
    · intro ha
      have hav := congrArg Fin.val ha
      simp at hav
      omega
    · intro ha
      have hav := congrArg Fin.val ha
      simp at hav
      omega

theorem interiorCutPalette_eq_of_interior_membership
    {n : ℕ}
    (hn : 1 ≤ n)
    (S T : Finset (Fin (n + 1)))
    (h :
      ∀ a : Fin (n + 1),
        0 < a.val → a.val < n →
        (a ∈ S ↔ a ∈ T)) :
    interiorCutPalette S = interiorCutPalette T := by
  classical
  ext a
  rw [mem_interiorCutPalette_iff hn,
      mem_interiorCutPalette_iff hn]
  constructor
  · rintro ⟨haS, ha0, haN⟩
    exact ⟨(h a ha0 haN).mp haS, ha0, haN⟩
  · rintro ⟨haT, ha0, haN⟩
    exact ⟨(h a ha0 haN).mpr haT, ha0, haN⟩

/-- A four-colour old palette which does not contain both 0 and n retains at
least three colours after deleting the two boundary representatives. -/
theorem interiorCutPalette_card_ge_three_of_card_four
    {n : ℕ}
    (hn : 1 ≤ n)
    (S : Finset (Fin (n + 1)))
    (hcard : S.card = 4)
    (hboundary :
      ¬ ((0 : Fin (n + 1)) ∈ S ∧ Fin.last n ∈ S)) :
    3 ≤ (interiorCutPalette S).card := by
  classical
  have hzeroLast :
      (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  by_cases h0 : (0 : Fin (n + 1)) ∈ S
  · have hnS : Fin.last n ∉ S := by
      intro hN
      exact hboundary ⟨h0, hN⟩
    have hnErase :
        Fin.last n ∉ S.erase (0 : Fin (n + 1)) := by
      simp [hnS]
    unfold interiorCutPalette
    rw [Finset.erase_eq_of_not_mem hnErase,
        Finset.card_erase_of_mem h0,
        hcard]
    omega
  · by_cases hnS : Fin.last n ∈ S
    · have h0Erase :
          (0 : Fin (n + 1)) ∉ S := h0
      unfold interiorCutPalette
      rw [Finset.erase_eq_of_not_mem h0Erase]
      rw [Finset.card_erase_of_mem hnS, hcard]
      omega
    · unfold interiorCutPalette
      rw [Finset.erase_eq_of_not_mem h0,
          Finset.erase_eq_of_not_mem hnS,
          hcard]
      omega

theorem uncovered_cut_two_bad_common_interior_palette
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {lam t delta c : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c)
    (hcpi : c < Real.pi)
    (hcardV : Fintype.card V = 6)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hTopExp :
      centreExponent (C top) t = n - 1)
    (hMinExp :
      ∀ v : V, v ≠ top →
        centreExponent (C v) t = n - 3)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (hTopSafe :
      ¬ CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi top)
    (hBad₁ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₁)
    (hBad₂ :
      CutSaturationBadAt
          hp hcap C htpos hlam ht hdelta0
          (by linarith : delta < 1)
          hc0 hcpi bad₂)
    (hOtherSafe :
      ∀ v : V,
        v ≠ top → v ≠ bad₁ → v ≠ bad₂ →
        ¬ CutSaturationBadAt
            hp hcap C htpos hlam ht hdelta0
            (by linarith : delta < 1)
            hc0 hcpi v) :
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]
      push_cast
      linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htop
    interiorCutPalette (active P bad₁) =
        interiorCutPalette (active P bad₂)
      ∧
    3 ≤
      (interiorCutPalette (active P bad₁)).card := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let P :=
    cutProjectiveBandPartition
      hp hcap htpos hlam hc0 hcpi n htop
  let exponent : V → ℕ :=
    fun i => centreExponent (C i) t

  have hrel :=
    uncovered_cut_two_bad_old_palettes_differ_only_boundary
      hp hcap C hn5 htpos hlam ht
      hdelta0 hdeltaHalf hc0 hcpi hcardV
      top bad₁ bad₂ htb₁ htb₂ hb₁₂
      hTopExp hMinExp huncovered
      hTopSafe hBad₁ hBad₂ hOtherSafe

  have hEqInterior :
      interiorCutPalette (active P bad₁) =
        interiorCutPalette (active P bad₂) :=
    interiorCutPalette_eq_of_interior_membership
      (by omega : 1 ≤ n)
      (active P bad₁) (active P bad₂) hrel.1

  have hBad₁' :
      SaturationCollisionFailure P exponent bad₁ := by
    simpa [CutSaturationBadAt, P, exponent, htop] using hBad₁

  have hExp₁ :
      exponent bad₁ = n - 3 := by
    dsimp [exponent]
    exact hMinExp bad₁ htb₁.symm

  have hCard₁ :
      (active P bad₁).card = 4 := by
    rw [hBad₁'.1, hExp₁]
    omega

  have hInteriorCard :
      3 ≤
        (interiorCutPalette (active P bad₁)).card :=
    interiorCutPalette_card_ge_three_of_card_four
      (by omega : 1 ≤ n)
      (active P bad₁) hCard₁ hBad₁'.2

  exact ⟨hEqInterior, hInteriorCard⟩

#print axioms mem_interiorCutPalette_iff
#print axioms interiorCutPalette_card_ge_three_of_card_four
#print axioms uncovered_cut_two_bad_common_interior_palette

end JSP000404Research
