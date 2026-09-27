import JSP000404Research.BoundaryCutShift
import JSP000404Research.CutTransitionSeedCriticalSlot
import JSP000404Research.CutProjectiveBandOccupancy
import Mathlib.Tactic

/-!
# Uncovered phases give a coherent Boolean bit on the merged boundary bands

Fix a partition cut c.  Its two colours to be merged are 0 and n.  Move to
the associated short cut cS from BoundaryCutShift.  Every ray in old colour
0 or n then has short-cut normalized coordinate in [0,1+delta].

If one vertex had two boundary rays with different short-cut signs, those two
rays would form a short cut-transition seed.  CutTransitionSeedCriticalSlot
would produce a canonical cyclic q=1 obstruction at the short-cut phase.
BoundaryCutShift identifies that phase with the original partition phase
x=t*c/pi, modulo one full period.

Therefore at any partition phase uncovered by every canonical critical unit
slot, all boundary rays at a fixed vertex share one short-cut sign.  Use that
sign as the merged boundary bit.  Edge reversal flips the short-cut sign, so
the resulting vertex bits separate every edge of old colour 0 or n.
-/

namespace JSP000404Research

def CutBoundaryRay
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t c : ℝ}
    (ht : 0 < t)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (n : ℕ)
    (htop : t < (n + 1 : ℕ))
    (i : V) (j : OtherVertex i) : Prop :=
  let b :=
    cutProjectiveBandColor hp ht hc0 hcpi n htop i j.1
  b.val = 0 ∨ b.val = n

theorem cutBoundaryRay_short_mem
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) (j : OtherVertex i)
    (hj :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i j) :
    0 ≤
        cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j
      ∧
    cutNormalizedRayTheta hp t
          (boundaryShortCut t delta c) i j
      ≤ 1 + delta := by
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let b :=
    cutProjectiveBandColor hp htpos hc0 hcpi n htop i j.1
  have hmem :
      RayInCutProjectiveBand hp t c i j b := by
    exact cutProjectiveBandColor_mem_lower
      hp htpos hc0 hcpi n htop j.2.symm
  change b.val = 0 ∨ b.val = n at hj
  rcases hj with hb0 | hbn
  · have beq : b = (0 : Fin (n + 1)) := Fin.ext hb0
    subst b
    have hband :
        0 ≤ cutNormalizedRayTheta hp t c i j ∧
        cutNormalizedRayTheta hp t c i j < 1 := by
      simpa [RayInCutProjectiveBand] using hmem
    exact boundaryShort_mem_of_band_zero
      hp hn htpos ht hdelta0 hc0 hcpi i j hband
  · have beq : b = Fin.last n := by
      apply Fin.ext
      simpa using hbn
    subst b
    have hband :
        (n : ℝ) ≤ cutNormalizedRayTheta hp t c i j ∧
        cutNormalizedRayTheta hp t c i j < (n : ℝ) + 1 := by
      simpa [RayInCutProjectiveBand] using hmem
    exact boundaryShort_mem_of_band_last
      hp hn htpos ht hdelta0 hc0 hcpi i j hband

/-- At an uncovered partition phase, any two boundary rays at one vertex have
the same short-cut sign. -/
theorem cutBoundaryRay_shortSign_eq_of_uncovered
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (i : V)
    {j k : OtherVertex i}
    (hj :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i j)
    (hk :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i k) :
    cutRaySign hp (boundaryShortCut t delta c) i j =
      cutRaySign hp (boundaryShortCut t delta c) i k := by
  by_cases hjk : j = k
  · subst k
    rfl
  by_contra hsign
  have hdelta1 : delta < 1 := by linarith
  have hjArc :=
    cutBoundaryRay_short_mem
      hp hn htpos ht hdelta0 hdelta1 hc0 hcpi i j hj
  have hkArc :=
    cutBoundaryRay_short_mem
      hp hn htpos ht hdelta0 hdelta1 hc0 hcpi i k hk
  have hcS0 :
      0 ≤ boundaryShortCut t delta c :=
    boundaryShortCut_nonneg
      hn ht hdelta0 hc0 hcpi
  have hcSpi :
      boundaryShortCut t delta c < Real.pi :=
    boundaryShortCut_lt_pi
      hn ht hdelta0 hc0 hcpi
  obtain ⟨u, _hui, hubad⟩ :=
    cut_transition_seed_has_cyclic_critical_slot
      hp hcap C htpos hlam hdeltaHalf
      hcS0 hcSpi i hjk hsign hjArc hkArc
  rcases boundaryShort_phase_eq_or_add_period
      hn htpos ht hdelta0 hc0 hcpi with hphase | hphase
  · rw [hphase] at hubad
    exact huncovered u hubad
  · rw [hphase] at hubad
    exact huncovered u
      (globalCyclicCriticalUnitBadAt_sub_period
        C u (t * c / Real.pi) hubad)

noncomputable def cutBoundaryWrapBit
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    {t delta c : ℝ}
    (n : ℕ)
    (htpos : 0 < t)
    (htop : t < (n + 1 : ℕ))
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (i : V) : Bool :=
  if h :
      ∃ j : OtherVertex i,
        CutBoundaryRay hp htpos hc0 hcpi n htop i j
  then
    cutRaySign hp (boundaryShortCut t delta c) i h.choose
  else false

theorem cutBoundaryWrapBit_eq_shortSign
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi))
    (i : V) (j : OtherVertex i)
    (hj :
      CutBoundaryRay hp htpos hc0 hcpi n
        (by rw [ht]; push_cast; linarith) i j) :
    cutBoundaryWrapBit hp n htpos
        (by rw [ht]; push_cast; linarith)
        hc0 hcpi i
      =
    cutRaySign hp (boundaryShortCut t delta c) i j := by
  unfold cutBoundaryWrapBit
  split_ifs with h
  · exact cutBoundaryRay_shortSign_eq_of_uncovered
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered i h.choose_spec hj
  · exact False.elim (h ⟨j, hj⟩)

/-- The coherent short-cut boundary bit separates every edge of old colour
0 or n in the partition at c. -/
theorem cutBoundaryWrapBit_separates
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (C : ∀ v : V, CentreProjectiveCycle hp v)
    {lam t delta c : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (htpos : 0 < t)
    (hlam : lam = Real.pi / t)
    (ht : t = (n : ℝ) + delta)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hc0 : 0 ≤ c) (hcpi : c < Real.pi)
    (huncovered :
      ∀ u : GlobalUnitGapSlot C t,
        ¬ GlobalCyclicCriticalUnitBadAt
            C t delta u (t * c / Real.pi)) :
    let htop : t < (n + 1 : ℕ) := by
      rw [ht]; push_cast; linarith
    let P :=
      cutProjectiveBandPartition
        hp hcap htpos hlam hc0 hcpi n htop
    let wrapBit :=
      cutBoundaryWrapBit hp n htpos htop hc0 hcpi
    ∀ {u v : V}, u < v →
      ((P.edgeColor u v).val = 0 ∨
        (P.edgeColor u v).val = n) →
      wrapBit u ≠ wrapBit v := by
  dsimp only
  intro u v huv hboundary
  let htop : t < (n + 1 : ℕ) := by
    rw [ht]
    push_cast
    linarith
  let uv : OtherVertex u := ⟨v, ne_of_gt huv⟩
  let vu : OtherVertex v := ⟨u, ne_of_lt huv⟩
  have huvRay :
      CutBoundaryRay hp htpos hc0 hcpi n htop u uv := by
    change
      (cutProjectiveBandColor
        hp htpos hc0 hcpi n htop u v).val = 0 ∨
      (cutProjectiveBandColor
        hp htpos hc0 hcpi n htop u v).val = n
    simpa [cutProjectiveBandPartition] using hboundary
  have hvuRay :
      CutBoundaryRay hp htpos hc0 hcpi n htop v vu := by
    change
      (cutProjectiveBandColor
        hp htpos hc0 hcpi n htop v u).val = 0 ∨
      (cutProjectiveBandColor
        hp htpos hc0 hcpi n htop v u).val = n
    rw [← cutProjectiveBandColor_symm
      hp htpos hc0 hcpi n htop (ne_of_lt huv)]
    simpa [cutProjectiveBandPartition] using hboundary
  have huBit :=
    cutBoundaryWrapBit_eq_shortSign
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered u uv huvRay
  have hvBit :=
    cutBoundaryWrapBit_eq_shortSign
      hp hcap C hn htpos hlam ht hdelta0 hdeltaHalf
      hc0 hcpi huncovered v vu hvuRay
  have hrev :
      cutRaySign hp (boundaryShortCut t delta c) v vu =
        !cutRaySign hp (boundaryShortCut t delta c) u uv :=
    cutRaySign_reverse_eq_not
      hp (boundaryShortCut t delta c) (ne_of_lt huv)
  rw [huBit, hvBit, hrev]
  cases h : cutRaySign hp (boundaryShortCut t delta c) u uv <;> decide

#print axioms cutBoundaryRay_short_mem
#print axioms cutBoundaryRay_shortSign_eq_of_uncovered
#print axioms cutBoundaryWrapBit_eq_shortSign
#print axioms cutBoundaryWrapBit_separates

end JSP000404Research
