import JSP000404Research.OrdinaryCriticalUnitObstruction
import JSP000404Research.SixPointUnitGapSlots
import Mathlib.Tactic

/-!
# Half-grid obstruction for six-point ordinary critical unit phases

For n >= 5 we can avoid any measure-theoretic phase-cover argument.

Sample the normalized phase interval at

  0, 1/2, 1, 3/2, ..., n.

There are 2*n+1 >= 11 samples.  Every OrdinaryCriticalUnitBadAt interval has
width at most delta < 1/2, so a fixed unit-gap slot can contain at most one
sample.  But the six-point top + five-minimum terminal has at most ten global
unit-gap slots.

Therefore the ordinary critical obstruction family cannot hit every half-grid
sample.  This is a finite pigeonhole theorem, with no appeal to coverage of all
of R and no interval-measure API.
-/

namespace JSP000404Research

/-- Two phases carried by the same ordinary critical unit slot are at distance
at most delta. -/
theorem ordinaryCriticalUnitBadAt_pair_distance_le_delta
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (u : GlobalUnitGapSlot C t)
    {x y : ℝ}
    (hx : OrdinaryCriticalUnitBadAt C t delta u x)
    (hy : OrdinaryCriticalUnitBadAt C t delta u y) :
    |x - y| ≤ delta := by
  rcases hx with
    ⟨mx, hmx, hidxX, _htransX,
      hs1X, hsTopX, hxL, hxR⟩
  rcases hy with
    ⟨my, hmy, hidxY, _htransY,
      hs1Y, hsTopY, hyL, hyR⟩
  have hm : mx = my := by
    omega
  subst my
  have hproof : hmy = hmx := Subsingleton.elim _ _
  subst hmy
  let alpha :=
    normalizedRayTheta hp t u.1
      ((C u.1).rays.get ⟨mx, by omega⟩)
  let s :=
    t * ((rayThetaAt hp u.1
        ((C u.1).rays.get ⟨mx + 1, hmx⟩) -
      rayThetaAt hp u.1
        ((C u.1).rays.get ⟨mx, by omega⟩)) / Real.pi)
  have hwidth :
      criticalBadRight alpha delta -
          criticalBadLeft alpha s
        ≤ delta := by
    exact
      (critical_bad_width_bounds
        (alpha := alpha) (s := s) (delta := delta)
        (by
          have := hsTopX
          have := hs1X
          linarith)
        hs1X hsTopX).2
  have hxy :
      x - y ≤ delta := by
    have : x - y ≤
        criticalBadRight alpha delta -
          criticalBadLeft alpha s := by
      dsimp [alpha, s] at hxL hxR hyL hyR ⊢
      linarith
    linarith
  have hyx :
      y - x ≤ delta := by
    have : y - x ≤
        criticalBadRight alpha delta -
          criticalBadLeft alpha s := by
      dsimp [alpha, s] at hxL hxR hyL hyR ⊢
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Distinct half-grid points are separated by at least one half. -/
theorem halfGrid_separation
    {N : ℕ}
    {a b : Fin N}
    (hab : a ≠ b) :
    (1 : ℝ) / 2 ≤
      |((a.val : ℝ) / 2) - ((b.val : ℝ) / 2)| := by
  have habVal : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  rcases lt_or_gt_of_ne habVal with hlt | hgt
  · have hnat : a.val + 1 ≤ b.val := by omega
    have hreal : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by
      exact_mod_cast hnat
    rw [abs_of_nonpos]
    · linarith
    · norm_num
      exact_mod_cast hlt.le
  · have hnat : b.val + 1 ≤ a.val := by omega
    have hreal : (b.val : ℝ) + 1 ≤ (a.val : ℝ) := by
      exact_mod_cast hnat
    rw [abs_of_nonneg]
    · linarith
    · norm_num
      exact_mod_cast hgt.le

/-- At most one half-grid sample can lie in one critical unit obstruction. -/
theorem ordinaryCriticalUnitBadAt_halfGrid_injective
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t delta : ℝ)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    {N : ℕ}
    (slot : Fin N → GlobalUnitGapSlot C t)
    (hbad :
      ∀ r : Fin N,
        OrdinaryCriticalUnitBadAt C t delta
          (slot r) ((r.val : ℝ) / 2)) :
    Function.Injective slot := by
  intro a b habSlot
  by_contra hab
  have hsep := halfGrid_separation hab
  have hdist :=
    ordinaryCriticalUnitBadAt_pair_distance_le_delta
      C t delta (slot a)
      (hbad a)
      (by simpa [habSlot] using hbad b)
  linarith

/-- Six-point n>=5 terminal: not every half-grid phase can be carried by an
ordinary critical unit obstruction. -/
theorem exists_uncovered_halfGrid_phase_of_six_point_terminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hn5 : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hcard : Fintype.card V = 6)
    (top : V)
    (hTop : centreExponent (C top) t = n - 1)
    (hMin :
      ∀ i : V, i ≠ top →
        centreExponent (C i) t = n - 3) :
    ∃ r : Fin (2 * n + 1),
      ∀ u : GlobalUnitGapSlot C t,
        ¬ OrdinaryCriticalUnitBadAt C t delta
            u ((r.val : ℝ) / 2) := by
  by_contra hnone
  push_neg at hnone
  let slot : Fin (2 * n + 1) → GlobalUnitGapSlot C t :=
    fun r => Classical.choose (hnone r)
  have hbad :
      ∀ r : Fin (2 * n + 1),
        OrdinaryCriticalUnitBadAt C t delta
          (slot r) ((r.val : ℝ) / 2) := by
    intro r
    exact Classical.choose_spec (hnone r)
  have hinj :
      Function.Injective slot :=
    ordinaryCriticalUnitBadAt_halfGrid_injective
      C t delta hdeltaHalf slot hbad
  have hcardInj :
      2 * n + 1 ≤
        Fintype.card (GlobalUnitGapSlot C t) := by
    have h :=
      Fintype.card_le_of_injective slot hinj
    simpa using h
  have hslot10 :
      Fintype.card (GlobalUnitGapSlot C t) ≤ 10 :=
    six_point_globalUnitGapSlot_card_le_ten
      C hn4 hdelta0 (by linarith) ht
      hcard top hTop hMin
  omega

#print axioms ordinaryCriticalUnitBadAt_pair_distance_le_delta
#print axioms halfGrid_separation
#print axioms ordinaryCriticalUnitBadAt_halfGrid_injective
#print axioms exists_uncovered_halfGrid_phase_of_six_point_terminal

end JSP000404Research
