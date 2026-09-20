import Mathlib.Tactic

/-!
# Ordered interval packing on the real line

This is the one-dimensional arithmetic core of the support-arc packing
argument.

If a finite list of closed endpoint pairs [l_i,r_i] is ordered so that every
earlier interval ends before every later interval begins, every interval lies
inside [A,B], and l_i <= r_i, then

  sum_i (r_i-l_i) <= B-A.

The circle argument for one-support JSP-000404 centres may therefore be split
cleanly into:

1. choose a cut avoiding all open strict-support arcs;
2. lift and sort those arcs into one real window of width 2*pi;
3. apply this file.

No convex-hull or measure theory is needed after the cut is supplied.
-/

namespace JSP000404Research

def realIntervalLength (x : ℝ × ℝ) : ℝ :=
  x.2 - x.1

/-- Pairwise ordered, disjoint real intervals fit inside the ambient window. -/
theorem ordered_interval_length_sum_le
    (xs : List (ℝ × ℝ))
    (A B : ℝ)
    (hAB : A ≤ B)
    (hnonneg : ∀ x ∈ xs, x.1 ≤ x.2)
    (hbounds : ∀ x ∈ xs, A ≤ x.1 ∧ x.2 ≤ B)
    (hpair :
      xs.Pairwise (fun x y => x.2 ≤ y.1)) :
    (xs.map realIntervalLength).sum ≤ B - A := by
  induction xs generalizing A with
  | nil =>
      simp [hAB]
  | cons x xs ih =>
      have hxNonneg : x.1 ≤ x.2 :=
        hnonneg x (by simp)
      have hxBounds : A ≤ x.1 ∧ x.2 ≤ B :=
        hbounds x (by simp)
      have hpair' := List.pairwise_cons.mp hpair
      cases xs with
      | nil =>
          simp [realIntervalLength]
          linarith
      | cons y ys =>
          have htailPair :
              (y :: ys).Pairwise
                (fun u v => u.2 ≤ v.1) :=
            hpair'.2
          have htailNonneg :
              ∀ z ∈ y :: ys, z.1 ≤ z.2 := by
            intro z hz
            exact hnonneg z (by simp [hz])
          have htailBounds :
              ∀ z ∈ y :: ys, x.2 ≤ z.1 ∧ z.2 ≤ B := by
            intro z hz
            constructor
            · exact hpair'.1 z (by simp [hz])
            · exact (hbounds z (by simp [hz])).2
          have hx2B : x.2 ≤ B := hxBounds.2
          have htail :=
            ih (x.2) hx2B
              htailNonneg htailBounds htailPair
          simp only [List.map_cons, List.sum_cons]
          dsimp [realIntervalLength]
          linarith

/-- Specialized window of angular width 2*pi. -/
theorem ordered_angular_intervals_sum_le_two_pi
    (xs : List (ℝ × ℝ))
    (A : ℝ)
    (hnonneg : ∀ x ∈ xs, x.1 ≤ x.2)
    (hbounds :
      ∀ x ∈ xs,
        A ≤ x.1 ∧ x.2 ≤ A + 2 * Real.pi)
    (hpair :
      xs.Pairwise (fun x y => x.2 ≤ y.1)) :
    (xs.map realIntervalLength).sum ≤ 2 * Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h :=
    ordered_interval_length_sum_le
      xs A (A + 2 * Real.pi)
      (by linarith)
      hnonneg hbounds hpair
  simpa using h

/-- If each angular interval has length pi*g_i, the normalized gap lengths
sum to at most two. -/
theorem normalized_gap_sum_le_two_of_ordered_arc_packing
    (gaps : List ℝ)
    (arcs : List (ℝ × ℝ))
    (A : ℝ)
    (hlen : arcs.length = gaps.length)
    (hgap0 : ∀ g ∈ gaps, 0 ≤ g)
    (hlength :
      ∀ k : Fin arcs.length,
        realIntervalLength (arcs.get k) =
          Real.pi * gaps.get
            ⟨k.val, by simpa [hlen] using k.isLt⟩)
    (hbounds :
      ∀ x ∈ arcs,
        A ≤ x.1 ∧ x.2 ≤ A + 2 * Real.pi)
    (hpair :
      arcs.Pairwise (fun x y => x.2 ≤ y.1)) :
    gaps.sum ≤ 2 := by
  have harcNonneg :
      ∀ x ∈ arcs, x.1 ≤ x.2 := by
    intro x hx
    obtain ⟨k, hk⟩ := List.get_of_mem hx
    subst x
    have hg :
        0 ≤ gaps.get ⟨k.val, by simpa [hlen] using k.isLt⟩ :=
      hgap0 _ (List.get_mem _ _)
    have hlenk := hlength k
    dsimp [realIntervalLength] at hlenk
    nlinarith [Real.pi_pos]
  have hsumArc :=
    ordered_angular_intervals_sum_le_two_pi
      arcs A harcNonneg hbounds hpair
  have hsumEq :
      (arcs.map realIntervalLength).sum =
        Real.pi * gaps.sum := by
    rw [← List.sum_map_mul_left]
    apply List.sum_congr_left
    intro k
    exact hlength k
  rw [hsumEq] at hsumArc
  nlinarith [Real.pi_pos]

#print axioms ordered_interval_length_sum_le
#print axioms ordered_angular_intervals_sum_le_two_pi
#print axioms normalized_gap_sum_le_two_of_ordered_arc_packing

end JSP000404Research
