import JSP000404Research.FourCentreSupportTwoContradiction
import JSP000404Research.StrictSupportCone
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-!
# A point outside the triangle of the other three is strictly exposed

For four pairwise-distinct planar points s,a,b,c, if p(c) does not belong to

  convexHull ℝ {p(s), p(a), p(b)},

the closed-convex-set / point Hahn--Banach theorem gives a continuous linear
functional strictly separating p(c) from that triangle.

By the Riesz representation theorem, the negative representing vector has
strictly positive inner product with every displacement p(j)-p(c), j != c.
Hence c is StrictlyExposedAt.

This isolates the convex-hull half of the mixed four-centre dichotomy.  The
quantitative conversion from strict exposure plus the global angle cap to a
support interval of turn at least lambda is kept separate.
-/

namespace JSP000404Research

open Real

theorem strictSupportsAt_of_not_mem_other_triangle_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hout :
      p c ∉ convexHull ℝ
        ({p s, p a, p b} : Set Plane)) :
    ∃ u : Plane, StrictSupportsAt p c u := by
  let S : Set Plane := {p s, p a, p b}
  have hfinite : S.Finite := by
    simp [S]
  have hconv : Convex ℝ (convexHull ℝ S) :=
    convex_convexHull ℝ S
  have hclosed : IsClosed (convexHull ℝ S) :=
    hfinite.isClosed_convexHull
  have hout' : p c ∉ convexHull ℝ S := by
    simpa [S] using hout
  obtain ⟨f, level, hfS, hfc⟩ :=
    geometric_hahn_banach_closed_point hconv hclosed hout'
  let w : Plane :=
    -((InnerProductSpace.toDual ℝ Plane).symm f)
  refine ⟨w, ?_⟩
  intro j hjc
  have hcover :=
    fin_four_exhaust_of_four_distinct
      hsa hsb hsc hab hac hbc j
  have hjmem : p j ∈ S := by
    rcases hcover with hjs | hja | hjb | hjc'
    · subst j
      simp [S]
    · subst j
      simp [S]
    · subst j
      simp [S]
    · exact False.elim (hjc hjc')
  have hjHull :
      p j ∈ convexHull ℝ S :=
    subset_convexHull ℝ S hjmem
  have hfj : f (p j) < level :=
    hfS (p j) hjHull
  have hlt : f (p j) < f (p c) :=
    hfj.trans hfc
  dsimp [w]
  rw [inner_neg_left,
      InnerProductSpace.toDual_symm_apply]
  rw [map_sub]
  linarith

theorem strictlyExposedAt_of_not_mem_other_triangle_fin_four
    {p : Fin 4 → Plane}
    (hp : Function.Injective p)
    {s a b c : Fin 4}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hout :
      p c ∉ convexHull ℝ
        ({p s, p a, p b} : Set Plane)) :
    StrictlyExposedAt p c := by
  exact strictSupportsAt_of_not_mem_other_triangle_fin_four
    hp hsa hsb hsc hab hac hbc hout

#print axioms strictSupportsAt_of_not_mem_other_triangle_fin_four
#print axioms strictlyExposedAt_of_not_mem_other_triangle_fin_four

end JSP000404Research
