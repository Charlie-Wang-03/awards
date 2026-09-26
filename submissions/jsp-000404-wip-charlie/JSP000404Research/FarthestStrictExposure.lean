import JSP000404Research.StrictExposure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# A farthest point from a fixed vertex is strictly exposed

Fix a vertex s.  Among all other vertices choose j maximizing the squared
Euclidean distance to s.

For every k != j, use the supporting vector

  u = p s - p j.

If k=s then <u,u> > 0.  Otherwise write

  v = p j - p s,
  e = p k - p j.

Then p k - p s = v + e.  Maximality gives

  ||v+e||^2 <= ||v||^2,

hence

  2 <v,e> + ||e||^2 <= 0.

Since k != j and p is injective, e != 0, so ||e||^2>0.  Therefore

  <p s-p j, p k-p j> = <-v,e> > 0.

Thus the line through p j orthogonal to u strictly supports the entire finite
configuration.  In particular, every finite injective configuration with at
least two points has a strictly exposed point different from any prescribed
vertex s.
-/

namespace JSP000404Research

/-- Squared distance to a fixed vertex, used only as a finite maximizing
functional. -/
noncomputable def sqDistanceFrom
    {V : Type*} {p : V → Plane}
    (s j : V) : ℝ :=
  ‖p j - p s‖ ^ 2

/-- A non-fixed vertex maximizing squared distance from s is strictly exposed. -/
theorem strictlyExposedAt_of_sqDistanceFrom_max
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (s j : V)
    (hjs : j ≠ s)
    (hmax :
      ∀ k : V, k ≠ s →
        sqDistanceFrom (p := p) s k ≤
          sqDistanceFrom (p := p) s j) :
    StrictlyExposedAt p j := by
  refine ⟨p s - p j, ?_⟩
  intro k hkj
  by_cases hks : k = s
  · subst k
    have huNe : p s - p j ≠ 0 := by
      exact sub_ne_zero.mpr (hp.ne hjs.symm)
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr huNe)
  · let v : Plane := p j - p s
    let e : Plane := p k - p j
    have heNe : e ≠ 0 := by
      dsimp [e]
      exact sub_ne_zero.mpr (hp.ne hkj)
    have heSq : 0 < ‖e‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr heNe)
    have hfar :=
      hmax k hks
    have hw :
        p k - p s = v + e := by
      dsimp [v, e]
      abel
    have hj :
        p j - p s = v := by
      rfl
    rw [sqDistanceFrom, hw, hj] at hfar
    have hexpand := norm_add_sq v e
    have hve :
        2 * inner ℝ v e + ‖e‖ ^ 2 ≤ 0 := by
      rw [hexpand] at hfar
      nlinarith
    have hneg : 0 < - inner ℝ v e := by
      nlinarith
    have hu : p s - p j = -v := by
      dsimp [v]
      abel
    have he : p k - p j = e := rfl
    rw [hu, he, inner_neg_left]
    exact hneg

/-- Finite existence form: relative to any fixed vertex s there is a different
strictly exposed vertex, provided the configuration contains at least two
vertices. -/
theorem exists_strictlyExposed_ne_fixed
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcard : 2 ≤ Fintype.card V)
    (s : V) :
    ∃ j : V, j ≠ s ∧ StrictlyExposedAt p j := by
  classical
  let S : Finset V := Finset.univ.erase s
  have hScard :
      S.card = Fintype.card V - 1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ s)]
    simp
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    rw [hScard]
    omega
  obtain ⟨j, hjS, hmaxS⟩ :=
    Finset.exists_max_image
      S
      (fun x => sqDistanceFrom (p := p) s x)
      hSne
  have hjs : j ≠ s :=
    (Finset.mem_erase.mp (by simpa [S] using hjS)).1
  have hmax :
      ∀ k : V, k ≠ s →
        sqDistanceFrom (p := p) s k ≤
          sqDistanceFrom (p := p) s j := by
    intro k hks
    apply hmaxS k
    simpa [S, hks]
  exact ⟨j, hjs,
    strictlyExposedAt_of_sqDistanceFrom_max
      hp s j hjs hmax⟩

#print axioms strictlyExposedAt_of_sqDistanceFrom_max
#print axioms exists_strictlyExposed_ne_fixed

end JSP000404Research
