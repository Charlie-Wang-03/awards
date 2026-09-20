import JSP000404Research.CentreProjectiveCycle
import JSP000404Research.CentreSignPath
import Mathlib.Tactic

/-!
# Aligning a ray-list cut with the corresponding cyclic projective gap

For a sorted nonempty ray list

  first :: before ++ right :: tail,

the cyclic projective gap at position |before| is exactly

  theta(right) - theta(left),

where left is the final ray of first :: before.

If there is no after-block, the distinguished final gap is the wrap gap

  theta(first) + pi - theta(last).

These identities are purely list-theoretic consequences of the concrete
definition of projectiveGaps / normalizedProjectiveGaps.
-/

namespace JSP000404Research

open Real

/-- Successive differences split cleanly at an appended nonempty tail. -/
theorem successiveDiffsFrom_append_cons
    (a b : ℝ) (xs bs : List ℝ) :
    successiveDiffsFrom a (xs ++ b :: bs) =
      successiveDiffsFrom a xs ++
        (b - xs.getLastD a) ::
          successiveDiffsFrom b bs := by
  induction xs generalizing a with
  | nil =>
      simp [successiveDiffsFrom]
  | cons x xs ih =>
      simp [successiveDiffsFrom, ih, List.append_assoc]

/-- Last element after appending a nonempty block is the last element of that
block. -/
theorem getLastD_append_cons
    {α : Type*} (d : α) (xs : List α) (b : α) (bs : List α) :
    (xs ++ b :: bs).getLastD d = bs.getLastD b := by
  induction xs generalizing d with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

/-- Physical projective gaps split at an ordinary ray cut. -/
theorem projectiveGaps_append_cons
    (a b : ℝ) (xs bs : List ℝ) :
    projectiveGaps (a :: (xs ++ b :: bs)) =
      successiveDiffsFrom a xs ++
        (b - xs.getLastD a) ::
          (successiveDiffsFrom b bs ++
            [a + Real.pi - bs.getLastD b]) := by
  rw [projectiveGaps, successiveDiffsFrom_append_cons]
  simp [getLastD_append_cons, List.append_assoc]

/-- Normalized version of the ordinary cut decomposition. -/
theorem normalizedProjectiveGaps_append_cons
    (a b : ℝ) (xs bs : List ℝ) :
    normalizedProjectiveGaps (a :: (xs ++ b :: bs)) =
      (successiveDiffsFrom a xs).map (fun d => d / Real.pi) ++
        ((b - xs.getLastD a) / Real.pi) ::
          ((successiveDiffsFrom b bs).map (fun d => d / Real.pi) ++
            [(a + Real.pi - bs.getLastD b) / Real.pi]) := by
  rw [normalizedProjectiveGaps, projectiveGaps_append_cons]
  simp [List.map_append]

/-- Two list decompositions with prefixes of equal length have the same
distinguished next entry. -/
theorem distinguished_entry_eq_of_decompositions
    {α : Type*}
    {l pre₁ post₁ pre₂ post₂ : List α}
    {x y : α}
    (h₁ : l = pre₁ ++ x :: post₁)
    (h₂ : l = pre₂ ++ y :: post₂)
    (hlen : pre₁.length = pre₂.length) :
    x = y := by
  have hdrop₁ :
      l.drop pre₁.length = x :: post₁ := by
    rw [h₁]
    simp
  have hdrop₂ :
      l.drop pre₂.length = y :: post₂ := by
    rw [h₂]
    simp
  rw [hlen] at hdrop₁
  rw [hdrop₂] at hdrop₁
  exact List.cons.inj hdrop₁ |>.1

/-- In an actual centre cycle, a decomposition at the same prefix length as an
ordinary ray cut identifies the distinguished normalized gap with the angular
difference across that cut. -/
theorem centre_gap_eq_ordinary_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (first right : OtherVertex i)
    (before tail : List (OtherVertex i))
    (hrays :
      C.rays = first :: (before ++ right :: tail))
    {gpre gpost : List ℝ} {ge : ℝ}
    (hgaps : C.gaps = gpre ++ ge :: gpost)
    (hlen : gpre.length = before.length) :
    ge =
      (rayThetaAt hp i right -
        rayThetaAt hp i ((first :: before).getLast (by simp))) /
        Real.pi := by
  let theta := rayThetaAt hp i
  have hstd :
      C.gaps =
        (successiveDiffsFrom (theta first)
          (before.map theta)).map (fun d => d / Real.pi) ++
          ((theta right -
            (before.map theta).getLastD (theta first)) / Real.pi) ::
            ((successiveDiffsFrom (theta right)
              (tail.map theta)).map (fun d => d / Real.pi) ++
              [((theta first + Real.pi -
                (tail.map theta).getLastD (theta right)) / Real.pi)]) := by
    rw [CentreProjectiveCycle.gaps, CentreProjectiveCycle.angles, hrays]
    simp only [List.map_cons, List.map_append]
    rw [normalizedProjectiveGaps_append_cons]
  have hpref :
      ((successiveDiffsFrom (theta first)
        (before.map theta)).map
          (fun d => d / Real.pi)).length =
        before.length := by
    simp [successiveDiffsFrom_length]
  have heq :=
    distinguished_entry_eq_of_decompositions
      hgaps hstd (by simpa [hpref] using hlen)
  have hlast :
      (before.map theta).getLastD (theta first) =
        theta ((first :: before).getLast (by simp)) := by
    cases before with
    | nil =>
        simp [theta]
    | cons b bs =>
        simp [theta, List.getLast_cons]
  rw [heq, hlast]

/-- Wrap analogue: if the distinguished entry occurs after all ordinary
successive gaps, it is exactly the normalized wrap gap. -/
theorem centre_gap_eq_wrap_cut
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (first : OtherVertex i)
    (rest : List (OtherVertex i))
    (hrays : C.rays = first :: rest)
    {gpre gpost : List ℝ} {ge : ℝ}
    (hgaps : C.gaps = gpre ++ ge :: gpost)
    (hlen : gpre.length = rest.length)
    (hpost : gpost = []) :
    ge =
      (rayThetaAt hp i first + Real.pi -
        rayThetaAt hp i ((first :: rest).getLast (by simp))) /
        Real.pi := by
  let theta := rayThetaAt hp i
  have hstd :
      C.gaps =
        (successiveDiffsFrom (theta first)
          (rest.map theta)).map (fun d => d / Real.pi) ++
          [((theta first + Real.pi -
            (rest.map theta).getLastD (theta first)) / Real.pi)] := by
    rw [CentreProjectiveCycle.gaps, CentreProjectiveCycle.angles, hrays]
    simp [normalizedProjectiveGaps, projectiveGaps, List.map_append]
  have hpref :
      ((successiveDiffsFrom (theta first)
        (rest.map theta)).map
          (fun d => d / Real.pi)).length =
        rest.length := by
    simp [successiveDiffsFrom_length]
  have heq :=
    distinguished_entry_eq_of_decompositions
      hgaps
      (by
        rw [hstd]
        rfl)
      (by simpa [hpref] using hlen)
  have hlast :
      (rest.map theta).getLastD (theta first) =
        theta ((first :: rest).getLast (by simp)) := by
    cases rest with
    | nil =>
        simp [theta]
    | cons b bs =>
        simp [theta, List.getLast_cons]
  rw [heq, hlast]

#print axioms successiveDiffsFrom_append_cons
#print axioms distinguished_entry_eq_of_decompositions
#print axioms centre_gap_eq_ordinary_cut
#print axioms centre_gap_eq_wrap_cut

end JSP000404Research
