
import JSP000404Research.ResidualBinaryRecursion
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualActiveDrop
import Mathlib.Tactic

/-!
# Actual n-colour child colourings after splitting the residual high band

Let D have total width n+delta with delta<1 and let C be its standard
(n+1)-band OrderedEdgeColoring.

The two overlapping recursive vertex sets are

  LeftChild  = {v | v is not a high sink},
  RightChild = {v | v is not a high source}.

Every edge internal to LeftChild has direction < n because its upper endpoint
is not a high sink.  Every edge internal to RightChild has direction < n
because its lower endpoint is not a high source.

Hence every internal parent edge is retained, and the parent colouring
restricts canonically to an n-colour OrderedEdgeColoring on each child.

If the parent profile satisfies

  exponent(v) < n
  card(active_C(v)) <= n-exponent(v)+1,

then the transformed child exponents from ResidualBinaryRecursion satisfy

  card(active_child(v)) <= n-childExponent(v).

This is exactly the one-layer local budget for the next integer parameter
n-1, whose standard construction has n colours.
-/

namespace JSP000404Research
namespace DirectionData

open OrderedEdgeColoring

def LeftResidualChild
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :=
  {v : V // ¬ HighSink D n v}

def RightResidualChild
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (n : ℕ) :=
  {v : V // ¬ HighSource D n v}

theorem width_lt_succ_of_eq_add_delta
    {width delta : ℝ} {n : ℕ}
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    width < (n + 1 : ℕ) := by
  rw [hwidth]
  norm_num
  linarith

/-- Internal edges of the left child are retained parent edges. -/
theorem leftChild_parentColor_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : LeftResidualChild D n}
    (huv : u < v) :
    ((standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)).color
        u.1 v.1).val < n := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  have hval :
      D.value u.1 v.1 < (n : ℝ) :=
    value_lt_high_threshold_of_not_sink
      D huv v.2
  by_contra hnot
  have hhigh :
      (n : ℝ) ≤ D.value u.1 v.1 :=
    (standardResidual_iff_high
      D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
      huv).1 hnot
  linarith

/-- Internal edges of the right child are retained parent edges. -/
theorem rightChild_parentColor_lt
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1)
    {u v : RightResidualChild D n}
    (huv : u < v) :
    ((standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)).color
        u.1 v.1).val < n := by
  have hval :
      D.value u.1 v.1 < (n : ℝ) :=
    value_lt_high_threshold_of_not_source
      D huv u.2
  by_contra hnot
  have hhigh :
      (n : ℝ) ≤ D.value u.1 v.1 :=
    (standardResidual_iff_high
      D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
      huv).1 hnot
  linarith

/-- Canonical n-colour restriction to the not-sink child. -/
noncomputable def leftChildColoring
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    OrderedEdgeColoring (LeftResidualChild D n) n := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  refine
    { color := fun u v =>
        retainedColor C u.1 v.1
          (by
            by_cases huv : u < v
            · exact leftChild_parentColor_lt
                D hwidth hdelta huv
            · have hnpos : 0 < n := by
                by_contra hn
                have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
                subst n
                have hu :
                    u.1 = v.1 ∨ v.1 < u.1 := by
                  rcases lt_trichotomy u.1 v.1 with h | h | h
                  · exact False.elim (huv h)
                  · exact Or.inl h
                  · exact Or.inr h
                rcases hu with rfl | hvu
                · simp [C, standardResidualColoring,
                    standardBandColoring, standardBandColor,
                    retainedColor]
                · have hlt :=
                    leftChild_parentColor_lt
                      D hwidth hdelta
                      (show (⟨v.1, v.2⟩ : LeftResidualChild D 0) <
                        ⟨u.1, u.2⟩ from hvu)
                  omega
              exact Fin.isLt _
          )
      noMonoTwoPath := ?_ }
  intro a v w hav hvw
  intro heq
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa [retainedColor] using hval

/-- Canonical n-colour restriction to the not-source child. -/
noncomputable def rightChildColoring
    {V : Type*} [LinearOrder V]
    {width delta : ℝ} {n : ℕ}
    (D : DirectionData V width)
    (hwidth : width = (n : ℝ) + delta)
    (hdelta : delta < 1) :
    OrderedEdgeColoring (RightResidualChild D n) n := by
  let C :=
    standardResidualColoring D n
      (width_lt_succ_of_eq_add_delta hwidth hdelta)
  refine
    { color := fun u v =>
        retainedColor C u.1 v.1
          (by
            by_cases huv : u < v
            · exact rightChild_parentColor_lt
                D hwidth hdelta huv
            · exact Fin.isLt _)
      noMonoTwoPath := ?_ }
  intro a v w hav hvw
  intro heq
  apply C.noMonoTwoPath hav hvw
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simpa [retainedColor] using hval

end DirectionData
end JSP000404Research
