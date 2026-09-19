import JSP000404Research.OrderedBandCode
import JSP000404Research.OrderedEdgeColor
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Standard unit-band ordered colouring

For direction width strictly below an integer k, assign every increasing edge
to the unit band containing its normalized direction.  This packages the
canonical unit-band construction as an OrderedEdgeColoring.

The active colours of this OrderedEdgeColoring are exactly the incidentBands
already used by OrderedBandCode.  Hence later residual-colour elimination can
operate directly on the standard n+1 band partition.
-/

namespace JSP000404Research
namespace DirectionData

/-- Standard floor-band colour of an increasing edge.  Non-increasing pairs
receive colour zero; they are irrelevant to OrderedEdgeColoring. -/
noncomputable def standardBandColor
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ)
    (hk : 0 < k) (hwidth : width < (k : ℝ)) :
    V → V → Fin k :=
  fun u v =>
    if h : u < v then
      ⟨Nat.floor (D.value u v),
        (Nat.floor_lt (D.nonnegative h)).2
          ((D.belowWidth h).trans hwidth)⟩
    else
      ⟨0, hk⟩

/-- Consecutive increasing edges cannot occupy the same standard unit band. -/
theorem standardBandColor_ne
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ)
    (hk : 0 < k) (hwidth : width < (k : ℝ))
    {a v w : V} (hav : a < v) (hvw : v < w) :
    standardBandColor D k hk hwidth a v ≠
      standardBandColor D k hk hwidth v w := by
  intro heq
  have hfloor :
      Nat.floor (D.value a v) = Nat.floor (D.value v w) := by
    have hval := congrArg Fin.val heq
    simpa [standardBandColor, hav, hvw] using hval
  have ha0 := D.nonnegative hav
  have hw0 := D.nonnegative hvw
  have halo : ((Nat.floor (D.value a v) : ℕ) : ℝ) ≤ D.value a v :=
    Nat.floor_le ha0
  have hahi : D.value a v <
      ((Nat.floor (D.value a v) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hwlo : ((Nat.floor (D.value v w) : ℕ) : ℝ) ≤ D.value v w :=
    Nat.floor_le hw0
  have hwhi : D.value v w <
      ((Nat.floor (D.value v w) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [hfloor] at halo hahi
  have hsmall : |D.value a v - D.value v w| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge (D.middleSeparated hav hvw)) hsmall

/-- Canonical standard unit-band OrderedEdgeColoring. -/
noncomputable def standardBandColoring
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ)
    (hk : 0 < k) (hwidth : width < (k : ℝ)) :
    OrderedEdgeColoring V k where
  color := standardBandColor D k hk hwidth
  noMonoTwoPath := by
    intro a v w hav hvw
    exact standardBandColor_ne D k hk hwidth hav hvw

/-- On an increasing edge, membership in a prescribed unit band is equivalent
to having that standard band colour. -/
theorem standardBandColor_eq_iff
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ)
    (hk : 0 < k) (hwidth : width < (k : ℝ))
    {u v : V} (huv : u < v) (c : Fin k) :
    standardBandColor D k hk hwidth u v = c ↔
      (c : ℝ) ≤ D.value u v ∧ D.value u v < (c : ℝ) + 1 := by
  have hx0 := D.nonnegative huv
  constructor
  · intro heq
    have hval : Nat.floor (D.value u v) = c.val := by
      have := congrArg Fin.val heq
      simpa [standardBandColor, huv] using this
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one (D.value u v)
    rw [hval] at hlo hhi
    simpa using And.intro hlo hhi
  · intro hband
    have hf :
        Nat.floor (D.value u v) = c.val := by
      exact (Nat.floor_eq_iff hx0).2 (by simpa using hband)
    apply Fin.ext
    simpa [standardBandColor, huv] using hf

/-- The active colours of the standard OrderedEdgeColoring are precisely the
canonical incident unit bands. -/
theorem standardBand_active_eq_incidentBands
    {V : Type*} [LinearOrder V] {width : ℝ}
    (D : DirectionData V width) (k : ℕ)
    (hk : 0 < k) (hwidth : width < (k : ℝ))
    (v : V) :
    OrderedEdgeColoring.active
        (standardBandColoring D k hk hwidth) v =
      incidentBands D k v := by
  classical
  ext c
  simp only [OrderedEdgeColoring.active, incidentBands,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases h with ⟨a, hav, hcol⟩ | ⟨w, hvw, hcol⟩
    · left
      have hb :=
        (standardBandColor_eq_iff D k hk hwidth hav c).1 hcol
      exact ⟨a, hav, hb.1, hb.2⟩
    · right
      have hb :=
        (standardBandColor_eq_iff D k hk hwidth hvw c).1 hcol
      exact ⟨w, hvw, hb.1, hb.2⟩
  · intro h
    rcases h with ⟨a, hav, hlo, hhi⟩ | ⟨w, hvw, hlo, hhi⟩
    · left
      refine ⟨a, hav, ?_⟩
      exact (standardBandColor_eq_iff D k hk hwidth hav c).2 ⟨hlo, hhi⟩
    · right
      refine ⟨w, hvw, ?_⟩
      exact (standardBandColor_eq_iff D k hk hwidth hvw c).2 ⟨hlo, hhi⟩

#print axioms standardBandColor_ne
#print axioms standardBandColoring
#print axioms standardBandColor_eq_iff
#print axioms standardBand_active_eq_incidentBands

end DirectionData
end JSP000404Research
