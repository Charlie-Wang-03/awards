
import JSP000404Research.LinearBandSaturation
import JSP000404Research.LocalDirectionCycle
import JSP000404Research.StandardResidual
import JSP000404Research.ResidualSaturationBridge
import Mathlib.Tactic

/-!
# Residual projected saturation forces equality in the local full-band bound

Let R be the standard residual (n+1)-band colouring of DirectionData D.

For a LocalDirectionCycle L at v, assume

  L.exponent = projectedFree(R,v)

and that the residual top colour n is active at v.

Then the residual coordinate contributes exactly one active colour beyond the
retained palette.  Consequently

  L.exponent + card(active R v) = n+1.

The active set is exactly incidentBands_{n+1}, and the LocalDirectionCycle
occupied natural bands are exactly the same band set after taking Fin.val.
Therefore

  L.exponent + card(occupiedNatBands L.values) = n+1.

Moreover top band n is occupied.  This supplies precisely the hypotheses of
LinearBandSaturation.
-/

namespace JSP000404Research
namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

theorem fullBand_saturated_of_projected_saturated
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D v)
    (hwidth : t < (n + 1 : ℕ))
    (hsat :
      L.exponent =
        projectedFree (standardResidualColoring D n hwidth) v)
    (hres :
      residualCoord n ∈
        active (standardResidualColoring D n hwidth) v) :
    L.exponent + (occupiedNatBands L.values).card =
      n + 1 := by
  let R := standardResidualColoring D n hwidth
  have hretN :
      (retainedActive R v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive R v)
  have hactive :
      (active R v).card =
        (retainedActive R v).card + 1 :=
    active_card_eq_retainedActive_card_add_one_of_residual_mem
      R v hres
  have hsat' :
      L.exponent =
        n - (retainedActive R v).card := by
    simpa [R, projectedFree] using hsat
  have hstd :
      active R v =
        incidentBands D (n + 1) v := by
    exact standardResidual_active_eq_incidentBands_succ
      D n hwidth v
  have htLe :
      t ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_of_lt hwidth)
  have hocc :
      (occupiedNatBands L.values).card =
        (incidentBands D (n + 1) v).card :=
    L.occupiedNatBands_values_card_eq_incidentBands_card
      (n + 1) htLe
  rw [hstd] at hactive
  rw [hocc]
  omega

/-- Residual activity means that the top natural band n occurs in the local
value list. -/
theorem top_band_mem_occupied_of_residual_mem
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D v)
    (hwidth : t < (n + 1 : ℕ))
    (hres :
      residualCoord n ∈
        active (standardResidualColoring D n hwidth) v) :
    n ∈ occupiedNatBands L.values := by
  have hstd :
      active (standardResidualColoring D n hwidth) v =
        incidentBands D (n + 1) v :=
    standardResidual_active_eq_incidentBands_succ
      D n hwidth v
  have htopIncident :
      (⟨n, by omega⟩ : Fin (n + 1)) ∈
        incidentBands D (n + 1) v := by
    rw [← hstd]
    simpa [residualCoord] using hres
  have htLe :
      t ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_of_lt hwidth)
  have hbands :=
    L.occupiedNatBands_values_eq_incident_val_map
      (n + 1) htLe
  rw [hbands]
  apply Finset.mem_image.mpr
  exact ⟨⟨n, by omega⟩, htopIncident, rfl⟩

/-- Packaged saturation certificate in a concrete nonempty value-list form. -/
theorem exists_saturated_linear_value_decomposition
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    (D : DirectionData V t)
    (L : LocalDirectionCycle D v)
    (hwidth : t < (n + 1 : ℕ))
    (hsat :
      L.exponent =
        projectedFree (standardResidualColoring D n hwidth) v)
    (hres :
      residualCoord n ∈
        active (standardResidualColoring D n hwidth) v) :
    ∃ a xs,
      L.values = a :: xs ∧
      0 ≤ a ∧
      (a :: xs).Pairwise (· ≤ ·) ∧
      (∀ x ∈ a :: xs, x < t) ∧
      n ∈ occupiedNatBands (a :: xs) ∧
      listExponent
          (linearCyclicGapQuotients t (a :: xs)) +
          (occupiedNatBands (a :: xs)).card
        =
      n + 1 := by
  obtain ⟨a, xs, hvalues⟩ :
      ∃ a xs, L.values = a :: xs := by
    cases h : L.values with
    | nil =>
        exact False.elim (L.values_nonempty h)
    | cons a xs =>
        exact ⟨a, xs, h⟩
  have haMem : a ∈ L.values := by
    rw [hvalues]
    simp
  have ha0 := (L.value_mem_bounds haMem).1
  have hsorted :
      (a :: xs).Pairwise (· ≤ ·) := by
    simpa [hvalues] using L.values_pairwise
  have hall :
      ∀ x ∈ a :: xs, x < t := by
    intro x hx
    exact (L.value_mem_bounds
      (by simpa [hvalues] using hx)).2
  have htop :=
    top_band_mem_occupied_of_residual_mem
      D L hwidth hres
  have hfull :=
    fullBand_saturated_of_projected_saturated
      D L hwidth hsat hres
  unfold LocalDirectionCycle.exponent
    LocalDirectionCycle.gapQuotients at hfull
  rw [hvalues] at hfull htop
  exact ⟨a, xs, hvalues, ha0, hsorted, hall, htop, hfull⟩

#print axioms fullBand_saturated_of_projected_saturated
#print axioms top_band_mem_occupied_of_residual_mem
#print axioms exists_saturated_linear_value_decomposition

end LocalDirectionCycle
end DirectionData
end JSP000404Research
