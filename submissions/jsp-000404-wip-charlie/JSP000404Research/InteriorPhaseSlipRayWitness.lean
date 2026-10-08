import JSP000404Research.CyclicInteriorPhaseSlip
import Mathlib.Tactic

/-!
# Real neighbouring rays at an interior floor phase slip

A non-wrap (floor(real gap), integer-band jump) = (0,1)
occurrence in a sorted local direction cycle is more than an
anonymous membership of two mapped integer lists: it is realized
by two consecutive actual rays in the centre's ordered ray list.

The statement below extracts those rays and the precise
real-direction inequalities required for further planar
triangle interactions, without assuming a new geometric
global matching principle.
-/

namespace JSP000404Research

/-- A (0,1) occurrence in paired successive floor-gap and integer-
band-jump lists is witnessed by actual neighbouring list elements. -/
theorem adjacent_pair_of_interior_phase_slip
    {α : Type*}
    (f : α → ℝ)
    (first : α)
    (rest : List α)
    (hsorted : (first :: rest).Pairwise (fun u v => f u ≤ f v))
    (h :
      (0, 1) ∈ List.zip
        ((successiveDiffsFrom (f first) (rest.map f)).map Nat.floor)
        (successiveNatDiffsFrom (Nat.floor (f first))
          (rest.map (Nat.floor ∘ f)))) :
    ∃ (u v : α) (pre post : List α),
      first :: rest = pre ++ u :: v :: post ∧
        f u ≤ f v ∧
        Nat.floor (f v - f u) = 0 ∧
        Nat.floor (f v) - Nat.floor (f u) = 1 := by
  induction rest generalizing first with
  | nil =>
      simp [successiveDiffsFrom, successiveNatDiffsFrom] at h
  | cons next tail ih =>
      simp only [List.map_cons, successiveDiffsFrom,
        successiveNatDiffsFrom, List.zip,
        List.mem_cons] at h
      rcases h with hhead | htail
      · have hq : Nat.floor (f next - f first) = 0 := by
          have hp := congrArg Prod.fst hhead
          simpa using hp.symm
        have hb :
            Nat.floor (f next) - Nat.floor (f first) = 1 := by
          have hp := congrArg Prod.snd hhead
          simpa using hp.symm
        have hle : f first ≤ f next :=
          (List.pairwise_cons.mp hsorted).1 next (by simp)
        exact ⟨first, next, [], tail, rfl, hle, hq, hb⟩
      · obtain ⟨u, v, pre, post, hsplit, hle, hq, hb⟩ :=
          ih next (List.pairwise_cons.mp hsorted).2 htail
        refine ⟨u, v, first :: pre, post, ?_, hle, hq, hb⟩
        simpa only [List.cons_append] using
          congrArg (List.cons first) hsplit

namespace DirectionData
namespace LocalDirectionCycle

open OrderedEdgeColoring

/-- A saturated residual-inactive centre contains two *consecutive
actual rays* whose direction values cross precisely one integer band
boundary, although their physical normalized separation is < 1. -/
theorem exists_adjacent_rays_with_short_band_crossing
    {V : Type*} [LinearOrder V] [Fintype V]
    {t : ℝ} {n : ℕ}
    {D : DirectionData V t} {i : V}
    (C : LocalDirectionCycle D i)
    (ht : t < (n : ℝ) + 1)
    (htight :
      C.exponent + (D.incidentBands (n + 1) i).card = n + 1)
    (hres : residualCoord n ∉
      active (standardResidualColoring D n
        (by exact_mod_cast ht)) i) :
    ∃ (u v : OtherVertex i) (pre post : List (OtherVertex i)),
      C.rays = pre ++ u :: v :: post ∧
        0 ≤ D.localDirectionValue i v - D.localDirectionValue i u ∧
        D.localDirectionValue i v - D.localDirectionValue i u < 1 ∧
        Nat.floor (D.localDirectionValue i v) -
          Nat.floor (D.localDirectionValue i u) = 1 := by
  obtain ⟨first, rest, hrays⟩ :
      ∃ a xs, C.rays = a :: xs := by
    cases h : C.rays with
    | nil => exact False.elim (C.nonempty h)
    | cons a xs => exact ⟨a, xs, rfl⟩
  have hvals :
      C.values = D.localDirectionValue i first ::
        rest.map (D.localDirectionValue i) := by
    simp [LocalDirectionCycle.values, hrays]
  have hslip :=
    C.interior_phase_slip_of_tight_and_residual_inactive
      ht (D.localDirectionValue i first)
      (rest.map (D.localDirectionValue i))
      hvals htight hres
  have hslip' :
      (0, 1) ∈ List.zip
        ((successiveDiffsFrom (D.localDirectionValue i first)
          (rest.map (D.localDirectionValue i))).map Nat.floor)
        (successiveNatDiffsFrom
          (Nat.floor (D.localDirectionValue i first))
          (rest.map (Nat.floor ∘ D.localDirectionValue i))) := by
    simpa only [List.map_map, Function.comp_def] using hslip
  have hsorted :
      (first :: rest).Pairwise
        (fun u v => D.localDirectionValue i u ≤
          D.localDirectionValue i v) := by
    simpa only [← hrays] using C.value_sorted
  obtain ⟨u, v, pre, post, hsplit, hle, hq, hb⟩ :=
    adjacent_pair_of_interior_phase_slip
      (D.localDirectionValue i) first rest hsorted hslip'
  have hnonneg :
      0 ≤ D.localDirectionValue i v - D.localDirectionValue i u := by
    linarith
  have hsmall :
      D.localDirectionValue i v - D.localDirectionValue i u < 1 := by
    exact (Nat.floor_lt hnonneg).1 (by omega : Nat.floor
      (D.localDirectionValue i v - D.localDirectionValue i u) < 1)
  exact ⟨u, v, pre, post, hrays.trans hsplit,
    hnonneg, hsmall, hb⟩

#print axioms adjacent_pair_of_interior_phase_slip
#print axioms LocalDirectionCycle.exists_adjacent_rays_with_short_band_crossing

end LocalDirectionCycle
end DirectionData
end JSP000404Research
