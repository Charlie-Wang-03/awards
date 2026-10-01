import JSP000404Research.ResidualEnlargedCandidateHall
import JSP000404Research.ResidualLossThreeExitRecursiveOutlet
import Mathlib.Tactic

/-!
# Minimal-core collapse from four second-layer vertices

Four second-layer vertices have total dyadic demand exactly 2^n.

Inside an inclusion-minimal deficient enlarged-candidate core T, if those four
vertices form a proper subset, minimality forces their candidate union to have
cardinality at least 2^n.  Since every candidate word lies in the ambient
Boolean cube of cardinality 2^n, those four blocks already cover the entire
cube.

Consequently T cannot contain two further vertices: adjoining just one extra
vertex to the four gives a proper subset whose union is still the whole cube
but whose positive demand exceeds 2^n, contradicting minimality.

Hence a minimal deficient core containing four distinct second-layer vertices
has cardinality at most five.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem four_secondLayer_demand_eq_cube
    {V : Type*} {n : ℕ}
    (exponent : V → ℕ)
    (hn2 : 2 ≤ n)
    {a b c d : V}
    (ha : exponent a = n - 2)
    (hb : exponent b = n - 2)
    (hc : exponent c = n - 2)
    (hd : exponent d = n - 2) :
    2 ^ exponent a + 2 ^ exponent b +
        2 ^ exponent c + 2 ^ exponent d =
      2 ^ n := by
  rw [ha,hb,hc,hd]
  have hpow :
      4 * 2 ^ (n - 2) = 2 ^ n := by
    let m := n - 2
    have hn : n = m + 2 := by
      dsimp [m]
      omega
    rw [hn]
    simp [pow_succ]
    ring
  omega

theorem minimal_deficient_four_secondLayer_union_eq_univ_of_proper
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn2 : 2 ≤ n)
    {T : Finset V}
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {a b c d : V}
    (haT : a ∈ T) (hbT : b ∈ T)
    (hcT : c ∈ T) (hdT : d ∈ T)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : exponent a = n - 2)
    (hb : exponent b = n - 2)
    (hc : exponent c = n - 2)
    (hd : exponent d = n - 2)
    (hproper : ({a,b,c,d} : Finset V) ⊂ T) :
    ({a,b,c,d} : Finset V).biUnion
        (enlargedProjectedCandidateBlock C exponent)
      =
    (Finset.univ : Finset (Fin n → Bool)) := by
  classical
  let U : Finset V := {a,b,c,d}
  have hnondef := hmin U hproper
  unfold BlockDeficient at hnondef
  push_neg at hnondef
  have hsum :
      (∑ x ∈ U, 2 ^ exponent x) = 2 ^ n := by
    have hcardForm :
        (∑ x ∈ ({a,b,c,d} : Finset V), 2 ^ exponent x)
          =
        2 ^ exponent a + 2 ^ exponent b +
          2 ^ exponent c + 2 ^ exponent d := by
      simp [hab,hac,had,hbc,hbd,hcd]
    rw [show U = {a,b,c,d} by rfl, hcardForm]
    exact four_secondLayer_demand_eq_cube
      exponent hn2 ha hb hc hd
  have hlower :
      2 ^ n ≤
        (U.biUnion
          (enlargedProjectedCandidateBlock C exponent)).card := by
    rw [← hsum]
    exact hnondef
  have hupper :
      (U.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        ≤ 2 ^ n := by
    have hsub :
        U.biUnion
            (enlargedProjectedCandidateBlock C exponent)
          ⊆
        (Finset.univ : Finset (Fin n → Bool)) :=
      Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool] using hc
  have hcardEq :
      (U.biUnion
        (enlargedProjectedCandidateBlock C exponent)).card
        =
      (Finset.univ : Finset (Fin n → Bool)).card := by
    simp only [Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
    omega
  apply Finset.eq_univ_of_card
  simpa [U] using hcardEq

theorem minimal_deficient_core_card_le_five_of_four_secondLayer
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hn2 : 2 ≤ n)
    {T : Finset V}
    (hdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        T)
    (hmin :
      ∀ U : Finset V,
        U ⊂ T →
        ¬ BlockDeficient
          (fun x => 2 ^ exponent x)
          (enlargedProjectedCandidateBlock C exponent)
          U)
    {a b c d : V}
    (haT : a ∈ T) (hbT : b ∈ T)
    (hcT : c ∈ T) (hdT : d ∈ T)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : exponent a = n - 2)
    (hb : exponent b = n - 2)
    (hc : exponent c = n - 2)
    (hd : exponent d = n - 2) :
    T.card ≤ 5 := by
  classical
  by_contra hnot
  have hT6 : 6 ≤ T.card := by omega
  let U : Finset V := {a,b,c,d}
  have hUsub : U ⊆ T := by
    intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact haT
    · exact hbT
    · exact hcT
    · exact hdT
  have hUcard : U.card = 4 := by
    simp [U,hab,hac,had,hbc,hbd,hcd]
  have hUproper : U ⊂ T := by
    refine ⟨hUsub,?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [hUcard] at hc
    omega
  have hUuniv :=
    minimal_deficient_four_secondLayer_union_eq_univ_of_proper
      C exponent hn2 hmin
      haT hbT hcT hdT
      hab hac had hbc hbd hcd
      ha hb hc hd hUproper

  obtain ⟨w,hwT,hwU⟩ :=
    Finset.exists_of_ssubset hUproper
  let W : Finset V := insert w U
  have hWsub : W ⊆ T := by
    intro q hq
    simp only [W, Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact hwT
    · exact hUsub hq
  have hwNotU : w ∉ U := hwU
  have hWcard : W.card = 5 := by
    simp [W,hwNotU,hUcard]
  have hWproper : W ⊂ T := by
    refine ⟨hWsub,?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    rw [hWcard] at hc
    omega
  have hWunion :
      W.biUnion (enlargedProjectedCandidateBlock C exponent)
        =
      (Finset.univ : Finset (Fin n → Bool)) := by
    ext word
    constructor
    · intro _h
      simp
    · intro _h
      have hwordU :
          word ∈ U.biUnion
            (enlargedProjectedCandidateBlock C exponent) := by
        rw [hUuniv]
        simp
      obtain ⟨q,hqU,hqWord⟩ :=
        Finset.mem_biUnion.mp hwordU
      apply Finset.mem_biUnion.mpr
      exact ⟨q,hWsub (hUsub hqU),hqWord⟩

  have hUSum :
      (∑ x ∈ U, 2 ^ exponent x) = 2 ^ n := by
    simpa [U,hab,hac,had,hbc,hbd,hcd] using
      (four_secondLayer_demand_eq_cube
        exponent hn2 ha hb hc hd)
  have hWSum :
      (∑ x ∈ W, 2 ^ exponent x) =
        2 ^ n + 2 ^ exponent w := by
    rw [show W = insert w U by rfl,
      Finset.sum_insert hwNotU,hUSum]
    omega
  have hWdef :
      BlockDeficient
        (fun x => 2 ^ exponent x)
        (enlargedProjectedCandidateBlock C exponent)
        W := by
    unfold BlockDeficient
    rw [hWunion,hWSum]
    simp only [Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_bool]
    have hpos : 0 < 2 ^ exponent w := by positivity
    omega
  exact hmin W hWproper hWdef

#print axioms four_secondLayer_demand_eq_cube
#print axioms minimal_deficient_four_secondLayer_union_eq_univ_of_proper
#print axioms minimal_deficient_core_card_le_five_of_four_secondLayer

end OrderedEdgeColoring
end JSP000404Research
