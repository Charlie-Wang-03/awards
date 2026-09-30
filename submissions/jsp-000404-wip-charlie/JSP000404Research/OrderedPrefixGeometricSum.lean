import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# Geometric sum from ordered prefix ranks

Let S be a finite subset of a linear order. Suppose an integer parameter a(v)
dominates the prefix rank of every v in S,

  card {u in S | u <= v} <= a(v) <= n.

Then

  sum_{v in S} 2^(n-a(v))
    <= 2^n - 2^(n-card S).

The proof removes the maximum element. Its prefix rank is card S, while all
earlier prefix ranks are unchanged after deletion. Strong induction on card S
then gives the exact finite geometric-series bound.
-/

namespace JSP000404Research

theorem ordered_prefix_geometric_sum_bound
    {V : Type*} [LinearOrder V]
    (S : Finset V)
    (a : V → ℕ)
    (n : ℕ)
    (haN : ∀ v ∈ S, a v ≤ n)
    (hrank :
      ∀ v ∈ S,
        (S.filter fun u => u ≤ v).card ≤ a v) :
    (∑ v ∈ S, 2 ^ (n - a v))
      ≤
    2 ^ n - 2 ^ (n - S.card) := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h m ih =>
      by_cases hS : S.Nonempty
      · let M := S.max' hS
        have hMmem : M ∈ S := Finset.max'_mem S hS
        let T := S.erase M
        have hTsub : T ⊆ S := Finset.erase_subset _ _
        have hMnotT : M ∉ T := by simp [T]
        have hcardT : T.card + 1 = S.card := by
          rw [← Finset.card_erase_add_one hMmem]
          rfl
        have hTlt : T.card < m := by
          rw [← hcard]
          omega
        have hmax :
            ∀ x ∈ T, x ≤ M := by
          intro x hx
          exact Finset.le_max' S x (hTsub hx)
        have hprefixM :
            (S.filter fun u => u ≤ M) = S := by
          apply Finset.filter_eq_self.2
          intro x hx
          exact Finset.le_max' S x hx
        have haM : S.card ≤ a M := by
          have h := hrank M hMmem
          rw [hprefixM] at h
          exact h
        have haMN : a M ≤ n := haN M hMmem
        have hcardN : S.card ≤ n := haM.trans haMN
        have htermM :
            2 ^ (n - a M) ≤ 2 ^ (n - S.card) := by
          apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
          omega

        have hprefixT :
            ∀ v ∈ T,
              (T.filter fun u => u ≤ v).card =
                (S.filter fun u => u ≤ v).card := by
          intro v hv
          have hvleM := hmax v hv
          have hvneM : v ≠ M := by
            intro h
            subst v
            exact hMnotT hv
          have hvltM : v < M := lt_of_le_of_ne hvleM hvneM
          apply congrArg Finset.card
          apply Finset.ext
          intro x
          constructor
          · intro hx
            have hxData := Finset.mem_filter.mp hx
            exact Finset.mem_filter.mpr
              ⟨hTsub hxData.1, hxData.2⟩
          · intro hx
            have hxData := Finset.mem_filter.mp hx
            have hxneM : x ≠ M := by
              intro h
              subst x
              exact (not_le_of_gt hvltM) hxData.2
            have hxT : x ∈ T :=
              Finset.mem_erase.mpr ⟨hxneM,hxData.1⟩
            exact Finset.mem_filter.mpr ⟨hxT,hxData.2⟩

        have haNT :
            ∀ v ∈ T, a v ≤ n := by
          intro v hv
          exact haN v (hTsub hv)
        have hrankT :
            ∀ v ∈ T,
              (T.filter fun u => u ≤ v).card ≤ a v := by
          intro v hv
          rw [hprefixT v hv]
          exact hrank v (hTsub hv)
        have ihT :
            (∑ v ∈ T, 2 ^ (n - a v))
              ≤
            2 ^ n - 2 ^ (n - T.card) :=
          ih T.card hTlt T rfl haNT hrankT

        have hsumSplit :
            (∑ v ∈ S, 2 ^ (n - a v)) =
              2 ^ (n - a M) +
                ∑ v ∈ T, 2 ^ (n - a v) := by
          rw [← Finset.sum_erase_add _ hMmem]
          rfl

        have hpowStep :
            2 ^ (n - T.card) =
              2 * 2 ^ (n - S.card) := by
          have hTcardLtN : T.card < n := by
            omega
          have hsub :
              n - T.card = (n - S.card) + 1 := by
            omega
          rw [hsub, pow_succ]
          omega

        rw [hsumSplit]
        omega
      · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simp

#print axioms ordered_prefix_geometric_sum_bound

end JSP000404Research
