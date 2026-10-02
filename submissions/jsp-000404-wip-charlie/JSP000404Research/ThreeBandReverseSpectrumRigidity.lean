import JSP000404Research.ThreeBandSpectrumRigidity
import Mathlib.Tactic

/-!
# Reverse spectrum rigidity for three consecutive occupied bands

If a sorted natural band-label list occupies exactly {m,m+1,m+2}, then every
ordinary consecutive jump is 0 or 1 and the cyclic wrap jump is n-1 (provided
all three bands are below the residual top n).

Thus its cyclic band-jump spectrum is contained in {0,1,n-1}.  This is the
reverse companion to ThreeBandSpectrumRigidity.
-/

namespace JSP000404Research

theorem successiveNatDiffs_three_consecutive_spectrum
    {m a : ℕ} {xs : List ℕ}
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hset : (a :: xs).toFinset = {m,m+1,m+2}) :
    ∀ b ∈ successiveNatDiffsFrom a xs,
      b = 0 ∨ b = 1 := by
  intro b hb
  induction xs generalizing a with
  | nil =>
      simp [successiveNatDiffsFrom] at hb
  | cons x xs ih =>
      simp only [successiveNatDiffsFrom, List.mem_cons] at hb
      have hpair := List.pairwise_cons.mp hsorted
      have hax : a ≤ x := hpair.1 x (by simp)
      have haMem : a ∈ ({m,m+1,m+2} : Finset ℕ) := by
        rw [← hset]
        simp
      have hxMem : x ∈ ({m,m+1,m+2} : Finset ℕ) := by
        rw [← hset]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at haMem hxMem
      rcases hb with rfl | hbTail
      · rcases haMem with rfl | rfl | rfl <;>
          rcases hxMem with rfl | rfl | rfl <;>
          simp_all <;> omega
      · have htailSet :
            (x :: xs).toFinset ⊆ ({m,m+1,m+2} : Finset ℕ) := by
          intro q hq
          rw [← hset]
          simp only [List.toFinset_cons, Finset.mem_insert] at hq ⊢
          exact Or.inr hq
        -- A jump of two inside the sorted tail would skip the occupied middle
        -- band globally.  We retain the original set equality to rule this out.
        have hglobalMem :
            m+1 ∈ (a :: x :: xs).toFinset := by
          rw [hset]
          simp
        have htailSorted :
            (x :: xs).Pairwise (· ≤ ·) := hpair.2
        have ih' :=
          ih x htailSorted
        -- If the tail itself no longer contains all three labels, the induction
        -- hypothesis's equality premise is unavailable.  Prove the local
        -- adjacent bound directly from sortedness plus existence of m+1.
        clear ih'
        induction xs generalizing x with
        | nil =>
            simp [successiveNatDiffsFrom] at hbTail
        | cons y ys ih2 =>
            simp only [successiveNatDiffsFrom, List.mem_cons] at hbTail
            have hp2 := List.pairwise_cons.mp htailSorted
            have hxy : x ≤ y := hp2.1 y (by simp)
            have hxG : x ∈ ({m,m+1,m+2} : Finset ℕ) := by
              apply htailSet
              simp
            have hyG : y ∈ ({m,m+1,m+2} : Finset ℕ) := by
              apply htailSet
              simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxG hyG
            rcases hbTail with rfl | hrest
            · rcases hxG with rfl | rfl | rfl <;>
                rcases hyG with rfl | rfl | rfl <;>
                simp_all <;>
                try { omega }
              -- The sole apparent jump 2 is m -> m+2.  It contradicts the
              -- presence of m+1 in the sorted full list.
              have hm1 :
                  m+1 ∈ a :: x :: y :: ys := by
                simpa using hglobalMem
              simp only [List.mem_cons] at hm1
              rcases hm1 with ha1 | hx1 | hy1 | hys1
              · omega
              · omega
              · omega
              · have hy_le :
                    y ≤ m+1 :=
                  (List.pairwise_cons.mp hp2.2).1 (m+1) hys1
                omega
            · exact ih2 y hp2.2
                (by
                  intro q hq
                  apply htailSet
                  simp [hq])
                hrest

theorem cyclicBandJumps_three_consecutive_spectrum
    {n m a : ℕ} {xs : List ℕ}
    (hn3 : 3 ≤ n)
    (hsorted : (a :: xs).Pairwise (· ≤ ·))
    (hset : (a :: xs).toFinset = {m,m+1,m+2})
    (hbelow : m + 2 ≤ n - 1) :
    ∀ b ∈ cyclicBandJumps n (a :: xs),
      b = 0 ∨ b = 1 ∨ b = n - 1 := by
  intro b hb
  unfold cyclicBandJumps at hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with hsucc | hwrap
  · have h :=
      successiveNatDiffs_three_consecutive_spectrum
        hsorted hset b hsucc
    rcases h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  · right; right
    subst b
    have haMem : a ∈ ({m,m+1,m+2} : Finset ℕ) := by
      rw [← hset]
      simp
    have hlastMem :
        xs.getLastD a ∈ ({m,m+1,m+2} : Finset ℕ) := by
      rw [← hset]
      exact List.getLastD_mem_cons a xs
    have hboundsA :=
      mem_between_head_last_of_pairwise_nat
        a xs hsorted a (by simp)
    have hboundsLast :=
      mem_between_head_last_of_pairwise_nat
        a xs hsorted (xs.getLastD a)
        (List.getLastD_mem_cons a xs)
    simp only [Finset.mem_insert, Finset.mem_singleton] at haMem hlastMem
    -- Sortedness and occupancy of all three labels force first=m,last=m+2.
    have hmMem : m ∈ a :: xs := by
      have : m ∈ (a :: xs).toFinset := by rw [hset]; simp
      simpa using this
    have hm2Mem : m+2 ∈ a :: xs := by
      have : m+2 ∈ (a :: xs).toFinset := by rw [hset]; simp
      simpa using this
    have ha_le_m :=
      (mem_between_head_last_of_pairwise_nat
        a xs hsorted m hmMem).1
    have hm2_le_last :=
      (mem_between_head_last_of_pairwise_nat
        a xs hsorted (m+2) hm2Mem).2
    have ha_ge_m : m ≤ a := by
      rcases haMem with rfl | rfl | rfl <;> omega
    have hlast_le : xs.getLastD a ≤ m+2 := by
      rcases hlastMem with h | h | h <;> omega
    have haEq : a = m := by omega
    have hlastEq : xs.getLastD a = m+2 := by omega
    rw [haEq, hlastEq]
    omega

#print axioms successiveNatDiffs_three_consecutive_spectrum
#print axioms cyclicBandJumps_three_consecutive_spectrum

end JSP000404Research
