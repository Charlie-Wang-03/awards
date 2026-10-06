import JSP000404Research.ProjectionThreeWholeCubeForceThreeSupportTwo
import JSP000404Research.QTTTThreeSupportSmallPairMatching
import Mathlib.Tactic

/-!
# Eleven-state geometric terminal for the saturated three-whole-cube star

For n >= 4 the saturated three-whole-cube four-vertex terminal contains at
least three support-two centres.  Selecting any such three and the unique
remaining fourth vertex, the general three-support-two small-pair reduction
places the configuration in one of eleven explicit crossed small-pair states.

This is the finite geometric terminal that remains after the whole-cube
recursion has saturated.
-/

namespace JSP000404Research

theorem four_insert_three_distinct_has_fourth
    {V : Type*} [DecidableEq V]
    {v s₁ s₂ s₃ a b c : V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
    (ha : a ∈ ({v,s₁,s₂,s₃} : Finset V))
    (hb : b ∈ ({v,s₁,s₂,s₃} : Finset V))
    (hc : c ∈ ({v,s₁,s₂,s₃} : Finset V))
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∃ d : V,
      d ∈ ({v,s₁,s₂,s₃} : Finset V) ∧
      a ≠ d ∧ b ≠ d ∧ c ≠ d := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    simp_all
  all_goals
    first
    | exact ⟨v,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨s₁,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨s₂,by simp,by simp_all,by simp_all,by simp_all⟩
    | exact ⟨s₃,by simp,by simp_all,by simp_all,by simp_all⟩

namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCubePartners_eleven_state_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs1Loss :
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs2Loss :
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs3Loss :
      s₃ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃) :
    ∃ a b c d : ProjectionOrdered V,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      b ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      c ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      d ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      positiveSupport (centreQuotient (Cfam a) t) = 2 ∧
      positiveSupport (centreQuotient (Cfam b) t) = 2 ∧
      positiveSupport (centreQuotient (Cfam c) t) = 2 ∧
      ThreeSupportTwoCrossedPattern11
        (reindexedPoint p) delta lam a b c d := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp

  obtain ⟨a,b,c,hab,hac,hbc,
      haMem,hbMem,hcMem,haSup,hbSup,hcSup⟩ :=
    planar_threeWholeCubePartners_force_three_supportTwo
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hc12 hc13 hc23 hactive
      hvLoss hs1Loss hs2Loss hs3Loss
      hvSecond hs1Second hs2Second hs3Second
      h₁ h₂ h₃

  obtain ⟨d,hdMem,had,hbd,hcd⟩ :=
    four_insert_three_distinct_has_fourth
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      haMem hbMem hcMem hab hac hbc

  have second_of_mem :
      ∀ {q : ProjectionOrdered V},
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        centreExponent (Cfam q) t = n - 2 := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvSecond
    · exact hs1Second
    · exact hs2Second
    · exact hs3Second

  have hcapR :
      AngleCap (reindexedPoint p) lam := by
    intro x y z hxy hxz hyz
    exact hcap x.toOriginal y.toOriginal z.toOriginal
      (by
        intro h
        apply hxy
        exact ProjectionOrdered.toOriginal_injective h)
      (by
        intro h
        apply hxz
        exact ProjectionOrdered.toOriginal_injective h)
      (by
        intro h
        apply hyz
        exact ProjectionOrdered.toOriginal_injective h)

  have hpattern :=
    three_supportTwo_secondLayer_four_reduce_to_eleven
      (reindexedPoint_injective hp)
      hcapR
      (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam
      hab hac had hbc hbd hcd
      Cfam
      (second_of_mem haMem)
      (second_of_mem hbMem)
      (second_of_mem hcMem)
      haSup hbSup hcSup

  exact ⟨a,b,c,d,
    hab,hac,had,hbc,hbd,hcd,
    haMem,hbMem,hcMem,hdMem,
    haSup,hbSup,hcSup,hpattern⟩

#print axioms four_insert_three_distinct_has_fourth
#print axioms planar_threeWholeCubePartners_eleven_state_terminal

end ProjectionOrdered
end JSP000404Research
