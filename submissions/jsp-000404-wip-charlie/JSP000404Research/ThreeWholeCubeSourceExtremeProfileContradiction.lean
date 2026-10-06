import JSP000404Research.ThreeWholeCubeInteriorProfileContradictionCore
import Mathlib.Tactic

/-!
# Source-extreme 000 / 111 support-two contradiction

If the whole-cube source is a projected-loss global minimum, its three active
retained bits are all false.  Flipping the three distinct owner coordinates
gives partner profiles 100, 010, 001.  At those three support-two partners,
the two false coordinates are outgoing and the true coordinate is incoming,
so the same-orientation support-two lemma forces all three owner pairs to be
one-step close.

The global-maximum profile 111 is dual: the partner profiles are 011, 101,
110 and the two true coordinates are incoming.

Three distinct natural labels cannot be pairwise one-step close.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

private theorem fin_val_ne_extreme
    {n : ℕ} {x y : Fin n}
    (hxy : x ≠ y) :
    x.val ≠ y.val := by
  intro h
  apply hxy
  exact Fin.ext h

theorem source_000_profile_supportTwo_impossible
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {x,y,z})
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v x)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v y)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v z)
    (hs1Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₁) t = n - 2)
    (hs2Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₂) t = n - 2)
    (hs3Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₃) t = n - 2)
    (hs1Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (hxFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v x = false)
    (hyFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v y = false)
    (hzFalse :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v z = false) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R v = {x,y,z} := by simpa [R] using hactive
  have h1' : WholeCubeQTPair R s₁ v x := by simpa [R] using h₁
  have h2' : WholeCubeQTPair R s₂ v y := by simpa [R] using h₂
  have h3' : WholeCubeQTPair R s₃ v z := by simpa [R] using h₃
  have hxFalse' : retainedBit R v x = false := by simpa [R] using hxFalse
  have hyFalse' : retainedBit R v y = false := by simpa [R] using hyFalse
  have hzFalse' : retainedBit R v z = false := by simpa [R] using hzFalse

  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp
  have hstar := threeWholeCubePartners_retainedCode_star
    R hxV hyV hzV h1' h2' h3'

  have hyS1 : y ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hyV
  have hzS1 : z ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hzV
  have hxS1 : x ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hxV
  have hxS2 : x ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hxV
  have hzS2 : z ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hzV
  have hyS2 : y ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hyV
  have hxS3 : x ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hxV
  have hyS3 : y ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hyV
  have hzS3 : z ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hzV

  have hxS1True : retainedBit R s₁ x = true := by
    have h := hstar.1.2.1
    rw [hxFalse'] at h
    simpa using h
  have hyS1False : retainedBit R s₁ y = false :=
    (hstar.1.2.2 y hyV hxy.symm).trans hyFalse'
  have hzS1False : retainedBit R s₁ z = false :=
    (hstar.1.2.2 z hzV hxz.symm).trans hzFalse'

  have hxS2False : retainedBit R s₂ x = false :=
    (hstar.2.1.2.2 x hxV hxy).trans hxFalse'
  have hyS2True : retainedBit R s₂ y = true := by
    have h := hstar.2.1.2.1
    rw [hyFalse'] at h
    simpa using h
  have hzS2False : retainedBit R s₂ z = false :=
    (hstar.2.1.2.2 z hzV hyz.symm).trans hzFalse'

  have hxS3False : retainedBit R s₃ x = false :=
    (hstar.2.2.2.2 x hxV hxz).trans hxFalse'
  have hyS3False : retainedBit R s₃ y = false :=
    (hstar.2.2.2.2 y hyV hyz).trans hyFalse'
  have hzS3True : retainedBit R s₃ z = true := by
    have h := hstar.2.2.2.1
    rw [hzFalse'] at h
    simpa using h

  have hYZ :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₁) hs1Second hs1Support hyz
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hyS1 hyS1False)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hzS1 hzS1False)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₁ x).2 hxS1True)

  have hXZ :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₂) hs2Second hs2Support hxz
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hxS2 hxS2False)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hzS2 hzS2False)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₂ y).2 hyS2True)

  have hXY :=
    supportTwo_two_outgoing_one_incoming_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₃) hs3Second hs3Support hxy
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hxS3 hxS3False)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hyS3 hyS3False)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₃ z).2 hzS3True)

  exact three_distinct_pairwise_oneStep_impossible
    x.val y.val z.val
    (fin_val_ne_extreme hxy) (fin_val_ne_extreme hxz) (fin_val_ne_extreme hyz)
    hXY hXZ hYZ

theorem source_111_profile_supportTwo_impossible
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    {x y z : Fin n}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {x,y,z})
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v x)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v y)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v z)
    (hs1Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₁) t = n - 2)
    (hs2Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₂) t = n - 2)
    (hs3Second :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      centreExponent (Cfam s₃) t = n - 2)
    (hs1Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (hxTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v x = true)
    (hyTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v y = true)
    (hzTrue :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedBit R v z = true) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith
  let R :=
    planarStandardResidualColoring
      hp hcap hn1 hdelta0 hdelta1 ht hlam

  have hactive' : retainedActive R v = {x,y,z} := by simpa [R] using hactive
  have h1' : WholeCubeQTPair R s₁ v x := by simpa [R] using h₁
  have h2' : WholeCubeQTPair R s₂ v y := by simpa [R] using h₂
  have h3' : WholeCubeQTPair R s₃ v z := by simpa [R] using h₃
  have hxTrue' : retainedBit R v x = true := by simpa [R] using hxTrue
  have hyTrue' : retainedBit R v y = true := by simpa [R] using hyTrue
  have hzTrue' : retainedBit R v z = true := by simpa [R] using hzTrue

  have hxV : x ∈ retainedActive R v := by rw [hactive']; simp
  have hyV : y ∈ retainedActive R v := by rw [hactive']; simp
  have hzV : z ∈ retainedActive R v := by rw [hactive']; simp
  have hstar := threeWholeCubePartners_retainedCode_star
    R hxV hyV hzV h1' h2' h3'

  have hxS1 : x ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hxV
  have hyS1 : y ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hyV
  have hzS1 : z ∈ retainedActive R s₁ := by rw [hstar.1.1]; exact hzV
  have hxS2 : x ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hxV
  have hyS2 : y ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hyV
  have hzS2 : z ∈ retainedActive R s₂ := by rw [hstar.2.1.1]; exact hzV
  have hxS3 : x ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hxV
  have hyS3 : y ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hyV
  have hzS3 : z ∈ retainedActive R s₃ := by rw [hstar.2.2.1]; exact hzV

  have hxS1False : retainedBit R s₁ x = false := by
    have h := hstar.1.2.1
    rw [hxTrue'] at h
    simpa using h
  have hyS1True : retainedBit R s₁ y = true :=
    (hstar.1.2.2 y hyV hxy.symm).trans hyTrue'
  have hzS1True : retainedBit R s₁ z = true :=
    (hstar.1.2.2 z hzV hxz.symm).trans hzTrue'

  have hxS2True : retainedBit R s₂ x = true :=
    (hstar.2.1.2.2 x hxV hxy).trans hxTrue'
  have hyS2False : retainedBit R s₂ y = false := by
    have h := hstar.2.1.2.1
    rw [hyTrue'] at h
    simpa using h
  have hzS2True : retainedBit R s₂ z = true :=
    (hstar.2.1.2.2 z hzV hyz.symm).trans hzTrue'

  have hxS3True : retainedBit R s₃ x = true :=
    (hstar.2.2.2.2 x hxV hxz).trans hxTrue'
  have hyS3True : retainedBit R s₃ y = true :=
    (hstar.2.2.2.2 y hyV hyz).trans hyTrue'
  have hzS3False : retainedBit R s₃ z = false := by
    have h := hstar.2.2.2.1
    rw [hzTrue'] at h
    simpa using h

  have hYZ :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₁) hs1Second hs1Support hyz
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₁ y).2 hyS1True)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₁ z).2 hzS1True)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hxS1 hxS1False)

  have hXZ :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₂) hs2Second hs2Support hxz
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₂ x).2 hxS2True)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₂ z).2 hzS2True)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hyS2 hyS2False)

  have hXY :=
    supportTwo_two_incoming_one_outgoing_labels_oneStep
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      (Cfam s₃) hs3Second hs3Support hxy
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₃ x).2 hxS3True)
      (by simpa [R] using
        (mem_incomingRetained_iff_retainedBit_true_light R s₃ y).2 hyS3True)
      (by simpa [R] using
        mem_outgoingRetained_of_mem_retainedActive_bit_false R hzS3 hzS3False)

  exact three_distinct_pairwise_oneStep_impossible
    x.val y.val z.val
    (fin_val_ne_extreme hxy) (fin_val_ne_extreme hxz) (fin_val_ne_extreme hyz)
    hXY hXZ hYZ

#print axioms source_000_profile_supportTwo_impossible
#print axioms source_111_profile_supportTwo_impossible

end ProjectionOrdered
end JSP000404Research
