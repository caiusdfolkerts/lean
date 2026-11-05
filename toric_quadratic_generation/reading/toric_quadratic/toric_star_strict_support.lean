module
public import PaperVerification.ToricStarSubdivision
public import PaperVerification.ToricStrictSupportFaces
public import Mathlib.Tactic.NormNum
@[expose] public section

/-!
# Strict convex support survives smooth star subdivision

The new coefficient on the exceptional ray is the sum of the old focus
coefficients minus one common sufficiently small positive real parameter.
All supporting linear forms and every strict inequality are constructed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def starCoefficientBase {n : ℕ} (a : Lattice n → ℝ) (t : Finset (Lattice n)) :
    Lattice n → ℝ := fun v => if v = ∑ w ∈ t, w then ∑ w ∈ t, a w else a v

def starCoefficientSlope {n : ℕ} (t : Finset (Lattice n)) : Lattice n → ℝ :=
  fun v => if v = ∑ w ∈ t, w then -1 else 0

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem starCandidates_subset_rays (t : Finset (Lattice n)) :
    ∀ s ∈ «Σ».starCandidates t, s ⊆ insert (∑ v ∈ t, v) «Σ».rays := by
  intro s hs
  rcases («Σ».mem_starCandidates t s).mp hs with ⟨hs, hts⟩ |
    ⟨u, hu, v, hv, htu, rfl⟩
  · intro v hv
    exact Finset.mem_insert_of_mem («Σ».ray_mem_of_mem_cone hs hv)
  · intro w hw
    rcases (mem_starRaySet u t v w).mp hw with rfl | ⟨_, hwu⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem («Σ».ray_mem_of_mem_cone hu hwu)

/-- On a cone not containing the focus, the sum ray has strictly positive
old supporting slack. -/
theorem supporting_sum_strict_of_not_subset (a : Lattice n → ℝ)
    {s t : Finset (Lattice n)} (ht : t ∈ «Σ».cones) (hts : ¬ t ⊆ s)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ v ∈ s, ℓ (embed n v) = a v)
    (hlt : ∀ v ∈ «Σ».rays, v ∉ s → ℓ (embed n v) < a v) :
    ℓ (embed n (∑ v ∈ t, v)) < ∑ v ∈ t, a v := by
  rw [map_sum, map_sum]
  apply Finset.sum_lt_sum
  · intro v hv
    by_cases hvs : v ∈ s
    · exact (heq v hvs).le
    · exact (hlt v («Σ».ray_mem_of_mem_cone ht hv) hvs).le
  · obtain ⟨v, hv, hvs⟩ := Finset.not_subset.mp hts
    exact ⟨v, hv, hlt v («Σ».ray_mem_of_mem_cone ht hv) hvs⟩

/-- Each candidate new cone admits two explicit linear forms whose
supporting slacks are lexicographically positive outside that cone. -/
theorem starCandidate_lexicographic_support
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hcard : 2 ≤ t.card) :
    ∀ c ∈ «Σ».starCandidates t, ∃ L₀ L₁ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ c, L₀ (embed n v) = starCoefficientBase a t v ∧
        L₁ (embed n v) = starCoefficientSlope t v) ∧
      (∀ v ∈ insert (∑ w ∈ t, w) «Σ».rays, v ∉ c →
        L₀ (embed n v) < starCoefficientBase a t v ∨
        (L₀ (embed n v) = starCoefficientBase a t v ∧
          L₁ (embed n v) < starCoefficientSlope t v)) := by
  let e := ∑ w ∈ t, w
  have he : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  have hcoeff (v : Lattice n) (hv : v ∈ «Σ».rays) :
      starCoefficientBase a t v = a v ∧ starCoefficientSlope t v = 0 := by
    have hve : v ≠ e := fun h => he (h ▸ hv)
    change v ≠ (∑ w ∈ t, w) at hve
    simp only [starCoefficientBase, starCoefficientSlope, if_neg hve, true_and]
  intro c hc
  rcases («Σ».mem_starCandidates t c).mp hc with ⟨hc, htc⟩ |
    ⟨s, hs, p, hp, hts, rfl⟩
  · obtain ⟨ℓ, heq, hlt⟩ := ha c hc
    refine ⟨ℓ, 0, ?_, ?_⟩
    · intro v hv
      obtain ⟨h₀, h₁⟩ := hcoeff v («Σ».ray_mem_of_mem_cone hc hv)
      exact ⟨(heq v hv).trans h₀.symm, by simp only [LinearMap.zero_apply, h₁]⟩
    · intro v hv hvc
      rcases Finset.mem_insert.mp hv with rfl | hv
      · left
        simpa only [starCoefficientBase, if_pos rfl, ite_true] using
          «Σ».supporting_sum_strict_of_not_subset a ht htc ℓ heq hlt
      · left
        rw [(hcoeff v hv).1]
        exact hlt v hv hvc
  · obtain ⟨ℓ, heq, hlt⟩ := ha s hs
    obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
    have hpJ : p ∈ J.image b := htJ ▸ hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hpJ
    let g : Ambient n →ₗ[ℝ] ℝ := -(integralBasisReal b).coord j
    have hgold (v : Lattice n) (hv : v ∈ s) :
        g (embed n v) = if v = p then -1 else 0 := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hsI ▸ hv)
      rw [← hpj, ← integralBasisReal_apply b i]
      simp only [g, LinearMap.neg_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, b.injective.ne hij]
    have heqsum : e = ∑ i ∈ J, b i := by
      change (∑ w ∈ t, w) = _
      rw [htJ, Finset.sum_image]
      exact fun i _ k _ hik => b.injective hik
    have hge : g (embed n e) = -1 := by
      rw [heqsum, map_sum]
      simp only [g, LinearMap.neg_apply, map_sum]
      simp [← integralBasisReal_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply, Finsupp.single_apply, hj]
    have hℓe : ℓ (embed n e) = ∑ v ∈ t, a v := by
      change ℓ (embed n (∑ v ∈ t, v)) = _
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl (fun v hv => heq v (hts hv))
    refine ⟨ℓ, g, ?_, ?_⟩
    · intro v hv
      rcases (mem_starRaySet s t p v).mp hv with hve | ⟨hvp, hvs⟩
      · subst v
        simpa only [e, starCoefficientBase, starCoefficientSlope, if_pos rfl,
          ite_true] using And.intro hℓe hge
      · obtain ⟨h₀, h₁⟩ := hcoeff v («Σ».ray_mem_of_mem_cone hs hvs)
        refine ⟨(heq v hvs).trans h₀.symm, ?_⟩
        rw [hgold v hvs, if_neg hvp, h₁]
    · intro v hv hvc
      have hve : v ≠ e := by
        intro h
        exact hvc ((mem_starRaySet s t p v).mpr (Or.inl h))
      have hvrays : v ∈ «Σ».rays := (Finset.mem_insert.mp hv).resolve_left hve
      obtain ⟨h₀, h₁⟩ := hcoeff v hvrays
      rw [h₀, h₁]
      by_cases hvs : v ∈ s
      · right
        have hvp : v = p := by
          by_contra hne
          exact hvc ((mem_starRaySet s t p v).mpr (Or.inr ⟨hne, hvs⟩))
        refine ⟨heq v hvs, ?_⟩
        rw [hgold v hvs, if_pos hvp]
        norm_num
      · exact Or.inl (hlt v hvrays hvs)

/-- Strict support survives a genuine smooth star subdivision. The new
exceptional coefficient is exactly `Σ a_v - ε`; every old ray coefficient
is unchanged because the sum ray is proved to be new. -/
theorem strictSupport_starSubdivision_all_small
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      («Σ».starSubdivision t ht hne).IsStrictSupport
      (fun v => starCoefficientBase a t v + ε * starCoefficientSlope t v) := by
  let C := «Σ».starCandidates t
  let R := insert (∑ v ∈ t, v) «Σ».rays
  have hcharts := «Σ».starCandidate_lexicographic_support a ha t ht hcard
  choose L₀ L₁ hactive hinactive using hcharts
  let K₀ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₀ s hs else 0
  let K₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₁ s hs else 0
  have heq : ∀ s ∈ C, ∀ v ∈ s,
      K₀ s (embed n v) = starCoefficientBase a t v ∧
      K₁ s (embed n v) = starCoefficientSlope t v := by
    intro s hs v hv
    simpa only [K₀, K₁, dif_pos hs] using hactive s hs v hv
  have hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      K₀ s (embed n v) < starCoefficientBase a t v ∨
      (K₀ s (embed n v) = starCoefficientBase a t v ∧
        K₁ s (embed n v) < starCoefficientSlope t v) := by
    intro s hs v hv hvs
    simpa only [K₀, K₁, dif_pos hs] using hinactive s hs v hv hvs
  obtain ⟨δ, hδ, hsupp⟩ := finite_lexicographic_support_perturbation_all_small
    C R (starCoefficientBase a t) (starCoefficientSlope t) K₀ K₁ heq hlex
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  apply strictSupport_fanOfFiniteSmoothCones C
    («Σ».starCandidates_smooth t) («Σ».starCandidates_intersection t ht)
    («Σ».starCandidates_cover t hne) R («Σ».starCandidates_subset_rays t)
  intro s hs
  exact ⟨K₀ s + ε • K₁ s, hsupp ε hε hεδ s hs⟩

theorem exists_strictSupport_starSubdivision
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ ε : ℝ, 0 < ε ∧ («Σ».starSubdivision t ht hne).IsStrictSupport
      (fun v => starCoefficientBase a t v + ε * starCoefficientSlope t v) := by
  obtain ⟨δ, hδ, hsmall⟩ := «Σ».strictSupport_starSubdivision_all_small a ha t ht hne hcard
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
