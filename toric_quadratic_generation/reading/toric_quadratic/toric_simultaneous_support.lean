module

public import PaperVerification.ToricSimultaneousCombinatorics
public import PaperVerification.ToricStarStrictSupport

@[expose] public section

/-!
# Support coefficients and strict support on simultaneous disjoint stars

Old coefficients are retained. At each new sum ray the coefficient is the
sum on its old focus minus the prescribed correction. A common sufficiently
small positive correction yields strict support on the constructed fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Pullback support with an independently prescribed correction at each
actual exceptional sum ray. The same expression applies over integers and
over reals. -/
def simultaneousSupport {n : ℕ} {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n)) (a : Lattice n → A) (t : ι → A) : Lattice n → A :=
  fun v => a v + ∑ i, if v = ∑ w ∈ T i, w then (∑ w ∈ T i, a w) - a v - t i else 0

theorem simultaneousSupport_of_not_sum {n : ℕ} {ι A : Type*}
    [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n)) (a : Lattice n → A) (t : ι → A)
    (v : Lattice n) (hv : ∀ i, v ≠ ∑ w ∈ T i, w) :
    simultaneousSupport T a t v = a v := by
  simp only [simultaneousSupport, hv, if_false, Finset.sum_const_zero, add_zero]

theorem simultaneousSupport_at_sum {n : ℕ} {ι A : Type*}
    [Fintype ι] [AddCommGroup A]
    (T : ι → Finset (Lattice n))
    (hinj : Function.Injective (fun i : ι => ∑ w ∈ T i, w))
    (a : Lattice n → A) (t : ι → A) (i : ι) :
    simultaneousSupport T a t (∑ w ∈ T i, w) = (∑ w ∈ T i, a w) - t i := by
  unfold simultaneousSupport
  have hs : (∑ j, if (∑ w ∈ T i, w) = ∑ w ∈ T j, w then
      (∑ w ∈ T j, a w) - a (∑ w ∈ T i, w) - t j else 0) =
      (∑ w ∈ T i, a w) - a (∑ w ∈ T i, w) - t i := by
    simp only [hinj.eq_iff]
    simp
  rw [hs]
  abel

theorem simultaneousSupport_parameter {n : ℕ} {ι : Type*} [Fintype ι]
    (T : ι → Finset (Lattice n))
    (hinj : Function.Injective (fun i : ι => ∑ w ∈ T i, w))
    (a : Lattice n → ℝ) (ε : ℝ) (v : Lattice n) :
    simultaneousSupport T a (fun _ => ε) v =
      simultaneousSupport T a 0 v + ε * simultaneousSupport T 0 1 v := by
  by_cases he : ∃ i, v = ∑ w ∈ T i, w
  · obtain ⟨i, rfl⟩ := he
    rw [simultaneousSupport_at_sum T hinj, simultaneousSupport_at_sum T hinj,
      simultaneousSupport_at_sum T hinj]
    simp [sub_eq_add_neg]
  · have hv : ∀ i, v ≠ ∑ w ∈ T i, w := by simpa only [not_exists] using he
    rw [simultaneousSupport_of_not_sum T _ _ v hv,
      simultaneousSupport_of_not_sum T _ _ v hv,
      simultaneousSupport_of_not_sum T _ _ v hv]
    simp

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i, T i ∈ «Σ».cones) (hne : ∀ i, (T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T) (hcard : ∀ i, 2 ≤ (T i).card)

include hT hcard in
theorem simultaneousSupport_old {A : Type*} [AddCommGroup A]
    (a : Lattice n → A) (t : ι → A) (v : Lattice n) (hv : v ∈ «Σ».rays) :
    simultaneousSupport T a t v = a v := by
  apply simultaneousSupport_of_not_sum
  intro i he
  exact «Σ».sum_rays_not_mem_rays (hT i) (hcard i) (he ▸ hv)

/-- A star chart has an explicitly chosen first-order linear perturbation,
with value minus one at the omitted pivot and zero at every other parent ray. -/
theorem star_chart_perturbation
    {U A : Finset (Lattice n)} (hU : U ∈ «Σ».cones) (hAU : A ⊆ U)
    {p : Lattice n} (hp : p ∈ A) :
    ∃ g : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ U, g (embed n v) = if v = p then -1 else 0) ∧
      g (embed n (∑ v ∈ A, v)) = -1 := by
  obtain ⟨b, I, J, hUI, hAJ, hJI⟩ := «Σ».adapted_basis_for_subcone hU hAU
  obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp (hAJ ▸ hp)
  let g : Ambient n →ₗ[ℝ] ℝ := -(integralBasisReal b).coord j
  have hgold (v : Lattice n) (hv : v ∈ U) :
      g (embed n v) = if v = p then -1 else 0 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hUI ▸ hv)
    rw [← hpj, ← integralBasisReal_apply b i]
    simp only [g, LinearMap.neg_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, b.injective.ne hij]
  refine ⟨g, hgold, ?_⟩
  rw [map_sum, map_sum]
  calc
    (∑ v ∈ A, g (embed n v)) = ∑ v ∈ A, if v = p then -1 else 0 :=
      Finset.sum_congr rfl (fun v hv => hgold v (hAU hv))
    _ = -1 := by simp [hp]

include hT hdisj hcard in
theorem simultaneousCandidate_lexicographic_support
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a) :
    ∀ C ∈ «Σ».simultaneousCandidates T, ∃ L₀ L₁ : Ambient n →ₗ[ℝ] ℝ,
      (∀ v ∈ C, L₀ (embed n v) = simultaneousSupport T a 0 v ∧
        L₁ (embed n v) = simultaneousSupport T 0 1 v) ∧
      (∀ v ∈ «Σ».rays ∪ Finset.univ.image (fun i : ι => ∑ w ∈ T i, w), v ∉ C →
        L₀ (embed n v) < simultaneousSupport T a 0 v ∨
        (L₀ (embed n v) = simultaneousSupport T a 0 v ∧
          L₁ (embed n v) < simultaneousSupport T 0 1 v)) := by
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  have hold (v : Lattice n) (hv : v ∈ «Σ».rays) :
      simultaneousSupport T a 0 v = a v ∧
        simultaneousSupport T (0 : Lattice n → ℝ) 1 v = 0 := by
    exact ⟨«Σ».simultaneousSupport_old T hT hcard a 0 v hv,
      «Σ».simultaneousSupport_old T hT hcard 0 1 v hv⟩
  have hnew (i : ι) :
      simultaneousSupport T a 0 (∑ v ∈ T i, v) = ∑ v ∈ T i, a v ∧
      simultaneousSupport T (0 : Lattice n → ℝ) 1 (∑ v ∈ T i, v) = -1 := by
    simp only [simultaneousSupport_at_sum T hinj, Pi.zero_apply, Pi.one_apply,
      Finset.sum_const_zero, sub_zero, zero_sub, true_and]
  intro C hC
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hC, hnone⟩ |
    ⟨i, U, hU, p, hp, hTU, rfl⟩
  · obtain ⟨ℓ, heq, hlt⟩ := ha C hC
    refine ⟨ℓ, 0, ?_, ?_⟩
    · intro v hv
      obtain ⟨h₀, h₁⟩ := hold v («Σ».ray_mem_of_mem_cone hC hv)
      exact ⟨(heq v hv).trans h₀.symm, by simp only [LinearMap.zero_apply, h₁]⟩
    · intro v hv hvC
      left
      rcases Finset.mem_union.mp hv with hv | hv
      · rw [(hold v hv).1]
        exact hlt v hv hvC
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        rw [(hnew i).1]
        exact «Σ».supporting_sum_strict_of_not_subset a (hT i) (hnone i) ℓ heq hlt
  · obtain ⟨ℓ, heq, hlt⟩ := ha U hU
    obtain ⟨g, hgold, hge⟩ := «Σ».star_chart_perturbation hU hTU hp
    have hℓe : ℓ (embed n (∑ v ∈ T i, v)) = ∑ v ∈ T i, a v := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl (fun v hv => heq v (hTU hv))
    refine ⟨ℓ, g, ?_, ?_⟩
    · intro v hv
      rcases (mem_starRaySet U (T i) p v).mp hv with hve | hv
      · subst v
        exact ⟨hℓe.trans (hnew i).1.symm, hge.trans (hnew i).2.symm⟩
      · obtain ⟨hvp, hvU⟩ := hv
        obtain ⟨h₀, h₁⟩ := hold v («Σ».ray_mem_of_mem_cone hU hvU)
        refine ⟨(heq v hvU).trans h₀.symm, ?_⟩
        rw [hgold v hvU, if_neg hvp, h₁]
    · intro v hv hvC
      rcases Finset.mem_union.mp hv with hv | hv
      · rw [(hold v hv).1, (hold v hv).2]
        by_cases hvU : v ∈ U
        · right
          have hvp : v = p := by
            by_contra hnot
            exact hvC ((mem_starRaySet U (T i) p v).mpr (Or.inr ⟨hnot, hvU⟩))
          refine ⟨heq v hvU, ?_⟩
          rw [hgold v hvU, if_pos hvp]
          norm_num
        · exact Or.inl (hlt v hv hvU)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        have hij : i ≠ j := by
          intro hh
          subst j
          exact hvC ((mem_starRaySet U (T i) p _).mpr (Or.inl rfl))
        left
        rw [(hnew j).1]
        have hjU : ¬ T j ⊆ U := fun hh => hdisj i j hij
          ⟨U, hU, Finset.union_subset hTU hh⟩
        exact «Σ».supporting_sum_strict_of_not_subset a (hT j) hjU ℓ heq hlt

include hcard in
/-- All sufficiently small common exceptional corrections give strict
support on the actual simultaneous subdivision. -/
theorem strictSupport_simultaneousSubdivision_all_small
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      («Σ».simultaneousSubdivision T hT hne hdisj).IsStrictSupport
        (simultaneousSupport T a (fun _ => ε)) := by
  let C := «Σ».simultaneousCandidates T
  let R := «Σ».rays ∪ Finset.univ.image (fun i : ι => ∑ w ∈ T i, w)
  have hcharts := «Σ».simultaneousCandidate_lexicographic_support T hT hdisj hcard a ha
  choose L₀ L₁ hactive hinactive using hcharts
  let K₀ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₀ s hs else 0
  let K₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ :=
    fun s => if hs : s ∈ C then L₁ s hs else 0
  have heq : ∀ s ∈ C, ∀ v ∈ s,
      K₀ s (embed n v) = simultaneousSupport T a 0 v ∧
      K₁ s (embed n v) = simultaneousSupport T 0 1 v := by
    intro s hs v hv
    simpa only [K₀, K₁, dif_pos hs] using hactive s hs v hv
  have hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      K₀ s (embed n v) < simultaneousSupport T a 0 v ∨
      (K₀ s (embed n v) = simultaneousSupport T a 0 v ∧
        K₁ s (embed n v) < simultaneousSupport T 0 1 v) := by
    intro s hs v hv hvs
    simpa only [K₀, K₁, dif_pos hs] using hinactive s hs v hv hvs
  obtain ⟨δ, hδ, hsmall⟩ := finite_lexicographic_support_perturbation_all_small
    C R (simultaneousSupport T a 0) (simultaneousSupport T 0 1) K₀ K₁ heq hlex
  have hinj := «Σ».simultaneous_sum_rays_injective T hT hdisj
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  refine strictSupport_fanOfFiniteSmoothCones C
    («Σ».simultaneousCandidates_smooth T)
    («Σ».simultaneousCandidates_intersection T hT hdisj)
    («Σ».simultaneousCandidates_cover T hne) R ?_
    (simultaneousSupport T a (fun _ => ε)) ?_
  · intro s hs v hv
    have hsnew : s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones := by
      apply (mem_finiteConeFamilyClosure C s).mpr
      exact ⟨s, hs, Finset.Subset.refl _⟩
    have hvr := («Σ».simultaneousSubdivision T hT hne hdisj).ray_mem_of_mem_cone hsnew hv
    simpa only [«Σ».simultaneous_rays_eq T hT hne hdisj hcard] using hvr
  · intro s hs
    refine ⟨K₀ s + ε • K₁ s, ?_⟩
    simpa only [simultaneousSupport_parameter T hinj a ε] using hsmall ε hε hεδ s hs

end SmoothCompleteFan

end PaperVerification.ToricGeometry
