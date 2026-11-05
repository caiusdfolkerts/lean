module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace EllipsoidVerification

/-- On a compact set, injectivity and invertible strict derivatives give a
uniform inverse Lipschitz estimate. The set need not be convex, nor does its
image need to be convex. The proof excludes the compact part outside a local
inverse chart before using its Lipschitz bound. -/
theorem compact_inverse_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {K : Set E} (hK : IsCompact K) (hF : ContinuousOn F K)
    (hinj : Set.InjOn F K)
    (hder : ∀ x ∈ K, ∃ A : E ≃L[ℝ] E, HasStrictFDerivAt F (A : E →L[ℝ] E) x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ L * ‖F x - F y‖ := by
  let g : E → E := Function.invFunOn F K
  have hg : ∀ x ∈ K, g (F x) = x := hinj.leftInvOn_invFunOn
  have hlocal : LocallyLipschitzOn (F '' K) g := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := hder x hx
    let P := hA.toOpenPartialHomeomorph F
    let I := hA.localInverse F A x
    obtain ⟨L, U, hU, hLip⟩ := hA.to_localInverse.exists_lipschitzOnWith
    have hclosed : IsClosed (F '' (K \ P.source)) :=
      ((hK.diff P.open_source).image_of_continuousOn
        (hF.mono Set.diff_subset)).isClosed
    have hxnot : F x ∉ F '' (K \ P.source) := by
      rintro ⟨y, hy, heq⟩
      have hyx := hinj hy.1 hx heq
      exact hy.2 (hyx.symm ▸ hA.mem_toOpenPartialHomeomorph_source)
    let V : Set E := U ∩ (F '' (K \ P.source))ᶜ ∩ (F '' K)
    refine ⟨L, V, ?_, ?_⟩
    · exact inter_mem (inter_mem (mem_nhdsWithin_of_mem_nhds hU)
        (mem_nhdsWithin_of_mem_nhds (hclosed.isOpen_compl.mem_nhds hxnot)))
        self_mem_nhdsWithin
    · have hgi (y : E) (hy : y ∈ V) : g y = I y := by
        have hyK : g y ∈ K := Function.invFunOn_mem hy.2
        have hyF : F (g y) = y := Function.invFunOn_eq hy.2
        have hyP : g y ∈ P.source := by
          by_contra h
          exact hy.1.2 ⟨g y, ⟨hyK, h⟩, hyF⟩
        have hleft := P.left_inv hyP
        change I (F (g y)) = g y at hleft
        rw [hyF] at hleft
        exact hleft.symm
      intro y hy z hz
      simpa only [hgi y hy, hgi z hz] using hLip hy.1.1 hz.1.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hK.image_of_continuousOn hF) hlocal
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro x hx y hy
  have h := hLip.dist_le_mul (F x) ⟨x, hx, rfl⟩ (F y) ⟨y, hy, rfl⟩
  rw [hg x hx, hg y hy, dist_eq_norm, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- A convenient finite-dimensional form of the compact estimate. No
quantitative lower bound on the derivative is assumed. -/
theorem compact_inverse_lipschitz_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → E} {K : Set E} (hK : IsCompact K)
    (hF : ∀ x ∈ K, ContDiffAt ℝ 1 F x) (hinj : Set.InjOn F K)
    (hder : ∀ x ∈ K, Function.Injective (fderiv ℝ F x)) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ L * ‖F x - F y‖ := by
  apply compact_inverse_lipschitz hK
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt) hinj
  intro x hx
  let A := (LinearEquiv.ofBijective (fderiv ℝ F x).toLinearMap
    ⟨hder x hx, LinearMap.injective_iff_surjective.mp (hder x hx)⟩).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  exact (hF x hx).hasStrictFDerivAt one_ne_zero

end EllipsoidVerification
