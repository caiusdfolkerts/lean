module

public import PaperVerification.JacobianEquivariantSection
public import PaperVerification.JacobianLinearAction
public import PaperVerification.EquivariantTowers
public import PaperVerification.GradedTowers
public import PaperVerification.NegativeQuotientGrading

/-!
# The equivariant Milnor-tower decomposition

The group acts by arbitrary invertible linear coordinate transformations that
preserve the potential and coordinate weights. The section and tower map are
constructed. The source is the direct sum over all nonnegative powers of the
potential, with the natural action on each Milnor summand.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module Polynomial

namespace PaperVerification.JacobianDivergence

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G]

theorem exists_actual_equivariant_milnor_section {n : ℕ}
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K)) :
    ∃ s : MilnorQuotient F →ₗ[K] MvPolynomial (Fin n) K,
      (∀ x, (jacobianSubmodule F).mkQ (s x) = x) ∧
      (∀ g x, s (JacobianLinearAction.milnorRepresentation ρ F hFix g x) =
        JacobianLinearAction.polynomialRepresentation ρ g (s x)) ∧
      ∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        (s x).IsWeightedHomogeneous w d := by
  let hJ : ∀ g p, p ∈ jacobianSubmodule F →
      JacobianLinearAction.polynomialRepresentation ρ g p ∈ jacobianSubmodule F :=
    fun g p hp => JacobianLinearAction.linearSubst_mem_jacobianSubmodule
      (ρ g⁻¹) F (hFix g⁻¹) p hp
  have haction : milnorAction F (JacobianLinearAction.polynomialRepresentation ρ) hJ =
      JacobianLinearAction.milnorRepresentation ρ F hFix := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨p, rfl⟩ := (jacobianSubmodule F).mkQ_surjective x
    simp only [milnorAction, QuotientLinearAction.action_mkQ,
      JacobianLinearAction.milnorRepresentation_mk]
  obtain ⟨s, hsq, hsG, hsgrade⟩ := exists_equivariant_homogeneous_milnor_section
    F w h hF (JacobianLinearAction.polynomialRepresentation ρ) hJ
    (fun g d p hp => JacobianLinearAction.polynomialRepresentation_preserves_weights
      ρ w hW g hp)
  rw [haction] at hsG
  exact ⟨s, hsq, hsG, hsgrade⟩

/-- The full (unbounded) tower decomposition with the actual finite-group
actions. Gradient regularity is the explicit algebraic input here; the
isolated-hypersurface wrapper below derives it from the paper's hypothesis. -/
theorem equivariant_milnor_towers_of_regular {n : ℕ}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K)) :
    ∃ (s : MilnorQuotient F →ₗ[K] MvPolynomial (Fin n) K)
      (e : (ℕ →₀ MilnorQuotient F) ≃ₗ[K] BrieskornModule F),
      (∀ x, (jacobianSubmodule F).mkQ (s x) = x) ∧
      (∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        (s x).IsWeightedHomogeneous w d) ∧
      (∀ j x, e (Finsupp.single j x) = classOf F (F ^ j * s x)) ∧
      TauCeti.LinearMap.IsHomogeneous e.toLinearMap
        (GradedTowers.sourceGrading (milnorNegativeGrading F w h hF) h).piece
        (brieskornGrading F w h hF).piece 0 ∧
      ∀ g x, e (EquivariantTowers.sourceAction
        (JacobianLinearAction.milnorRepresentation ρ F hFix) g x) =
          JacobianLinearAction.brieskornRepresentation ρ F hFix g (e x) := by
  classical
  obtain ⟨s, hsq, hsG, hsgrade⟩ :=
    exists_actual_equivariant_milnor_section F w h hF ρ hFix hW
  obtain ⟨I, b, B, hb, hrep⟩ := exists_homogeneous_milnor_basis F w
  choose degree hdegree using hb
  have hBcomponent (i : I) :
      B i ∈ EulerResonance.quotientComponent w (degree i) (jacobianSubmodule F) := by
    rw [EulerResonance.quotientComponent_eq_map]
    exact ⟨b i, hdegree i, hrep i⟩
  obtain ⟨Bpol, hBpol⟩ := homogeneous_milnor_basis_lifts hn F w h hw hh hF hreg
    (fun i => s (B i)) (fun i => ⟨degree i, hsgrade _ _ (hBcomponent i)⟩)
    B (fun i => hsq (B i))
  let T : Module.End K (BrieskornModule F) :=
    Algebra.lsmul K K (BrieskornModule F) (Polynomial.X : K[X])
  let sv := (classOf F).comp s
  let C := GradedComponentBasis.towerBasis Bpol
  have hC (a : ℕ × I) : C a = (T ^ a.1) (sv (B a.2)) := by
    rw [GradedComponentBasis.towerBasis_apply, hBpol]
    dsimp only [T, sv, LinearMap.comp_apply]
    rw [← map_pow, Algebra.lsmul_apply]
  let e := EquivariantTowers.extensionEquiv T sv B C hC
  refine ⟨s, e, hsq, hsgrade, ?_, ?_, ?_⟩
  · intro j x
    change EquivariantTowers.extension T sv (Finsupp.single j x) = _
    rw [EquivariantTowers.extension_single]
    dsimp only [T, sv, LinearMap.comp_apply]
    rw [← map_pow, Algebra.lsmul_apply, X_pow_smul_classOf]
  · change TauCeti.LinearMap.IsHomogeneous (EquivariantTowers.extension T sv) _ _ 0
    apply GradedTowers.extension_isHomogeneous
    · intro p x hx
      change (Polynomial.X : K[X]) • x ∈ _
      exact parameter_homogeneous F w h hF hx
    · intro p x hx
      exact classOf_section_homogeneous F w h hF s hsgrade p x hx
  · intro g x
    apply EquivariantTowers.extensionEquiv_intertwines
      (JacobianLinearAction.brieskornRepresentation ρ F hFix)
      (JacobianLinearAction.milnorRepresentation ρ F hFix) T sv B C hC
    · intro a y
      exact JacobianLinearAction.brieskornRepresentation_polynomial_smul
        ρ F hFix a Polynomial.X y
    · intro a y
      change classOf F (s (JacobianLinearAction.milnorRepresentation ρ F hFix a y)) =
        JacobianLinearAction.brieskornRepresentation ρ F hFix a (classOf F (s y))
      rw [hsG, JacobianLinearAction.brieskornRepresentation_classOf]

/-- The same construction under the paper's isolated complex hypersurface
hypotheses, with no supplied regularity, basis or equivariant section. -/
theorem hypersurface_equivariant_milnor_towers {n : ℕ}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) (h : ℕ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (ρ : G →* (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) ℂ) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (s : MilnorQuotient F →ₗ[ℂ] MvPolynomial (Fin n) ℂ)
      (e : (ℕ →₀ MilnorQuotient F) ≃ₗ[ℂ] BrieskornModule F),
      (∀ x, (jacobianSubmodule F).mkQ (s x) = x) ∧
      (∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        (s x).IsWeightedHomogeneous w d) ∧
      (∀ j x, e (Finsupp.single j x) = classOf F (F ^ j * s x)) ∧
      TauCeti.LinearMap.IsHomogeneous e.toLinearMap
        (GradedTowers.sourceGrading (milnorNegativeGrading F w h hF) h).piece
        (brieskornGrading F w h hF).piece 0 ∧
      ∀ g x, e (EquivariantTowers.sourceAction
        (JacobianLinearAction.milnorRepresentation ρ F hFix) g x) =
          JacobianLinearAction.brieskornRepresentation ρ F hFix g (e x) :=
  equivariant_milnor_towers_of_regular hn F w h hw hh hF
    (gradient_regular_of_isolated F w h hw hF hiso) ρ hFix hW

end PaperVerification.JacobianDivergence
