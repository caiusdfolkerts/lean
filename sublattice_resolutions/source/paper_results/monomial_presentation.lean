module
public import graph_foundation.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialPresentation -/
section

set_option autoImplicit false

/-!
# Recognizing a presentation by its standard monomial images

This is the algebraic last step of Proposition 2.2.  Division supplies a remainder;
linear independence of the images of its standard monomials forces a kernel
remainder to vanish.  The conclusion is the actual Gröbner-basis predicate and the
actual kernel of the polynomial algebra map.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial

variable {σ R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The exponents avoiding all nonzero leading monomials in a proposed relation set. -/
def RelationStandard (m : MonomialOrder σ) (G : Set (MvPolynomial σ R)) :
    Set (σ →₀ ℕ) := {c | ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c}

theorem isGroebnerBasis_kernel_of_independent
    (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (φ : MvPolynomial σ R →ₐ[R] A)
    (hG : ∀ g ∈ G, φ g = 0)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hind : LinearIndependent R
      (fun c : RelationStandard m G => φ (monomial c.val 1))) :
    m.IsGroebnerBasis G (RingHom.ker φ.toRingHom) := by
  let P := MvPolynomial.restrictSupport R (RelationStandard m G)
  let F : P →ₗ[R] A := φ.toLinearMap.comp P.subtype
  have hF : Function.Injective F := by
    apply LinearMap.injective_of_linearIndependent
      (MvPolynomial.basisRestrictSupport R (RelationStandard m G)).span_eq
    simpa [Function.comp_def, F, P] using hind
  have hker : G ⊆ RingHom.ker φ.toRingHom := fun g hg => hG g hg
  rw [MonomialOrder.isGroebnerBasis_iff_isRemainder_zero]
  refine ⟨hker, ?_⟩
  intro f hf
  obtain ⟨r, hr⟩ := MonomialOrder.exists_isRemainder (m := m) hunit f
  have hrP : r ∈ P := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro c hc
    exact hr.2 c hc
  have hfr : f - r ∈ RingHom.ker φ.toRingHom :=
    (Ideal.span_le.mpr hker) hr.sub_mem_span
  have hrker : r ∈ RingHom.ker φ.toRingHom := by
    have hh := (RingHom.ker φ.toRingHom).sub_mem hf hfr
    simpa using hh
  have hz : F ⟨r, hrP⟩ = F 0 := by
    simpa [F] using (show φ r = 0 from hrker)
  have hr0 : r = 0 := congrArg Subtype.val (hF hz)
  simpa [hr0] using hr

/-- No presentation relations are missing once the displayed standard images are
linearly independent. This applies over arbitrary commutative coefficient rings. -/
theorem kernel_eq_span_of_independent
    (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (φ : MvPolynomial σ R →ₐ[R] A)
    (hG : ∀ g ∈ G, φ g = 0)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hind : LinearIndependent R
      (fun c : RelationStandard m G => φ (monomial c.val 1))) :
    RingHom.ker φ.toRingHom = Ideal.span G :=
  (isGroebnerBasis_kernel_of_independent m G φ hG hunit hind).ideal_eq_span

end FourPapers.Sublattice

end
end

#print axioms FourPapers.Sublattice.isGroebnerBasis_kernel_of_independent
#print axioms FourPapers.Sublattice.kernel_eq_span_of_independent

end
