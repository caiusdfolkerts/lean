module

public import Continuation.Runtime.GraphicNormalEmbedding
public import Continuation.Runtime.SectionPolynomialRestriction

/-!
# The geometric vanishing ideal of the same actual embedding

The sections in this module are extracted from the actual pullbacks of
polynomial projective coordinates, followed by the original-line-bundle
isomorphism. Polynomial restriction uses their ordinary tensor products.
The vanishing set is defined by vanishing of those actual sections in every
degree, before it is compared with the section-evaluation kernel. This gives
an explicit geometric-ideal comparison, including every homogeneous degree,
without assuming an O(d) or scheme-image identification.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing.ActualSections
open scoped BaseSections

namespace Unimodular.ActualVeryAmple.NormalQuadraticSectionEmbedding

variable (k : Type) [Field k] (X : Scheme) [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (M : X.Modules)
  (E : NormalQuadraticSectionEmbedding k X M)

/-- Extract a genuine section from the actual pullback of a projective
coordinate, then express it in the proved Cartier presentation of M. -/
def pulledCoordinateSections (i : E.index) : Γ(E.cocycle.sheaf, ⊤) :=
  Scheme.Modules.Hom.app
    (BondalThomsen.polynomialProjDegreeOnePullbackCoordinateHom k E.index E.morphism i ≫
      E.pullbackIso.hom ≫ E.original.inv) ⊤ (1 : Γ(X, ⊤))

/-- Coordinate compatibility is equality of the actual original sections,
not merely equality of the associated line-bundle classes. -/
theorem pulledCoordinateSections_eq : E.pulledCoordinateSections k X M = E.sections := by
  funext i
  unfold pulledCoordinateSections
  rw [← Category.assoc, E.coordinate i, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  simp only [BondalThomsen.moduleGlobalSectionHom_app, one_smul,
    homOfLE_refl, op_id, E.cocycle.sheaf.presheaf.map_id,
    ConcreteCategory.id_apply]

/-- Actual degree-d polynomial restriction to the original ordinary M.
It is evaluated using the pulled projective coordinates and the ordinary
tensor multiplication, whose comparison is proved in SectionPolynomialRestriction. -/
def polynomialPullbackSection (d : ℕ) (p : MvPolynomial E.index k) :
    Γ(tensorSheafPower M d, ⊤) :=
  (BaseSections.globalSectionsIso k (tensorSheafPowerIso E.original d))
    (tensorPolynomialSection k E.cocycle (E.pulledCoordinateSections k X M) d p)

/-- Every polynomial restriction equals evaluation in the original
sections, with their actual tensor-power transport. -/
theorem polynomialPullbackSection_eq (d : ℕ) (p : MvPolynomial E.index k) :
    E.polynomialPullbackSection k X M d p =
      (BaseSections.globalSectionsIso k (tensorSheafPowerIso E.original d))
        (tensorPolynomialSection k E.cocycle E.sections d p) := by
  rw [polynomialPullbackSection, E.pulledCoordinateSections_eq k X M]

/-- For every homogeneous polynomial, geometric vanishing of its actual
pullback is precisely membership in the actual section-map kernel. -/
theorem polynomialPullbackSection_eq_zero_iff (d : ℕ)
    (p : MvPolynomial E.index k) (hp : p.IsHomogeneous d) :
    E.polynomialPullbackSection k X M d p = 0 ↔
      p ∈ RingHom.ker (degreeOneSectionMap k E.cocycle E.sections).toRingHom := by
  rw [E.polynomialPullbackSection_eq k X M, LinearEquiv.map_eq_zero_iff]
  exact tensorPolynomialSection_eq_zero_iff k E.cocycle E.sections d p hp

/-- The homogeneous vanishing set is defined using actual tensor-power
sections obtained from the actual projective coordinate pullbacks. -/
def polynomialVanishingSet : Set (MvPolynomial E.index k) :=
  {p | ∀ d : ℕ, E.polynomialPullbackSection k X M d p = 0}

theorem polynomialVanishingSet_eq_kernel :
    E.polynomialVanishingSet k X M =
      (RingHom.ker (degreeOneSectionMap k E.cocycle E.sections).toRingHom :
        Set (MvPolynomial E.index k)) := by
  ext p
  change (∀ d : ℕ, E.polynomialPullbackSection k X M d p = 0) ↔ _
  simp only [E.polynomialPullbackSection_eq k X M, LinearEquiv.map_eq_zero_iff]
  exact (mem_kernel_iff_tensorPolynomialSections_zero k E.cocycle E.sections p).symm

/-- The actual vanishing set is an ideal; the proof uses the established
comparison, while its carrier remains the geometric vanishing condition. -/
def geometricCoordinateIdeal : Ideal (MvPolynomial E.index k) where
  carrier := E.polynomialVanishingSet k X M
  zero_mem' := by
    rw [E.polynomialVanishingSet_eq_kernel k X M]
    exact Ideal.zero_mem _
  add_mem' := by
    intro p q hp hq
    rw [E.polynomialVanishingSet_eq_kernel k X M] at hp hq ⊢
    exact Ideal.add_mem _ hp hq
  smul_mem' := by
    intro a p hp
    rw [E.polynomialVanishingSet_eq_kernel k X M] at hp ⊢
    exact Ideal.mul_mem_left _ a hp

/-- Equality with the literal kernel is a theorem about the independently
defined geometric vanishing condition. -/
theorem geometricCoordinateIdeal_eq_kernel :
    E.geometricCoordinateIdeal k X M =
      RingHom.ker (degreeOneSectionMap k E.cocycle E.sections).toRingHom := by
  apply SetLike.coe_injective
  exact E.polynomialVanishingSet_eq_kernel k X M

abbrev geometricCoordinateRing :=
  MvPolynomial E.index k ⧸ E.geometricCoordinateIdeal k X M

/-- The homogeneous coordinate ring defined by actual geometric vanishing
on the embedding is a nonzero normal domain. -/
theorem geometricCoordinateRing_normal_domain :
    IsDomain (E.geometricCoordinateRing k X M) ∧
      IsIntegrallyClosed (E.geometricCoordinateRing k X M) := by
  change IsDomain (MvPolynomial E.index k ⧸ E.geometricCoordinateIdeal k X M) ∧
    IsIntegrallyClosed (MvPolynomial E.index k ⧸ E.geometricCoordinateIdeal k X M)
  rw [E.geometricCoordinateIdeal_eq_kernel k X M]
  exact ⟨E.domain, E.normal⟩

/-- The entire geometric ideal of this same embedding is generated by
homogeneous quadrics. -/
theorem geometricCoordinateIdeal_quadrics :
    ∃ S : Set (MvPolynomial E.index k),
      E.geometricCoordinateIdeal k X M = Ideal.span S ∧
        ∀ p ∈ S, p.IsHomogeneous 2 := by
  rw [E.geometricCoordinateIdeal_eq_kernel k X M]
  exact E.quadrics

#print axioms polynomialPullbackSection_eq_zero_iff
#print axioms geometricCoordinateIdeal_eq_kernel
#print axioms geometricCoordinateRing_normal_domain
#print axioms geometricCoordinateIdeal_quadrics

end Unimodular.ActualVeryAmple.NormalQuadraticSectionEmbedding

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Unimodular.ActualVeryAmple

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type) [Field k]

/-- Corollary 6.11's ample-embedding clause with the homogeneous coordinate
ideal defined by actual polynomial pullback vanishing. The same closed
embedding and the same original ordinary line bundle occur in every clause. -/
theorem corollary_6_11_projectivelyNormal_quadrics_actual
    (hprojective : HasFiniteProjectiveEmbedding k (F.fanScheme k))
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)))
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf (F.fanScheme k))
    (hample : Unimodular.NefBig.IsAmpleModule L.obj) :
    ∃ E : NormalQuadraticSectionEmbedding k (F.fanScheme k) L.obj,
      VeryAmpleOverField k (F.fanScheme k) L.obj ∧
      IsDomain (E.geometricCoordinateRing k (F.fanScheme k) L.obj) ∧
      IsIntegrallyClosed (E.geometricCoordinateRing k (F.fanScheme k) L.obj) ∧
      ∃ S : Set (MvPolynomial E.index k),
        E.geometricCoordinateIdeal k (F.fanScheme k) L.obj = Ideal.span S ∧
          ∀ p ∈ S, p.IsHomogeneous 2 := by
  obtain ⟨hvery, ⟨E⟩⟩ :=
    F.corollary_6_11_ample_embedding_actual k hprojective Q hQ hanti L hample
  exact ⟨E, hvery, (E.geometricCoordinateRing_normal_domain k _ _).1,
    (E.geometricCoordinateRing_normal_domain k _ _).2,
    E.geometricCoordinateIdeal_quadrics k _ _⟩

#print axioms corollary_6_11_projectivelyNormal_quadrics_actual

end PaperVerification.ToricGeometry.SmoothCompleteFan

end
