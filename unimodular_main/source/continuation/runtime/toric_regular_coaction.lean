module

public import Continuation.Runtime.IntrinsicReconstruction
public import Continuation.Runtime.LaurentProductCoordinates
public import Continuation.Runtime.ToricAffineActionCriterion

/-!
# Regular monomial functions and their actual coaction

A global regular function whose rational value is a Laurent monomial
transforms with that character under the actual torus action. For a finite
family of distinct weights, the action pullback of their sum is the
Laurent polynomial with those regular functions as coefficients. A unit
coefficient then supplies the faithful-flat affineness criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open scoped TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

/-- The actual affinization map respects the structure morphism to the
ground field for the section algebra induced by that morphism. -/
theorem affinization_toBase (k : Type u) [CommRing k]
    (X : Over (Spec (CommRingCat.of k))) :
    X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k Γ(X.left, ⊤))) = X.hom := by
  letI : IsIso (⊤ : X.left.Opens).ι :=
    ⟨⟨X.left.topIso.inv, X.left.ι_toIso_inv, X.left.toIso_inv_ι⟩⟩
  apply (cancel_epi (⊤ : X.left.Opens).ι).mp
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_top]
  exact BaseSections.toSpec_scalarMap k (⊤ : X.left.Opens)

/-- The coordinate value in the torus's function field is the ordinary
generic germ of its actual affine global section. -/
theorem torusCoordinateValueAlgHom_eq_germ (k : Type u) [Field k] (n : ℕ)
    (b : AddMonoidAlgebra k (Fin n → ℤ)) :
    torusCoordinateValueAlgHom k n b =
      (splitTorusOver k (Fin n → ℤ)).left.germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (Fin n → ℤ)))).inv b) := by
  let A := CommRingCat.of (AddMonoidAlgebra k (Fin n → ℤ))
  letI : IsDomain A := torusCoordinateRing_isDomain k n
  change affineOpenCoordinateMap A (𝟙 (Spec A)) b = _
  apply (affineOpenFunctionFieldEquiv A (𝟙 (Spec A))).injective
  erw [affineOpenFunctionFieldEquiv_coordinateMap,
    affineOpenFunctionFieldEquiv_germ_top]
  simp only [Scheme.Hom.id_appTop, ConcreteCategory.id_apply]
  change algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) ((Scheme.ΓSpecIso A).hom ((Scheme.ΓSpecIso A).inv b))
  rw [Iso.inv_hom_id_apply]

/-- Distinct weights retain the exact coefficients of a finite Laurent
sum, with no cancellation between different weights. -/
theorem coeff_finite_weight_sum {R : Type u} [CommRing R]
    {M : Type v} [AddCommMonoid M] {embedding : Type w} [Fintype embedding]
    (w : embedding → M) (hw : Function.Injective w) (r : embedding → R) (i : embedding) :
    (∑ j, AddMonoidAlgebra.single (w j) (r j)).coeff (w i) = r i := by
  classical
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.sum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hw.eq_iff]
  simp [Finsupp.single_apply, hw.eq_iff]

namespace SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

local instance regularCoactionLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

local notation "G" => splitTorusOver k (Fin n → ℤ)

local instance regularCoactionProductIntegral : IsIntegral (G ⊗ X).left :=
  torusProduct_integral k n X

/-- A regular function with the displayed genuine rational monomial
value transforms by precisely that character. -/
theorem action_pullback_regular_monomial (r : Γ(X.left, ⊤))
    (m : Fin n → ℤ) (c : k)
    (hr : X.left.germToFunctionField ⊤ r =
      openTorusRationalAlgHom k n X.left T.torus.left (AddMonoidAlgebra.single m c)) :
    (γ[G,X]).left.appTop r =
      (snd G X).left.appTop r *
        (fst G X).left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (Fin n → ℤ)))).inv
            (AddMonoidAlgebra.single m 1)) := by
  letI : Nonempty ((γ[G,X]).left ⁻¹ᵁ (⊤ : X.left.Opens)) := dominant_preimage_nonempty _ _
  letI : Nonempty ((snd G X).left ⁻¹ᵁ (⊤ : X.left.Opens)) := dominant_preimage_nonempty _ _
  letI : Nonempty ((fst G X).left ⁻¹ᵁ (⊤ : (G).left.Opens)) := dominant_preimage_nonempty _ _
  apply (G ⊗ X).left.germToFunctionField_injective ⊤
  erw [map_mul,
    ← dominantFunctionFieldMap_germ (γ[G,X]).left ⊤ r,
    ← dominantFunctionFieldMap_germ (snd G X).left ⊤ r,
    ← dominantFunctionFieldMap_germ (fst G X).left ⊤,
    hr, T.action_pullback_laurent,
    ← torusCoordinateValueAlgHom_eq_germ k n]
  simp only [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    torusProductRationalMap_tmul]
  exact mul_comm _ _

/-- The actual global-section coaction for a finite family of monomial
functions. The comparison is the genuine product base change. -/
theorem finite_regular_monomial_coaction {embedding : Type u} [Fintype embedding]
    (w : embedding → Fin n → ℤ) (c : embedding → k) (r : embedding → Γ(X.left, ⊤))
    (hr : ∀ j, X.left.germToFunctionField ⊤ (r j) =
      openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single (w j) (c j))) :
    laurentProductSectionMap k Γ(X.left, ⊤) (Fin n → ℤ) X.hom X.left.toSpecΓ
        (affinization_toBase k X) (∑ j, AddMonoidAlgebra.single (w j) (r j)) =
      (γ[G,X]).left.appTop (∑ j, r j) := by
  classical
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [laurentProductSectionMap_single, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id_apply]
  exact (T.action_pullback_regular_monomial (r j) (w j) (c j) (hr j)).symm

/-- A finite sum of actual monomial regular functions detects affineness
when its principal open is affine and one of the distinct weight
coefficients is the global unit. -/
theorem isAffine_of_regular_monomial_sum
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    {embedding : Type u} [Fintype embedding]
    (w : embedding → Fin n → ℤ) (hw : Function.Injective w)
    (c : embedding → k) (r : embedding → Γ(X.left, ⊤))
    (hr : ∀ j, X.left.germToFunctionField ⊤ (r j) =
      openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single (w j) (c j)))
    (i : embedding) (hi : r i = 1)
    (hD : IsAffineOpen (X.left.basicOpen (∑ j, r j))) : IsAffine X.left := by
  let F : AddMonoidAlgebra Γ(X.left, ⊤) (Fin n → ℤ) :=
    ∑ j, AddMonoidAlgebra.single (w j) (r j)
  have hcoeff : IsUnit (F.coeff (w i)) := by
    rw [show F.coeff (w i) = r i from coeff_finite_weight_sum w hw r i, hi]
    exact isUnit_one
  apply isAffine_of_affine_torus_action_principal
    k Γ(X.left, ⊤) (Fin n → ℤ) X X.left.toSpecΓ
    (affinization_toBase k X) (∑ j, r j) hD F (w i) hcoeff
  exact T.finite_regular_monomial_coaction w c r hr

end SplitToricEmbedding
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isAffine_of_regular_monomial_sum
