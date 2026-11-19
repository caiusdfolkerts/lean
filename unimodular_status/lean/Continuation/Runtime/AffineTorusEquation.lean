module

public import Continuation.Runtime.FactorialAffineOpens
public import Continuation.Runtime.IntrinsicLocalCharacterRatios

/-!
# The Laurent equation of an affine open on the dense torus

The intersection of an affine open with the specified open torus is affine
by separatedness. The Laurent coordinate ring is factorial, so that
intersection is principal. Its actual nonvanishing condition is expressed
in the original scheme's local rings, using the genuine affine stalk
isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters
open MonoidalCategory CartesianMonoidalCategory

namespace PaperVerification.ToricSchemes

/-- Inverse regularity in the original affine-chart stalk is exactly
avoidance of the original prime ideal. -/
theorem affineOpenCoordinate_inverse_regular_iff
    {X : Scheme.{u}} [IsIntegral X] (R : CommRingCat.{u}) [IsDomain R]
    (j : Spec R ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum R)
    (r : R) (hr : r ≠ 0) :
    (affineOpenCoordinateMap R j r)⁻¹ ∈ regularAtSubring X (j p) ↔ r ∉ p.asIdeal := by
  let e := affineOpenStalkEquiv R j p
  let a := algebraMap R (Localization.AtPrime p.asIdeal) r
  have hv : affineOpenCoordinateMap R j r ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr
  have hstalk := isUnit_stalk_iff (j p) (e a)
  rw [affineOpenStalkEquiv_functionField R j p r] at hstalk
  have hstalk' : IsUnit (e a) ↔ (affineOpenCoordinateMap R j r)⁻¹ ∈ regularAtSubring X (j p) := by
    exact hstalk.trans ⟨fun h => h.2, fun h => ⟨hv,h⟩⟩
  calc
    _ ↔ IsUnit (e a) := hstalk'.symm
    _ ↔ IsUnit a := (MulEquiv.isUnit_map e.toMulEquiv)
    _ ↔ r ∉ p.asIdeal := IsLocalization.AtPrime.isUnit_to_map_iff
      (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r

namespace SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [X.left.IsSeparated]
    (T : SplitToricEmbedding k n X)

/-- Every nonempty affine open has an actual nonzero Laurent equation on
the specified open torus. Its unit locus is exactly that intersection. -/
theorem exists_affineTorusEquation
    (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ∃ f : AddMonoidAlgebra k (Fin n → ℤ), f ≠ 0 ∧
      ∀ x ∈ T.torusOpen,
        (openTorusRationalAlgHom k n X.left T.torus.left f)⁻¹ ∈
          regularAtSubring X.left x ↔ x ∈ U := by
  let A := torusCoordinateRing k n
  letI : IsDomain A := torusCoordinateRing_isDomain k n
  letI : UniqueFactorizationMonoid A := torusCoordinateRing_uniqueFactorization k n
  letI : IsNoetherianRing A := torusCoordinateRing_isNoetherianRing k n
  letI : IsAffine (splitTorusOver k (Fin n → ℤ)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  let V := T.torus.left ⁻¹ᵁ U
  letI : Nonempty V := dominant_preimage_nonempty T.torus.left U
  have hV : IsAffineOpen V := by
    apply (T.torus.left.isAffineOpen_iff_of_isOpenImmersion).mp
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact (isAffineOpen_opensRange T.torus.left).inf hU
  obtain ⟨f, hf, hVf⟩ := exists_nonzero_basicOpen_eq_of_factorial A V hV
  refine ⟨f, hf, ?_⟩
  rintro x ⟨p, rfl⟩
  change (affineOpenCoordinateMap (CommRingCat.of A) T.torus.left f)⁻¹ ∈
    regularAtSubring X.left (T.torus.left p) ↔ p ∈ V
  have h := affineOpenCoordinate_inverse_regular_iff (CommRingCat.of A) T.torus.left p f hf
  exact h.trans (by rw [hVf]; rfl)

end SplitToricEmbedding
end PaperVerification.ToricSchemes
