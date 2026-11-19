module

public import PaperVerification.TotalChowLocalization
public import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective
public import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero
public import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties
public import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv

/-!
# The full genuine Chow rank of an affine space is at most one

Only surjectivity of the actual affine-line Chow pullback is needed for the
paving bound.  Its degree-zero cokernel vanishes by an explicit principal-divisor
calculation.  Iterating those proved facts covers every affine dimension and
every Chow grading, without importing projective bundle or Chern machinery.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry
open Divisors.LineBundles
open DimensionChow.BundleCycles
open scoped DirectSum

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
  (f : X ⟶ complexBase) [LocallyOfFiniteType f]

/-- The actual affine-line pullback, with its degree shift retained. -/
def affineLineTotalExtension : TotalChowQ f →ₗ[ℚ]
    TotalChowQ (AffineLine.Charts.BundleCycles.affineLineProjection X ≫ f) :=
  DirectSum.toModule ℚ ℕ _ (fun d =>
    (DirectSum.lof ℚ ℕ _ (d+1)).comp
      (AffineLine.ChowExtension.BundleCycles.affineLineChowExtension X f d))

theorem affineLineTotalExtension_surjective :
    Function.Surjective (affineLineTotalExtension X f) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro a ha
  clear ha
  induction a using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | of d a =>
    cases d with
    | zero =>
      rw [AffineLine.ChowZero.BundleCycles.affineLineZeroDimension_chow_eq_zero X f a]
      simp only [map_zero]
      exact Submodule.zero_mem _
    | succ d =>
      obtain ⟨b,rfl⟩ :=
        AffineLine.ChowSurjective.BundleCycles.affineLineChowExtension_surjective X f d a
      refine ⟨DirectSum.lof ℚ ℕ _ d b,?_⟩
      exact DirectSum.toModule_lof ℚ
        (M := fun d => DimensionChowQ f d)
        (φ := fun d => (DirectSum.lof ℚ ℕ
          (fun q => DimensionChowQ (AffineLine.Charts.BundleCycles.affineLineProjection X ≫ f) q)
          (d+1)).comp
          (AffineLine.ChowExtension.BundleCycles.affineLineChowExtension X f d)) d b

theorem affineSpaceSuccEquiv_over_complex (n : ℕ) :
    (Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom ≫
      (AffineLine.Charts.BundleCycles.affineLineProjection (AlgebraicGeometry.AffineSpace (Fin n) X) ≫
        ((AlgebraicGeometry.AffineSpace (Fin n) X ↘ X) ≫ f)) =
      (AlgebraicGeometry.AffineSpace (Fin (n+1)) X ↘ X) ≫ f := by
  simpa only [Category.assoc, AffineLine.Charts.BundleCycles.affineLineProjection] using
    congrArg (fun h => h ≫ f)
      (Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv_over X n)

/-- Every total Chow class on an actual finite affine space is the
pullback of a total class on its base. -/
theorem exists_affineSpaceFin_total_surjection (n : ℕ) :
    ∃ L : TotalChowQ f →ₗ[ℚ]
      TotalChowQ ((AlgebraicGeometry.AffineSpace (Fin n) X ↘ X) ≫ f),
        Function.Surjective L := by
  induction n with
  | zero =>
    let e := Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)
    let E := totalChowEquiv e ((AlgebraicGeometry.AffineSpace (Fin 0) X ↘ X) ≫ f) f rfl
    exact ⟨E.symm.toLinearMap,E.symm.surjective⟩
  | succ n ih =>
    obtain ⟨L,hL⟩ := ih
    let E := totalChowEquiv
      (Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n)
      ((AlgebraicGeometry.AffineSpace (Fin (n+1)) X ↘ X) ≫ f)
      (AffineLine.Charts.BundleCycles.affineLineProjection (AlgebraicGeometry.AffineSpace (Fin n) X) ≫
        ((AlgebraicGeometry.AffineSpace (Fin n) X ↘ X) ≫ f))
      (affineSpaceSuccEquiv_over_complex X f n)
    exact ⟨E.symm.toLinearMap.comp ((affineLineTotalExtension _ _).comp L),
      E.symm.surjective.comp ((affineLineTotalExtension_surjective _ _).comp hL)⟩

theorem exists_affineSpace_total_surjection (ι : Type) [Finite ι] :
    ∃ L : TotalChowQ f →ₗ[ℚ]
      TotalChowQ ((AlgebraicGeometry.AffineSpace ι X ↘ X) ≫ f),
        Function.Surjective L := by
  obtain ⟨L,hL⟩ := exists_affineSpaceFin_total_surjection X f (Nat.card ι)
  let e := Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv
    X (Finite.equivFin ι).symm
  have he : e.hom ≫ ((AlgebraicGeometry.AffineSpace ι X ↘ X) ≫ f) =
      (AlgebraicGeometry.AffineSpace (Fin (Nat.card ι)) X ↘ X) ≫ f := by
    rw [← Category.assoc]
    exact congrArg (fun h => h ≫ f)
      (Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv_over
        X (Finite.equivFin ι).symm)
  let E := totalChowEquiv e _ _ he
  exact ⟨E.toLinearMap.comp L,E.surjective.comp hL⟩

theorem finite_affineSpace_total (ι : Type) [Finite ι]
    [Module.Finite ℚ (TotalChowQ f)] :
    Module.Finite ℚ (TotalChowQ ((AlgebraicGeometry.AffineSpace ι X ↘ X) ≫ f)) := by
  obtain ⟨L,hL⟩ := exists_affineSpace_total_surjection X f ι
  exact Module.Finite.of_surjective L hL

theorem finrank_affineSpace_total_le (ι : Type) [Finite ι]
    [Module.Finite ℚ (TotalChowQ f)] :
    Module.finrank ℚ (TotalChowQ ((AlgebraicGeometry.AffineSpace ι X ↘ X) ≫ f)) ≤
      Module.finrank ℚ (TotalChowQ f) := by
  obtain ⟨L,hL⟩ := exists_affineSpace_total_surjection X f ι
  exact LinearMap.finrank_le_finrank_of_surjective hL

/-- The all-grading bound for every actual complex affine space. -/
theorem finrank_complexAffineSpace_total_le_one (ι : Type) [Finite ι] :
    Module.Finite ℚ (TotalChowQ
      ((AlgebraicGeometry.AffineSpace ι complexBase ↘ complexBase) ≫ 𝟙 complexBase)) ∧
    Module.finrank ℚ (TotalChowQ
      ((AlgebraicGeometry.AffineSpace ι complexBase ↘ complexBase) ≫ 𝟙 complexBase)) ≤ 1 := by
  letI := finite_complexBase
  exact ⟨finite_affineSpace_total complexBase (𝟙 _) ι,
    (finrank_affineSpace_total_le complexBase (𝟙 _) ι).trans finrank_complexBase_le_one⟩

end PaperVerification.TotalChow
