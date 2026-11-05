module

public import Recovery.Unimodular.GraphicSectionRing.GeometricKoszul

/-!
# The original grading and degree-zero augmentation of the actual section ring

These formulas audit the grading used in the ordinary Tor theorem. A genuine
lattice monomial of degree d maps to a rational section in exactly degree d;
principal normalization changes only its rational coefficient, by q^d. Thus
the Tor grading is the ordinary tensor-power grading, not the auxiliary height.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Unimodular.GraphicSectionRing
open PaperVerification.ToricSchemes
open scoped BaseSections

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]

@[simp] theorem fanSectionRingEquiv_single (a : Lattice n → ℤ)
    (z : F.fanSectionSemigroup a) (c : k) :
    (F.fanSectionRingEquiv k a (AddMonoidAlgebra.single z c)).val =
      AddMonoidAlgebra.single z.val.1
        (F.torusRationalAlgHom k (AddMonoidAlgebra.single z.val.2 c)) :=
  GradedCharacters.evaluation_single _ _ z c

@[simp] theorem arbitraryCartierRingEquiv_symm_coefficient
    (D : CartierData (F.fanScheme k))
    (p : ActualSections.sectionRing k
      (F.fanCartierCocycle k F.isPure (F.cartierCoefficients k F.isPure D))) (d : ℕ) :
    ((F.arbitraryCartierRingEquiv k D).symm p).val.coeff d =
      ((F.normalizationUnit k D : (F.fanScheme k).functionField)⁻¹) ^ d * p.val.coeff d := by
  have he := F.arbitraryCartierRingEquiv_coefficient k D
    ((F.arbitraryCartierRingEquiv k D).symm p) d
  rw [AlgEquiv.apply_symm_apply] at he
  rw [he, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero _), one_pow, one_mul]

namespace GraphicCoordinates

variable {F} (G : F.GraphicCoordinates)

/-- The exact image of every actual lattice monomial retains its literal
nonnegative grading coordinate. -/
@[simp] theorem actualSectionRingEquiv_single (a : Lattice n → ℤ)
    (z : sectionSemigroup (G.constraints a)) (c : k) :
    (G.actualSectionRingEquiv k a (AddMonoidAlgebra.single z c)).val =
      AddMonoidAlgebra.single z.val.1
        (F.torusRationalAlgHom k (AddMonoidAlgebra.single (G.equiv.symm z.val.2) c)) := by
  change (F.fanSectionRingEquiv k a
    (AddMonoidAlgebra.domCongr k k (G.semigroupEquiv a).symm
      (AddMonoidAlgebra.single z c))).val = _
  rw [AddMonoidAlgebra.domCongr_single, F.fanSectionRingEquiv_single]
  rfl

/-- Normalization changes only the rational coefficient of a homogeneous
section, never its original tensor-power degree. -/
@[simp] theorem arbitraryGraphicSectionRingEquiv_single_coefficient
    (D : CartierData (F.fanScheme k))
    (z : sectionSemigroup (G.constraints (F.cartierCoefficients k F.isPure D)))
    (c : k) (d : ℕ) :
    (G.arbitraryGraphicSectionRingEquiv k D (AddMonoidAlgebra.single z c)).val.coeff d =
      ((F.normalizationUnit k D : (F.fanScheme k).functionField)⁻¹) ^ d *
        (AddMonoidAlgebra.single z.val.1
          (F.torusRationalAlgHom k (AddMonoidAlgebra.single (G.equiv.symm z.val.2) c))).coeff d := by
  change ((F.arbitraryCartierRingEquiv k D).symm
    (G.actualSectionRingEquiv k _ (AddMonoidAlgebra.single z c))).val.coeff d = _
  rw [F.arbitraryCartierRingEquiv_symm_coefficient, G.actualSectionRingEquiv_single k]

/-- All coefficients away from the original degree vanish. -/
theorem arbitraryGraphicSectionRingEquiv_homogeneous
    (D : CartierData (F.fanScheme k))
    (z : sectionSemigroup (G.constraints (F.cartierCoefficients k F.isPure D)))
    (c : k) (d : ℕ) (hd : d ≠ z.val.1) :
    (G.arbitraryGraphicSectionRingEquiv k D (AddMonoidAlgebra.single z c)).val.coeff d = 0 := by
  classical
  rw [G.arbitraryGraphicSectionRingEquiv_single_coefficient k]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hd), mul_zero]

/-- The mapped flag-indexed basis used by the Tor theorem is homogeneous
for exactly the original section degree. -/
theorem actualTorBasis_homogeneous (D : CartierData (F.fanScheme k))
    (v : GeometricKoszul.Index.{u} (G.constraints (F.cartierCoefficients k F.isPure D)))
    (d : ℕ) (hd : d ≠ GeometricKoszul.degree
      (G.constraints (F.cartierCoefficients k F.isPure D)) v) :
    (GeometricKoszul.basis (G.constraints (F.cartierCoefficients k F.isPure D)) k
      (G.arbitraryGraphicSectionRingEquiv k D) (some v)).val.coeff d = 0 := by
  simp only [GeometricKoszul.basis, Unimodular.FlagKoszul.BarReindex.basis_some,
    Unimodular.FlagKoszul.AlgebraTransport.basis_apply]
  change (G.arbitraryGraphicSectionRingEquiv k D
    (FlagModel.basis (G.constraints (F.cartierCoefficients k F.isPure D)) k (some v.down))).val.coeff d = 0
  rw [FlagModel.basis_some]
  apply G.arbitraryGraphicSectionRingEquiv_homogeneous k
  change d ≠ internalDegree (G.constraints (F.cartierCoefficients k F.isPure D))
    (sectionDegree (G.constraints (F.cartierCoefficients k F.isPure D)) v.down.val)
  rw [internalDegree_sectionDegree]
  exact hd

#print axioms actualSectionRingEquiv_single
#print axioms arbitraryGraphicSectionRingEquiv_single_coefficient
#print axioms arbitraryGraphicSectionRingEquiv_homogeneous
#print axioms actualTorBasis_homogeneous

end GraphicCoordinates

#print axioms arbitraryCartierRingEquiv_symm_coefficient

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.actualTorBasis_homogeneous
