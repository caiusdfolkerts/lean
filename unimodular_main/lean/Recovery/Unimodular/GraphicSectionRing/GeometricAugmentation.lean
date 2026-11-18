module

public import Recovery.Unimodular.GraphicSectionRing.GeometricGrading

/-!
# The ordinary degree-zero augmentation of the genuine section ring

The augmentation used in the derived Tor computation is proved to be precisely
the original degree-zero coefficient, viewed in the ground field through the
scheme's structural scalar map. This is an equality in the actual rational
function field, for every finite graded section sum.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing
open scoped BaseSections

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type u) [Field k]

/-- Degree zero of the actual image is exactly the original semigroup
augmentation, under the actual scheme scalar inclusion. -/
theorem arbitraryGraphicSectionRingEquiv_zero_coefficient
    (D : CartierData (F.fanScheme k))
    (f : SectionAlgebra (G.constraints (F.cartierCoefficients k F.isPure D)) k) :
    (G.arbitraryGraphicSectionRingEquiv k D f).val.coeff 0 =
      algebraMap k (F.fanScheme k).functionField
        (sectionAugmentation (G.constraints (F.cartierCoefficients k F.isPure D)) k f) := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using congrArg₂ (· + ·) hf hg
  | single z c =>
    rw [G.arbitraryGraphicSectionRingEquiv_single_coefficient k,
      sectionAugmentation_single]
    change _ = algebraMap k (F.fanScheme k).functionField (if z.val.1 = 0 then c else 0)
    simp only [pow_zero, one_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hz : z.val.1 = 0
    · simp only [hz, if_pos rfl]
      rw [z.property.1 hz, map_zero]
      change F.torusRationalAlgHom k (algebraMap k (AddMonoidAlgebra k (Lattice n)) c) = _
      exact (F.torusRationalAlgHom k).commutes c
    · simp only [if_neg hz, map_zero]

/-- The exact natural augmentation used by the ordinary derived Tor endpoint.
No different scalar quotient or ungraded residue field is substituted. -/
theorem actualAugmentation_is_degreeZero (D : CartierData (F.fanScheme k))
    (p : ActualSections.sectionRing k D.localCocycle) :
    algebraMap k (F.fanScheme k).functionField
      (GeometricKoszul.augmentation (G.constraints (F.cartierCoefficients k F.isPure D)) k
        (G.arbitraryGraphicSectionRingEquiv k D) p) = p.val.coeff 0 := by
  have h := G.arbitraryGraphicSectionRingEquiv_zero_coefficient k D
    ((G.arbitraryGraphicSectionRingEquiv k D).symm p)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

include G in
/-- Every actual degree-zero coefficient is a unique ground-field scalar. -/
theorem actual_degreeZero_unique_scalar (D : CartierData (F.fanScheme k))
    (p : ActualSections.sectionRing k D.localCocycle) :
    ∃! c : k, algebraMap k (F.fanScheme k).functionField c = p.val.coeff 0 := by
  refine ⟨GeometricKoszul.augmentation (G.constraints (F.cartierCoefficients k F.isPure D)) k
    (G.arbitraryGraphicSectionRingEquiv k D) p,
    G.actualAugmentation_is_degreeZero k D p, ?_⟩
  intro c hc
  exact (algebraMap k (F.fanScheme k).functionField).injective
    (hc.trans (G.actualAugmentation_is_degreeZero k D p).symm)

#print axioms arbitraryGraphicSectionRingEquiv_zero_coefficient
#print axioms actualAugmentation_is_degreeZero
#print axioms actual_degreeZero_unique_scalar

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

#check PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.actualAugmentation_is_degreeZero
