module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

/-!
# Residue degree at an actual rational point

A section of a scheme morphism induces inverse maps on residue fields
at its image. The proof uses the actual maps on local residue fields.
In particular, the two coordinate boundary points of an invariant
projective line contribute residue degree one over the ground field.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme.{u}}

/-- A section is an isomorphism on the residue field at every point of
its image, regardless of whether the base field is algebraically closed. -/
theorem residueFieldMap_bijective_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    Function.Bijective (f.residueFieldMap (s y)) := by
  have hpoint : f (s y)=y := congrArg (fun g : Y ⟶ Y => g y) hs
  have hcomp : f.residueFieldMap (s y) ≫ s.residueFieldMap y =
      (Y.residueFieldCongr hpoint).hom := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr hs,
      Scheme.residueFieldMap_id]
    exact Category.comp_id ((Y.residueFieldCongr hpoint).hom)
  refine ⟨(f.residueFieldMap (s y)).hom.injective,?_⟩
  intro z
  obtain ⟨a,ha⟩ := (Y.residueFieldCongr hpoint).commRingCatIsoToRingEquiv.surjective
    (s.residueFieldMap y z)
  refine ⟨a,(s.residueFieldMap y).hom.injective ?_⟩
  exact (congrArg (fun g => g a) hcomp).trans ha

/-- Degree one is computed from Mathlib's literal residue extension. -/
theorem residueDegree_of_section
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (y : Y) :
    f.residueDegree (s y) = 1 := by
  letI := (f.residueFieldMap (s y)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (residueFieldMap_bijective_of_section f s hs y)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.residueDegree_of_section
