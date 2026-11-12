module

public import ToricPower.ProjectiveSectionConverse
public import ToricPower.ProjectiveCochainBounds

/-! # Unbounded assembly of the specified projective section comparison

The actual finite projective resolution gives the comparison on an
arbitrary unbounded coefficient complex. The assumptions concern its
ordinary rows, or equivalently the specified comparison on each single
coefficient. No boundedness or finite-dimensionality of the target is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower

universe u v w
variable (R : Type v) [CommRing R]
  {A : Type u} {C : Type w} [Category.{v} A] [Category.{v} C]
  [Abelian A] [Abelian C] [Linear R C]
  (S : A ⥤ C) [S.Additive] {Z : C} (P : ProjectiveResolution Z)

/-- Exact ordinary coefficient rows assemble to the genuine projective
augmentation on an unbounded complex. -/
theorem projectiveCoefficientComplexUnit_quasiIso_of_finiteRows
    (bound : ℕ) (terminates : ∀ m : ℕ, bound < m → IsZero (P.complex.X m))
    (K : CochainComplex A ℤ)
    (rows : ∀ q (m : ℕ),
      (projectiveCoefficientComplex R P (S.obj (K.X q))).ExactAt (m+1)) :
    QuasiIso ((projectiveCoefficientComplexUnit R S P).app K) := by
  haveI : QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      ((S.mapHomologicalComplex (.up ℤ)).obj K)) :=
    finiteProjective_linearHomPrecomp_quasiIso R P bound terminates _ rows
  dsimp only [projectiveCoefficientComplexUnit]
  infer_instance

variable (E : A ⥤ ModuleCat.{v} R) [E.Additive]
  (a : E ⟶ ordinaryProjectiveCoefficients R S (Z := Z))

/-- The actual section map on every coefficient is an isomorphism if
its specified projective comparison on that coefficient is a quasi-isomorphism. -/
theorem mappedProjectiveSection_isIso_of_singleComparisons
    (K : CochainComplex A ℤ)
    (singles : ∀ q, QuasiIso (scalarProjectiveSectionMap R P (a.app (K.X q)))) :
    IsIso ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  haveI (q : ℤ) : IsIso (a.app (K.X q)) := by
    haveI := singles q
    exact scalarProjectiveSectionMap_section_isIso R P (a.app (K.X q))
  haveI (q : ℤ) : IsIso (((NatTrans.mapHomologicalComplex a (.up ℤ)).app K).f q) := by
    change IsIso (a.app (K.X q))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The original comparison on all integer degrees follows from the
actual single-coefficient comparisons and the finite source resolution. -/
theorem projectiveSectionComparison_quasiIso_of_singleComparisons
    (bound : ℕ) (terminates : ∀ m : ℕ, bound < m → IsZero (P.complex.X m))
    (K : CochainComplex A ℤ)
    (singles : ∀ q, QuasiIso (scalarProjectiveSectionMap R P (a.app (K.X q)))) :
    QuasiIso ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K ≫
      (projectiveCoefficientComplexUnit R S P).app K) := by
  haveI := mappedProjectiveSection_isIso_of_singleComparisons R S P E a K singles
  haveI : QuasiIso ((projectiveCoefficientComplexUnit R S P).app K) := by
    apply projectiveCoefficientComplexUnit_quasiIso_of_finiteRows R S P bound terminates
    intro q m
    haveI := singles q
    exact scalarProjectiveSectionMap_positive_exact R P (a.app (K.X q)) m
  infer_instance

end ToricPower

end
