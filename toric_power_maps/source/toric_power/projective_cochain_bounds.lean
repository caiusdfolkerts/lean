module

public import ToricPower.RelativeBoundedSourceHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Bounds for the actual projective augmentation cone

A resolution whose terms vanish above `N` becomes a cochain complex
supported in `[-N, 0]`. Its actual augmentation cone is supported in
`[-N-1, 0]`. These bounds discharge the source condition in the
unbounded relative Hom comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The extension to integer cochain degrees retains the proved finite
support of the original resolution. -/
theorem projectiveCochain_isStrictlyGE {Z : C} (P : ProjectiveResolution Z)
    (N : ℕ) (h : ∀ m : ℕ, N < m → IsZero (P.complex.X m)) :
    (projectiveCochain P).IsStrictlyGE (-(N : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero (show i < 0 by omega)
  exact IsZero.of_iso (h (m+1) (by omega))
    (P.complex.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f (m+1) = Int.negSucc m by dsimp; omega))

/-- The mapping cone bound uses the literal augmentation, including
its term in degree zero. -/
theorem projectiveCochainAugmentation_cone_isStrictlyGE
    {Z : C} (P : ProjectiveResolution Z) (N : ℕ)
    (h : ∀ m : ℕ, N < m → IsZero (P.complex.X m)) :
    (mappingCone (projectiveCochainAugmentation P)).IsStrictlyGE (-(N : ℤ)-1) := by
  letI := projectiveCochain_isStrictlyGE P N h
  exact isStrictlyGE_mappingCone (projectiveCochainAugmentation P)
    (-(N : ℤ)) 0 (-(N : ℤ)-1) (by omega) (by omega)

/-- A finite resolution and exact ordinary coefficient rows suffice
for the actual comparison on every unbounded coefficient complex. -/
theorem finiteProjective_linearHomPrecomp_quasiIso
    (R : Type r) [CommRing R] [Linear R C]
    {Z : C} (P : ProjectiveResolution Z) (N : ℕ)
    (bound : ∀ m : ℕ, N < m → IsZero (P.complex.X m))
    (X : CochainComplex C ℤ)
    (rows : ∀ q (n : ℕ), (projectiveCoefficientComplex R P (X.X q)).ExactAt (n+1)) :
    QuasiIso (linearHomComplexPrecomp R (projectiveCochainAugmentation P) X) := by
  letI := projectiveCochainAugmentation_cone_isStrictlyGE P N bound
  exact projective_linearHomPrecomp_quasiIso_of_boundedSource R P X (-(N : ℤ)-1) rows

end ToricPower

end
