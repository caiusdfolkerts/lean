module

public import ToricPower.ProjectiveAugmentationRows
public import ToricPower.LinearHomComplexFunctor
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Signed Hom into a single object and ordinary coefficient cochains

The standard signed Hom differential on maps from a nonpositive chain
resolution to a single target differs from ordinary contravariant Hom
by a degree sign. The recursive sign below accounts for that difference
explicitly. Its degreewise linear equivalences give an isomorphism with
the full ordinary natural-number-indexed coefficient complex.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

/-- The cumulative sign required by the signed Hom differential. -/
def homDualSign : ℕ → ℤˣ
  | 0 => 1
  | n+1 => (n+1 : ℤ).negOnePow * homDualSign n

@[simp]
theorem homDualSign_step (n : ℕ) :
    homDualSign (n+1) * (n+1 : ℤ).negOnePow = homDualSign n := by
  rw [homDualSign]
  rw [mul_comm ((n+1 : ℤ).negOnePow) (homDualSign n), mul_assoc,
    Int.units_mul_self, mul_one]

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Multiplication by the exact integer unit sign, linear over the base ring. -/
def homDualSignLinearEquiv (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : M ≃ₗ[R] M where
  toFun x := homDualSign n • x
  invFun x := homDualSign n • x
  left_inv x := by
    change homDualSign n • (homDualSign n • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  right_inv x := by
    change homDualSign n • (homDualSign n • x) = x
    rw [smul_smul, Int.units_mul_self, one_smul]
  map_add' x y := smul_add _ _ _
  map_smul' a x := smul_comm _ _ _

variable (K : ChainComplex C ℕ) (Y : C)

/-- The actual ordinary contravariant coefficient complex. -/
def ordinaryChainCoefficients : CochainComplex (ModuleCat.{v} R) ℕ :=
  (((linearYoneda R C).obj Y).mapHomologicalComplex (.up ℕ)).obj K.op

/-- The exact unsigned evaluation on the unique possible source degree. -/
def homToSingleRawDegreeEquiv (n : ℕ) :
    Cochain (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ) ≃ₗ[R] (K.X n ⟶ Y) :=
  (Cochain.toSingleLinearEquiv (R := R)
    (show -(n : ℤ)+(n : ℤ)=0 by omega)).trans
      (Linear.homCongr R (K.extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by rfl)) (Iso.refl Y))

theorem homToSingleRawDegreeEquiv_toSingleMk (n : ℕ)
    (f : (K.extend ComplexShape.embeddingDownNat).X (-(n : ℤ)) ⟶ Y) :
    homToSingleRawDegreeEquiv R K Y n
      (Cochain.toSingleMk f (show -(n : ℤ)+(n : ℤ)=0 by omega)) =
      (K.extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by rfl)).inv ≫ f := by
  simp [homToSingleRawDegreeEquiv, Linear.homCongr]

/-- The signed Hom differential has exactly this sign in ordinary coordinates. -/
theorem homToSingleRawDegreeEquiv_d (n : ℕ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    homToSingleRawDegreeEquiv R K Y (n+1) (δ (n : ℤ) ((n+1 : ℕ) : ℤ) z) =
      (n+1 : ℤ).negOnePow • (K.d (n+1) n ≫ homToSingleRawDegreeEquiv R K Y n z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-(n : ℤ)) (by omega)
  rw [Cochain.δ_toSingleMk _ _ ((n+1 : ℕ) : ℤ) (-((n+1 : ℕ) : ℤ)) (by omega)]
  simp only [Units.smul_def, map_zsmul, homToSingleRawDegreeEquiv_toSingleMk]
  congr 1
  rw [K.extend_d_eq ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f (n+1) = -((n+1 : ℕ) : ℤ) by rfl)
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) by rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The precise degreewise sign normalization. -/
def homToSingleDegreeEquiv (n : ℕ) :
    Cochain (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ) ≃ₗ[R] (K.X n ⟶ Y) :=
  (homToSingleRawDegreeEquiv R K Y n).trans (homDualSignLinearEquiv R _ n)

/-- A genuine isomorphism of the entire ordinary coefficient complex,
with every degree sign in the actual Hom differential accounted for. -/
def homToSingleRestrictionIso :
    (linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).restriction ComplexShape.embeddingUpNat ≅
        ordinaryChainCoefficients R K Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homToSingleDegreeEquiv R K Y n).toModuleIso)
    (fun n m hnm => by
      obtain rfl : n+1=m := hnm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change K.d (n+1) n ≫ (homDualSign n • homToSingleRawDegreeEquiv R K Y n z) =
        homDualSign (n+1) • homToSingleRawDegreeEquiv R K Y (n+1)
          (δ (n : ℤ) ((n+1 : ℕ) : ℤ) z)
      rw [homToSingleRawDegreeEquiv_d, smul_smul, homDualSign_step,
        Linear.comp_units_smul])

end ToricPower
