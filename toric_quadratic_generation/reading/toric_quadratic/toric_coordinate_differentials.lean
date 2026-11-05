module

public import PaperVerification.ToricChartFaceLocalization
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.SMul

@[expose] public section

/-!
# Actual Kähler differentials in integral toric coordinates

A full smooth coordinate chart is identified with the actual polynomial
algebra by its character coordinates. Its differential basis is obtained
from the universal Kähler module, and localization proves the corresponding
basis in the actual Laurent character ring. Multiplying by inverse
characters gives the logarithmic differential basis.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical TensorProduct

variable (k : Type*) [CommRing k]

section PolynomialPresentation

variable {ι A : Type*} [CommRing A] [Algebra k A]

/-- The differential basis transported through an actual polynomial
algebra equivalence. Both the universal module and its scalar action are
the ordinary Mathlib Kähler constructions. -/
def polynomialDifferentialBasis (e : MvPolynomial ι k ≃ₐ[k] A) :
    Module.Basis ι A Ω[A⁄k] := by
  letI : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e.toAlgHom
  let eA : MvPolynomial ι k ≃ₐ[MvPolynomial ι k] A :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.of_equiv eA
  exact ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) A)

@[simp] theorem polynomialDifferentialBasis_apply
    (e : MvPolynomial ι k ≃ₐ[k] A) (i : ι) :
    polynomialDifferentialBasis k e i = D k A (e (MvPolynomial.X i)) := by
  letI : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e.toAlgHom
  let eA : MvPolynomial ι k ≃ₐ[MvPolynomial ι k] A :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (MvPolynomial ι k) A := Algebra.FormallyEtale.of_equiv eA
  simp only [polynomialDifferentialBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  change KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) A
    (1 ⊗ₜ[MvPolynomial ι k] D k (MvPolynomial ι k) (MvPolynomial.X i)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

end PolynomialPresentation

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]

def fullCoordinateFunctionsEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι → ℕ) where
  toFun x i := (b.repr (x : E) i).toNat
  invFun x := ⟨b.equivFun.symm (fun i => (x i : ℤ)), by
    intro i hi
    change 0 ≤ b.equivFun (b.equivFun.symm _) i
    rw [b.equivFun.apply_symm_apply]
    exact Int.natCast_nonneg _⟩
  left_inv x := by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rw [b.equivFun.apply_symm_apply]
    exact Int.toNat_of_nonneg (x.property i (Finset.mem_univ i))
  right_inv x := by
    funext i
    change (b.equivFun (b.equivFun.symm _) i).toNat = x i
    rw [b.equivFun.apply_symm_apply, Int.toNat_natCast]
  map_add' x y := by
    funext i
    change (b.repr ((x : E) + (y : E)) i).toNat =
      (b.repr (x : E) i).toNat + (b.repr (y : E) i).toNat
    rw [map_add, Finsupp.add_apply, Int.toNat_add
      (x.property i (Finset.mem_univ i)) (y.property i (Finset.mem_univ i))]

def fullCoordinateFinsuppEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι →₀ ℕ) :=
  (fullCoordinateFunctionsEquiv b).trans (naturalFunctionFinsuppEquiv ι)

theorem basis_mem_fullCoordinateCone (b : Module.Basis ι ℤ E) (i : ι) :
    b i ∈ coordinateConeMonoid b Finset.univ := by
  intro j hj
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem fullCoordinateFinsuppEquiv_basis (b : Module.Basis ι ℤ E) (i : ι) :
    fullCoordinateFinsuppEquiv b ⟨b i, basis_mem_fullCoordinateCone b i⟩ =
      Finsupp.single i 1 := by
  ext j
  simp [fullCoordinateFinsuppEquiv, fullCoordinateFunctionsEquiv,
    naturalFunctionFinsuppEquiv, Module.Basis.repr_self_apply]
  by_cases hij : i = j <;> simp [Finsupp.single_apply, hij]

def fullChartPolynomialEquiv (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) ≃ₐ[k] MvPolynomial ι k :=
  (monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)).symm.trans
    (AddMonoidAlgebra.domCongr k k (fullCoordinateFinsuppEquiv b))

@[simp] theorem fullChartPolynomialEquiv_character (b : Module.Basis ι ℤ E) (i : ι) :
    fullChartPolynomialEquiv k b
      (chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i)) = MvPolynomial.X i := by
  have hchar : monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)
      (single ⟨b i, basis_mem_fullCoordinateCone b i⟩ 1) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) := by
    apply Subtype.ext
    exact monoidChartMap_single k _ _ _
  rw [fullChartPolynomialEquiv, AlgEquiv.trans_apply, ← hchar,
    AlgEquiv.symm_apply_apply, AddMonoidAlgebra.domCongr_single,
    fullCoordinateFinsuppEquiv_basis]
  rfl

@[simp] theorem fullChartPolynomialEquiv_symm_X (b : Module.Basis ι ℤ E) (i : ι) :
    (fullChartPolynomialEquiv k b).symm (MvPolynomial.X i) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) :=
  (fullChartPolynomialEquiv k b).symm_apply_eq.mpr
    (fullChartPolynomialEquiv_character k b i).symm

def fullChartDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (monoidChartAlgebra k (coordinateConeMonoid b Finset.univ))
      Ω[monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)⁄k] :=
  polynomialDifferentialBasis k (fullChartPolynomialEquiv k b).symm

@[simp] theorem fullChartDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    fullChartDifferentialBasis k b i = D k _
      (chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i)) := by
  rw [fullChartDifferentialBasis, polynomialDifferentialBasis_apply,
    fullChartPolynomialEquiv_symm_X]

def unconstrainedChartEquiv (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b ∅) ≃ₐ[k] AddMonoidAlgebra k E :=
  AlgEquiv.ofBijective (Subalgebra.val _) ⟨Subtype.val_injective, by
    intro f
    refine ⟨⟨f, (mem_monoidChartAlgebra k _ f).mpr ?_⟩, rfl⟩
    intro m hm i hi
    exact (Finset.notMem_empty i hi).elim⟩

def fullChartDenominator (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) :=
  chartCharacter k _ (faceDenominatorExponent b ∅ Finset.univ)
    (faceDenominatorExponent_mem b ∅ Finset.univ)

theorem laurent_isLocalization_fullChart (b : Module.Basis ι ℤ E) :
    IsLocalization.Away (fullChartDenominator k b) (AddMonoidAlgebra k E) := by
  apply (isLocalization_iff_isLocalizationMap _ _).mpr
  have hloc := coordinateChartInclusion_isLocalizationMap k b
    (Finset.empty_subset (Finset.univ : Finset ι))
  exact hloc.mulEquiv_comp (unconstrainedChartEquiv k b).toMulEquiv

/-- Localizing the actual universal differential module gives a basis of
the Laurent differential module consisting of the character differentials. -/
def laurentDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (AddMonoidAlgebra k E) Ω[AddMonoidAlgebra k E⁄k] := by
  let S := monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)
  letI := laurent_isLocalization_fullChart k b
  exact (fullChartDifferentialBasis k b).ofIsLocalizedModule (AddMonoidAlgebra k E)
    (Submonoid.powers (fullChartDenominator k b))
    (KaehlerDifferential.map k k S (AddMonoidAlgebra k E))

@[simp] theorem laurentDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    laurentDifferentialBasis k b i = D k (AddMonoidAlgebra k E) (single (b i) 1) := by
  simp only [laurentDifferentialBasis, Module.Basis.ofIsLocalizedModule_apply,
    fullChartDifferentialBasis_apply, KaehlerDifferential.map_D]
  rfl

def groupCharacterUnit (m : E) : (AddMonoidAlgebra k E)ˣ where
  val := single m 1
  inv := single (-m) 1
  val_inv := by simp [AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.one_def]

@[simp] theorem groupCharacterUnit_val (m : E) :
    (groupCharacterUnit k m : AddMonoidAlgebra k E) = single m 1 := rfl

def logDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (AddMonoidAlgebra k E) Ω[AddMonoidAlgebra k E⁄k] :=
  (laurentDifferentialBasis k b).unitsSMul (fun i => groupCharacterUnit k (-b i))

@[simp] theorem logDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    logDifferentialBasis k b i = single (-b i) (1 : k) • D k (AddMonoidAlgebra k E) (single (b i) 1) := by
  simp only [logDifferentialBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    groupCharacterUnit_val, laurentDifferentialBasis_apply]

end PaperVerification.ToricCharacters
