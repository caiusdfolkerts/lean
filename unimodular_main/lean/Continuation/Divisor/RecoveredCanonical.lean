module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Continuation.Divisor.FanDimension
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity

@[expose] public section
noncomputable section

/-! Recovered intrinsic canonical-sheaf proof; exact source provenance in the adjacent manifest. -/

section Source_ToricCoordinateDifferentials

/-!
# Actual Kähler differentials in integral toric coordinates

A full smooth coordinate chart is identified with the actual polynomial
algebra by its character coordinates. Its differential basis is obtained
from the universal Kähler module, and localization proves the corresponding
basis in the actual Laurent character ring. Multiplying by inverse
characters gives the logarithmic differential basis.
-/


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

end Source_ToricCoordinateDifferentials

section Source_ToricLogarithmicVolume

/-!
# The logarithmic character volume form

Logarithmic differentials are defined using the universal Kähler
derivation, and additivity is proved by the Leibniz rule. An integral basis
gives their genuine Laurent-module basis. The actual top exterior power
then changes by the determinant of an integral basis change. In a smooth
polynomial chart its regular volume is the product of the coordinates
times this logarithmic volume.
-/


namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical

section Exterior

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ}

theorem alternating_eq_basis_determinant (b : Module.Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) : f = b.det.smulRight (f b) := by
  apply b.ext_alternating
  intro v hv
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change f (b ∘ σ) = b.det (b ∘ σ) • f b
  simp only [AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def,
    Int.smul_one_eq_cast, Int.cast_smul_eq_zsmul]

/-- The actual top exterior power of a finite free module is a rank-one
module, with coefficient given by the determinant in the chosen basis. -/
def basisTopExteriorEquiv (b : Module.Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R := by
  let f : (⋀[R]^n M) →ₗ[R] R := exteriorPower.alternatingMapLinearEquiv b.det
  let w := exteriorPower.ιMulti R n b
  refine { f with invFun := fun r => r • w, left_inv := ?_, right_inv := ?_ }
  · intro x
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨v, rfl⟩
      change f (exteriorPower.ιMulti R n v) • w = exteriorPower.ιMulti R n v
      rw [show f (exteriorPower.ιMulti R n v) = b.det v from
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v]
      exact (congrArg (fun F => F v)
        (alternating_eq_basis_determinant b (exteriorPower.ιMulti R n))).symm
    · change f 0 • w = 0
      rw [map_zero, zero_smul]
    · intro x y hx hy ihx ihy
      change f (x + y) • w = x + y
      change f x • w = x at ihx
      change f y • w = y at ihy
      rw [map_add, add_smul, ihx, ihy]
    · intro r x hx ihx
      change f (r • x) • w = r • x
      change f x • w = x at ihx
      rw [map_smul, smul_eq_mul, mul_smul, ihx]
  · intro r
    change f (r • exteriorPower.ιMulti R n b) = r
    rw [map_smul, show f (exteriorPower.ιMulti R n b) = b.det b from
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det b,
      Module.Basis.det_self, smul_eq_mul, mul_one]

@[simp] theorem basisTopExteriorEquiv_wedge (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp] theorem basisTopExteriorEquiv_basis (b : Module.Basis (Fin n) R M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n b) = 1 := by
  rw [basisTopExteriorEquiv_wedge, Module.Basis.det_self]

end Exterior

variable (k : Type*) [CommRing k] {E : Type*} [AddCommGroup E] [Module ℤ E]

def logDifferential (m : E) : Ω[AddMonoidAlgebra k E⁄k] :=
  single (-m) (1 : k) • D k (AddMonoidAlgebra k E) (single m 1)

@[simp] theorem logDifferential_zero : logDifferential k (0 : E) = 0 := by
  simp [logDifferential, ← AddMonoidAlgebra.one_def]

theorem logDifferential_add (m p : E) :
    logDifferential k (m + p) = logDifferential k m + logDifferential k p := by
  have hprod : (single (m + p) (1 : k)) = single m 1 * single p 1 := by simp
  have hm : -(m + p) + m = -p := by abel
  have hp : -(m + p) + p = -m := by abel
  unfold logDifferential
  rw [hprod, Derivation.leibniz, smul_add, smul_smul, smul_smul]
  simp only [single_mul_single, one_mul, hm, hp]
  exact add_comm _ _

def logDifferentialAddHom : E →+ Ω[AddMonoidAlgebra k E⁄k] where
  toFun := logDifferential k
  map_zero' := logDifferential_zero k
  map_add' := logDifferential_add k

@[simp] theorem logDifferential_zsmul (m : E) (z : ℤ) :
    logDifferential k (z • m) = z • logDifferential k m :=
  (logDifferentialAddHom k).map_zsmul z m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem logDifferentialBasis_eq (b : Module.Basis ι ℤ E) (i : ι) :
    logDifferentialBasis k b i = logDifferential k (b i) :=
  logDifferentialBasis_apply k b i

theorem logDifferential_expansion (b : Module.Basis ι ℤ E) (m : E) :
    logDifferential k m =
      ∑ i, (b.repr m i : AddMonoidAlgebra k E) • logDifferential k (b i) := by
  calc
    logDifferential k m = logDifferential k (∑ i, b.repr m i • b i) := by
      apply congrArg (logDifferential k)
      calc
        m = ∑ i, (inferInstance : Module ℤ E).smul (b.repr m i) (b i) :=
          (b.sum_repr m).symm
        _ = _ := Finset.sum_congr rfl (fun i _ =>
          int_smul_eq_zsmul (inferInstance : Module ℤ E) (b.repr m i) (b i))
    _ = ∑ i, (b.repr m i : ℤ) • logDifferential k (b i) := by
      exact (map_sum (logDifferentialAddHom k (E := E)) _ _).trans (by
        congr 1
        funext i
        exact logDifferential_zsmul k (b i) (b.repr m i))
    _ = _ := by simp only [Int.cast_smul_eq_zsmul]

theorem logDifferentialBasis_repr (b : Module.Basis ι ℤ E) (m : E) (i : ι) :
    (logDifferentialBasis k b).repr (logDifferential k m) i = (b.repr m i : AddMonoidAlgebra k E) := by
  have hrepr (j : ι) : (logDifferentialBasis k b).repr (logDifferential k (b j)) =
      Finsupp.single j 1 := by
    rw [← logDifferentialBasis_eq, Module.Basis.repr_self]
  rw [logDifferential_expansion k b m]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, hrepr]
  simp [Finsupp.single_apply]

theorem character_differential_eq_smul_log (m : E) :
    D k (AddMonoidAlgebra k E) (single m 1) = single m (1 : k) • logDifferential k m := by
  rw [logDifferential, smul_smul]
  simp [← AddMonoidAlgebra.one_def]

section TopVolume

variable {n : ℕ}

def logVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n (logDifferentialBasis k b)

def regularCoordinateVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n
    (fun i => D k (AddMonoidAlgebra k E) (single (b i) 1))

theorem logDifferentialBasis_det (b c : Module.Basis (Fin n) ℤ E) :
    (logDifferentialBasis k b).det (logDifferentialBasis k c) =
      (b.det c : AddMonoidAlgebra k E) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix : (logDifferentialBasis k b).toMatrix (logDifferentialBasis k c) =
      (Int.castRingHom (AddMonoidAlgebra k E)).mapMatrix (b.toMatrix c) := by
    funext i j
    change (logDifferentialBasis k b).repr (logDifferentialBasis k c j) i =
      (b.repr (c j) i : AddMonoidAlgebra k E)
    rw [logDifferentialBasis_eq, logDifferentialBasis_repr]
  rw [hmatrix, ← RingHom.map_det]
  rfl

/-- The transition factor is the genuine determinant of the unimodular
integral character change of basis. -/
theorem logVolume_change_basis (b c : Module.Basis (Fin n) ℤ E) :
    logVolume k c = (b.det c : AddMonoidAlgebra k E) • logVolume k b := by
  have h := congrArg (fun f => f (logDifferentialBasis k c))
    (alternating_eq_basis_determinant (logDifferentialBasis k b)
      (exteriorPower.ιMulti (AddMonoidAlgebra k E) n))
  change logVolume k c = (logDifferentialBasis k b).det (logDifferentialBasis k c) •
    logVolume k b at h
  rw [logDifferentialBasis_det] at h
  exact h

theorem logVolume_transition_isUnit (b c : Module.Basis (Fin n) ℤ E) :
    IsUnit (b.det c : AddMonoidAlgebra k E) :=
  (b.isUnit_det c).map (Int.castRingHom (AddMonoidAlgebra k E))

/-- In a smooth full chart the regular differential volume has precisely
one copy of every coordinate character relative to the logarithmic volume. -/
theorem regularCoordinateVolume_eq_character_logVolume (b : Module.Basis (Fin n) ℤ E) :
    regularCoordinateVolume k b = single (∑ i, b i) (1 : k) • logVolume k b := by
  unfold regularCoordinateVolume
  simp_rw [character_differential_eq_smul_log]
  rw [AlternatingMap.map_smul_univ]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  exact congrArg (exteriorPower.ιMulti (AddMonoidAlgebra k E) n)
    (funext (fun i => (logDifferentialBasis_eq k b i).symm))

end TopVolume

end PaperVerification.ToricCharacters

end Source_ToricLogarithmicVolume

section Source_ToricFractionDifferentials

/-!
# Differential forms in the actual character fraction field

All maps in this file come from the universal Kähler derivation and its
localization theorem.  In particular, the map from a chart's top exterior
power is the exterior extension of the actual differential map; its
principal image is a conclusion, not part of the definition.
-/


namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical

section ExteriorExtension

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {n : ℕ}

/-- Extension of scalars for actual exterior forms, constructed from the
universal alternating map.  The source and target exterior powers retain
their respective coefficient rings. -/
def exteriorScalarExtensionMap (f : M →ₗ[R] N) :
    (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) := by
  let a : N [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { (exteriorPower.ιMulti S n (M := N)).toMultilinearMap.restrictScalars R with
      map_eq_zero_of_eq' := fun v i j hij hne =>
        (exteriorPower.ιMulti S n).map_eq_zero_of_eq v hij hne }
  exact exteriorPower.alternatingMapLinearEquiv (a.compLinearMap f)

@[simp] theorem exteriorScalarExtensionMap_wedge (f : M →ₗ[R] N) (v : Fin n → M) :
    exteriorScalarExtensionMap (S := S) f (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => f (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem topExterior_eq_smul_basis (b : Module.Basis (Fin n) R M)
    (x : ⋀[R]^n M) :
    x = basisTopExteriorEquiv b x • exteriorPower.ιMulti R n b :=
  ((basisTopExteriorEquiv b).symm_apply_apply x).symm

end ExteriorExtension

variable (k : Type*) [CommRing k] {E : Type*} [AddCommGroup E] [Module ℤ E]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k E) K]
    [IsScalarTower k (AddMonoidAlgebra k E) K]
    [IsFractionRing (AddMonoidAlgebra k E) K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordinary Kähler differential basis after localization to the
actual fraction field of the character ring. -/
def fractionLogDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι K Ω[K⁄k] :=
  (logDifferentialBasis k b).ofIsLocalizedModule K
    (nonZeroDivisors (AddMonoidAlgebra k E))
    (KaehlerDifferential.map k k (AddMonoidAlgebra k E) K)

def fractionLogDifferential (m : E) : Ω[K⁄k] :=
  algebraMap (AddMonoidAlgebra k E) K (single (-m) 1) •
    D k K (algebraMap (AddMonoidAlgebra k E) K (single m 1))

@[simp] theorem map_logDifferential (m : E) :
    KaehlerDifferential.map k k (AddMonoidAlgebra k E) K (logDifferential k m) =
      fractionLogDifferential k K m := by
  rw [logDifferential, map_smul, KaehlerDifferential.map_D]
  exact (IsScalarTower.algebraMap_smul K _ _).symm

@[simp] theorem fractionLogDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    fractionLogDifferentialBasis k K b i = fractionLogDifferential k K (b i) := by
  rw [fractionLogDifferentialBasis, Module.Basis.ofIsLocalizedModule_apply,
    logDifferentialBasis_eq, map_logDifferential]

theorem fractionLogDifferentialBasis_repr (b : Module.Basis ι ℤ E) (m : E) (i : ι) :
    (fractionLogDifferentialBasis k K b).repr (fractionLogDifferential k K m) i =
      (b.repr m i : K) := by
  rw [← map_logDifferential, fractionLogDifferentialBasis,
    Module.Basis.ofIsLocalizedModule_repr_apply, logDifferentialBasis_repr, map_intCast]

theorem fraction_character_differential (m : E) :
    D k K (algebraMap (AddMonoidAlgebra k E) K (single m 1)) =
      algebraMap (AddMonoidAlgebra k E) K (single m 1) •
        fractionLogDifferential k K m := by
  rw [fractionLogDifferential, smul_smul, ← map_mul]
  simp only [single_mul_single, add_neg_cancel, mul_one,
    ← AddMonoidAlgebra.one_def, map_one, one_smul]

section Top

variable {n : ℕ}

def fractionLogVolume (b : Module.Basis (Fin n) ℤ E) : ⋀[K]^n Ω[K⁄k] :=
  exteriorPower.ιMulti K n (fractionLogDifferentialBasis k K b)

def fractionRegularCoordinateVolume (b : Module.Basis (Fin n) ℤ E) : ⋀[K]^n Ω[K⁄k] :=
  exteriorPower.ιMulti K n
    (fun i => D k K (algebraMap (AddMonoidAlgebra k E) K (single (b i) 1)))

theorem fractionLogDifferentialBasis_det (b c : Module.Basis (Fin n) ℤ E) :
    (fractionLogDifferentialBasis k K b).det (fractionLogDifferentialBasis k K c) =
      (b.det c : K) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix :
      (fractionLogDifferentialBasis k K b).toMatrix (fractionLogDifferentialBasis k K c) =
        (Int.castRingHom K).mapMatrix (b.toMatrix c) := by
    ext i j
    change (fractionLogDifferentialBasis k K b).repr
      (fractionLogDifferentialBasis k K c j) i = (b.repr (c j) i : K)
    rw [fractionLogDifferentialBasis_apply, fractionLogDifferentialBasis_repr]
  rw [hmatrix, ← RingHom.map_det]
  rfl

theorem fractionLogVolume_change_basis (b c : Module.Basis (Fin n) ℤ E) :
    fractionLogVolume k K c = (b.det c : K) • fractionLogVolume k K b := by
  have h := congrArg (fun f => f (fractionLogDifferentialBasis k K c))
    (alternating_eq_basis_determinant (fractionLogDifferentialBasis k K b)
      (exteriorPower.ιMulti K n))
  change fractionLogVolume k K c =
    (fractionLogDifferentialBasis k K b).det (fractionLogDifferentialBasis k K c) •
      fractionLogVolume k K b at h
  rw [fractionLogDifferentialBasis_det] at h
  exact h

theorem fractionRegularCoordinateVolume_eq_character
    (b : Module.Basis (Fin n) ℤ E) :
    fractionRegularCoordinateVolume k K b =
      algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) •
        fractionLogVolume k K b := by
  unfold fractionRegularCoordinateVolume
  simp_rw [fraction_character_differential]
  rw [AlternatingMap.map_smul_univ, ← map_prod]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  exact congrArg (exteriorPower.ιMulti K n)
    (funext (fun i => (fractionLogDifferentialBasis_apply k K b i).symm))

variable (b : Module.Basis (Fin n) ℤ E)

local notation "S" => monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)

-- The chart acts through its canonical inclusion into the character algebra
-- and the already supplied character-algebra map to K.  In particular, the
-- algebra and inherited subalgebra actions are the same actual action.

/-- Coefficients of genuine regular top differential forms in a chosen
generic logarithmic volume. This is defined from the differential map,
without a monomial or divisor formula. -/
def chartTopDifferentialCoefficient (b₀ : Module.Basis (Fin n) ℤ E) :
    (⋀[S]^n Ω[S⁄k]) →ₗ[S] K := by
  let d : Ω[S⁄k] →ₗ[S] Ω[K⁄k] := KaehlerDifferential.map k k S K
  let e : (⋀[S]^n Ω[S⁄k]) →ₗ[S] (⋀[K]^n Ω[K⁄k]) :=
    exteriorScalarExtensionMap (R := S) («S» := K)
      (M := KaehlerDifferential k S) (N := KaehlerDifferential k K) (n := n) d
  exact ((basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)).toLinearMap.restrictScalars S).comp e

theorem chartTopDifferentialCoefficient_basis (b₀ : Module.Basis (Fin n) ℤ E) :
    chartTopDifferentialCoefficient k K b b₀
        (exteriorPower.ιMulti S n (fullChartDifferentialBasis k b)) =
      algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) * (b₀.det b : K) := by
  have hw := exteriorScalarExtensionMap_wedge (R := S) («S» := K)
    (M := KaehlerDifferential k S) (N := KaehlerDifferential k K) (n := n)
    (show Ω[S⁄k] →ₗ[S] Ω[K⁄k] from KaehlerDifferential.map k k S K)
    (fullChartDifferentialBasis k b)
  refine (congrArg (basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)) hw).trans ?_
  have hdiff (i : Fin n) :
      KaehlerDifferential.map k k S K (fullChartDifferentialBasis k b i) =
        D k K (algebraMap (AddMonoidAlgebra k E) K (single (b i) 1)) := by
    rw [fullChartDifferentialBasis_apply, KaehlerDifferential.map_D,
      IsScalarTower.algebraMap_eq S (AddMonoidAlgebra k E) K]
    rfl
  refine (congrArg
    (fun v : Fin n→Ω[K⁄k] =>
      basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
        (exteriorPower.ιMulti K n v))
    (funext hdiff)).trans ?_
  change basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
    (fractionRegularCoordinateVolume k K b) = _
  rw [fractionRegularCoordinateVolume_eq_character, map_smul,
    fractionLogVolume_change_basis k K b₀ b, map_smul]
  change _ * ((b₀.det b : K) *
    basisTopExteriorEquiv (fractionLogDifferentialBasis k K b₀)
      (exteriorPower.ιMulti K n (fractionLogDifferentialBasis k K b₀))) = _
  rw [basisTopExteriorEquiv_basis, mul_one]

/-- The principal chart formula is derived for the image of the actual
top Kähler module. The determinant is a unit because both lattices bases
are integral bases; this statement keeps the exact transition scalar. -/
theorem mem_range_chartTopDifferentialCoefficient_iff
    (b₀ : Module.Basis (Fin n) ℤ E) (z : K) :
    z ∈ LinearMap.range (chartTopDifferentialCoefficient k K b b₀) ↔
      ∃ r : S, algebraMap S K r *
        (algebraMap (AddMonoidAlgebra k E) K (single (∑ i, b i) 1) * (b₀.det b : K)) = z := by
  constructor
  · rintro ⟨ω, rfl⟩
    refine ⟨basisTopExteriorEquiv (fullChartDifferentialBasis k b) ω, ?_⟩
    conv_rhs => rw [topExterior_eq_smul_basis (fullChartDifferentialBasis k b) ω]
    rw [map_smul, chartTopDifferentialCoefficient_basis]
    exact (Algebra.smul_def _ _).symm
  · rintro ⟨r, hr⟩
    refine ⟨r • exteriorPower.ιMulti S n (fullChartDifferentialBasis k b), ?_⟩
    rw [map_smul, chartTopDifferentialCoefficient_basis]
    exact (Algebra.smul_def _ _).trans hr

end Top

end PaperVerification.ToricCharacters

end Source_ToricFractionDifferentials

section Source_ToricIntrinsicDifferentialSheaf

/-!
# Intrinsic Kähler sheaves and their ordinary exterior powers

These constructions are defined on every scheme over the base ring,
independently of a fan or a rational differential trivialization. The
cotangent sheaf is the sheafification of the universal Kähler presheaf.
Its universal property for derivations into every actual module sheaf is
proved from the universal algebraic derivation and the sheafification
adjunction. Exterior powers are the sheafifications of the ordinary
sectionwise exterior modules.
-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters
open scoped Classical BaseSections

section Exterior

variable {C : Type u} [Category C] (R : Cᵒᵖ⥤CommRingCat.{v})
    (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
def presheafExteriorPowerMap {U V : Cᵒᵖ} (f : U⟶V) :
    (M.obj U).exteriorPower n⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj V).exteriorPower n) := by
  letI := (R.map f).hom.toAlgebra
  letI := Module.compHom (M.obj V) (R.map f).hom
  letI : IsScalarTower (R.obj U) (R.obj V) (M.obj V) := IsScalarTower.of_compHom _ _ _
  exact ModuleCat.ofHom (X := (M.obj U).exteriorPower n)
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj V).exteriorPower n))
    (exteriorScalarExtensionMap (R := R.obj U) (S := R.obj V)
      (M := M.obj U) (N := M.obj V) (n := n) (M.map f).hom)

@[simp] theorem presheafExteriorPowerMap_wedge {U V : Cᵒᵖ} (f : U⟶V)
    (x : Fin n→M.obj U) :
    presheafExteriorPowerMap R M n f (exteriorPower.ιMulti (R.obj U) n x)=
      exteriorPower.ιMulti (R.obj V) n (fun i=>M.map f (x i)) := by
  letI := (R.map f).hom.toAlgebra
  letI := Module.compHom (M.obj V) (R.map f).hom
  letI : IsScalarTower (R.obj U) (R.obj V) (M.obj V) := IsScalarTower.of_compHom _ _ _
  exact exteriorScalarExtensionMap_wedge (R := R.obj U) (S := R.obj V)
    (M := M.obj U) (N := M.obj V) (n := n) (M.map f).hom x

set_option maxHeartbeats 2000000 in
theorem presheafExteriorPowerMap_id (U : Cᵒᵖ) :
    presheafExteriorPowerMap R M n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (R.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (R.map_id U))).inv.app
          ((M.obj U).exteriorPower n) := by
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
    (N := (ModuleCat.restrictScalars (R.map (𝟙 U)).hom).obj ((M.obj U).exteriorPower n))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change presheafExteriorPowerMap R M n (𝟙 U)
    (exteriorPower.ιMulti (R.obj U) n x) = exteriorPower.ιMulti (R.obj U) n x
  rw [presheafExteriorPowerMap_wedge]
  congr 1
  funext i
  exact congrArg (fun φ => φ (x i)) (M.map_id U)

set_option maxHeartbeats 2000000 in
theorem presheafExteriorPowerMap_comp {U V W : Cᵒᵖ} (f : U⟶V) (g : V⟶W) :
    presheafExteriorPowerMap R M n (f ≫ g) =
      presheafExteriorPowerMap R M n f ≫
        (ModuleCat.restrictScalars (R.map f).hom).map (presheafExteriorPowerMap R M n g) ≫
          (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom
            (R.map (f ≫ g)).hom (congrArg CommRingCat.Hom.hom (R.map_comp f g))).inv.app
              ((M.obj W).exteriorPower n) := by
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
    (N := (ModuleCat.restrictScalars (R.map (f ≫ g)).hom).obj ((M.obj W).exteriorPower n))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change presheafExteriorPowerMap R M n (f ≫ g)
    (exteriorPower.ιMulti (R.obj U) n x) =
      presheafExteriorPowerMap R M n g
        (presheafExteriorPowerMap R M n f (exteriorPower.ιMulti (R.obj U) n x))
  calc
    _ = exteriorPower.ιMulti (R.obj W) n
        (fun i : Fin n => (show M.obj W from M.map (f ≫ g) (x i))) :=
      presheafExteriorPowerMap_wedge R M n (f ≫ g) x
    _ = exteriorPower.ιMulti (R.obj W) n
        (fun i : Fin n => (show M.obj W from M.map g (M.map f (x i)))) :=
      congrArg (fun y : Fin n → M.obj W => exteriorPower.ιMulti (R.obj W) n y)
        (funext (fun i => PresheafOfModules.map_comp_apply M f g (x i)))
    _ = presheafExteriorPowerMap R M n g
        (exteriorPower.ιMulti (R.obj V) n
          (fun i : Fin n => (show M.obj V from M.map f (x i)))) :=
      (presheafExteriorPowerMap_wedge R M n g
        (fun i : Fin n => (show M.obj V from M.map f (x i)))).symm
    _ = _ := congrArg (presheafExteriorPowerMap R M n g)
      (presheafExteriorPowerMap_wedge R M n f x).symm

set_option backward.isDefEq.respectTransparency false in
def presheafExteriorPower : PresheafOfModulesOfCommRing.{v} R :=
  PresheafOfModulesOfCommRing.mk (R := R)
    (fun U=>(M.obj U).exteriorPower n)
    (fun f=>presheafExteriorPowerMap R M n f)
    (presheafExteriorPowerMap_id R M n)
    (fun f g=>presheafExteriorPowerMap_comp R M n f g)

@[simp] theorem presheafExteriorPower_map_wedge {U V : Cᵒᵖ} (f : U⟶V)
    (x : Fin n→M.obj U) :
    (presheafExteriorPower R M n).map f (exteriorPower.ιMulti (R.obj U) n x)=
      exteriorPower.ιMulti (R.obj V) n (fun i=>M.map f (x i)) :=
  presheafExteriorPowerMap_wedge R M n f x

variable {M} {N : PresheafOfModulesOfCommRing.{v} R}

set_option maxHeartbeats 2000000 in
def presheafExteriorPowerHom (f : M⟶N) :
    presheafExteriorPower R M n⟶presheafExteriorPower R N n :=
  PresheafOfModulesOfCommRing.homMk (R := R)
    (fun U=>ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n)
    (by
      intro U V g
      apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U)
        (N := (ModuleCat.restrictScalars (R.map g).hom).obj ((N.obj V).exteriorPower n))
      apply ModuleCat.AlternatingMap.ext
      intro x
      change ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n
          (presheafExteriorPowerMap R M n g (exteriorPower.ιMulti (R.obj U) n x)) =
        presheafExteriorPowerMap R N n g
          (ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n
            (exteriorPower.ιMulti (R.obj U) n x))
      calc
        _ = ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n
            (exteriorPower.ιMulti (R.obj V) n
              (fun i : Fin n => (show M.obj V from M.map g (x i)))) :=
          congrArg (ModuleCat.exteriorPower.map (R := R.obj V) (f.app V) n)
            (presheafExteriorPowerMap_wedge R M n g x)
        _ = exteriorPower.ιMulti (R.obj V) n
            (fun i : Fin n => f.app V (M.map g (x i))) :=
          ModuleCat.exteriorPower.map_mk (R := R.obj V) (f.app V)
            (fun i : Fin n => (show M.obj V from M.map g (x i)))
        _ = exteriorPower.ιMulti (R.obj V) n
            (fun i : Fin n => (show N.obj V from N.map g (f.app U (x i)))) :=
          congrArg (fun y : Fin n → N.obj V => exteriorPower.ιMulti (R.obj V) n y)
            (funext (fun i => PresheafOfModules.naturality_apply f g (x i)))
        _ = presheafExteriorPowerMap R N n g
            (exteriorPower.ιMulti (R.obj U) n (fun i : Fin n => f.app U (x i))) :=
          (presheafExteriorPowerMap_wedge R N n g (fun i => f.app U (x i))).symm
        _ = _ := congrArg (presheafExteriorPowerMap R N n g)
          (ModuleCat.exteriorPower.map_mk (R := R.obj U) (f.app U) x).symm)

def presheafExteriorPowerFunctor :
    PresheafOfModulesOfCommRing.{v} R⥤PresheafOfModulesOfCommRing.{v} R where
  obj M := presheafExteriorPower R M n
  map f := presheafExteriorPowerHom R n f
  map_id M := by
    ext U : 1
    change ModuleCat.exteriorPower.map (R := R.obj U) (𝟙 (M.obj U)) n = 𝟙 _
    exact (ModuleCat.exteriorPower.functor (R.obj U) n).map_id (M.obj U)
  map_comp f g := by
    ext U : 1
    change ModuleCat.exteriorPower.map (R := R.obj U) (f.app U ≫ g.app U) n =
      ModuleCat.exteriorPower.map (R := R.obj U) (f.app U) n ≫
        ModuleCat.exteriorPower.map (R := R.obj U) (g.app U) n
    exact (ModuleCat.exteriorPower.functor (R.obj U) n).map_comp (f.app U) (g.app U)

end Exterior

section Schemes

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]

/-- The actual constant base-ring presheaf maps into the actual structure
presheaf through the given structural morphism of the scheme. -/
def scalarPresheafMap :
    (Functor.const X.Opensᵒᵖ).obj (CommRingCat.of k)⟶X.presheaf where
  app U := CommRingCat.ofHom (BaseSections.scalarMap k X U.unop)
  naturality U V f := by
    ext c
    exact (BaseSections.scalarMap_restrict k f.unop.le c).symm

def differentialPresheaf : PresheafOfModulesOfCommRing.{u} X.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (scalarPresheafMap k X)

def differentialPresheafDerivation :
    (differentialPresheaf k X).Derivation' (scalarPresheafMap k X) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (scalarPresheafMap k X)

def differentialPresheafUniversal :
    (differentialPresheafDerivation k X).Universal :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
    (scalarPresheafMap k X)

/-- The intrinsic relative Kähler sheaf. -/
def differentialSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (differentialPresheaf k X)

def differentialSheafUnit : differentialPresheaf k X⟶(differentialSheaf k X).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

def differentialSheafDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf)
      (differentialSheaf k X).val (scalarPresheafMap k X) :=
  (differentialPresheafDerivation k X).postcomp (differentialSheafUnit k X)

def differentialPresheafHomEquiv (M : PresheafOfModulesOfCommRing.{u} X.presheaf) :
    (differentialPresheaf k X⟶M) ≃ M.Derivation' (scalarPresheafMap k X) where
  toFun f := (differentialPresheafDerivation k X).postcomp f
  invFun d := (differentialPresheafUniversal k X).desc d
  left_inv f := (differentialPresheafUniversal k X).postcomp_injective _ _
    ((differentialPresheafUniversal k X).fac _)
  right_inv d := (differentialPresheafUniversal k X).fac d

/-- The defining universal property of the actual sheaf of Kähler
differentials, for every actual sheaf of structure modules. -/
def differentialSheafHomEquiv (M : X.Modules) :
    (differentialSheaf k X⟶M) ≃
      PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf) M.val
        (scalarPresheafMap k X) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (differentialPresheaf k X) M).trans (differentialPresheafHomEquiv k X M.val)

theorem differentialSheafHomEquiv_apply (M : X.Modules)
    (f : differentialSheaf k X⟶M) :
    differentialSheafHomEquiv k X M f=
      (differentialSheafDerivation k X).postcomp f.val := by
  ext U r
  change (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv (differentialPresheaf k X) M f).app U)
      ((differentialPresheafDerivation k X).d r) =
    f.val.app U (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (differentialPresheaf k X)).app U
      ((differentialPresheafDerivation k X).d r))
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The ordinary exterior power of a module sheaf, constructed by
sheafifying the ordinary exterior powers of its section modules. -/
def sheafExteriorPower (M : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (presheafExteriorPower X.presheaf M.val n)

def sheafExteriorPowerIso {M N : X.Modules} (e : M≅N) (n : ℕ) :
    sheafExteriorPower X M n≅sheafExteriorPower X N n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    ((presheafExteriorPowerFunctor X.presheaf n).mapIso
      ((SheafOfModules.forget _).mapIso e))

/-- The intrinsic top differential sheaf; on a smooth n-dimensional
scheme this is its ordinary canonical invertible sheaf. -/
def topDifferentialSheaf (n : ℕ) : X.Modules :=
  sheafExteriorPower X (differentialSheaf k X) n

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.differentialSheafHomEquiv

end Source_ToricIntrinsicDifferentialSheaf

section Source_ToricModuleBasisComparison

/-!
# Module comparisons constructed on an actual topological basis

Compatible module maps on basis opens extend uniquely to a map from a
module presheaf into a module sheaf. If the maps on the basis are
bijective, the extension becomes an isomorphism after actual
sheafification. No quasi-coherence or stalk comparison is assumed.
-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}} {ι : Type v} (B : ι→X.Opens)
    (hB : Opens.IsBasis (Set.range B))
    (P : PresheafOfModulesOfCommRing.{u} X.presheaf) (Q : X.Modules)
    (β : ∀ i,P.obj (op (B i))→ₗ[Γ(X,B i)] Γ(Q,B i))
    (hβ : ∀ i j (h : B j≤B i) (s : P.obj (op (B i))),
      β j (P.map (homOfLE h).op s)=Q.presheaf.map (homOfLE h).op (β i s))

def basisModuleComparisonOnBasis :
    (inducedFunctor B).op⋙P.presheaf ⟶ (inducedFunctor B).op⋙Q.presheaf where
  app i := AddCommGrpCat.ofHom (β i.unop).toAddMonoidHom
  naturality i j f := by
    ext s
    exact hβ i.unop j.unop f.unop.hom.le s

def basisModuleComparisonAdditive : P.presheaf⟶Q.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
    (basisModuleComparisonOnBasis B P Q β hβ)

@[simp] theorem basisModuleComparisonAdditive_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op (B i)) s=β i s := by
  exact congrArg
    (fun f : P.presheaf.obj (op (B i)) ⟶ Q.presheaf.obj (op (B i)) => f s)
    (TopCat.Sheaf.extend_hom_app P.presheaf ⟨Q.presheaf,Q.isSheaf⟩ hB
      (basisModuleComparisonOnBasis B P Q β hβ) i)

theorem basisModuleComparisonAdditive_smul (U : X.Opens)
    (a : Γ(X,U)) (s : P.obj (op U)) :
    (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) (a • s)=
      a • (basisModuleComparisonAdditive B hB P Q β hβ).app (op U) s := by
  let φ := basisModuleComparisonAdditive B hB P Q β hβ
  apply TopCat.Presheaf.IsSheaf.section_ext Q.isSheaf
  intro x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,hVU,hi,?_⟩
  erw [← NatTrans.naturality_apply φ (homOfLE hVU).op,
    Q.map_smul,← NatTrans.naturality_apply φ (homOfLE hVU).op]
  change φ.app (op (B i)) (P.map (homOfLE hVU).op (a • s))=
    X.presheaf.map (homOfLE hVU).op a • φ.app (op (B i)) (P.map (homOfLE hVU).op s)
  dsimp only [φ]
  rw [basisModuleComparisonAdditive_app,basisModuleComparisonAdditive_app]
  exact (congrArg (β i) (P.map_smul (homOfLE hVU).op a s)).trans
    ((β i).map_smul _ _)

/-- The extension is genuinely linear over the section ring on every
open, as follows from the actual sheaf separation axiom. -/
def basisModuleComparison : P⟶Q.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (fun U => ModuleCat.ofHom
      ({ toFun := (basisModuleComparisonAdditive B hB P Q β hβ).app U
         map_add' := map_add _
         map_smul' := basisModuleComparisonAdditive_smul B hB P Q β hβ U.unop } :
        P.obj U →ₗ[Γ(X,U.unop)] Γ(Q,U.unop)))
    (by
      intro U V f
      ext s
      exact NatTrans.naturality_apply
        (basisModuleComparisonAdditive B hB P Q β hβ) f s)

@[simp] theorem basisModuleComparison_app (i : ι)
    (s : P.obj (op (B i))) :
    (basisModuleComparison B hB P Q β hβ).app (op (B i)) s=β i s :=
  basisModuleComparisonAdditive_app B hB P Q β hβ i s

theorem basisModuleComparison_locallyInjective
    (hinj : ∀ i,Function.Injective (β i)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s t h x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i,homOfLE hVU,?_,hi⟩
  apply hinj i
  change β i (P.map (homOfLE hVU).op s) = β i (P.map (homOfLE hVU).op t)
  calc
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op s) :=
      (basisModuleComparison_app B hB P Q β hβ i _).symm
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U s) :=
      PresheafOfModules.naturality_apply _ _ _
    _ = Q.val.map (homOfLE hVU).op
          ((basisModuleComparison B hB P Q β hβ).app U t) :=
      congrArg (Q.presheaf.map (homOfLE hVU).op) h
    _ = (basisModuleComparison B hB P Q β hβ).app (op (B i))
          (P.map (homOfLE hVU).op t) :=
      (PresheafOfModules.naturality_apply
        (basisModuleComparison B hB P Q β hβ) (homOfLE hVU).op t).symm
    _ = β i (P.map (homOfLE hVU).op t) :=
      basisModuleComparison_app B hB P Q β hβ i _

theorem basisModuleComparison_locallySurjective
    (hsurj : ∀ i,Function.Surjective (β i)) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (basisModuleComparison B hB P Q β hβ)) := by
  constructor
  intro U s x hx
  obtain ⟨V,⟨i,rfl⟩,hi,hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  obtain ⟨t,ht⟩ := hsurj i (Q.presheaf.map (homOfLE hVU).op s)
  exact ⟨B i,homOfLE hVU,⟨t,(basisModuleComparison_app B hB P Q β hβ i t).trans ht⟩,hi⟩

theorem basisModuleComparison_sheafification_isIso
    (hbij : ∀ i,Function.Bijective (β i)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) := by
  letI := basisModuleComparison_locallyInjective B hB P Q β hβ (fun i=>(hbij i).1)
  letI := basisModuleComparison_locallySurjective B hB P Q β hβ (fun i=>(hbij i).2)
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (basisModuleComparison B hB P Q β hβ))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (basisModuleComparison B hB P Q β hβ) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison with the actual sheafification. -/
def basisModuleSheafificationIso (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P≅Q := by
  letI := basisModuleComparison_sheafification_isIso B hB P Q β hβ hbij
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (basisModuleComparison B hB P Q β hβ)) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app Q)

theorem basisModuleSheafificationIso_unit (hbij : ∀ i,Function.Bijective (β i)) :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.val=
        basisModuleComparison B hB P Q β hβ := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv P Q).symm (basisModuleComparison B hB P Q β hβ)=
      (basisModuleSheafificationIso B hB P Q β hβ hbij).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg (adj.homEquiv P Q) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

/-- The comparison after the actual sheafification unit agrees with
its specified linear map on every member of the genuine open basis. -/
theorem basisModuleSheafificationIso_app (hbij : ∀ i,Function.Bijective (β i))
    (i : ι) (s : P.obj (op (B i))) :
    (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) = β i s := by
  have h := congrArg (fun φ : P ⟶ Q.val => φ.app (op (B i)) s)
    (basisModuleSheafificationIso_unit B hB P Q β hβ hbij)
  have h' : (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s := by
    change (basisModuleSheafificationIso B hB P Q β hβ hbij).hom.app (B i)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op (B i)) s) =
      (basisModuleComparison B hB P Q β hβ).app (op (B i)) s at h
    exact h
  exact h'.trans (basisModuleComparison_app B hB P Q β hβ i s)

end PaperVerification.ToricSchemes

end Source_ToricModuleBasisComparison

section Source_ToricAffineDifferentialSheaf

/-!
# The intrinsic differential sheaf on an actual affine scheme

On every principal open D(f), the universal Kähler module of the actual
regular-function ring and the sections of the actual tilde module are
both localizations of Ω[R/k]. Their unique localization isomorphism
commutes with the actual restriction maps. Extending on the principal
open basis and sheafifying proves the affine comparison, without
postulating quasi-coherence of the differential sheaf.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

attribute [local instance] SMulCommClass.of_commMonoid

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

local notation "X" => Spec (CommRingCat.of R)
local notation "ΩR" => KaehlerDifferential k R
local notation "M" => ModuleCat.of R ΩR
local notation "P" => differentialPresheaf k X
local notation "Q" => tilde (R := CommRingCat.of R) M

local instance affineBaseSectionsAlgebra (U : (X).Opens) : Algebra k Γ(X,U) :=
  BaseSections.sectionsAlgebra k X U

local instance affineCoordinateAlgebra (U : (X).Opens) : Algebra R Γ(X,U) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf (CommRingCat.of R)).presheaf.obj (op U)))

local instance affinePrincipalLocalization (f : R) :
    IsLocalization.Away f Γ(X,PrimeSpectrum.basicOpen f) :=
  inferInstanceAs (IsLocalization.Away (f : CommRingCat.of R)
    ((Spec.structureSheaf (CommRingCat.of R)).obj.obj (op (PrimeSpectrum.basicOpen f))))

local instance affineTildeSectionsModule (U : (X).Opens) : Module R Γ(Q,U) :=
  (((modulesSpecToSheaf (R := CommRingCat.of R)).obj Q).presheaf.obj (op U)).isModule

local instance affineTildeSectionsScalarTower (U : (X).Opens) :
    IsScalarTower R Γ(X,U) Γ(Q,U) :=
  IsScalarTower.of_compHom R Γ(X,U) Γ(Q,U)

local instance affineTildeToBasic_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom) :=
  IsLocalizedModule.of_linearEquiv (.powers f)
    (StructureSheaf.toOpenₗ (CommRingCat.of R) M (PrimeSpectrum.basicOpen f))
    ((tilde.modulesSpecToSheafIso (R := CommRingCat.of R) M).app _).toLinearEquiv.symm

theorem affine_base_scalar_tower (U : (X).Opens) :
    IsScalarTower k R Γ(X,U) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change BaseSections.scalarMap k X U c=
    algebraMap R Γ(X,U) (algebraMap k R c)
  change BaseSections.scalarMap k X U c=
    (X).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (algebraMap k R c))
  rw [← BaseSections.scalarMap_affine_top,
    BaseSections.scalarMap_restrict]

local instance affineBaseScalarTower (U : (X).Opens) : IsScalarTower k R Γ(X,U) :=
  affine_base_scalar_tower k R U

local instance affineDifferentialModule (U : (X).Opens) :
    Module R ((P).obj (op U)) :=
  inferInstanceAs (Module R (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialScalarTower (U : (X).Opens) :
    IsScalarTower R Γ(X,U) ((P).obj (op U)) :=
  inferInstanceAs (IsScalarTower R Γ(X,U) (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialBaseModule (U : (X).Opens) :
    Module k ((P).obj (op U)) :=
  inferInstanceAs (Module k (KaehlerDifferential k Γ(X,U)))

local instance affineDifferentialBaseScalarTower (U : (X).Opens) :
    IsScalarTower k R ((P).obj (op U)) :=
  inferInstanceAs (IsScalarTower k R (KaehlerDifferential k Γ(X,U)))

/-- The canonical algebraic differential map into the actual principal
open's differential module. -/
def affineDifferentialToBasic (f : R) :
    ΩR→ₗ[R](P).obj (op (PrimeSpectrum.basicOpen f)) :=
  KaehlerDifferential.map k k R Γ(X,PrimeSpectrum.basicOpen f)

instance affineDifferentialToBasic_isLocalized (f : R) :
    IsLocalizedModule.Away f (affineDifferentialToBasic k R f) := by
  change IsLocalizedModule (.powers f)
    (KaehlerDifferential.map k k R Γ(X,PrimeSpectrum.basicOpen f))
  infer_instance

@[simp] theorem affineDifferentialToBasic_D (f r : R) :
    affineDifferentialToBasic k R f (KaehlerDifferential.D k R r)=
      CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) :=
  KaehlerDifferential.map_D k k R Γ(X,PrimeSpectrum.basicOpen f) r

/-- The actual principal-open Kähler/tilde comparison. It is linear
over Γ(D(f),O), not only over the original affine coordinate ring. -/
def affineDifferentialBasicEquiv (f : R) :
    (P).obj (op (PrimeSpectrum.basicOpen f))≃ₗ[Γ(X,PrimeSpectrum.basicOpen f)]
      Γ(Q,PrimeSpectrum.basicOpen f) :=
  (IsLocalizedModule.linearEquiv (.powers f)
    (affineDifferentialToBasic k R f)
    (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom)).extendScalarsOfIsLocalization
      (.powers f) Γ(X,PrimeSpectrum.basicOpen f)

@[simp] theorem affineDifferentialBasicEquiv_toOpen (f : R) (ω : ΩR) :
    affineDifferentialBasicEquiv k R f (affineDifferentialToBasic k R f ω)=
      tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f) ω :=
  IsLocalizedModule.linearEquiv_apply (.powers f)
    (affineDifferentialToBasic k R f)
    (show ΩR →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)).hom) ω

theorem affine_algebraMap_restrict {U V : (X).Opens} (h : V≤U) (r : R) :
    (X).presheaf.map (homOfLE h).op (algebraMap R Γ(X,U) r)=
      algebraMap R Γ(X,V) r := by
  change (X).presheaf.map (homOfLE h).op
      ((X).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    (X).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  exact congrArg (fun φ=>φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    ((X).presheaf.map_comp (homOfLE le_top).op (homOfLE h).op).symm

def affineDifferentialBasicRestriction (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) :
    (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      (P).obj (op (PrimeSpectrum.basicOpen g)) where
  toFun := (P).map (homOfLE h).op
  map_add' := map_add ((P).map (homOfLE h).op).hom
  map_smul' r ω := by
    let φ : (P).obj (op (PrimeSpectrum.basicOpen f)) →
        (P).obj (op (PrimeSpectrum.basicOpen g)) :=
      fun η => (P).map (homOfLE h).op η
    change φ (r • ω) = r • φ ω
    calc
      _ = φ (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r • ω) :=
        congrArg φ
          (IsScalarTower.algebraMap_smul Γ(X,PrimeSpectrum.basicOpen f) r ω).symm
      _ = (X).presheaf.map (homOfLE h).op
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) • φ ω :=
        (P).map_smul (homOfLE h).op (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r) ω
      _ = algebraMap R Γ(X,PrimeSpectrum.basicOpen g) r • φ ω :=
        congrArg (fun c : Γ(X,PrimeSpectrum.basicOpen g) => c • φ ω)
          (affine_algebraMap_restrict R h r)
      _ = r • φ ω :=
        IsScalarTower.algebraMap_smul Γ(X,PrimeSpectrum.basicOpen g) r (φ ω)

theorem affineDifferentialBasicRestriction_toBasic (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) :
    (affineDifferentialBasicRestriction k R f g h).comp
      (affineDifferentialToBasic k R f)=affineDifferentialToBasic k R g := by
  apply Derivation.liftKaehlerDifferential_unique
  ext r
  change (P).map (homOfLE h).op
    (affineDifferentialToBasic k R f (KaehlerDifferential.D k R r))=
      affineDifferentialToBasic k R g (KaehlerDifferential.D k R r)
  calc
    _ = (P).map (homOfLE h).op
        (CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)) :=
      congrArg ((P).map (homOfLE h).op) (affineDifferentialToBasic_D k R f r)
    _ = CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g)))
        ((X).presheaf.map (homOfLE h).op
          (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)) :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
        (scalarPresheafMap k X) (homOfLE h).op
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r)
    _ = CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen g) r) :=
      congrArg (CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen g))))
        (affine_algebraMap_restrict R h r)
    _ = _ := (affineDifferentialToBasic_D k R g r).symm

/-- The unique localization comparison commutes with all inclusions
between genuine principal opens. -/
theorem affineDifferentialBasicEquiv_natural (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    affineDifferentialBasicEquiv k R g ((P).map (homOfLE h).op ω)=
      (Q).presheaf.map (homOfLE h).op (affineDifferentialBasicEquiv k R f ω) := by
  let L : (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      Γ(Q,PrimeSpectrum.basicOpen g) :=
    (affineDifferentialBasicEquiv k R g).toLinearMap.restrictScalars R ∘ₗ
      affineDifferentialBasicRestriction k R f g h
  let H : (P).obj (op (PrimeSpectrum.basicOpen f))→ₗ[R]
      Γ(Q,PrimeSpectrum.basicOpen g) :=
    (((modulesSpecToSheaf (R := CommRingCat.of R)).obj Q).presheaf.map (homOfLE h).op).hom ∘ₗ
      (affineDifferentialBasicEquiv k R f).toLinearMap.restrictScalars R
  have hLH : L=H := by
    apply IsLocalizedModule.ext (.powers f) (affineDifferentialToBasic k R f)
    · intro z
      obtain ⟨m,hm⟩ := z.property
      change IsUnit (algebraMap R (Module.End R Γ(Q,PrimeSpectrum.basicOpen g)) z.val)
      rw [← hm,map_pow]
      exact ((Q).isUnit_algebraMap_end_of_le_basicOpen f h).pow m
    · ext η
      change affineDifferentialBasicEquiv k R g
        ((affineDifferentialBasicRestriction k R f g h)
          (affineDifferentialToBasic k R f η))=
        (Q).presheaf.map (homOfLE h).op
          (affineDifferentialBasicEquiv k R f (affineDifferentialToBasic k R f η))
      rw [show (affineDifferentialBasicRestriction k R f g h)
          (affineDifferentialToBasic k R f η)=affineDifferentialToBasic k R g η from
        congrArg (fun l=>l η) (affineDifferentialBasicRestriction_toBasic k R f g h),
        affineDifferentialBasicEquiv_toOpen,affineDifferentialBasicEquiv_toOpen]
      exact (congrArg (fun l=>l η)
        (tilde.toOpen_res (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f)
          (PrimeSpectrum.basicOpen g) (homOfLE h))).symm
  exact congrArg (fun l=>l ω) hLH

set_option maxHeartbeats 2000000 in
/-- The intrinsic sheafification of universal differentials is the
ordinary tilde sheaf of the ordinary algebraic Kähler module. -/
def affineDifferentialSheafIso : differentialSheaf k X≅tilde (R := CommRingCat.of R) M :=
  basisModuleSheafificationIso («X» := Spec (CommRingCat.of R))
    (fun f : R=>PrimeSpectrum.basicOpen f)
    PrimeSpectrum.isBasis_basic_opens P Q
    (fun f=>(affineDifferentialBasicEquiv k R f).toLinearMap)
    (affineDifferentialBasicEquiv_natural k R)
    (fun f=>(affineDifferentialBasicEquiv k R f).bijective)

set_option maxHeartbeats 2000000 in
theorem affineDifferentialSheafIso_basic (f : R)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
      ((differentialSheafUnit k X).app (op (PrimeSpectrum.basicOpen f)) ω)=
        affineDifferentialBasicEquiv k R f ω := by
  exact basisModuleSheafificationIso_app («X» := Spec (CommRingCat.of R))
    (fun f : R=>PrimeSpectrum.basicOpen f) PrimeSpectrum.isBasis_basic_opens P Q
    (fun f=>(affineDifferentialBasicEquiv k R f).toLinearMap)
    (affineDifferentialBasicEquiv_natural k R)
    (fun f=>(affineDifferentialBasicEquiv k R f).bijective) f ω

/-- The comparison sends the actual differential of the restriction of
r to the actual restriction of the algebraic differential d r. -/
theorem affineDifferentialSheafIso_D (f r : R) :
    (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
      ((differentialSheafDerivation k X).d
        («X» := op (PrimeSpectrum.basicOpen f))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r))=
      tilde.toOpen (R := CommRingCat.of R) M (PrimeSpectrum.basicOpen f) (KaehlerDifferential.D k R r) := by
  change (affineDifferentialSheafIso k R).hom.app (PrimeSpectrum.basicOpen f)
    ((differentialSheafUnit k X).app (op (PrimeSpectrum.basicOpen f))
      (CommRingCat.KaehlerDifferential.d
        (f := (scalarPresheafMap k X).app (op (PrimeSpectrum.basicOpen f)))
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f) r))) = _
  rw [← affineDifferentialToBasic_D k R f r,
    affineDifferentialSheafIso_basic,affineDifferentialBasicEquiv_toOpen]

end PaperVerification.ToricSchemes

end Source_ToricAffineDifferentialSheaf

section Source_ToricAffineExteriorSheaf

/-!
# Actual top exterior powers of free affine module sheaves

The comparison is proved for every finite free module of the stated
rank, including rank zero. The top exterior coefficient on each
principal open is computed in the genuinely localized basis. These
coefficients commute with actual restriction and therefore give the
ordinary tilde/exterior comparison after sheafification. In the toric
application the input basis is the already computed Kähler basis of a
genuine polynomial chart.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) {n : ℕ}
    (b : Module.Basis (Fin n) R M)

local notation "X" => Spec R
local notation "Q" => tilde M
local notation "W" => ModuleCat.of R (⋀[R]^n M)
local notation "P" => presheafExteriorPower
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace (Spec R)))))
  (SheafOfModules.val (tilde M)) n

local instance tildeToOpen_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) :=
  inferInstanceAs (IsLocalizedModule.Away f
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

def tildeLocalizedBasis (f : R) :
    Module.Basis (Fin n) Γ(X,PrimeSpectrum.basicOpen f) Γ(Q,PrimeSpectrum.basicOpen f) :=
  b.ofIsLocalizedModule Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
    (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

@[simp] theorem tildeLocalizedBasis_apply (f : R) (i : Fin n) :
    tildeLocalizedBasis R M b f i=tilde.toOpen M (PrimeSpectrum.basicOpen f) (b i) :=
  Module.Basis.ofIsLocalizedModule_apply _ _ _ _ _

theorem tildeLocalizedBasis_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) (i : Fin n) :
    (Q).presheaf.map (homOfLE h).op (tildeLocalizedBasis R M b f i)=
      tildeLocalizedBasis R M b g i := by
  rw [tildeLocalizedBasis_apply,tildeLocalizedBasis_apply]
  exact congrArg (fun φ=>φ (b i))
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h))

/-- The actual global frame of the tilde top module coming from the
ordinary determinant coefficient of the given basis. -/
def tildeTopBasisFrame : tilde W≅SheafOfModules.unit (X).ringCatSheaf :=
  (tilde.functor R).mapIso (basisTopExteriorEquiv b).toModuleIso ≪≫ tildeSelf

def tildeTopBasisCoordinates (U : (X).Opens) : Γ(tilde W,U)≃ₗ[Γ(X,U)] Γ(X,U) :=
  ((PresheafOfModules.evaluation (X).ringCatSheaf.obj (op U)).mapIso
    ((SheafOfModules.forget _).mapIso (tildeTopBasisFrame R M b))).toLinearEquiv

theorem tildeTopBasisCoordinates_restrict {U V : (X).Opens} (h : V≤U)
    (s : Γ(tilde W,U)) :
    tildeTopBasisCoordinates R M b V ((tilde W).presheaf.map (homOfLE h).op s)=
      (X).presheaf.map (homOfLE h).op (tildeTopBasisCoordinates R M b U s) :=
  PresheafOfModules.naturality_apply (tildeTopBasisFrame R M b).hom.val
    (homOfLE h).op s

theorem tildeTopBasisCoordinates_toOpen (U : (X).Opens) (ω : ⋀[R]^n M) :
    tildeTopBasisCoordinates R M b U (tilde.toOpen W U ω)=
      algebraMap R Γ(X,U) (basisTopExteriorEquiv b ω) := by
  calc
    _ = tilde.toOpen (ModuleCat.of R R) U (basisTopExteriorEquiv b ω) := by
      exact congrArg (fun φ=>φ ω)
        (tilde.toOpen_map_app (basisTopExteriorEquiv b).toModuleIso.hom U)
    _ = _ := rfl

/-- The coefficient comparison is an equivalence over the actual
principal-open structure ring. -/
def affineTopExteriorBasicEquiv (f : R) :
    (P).obj (op (PrimeSpectrum.basicOpen f))≃ₗ[Γ(X,PrimeSpectrum.basicOpen f)]
      Γ(tilde W,PrimeSpectrum.basicOpen f) :=
  (basisTopExteriorEquiv (tildeLocalizedBasis R M b f)).trans
    (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).symm

theorem localizedTopCoefficient_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
      (X).presheaf.map (homOfLE h).op
        (basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω) := by
  let c := basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω
  have hω : ω=c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
      (tildeLocalizedBasis R M b f) :=
    topExterior_eq_smul_basis (tildeLocalizedBasis R M b f) ω
  calc
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((P).map (homOfLE h).op
            (c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) := congrArg _ (congrArg _ hω)
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          (P).map (homOfLE h).op
            (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) :=
      congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g) z)
        ((P).map_smul (homOfLE h).op c
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)))
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) := by
      have hw : (P).map (homOfLE h).op
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)) =
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g) := by
        calc
          _ = exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
              (fun i : Fin n => (Q).val.map (homOfLE h).op
                (tildeLocalizedBasis R M b f i)) :=
            presheafExteriorPower_map_wedge (X).presheaf (Q).val n
              (homOfLE h).op (tildeLocalizedBasis R M b f)
          _ = _ := congrArg
            (fun v : Fin n → Γ(Q,PrimeSpectrum.basicOpen g) =>
              exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n v)
            (funext (fun i => tildeLocalizedBasis_restrict R M b f g h i))
      exact congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((X).presheaf.map (homOfLE h).op c • z)) hw
    _ = (X).presheaf.map (homOfLE h).op c *
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) :=
      (basisTopExteriorEquiv (tildeLocalizedBasis R M b g)).map_smul _ _
    _ = (X).presheaf.map (homOfLE h).op c * 1 :=
      congrArg (fun r : Γ(X,PrimeSpectrum.basicOpen g) =>
        (X).presheaf.map (homOfLE h).op c * r)
        (basisTopExteriorEquiv_basis (tildeLocalizedBasis R M b g))
    _ = (X).presheaf.map (homOfLE h).op c := mul_one _

theorem affineTopExteriorBasicEquiv_natural (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    affineTopExteriorBasicEquiv R M b g ((P).map (homOfLE h).op ω)=
      (tilde W).presheaf.map (homOfLE h).op (affineTopExteriorBasicEquiv R M b f ω) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen g)).injective
  rw [tildeTopBasisCoordinates_restrict]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact localizedTopCoefficient_restrict R M b f g h ω

theorem tildeLocalizedBasis_det (f : R) (v : Fin n→M) :
    (tildeLocalizedBasis R M b f).det
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
      algebraMap R Γ(X,PrimeSpectrum.basicOpen f) (b.det v) := by
  have hm : (tildeLocalizedBasis R M b f).toMatrix
      (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f)).mapMatrix (b.toMatrix v) := by
    funext i j
    exact b.ofIsLocalizedModule_repr_apply
      Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) (v j) i
  rw [Module.Basis.det_apply,hm,← RingHom.map_det,← Module.Basis.det_apply]

/-- The comparison is the ordinary wedge map on actual restricted
sections; the coefficient construction has not changed the exterior map. -/
theorem affineTopExteriorBasicEquiv_wedge (f : R) (v : Fin n→M) :
    affineTopExteriorBasicEquiv R M b f
      (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i)))=
      tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).injective
  rw [tildeTopBasisCoordinates_toOpen]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact (basisTopExteriorEquiv_wedge (tildeLocalizedBasis R M b f)
    (fun i => tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))).trans
      ((tildeLocalizedBasis_det R M b f v).trans
        (congrArg (algebraMap R Γ(X,PrimeSpectrum.basicOpen f))
          (basisTopExteriorEquiv_wedge b v)).symm)

/-- Actual top exterior power commutes with the actual affine tilde
construction. The source is the sheafification definition of the
ordinary exterior module of the actual section modules. -/
def affineTopExteriorSheafIso :
    sheafExteriorPower X (tilde M) n≅tilde W :=
  basisModuleSheafificationIso (fun f : R=>PrimeSpectrum.basicOpen f)
    PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)

theorem affineTopExteriorSheafIso_basic (f : R)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f)) ω)=
        affineTopExteriorBasicEquiv R M b f ω := by
  have h := basisModuleSheafificationIso_unit
    (fun f : R=>PrimeSpectrum.basicOpen f) PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)
  exact (congrArg (fun φ=>φ.app (op (PrimeSpectrum.basicOpen f)) ω) h).trans
    (basisModuleComparison_app _ _ _ _ _ _ f ω)

theorem affineTopExteriorSheafIso_wedge (f : R) (v : Fin n→M) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f))
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))))=
        tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  rw [affineTopExteriorSheafIso_basic,affineTopExteriorBasicEquiv_wedge]

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

/-- The ordinary intrinsic top differential sheaf on the affine chart
is the tilde of the ordinary top algebraic Kähler module. -/
def affineTopDifferentialSheafIso :
    topDifferentialSheaf k (Spec (CommRingCat.of R)) n≅
      tilde (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) :=
  sheafExteriorPowerIso (Spec (CommRingCat.of R))
    (affineDifferentialSheafIso k R) n ≪≫
      affineTopExteriorSheafIso (CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) b

end PaperVerification.ToricSchemes

end Source_ToricAffineExteriorSheaf

section Source_ToricGenericDifferentialSections

/-!
# Actual values of differential sections at the generic point

For any module over the actual function field, its tilde sheaf on the
generic-point scheme is pushed forward to the original integral scheme.
Its sections on every nonempty open are identified with the original
module. The universal differential of regular functions then gives an
actual morphism from the intrinsic Kähler sheaf into this generic module.
All restriction and scalar compatibilities are proved from actual sheaf
maps, and d(r) has value d(germ(r)).
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BaseSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (X : Scheme.{u}) [IsIntegral X]
    (N : ModuleCat.{u} X.functionField)

/-- A genuine module sheaf supported at the actual generic point. -/
def genericModule : X.Modules :=
  (Scheme.Modules.pushforward (genericPointMap X)).obj (tilde N)

def genericModuleValueAdd (U : X.Opens) [Nonempty U] :
    Γ(genericModule X N,U)≃+N :=
  ((tilde N).presheaf.mapIso
    (eqToIso (congrArg op (genericPointMap_preimage X U)))).addCommGroupIsoToAddEquiv.trans
      (tilde.isoTop N).toLinearEquiv.toAddEquiv.symm

theorem genericModuleValueAdd_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U) (s : Γ(genericModule X N,U)) :
    genericModuleValueAdd X N V ((genericModule X N).presheaf.map i.op s)=
      genericModuleValueAdd X N U s := by
  change (tilde.isoTop N).inv
      ((tilde N).presheaf.map
        (eqToHom (congrArg op (genericPointMap_preimage X V)))
          ((tilde N).presheaf.map
            ((Opens.map (genericPointMap X).base).map i).op s))=
    (tilde.isoTop N).inv
      ((tilde N).presheaf.map
        (eqToHom (congrArg op (genericPointMap_preimage X U))) s)
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
theorem genericModuleValueAdd_smul (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) (s : Γ(genericModule X N,U)) :
    genericModuleValueAdd X N U (a • s)=
      X.germToFunctionField U a • genericModuleValueAdd X N U s := by
  let φ := eqToHom (congrArg op (genericPointMap_preimage X U))
  let t := (tilde N).presheaf.map φ s
  have hscalar : (Spec X.functionField).presheaf.map φ ((genericPointMap X).app U a)=
      (Scheme.ΓSpecIso X.functionField).inv (X.germToFunctionField U a) := by
    have h := congrArg (fun f=>f a) (genericPointMap_app_value X U)
    change (Scheme.ΓSpecIso X.functionField).hom
      ((Spec X.functionField).presheaf.map φ ((genericPointMap X).app U a)) =
        X.germToFunctionField U a at h
    simpa only [Iso.hom_inv_id_apply] using
      congrArg (fun t => (Scheme.ΓSpecIso X.functionField).inv t) h
  change (tilde.isoTop N).inv
      ((tilde N).val.map φ ((genericPointMap X).app U a •
        (show Γ(tilde N,genericPointMap X ⁻¹ᵁ U) from s)))=
    X.germToFunctionField U a • (tilde.isoTop N).inv t
  rw [(tilde N).val.map_smul]
  erw [hscalar]
  change (tilde.isoTop N).inv ((X.germToFunctionField U a) • t)=_
  exact (tilde.isoTop N).inv.hom.map_smul _ _

/-- The scalar action on N is restriction through the actual germ map. -/
def genericModuleValue (U : X.Opens) [Nonempty U] :
    Γ(genericModule X N,U)≃ₗ[Γ(X,U)]
      (ModuleCat.restrictScalars (X.germToFunctionField U).hom).obj N where
  __ := genericModuleValueAdd X N U
  map_smul' a s := genericModuleValueAdd_smul X N U a s

@[simp] theorem genericModuleValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U) (s : Γ(genericModule X N,U)) :
    genericModuleValue X N V ((genericModule X N).presheaf.map i.op s)=
      genericModuleValue X N U s :=
  genericModuleValueAdd_restrict X N i s

section Differentials

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]

local notation "ΩK" => ModuleCat.of X.functionField (KaehlerDifferential k X.functionField)
local notation "GΩ" => genericModule X ΩK

def genericDifferentialDerivationValue (U : X.Opens) : Γ(X,U)→+Γ(GΩ,U) := by
  classical
  exact if hU : Nonempty U then
    (genericModuleValue X ΩK U).symm.toAddEquiv.toAddMonoidHom.comp
      ((KaehlerDifferential.D k X.functionField).toLinearMap.toAddMonoidHom.comp
        (X.germToFunctionField U).hom.toAddMonoidHom)
  else 0

theorem genericDifferentialDerivationValue_value (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) :
    genericModuleValue X ΩK U (genericDifferentialDerivationValue X k U a)=
      KaehlerDifferential.D k X.functionField (X.germToFunctionField U a) := by
  simp only [genericDifferentialDerivationValue,dif_pos (show Nonempty U from inferInstance),
    AddMonoidHom.comp_apply,LinearEquiv.apply_symm_apply]
  exact (genericModuleValue X ΩK U).apply_symm_apply _

theorem genericDifferentialDerivationValue_mul (U : X.Opens) (a b : Γ(X,U)) :
    genericDifferentialDerivationValue X k U (a*b)=
      a • genericDifferentialDerivationValue X k U b+
        b • genericDifferentialDerivationValue X k U a := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    apply (genericModuleValue X ΩK U).injective
    simp only [genericDifferentialDerivationValue_value,map_add,map_smul,map_mul]
    exact (KaehlerDifferential.D k X.functionField).leibniz
      (X.germToFunctionField U a) (X.germToFunctionField U b)
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty GΩ U hbot
    exact Subsingleton.elim _ _

theorem genericDifferentialDerivationValue_restrict {U V : X.Opens}
    (i : V⟶U) (a : Γ(X,U)) :
    genericDifferentialDerivationValue X k V (X.presheaf.map i.op a)=
      (GΩ).presheaf.map i.op (genericDifferentialDerivationValue X k U a) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply (genericModuleValue X ΩK V).injective
    rw [genericDifferentialDerivationValue_value,genericModuleValue_restrict,
      genericDifferentialDerivationValue_value,germToFunctionField_restrict]
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty GΩ V hbot
    exact Subsingleton.elim _ _

theorem genericDifferentialDerivationValue_scalar (U : X.Opens) (a : k) :
    genericDifferentialDerivationValue X k U (BaseSections.scalarMap k X U a)=0 := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    apply (genericModuleValue X ΩK U).injective
    rw [genericDifferentialDerivationValue_value,map_zero,BaseSections.germ_scalarMap]
    exact (KaehlerDifferential.D k X.functionField).map_algebraMap a
  · simp only [genericDifferentialDerivationValue,dif_neg hU,AddMonoidHom.zero_apply]

/-- The ordinary universal differential of actual regular functions,
with values in the genuine pushed-forward generic module. -/
def genericDifferentialDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf)
      (GΩ).val (scalarPresheafMap k X) where
  d {U} := genericDifferentialDerivationValue X k U.unop
  d_mul {U} := genericDifferentialDerivationValue_mul X k U.unop
  d_map {U V} f a := genericDifferentialDerivationValue_restrict X k f.unop a
  d_app {U} := genericDifferentialDerivationValue_scalar X k U.unop

/-- The genuine sheaf morphism supplied by the universal Kähler
derivation and the actual module-sheafification adjunction. -/
def differentialGenericMap : differentialSheaf k X⟶GΩ :=
  (differentialSheafHomEquiv k X GΩ).symm (genericDifferentialDerivation X k)

/-- Differential sections have actual generic values linear over the
regular-function ring through the actual germ map. -/
def differentialSectionValue (U : X.Opens) [Nonempty U] :
    Γ(differentialSheaf k X,U)→ₗ[Γ(X,U)]
      (ModuleCat.restrictScalars (X.germToFunctionField U).hom).obj ΩK :=
  (genericModuleValue X ΩK U).toLinearMap.comp
    ((differentialGenericMap X k).val.app (op U)).hom

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSectionValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U)
    (s : Γ(differentialSheaf k X,U)) :
    differentialSectionValue X k V ((differentialSheaf k X).presheaf.map i.op s)=
      differentialSectionValue X k U s := by
  change genericModuleValue X ΩK V
      ((differentialGenericMap X k).app V
        ((differentialSheaf k X).presheaf.map i.op s)) =
    genericModuleValue X ΩK U ((differentialGenericMap X k).app U s)
  have hn := congrArg (fun f => f s)
    ((Scheme.Modules.Hom.mapPresheaf (differentialGenericMap X k)).naturality i.op)
  exact (congrArg (genericModuleValue X ΩK V) hn).trans
    (genericModuleValue_restrict X ΩK i ((differentialGenericMap X k).app U s))

theorem differentialGenericMap_D (U : X.Opens) (a : Γ(X,U)) :
    (differentialGenericMap X k).app U
      ((differentialSheafDerivation k X).d (X:=op U) a)=
        genericDifferentialDerivationValue X k U a := by
  have h := (differentialSheafHomEquiv k X GΩ).apply_symm_apply
    (genericDifferentialDerivation X k)
  rw [differentialSheafHomEquiv_apply] at h
  exact PresheafOfModulesOfCommRing.Derivation.congr_d h a

set_option backward.isDefEq.respectTransparency.types false in
/-- The value of d(a) is precisely the ordinary algebraic differential
of the actual generic germ of a. -/
theorem differentialSectionValue_D (U : X.Opens) [Nonempty U] (a : Γ(X,U)) :
    differentialSectionValue X k U ((differentialSheafDerivation k X).d (X:=op U) a)=
      KaehlerDifferential.D k X.functionField (X.germToFunctionField U a) := by
  change genericModuleValue X ΩK U
    ((differentialGenericMap X k).app U
      ((differentialSheafDerivation k X).d (X:=op U) a)) = _
  exact (congrArg (genericModuleValue X ΩK U)
    (differentialGenericMap_D X k U a)).trans
      (genericDifferentialDerivationValue_value X k U a)

end Differentials

end PaperVerification.ToricSchemes

end Source_ToricGenericDifferentialSections

section Source_ToricModuleRestrictionSheafification

/-!
# Actual module sheafification on an open subscheme

Restriction to an open subscheme is the literal restriction on the open
image, with scalars transported by the structure-sheaf isomorphism. It
preserves local bijections because the open-image functor is
cocontinuous. Consequently it commutes with actual module
sheafification, including its universal map.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} (j : X⟶Y) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true in
def openPresheafRestrict :
    PresheafOfModulesOfCommRing.{u} Y.presheaf⥤
      PresheafOfModulesOfCommRing.{u} X.presheaf :=
  let α : X.presheaf⟶j.opensFunctor.op⋙Y.presheaf :=
    { app U := (j.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

@[simp] theorem openPresheafRestrict_sheaf_val (M : Y.Modules) :
    (openPresheafRestrict j).obj M.val=(M.restrict j).val := rfl

@[simp] theorem openPresheafRestrict_map_apply
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    (U : X.Opens) (s : P.obj (op (j ''ᵁ U))) :
    ((openPresheafRestrict j).map f).app (op U) s=f.app (op (j ''ᵁ U)) s := rfl

theorem openPresheafRestrict_locallyInjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

theorem openPresheafRestrict_locallySurjective
    {P Q : PresheafOfModulesOfCommRing.{u} Y.presheaf} (f : P⟶Q)
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)] :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((openPresheafRestrict j).map f)) := by
  change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (Functor.whiskerLeft j.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f))
  exact CategoryTheory.Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) j.opensFunctor
    ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map f)

variable (P : PresheafOfModulesOfCommRing.{u} Y.presheaf)

def openRestrictionSheafificationUnit : (openPresheafRestrict j).obj P⟶
    (Scheme.Modules.restrict
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j).val :=
  (openPresheafRestrict j).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallyInjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (openRestrictionSheafificationUnit j P)) := by
  letI : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) := by
    change CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf)
    infer_instance
  exact openPresheafRestrict_locallySurjective j
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P)

instance openRestrictionSheafificationUnit_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (openRestrictionSheafificationUnit j P)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (openRestrictionSheafificationUnit j P))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (openRestrictionSheafificationUnit j P) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The canonical comparison, derived from actual sheafification of a
locally bijective restriction map. -/
def openRestrictionSheafificationIso :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((openPresheafRestrict j).obj P) ≅
        Scheme.Modules.restrict
          ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j :=
  asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (openRestrictionSheafificationUnit j P)) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app
          (Scheme.Modules.restrict
            ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j)

set_option backward.isDefEq.respectTransparency.types false in
theorem openRestrictionSheafificationIso_unit :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app ((openPresheafRestrict j).obj P) ≫
      (openRestrictionSheafificationIso j P).hom.val=
        openRestrictionSheafificationUnit j P := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q : X.Modules := Scheme.Modules.restrict
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) j
  have h : (adj.homEquiv ((openPresheafRestrict j).obj P) Q).symm
      (openRestrictionSheafificationUnit j P) =
        (openRestrictionSheafificationIso j P).hom := rfl
  have he := congrArg (adj.homEquiv ((openPresheafRestrict j).obj P) Q) h.symm
  exact he.trans
    ((adj.homEquiv ((openPresheafRestrict j).obj P) Q).apply_symm_apply
      (openRestrictionSheafificationUnit j P))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openRestrictionSheafificationIso

end Source_ToricModuleRestrictionSheafification

section Source_ToricDifferentialRestriction

/-!
# Kähler differentials under an actual open immersion

The comparison is induced by the actual structure-ring maps. Its
compatibility with universal derivations is retained explicitly. No
affineness, smoothness, integrality, or fan presentation is needed.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BaseSections

section Rings

variable {A B C : CommRingCat.{u}} (f : A⟶B) (g : A⟶C)
    (e : B≅C) (he : f≫e.hom=g)

include he in
theorem differentialRingIso_forward_square : 𝟙 A≫g=f≫e.hom := by
  simpa using he.symm

include he in
theorem differentialRingIso_backward_square : 𝟙 A≫f=g≫e.inv := by
  rw [←he]
  simp

def differentialRingForward :
    CommRingCat.KaehlerDifferential f⟶
      (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential g) :=
  CommRingCat.KaehlerDifferential.map (differentialRingIso_forward_square f g e he)

def differentialRingBackward :
    CommRingCat.KaehlerDifferential g⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f) :=
  CommRingCat.KaehlerDifferential.map (differentialRingIso_backward_square f g e he)

private theorem differentialRingForward_d (b : B) :
    differentialRingForward f g e he (CommRingCat.KaehlerDifferential.d b)=
      CommRingCat.KaehlerDifferential.d (e.hom b) :=
  CommRingCat.KaehlerDifferential.map_d _ _

private theorem differentialRingBackward_d (c : C) :
    differentialRingBackward f g e he (CommRingCat.KaehlerDifferential.d c)=
      CommRingCat.KaehlerDifferential.d (e.inv c) :=
  CommRingCat.KaehlerDifferential.map_d _ _

set_option backward.isDefEq.respectTransparency false in
private theorem differentialRingBackward_forward
    (x : CommRingCat.KaehlerDifferential f) :
    differentialRingBackward f g e he (differentialRingForward f g e he x)=x := by
  letI := f.hom.toAlgebra
  have hx : x∈Submodule.span B (Set.range (CommRingCat.KaehlerDifferential.d (f:=f))) := by
    change x∈Submodule.span B (Set.range (_root_.KaehlerDifferential.D A B))
    rw [_root_.KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b,rfl⟩ := hx
      rw [differentialRingForward_d,differentialRingBackward_d]
      simp
  | zero => simp [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | smul a x hx ih =>
      rw [map_smul]
      change differentialRingBackward f g e he
        (e.hom a • differentialRingForward f g e he x)=a • x
      rw [map_smul]
      change e.inv (e.hom a) • differentialRingBackward f g e he
        (differentialRingForward f g e he x)=a • x
      simp only [Iso.hom_inv_id_apply,ih]

set_option backward.isDefEq.respectTransparency false in
/-- Kähler differentials transported through the actual isomorphism of
structure rings. The source has precisely the transported scalar action. -/
def differentialRingIso :
    (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f) ≅
      CommRingCat.KaehlerDifferential g where
  hom := ModuleCat.ofHom
    (R := C)
    (X := (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential f))
    (Y := CommRingCat.KaehlerDifferential g)
    { toFun := differentialRingForward f g e he
      map_add' := map_add _
      map_smul' c x := by
        change differentialRingForward f g e he (e.inv c • x)=
          c • differentialRingForward f g e he x
        rw [map_smul]
        change e.hom (e.inv c) • differentialRingForward f g e he x=_
        simp only [Iso.inv_hom_id_apply] }
  inv := differentialRingBackward f g e he
  hom_inv_id := by
    ext x
    exact differentialRingBackward_forward f g e he x
  inv_hom_id := by
    apply CommRingCat.KaehlerDifferential.ext
    intro c
    change differentialRingForward f g e he
      (differentialRingBackward f g e he (CommRingCat.KaehlerDifferential.d c)) =
        CommRingCat.KaehlerDifferential.d c
    rw [differentialRingBackward_d,differentialRingForward_d,Iso.inv_hom_id_apply]

@[simp] theorem differentialRingIso_hom_d (b : B) :
    (differentialRingIso f g e he).hom (CommRingCat.KaehlerDifferential.d b)=
      CommRingCat.KaehlerDifferential.d (e.hom b) :=
  differentialRingForward_d f g e he b

@[simp] theorem differentialRingIso_inv_d (c : C) :
    (differentialRingIso f g e he).inv (CommRingCat.KaehlerDifferential.d c)=
      CommRingCat.KaehlerDifferential.d (e.inv c) :=
  differentialRingBackward_d f g e he c

end Rings

section Schemes

variable (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (j : X⟶Y) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

set_option backward.isDefEq.respectTransparency.types false in
theorem BaseSections.scalarMap_appLE (V : Y.Opens) (U : X.Opens)
    (h : U≤j ⁻¹ᵁ V) (c : k) :
    j.appLE V U h (scalarMap k Y V c)=scalarMap k X U c := by
  have hm : Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫ j.appLE V U h =
      j.appLE ⊤ U (by simp) :=
    j.map_appLE h (homOfLE (show V ≤ ⊤ from le_top)).op
  calc
    j.appLE V U h (scalarMap k Y V c) =
        j.appLE V U h
          (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
            (scalarMap k Y ⊤ c)) :=
      congrArg (fun s : Γ(Y,V) => j.appLE V U h s)
        (scalarMap_restrict k (X := Y) (U := ⊤) (V := V) le_top c).symm
    _ = j.appLE ⊤ U (by simp) (scalarMap k Y ⊤ c) :=
      congrArg (fun q : Γ(Y,⊤) ⟶ Γ(X,U) => q.hom (scalarMap k Y ⊤ c)) hm
    _ = scalarMap k X U c := by
      change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (j.appTop (scalarMap k Y ⊤ c)) = _
      rw [scalarMap_top_natural]
      exact scalarMap_restrict k (X := X) (U := ⊤) (V := U) le_top c

theorem scalarPresheafMap_appIso (U : X.Opens) :
    (scalarPresheafMap k Y).app (op (j ''ᵁ U))≫(j.appIso U).hom=
      (scalarPresheafMap k X).app (op U) := by
  ext c
  rw [Scheme.Hom.appIso_hom']
  exact BaseSections.scalarMap_appLE k j (j ''ᵁ U) U (j.preimage_image_eq U).ge c

theorem differentialPresheaf_map_d {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    (r : X.presheaf.obj U) :
    (differentialPresheaf k X).map h
      (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r) =
        CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k X).app V) (X.presheaf.map h r) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
    (scalarPresheafMap k X) h r

set_option backward.isDefEq.respectTransparency.types false in
def differentialPresheafRestrictionComponent (U : X.Opensᵒᵖ) :
    (differentialPresheaf k X).obj U ≅
      ((openPresheafRestrict j).obj (differentialPresheaf k Y)).obj U :=
  (differentialRingIso
    ((scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
    ((scalarPresheafMap k X).app U) (j.appIso U.unop)
    (scalarPresheafMap_appIso k j U.unop)).symm

theorem differentialPresheafRestrictionComponent_d (U : X.Opensᵒᵖ)
    (r : X.presheaf.obj U) :
    (differentialPresheafRestrictionComponent k j U).hom
      (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r) =
        CommRingCat.KaehlerDifferential.d
          (f := (scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
          ((j.appIso U.unop).inv r) :=
  differentialRingIso_inv_d
    ((scalarPresheafMap k Y).app (op (j ''ᵁ U.unop)))
    ((scalarPresheafMap k X).app U) (j.appIso U.unop)
    (scalarPresheafMap_appIso k j U.unop) r

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialPresheafRestrictionComponent_naturality
    {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    (differentialPresheaf k X).map h ≫
        (ModuleCat.restrictScalars (X.presheaf.map h).hom).map
          (differentialPresheafRestrictionComponent k j V).hom =
      (differentialPresheafRestrictionComponent k j U).hom ≫
        ((openPresheafRestrict j).obj (differentialPresheaf k Y)).map h := by
  apply CommRingCat.KaehlerDifferential.ext (f := (scalarPresheafMap k X).app U)
  intro r
  change (differentialPresheafRestrictionComponent k j V).hom
      ((differentialPresheaf k X).map h
        (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r)) =
    (differentialPresheaf k Y).map (j.opensFunctor.op.map h)
      ((differentialPresheafRestrictionComponent k j U).hom
        (CommRingCat.KaehlerDifferential.d (f := (scalarPresheafMap k X).app U) r))
  exact
    (congrArg (differentialPresheafRestrictionComponent k j V).hom
      (differentialPresheaf_map_d k h r)).trans
    ((differentialPresheafRestrictionComponent_d k j V (X.presheaf.map h r)).trans
    ((congrArg (CommRingCat.KaehlerDifferential.d
      (f := (scalarPresheafMap k Y).app (op (j ''ᵁ V.unop))))
      (congrArg (fun q : Γ(X,U.unop) ⟶ Γ(Y,j ''ᵁ V.unop) => q.hom r)
        (j.appIso_inv_naturality h))).trans
    ((differentialPresheaf_map_d k (j.opensFunctor.op.map h)
      ((j.appIso U.unop).inv r)).symm.trans
    (congrArg ((differentialPresheaf k Y).map (j.opensFunctor.op.map h))
      (differentialPresheafRestrictionComponent_d k j U r).symm))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse comparison differentiates the inverse of the actual
structure-ring isomorphism, with its naturality proved separately. -/
def differentialPresheafRestrictionIso :
    differentialPresheaf k X≅
      (openPresheafRestrict j).obj (differentialPresheaf k Y) :=
  PresheafOfModulesOfCommRing.isoMk (R := X.presheaf)
    (M₁ := differentialPresheaf k X)
    (M₂ := (openPresheafRestrict j).obj (differentialPresheaf k Y))
    (differentialPresheafRestrictionComponent k j)
    (fun {_ _} h => differentialPresheafRestrictionComponent_naturality k j h)

@[simp] theorem differentialPresheafRestrictionIso_inv_d (U : X.Opens)
    (r : Γ(Y,j ''ᵁ U)) :
    (differentialPresheafRestrictionIso k j).inv.app (op U)
      ((differentialPresheafDerivation k Y).d r)=
        (differentialPresheafDerivation k X).d ((j.appIso U).hom r) :=
  differentialRingIso_hom_d _ _ _ _ r

/-- Intrinsic Kähler sheaves commute with restriction along every actual
open immersion over the base ring. -/
def differentialSheafRestrictIso :
    (differentialSheaf k Y).restrict j≅differentialSheaf k X :=
  (openRestrictionSheafificationIso j (differentialPresheaf k Y)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (differentialPresheafRestrictionIso k j).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSheafRestrictIso_unit :
    openRestrictionSheafificationUnit j (differentialPresheaf k Y) ≫
      (differentialSheafRestrictIso k j).hom.val =
        (differentialPresheafRestrictionIso k j).inv ≫ differentialSheafUnit k X := by
  let E := openRestrictionSheafificationIso j (differentialPresheaf k Y)
  let e := differentialPresheafRestrictionIso k j
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hE : E.hom.val ≫ E.inv.val = 𝟙 _ :=
    congrArg
      (fun f : F.obj ((openPresheafRestrict j).obj (differentialPresheaf k Y)) ⟶
        F.obj ((openPresheafRestrict j).obj (differentialPresheaf k Y)) => f.val)
      E.hom_inv_id
  change openRestrictionSheafificationUnit j (differentialPresheaf k Y) ≫
    (E.inv.val ≫ (F.map e.inv).val) = e.inv ≫ differentialSheafUnit k X
  rw [← openRestrictionSheafificationIso_unit]
  change (_ ≫ E.hom.val) ≫ (E.inv.val ≫ (F.map e.inv).val) = _
  rw [Category.assoc, ← Category.assoc E.hom.val E.inv.val, hE, Category.id_comp]
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality e.inv).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSheafRestrictIso_D (U : X.Opens) (r : Γ(Y,j ''ᵁ U)) :
    (differentialSheafRestrictIso k j).hom.app U
      (((differentialSheaf k Y).restrictAppIso j U).inv
        ((differentialSheafDerivation k Y).d (X:=op (j ''ᵁ U)) r)) =
      (differentialSheafDerivation k X).d (X:=op U) ((j.appIso U).hom r) := by
  have h := congrArg
    (fun f=>f.app (op U) ((differentialPresheafDerivation k Y).d r))
    (differentialSheafRestrictIso_unit k j)
  change (differentialSheafRestrictIso k j).hom.val.app (op U)
      ((openRestrictionSheafificationUnit j (differentialPresheaf k Y)).app (op U)
        ((differentialPresheafDerivation k Y).d r)) =
    (differentialSheafUnit k X).app (op U)
      ((differentialPresheafRestrictionIso k j).inv.app (op U)
        ((differentialPresheafDerivation k Y).d r)) at h
  rw [differentialPresheafRestrictionIso_inv_d] at h
  exact h

/-- The ordinary pullback comparison, obtained from the proved
restriction/pullback adjoint identification. -/
def differentialSheafPullbackIso :
    (Scheme.Modules.pullback j).obj (differentialSheaf k Y)≅differentialSheaf k X :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app (differentialSheaf k Y)).symm ≪≫
    differentialSheafRestrictIso k j

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.differentialSheafRestrictIso
#print axioms PaperVerification.ToricSchemes.differentialSheafPullbackIso

end Source_ToricDifferentialRestriction

section Source_ToricExteriorRestriction

/-!
# Ordinary exterior sheaves under open restriction

The exterior comparison is induced by the universal alternating map,
including degree zero. Together with actual module sheafification it
gives restriction and pullback compatibility for intrinsic top
differential sheaves.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite

section Rings

variable {R S : CommRingCat.{u}} (e : R≅S) (M : ModuleCat.{u} R) (n : ℕ)

abbrev ringExteriorRestrictedModule := (ModuleCat.restrictScalars e.inv.hom).obj M

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPullAlternating :
    ringExteriorRestrictedModule e M [⋀^Fin n]→ₗ[S]
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) where
  toFun x := exteriorPower.ιMulti R n (M := M) x
  map_update_add' x i a b := (exteriorPower.ιMulti R n (M := M)).map_update_add x i a b
  map_update_smul' x i c a := (exteriorPower.ιMulti R n (M := M)).map_update_smul x i (e.inv c) a
  map_eq_zero_of_eq' x i j h hij :=
    (exteriorPower.ιMulti R n (M := M)).map_eq_zero_of_eq x h hij

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPushAlternating :
    M [⋀^Fin n]→ₗ[R]
      (ModuleCat.restrictScalars e.hom.hom).obj
        ((ringExteriorRestrictedModule e M).exteriorPower n) where
  toFun x := exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x
  map_update_add' x i a b := (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_update_add x i a b
  map_update_smul' x i r a := by
    have h := (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_update_smul x i (e.hom r) a
    change exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) (Function.update x i (e.inv (e.hom r) • a))=
      e.hom r • exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) (Function.update x i a) at h
    change exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)
      (Function.update x i (r • a)) =
        e.hom r • exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)
          (Function.update x i a)
    simpa only [Iso.hom_inv_id_apply] using h
  map_eq_zero_of_eq' x i j h hij :=
    (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M)).map_eq_zero_of_eq x h hij

def ringExteriorPull :
    (ringExteriorRestrictedModule e M).exteriorPower n⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc (ringExteriorPullAlternating e M n)

def ringExteriorPushRaw : M.exteriorPower n⟶
    (ModuleCat.restrictScalars e.hom.hom).obj
      ((ringExteriorRestrictedModule e M).exteriorPower n) :=
  ModuleCat.exteriorPower.desc (ringExteriorPushAlternating e M n)

@[simp] private theorem ringExteriorPull_wedge
    (x : Fin n → ringExteriorRestrictedModule e M) :
    ringExteriorPull e M n (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)=
      exteriorPower.ιMulti R n (M := M) x :=
  ModuleCat.exteriorPower.desc_mk _ _

@[simp] private theorem ringExteriorPushRaw_wedge (x : Fin n→M) :
    ringExteriorPushRaw e M n (exteriorPower.ιMulti R n (M := M) x)=
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x :=
  ModuleCat.exteriorPower.desc_mk _ _

set_option backward.isDefEq.respectTransparency false in
def ringExteriorPush :
    (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n)⟶
      (ringExteriorRestrictedModule e M).exteriorPower n :=
  ModuleCat.ofHom
    (R := S)
    (X := (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n))
    (Y := (ringExteriorRestrictedModule e M).exteriorPower n)
    { toFun := ringExteriorPushRaw e M n
      map_add' := map_add _
      map_smul' c x := by
        change ringExteriorPushRaw e M n (e.inv c • x)=
          c • ringExteriorPushRaw e M n x
        rw [map_smul]
        change e.hom (e.inv c) • ringExteriorPushRaw e M n x=_
        simp }

set_option backward.isDefEq.respectTransparency false in
private theorem ringExteriorPull_push (x : M.exteriorPower n) :
    ringExteriorPull e M n (ringExteriorPushRaw e M n x)=x := by
  have hx : x∈Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v,rfl⟩ := hx
      exact (congrArg (ringExteriorPull e M n)
        (ringExteriorPushRaw_wedge e M n v)).trans (ringExteriorPull_wedge e M n v)
  | zero => simp only [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add,ihx,ihy]
  | smul a x hx ih =>
      rw [map_smul]
      change ringExteriorPull e M n (e.hom a • ringExteriorPushRaw e M n x)=a • x
      rw [map_smul]
      change e.inv (e.hom a) • ringExteriorPull e M n
        (ringExteriorPushRaw e M n x)=a • x
      simp only [Iso.hom_inv_id_apply,ih]

/-- Exterior powers commute with an actual change of scalars through a
ring isomorphism, by their ordinary alternating universal property. -/
def ringExteriorIso :
    ((ModuleCat.restrictScalars e.inv.hom).obj M).exteriorPower n≅
      (ModuleCat.restrictScalars e.inv.hom).obj (M.exteriorPower n) where
  hom := ringExteriorPull e M n
  inv := ringExteriorPush e M n
  hom_inv_id := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    change ringExteriorPushRaw e M n
      (ringExteriorPull e M n
        (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)) =
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x
    exact (congrArg (ringExteriorPushRaw e M n)
      (ringExteriorPull_wedge e M n x)).trans (ringExteriorPushRaw_wedge e M n x)
  inv_hom_id := by
    ext x
    change ringExteriorPull e M n (ringExteriorPushRaw e M n x) = x
    exact ringExteriorPull_push e M n x

@[simp] theorem ringExteriorIso_hom_wedge
    (x : Fin n→(ModuleCat.restrictScalars e.inv.hom).obj M) :
    (ringExteriorIso e M n).hom (exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x)=
      exteriorPower.ιMulti R n (M := M) x := ringExteriorPull_wedge e M n x

@[simp] theorem ringExteriorIso_inv_wedge (x : Fin n→M) :
    (ringExteriorIso e M n).inv (exteriorPower.ιMulti R n (M := M) x)=
      exteriorPower.ιMulti S n (M := ringExteriorRestrictedModule e M) x := ringExteriorPushRaw_wedge e M n x

end Rings

section Schemes

variable {X Y : Scheme.{u}} (j : X⟶Y) [IsOpenImmersion j]
    (P : PresheafOfModulesOfCommRing.{u} Y.presheaf) (n : ℕ)

def openPresheafExteriorComponent (U : X.Opensᵒᵖ) :
    ((ModuleCat.restrictScalars (j.appIso U.unop).inv.hom).obj
      (P.obj (op (j ''ᵁ U.unop)))).exteriorPower n ≅
    (ModuleCat.restrictScalars (j.appIso U.unop).inv.hom).obj
      ((P.obj (op (j ''ᵁ U.unop))).exteriorPower n) :=
  ringExteriorIso (R := Y.presheaf.obj (op (j ''ᵁ U.unop)))
    (S := X.presheaf.obj U) (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n

set_option maxHeartbeats 2000000 in
theorem openPresheafExteriorComponent_naturality
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n).map f ≫
        (ModuleCat.restrictScalars (X.presheaf.map f).hom).map
          (openPresheafExteriorComponent j P n V).hom =
      (openPresheafExteriorComponent j P n U).hom ≫
        ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n)).map f := by
  apply ModuleCat.exteriorPower.hom_ext (R := X.presheaf.obj U)
    (M := ((openPresheafRestrict j).obj P).obj U)
    (N := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
      (((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n)).obj V))
  apply ModuleCat.AlternatingMap.ext
  intro x
  change (ringExteriorIso (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n).hom
      ((presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n).map f
        (exteriorPower.ιMulti (X.presheaf.obj U) n x)) =
    (presheafExteriorPower Y.presheaf P n).map (j.opensFunctor.op.map f)
      ((ringExteriorIso (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n).hom
        (exteriorPower.ιMulti (X.presheaf.obj U) n x))
  exact
    (congrArg (ringExteriorIso (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n).hom
      (presheafExteriorPower_map_wedge X.presheaf ((openPresheafRestrict j).obj P) n f x)).trans
    ((ringExteriorIso_hom_wedge (j.appIso V.unop) (P.obj (op (j ''ᵁ V.unop))) n
      (fun i => ((openPresheafRestrict j).obj P).map f (x i))).trans
    ((presheafExteriorPower_map_wedge Y.presheaf P n (j.opensFunctor.op.map f) x).symm.trans
    (congrArg ((presheafExteriorPower Y.presheaf P n).map (j.opensFunctor.op.map f))
      (ringExteriorIso_hom_wedge (j.appIso U.unop) (P.obj (op (j ''ᵁ U.unop))) n x).symm)))

set_option maxHeartbeats 2000000 in
def openPresheafExteriorIso :
    presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n≅
      (openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n) :=
  PresheafOfModulesOfCommRing.isoMk (R := X.presheaf)
    (M₁ := presheafExteriorPower X.presheaf ((openPresheafRestrict j).obj P) n)
    (M₂ := (openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf P n))
    (fun U => openPresheafExteriorComponent j P n U)
    (fun {_ _} f => openPresheafExteriorComponent_naturality j P n f)


variable (M : Y.Modules)

def sheafExteriorRestrictIso :
    (sheafExteriorPower Y M n).restrict j≅sheafExteriorPower X (M.restrict j) n :=
  (openRestrictionSheafificationIso j (presheafExteriorPower Y.presheaf M.val n)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (openPresheafExteriorIso j M.val n).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem sheafExteriorRestrictIso_unit :
    openRestrictionSheafificationUnit j (presheafExteriorPower Y.presheaf M.val n) ≫
      (sheafExteriorRestrictIso j n M).hom.val=
        (openPresheafExteriorIso j M.val n).inv ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (presheafExteriorPower X.presheaf (M.restrict j).val n) := by
  let E := openRestrictionSheafificationIso j (presheafExteriorPower Y.presheaf M.val n)
  let e := openPresheafExteriorIso j M.val n
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have hE : E.hom.val ≫ E.inv.val = 𝟙 _ :=
    congrArg
      (fun f : F.obj ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf M.val n)) ⟶
        F.obj ((openPresheafRestrict j).obj (presheafExteriorPower Y.presheaf M.val n)) => f.val)
      E.hom_inv_id
  change openRestrictionSheafificationUnit j (presheafExteriorPower Y.presheaf M.val n) ≫
    (E.inv.val ≫ (F.map e.inv).val) = e.inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf (M.restrict j).val n)
  rw [← openRestrictionSheafificationIso_unit]
  change (_ ≫ E.hom.val) ≫ (E.inv.val ≫ (F.map e.inv).val) = _
  rw [Category.assoc, ← Category.assoc E.hom.val E.inv.val, hE, Category.id_comp]
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality e.inv).symm

variable (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [j.IsOver (Spec (CommRingCat.of k))]

/-- Actual restriction of the ordinary top exterior power of the
intrinsic cotangent sheaf. -/
def topDifferentialSheafRestrictIso :
    (topDifferentialSheaf k Y n).restrict j≅topDifferentialSheaf k X n :=
  sheafExteriorRestrictIso j n (differentialSheaf k Y) ≪≫
    sheafExteriorPowerIso X (differentialSheafRestrictIso k j) n

/-- In particular this is the canonical transport of top differential
sheaves through every scheme isomorphism over the base. -/
def topDifferentialSheafPullbackIso :
    (Scheme.Modules.pullback j).obj (topDifferentialSheaf k Y n)≅
      topDifferentialSheaf k X n :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).app
    (topDifferentialSheaf k Y n)).symm ≪≫ topDifferentialSheafRestrictIso j n k

end Schemes
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.topDifferentialSheafPullbackIso

end Source_ToricExteriorRestriction

section Source_ToricGenericTopDifferentials

/-!
# Generic coefficients of the intrinsic top differential sheaf

The map is induced from the actual universal derivation of regular
functions and the ordinary exterior universal property. A chosen basis
of generic differentials only chooses a nonzero rational volume; it
does not prescribe the regular image or its divisor.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped BaseSections Classical

variable (X : Scheme.{u}) [IsIntegral X] (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] {n : ℕ}
    (b : Module.Basis (Fin n) X.functionField (KaehlerDifferential k X.functionField))

local notation "ΩX" => differentialSheaf k X
local notation "P" => presheafExteriorPower X.presheaf (SheafOfModules.val (differentialSheaf k X)) n
local notation "K" => X.functionField

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
def genericTopCoefficientValue (U : X.Opens) [Nonempty U] :
    (P).obj (op U)→ₗ[Γ(X,U)]K := by
  letI : Algebra Γ(X,U) K := (X.germToFunctionField U).hom.toAlgebra
  letI : Module Γ(X,U) (KaehlerDifferential k K) :=
    Module.compHom (KaehlerDifferential k K) (X.germToFunctionField U).hom
  letI : IsScalarTower Γ(X,U) K (KaehlerDifferential k K) :=
    IsScalarTower.of_compHom _ _ _
  exact ((basisTopExteriorEquiv b).toLinearMap.restrictScalars Γ(X,U)).comp
    (exteriorScalarExtensionMap (R := Γ(X,U)) (S := K)
      (M := Γ(differentialSheaf k X,U)) (N := KaehlerDifferential k K) (n := n)
      (differentialSectionValue X k U))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
@[simp] theorem genericTopCoefficientValue_wedge (U : X.Opens) [Nonempty U]
    (ω : Fin n→Γ(ΩX,U)) :
    genericTopCoefficientValue X k b U (exteriorPower.ιMulti Γ(X,U) n ω)=
      basisTopExteriorEquiv b (exteriorPower.ιMulti K n
        (fun i=>differentialSectionValue X k U (ω i))) := by
  letI : Algebra Γ(X,U) K := (X.germToFunctionField U).hom.toAlgebra
  letI : Module Γ(X,U) (KaehlerDifferential k K) :=
    Module.compHom (KaehlerDifferential k K) (X.germToFunctionField U).hom
  letI : IsScalarTower Γ(X,U) K (KaehlerDifferential k K) :=
    IsScalarTower.of_compHom _ _ _
  exact congrArg (basisTopExteriorEquiv b)
    (exteriorScalarExtensionMap_wedge (R := Γ(X,U)) (S := K)
      (M := Γ(differentialSheaf k X,U)) (N := KaehlerDifferential k K) (n := n)
      (differentialSectionValue X k U) ω)

def genericTopCoefficientSection (U : X.Opens) :
    (P).obj (op U)→ₗ[Γ(X,U)]Γ(rationalFunctions X,U) :=
  if hU : Nonempty U then
    (rationalValueLinearEquiv X U).symm.toLinearMap.comp
      (genericTopCoefficientValue X k b U)
  else 0

@[simp] theorem genericTopCoefficientSection_value (U : X.Opens) [Nonempty U]
    (ω : (P).obj (op U)) :
    rationalValue X U (genericTopCoefficientSection X k b U ω)=
      genericTopCoefficientValue X k b U ω := by
  simp only [genericTopCoefficientSection,dif_pos (show Nonempty U from inferInstance),
    LinearMap.comp_apply]
  exact (rationalValueLinearEquiv X U).apply_symm_apply _

theorem genericTopCoefficientSection_natural {U V : X.Opens} (i : V⟶U) :
    (P).map i.op ≫ (ModuleCat.restrictScalars (X.presheaf.map i.op).hom).map
        (ModuleCat.ofHom (genericTopCoefficientSection X k b V)) =
      ModuleCat.ofHom (genericTopCoefficientSection X k b U) ≫
        (rationalFunctions X).val.map i.op := by
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply ModuleCat.exteriorPower.hom_ext (R := Γ(X,U)) (n := n)
      (M := PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (SheafOfModules.val (differentialSheaf k X)) (op U))
      (N := (ModuleCat.restrictScalars (X.presheaf.map i.op).hom).obj
        ((rationalFunctions X).val.obj (op V)))
    apply ModuleCat.AlternatingMap.ext
    intro ω
    change genericTopCoefficientSection X k b V
        ((P).map i.op (exteriorPower.ιMulti Γ(X,U) n ω)) =
      (rationalFunctions X).presheaf.map i.op
        (genericTopCoefficientSection X k b U (exteriorPower.ιMulti Γ(X,U) n ω))
    apply (rationalValue X V).injective
    let ω' : Fin n→Γ(differentialSheaf k X,V) :=
      fun a => (differentialSheaf k X).presheaf.map i.op (ω a)
    calc
      _ = genericTopCoefficientValue X k b V
          ((P).map i.op (exteriorPower.ιMulti Γ(X,U) n ω)) :=
        genericTopCoefficientSection_value X k b V _
      _ = genericTopCoefficientValue X k b V (exteriorPower.ιMulti Γ(X,V) n ω') :=
        congrArg (genericTopCoefficientValue X k b V)
          (presheafExteriorPower_map_wedge X.presheaf
            (SheafOfModules.val (differentialSheaf k X)) n i.op ω)
      _ = basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun a => differentialSectionValue X k V (ω' a))) :=
        genericTopCoefficientValue_wedge X k b V ω'
      _ = basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun a => differentialSectionValue X k U (ω a))) :=
        congrArg (fun v => basisTopExteriorEquiv b (exteriorPower.ιMulti K n v))
          (funext (fun a => differentialSectionValue_restrict X k i (ω a)))
      _ = _ := ((rationalValue_restrict X i _).trans
        ((genericTopCoefficientSection_value X k b U _).trans
          (genericTopCoefficientValue_wedge X k b U ω))).symm
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    ext ω
    exact @Subsingleton.elim Γ(rationalFunctions X,V)
      (moduleSections_subsingleton_of_empty (rationalFunctions X) V hbot) _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf map uses ordinary generic differential coefficients on
every nonempty open and the unique zero section on the empty open. -/
def genericTopCoefficientPresheaf : P⟶(rationalFunctions X).val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (M₁ := P) (M₂ := (rationalFunctions X).val)
    (fun U=>ModuleCat.ofHom (R := Γ(X,U.unop))
      (X := (P).obj U) (Y := Γ(rationalFunctions X,U.unop))
      (genericTopCoefficientSection X k b U.unop))
    (fun f=>genericTopCoefficientSection_natural X k b f.unop)

/-- The actual generic-coefficient morphism from the ordinary top
exterior sheaf of the intrinsic Kähler sheaf. -/
def topDifferentialRationalMap : topDifferentialSheaf k X n⟶rationalFunctions X :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    P (rationalFunctions X)).symm (genericTopCoefficientPresheaf X k b)

theorem topDifferentialRationalMap_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (topDifferentialRationalMap X k b).val=genericTopCoefficientPresheaf X k b := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv P (rationalFunctions X)).apply_symm_apply _

def differentialWedgeSection (U : X.Opens) (a : Fin n→Γ(X,U)) :
    Γ(topDifferentialSheaf k X n,U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
    (op U) (exteriorPower.ιMulti Γ(X,U) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i)))

theorem differentialWedgeSection_restrict {U V : X.Opens} (h : V≤U)
    (a : Fin n→Γ(X,U)) :
    moduleRes (topDifferentialSheaf k X n) h (differentialWedgeSection X k U a)=
      differentialWedgeSection X k V (fun i=>regularRes h (a i)) := by
  let η : P⟶(topDifferentialSheaf k X n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  let v := exteriorPower.ιMulti Γ(X,U) n
    (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))
  have hv : (P).map (homOfLE h).op v = exteriorPower.ιMulti Γ(X,V) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op V) (regularRes h (a i))) := by
    calc
      _ = exteriorPower.ιMulti Γ(X,V) n (M := Γ(differentialSheaf k X,V))
          (fun i=>(differentialSheaf k X).presheaf.map (homOfLE h).op
            ((differentialSheafDerivation k X).d (X:=op U) (a i))) :=
        presheafExteriorPower_map_wedge X.presheaf
          (SheafOfModules.val (differentialSheaf k X)) n (homOfLE h).op _
      _ = _ := congrArg (fun v : Fin n→Γ(differentialSheaf k X,V) =>
          exteriorPower.ιMulti Γ(X,V) n v)
        (funext (fun i =>
          ((differentialSheafDerivation k X).d_map (homOfLE h).op (a i)).symm))
  exact (PresheafOfModules.naturality_apply η (homOfLE h).op v).symm.trans
    (congrArg (η.app (op V)) hv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem differentialWedgeSection_openRestriction
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (j : Y⟶X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]
    (U : Y.Opens) (a : Fin n→Γ(X,j ''ᵁ U)) :
    (topDifferentialSheafRestrictIso j n k).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)) =
      differentialWedgeSection Y k U (fun i=>(j.appIso U).hom (a i)) := by
  let P₀ := presheafExteriorPower X.presheaf (differentialSheaf k X).val n
  let P₁ := presheafExteriorPower Y.presheaf ((differentialSheaf k X).restrict j).val n
  let P₂ := presheafExteriorPower Y.presheaf (differentialSheaf k Y).val n
  let η₁ : P₁⟶(sheafExteriorPower Y ((differentialSheaf k X).restrict j) n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P₁
  let η₂ : P₂⟶(topDifferentialSheaf k Y n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P₂
  let ωX : Fin n→Γ(differentialSheaf k X,j ''ᵁ U) :=
    fun i=>(differentialSheafDerivation k X).d (X:=op (j ''ᵁ U)) (a i)
  let ωY : Fin n→Γ((differentialSheaf k X).restrict j,U) :=
    fun i=>((differentialSheaf k X).restrictAppIso j U).inv (ωX i)
  let wX := exteriorPower.ιMulti Γ(X,j ''ᵁ U) n ωX
  let wY := exteriorPower.ιMulti Γ(Y,U) n ωY
  have hW : (openPresheafExteriorIso j (differentialSheaf k X).val n).inv.app (op U) wX = wY := by
    change (ringExteriorIso (R := X.presheaf.obj (op (j ''ᵁ U)))
      (S := Y.presheaf.obj (op U)) (j.appIso U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (differentialSheaf k X).val (op (j ''ᵁ U))) n).inv wX = wY
    exact ringExteriorIso_inv_wedge (j.appIso U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (differentialSheaf k X).val (op (j ''ᵁ U))) n ωX
  have hu := congrArg
    (fun f : (openPresheafRestrict j).obj P₀⟶
        (sheafExteriorPower Y ((differentialSheaf k X).restrict j) n).val =>
      f.app (op U) wX)
    (sheafExteriorRestrictIso_unit j n (differentialSheaf k X))
  change (sheafExteriorRestrictIso j n (differentialSheaf k X)).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)) =
    η₁.app (op U) ((openPresheafExteriorIso j (differentialSheaf k X).val n).inv.app (op U) wX) at hu
  have hu' := hu.trans (congrArg (η₁.app (op U)) hW)
  let m : P₁⟶P₂ :=
    presheafExteriorPowerHom Y.presheaf n (differentialSheafRestrictIso k j).hom.val
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).unit.naturality m
  have hn' : η₂.app (op U) (m.app (op U) wY) =
      (sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U
        (η₁.app (op U) wY) :=
    congrArg (fun f : P₁⟶(topDifferentialSheaf k Y n).val => f.app (op U) wY) hn
  have hMap : m.app (op U) wY = exteriorPower.ιMulti Γ(Y,U) n
      (fun i=>(differentialSheafDerivation k Y).d (X:=op U) ((j.appIso U).hom (a i))) := by
    change ModuleCat.exteriorPower.map (R := Γ(Y,U))
      ((differentialSheafRestrictIso k j).hom.val.app (op U)) n wY = _
    exact (ModuleCat.exteriorPower.map_mk (R := Γ(Y,U))
      ((differentialSheafRestrictIso k j).hom.val.app (op U)) ωY).trans
        (congrArg (fun v : Fin n→Γ(differentialSheaf k Y,U) =>
          exteriorPower.ιMulti Γ(Y,U) n v)
          (funext (fun i=>differentialSheafRestrictIso_D k j U (a i))))
  change (sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U
    ((sheafExteriorRestrictIso j n (differentialSheaf k X)).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)))=_
  exact (congrArg ((sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U)
    hu').trans (hn'.symm.trans (congrArg (η₂.app (op U)) hMap))

/-- On a wedge of genuine differentials of regular functions the map
is exactly the wedge of their generic differentials. -/
theorem topDifferentialRationalMap_differentialWedge
    (U : X.Opens) [Nonempty U] (a : Fin n→Γ(X,U)) :
    rationalValue X U ((topDifferentialRationalMap X k b).app U
      (differentialWedgeSection X k U a))=
        basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun i=>KaehlerDifferential.D k K (X.germToFunctionField U (a i)))) := by
  have h := congrArg
    (fun f=>f.app (op U) (exteriorPower.ιMulti Γ(X,U) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))))
    (topDifferentialRationalMap_unit X k b)
  change (topDifferentialRationalMap X k b).app U
    (differentialWedgeSection X k U a)=
      genericTopCoefficientSection X k b U
        (exteriorPower.ιMulti Γ(X,U) n
          (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))) at h
  exact (congrArg (rationalValue X U) h).trans
    ((genericTopCoefficientSection_value X k b U _).trans
      ((genericTopCoefficientValue_wedge X k b U _).trans
        (congrArg (fun v : Fin n → KaehlerDifferential k K =>
          basisTopExteriorEquiv b (exteriorPower.ιMulti K n v))
            (funext (fun i => differentialSectionValue_D X k U (a i))))))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.topDifferentialRationalMap_differentialWedge

end Source_ToricGenericTopDifferentials

section Source_ToricAffineDifferentialWedges

/-! # The affine comparison preserves actual wedges of differentials -/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped BaseSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} {M N : X.Modules} (e : M≅N) (n : ℕ)

theorem sheafExteriorPowerIso_wedge (U : X.Opens) (ω : Fin n→Γ(M,U)) :
    (sheafExteriorPowerIso X e n).hom.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf M.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf N.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i))) := by
  have h := congrArg
    (fun f=>f.app (op U) (exteriorPower.ιMulti Γ(X,U) n ω))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (presheafExteriorPowerHom X.presheaf n e.hom.val))
  change
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U)
        (ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      (sheafExteriorPowerIso X e n).hom.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (presheafExteriorPower X.presheaf M.val n)).app (op U)
            (exteriorPower.ιMulti Γ(X,U) n ω)) at h
  have hmap :
      ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
        (exteriorPower.ιMulti Γ(X,U) n ω) =
      exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i)) :=
    ModuleCat.exteriorPower.map_mk (R := Γ(X,U)) (e.hom.val.app (op U)) ω
  exact h.symm.trans (congrArg
    (fun x=>((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U) x) hmap)

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

local instance affineWedgeCoordinateAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of R),U) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf (CommRingCat.of R)).presheaf.obj (op U)))

theorem affineTopDifferentialSheafIso_differentialWedge (f : R) (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app (PrimeSpectrum.basicOpen f)
      (differentialWedgeSection (Spec (CommRingCat.of R)) k
        (PrimeSpectrum.basicOpen f)
        (fun i=>algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen f) (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R)))
        (PrimeSpectrum.basicOpen f)
          (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen f
  let ω : Fin n→Γ(differentialSheaf k (Spec (CommRingCat.of R)),U) :=
    fun i=>(differentialSheafDerivation k (Spec (CommRingCat.of R))).d
      («X» := op U) (algebraMap R Γ(Spec (CommRingCat.of R),U) (a i))
  have hw := sheafExteriorPowerIso_wedge (affineDifferentialSheafIso k R) n U ω
  have hv : (fun i=>(affineDifferentialSheafIso k R).hom.app U (ω i)) =
      (fun i=>tilde.toOpen (R := CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) U
          (KaehlerDifferential.D k R (a i))) := by
    funext i
    exact affineDifferentialSheafIso_D k R f (a i)
  have hη := congrArg
    (fun v=>((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
        (presheafExteriorPower (Spec (CommRingCat.of R)).presheaf
          (tilde (R := CommRingCat.of R) (ModuleCat.of R (KaehlerDifferential k R))).val n)).app
            (op U) (exteriorPower.ιMulti Γ(Spec (CommRingCat.of R),U) n v)) hv
  exact (congrArg
    (fun z=>(affineTopExteriorSheafIso (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b).hom.app U z)
      (hw.trans hη)).trans
    (affineTopExteriorSheafIso_wedge (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b f
        (fun i=>KaehlerDifferential.D k R (a i)))

theorem affineTopDifferentialSheafIso_differentialWedge_top (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app ⊤
      (differentialWedgeSection (Spec (CommRingCat.of R)) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  have h := affineTopDifferentialSheafIso_differentialWedge k R b 1 a
  have hU : (PrimeSpectrum.basicOpen (1 : R) : (Spec (CommRingCat.of R)).Opens)=⊤ :=
    PrimeSpectrum.basicOpen_one
  erw [hU] at h
  have htop (r : R) : algebraMap R Γ(Spec (CommRingCat.of R),⊤) r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv r := by
    change (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = _
    exact congrArg (fun φ=>φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
      ((Spec (CommRingCat.of R)).presheaf.map_id (op ⊤))
  simpa only [htop] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineTopDifferentialSheafIso_differentialWedge_top

end Source_ToricAffineDifferentialWedges

section Source_ToricInvertiblePullback

/-!
# Ordinary pullback preserves actual invertible module sheaves

The proof uses the genuine pullback pseudofunctor, the established
equivalence between an open subsite and its open subscheme, and the
ordinary pullback of the structure module. It applies to arbitrary
scheme morphisms, including nondominant closed immersions.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

namespace ModuleFrame

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- The actual open-subscheme version of a frame on the open subsite. -/
def toRestrictIso (e : ModuleFrame M U) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((overFunctorEquiv U).app M).symm ≪≫
    (overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Transport a genuine open-subscheme frame back to the open subsite. -/
def ofRestrictIso
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ModuleFrame M U :=
  (overEquiv U).unitIso.app (M.over U) ≪≫
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M ≪≫ e) ≪≫
      U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

end ModuleFrame

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The pullback of the actual structure module is the actual structure
module; finality here follows from preservation of the terminal open. -/
def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : Limits.PreservesFiniteLimits (Opens.map f.base) := by
    change Limits.PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
    infer_instance
  letI : (Opens.map f.base).Final := inferInstance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
      (R := Y.ringCatSheaf) f.toRingCatSheafHom) := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
    (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
    (R := Y.ringCatSheaf) f.toRingCatSheafHom)

namespace ModuleFrame

variable {M : X.Modules} {U : X.Opens} (e : ModuleFrame M U)

/-- The actual pullback frame, with its actual preimage open. -/
def pullbackRestrictIso :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let g : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme := f ∣_ U
  have hg : (f ⁻¹ᵁ U).ι ≫ f = g ≫ U.ι := by
    exact (morphismRestrict_ι f U).symm
  exact
    (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr hg).app M ≪≫
    ((pullbackComp g U.ι).app M).symm ≪≫
    (pullback g).mapIso ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (pullback g).mapIso e.toRestrictIso ≪≫
    pullbackUnitIso g

def pullbackFrame : ModuleFrame ((pullback f).obj M) (f ⁻¹ᵁ U) :=
  ofRestrictIso (pullbackRestrictIso f e)

end ModuleFrame

/-- Pullback preserves genuine local rank one without a dominance,
flatness, smoothness, or integrality assumption on the morphism. -/
theorem isInvertibleModule_pullback {M : X.Modules} (hM : IsInvertibleModule M) :
    IsInvertibleModule ((pullback f).obj M) := by
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := hM (f y)
  exact ⟨f ⁻¹ᵁ U,hy,⟨ModuleFrame.pullbackFrame f e⟩⟩

/-- On an integral target of pullback, the pulled-back invertible sheaf
therefore has an actual fractional Cartier presentation as well. -/
theorem exists_cartierData_pullback [IsIntegral Y]
    {M : X.Modules} (hM : IsInvertibleModule M) :
    ∃ D : CartierData Y,Nonempty ((pullback f).obj M≅D.sheaf) :=
  exists_cartierData_of_isInvertibleModule _ (isInvertibleModule_pullback f hM)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_pullback
#print axioms PaperVerification.ToricSchemes.exists_cartierData_pullback

end Source_ToricInvertiblePullback

section Source_ToricOpenModuleFrames

/-! # Actual open-chart frames on the corresponding open subsite -/


universe u

namespace PaperVerification.ToricSchemes.ModuleFrame

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- The inverse open-subsite transport is a genuine inverse on frames. -/
theorem toRestrictIso_ofRestrictIso
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    toRestrictIso (ofRestrictIso d) = d := by
  let E := overEquiv U
  let c := (overFunctorEquiv U).app M
  let v := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  have hpre : E.functor.map (ofRestrictIso d).hom = c.hom ≫ d.hom ≫ v.inv := by
    simpa only [E,c,v,ofRestrictIso,Scheme.Modules.overEquiv,
      TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit,
      Equivalence.fullyFaithfulFunctor,Iso.trans_hom,Iso.symm_hom,
      Iso.app_hom,Iso.app_inv,Functor.mapIso_hom,Functor.map_comp,Category.assoc] using
      E.fullyFaithfulFunctor.map_preimage (c.hom ≫ d.hom ≫ v.inv)
  apply Iso.ext
  change c.inv ≫ E.functor.map (ofRestrictIso d).hom ≫ v.hom = d.hom
  rw [hpre]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

/-- The forward open-site comparison evaluates the actual inverse frame. -/
theorem toRestrictIso_generator_eval (f : ModuleFrame M U) :
    (M.restrictAppIso U.ι ⊤).hom
      ((toRestrictIso f).inv.app ⊤ (1 : Γ(U.toScheme,⊤))) =
      f.generator (U.ι ''ᵁ ⊤) (U.ι_image_le ⊤) := by
  rfl

/-- The frame transported back to the open subsite has the expected section. -/
theorem ofRestrictIso_generator_eval
    (d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((M.restrictAppIso U.ι ⊤).hom (d.inv.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
      (ofRestrictIso d).generator U le_rfl := by
  have hgen := toRestrictIso_generator_eval (ofRestrictIso d)
  rw [toRestrictIso_ofRestrictIso d] at hgen
  rw [hgen]
  rw [← (ofRestrictIso d).generator_res le_rfl (U.ι_image_le ⊤)]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (M.presheaf.map (homOfLE (U.ι_image_le ⊤)).op
      ((ofRestrictIso d).generator U le_rfl)) = _
  rw [← ConcreteCategory.comp_apply,← Functor.map_comp,← op_comp]
  have hc : eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) = 𝟙 U :=
    Subsingleton.elim _ _
  rw [hc,op_id]
  exact congrArg (fun φ=>φ ((ofRestrictIso d).generator U le_rfl))
    (M.presheaf.map_id (op U))


variable {X Y : Scheme.{u}} (j : Y⟶X) [IsOpenImmersion j]
    {M : X.Modules} (e : M.restrict j≅SheafOfModules.unit Y.ringCatSheaf)

/-- Move a chart frame through the actual isomorphism with its open
image, then through the established open-subscheme/open-subsite
equivalence. -/
def ofOpenImmersionIso : ModuleFrame M j.opensRange :=
  ofRestrictIso
    (((restrictFunctorCongr j.isoOpensRange_inv_comp).app M).symm ≪≫
      (restrictFunctorComp j.isoOpensRange.inv j).app M ≪≫
        (restrictFunctor j.isoOpensRange.inv).mapIso e ≪≫
          restrictUnitIso j.isoOpensRange.inv)

/-- The actual global section on the open image corresponding to the
chart's distinguished section. -/
def imageFrameGenerator : Γ(M,j.opensRange) :=
  M.presheaf.map (eqToHom (j.image_top_eq_opensRange).symm).op
    ((M.restrictAppIso j ⊤).hom (e.inv.app ⊤ (1 : Γ(Y,⊤))))

/-- The actual inverse structure-module restriction preserves one. -/
theorem restrictUnitIso_inv_one {Y Z : Scheme.{u}} (f : Y⟶Z)
    [IsOpenImmersion f] (V : Y.Opens) :
    (restrictUnitIso f).inv.app V (1 : Γ(Y,V)) =
      (1 : Γ(Z,f ''ᵁ V)) := by
  change (f.appIso V).inv (1 : Γ(Y,V)) = 1
  exact map_one _

set_option maxHeartbeats 2000000 in
/-- No independent scalar is introduced when the chart frame is moved
to the image open. -/
theorem ofOpenImmersionIso_generator :
    (ofOpenImmersionIso j e).generator j.opensRange le_rfl=imageFrameGenerator j e := by
  have he (V : Y.Opens) : e.inv.app V (1 : Γ(Y,V)) =
      (M.restrict j).presheaf.map (homOfLE (show V≤⊤ from le_top)).op
        (e.inv.app ⊤ (1 : Γ(Y,⊤))) := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op (1 : Γ(Y,⊤))
    change e.inv.app V
      ((Y.presheaf.map (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op).hom 1) =
        (M.restrict j).presheaf.map (homOfLE le_top).op
          (e.inv.app ⊤ (1 : Γ(Y,⊤))) at hn
    simpa only [map_one] using hn
  have hmap : ((restrictFunctor j.isoOpensRange.inv).map e.inv).app ⊤
      (1 : Γ(Y,j.isoOpensRange.inv ''ᵁ ⊤)) =
      e.inv.app (j.isoOpensRange.inv ''ᵁ ⊤)
        (1 : Γ(Y,j.isoOpensRange.inv ''ᵁ ⊤)) := rfl
  unfold ofOpenImmersionIso
  rw [← ofRestrictIso_generator_eval]
  simp only [Iso.trans_inv,Iso.symm_inv,Iso.app_hom,Iso.app_inv,
    Functor.mapIso_inv,Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,
    restrictUnitIso_inv_one,Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  erw [hmap,he (j.isoOpensRange.inv ''ᵁ ⊤)]
  let V : Y.Opens := j.isoOpensRange.inv ''ᵁ ⊤
  let t : Γ(M,j ''ᵁ ⊤) :=
    (M.restrictAppIso j ⊤).hom (e.inv.app ⊤ (1 : Γ(Y,⊤)))
  have hi : (j.isoOpensRange.inv ≫ j) ''ᵁ (⊤ : j.opensRange.toScheme.Opens) =
      j.opensRange.ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    simp only [Scheme.Hom.coe_image]
    rw [j.isoOpensRange_inv_comp]
  change M.presheaf.map (eqToHom j.opensRange.ι_image_top.symm).op
    (M.presheaf.map (eqToHom hi.symm).op
      (M.presheaf.map (eqToHom (Scheme.Hom.comp_image j.isoOpensRange.inv j ⊤)).op
        (M.presheaf.map
          ((j.opensFunctor.map (homOfLE (show V ≤ (⊤ : Y.Opens) from le_top))).op) t))) =
    M.presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op t
  have hcomp {U V W : X.Opensᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
      (s : M.presheaf.obj U) :
      M.presheaf.map g (M.presheaf.map f s) = M.presheaf.map (f ≫ g) s :=
    (congrArg (fun φ : M.presheaf.obj U ⟶ M.presheaf.obj W => φ s)
      (M.presheaf.map_comp f g)).symm
  simp only [hcomp]
  erw [hcomp]
  apply congrArg (fun φ : op (j ''ᵁ (⊤ : Y.Opens)) ⟶ op j.opensRange =>
    M.presheaf.map φ t)
  exact Subsingleton.elim _ _

end PaperVerification.ToricSchemes.ModuleFrame

end Source_ToricOpenModuleFrames

section Source_ToricFanDifferentials

/-!
# Actual generic and affine-chart differential forms on the fan scheme

The coefficient field is the actual generic stalk of the glued scheme.
Its algebra structures are explicitly induced by the previously proved
chart maps. The fraction-field assertion is transferred from the actual
open affine zero-cone chart. Full-chart Kähler bases are then constructed
through the literal polynomial character presentations.
-/


universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def fanFunctionFieldAlgebra : Algebra k («Σ».fanScheme k).functionField :=
  BaseSections.functionFieldAlgebra k («Σ».fanScheme k)

def torusFunctionFieldAlgebra :
    Algebra (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  («Σ».torusRationalMap k).toAlgebra

def chartFunctionFieldAlgebra (s : «Σ».ConeIndex) :
    Algebra (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  («Σ».chartRationalMap k s).toAlgebra

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra

instance fanFunctionField_scalarTower :
    IsScalarTower k (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  IsScalarTower.of_algebraMap_eq fun r => («Σ».rationalScalar_eq_algebraMap k r).symm

instance chartFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField :=
  ⟨fun r a z => smul_assoc r (a : AddMonoidAlgebra k (Lattice n)) z⟩

instance chartTorusFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower (monoidChartAlgebra k (dualConeMonoid s.val))
      (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  ⟨fun a r z => smul_assoc (a : AddMonoidAlgebra k (Lattice n)) r z⟩

/-- This localization is for the exact character map into the generic
stalk, not for an independently chosen isomorphic field. -/
theorem torusFunctionField_isFractionRing :
    IsFractionRing (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField := by
  let R := monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n)))
  letI : IsDomain R := «Σ».chartRing_isDomain k ∅ «Σ».zeroConeIndex.property
  let j : Spec (CommRingCat.of R) ⟶ «Σ».fanScheme k := «Σ».torusOpenMap k
  letI : IsOpenImmersion j := «Σ».torusOpenMap_isOpenImmersion k
  letI : Algebra R («Σ».fanScheme k).functionField :=
    affineOpenCoordinateAlgebra (CommRingCat.of R) j
  letI : IsFractionRing R («Σ».fanScheme k).functionField :=
    affineOpenCoordinate_isFractionRing (CommRingCat.of R) j
  exact IsFractionRing.of_ringEquiv_left (zeroConeChartAlgEquiv k n).symm.toRingEquiv
    (fun _ => rfl)

attribute [local instance] torusFunctionField_isFractionRing

def genericLogDifferentialBasis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) («Σ».fanScheme k).functionField
      Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b

def genericLogVolume (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    ⋀[(«Σ».fanScheme k).functionField]^n Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogVolume k («Σ».fanScheme k).functionField b

/-- The actual module Ω of the actual affine coordinate ring. -/
def actualFullChartDifferentialBasis (s : «Σ».fullCones) :
    Module.Basis (Fin n) (monoidChartAlgebra k (dualConeMonoid s.val))
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k] :=
  polynomialDifferentialBasis k («Σ».fullChartPolynomialPresentation k s)

@[simp] theorem actualFullChartDifferentialBasis_apply (s : «Σ».fullCones) (i : Fin n) :
    «Σ».actualFullChartDifferentialBasis k s i =
      D k (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fullChartCoordinate k s i) := by
  rw [actualFullChartDifferentialBasis, polynomialDifferentialBasis_apply,
    fullChartPolynomialPresentation_X]

@[simp] theorem map_actualFullChartDifferentialBasis (s : «Σ».fullCones) (i : Fin n) :
    KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField («Σ».actualFullChartDifferentialBasis k s i) =
      D k («Σ».fanScheme k).functionField
        («Σ».rationalCharacter k («Σ».fullCharacterBasis s i)) := by
  rw [actualFullChartDifferentialBasis_apply, KaehlerDifferential.map_D]
  congr 1

/-- Coefficients of actual chart top forms in an actual generic logarithmic
volume. This definition uses only Kähler functoriality and the universal
exterior map; the support-coefficient formula is proved afterward. -/
def actualChartTopCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) :
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) →ₗ[
        monoidChartAlgebra k (dualConeMonoid s.val)] («Σ».fanScheme k).functionField :=
  ((basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀)).toLinearMap.restrictScalars _).comp
    (exteriorScalarExtensionMap (S := («Σ».fanScheme k).functionField)
      (KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField))

def chartVolumeCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ((«Σ».fanScheme k).functionField)ˣ :=
  «Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) *
    Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
      (b₀.isUnit_det («Σ».fullCharacterBasis s)).unit

@[simp] theorem chartVolumeCoefficient_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) =
      («Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) : («Σ».fanScheme k).functionField) *
        (b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) := rfl

theorem actualChartTopCoefficient_basis
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    «Σ».actualChartTopCoefficient k b₀ s
        (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
          («Σ».actualFullChartDifferentialBasis k s)) =
      («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) := by
  rw [actualChartTopCoefficient, LinearMap.comp_apply,
    exteriorScalarExtensionMap_wedge]
  simp_rw [«Σ».map_actualFullChartDifferentialBasis k s]
  change basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
        (fractionRegularCoordinateVolume k («Σ».fanScheme k).functionField
          («Σ».fullCharacterBasis s)) = _
  rw [fractionRegularCoordinateVolume_eq_character, map_smul,
    fractionLogVolume_change_basis k («Σ».fanScheme k).functionField b₀
      («Σ».fullCharacterBasis s), map_smul]
  change _ * ((b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) *
    basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
      (exteriorPower.ιMulti («Σ».fanScheme k).functionField n
        (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀))) = _
  rw [basisTopExteriorEquiv_basis, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar action inherited from the Laurent ring agrees with
regular evaluation through the actual full-chart map. -/
theorem fullChart_functionField_smul (s : «Σ».fullCones)
    (a : monoidChartAlgebra k (dualConeMonoid s.val))
    (z : («Σ».fanScheme k).functionField) :
    a • z = «Σ».chartRationalMap k («Σ».fullConeIndex s) a * z := by
  change «Σ».torusRationalMap k (a : AddMonoidAlgebra k (Lattice n)) * z = _
  exact congrArg (fun r => r * z)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) a).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Linearity and the genuine exterior basis determine every coefficient;
the scalar compatibility is proved through the actual chart morphism. -/
theorem actualChartTopCoefficient_apply
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    «Σ».actualChartTopCoefficient k b₀ s ω =
      «Σ».chartRationalMap k («Σ».fullConeIndex s)
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω) *
          «Σ».chartVolumeCoefficient k b₀ s := by
  calc
    _ = «Σ».actualChartTopCoefficient k b₀ s
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
          exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) :=
      congrArg («Σ».actualChartTopCoefficient k b₀ s)
        (topExterior_eq_smul_basis («Σ».actualFullChartDifferentialBasis k s) ω)
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
      congrArg (fun z : («Σ».fanScheme k).functionField =>
        basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω • z)
        («Σ».actualChartTopCoefficient_basis k b₀ s)
    _ = _ := «Σ».fullChart_functionField_smul k s _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem mem_range_actualChartTopCoefficient_iff
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (z : («Σ».fanScheme k).functionField) :
    z ∈ LinearMap.range («Σ».actualChartTopCoefficient k b₀ s) ↔
      ∃ r : monoidChartAlgebra k (dualConeMonoid s.val),
        «Σ».chartRationalMap k («Σ».fullConeIndex s) r * «Σ».chartVolumeCoefficient k b₀ s = z := by
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω,
      («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨r • exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s), ?_⟩
    calc
      _ = r • «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
      _ = r • («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
        congrArg (fun z : («Σ».fanScheme k).functionField => r • z)
          («Σ».actualChartTopCoefficient_basis k b₀ s)
      _ = «Σ».chartRationalMap k («Σ».fullConeIndex s) r *
          «Σ».chartVolumeCoefficient k b₀ s := «Σ».fullChart_functionField_smul k s r _
      _ = z := hr

set_option backward.isDefEq.respectTransparency.types false in
theorem actualChartTopCoefficient_injective
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    Function.Injective («Σ».actualChartTopCoefficient k b₀ s) := by
  intro ω η he
  apply (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s)).injective
  apply «Σ».chartRationalMap_injective k («Σ».fullConeIndex s)
  apply mul_right_cancel₀ (Units.ne_zero («Σ».chartVolumeCoefficient k b₀ s))
  exact («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm.trans
    (he.trans («Σ».actualChartTopCoefficient_apply k b₀ s η))

/-- The local character is computed from the actual differential volume.
This is the sign in the toric canonical divisor formula. -/
theorem canonical_cartierLatticePoint (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint (fun _ => -1) s = ∑ i, «Σ».fullCharacterBasis s i := by
  simp only [cartierLatticePoint, neg_one_zsmul, Finset.sum_neg_distrib, neg_neg]
  rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.actualChartTopCoefficient_basis

end Source_ToricFanDifferentials

section Source_ToricCanonicalDifferentialCocycle

/-!
# Gluing the actual top differential modules

The rational local generators here are the coefficients of the actual
top Kähler forms, defined through their images in the generic differential
module. Their regular-unit transition property is proved from the
differential calculation. Thus the resulting invertible fractional sheaf
is obtained from genuine differential modules. Its identification with
the fan coefficient function -1 is a theorem.
-/


universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- Equal actual subsheaves give equivalent fractional presentations,
with the rational embeddings preserved. -/
theorem cartierCocycles_equivalent_of_submodule_eq
    (C D : RationalCartierCocycle X) (h : C.sheafSubmodule = D.sheafSubmodule) :
    C.toCartierData.Equivalent D.toCartierData := by
  have aux {A B : (rationalFunctions X).Submodule} (hAB : A = B) :
      ∃ e : A.toSheafOfModules ≅ B.toSheafOfModules, e.hom ≫ B.ι = A.ι := by
    subst B
    exact ⟨Iso.refl _, Category.id_comp _⟩
  exact aux h

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AddMonoidAlgebra KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- The nonzero rational coefficient of a genuine regular coordinate
volume. Its definition refers to the actual Kähler map, not a divisor
coefficient or a prescribed character. -/
def differentialVolumeUnit (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ((«Σ».fanScheme k).functionField)ˣ :=
  Units.mk0
    («Σ».actualChartTopCoefficient k b₀ s
      (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
        («Σ».actualFullChartDifferentialBasis k s))) (by
      rw [«Σ».actualChartTopCoefficient_basis]
      exact Units.ne_zero _)

theorem differentialVolumeUnit_eq (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) :
    «Σ».differentialVolumeUnit k b₀ s = «Σ».chartVolumeCoefficient k b₀ s := by
  apply Units.ext
  exact «Σ».actualChartTopCoefficient_basis k b₀ s

def differentialDetUnit (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ℤˣ :=
  (b₀.isUnit_det («Σ».fullCharacterBasis s)).unit

theorem differentialVolumeUnit_character
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    «Σ».differentialVolumeUnit k b₀ s =
      «Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) *
        Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
          («Σ».differentialDetUnit b₀ s) := by
  rw [«Σ».differentialVolumeUnit_eq, «Σ».canonical_cartierLatticePoint]
  rfl

theorem differentialVolume_transition_regular
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s t : «Σ».fullCones)
    (x : «Σ».fanScheme k) (hxs : x ∈ «Σ».fullChartOpen k s)
    (hxt : x ∈ «Σ».fullChartOpen k t) :
    ((«Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) /
      («Σ».differentialVolumeUnit k b₀ t : («Σ».fanScheme k).functionField)) ∈
        regularAtSubring («Σ».fanScheme k) x := by
  have hc := «Σ».cartier_rational_transition_regular k (fun _ => -1) s t x hxs hxt
  have hd : (((«Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t : ℤˣ) : ℤ) :
      («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have he :
      («Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) /
          («Σ».differentialVolumeUnit k b₀ t : («Σ».fanScheme k).functionField) =
        ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) :
            («Σ».fanScheme k).functionField) /
          («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) t) :
            («Σ».fanScheme k).functionField)) *
          (((«Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t : ℤˣ) : ℤ) :
            («Σ».fanScheme k).functionField) := by
    rw [«Σ».differentialVolumeUnit_character, «Σ».differentialVolumeUnit_character]
    let ψ : ℤˣ →* ((«Σ».fanScheme k).functionField)ˣ :=
      Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
    change
      ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) *
          ψ («Σ».differentialDetUnit b₀ s) : ((«Σ».fanScheme k).functionField)ˣ) :
          («Σ».fanScheme k).functionField) /
        ((«Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) t) *
          ψ («Σ».differentialDetUnit b₀ t) : ((«Σ».fanScheme k).functionField)ˣ) :
          («Σ».fanScheme k).functionField) =
        _ * ((ψ («Σ».differentialDetUnit b₀ s / «Σ».differentialDetUnit b₀ t) :
          ((«Σ».fanScheme k).functionField)ˣ) : («Σ».fanScheme k).functionField)
    rw [map_div]
    simp only [Units.val_mul, Units.val_div_eq_div_val]
    exact mul_div_mul_comm _ _ _ _
  rw [he]
  exact (regularAtSubring («Σ».fanScheme k) x).mul_mem hc hd

/-- The actual differential-volume gluing data. The cover is the genuine
full affine cover, and the generators come from its actual top Ω modules. -/
def differentialVolumeCocycle (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    RationalCartierCocycle («Σ».fanScheme k) where
  index := ULift.{u} «Σ».fullCones
  openSet i := «Σ».fullChartOpen k i.down
  covers x := by
    obtain ⟨s, hs⟩ := «Σ».fullChartOpen_cover k hpure x
    exact ⟨⟨s⟩, hs⟩
  generator i := «Σ».differentialVolumeUnit k b₀ i.down
  transition i j x hi hj := «Σ».differentialVolume_transition_regular k b₀ i.down j.down x hi hj

/-- The invertible fractional sheaf obtained by gluing the actual local
top differential modules through their generic differential images. -/
def differentialVolumeData (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    CartierData («Σ».fanScheme k) :=
  («Σ».differentialVolumeCocycle k hpure b₀).toCartierData

theorem differential_division_regular_iff
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (x : «Σ».fanScheme k) (z : («Σ».fanScheme k).functionField) :
    z / («Σ».differentialVolumeUnit k b₀ s : («Σ».fanScheme k).functionField) ∈
        regularAtSubring («Σ».fanScheme k) x ↔
      z / («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) s) :
        («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x := by
  let d := «Σ».differentialDetUnit b₀ s
  have hd : ((d : ℤ) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have hdi : (((d⁻¹ : ℤˣ) : ℤ) : («Σ».fanScheme k).functionField) ∈
      regularAtSubring («Σ».fanScheme k) x :=
    intCast_mem (regularAtSubring («Σ».fanScheme k) x) _
  have hdinv : (((d⁻¹ : ℤˣ) : ℤ) : («Σ».fanScheme k).functionField) =
      (((d : ℤ) : («Σ».fanScheme k).functionField))⁻¹ := by
    exact Units.val_inv_eq_inv_val
      (Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom d)
  have hd0 : ((d : ℤ) : («Σ».fanScheme k).functionField) ≠ 0 :=
    Units.ne_zero (Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom d)
  rw [«Σ».differentialVolumeUnit_character, Units.val_mul]
  change z / (_ * ((d : ℤ) : («Σ».fanScheme k).functionField)) ∈ _ ↔ _
  constructor
  · intro h
    have hm := (regularAtSubring («Σ».fanScheme k) x).mul_mem h hd
    convert hm using 1
    field_simp [Units.ne_zero, hd0]
  · intro h
    have hm := (regularAtSubring («Σ».fanScheme k) x).mul_mem h hdi
    rw [hdinv] at hm
    convert hm using 1
    field_simp [Units.ne_zero, hd0]

theorem differentialVolume_subsheaf_eq (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeCocycle k hpure b₀).sheafSubmodule =
      («Σ».fanCartierCocycle k hpure (fun _ => -1)).sheafSubmodule := by
  apply SheafOfModules.Submodule.ext
  apply PresheafOfModules.Submodule.ext
  intro U
  apply Submodule.ext
  intro z
  change (∀ i : ULift.{u} «Σ».fullCones, ∀ x : U.unop,
      x.val ∈ «Σ».fullChartOpen k i.down →
        rationalValueAt («Σ».fanScheme k) U.unop x z /
          («Σ».differentialVolumeUnit k b₀ i.down : («Σ».fanScheme k).functionField) ∈
            regularAtSubring («Σ».fanScheme k) x.val) ↔
    (∀ i : ULift.{u} «Σ».fullCones, ∀ x : U.unop,
      x.val ∈ «Σ».fullChartOpen k i.down →
        rationalValueAt («Σ».fanScheme k) U.unop x z /
          («Σ».rationalCharacter k («Σ».cartierLatticePoint (fun _ => -1) i.down) :
            («Σ».fanScheme k).functionField) ∈ regularAtSubring («Σ».fanScheme k) x.val)
  exact forall_congr' fun i => forall_congr' fun x => imp_congr_right fun _ =>
    «Σ».differential_division_regular_iff k b₀ i.down x.val _

/-- The toric canonical coefficient formula, obtained from the actual
top Kähler gluing and preserving its embedding in rational functions. -/
theorem differentialVolumeData_equivalent_canonical (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeData k hpure b₀).Equivalent
      («Σ».fanCartierData k hpure (fun _ => -1)) :=
  cartierCocycles_equivalent_of_submodule_eq _ _
    («Σ».differentialVolume_subsheaf_eq k hpure b₀)

/-- The actual affine sheaf associated to the full chart's top Kähler
module. This is independent of the Cartier coefficient formula. -/
def fullChartTopDifferentialSheaf (s : «Σ».fullCones) : (coneChart k s.val).Modules :=
  tilde (ModuleCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]))

/-- Its local freeness follows from the actual polynomial Ω basis. -/
def fullChartTopDifferentialFrame (s : «Σ».fullCones) :
    «Σ».fullChartTopDifferentialSheaf k s ≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  (tilde.functor (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))).mapIso
      (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s)).toModuleIso ≪≫ tildeSelf

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.differentialVolumeData_equivalent_canonical

end Source_ToricCanonicalDifferentialCocycle

section Source_ToricCanonicalDifferentialGluing

/-!
# The differential gluing maps are actual localization maps

Kähler functoriality and exterior functoriality give compatibility on
chains of actual ring maps. Localizing a free differential module
localizes its top exterior power; the resulting base-change equivalence
is computed on its genuine wedge generator. The global differential
volume sheaf restricts to the actual tilde of each chart's top Ω module.
-/


universe u

namespace PaperVerification.ToricCharacters

open KaehlerDifferential
open scoped BigOperators Classical TensorProduct

section Naturality

variable (k R S T : Type*) [CommRing k] [CommRing R] [CommRing S] [CommRing T]
    [Algebra k R] [Algebra k S] [Algebra k T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower k R S] [IsScalarTower k S T] [IsScalarTower k R T]
    [IsScalarTower R S T]

theorem kahler_map_comp :
    (KaehlerDifferential.map k k S T).restrictScalars R ∘ₗ
        KaehlerDifferential.map k k R S = KaehlerDifferential.map k k R T := by
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
    (KaehlerDifferential.span_range_derivation k R)]
  rintro ⟨_, ⟨r, rfl⟩⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply R S T]

def topDifferentialMap (n : ℕ) :
    (⋀[R]^n Ω[R⁄k]) →ₗ[R] (⋀[S]^n Ω[S⁄k]) :=
  exteriorScalarExtensionMap (S := S) (KaehlerDifferential.map k k R S)

@[simp] theorem topDifferentialMap_wedge (n : ℕ) (v : Fin n → Ω[R⁄k]) :
    topDifferentialMap k R S n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => KaehlerDifferential.map k k R S (v i)) :=
  exteriorScalarExtensionMap_wedge _ _

theorem topDifferentialMap_comp (n : ℕ) :
    (topDifferentialMap k S T n).restrictScalars R ∘ₗ
        topDifferentialMap k R S n = topDifferentialMap k R T n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, topDifferentialMap_wedge]
  apply congrArg (fun w : Fin n → Ω[T⁄k] => exteriorPower.ιMulti T n w)
  funext i
  exact congrArg (fun f => f (v i)) (kahler_map_comp k R S T)

end Naturality

section Localization

variable (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    {n : ℕ} (M : Submonoid R) [IsLocalization M S]
    (b : Module.Basis (Fin n) R Ω[R⁄k])

def localizedDifferentialBasis : Module.Basis (Fin n) S Ω[S⁄k] :=
  b.ofIsLocalizedModule S M (KaehlerDifferential.map k k R S)

theorem localized_topDifferential_coefficient (ω : ⋀[R]^n Ω[R⁄k]) :
    basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)
        (topDifferentialMap k R S n ω) =
      algebraMap R S (basisTopExteriorEquiv b ω) := by
  conv_lhs => rw [topExterior_eq_smul_basis b ω]
  rw [map_smul, topDifferentialMap_wedge]
  have hb : (fun i => KaehlerDifferential.map k k R S (b i)) =
      localizedDifferentialBasis k R S M b := by
    funext i
    exact (b.ofIsLocalizedModule_apply S M
      (KaehlerDifferential.map k k R S) i).symm
  rw [hb, ← IsScalarTower.algebraMap_smul S, map_smul,
    basisTopExteriorEquiv_basis, smul_eq_mul, mul_one]

include M b in
/-- A free top differential module embeds in its localization whenever
the underlying coordinate-ring map is injective. -/
theorem topDifferentialMap_injective_of_localization
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (topDifferentialMap k R S n) := by
  intro ω η h
  apply (basisTopExteriorEquiv b).injective
  apply hinj
  simpa only [localized_topDifferential_coefficient] using
    congrArg (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)) h

/-- The actual top differential modules before and after localization
satisfy the ordinary tensor-product base-change property. -/
def topDifferentialLocalizationEquiv :
    S ⊗[R] (⋀[R]^n Ω[R⁄k]) ≃ₗ[S] (⋀[S]^n Ω[S⁄k]) :=
  ((basisTopExteriorEquiv b).baseChange R S (⋀[R]^n Ω[R⁄k]) R).trans
    ((TensorProduct.AlgebraTensorModule.rid R S S).trans
      (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)).symm)

theorem topDifferentialLocalizationEquiv_tmul (s : S) (ω : ⋀[R]^n Ω[R⁄k]) :
    topDifferentialLocalizationEquiv k R S M b (s ⊗ₜ[R] ω) =
      s • topDifferentialMap k R S n ω := by
  apply (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)).injective
  simp only [topDifferentialLocalizationEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    LinearEquiv.apply_symm_apply, map_smul, localized_topDifferential_coefficient,
    smul_eq_mul, Algebra.smul_def]
  exact mul_comm _ _

end Localization

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X]
    (C : RationalCartierCocycle X) (i : C.index)
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : j.opensRange ≤ C.openSet i)

/-- The proved cocycle frame transported to an actual open chart, with
the actual section isomorphism supplying the scalar change. -/
def cocycleOpenFrameCoordinates (U : Y.Opens) :
    Γ(C.sheaf.restrict j,U) ≃ₗ[Γ(Y,U)] Γ(Y,U) := by
  let hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  let eM := (C.sheaf.restrictAppIso j U).addCommGroupIsoToAddEquiv
  let eX := C.localCoordinates i (j ''ᵁ U) hU
  let eR := (j.appIso U).commRingCatIsoToRingEquiv
  refine
    { toFun := fun s => eR (eX (eM s))
      invFun := fun a => eM.symm (eX.symm (eR.symm a))
      left_inv := by intro s; simp
      right_inv := by intro a; simp
      map_add' := by intro s t; simp
      map_smul' := ?_ }
  intro a s
  change eR (eX (eR.symm a • eM s)) = a * eR (eX (eM s))
  rw [eX.map_smul]
  change eR (eR.symm a * eX (eM s)) = _
  rw [map_mul, RingEquiv.apply_symm_apply]

theorem cocycleOpenFrameCoordinates_restrict
    {U V : Y.Opens} (f : V ⟶ U) (s : Γ(C.sheaf.restrict j,U)) :
    cocycleOpenFrameCoordinates C i j hj V
      ((C.sheaf.restrict j).presheaf.map f.op s) =
      Y.presheaf.map f.op (cocycleOpenFrameCoordinates C i j hj U s) := by
  let f' : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_mono f.le)
  let t : Γ(C.sheaf,j ''ᵁ U) := (C.sheaf.restrictAppIso j U).hom s
  have hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  have hV : j ''ᵁ V ≤ C.openSet i := (j.image_mono f.le).trans hU
  change (j.appIso V).hom
      (C.localCoordinates i (j ''ᵁ V) hV
        (C.sheaf.presheaf.map f'.op t)) =
    Y.presheaf.map f.op ((j.appIso U).hom (C.localCoordinates i (j ''ᵁ U) hU t))
  have hn : X.presheaf.map f'.op ≫ (j.appIso V).hom =
      (j.appIso U).hom ≫ Y.presheaf.map f.op := by
    simp [Scheme.Hom.appIso_hom']
  calc
    _ = (j.appIso V).hom (X.presheaf.map f'.op
        (C.localCoordinates i (j ''ᵁ U) hU t)) :=
      congrArg (fun a : Γ(X,j ''ᵁ V) => (j.appIso V).hom a)
        (C.localCoordinates_restrict i f' hU hV t)
    _ = _ := congrArg (fun h : Γ(X,j ''ᵁ U) ⟶ Γ(Y,V) =>
      h (C.localCoordinates i (j ''ᵁ U) hU t)) hn

def cocycleOpenFrame :
    C.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (cocycleOpenFrameCoordinates C i j hj U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        exact cocycleOpenFrameCoordinates_restrict C i j hj f.unop s)

theorem cocycleOpenFrameCoordinates_value (U : Y.Opens) [Nonempty U]
    (s : Γ(C.sheaf.restrict j,U)) :
    letI : Nonempty (j ''ᵁ U) := by
      obtain ⟨y⟩ := (inferInstance : Nonempty U)
      exact ⟨⟨j y.val,⟨y.val,y.property,rfl⟩⟩⟩
    X.germToFunctionField (j ''ᵁ U)
      ((j.appIso U).inv (cocycleOpenFrameCoordinates C i j hj U s)) =
        rationalValue X (j ''ᵁ U)
          ((C.sheaf.restrictAppIso j U).hom s).val / (C.generator i : X.functionField) := by
  letI : Nonempty (j ''ᵁ U) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨j y.val,⟨y.val,y.property,rfl⟩⟩⟩
  let t : Γ(C.sheaf,j ''ᵁ U) := (C.sheaf.restrictAppIso j U).hom s
  have hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  change X.germToFunctionField (j ''ᵁ U)
      ((j.appIso U).inv ((j.appIso U).hom
        (C.localCoordinates i (j ''ᵁ U) hU t))) =
    rationalValue X (j ''ᵁ U) t.val / (C.generator i : X.functionField)
  rw [Iso.hom_inv_id_apply]
  exact C.localCoordinates_value i (j ''ᵁ U) hU t

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- The global differential sheaf restricts to the actual affine sheaf
associated to the actual top Kähler module of every full smooth chart.
The coordinate maps divide by the genuine generic differential image. -/
def differentialVolumeData_chartIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    («Σ».differentialVolumeData k hpure b₀).sheaf.restrict
        («Σ».fanChartMap k («Σ».fullConeIndex s)) ≅
      «Σ».fullChartTopDifferentialSheaf k s :=
  cocycleOpenFrame («Σ».differentialVolumeCocycle k hpure b₀) ⟨s⟩
      («Σ».fanChartMap k («Σ».fullConeIndex s)) le_rfl ≪≫
    («Σ».fullChartTopDifferentialFrame k s).symm

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricCharacters.topDifferentialMap_comp
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.differentialVolumeData_chartIso

end Source_ToricCanonicalDifferentialGluing

section Source_ToricDifferentialOverlaps

/-!
# Natural differential localization on actual fan overlaps

The maps below are induced by the literal inclusions of character
algebras. Every cone chart has a free Kähler module, obtained by
localizing a full chart. Its top differential module injects into the
actual generic differential module. Consequently agreement on an
intersection chart is exactly agreement of the actual generic forms.
This supplies the overlap compatibility of the differential-volume
sheaf, independently of its later Cartier description.
-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open KaehlerDifferential

/-- Coefficients after the genuine differential map to a coefficient
ring. Keeping this composition over abstract rings fixes the native
restricted exterior-module structure before applying it to a chart. -/
def topDifferentialCoefficient (k R K : Type*)
    [CommRing k] [CommRing R] [CommRing K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    (n : ℕ) (b : Module.Basis (Fin n) K Ω[K⁄k]) :
    (⋀[R]^n Ω[R⁄k]) →ₗ[R] K :=
  ((basisTopExteriorEquiv b).toLinearMap.restrictScalars R).comp
    (topDifferentialMap k R K n)

/-- Equal actual structure homomorphisms induce the same coefficient
function. The scalar-tower witnesses are propositions; no definitional
identification of unequal chosen algebra structures is assumed. -/
theorem topDifferentialCoefficient_algebra_eq (k R K : Type*)
    [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra k K]
    (A B : Algebra R K) (hAB : A=B)
    (hA : letI := A; IsScalarTower k R K)
    (hB : letI := B; IsScalarTower k R K)
    (n : ℕ) (b : Module.Basis (Fin n) K Ω[K⁄k]) (ω : ⋀[R]^n Ω[R⁄k]) :
    (letI := A; letI := hA; topDifferentialCoefficient k R K n b ω)=
      (letI := B; letI := hB; topDifferentialCoefficient k R K n b ω) := by
  subst B
  rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- Here the scalar action is the action of the actual chart map to the
function field. Its agreement with the Laurent action is proved by the
chart/torus coordinate compatibility, rather than inferred by definitional
conversion between the two module structures. -/
local instance chartGenericFunctionFieldSMul (s : «Σ».ConeIndex) :
    SMul (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  («Σ».chartFunctionFieldAlgebra k s).toSMul

local instance chartGenericFunctionFieldModule (s : «Σ».ConeIndex) :
    Module (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  @Algebra.toModule _ _ _ _ («Σ».chartFunctionFieldAlgebra k s)

local instance chartGenericFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap k («Σ».fanScheme k).functionField r=
    «Σ».chartRationalMap k s (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) r)
  exact (IsScalarTower.algebraMap_apply k (AddMonoidAlgebra k (Lattice n))
    («Σ».fanScheme k).functionField r).trans
      («Σ».chartRationalMap_eq_torusRationalMap k s
        (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) r)).symm

def chartFaceAlgebra {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    Algebra (monoidChartAlgebra k (dualConeMonoid s))
      (monoidChartAlgebra k (dualConeMonoid t)) :=
  (monoidChartInclusion k (dualConeMonoid_antitone hts)).toRingHom.toAlgebra

def chartFace_scalarTower {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    letI := chartFaceAlgebra k hts
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s))
      (monoidChartAlgebra k (dualConeMonoid t)) := by
  letI := chartFaceAlgebra k hts
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((monoidChartInclusion k (dualConeMonoid_antitone hts)).commutes r).symm

def chartFaceFunctionField_scalarTower {s t : «Σ».ConeIndex} (hts : t.val ⊆ s.val) :
    letI := chartFaceAlgebra k hts
    IsScalarTower (monoidChartAlgebra k (dualConeMonoid s.val))
      (monoidChartAlgebra k (dualConeMonoid t.val)) («Σ».fanScheme k).functionField := by
  letI := chartFaceAlgebra k hts
  exact IsScalarTower.of_algebraMap_eq fun r =>
    («Σ».chartRationalMap_restrict k (s := t) (t := s) hts r).symm

theorem chartFunctionField_isFractionRing (s : «Σ».ConeIndex) :
    IsFractionRing (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  letI : IsOpenImmersion («Σ».fanChartMap k s) := «Σ».fanChartMap_isOpenImmersion k s
  exact affineOpenCoordinate_isFractionRing
    (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))
    («Σ».fanChartMap k s)

theorem exists_chartDifferentialBasis (hpure : «Σ».IsPure) (s : «Σ».ConeIndex) :
    Nonempty (Module.Basis (Fin n) (monoidChartAlgebra k (dualConeMonoid s.val))
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) := by
  obtain ⟨t, ht, hst, hcard⟩ := hpure s.val s.property
  let t' : «Σ».fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k t s.val ht hst
  letI : Algebra (monoidChartAlgebra k (dualConeMonoid t))
      (monoidChartAlgebra k (dualConeMonoid s.val)) := chartFaceAlgebra k hst
  letI : IsScalarTower k (monoidChartAlgebra k (dualConeMonoid t))
      (monoidChartAlgebra k (dualConeMonoid s.val)) := chartFace_scalarTower k hst
  letI : IsLocalization (Submonoid.powers (chartCharacter k _ v hv))
      (monoidChartAlgebra k (dualConeMonoid s.val)) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact ⟨localizedDifferentialBasis k _ _
    (Submonoid.powers (chartCharacter k _ v hv))
    («Σ».actualFullChartDifferentialBasis k t')⟩

theorem chartTopDifferentialMap_injective (hpure : «Σ».IsPure) (s : «Σ».ConeIndex) :
    Function.Injective (topDifferentialMap k
      (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField n) := by
  letI := «Σ».chartFunctionField_isFractionRing k s
  obtain ⟨b⟩ := «Σ».exists_chartDifferentialBasis k hpure s
  exact topDifferentialMap_injective_of_localization k _ _
    (nonZeroDivisors (monoidChartAlgebra k (dualConeMonoid s.val))) b
    («Σ».chartRationalMap_injective k s)

/-- The coefficient of a genuine top differential on any actual chart. -/
def chartGenericTopCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».ConeIndex) :
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) →ₗ[
        monoidChartAlgebra k (dualConeMonoid s.val)] («Σ».fanScheme k).functionField :=
  topDifferentialCoefficient k (monoidChartAlgebra k (dualConeMonoid s.val))
    («Σ».fanScheme k).functionField n («Σ».genericLogDifferentialBasis k b₀)

theorem chartGenericTopCoefficient_injective (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».ConeIndex) :
    Function.Injective («Σ».chartGenericTopCoefficient k b₀ s) :=
  (basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀)).injective.comp
    («Σ».chartTopDifferentialMap_injective k hpure s)

theorem chartGenericTopCoefficient_restrict
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) {s t : «Σ».ConeIndex}
    (hts : t.val ⊆ s.val)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    letI := chartFaceAlgebra k hts
    letI := chartFace_scalarTower k hts
    «Σ».chartGenericTopCoefficient k b₀ t
        (topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid s.val))
          (monoidChartAlgebra k (dualConeMonoid t.val)) n ω) =
      «Σ».chartGenericTopCoefficient k b₀ s ω := by
  letI := chartFaceAlgebra k hts
  letI := chartFace_scalarTower k hts
  letI := «Σ».chartFaceFunctionField_scalarTower k hts
  exact congrArg (fun f =>
    basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) (f ω))
      (topDifferentialMap_comp k
        (monoidChartAlgebra k (dualConeMonoid s.val))
        (monoidChartAlgebra k (dualConeMonoid t.val)) («Σ».fanScheme k).functionField n)

set_option maxHeartbeats 2000000 in
/-- On a full chart this is the already constructed actual differential
coefficient. The explicit chart scalar action changes no generic form. -/
theorem chartGenericTopCoefficient_fullCone
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    «Σ».chartGenericTopCoefficient k b₀ («Σ».fullConeIndex s) ω=
      «Σ».actualChartTopCoefficient k b₀ s ω := by
  let R := monoidChartAlgebra k (dualConeMonoid s.val)
  let K := («Σ».fanScheme k).functionField
  let A : Algebra R K := «Σ».chartFunctionFieldAlgebra k («Σ».fullConeIndex s)
  let B : Algebra R K := (monoidChartAlgebra k (dualConeMonoid s.val)).toAlgebra
  have hAB : A=B := Algebra.algebra_ext A B fun r =>
    «Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) r
  exact topDifferentialCoefficient_algebra_eq k R K A B hAB
    («Σ».chartGenericFunctionField_scalarTower k («Σ».fullConeIndex s))
    (by
      letI : Algebra R K := B
      exact IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := K) fun r =>
        IsScalarTower.algebraMap_apply k (AddMonoidAlgebra k (Lattice n)) K r)
    n («Σ».genericLogDifferentialBasis k b₀) ω

/-- The actual localized differential forms agree on the actual common
face precisely when they give the same generic form. Thus the computed
volume transition is the natural differential transition, not an
independently prescribed line-bundle cocycle. -/
theorem fullChart_differentials_agree_on_overlap_iff (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s t : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k])
    (η : ⋀[monoidChartAlgebra k (dualConeMonoid t.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid t.val)⁄k]) :
    let l : «Σ».ConeIndex :=
      ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
    letI := chartFaceAlgebra k (Finset.inter_subset_left : l.val ⊆ s.val)
    letI := chartFaceAlgebra k (Finset.inter_subset_right : l.val ⊆ t.val)
    letI := chartFace_scalarTower k (Finset.inter_subset_left : l.val ⊆ s.val)
    letI := chartFace_scalarTower k (Finset.inter_subset_right : l.val ⊆ t.val)
    topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid s.val))
        (monoidChartAlgebra k (dualConeMonoid l.val)) n ω =
      topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid t.val))
        (monoidChartAlgebra k (dualConeMonoid l.val)) n η ↔
      «Σ».actualChartTopCoefficient k b₀ s ω = «Σ».actualChartTopCoefficient k b₀ t η := by
  dsimp only
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
  letI := chartFaceAlgebra k (Finset.inter_subset_left : l.val ⊆ s.val)
  letI := chartFaceAlgebra k (Finset.inter_subset_right : l.val ⊆ t.val)
  letI := chartFace_scalarTower k (Finset.inter_subset_left : l.val ⊆ s.val)
  letI := chartFace_scalarTower k (Finset.inter_subset_right : l.val ⊆ t.val)
  have hω := («Σ».chartGenericTopCoefficient_restrict k b₀
    (s := «Σ».fullConeIndex s) (t := l)
    (Finset.inter_subset_left : l.val ⊆ s.val) ω).trans
      («Σ».chartGenericTopCoefficient_fullCone k b₀ s ω)
  have hη := («Σ».chartGenericTopCoefficient_restrict k b₀
    (s := «Σ».fullConeIndex t) (t := l)
    (Finset.inter_subset_right : l.val ⊆ t.val) η).trans
      («Σ».chartGenericTopCoefficient_fullCone k b₀ t η)
  exact («Σ».chartGenericTopCoefficient_injective k hpure b₀ l).eq_iff.symm.trans
    (congrArg₂ (fun x y : («Σ».fanScheme k).functionField => x=y) hω hη).to_iff

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fullChart_differentials_agree_on_overlap_iff

end Source_ToricDifferentialOverlaps

section Source_ToricRationalFrameComparison

/-!
# Comparing an actual locally free sheaf with prescribed rational Cartier frames

The input is a genuine map of module sheaves into rational functions and
actual local frames on the given Cartier cover. Its value on each frame is
the specified nonzero rational generator. These equalities prove that the
map is injective, identify all local fractional modules, and hence give an
actual isomorphism with the Cartier sheaf, preserving rational values.

In particular, neither injectivity nor the desired Cartier identification
is assumed as part of the comparison data.
-/


universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X]
    (C : RationalCartierCocycle X) (M : X.Modules)
    (v : M ⟶ rationalFunctions X)
    (e : ∀ i, ModuleFrame M (C.openSet i))

/-- Equality of the genuine rational values of the actual local frames.
Empty members of the cover impose no condition. -/
def FrameValues : Prop :=
  ∀ (i : C.index) [Nonempty (C.openSet i)],
    rationalValue X (C.openSet i)
      (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) =
        (C.generator i : X.functionField)

theorem frameValues_restrict (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V] (hi : V≤C.openSet i) :
    rationalValue X V (v.app V ((e i).generator V hi)) =
      (C.generator i : X.functionField) := by
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.arbitrary V).val,hi (Classical.arbitrary V).property⟩⟩
  have hn := PresheafOfModules.naturality_apply v.val (homOfLE hi).op
    ((e i).generator (C.openSet i) le_rfl)
  have hgen : moduleRes M hi ((e i).generator (C.openSet i) le_rfl) =
      (e i).generator V hi := (e i).generator_res le_rfl hi
  change v.app V (moduleRes M hi ((e i).generator (C.openSet i) le_rfl)) =
    moduleRes (rationalFunctions X) hi
      (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) at hn
  have hn' : v.app V ((e i).generator V hi) =
      moduleRes (rationalFunctions X) hi
        (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) :=
    (congrArg (v.app V) hgen.symm).trans hn
  rw [hn',rationalValue_restrict]
  exact hv i

theorem frameValues_section (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V]
    (hi : V≤C.openSet i) (s : Γ(M,V)) :
    rationalValue X V (v.app V s) =
      X.germToFunctionField V ((e i).coordinates V hi s) *
        (C.generator i : X.functionField) := by
  conv_lhs => rw [(e i).section_eq V hi s]
  rw [Scheme.Modules.Hom.app_smul,rationalValue_smul,
    C.frameValues_restrict M v e hv i V hi]

/-- Nonzero rational frame values imply local injectivity; it is not an
extra assumption on the sheaf map. -/
theorem frameValues_injective_on (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V]
    (hi : V≤C.openSet i) : Function.Injective (v.app V) := by
  intro s t h
  apply ((e i).coordinates V hi).injective
  apply X.germToFunctionField_injective V
  apply mul_right_cancel₀ (Units.ne_zero (C.generator i))
  rw [← C.frameValues_section M v e hv i V hi s,
    ← C.frameValues_section M v e hv i V hi t,h]

/-- Local injectivity on the actual cover gives injectivity on every
open, including the empty open. -/
theorem frameValues_injective (hv : C.FrameValues M v e)
    (W : X.Opens) : Function.Injective (v.app W) := by
  intro s t h
  apply module_sections_ext_cover M C.openSet C.covers W s t
  intro i
  by_cases hV : Nonempty (W⊓C.openSet i : X.Opens)
  · letI := hV
    apply C.frameValues_injective_on M v e hv i (W⊓C.openSet i) inf_le_right
    have hs := PresheafOfModules.naturality_apply v.val
      (homOfLE (show W⊓C.openSet i≤W from inf_le_left)).op s
    have ht := PresheafOfModules.naturality_apply v.val
      (homOfLE (show W⊓C.openSet i≤W from inf_le_left)).op t
    calc
      v.app (W⊓C.openSet i) (moduleRes M inf_le_left s) =
          moduleRes (rationalFunctions X) inf_le_left (v.app W s) := hs
      _ = moduleRes (rationalFunctions X) inf_le_left (v.app W t) := by rw [h]
      _ = v.app (W⊓C.openSet i) (moduleRes M inf_le_left t) := ht.symm
  · have hbot : W⊓C.openSet i=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M (W⊓C.openSet i) hbot
    exact Subsingleton.elim _ _

/-- The actual sheaf with its proved rational embedding, retaining its
underlying module sheaf literally. -/
def cartierDataOfFrames (hv : C.FrameValues M v e) : CartierData X where
  sheaf := M
  inclusion := v
  inclusion_injective := C.frameValues_injective M v e hv
  locallyFree := by
    intro x
    obtain ⟨i,hi⟩ := C.covers x
    exact ⟨C.openSet i,hi,⟨e i⟩⟩

@[simp] theorem cartierDataOfFrames_sheaf (hv : C.FrameValues M v e) :
    (C.cartierDataOfFrames M v e hv).sheaf=M := rfl

/-- The comparison preserves the actual fractional embedding. The
local ranges are both exactly the regular multiples of the same generator. -/
theorem cartierDataOfFrames_equivalent (hv : C.FrameValues M v e) :
    (C.cartierDataOfFrames M v e hv).Equivalent C.toCartierData := by
  let D := C.cartierDataOfFrames M v e hv
  apply D.equivalent_of_local_ranges C.toCartierData C.openSet C.covers
  intro i V hV hi
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.arbitrary V).val,hi (Classical.arbitrary V).property⟩⟩
  have hg : D.frameRationalGenerator (e i) =
      (C.generator i : X.functionField) := hv i
  ext r
  change r ∈ D.sectionValueRange V ↔ r ∈ C.toCartierData.sectionValueRange V
  rw [D.mem_sectionValueRange_iff (e i) hi r,
    C.mem_sectionValueRange_iff i V hi r,hg]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(eq_div_iff (Units.ne_zero (C.generator i))).mpr ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(eq_div_iff (Units.ne_zero (C.generator i))).mp ha⟩

/-- A genuine isomorphism with the Cartier sheaf associated to the
specified rational cocycle. -/
def sheafIsoOfFrames (hv : C.FrameValues M v e) : M ≅ C.sheaf :=
  (C.cartierDataOfFrames_equivalent M v e hv).choose

theorem sheafIsoOfFrames_inclusion (hv : C.FrameValues M v e) :
    (C.sheafIsoOfFrames M v e hv).hom≫C.inclusion=v :=
  (C.cartierDataOfFrames_equivalent M v e hv).choose_spec

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.frameValues_injective
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sheafIsoOfFrames

end Source_ToricRationalFrameComparison

section Source_ToricFanIntrinsicCanonical

/-!
# The intrinsic canonical sheaf of the actual fan scheme

The left-hand side below is the ordinary top exterior power of the
intrinsic Kähler sheaf. Its actual polynomial-chart frames map to the
previously computed genuine generic differential volumes. This proves
the global sheaf comparison, and only then identifies the canonical
Cartier coefficients with minus one on every ray.
-/


universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical BaseSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

local notation "X" => «Σ».fanScheme k
local notation "M" => topDifferentialSheaf k X n

def fullChartIntrinsicTopFrame (s : «Σ».fullCones) :
    topDifferentialSheaf k (coneChart k s.val) n≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  affineTopDifferentialSheafIso k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».actualFullChartDifferentialBasis k s) ≪≫
    «Σ».fullChartTopDifferentialFrame k s

def intrinsicTopChartFrame (s : «Σ».fullCones) :
    (M).restrict («Σ».fanChartMap k («Σ».fullConeIndex s))≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  topDifferentialSheafRestrictIso («Σ».fanChartMap k («Σ».fullConeIndex s)) n k ≪≫
    «Σ».fullChartIntrinsicTopFrame k s

/-- Actual local freeness on the actual image open. -/
def intrinsicTopOpenFrame (s : «Σ».fullCones) : ModuleFrame M («Σ».fullChartOpen k s) :=
  ModuleFrame.ofOpenImmersionIso («Σ».fanChartMap k («Σ».fullConeIndex s))
    («Σ».intrinsicTopChartFrame k s)

set_option maxHeartbeats 2000000 in
theorem fullChartIntrinsicTopFrame_wedge (s : «Σ».fullCones) :
    («Σ».fullChartIntrinsicTopFrame k s).hom.app ⊤
      (differentialWedgeSection (coneChart k s.val) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of
          (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
            («Σ».fullChartCoordinate k s i)))=(1 : Γ(coneChart k s.val,⊤)) := by
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
  let b := «Σ».actualFullChartDifferentialBasis k s
  have hw := affineTopDifferentialSheafIso_differentialWedge_top k R b
    («Σ».fullChartCoordinate k s)
  have hb : (fun i : Fin n => D k R («Σ».fullChartCoordinate k s i))=b := by
    funext i
    exact («Σ».actualFullChartDifferentialBasis_apply k s i).symm
  have hw' := hw.trans (congrArg
    (fun v : Fin n → KaehlerDifferential k R =>
      tilde.toOpen (R := R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n v)) hb)
  have hc : tildeTopBasisCoordinates R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n b))=(1 : Γ(Spec R,⊤)) :=
    (tildeTopBasisCoordinates_toOpen R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (exteriorPower.ιMulti R n b)).trans (by
        rw [basisTopExteriorEquiv_basis,map_one])
  exact (congrArg ((«Σ».fullChartTopDifferentialFrame k s).hom.app ⊤) hw').trans hc

/-- The chart coordinate, now as an actual regular function on the
actual image open of the chart. -/
def fullChartGlobalCoordinate (s : «Σ».fullCones) (i : Fin n) :
    Γ(X,«Σ».fullChartOpen k s) :=
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  (X).presheaf.map (eqToHom (j.image_top_eq_opensRange).symm).op
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
        («Σ».fullChartCoordinate k s i)))

theorem intrinsicTopChartFrame_inv_one (s : «Σ».fullCones) :
    («Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)) =
      ((M).restrictAppIso («Σ».fanChartMap k («Σ».fullConeIndex s)) ⊤).inv
        (differentialWedgeSection X k
          ((«Σ».fanChartMap k («Σ».fullConeIndex s)) ''ᵁ ⊤)
          (fun i=>((«Σ».fanChartMap k («Σ».fullConeIndex s)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of
              (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
                («Σ».fullChartCoordinate k s i)))) := by
  letI : IsIso ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso («Σ».intrinsicTopChartFrame k s).hom) ⊤
  apply (ConcreteCategory.bijective_of_isIso
    ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤)).injective
  have hc := congrArg (fun f=>f.app ⊤ (1 : Γ(coneChart k s.val,⊤)))
    («Σ».intrinsicTopChartFrame k s).inv_hom_id
  rw [show («Σ».intrinsicTopChartFrame k s).hom.app ⊤
      ((«Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)))=(1 : Γ(coneChart k s.val,⊤)) from by
        simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
          ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using hc]
  simp only [intrinsicTopChartFrame,Iso.trans_hom,Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply,differentialWedgeSection_openRestriction,
    Iso.inv_hom_id_apply]
  exact («Σ».fullChartIntrinsicTopFrame_wedge k s).symm

/-- The local basis of the intrinsic top sheaf is the actual wedge of
the actual affine coordinate differentials. -/
theorem intrinsicTopOpenFrame_generator (s : «Σ».fullCones) :
    («Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl=
      differentialWedgeSection X k («Σ».fullChartOpen k s)
        («Σ».fullChartGlobalCoordinate k s) := by
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  let e : (M).restrict j ≅
      SheafOfModules.unit (coneChart k («Σ».fullConeIndex s).val).ringCatSheaf :=
    «Σ».intrinsicTopChartFrame k s
  let a : Fin n → Γ(X,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) :=
    fun i => (j.appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
          («Σ».fullChartCoordinate k s i))
  let ω := differentialWedgeSection X k (j ''ᵁ ⊤) a
  have he : e.inv.app ⊤
      (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤)) =
      ((M).restrictAppIso j ⊤).inv ω :=
    «Σ».intrinsicTopChartFrame_inv_one k s
  have hv : ((M).restrictAppIso j ⊤).hom
      (e.inv.app ⊤ (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤))) = ω :=
    (congrArg ((M).restrictAppIso j ⊤).hom he).trans
      (((M).restrictAppIso j ⊤).inv_hom_id_apply ω)
  have himage : ModuleFrame.imageFrameGenerator j e =
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω :=
    congrArg (fun v : Γ(M,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) =>
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op v) hv
  have hres : (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω =
      differentialWedgeSection X k j.opensRange
        (fun i => (X).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op (a i)) :=
    differentialWedgeSection_restrict X k j.image_top_eq_opensRange.symm.le a
  exact (ModuleFrame.ofOpenImmersionIso_generator j e).trans (himage.trans hres)

theorem fullChartGlobalCoordinate_germ (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] (i : Fin n) :
    (X).germToFunctionField («Σ».fullChartOpen k s) («Σ».fullChartGlobalCoordinate k s i)=
      «Σ».chartRationalMap k («Σ».fullConeIndex s) («Σ».fullChartCoordinate k s i) := by
  let R := CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val))
  let j : coneChart k («Σ».fullConeIndex s).val ⟶ X :=
    «Σ».fanChartMap k («Σ».fullConeIndex s)
  letI : IsIntegral (coneChart k («Σ».fullConeIndex s).val) :=
    «Σ».coneChart_isIntegral k («Σ».fullConeIndex s)
  letI : IsOpenImmersion j :=
    «Σ».fanChartMap_isOpenImmersion k («Σ».fullConeIndex s)
  let a : Γ(coneChart k («Σ».fullConeIndex s).val,⊤) :=
    (Scheme.ΓSpecIso R).inv («Σ».fullChartCoordinate k s i)
  let U : (X).Opens := j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)
  letI : Nonempty U := by
    rw [show U=«Σ».fullChartOpen k s from j.image_top_eq_opensRange]
    infer_instance
  let b : Γ(X,U) := (j.appIso ⊤).inv a
  let f : «Σ».fullChartOpen k s ⟶ U :=
    eqToHom (j.image_top_eq_opensRange).symm
  change (X).germToFunctionField («Σ».fullChartOpen k s)
    ((X).presheaf.map f.op b) = _
  calc
    _ = (X).germToFunctionField U b :=
      germToFunctionField_restrict X f b
    _ = openImmersionRegularToFunctionField j ⊤ a :=
      (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm
    _ = _ := rfl


/-- The generic coefficient of the intrinsic local basis is exactly
the coefficient already obtained from actual chart Kähler modules. -/
theorem intrinsicTopOpenFrame_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] :
    rationalValue X («Σ».fullChartOpen k s)
      ((topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀)).app
        («Σ».fullChartOpen k s)
          ((«Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl))=
      («Σ».differentialVolumeUnit k b₀ s : (X).functionField) := by
  rw [«Σ».intrinsicTopOpenFrame_generator,
    topDifferentialRationalMap_differentialWedge]
  simp_rw [«Σ».fullChartGlobalCoordinate_germ]
  change _=«Σ».actualChartTopCoefficient k b₀ s
    (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s))
  unfold actualChartTopCoefficient
  rw [LinearMap.comp_apply,exteriorScalarExtensionMap_wedge]
  change basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _ =
    basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _
  apply congrArg (fun ω :
    ⋀[(«Σ».fanScheme k).functionField]^n
      (KaehlerDifferential k («Σ».fanScheme k).functionField) =>
        basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) ω)
  apply congrArg (fun v : Fin n → KaehlerDifferential k («Σ».fanScheme k).functionField =>
    exteriorPower.ιMulti («Σ».fanScheme k).functionField n v)
  funext i
  rw [«Σ».actualFullChartDifferentialBasis_apply,KaehlerDifferential.map_D]
  exact congrArg (D k («Σ».fanScheme k).functionField)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s)
      («Σ».fullChartCoordinate k s i))

theorem intrinsicTopFrameValues (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeCocycle k hpure b₀).FrameValues M
      (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
      (fun s=>«Σ».intrinsicTopOpenFrame k s.down) := by
  intro s h
  letI : Nonempty («Σ».fullChartOpen k s.down) := h
  exact «Σ».intrinsicTopOpenFrame_value k b₀ s.down

/-- The genuine intrinsic canonical sheaf is the fractional sheaf
obtained from its genuine generic differential volume. -/
def intrinsicTopDifferentialVolumeIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».differentialVolumeData k hpure b₀).sheaf :=
  («Σ».differentialVolumeCocycle k hpure b₀).sheafIsoOfFrames M
    (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
    (fun s=>«Σ».intrinsicTopOpenFrame k s.down)
    («Σ».intrinsicTopFrameValues k hpure b₀)

/-- The minus-one ray coefficients are a consequence of the actual
Kähler/top-exterior computation, not the definition of the canonical sheaf. -/
def intrinsicCanonicalFanIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».fanCartierData k hpure (fun _=>-1)).sheaf :=
  «Σ».intrinsicTopDifferentialVolumeIso k hpure b₀ ≪≫
    («Σ».differentialVolumeData_equivalent_canonical k hpure b₀).choose

theorem intrinsicTopDifferential_isInvertible (hpure : «Σ».IsPure) :
    IsInvertibleModule (topDifferentialSheaf k («Σ».fanScheme k) n) := by
  intro x
  obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure x
  exact ⟨«Σ».fullChartOpen k s,hs,⟨«Σ».intrinsicTopOpenFrame k s⟩⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicTopDifferentialVolumeIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicCanonicalFanIso

end Source_ToricFanIntrinsicCanonical

#eval "RECOVERED_INTRINSIC_CANONICAL_END"
