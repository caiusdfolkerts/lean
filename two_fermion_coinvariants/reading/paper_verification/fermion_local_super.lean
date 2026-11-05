module

public import PaperVerification.FermionLocalPrefactors
public import PaperVerification.FermionSeparatedFinite
public import PaperVerification.FermionArtinianProduct
public import PaperVerification.FermionExteriorBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Actual separated super quotient and its central local factors

The super algebra below is the paper's literal polynomial tensor exterior
algebra quotient. The ordinary coefficient action is descended from its
polynomial action and shown to be central.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators Classical

namespace PaperVerification.Fermion

theorem theta_as_tensor_generator {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    theta R n i = (1 : PolynomialRing R n) ⊗ₜ[R]
      exteriorGenerator (A := R) (Sum.inl i : OddIndex n) := by
  unfold theta exteriorGenerator
  rw [Algebra.TensorProduct.includeRight_apply]
  apply congrArg (fun m : OddModule R n ↦
    (1 : PolynomialRing R n) ⊗ₜ[R] (ExteriorAlgebra.ι R m))
  funext j
  by_cases h : j = Sum.inl i
  · subst j
    simp
  · simp [Pi.single_apply,h,Ne.symm h]

theorem xi_as_tensor_generator {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    xi R n i = (1 : PolynomialRing R n) ⊗ₜ[R]
      exteriorGenerator (A := R) (Sum.inr i : OddIndex n) := by
  unfold xi exteriorGenerator
  rw [Algebra.TensorProduct.includeRight_apply]
  apply congrArg (fun m : OddModule R n ↦
    (1 : PolynomialRing R n) ⊗ₜ[R] (ExteriorAlgebra.ι R m))
  funext j
  by_cases h : j = Sum.inr i
  · subst j
    simp
  · simp [Pi.single_apply,h,Ne.symm h]

namespace SeparatedPairedData

variable {F : Type*} [Field F] {n : ℕ}
variable (d : SeparatedPairedData F n)

def phiPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.phi i)
def aPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.a i)
def bPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.b i)

theorem polynomial_paired_product (i : Fin n) :
    d.aPolynomial i*d.bPolynomial i=Polynomial.aeval (d.phiPolynomial i) d.G := by
  rw [aPolynomial,bPolynomial,←map_mul,d.paired_product,Polynomial.aeval_comp]
  rfl

abbrev superIdeal := pairedIdeal d.beta d.phiPolynomial d.aPolynomial d.bPolynomial

/-- The literal paired moment quotient. Keeping this as a named definition
retains the data parameter when Lean infers its descended coefficient action. -/
def SuperQuotient := PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial

instance superQuotientRing : Ring d.SuperQuotient :=
  inferInstanceAs (Ring (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))

instance superQuotientFieldAlgebra : Algebra F d.SuperQuotient :=
  inferInstanceAs (Algebra F (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))

@[reducible] instance superQuotientFieldModule : Module F d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.superQuotientFieldAlgebra

def superMk : SuperRing F n →ₐ[F] d.SuperQuotient := d.superIdeal.ringCon.mkₐ F

theorem ordinary_scalar_mem (k : ℕ) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n)
      (moment d.phiPolynomial
        (fun i ↦ MvPolynomial.C (d.beta i)*Polynomial.aeval (d.phiPolynomial i) d.G) k)
        ∈d.superIdeal := by
  rw [includeLeft_scalar_moment]
  have hcoef : (fun i ↦
      (MvPolynomial.C (d.beta i)*Polynomial.aeval (d.phiPolynomial i) d.G) •
        (1 : SuperRing F n)) =
      pairedCoefficients d.beta d.aPolynomial d.bPolynomial .polynomial := by
    funext i
    simp only [pairedCoefficients,mul_assoc,d.polynomial_paired_product]
  rw [hcoef]
  exact TwoSidedIdeal.subset_span ⟨(.polynomial,k),rfl⟩

theorem ordinary_scalar_ideal_mem
    (p : PolynomialRing F n)
    (hp : p∈separatedOrdinaryIdeal d.beta d.G d.phi) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n) p
      ∈d.superIdeal := by
  have hle : separatedOrdinaryIdeal d.beta d.G d.phi ≤
      (d.superIdeal.comap
        (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n).toRingHom).asIdeal := by
    apply Ideal.span_le.mpr
    rintro x ⟨k,rfl⟩
    change moment d.phiPolynomial
      (fun i ↦ MvPolynomial.C (d.beta i) * Polynomial.aeval (d.phiPolynomial i) d.G) k ∈
      (d.superIdeal.comap
        (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n).toRingHom).asIdeal
    rw [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap]
    change (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n)
      (moment d.phiPolynomial
        (fun i ↦ MvPolynomial.C (d.beta i) * Polynomial.aeval (d.phiPolynomial i) d.G) k)
      ∈ d.superIdeal
    exact d.ordinary_scalar_mem k
  simpa only [TwoSidedIdeal.mem_asIdeal, TwoSidedIdeal.mem_comap,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hle hp

def ordinaryToSuper : d.toSeparatedOrdinaryData.Ordinary →ₐ[F] d.SuperQuotient :=
  Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
    (d.superMk.comp Algebra.TensorProduct.includeLeft)
    (fun p hp ↦ quotientMk_eq_zero_of_mem (R := F) d.superIdeal _
      (d.ordinary_scalar_ideal_mem p hp))

instance polynomialSuperAlgebra : Algebra (PolynomialRing F n) d.SuperQuotient :=
  inferInstanceAs (Algebra (PolynomialRing F n) d.superIdeal.ringCon.Quotient)

/-- The module of the canonical polynomial algebra on the actual ring quotient. -/
@[reducible] instance polynomialSuperModule : Module (PolynomialRing F n) d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.polynomialSuperAlgebra

instance fieldPolynomialSuperTower :
    IsScalarTower F (PolynomialRing F n) d.SuperQuotient :=
  inferInstanceAs (IsScalarTower F (PolynomialRing F n)
    (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))

@[simp] theorem ordinaryToSuper_mk (p : PolynomialRing F n) :
    d.ordinaryToSuper (d.toSeparatedOrdinaryData.ordinaryMk p)=
      @algebraMap (PolynomialRing F n) d.SuperQuotient _ _
        (d.polynomialSuperAlgebra) p := rfl

instance ordinarySuperAlgebra : Algebra d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  d.ordinaryToSuper.toRingHom.toAlgebra' (by
    intro c x
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨a,rfl⟩ := RingCon.mkₐ_surjective (α := F) d.superIdeal.ringCon x
    change d.superMk ((Algebra.TensorProduct.includeLeft :
      PolynomialRing F n →ₐ[F] SuperRing F n) p) * d.superMk a =
      d.superMk a * d.superMk ((Algebra.TensorProduct.includeLeft :
        PolynomialRing F n →ₐ[F] SuperRing F n) p)
    rw [←map_mul,←map_mul]
    apply congrArg d.superMk
    exact Algebra.commutes p a)

/-- The module action induced by the canonical central ordinary coefficient map. -/
@[reducible] instance ordinarySuperModule : Module d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.ordinarySuperAlgebra

/-- The existing tensor-product ring, with its scalar base made explicit. -/
instance ordinarySuperTensorRing (A : Type*) [CommRing A]
    [Algebra d.toSeparatedOrdinaryData.Ordinary A] :
    Ring (A ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient) :=
  Algebra.TensorProduct.instRing (R := d.toSeparatedOrdinaryData.Ordinary)
    (A := A) (B := d.SuperQuotient)

/-- The same canonical tensor-product ring before descending the coefficient base. -/
instance polynomialSuperTensorRing (A : Type*) [CommRing A]
    [Algebra (PolynomialRing F n) A] : Ring (A ⊗[PolynomialRing F n] d.SuperQuotient) :=
  Algebra.TensorProduct.instRing (R := PolynomialRing F n) (A := A) (B := d.SuperQuotient)

/-- The canonical ring on scalar base change of the original ambient
polynomial/exterior algebra, with the polynomial scalar base explicit. -/
def polynomialAmbientTensorRing (A : Type*) [CommRing A]
    [Algebra (PolynomialRing F n) A] : Ring (A ⊗[PolynomialRing F n] SuperRing F n) :=
  Algebra.TensorProduct.instRing (R := PolynomialRing F n) (A := A) (B := SuperRing F n)

instance polynomialOrdinarySuperTower :
    IsScalarTower (PolynomialRing F n) d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := PolynomialRing F n)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient) (fun p ↦ rfl)

instance fieldOrdinarySuperTower :
    IsScalarTower F d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := F)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient)
    (fun c ↦ (d.ordinaryToSuper.commutes c).symm)

/-- A central local factor of the actual super quotient. The named carrier
retains the support point when its canonical tensor operations are inferred. -/
def LocalSuper (rho : d.toSeparatedOrdinaryData.SupportPoint) :=
  d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[d.toSeparatedOrdinaryData.Ordinary]
    d.SuperQuotient

instance localSuperRing (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Ring (d.LocalSuper rho) :=
  d.ordinarySuperTensorRing (d.toSeparatedOrdinaryData.LocalOrdinary rho)

instance localSuperLocalAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (Algebra (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

@[reducible] instance localSuperLocalModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperLocalAlgebra rho)

instance localSuperOrdinaryAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  inferInstanceAs (Algebra d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

@[reducible] instance localSuperOrdinaryModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperOrdinaryAlgebra rho)

instance localSuperFieldAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra F (d.LocalSuper rho) :=
  inferInstanceAs (Algebra F (d.toSeparatedOrdinaryData.LocalOrdinary rho
    ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

@[reducible] instance localSuperFieldModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module F (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperFieldAlgebra rho)

instance localSuperFieldOrdinaryTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower F d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower F d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

instance localSuperFieldLocalTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower F (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower F (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

instance localSuperOrdinaryLocalTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower d.toSeparatedOrdinaryData.Ordinary
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))

/-- The complete Artinian product decomposition before reindexing maximal
ideals by their support points. -/
def superProductEquiv :
    d.SuperQuotient ≃ₐ[d.toSeparatedOrdinaryData.Ordinary]
      ∀ m : MaximalSpectrum d.toSeparatedOrdinaryData.Ordinary,
        Localization.AtPrime m.asIdeal ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient :=
  centralArtinianProductEquiv d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient

/-- Quotienting the scalar base introduces no extra tensor relations after
localization: both tensor products are literally balanced over the same
surjective polynomial action. -/
def localSuperPolynomialBaseEquiv (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    d.LocalSuper rho ≃ₐ[d.toSeparatedOrdinaryData.LocalOrdinary rho]
      d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[PolynomialRing F n] d.SuperQuotient := by
  letI : TensorProduct.CompatibleSMul (PolynomialRing F n)
      d.toSeparatedOrdinaryData.Ordinary
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := PolynomialRing F n) (A := d.toSeparatedOrdinaryData.Ordinary)
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient
      (show Function.Surjective (algebraMap (PolynomialRing F n)
        d.toSeparatedOrdinaryData.Ordinary) from Ideal.Quotient.mk_surjective)
  exact Algebra.TensorProduct.equivOfCompatibleSMul (PolynomialRing F n)
    d.toSeparatedOrdinaryData.Ordinary (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient

@[simp] theorem localSuperPolynomialBaseEquiv_tmul
    (rho : d.toSeparatedOrdinaryData.SupportPoint)
    (a : d.toSeparatedOrdinaryData.LocalOrdinary rho) (q : d.SuperQuotient) :
    d.localSuperPolynomialBaseEquiv rho (a ⊗ₜ[d.toSeparatedOrdinaryData.Ordinary] q)=
      a ⊗ₜ[PolynomialRing F n] q := rfl

/-- The ambient polynomial tensor exterior algebra becomes the exterior
algebra on the same literal odd generators over the local coefficient ring. -/
def localAmbientEquiv (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n ≃ₐ[
      d.toSeparatedOrdinaryData.LocalOrdinary rho]
        ClusterExterior (d.toSeparatedOrdinaryData.LocalOrdinary rho) (Fin n) :=
  scalarExteriorBaseChange F (PolynomialRing F n)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho) (OddIndex n)

@[simp] theorem localAmbientEquiv_theta (rho : d.toSeparatedOrdinaryData.SupportPoint)
    (i : Fin n) :
    d.localAmbientEquiv rho
      (1 ⊗ₜ[PolynomialRing F n] theta F n i)=clusterTheta i := by
  rw [theta_as_tensor_generator]
  simpa only [localAmbientEquiv,clusterTheta,one_smul] using
    scalarExteriorBaseChange_generator (R := F) (P := PolynomialRing F n)
      (S := d.toSeparatedOrdinaryData.LocalOrdinary rho) (ι := OddIndex n) 1 1 (Sum.inl i)

@[simp] theorem localAmbientEquiv_xi (rho : d.toSeparatedOrdinaryData.SupportPoint)
    (i : Fin n) :
    d.localAmbientEquiv rho
      (1 ⊗ₜ[PolynomialRing F n] xi F n i)=clusterXi i := by
  rw [xi_as_tensor_generator]
  simpa only [localAmbientEquiv,clusterXi,one_smul] using
    scalarExteriorBaseChange_generator (R := F) (P := PolynomialRing F n)
      (S := d.toSeparatedOrdinaryData.LocalOrdinary rho) (ι := OddIndex n) 1 1 (Sum.inr i)

end SeparatedPairedData
end PaperVerification.Fermion

