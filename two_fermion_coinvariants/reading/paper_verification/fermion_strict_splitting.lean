module

public import PaperVerification.FermionStrictExtension
public import PaperVerification.FermionPairedRank

/-!
# The literal strict quotient splits off one exterior factor

The quotient map from the actual paired extension has kernel equal to the
image of multiplication by the missing zeroth xi relation.  Normalized total
xi contraction descends through the actual ideal and anticommutes with this
creation operator to the identity.  The resulting two-copy module equivalence
gives the precise field dimension, without assuming a strict basis.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

def strictExtensionProjection (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    SuperRing R n →ₗ[R] StrictExtensionQuotient β φ :=
  ((strictExtensionIdeal β φ).ringCon.mkₐ R).toLinearMap

def strictProjection (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    SuperRing R n →ₗ[R] StrictQuotient β φ :=
  ((strictIdeal β φ).ringCon.mkₐ R).toLinearMap

def strictExtensionToStrict (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    StrictExtensionQuotient β φ →ₗ[R] StrictQuotient β φ :=
  (strictExtensionProjection β φ).liftOfSurjective
    ((strictExtensionIdeal β φ).ringCon.mkₐ_surjective (α := R))
    ⟨strictProjection β φ,by
      rw [strictProjection,strictExtensionProjection,
        quotient_kernel_eq_twoSidedIdealSubmodule,quotient_kernel_eq_twoSidedIdealSubmodule]
      exact strictExtensionIdeal_le β φ⟩

@[simp] theorem strictExtensionToStrict_apply (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (x : SuperRing R n) :
    strictExtensionToStrict β φ (strictExtensionProjection β φ x)=strictProjection β φ x :=
  LinearMap.equivOfSurjective_apply _ _

theorem strictExtensionToStrict_surjective (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) : Function.Surjective (strictExtensionToStrict β φ) := by
  intro y
  obtain ⟨x,rfl⟩ := (strictIdeal β φ).ringCon.mkₐ_surjective (α := R) y
  exact ⟨strictExtensionProjection β φ x,strictExtensionToStrict_apply β φ x⟩

def strictWeightUnit (d : StrictData (K := R) (n := n)) : Rˣ :=
  (show IsUnit (∑ i,d.beta i) from by
    exact d.allowed_weights.2 Finset.univ
      ⟨⟨0,d.positive_n⟩,Finset.mem_univ _⟩).unit

@[simp] theorem strictWeightUnit_val (d : StrictData (K := R) (n := n)) :
    (strictWeightUnit d : R)=∑ i,d.beta i := IsUnit.unit_spec _

def strictAmbientCreation (β : Fin n → R) : Module.End R (SuperRing R n) :=
  LinearMap.mulLeft R (strictZerothXi β)

def strictAmbientContraction (d : StrictData (K := R) (n := n)) :
    Module.End R (SuperRing R n) :=
  ((↑((strictWeightUnit d)⁻¹) : R)) • superContraction strictXiFunctional

theorem strictAmbientCreation_square (β : Fin n → R) :
    strictAmbientCreation β*strictAmbientCreation β=0 := by
  apply LinearMap.ext
  intro x
  change strictZerothXi β*(strictZerothXi β*x)=0
  rw [←mul_assoc,strictZerothXi,superOdd_sq,zero_mul]

theorem strictAmbientContraction_square (d : StrictData (K := R) (n := n)) :
    strictAmbientContraction d*strictAmbientContraction d=0 := by
  apply LinearMap.ext
  intro x
  have hz := LinearMap.congr_fun (superContraction_square (strictXiFunctional (R := R) (n := n))) x
  simp only [strictAmbientContraction,Module.End.mul_apply,LinearMap.smul_apply,
    map_smul,LinearMap.zero_apply] at hz ⊢
  rw [hz,smul_zero,smul_zero]

theorem strictAmbient_anticommutator (d : StrictData (K := R) (n := n)) :
    strictAmbientContraction d*strictAmbientCreation d.beta+
      strictAmbientCreation d.beta*strictAmbientContraction d=1 := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (superContraction_creation (strictXiFunctional (R := R) (n := n)) (strictXiVector d.beta)) x
  change superContraction strictXiFunctional (strictZerothXi d.beta*x)+
    strictZerothXi d.beta*superContraction strictXiFunctional x=(∑ i,d.beta i) • x at h
  change (↑((strictWeightUnit d)⁻¹) : R) •
      superContraction strictXiFunctional (strictZerothXi d.beta*x)+
    strictZerothXi d.beta*((↑((strictWeightUnit d)⁻¹) : R) •
      superContraction strictXiFunctional x)=x
  rw [mul_smul_comm,←smul_add,h,smul_smul,←strictWeightUnit_val d,
    Units.inv_mul,one_smul]

theorem strictAmbientCreation_stable (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) :
    ∀ x ∈ (strictExtensionProjection β φ).ker,
      strictAmbientCreation β x ∈ (strictExtensionProjection β φ).ker := by
  rw [strictExtensionProjection,quotient_kernel_eq_twoSidedIdealSubmodule]
  intro x hx
  exact (strictExtensionIdeal β φ).mul_mem_left _ _ hx

theorem strictAmbientContraction_stable (d : StrictData (K := R) (n := n)) :
    ∀ x ∈ (strictExtensionProjection d.beta d.phi).ker,
      strictAmbientContraction d x ∈ (strictExtensionProjection d.beta d.phi).ker := by
  rw [strictExtensionProjection,quotient_kernel_eq_twoSidedIdealSubmodule]
  intro x hx
  exact (twoSidedIdealSubmodule (K := R) (strictExtensionIdeal d.beta d.phi)).smul_mem _
    (strictExtensionIdeal_contraction_stable d.beta d.phi x hx)

def strictCreation (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    Module.End R (StrictExtensionQuotient β φ) :=
  descendEnd (strictExtensionProjection β φ) ((strictExtensionIdeal β φ).ringCon.mkₐ_surjective (α := R))
    (strictAmbientCreation β) (strictAmbientCreation_stable β φ)

def strictContraction (d : StrictData (K := R) (n := n)) :
    Module.End R (StrictExtensionQuotient d.beta d.phi) :=
  descendEnd (strictExtensionProjection d.beta d.phi)
    ((strictExtensionIdeal d.beta d.phi).ringCon.mkₐ_surjective (α := R))
    (strictAmbientContraction d) (strictAmbientContraction_stable d)

@[simp] theorem strictCreation_apply (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (x : SuperRing R n) :
    strictCreation β φ (strictExtensionProjection β φ x)=
      strictExtensionProjection β φ (strictZerothXi β*x) :=
  descendEnd_apply _ _ _ _ _

theorem strictCreation_square (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    strictCreation β φ*strictCreation β φ=0 :=
  descendEnd_square _ _ _ _ (strictAmbientCreation_square β)

theorem strictContraction_square (d : StrictData (K := R) (n := n)) :
    strictContraction d*strictContraction d=0 :=
  descendEnd_square _ _ _ _ (strictAmbientContraction_square d)

theorem strict_anticommutator (d : StrictData (K := R) (n := n)) :
    strictContraction d*strictCreation d.beta d.phi+
      strictCreation d.beta d.phi*strictContraction d=1 :=
  descendEnd_anticommutator _ _ _ _ _ _ (strictAmbient_anticommutator d)

/-- The quotient kernel is proved from the actual ideal equality and odd
normality, not supplied as an assumption to the splitting theorem. -/
theorem strictExtensionToStrict_kernel (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) :
    (strictExtensionToStrict β φ).ker=(strictCreation β φ).range := by
  ext y
  obtain ⟨x,rfl⟩ := (strictExtensionIdeal β φ).ringCon.mkₐ_surjective (α := R) y
  constructor
  · intro hx
    have hx' : x ∈ strictIdeal β φ := by
      have hx0 : strictExtensionToStrict β φ (strictExtensionProjection β φ x) = 0 := hx
      rw [strictExtensionToStrict_apply] at hx0
      apply (strictIdeal β φ).ringCon.eq.mp
      exact hx0
    rw [strictIdeal_eq_extension_sup] at hx'
    obtain ⟨a,ha,b,hb,hab⟩ := TwoSidedIdeal.mem_sup.mp hx'
    have hb' : b ∈ (LinearMap.mulLeft R (strictZerothXi β)).range := by
      have hn : ∀ z : SuperRing R n, z * strictZerothXi β =
          strictZerothXi β * superParity z := by
        intro z
        exact superOdd_normal (strictXiVector β) z
      rw [← normal_singleton_span_eq_range (R := R)
        (superParity (R := R) (n := n)) (strictZerothXi β) hn]
      exact hb
    obtain ⟨z,hz⟩ := hb'
    refine ⟨strictExtensionProjection β φ z,?_⟩
    rw [strictCreation_apply]
    change strictExtensionProjection β φ (strictZerothXi β*z)=strictExtensionProjection β φ x
    rw [show strictZerothXi β*z=b from hz,←hab,map_add]
    have ha' : strictExtensionProjection β φ a=0 :=
      (strictExtensionIdeal β φ).ringCon.eq.mpr ha
    rw [ha',zero_add]
  · rintro ⟨z,hz⟩
    obtain ⟨a,rfl⟩ := (strictExtensionIdeal β φ).ringCon.mkₐ_surjective (α := R) z
    change strictCreation β φ (strictExtensionProjection β φ a) =
      strictExtensionProjection β φ x at hz
    change strictExtensionToStrict β φ (strictExtensionProjection β φ x)=0
    rw [←hz,strictCreation_apply,strictExtensionToStrict_apply]
    change (strictIdeal β φ).ringCon.mkₐ R (strictZerothXi β*a)=0
    rw [map_mul]
    have hη : (strictIdeal β φ).ringCon.mkₐ R (strictZerothXi β)=0 := by
      apply (strictIdeal β φ).ringCon.eq.mpr
      rw [strictZerothXi_eq_moment β φ]
      exact TwoSidedIdeal.subset_span ⟨(.xi,0),rfl⟩
    rw [hη,zero_mul]

/-- A genuine module equivalence with two copies of the full strict
quotient, valid over the original arbitrary base ring. -/
def strictExtensionCopiesEquiv (d : StrictData (K := R) (n := n)) :
    StrictExtensionQuotient d.beta d.phi ≃ₗ[R]
      StrictQuotient d.beta d.phi × StrictQuotient d.beta d.phi :=
  OddSplitting.quotientCopiesEquiv (strictCreation d.beta d.phi) (strictContraction d)
    (strictCreation_square d.beta d.phi) (strictContraction_square d) (strict_anticommutator d)
    (strictExtensionToStrict d.beta d.phi) (strictExtensionToStrict_surjective d.beta d.phi)
    (strictExtensionToStrict_kernel d.beta d.phi)

theorem strictCoupled_quotient_finite (d : StrictData (K := R) (n := n)) :
    Module.Finite R (StrictQuotient d.beta d.phi) := by
  letI : Module.Finite R (StrictExtensionQuotient d.beta d.phi) := by
    exact pairedCoupled_quotient_finite d.pairedExtension
  exact Module.Finite.of_surjective (strictExtensionToStrict d.beta d.phi)
    (strictExtensionToStrict_surjective d.beta d.phi)

end PaperVerification.Fermion

namespace PaperVerification.Fermion

open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

/-- The exact dimension of the full coupled strict algebra is obtained
independently of the strict candidate monomials. -/
theorem strictCoupled_finrank (d : StrictData (K := F) (n := n)) :
    Module.finrank F (StrictQuotient d.beta d.phi)=2^(n-1)*(∏ i,d.r i)*n.factorial := by
  letI := strictCoupled_quotient_finite d
  have h := (strictExtensionCopiesEquiv d).finrank_eq
  rw [Module.finrank_prod] at h
  have hp := paired_finrank d.pairedExtension
  change Module.finrank F (StrictExtensionQuotient d.beta d.phi)=
    2^n*(∏ i,d.r i)*(1 : ℕ).ascFactorial n at hp
  rw [Nat.one_ascFactorial] at hp
  have hn : n=(n-1)+1 := by have := d.positive_n; omega
  have hpow : 2^n=2*2^(n-1) := calc
    2^n = 2^((n-1)+1) := congrArg (fun a : ℕ ↦ 2^a) hn
    _ = 2*2^(n-1) := by rw [pow_succ]; ring
  rw [hp,hpow] at h
  have he : 2*Module.finrank F (StrictQuotient d.beta d.phi)=
      2*(2^(n-1)*(∏ i,d.r i)*n.factorial) := by
    simpa only [two_mul,mul_assoc,add_mul] using h.symm
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) he

end PaperVerification.Fermion
