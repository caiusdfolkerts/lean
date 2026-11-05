module

public import PaperVerification.FermionSuperContraction
public import PaperVerification.FermionHomogenizedFamily

/-!
# The actual paired extension of the strict moment algebra

Put s = 1, a = phi, and b = 1 in the paired family.  Adding its missing
zeroth xi moment gives exactly the strict ideal.  Total xi contraction
preserves the paired ideal: its four generator images are respectively
zero, zero, the ordinary moment, and minus the theta moment.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

def StrictData.pairedExtension (d : StrictData (K := R) (n := n)) :
    PairedData (K := R) (n := n) where
  positive_n := d.positive_n
  s := 1
  positive_s := Nat.zero_lt_one
  r := d.r
  u := d.r
  v := fun _ ↦ 0
  positive_r := d.positive_r
  degree_split := fun _ ↦ by simp only [add_zero,mul_one]
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := d.phi
  a := d.phi
  b := fun _ ↦ 1
  highest_phi := d.highest_phi
  highest_a := d.highest_phi
  highest_b := fun i ↦ by
    simpa only [pow_zero] using highestPower_X_pow d.r i 0

def StrictData.power (d : StrictData (K := R) (n := n)) :
    StrictData (K := R) (n := n) where
  positive_n := d.positive_n
  r := d.r
  positive_r := d.positive_r
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := fun i ↦ X i^d.r i
  highest_phi := fun i ↦ highestPower_X_pow d.r i (d.r i)

abbrev strictExtensionIdeal (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :=
  pairedIdeal β φ φ (fun _ ↦ 1)

abbrev StrictExtensionQuotient (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :=
  PairedQuotient β φ φ (fun _ ↦ 1)

def strictExtensionMoment (β : Fin n → R) (φ : Fin n → PolynomialRing R n)
    (j : MomentKind) (k : ℕ) : SuperRing R n :=
  moment φ (pairedCoefficients β φ (fun _ ↦ 1) j) k

@[simp] theorem strictExtensionMoment_polynomial (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (k : ℕ) :
    strictExtensionMoment β φ .polynomial k = moment φ (strictCoefficients β φ .polynomial) k := by
  simp only [strictExtensionMoment,moment,pairedCoefficients,strictCoefficients,mul_one]

@[simp] theorem strictExtensionMoment_theta (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (k : ℕ) :
    strictExtensionMoment β φ .theta k = moment φ (strictCoefficients β φ .theta) k := by
  simp only [strictExtensionMoment,moment,pairedCoefficients,strictCoefficients,one_smul]

@[simp] theorem strictExtensionMoment_xi (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (k : ℕ) :
    strictExtensionMoment β φ .xi k = moment φ (strictCoefficients β φ .xi) (k+1) := by
  simp only [strictExtensionMoment,moment,pairedCoefficients,strictCoefficients,smul_smul,pow_succ]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

@[simp] theorem strictExtensionMoment_mixed (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (k : ℕ) :
    strictExtensionMoment β φ .mixed k = moment φ (strictCoefficients β φ .mixed) k := rfl

def strictZerothXi (β : Fin n → R) : SuperRing R n := superOdd (strictXiVector β)

theorem strictXiVector_eq_sum (β : Fin n → R) :
    strictXiVector β = ∑ i,β i • Pi.single (Sum.inr i) 1 := by
  ext j
  cases j with
  | inl j => simp [strictXiVector,Pi.single_apply]
  | inr j => simp [strictXiVector,Pi.single_apply,eq_comm]

theorem strictZerothXi_eq_sum (β : Fin n → R) :
    strictZerothXi β = ∑ i,β i • xi R n i := by
  rw [strictZerothXi,strictXiVector_eq_sum]
  simp only [superOdd,map_sum,map_smul,xi]

theorem strictZerothXi_eq_moment (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) :
    strictZerothXi β=moment φ (strictCoefficients β φ .xi) 0 := by
  rw [strictZerothXi_eq_sum]
  simp only [moment,pow_zero,one_smul,strictCoefficients]
  apply Finset.sum_congr rfl
  intro i hi
  exact (IsScalarTower.algebraMap_smul (PolynomialRing R n) (β i) (xi R n i)).symm

theorem strictExtensionMoment_mem (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (j : MomentKind) (k : ℕ) :
    strictExtensionMoment β φ j k ∈ strictExtensionIdeal β φ :=
  TwoSidedIdeal.subset_span ⟨(j,k),rfl⟩

theorem strictExtensionIdeal_le (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    strictExtensionIdeal β φ ≤ strictIdeal β φ := by
  apply TwoSidedIdeal.span_le.mpr
  rintro x ⟨⟨j,k⟩,rfl⟩
  change strictExtensionMoment β φ j k ∈ strictIdeal β φ
  cases j with
  | polynomial => rw [strictExtensionMoment_polynomial]; exact TwoSidedIdeal.subset_span ⟨(.polynomial,k),rfl⟩
  | theta => rw [strictExtensionMoment_theta]; exact TwoSidedIdeal.subset_span ⟨(.theta,k),rfl⟩
  | xi => rw [strictExtensionMoment_xi]; exact TwoSidedIdeal.subset_span ⟨(.xi,k+1),rfl⟩
  | mixed => rw [strictExtensionMoment_mixed]; exact TwoSidedIdeal.subset_span ⟨(.mixed,k),rfl⟩

/-- The literal strict ideal differs by exactly one actual exterior linear
relation.  All four infinite moment families occur on both sides. -/
theorem strictIdeal_eq_extension_sup (β : Fin n → R) (φ : Fin n → PolynomialRing R n) :
    strictIdeal β φ = strictExtensionIdeal β φ ⊔
      TwoSidedIdeal.span ({strictZerothXi β} : Set (SuperRing R n)) := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨j,k⟩,rfl⟩
    change moment φ (strictCoefficients β φ j) k ∈
      strictExtensionIdeal β φ ⊔ TwoSidedIdeal.span ({strictZerothXi β} : Set (SuperRing R n))
    cases j with
    | polynomial =>
        rw [←strictExtensionMoment_polynomial]
        exact TwoSidedIdeal.mem_sup_left (strictExtensionMoment_mem β φ .polynomial k)
    | theta =>
        rw [←strictExtensionMoment_theta]
        exact TwoSidedIdeal.mem_sup_left (strictExtensionMoment_mem β φ .theta k)
    | mixed =>
        rw [←strictExtensionMoment_mixed]
        exact TwoSidedIdeal.mem_sup_left (strictExtensionMoment_mem β φ .mixed k)
    | xi =>
        cases k with
        | zero =>
            rw [←strictZerothXi_eq_moment]
            exact TwoSidedIdeal.mem_sup_right (TwoSidedIdeal.subset_span (Set.mem_singleton _))
        | succ k =>
            rw [←strictExtensionMoment_xi]
            exact TwoSidedIdeal.mem_sup_left (strictExtensionMoment_mem β φ .xi k)
  · refine sup_le (strictExtensionIdeal_le β φ) (TwoSidedIdeal.span_le.mpr ?_)
    rintro x (rfl : x=strictZerothXi β)
    rw [strictZerothXi_eq_moment β φ]
    exact TwoSidedIdeal.subset_span ⟨(.xi,0),rfl⟩

theorem superContraction_moment (l : Module.Dual R (OddModule R n))
    (φ : Fin n → PolynomialRing R n) (v : Fin n → SuperRing R n) (k : ℕ) :
    superContraction l (moment φ v k)=moment φ (fun i ↦ superContraction l (v i)) k := by
  simp only [moment,map_sum,superContraction_polynomial_smul]

theorem superParity_moment (φ : Fin n → PolynomialRing R n)
    (v : Fin n → SuperRing R n) (k : ℕ) :
    superParity (moment φ v k)=moment φ (fun i ↦ superParity (v i)) k := by
  simp only [moment,map_sum,superParity_polynomial_smul]

theorem strictExtensionMoment_parity (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (j : MomentKind) (k : ℕ) :
    superParity (strictExtensionMoment β φ j k) =
      match j with
      | .polynomial | .mixed => strictExtensionMoment β φ j k
      | .theta | .xi => -strictExtensionMoment β φ j k := by
  cases j <;>
    simp only [strictExtensionMoment, moment, map_sum, pairedCoefficients,
      superParity_polynomial_smul,map_one,map_mul,superParity_theta,superParity_xi,
      neg_mul_neg,smul_neg,Finset.sum_neg_distrib]
  all_goals
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact neg_mul_neg (theta R n i) (xi R n i)

theorem strictExtensionMoment_contraction (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (j : MomentKind) (k : ℕ) :
    superContraction strictXiFunctional (strictExtensionMoment β φ j k) =
      match j with
      | .polynomial | .theta => 0
      | .xi => strictExtensionMoment β φ .polynomial k
      | .mixed => -strictExtensionMoment β φ .theta k := by
  cases j <;>
    simp only [strictExtensionMoment,moment,map_sum,pairedCoefficients,
      superContraction_polynomial_smul,superContraction_one,strictXiContraction_theta,
      strictXiContraction_xi,superContraction_mul,superParity_theta,
      smul_zero,Finset.sum_const_zero,mul_one,zero_mul,zero_add,one_smul,
      smul_neg,Finset.sum_neg_distrib]

theorem strictExtensionIdeal_parity_stable (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) :
    ∀ x ∈ strictExtensionIdeal β φ,superParity x ∈ strictExtensionIdeal β φ := by
  apply parity_span_stable
  rintro x ⟨⟨j,k⟩,rfl⟩
  change superParity (strictExtensionMoment β φ j k) ∈ strictExtensionIdeal β φ
  rw [strictExtensionMoment_parity]
  cases j
  · exact strictExtensionMoment_mem β φ _ k
  · exact TwoSidedIdeal.neg_mem _ (strictExtensionMoment_mem β φ _ k)
  · exact TwoSidedIdeal.neg_mem _ (strictExtensionMoment_mem β φ _ k)
  · exact strictExtensionMoment_mem β φ _ k

/-- Total xi contraction preserves the complete paired ideal, including
all left and right multiples of the moment generators. -/
theorem strictExtensionIdeal_contraction_stable (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) :
    ∀ x ∈ strictExtensionIdeal β φ,
      superContraction strictXiFunctional x ∈ strictExtensionIdeal β φ := by
  apply twistedDerivation_span_stable superParity (superContraction strictXiFunctional)
    (superContraction_mul strictXiFunctional)
    (Set.range (fun p : MomentKind × ℕ ↦ strictExtensionMoment β φ p.1 p.2))
  · intro x hx
    exact strictExtensionIdeal_parity_stable β φ x (TwoSidedIdeal.subset_span hx)
  · rintro x ⟨⟨j,k⟩,rfl⟩
    change superContraction strictXiFunctional (strictExtensionMoment β φ j k) ∈
      strictExtensionIdeal β φ
    rw [strictExtensionMoment_contraction]
    cases j
    · exact TwoSidedIdeal.zero_mem _
    · exact TwoSidedIdeal.zero_mem _
    · exact strictExtensionMoment_mem β φ .polynomial k
    · exact TwoSidedIdeal.neg_mem _ (strictExtensionMoment_mem β φ .theta k)

end PaperVerification.Fermion
