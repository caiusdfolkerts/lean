module

public import PaperVerification.FermionPowerCover
public import PaperVerification.FermionFrobenius
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

 theorem powerCover_sum_repr (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (p : MvPolynomial (Fin n) R) :
    ∑ b : PowerResidues r, powerSubstitution r (powerCoverRepr r hr p b) *
      monomial (residuePowerExponent b) 1 = p := by
  classical
  apply (powerCoverRepr r hr).injective
  simp_rw [map_sum, powerCoverRepr_substitution_mul, powerCoverRepr_residue_monomial,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Finsupp.univ_sum_single _

/-- Extension of an ideal through the power covering is coordinatewise extension. -/
 theorem mem_map_powerSubstitution_iff (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) (p : MvPolynomial (Fin n) R) :
    p ∈ I.map (powerSubstitution r).toRingHom ↔
      ∀ b : PowerResidues r, powerCoverRepr r hr p b ∈ I := by
  classical
  constructor
  · intro hp
    have h : ∀ c : MvPolynomial (Fin n) R, ∀ b : PowerResidues r,
        powerCoverRepr r hr (c * p) b ∈ I := by
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        intro c b
        change powerCoverRepr r hr (c * powerSubstitution r a) b ∈ I
        rw [mul_comm c, powerCoverRepr_substitution_mul, Finsupp.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ ha
      | zero => intro c b; simpa using I.zero_mem
      | add x y hx hy ihx ihy =>
        intro c b
        simpa only [mul_add, map_add, Finsupp.add_apply] using I.add_mem (ihx c b) (ihy c b)
      | smul c x hx ih =>
        intro d b
        simpa only [smul_eq_mul, mul_assoc] using ih (d * c) b
    simpa only [one_mul] using h 1
  · intro hp
    rw [← powerCover_sum_repr r hr p]
    exact Ideal.sum_mem _ fun b _ ↦
      (I.map (powerSubstitution r).toRingHom).mul_mem_right _
        (Ideal.mem_map_of_mem (powerSubstitution r).toRingHom (hp b))

/-- Principal colons commute with the unequal-degree power covering, with no
unproved flatness or cancellation hypothesis. -/
 theorem map_principalColon_powerSubstitution (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) (g : MvPolynomial (Fin n) R) :
    (principalColon I g).map (powerSubstitution r).toRingHom =
      principalColon (I.map (powerSubstitution r).toRingHom) (powerSubstitution r g) := by
  ext p
  rw [mem_map_powerSubstitution_iff r hr, mem_principalColon,
    mem_map_powerSubstitution_iff r hr]
  simp_rw [mem_principalColon, mul_comm p (powerSubstitution r g),
    powerCoverRepr_substitution_mul, Finsupp.smul_apply, smul_eq_mul, mul_comm g]

/-- One coefficient coordinate, linear over the original coefficient ring. -/
noncomputable def powerCoverCoordinate (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (b : PowerResidues r) : MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin n) R where
  toFun p := powerCoverRepr r hr p b
  map_add' p q := by simp
  map_smul' a p := by
    have h := congrArg (fun f ↦ f b)
      (powerCoverRepr_substitution_mul (R := R) r hr (C a) p)
    simpa [powerSubstitution, Algebra.smul_def] using h

noncomputable def powerCoverQuotientCoordinate (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) (b : PowerResidues r) :
    MvPolynomial (Fin n) R ⧸ I.map (powerSubstitution r).toRingHom →ₗ[R]
      MvPolynomial (Fin n) R ⧸ I :=
  ((I.map (powerSubstitution r).toRingHom).restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (powerCoverCoordinate r hr b))
    (by
      intro p hp
      change Ideal.Quotient.mk I (powerCoverRepr r hr p b) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((mem_map_powerSubstitution_iff r hr I p).mp hp b))

@[simp] theorem powerCoverQuotientCoordinate_mk (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) (b : PowerResidues r)
    (p : MvPolynomial (Fin n) R) :
    powerCoverQuotientCoordinate r hr I b
      (Ideal.Quotient.mk (I.map (powerSubstitution r).toRingHom) p) =
        Ideal.Quotient.mk I (powerCoverRepr r hr p b) := rfl

noncomputable def powerCoverQuotientCoordinates (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    MvPolynomial (Fin n) R ⧸ I.map (powerSubstitution r).toRingHom →ₗ[R]
      (PowerResidues r → MvPolynomial (Fin n) R ⧸ I) :=
  LinearMap.pi (powerCoverQuotientCoordinate r hr I)

 theorem powerCoverQuotientCoordinates_bijective (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Function.Bijective (powerCoverQuotientCoordinates r hr I) := by
  classical
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [mem_map_powerSubstitution_iff r hr]
    intro b
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hq b)
  · intro q
    choose p hp using fun b ↦ Ideal.Quotient.mk_surjective (q b)
    let f : MvPolynomial (Fin n) R :=
      ∑ b : PowerResidues r, powerSubstitution r (p b) * monomial (residuePowerExponent b) 1
    refine ⟨Ideal.Quotient.mk (I.map (powerSubstitution r).toRingHom) f, ?_⟩
    ext b
    change Ideal.Quotient.mk I (powerCoverRepr r hr f b) = q b
    dsimp [f]
    simp_rw [map_sum, powerCoverRepr_substitution_mul, powerCoverRepr_residue_monomial,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    simpa only [Finsupp.coe_univ_sum_single] using hp b

/-- A literal isomorphism of the extended quotient with one copy of the original
quotient for each residue monomial. -/
noncomputable def powerCoverQuotientEquiv (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (MvPolynomial (Fin n) R ⧸ I.map (powerSubstitution r).toRingHom) ≃ₗ[R]
      (PowerResidues r → (MvPolynomial (Fin n) R ⧸ I)) :=
  LinearEquiv.ofBijective (powerCoverQuotientCoordinates r hr I)
    (powerCoverQuotientCoordinates_bijective r hr I)

/-- Every basis of the ordinary quotient extends to the covering by multiplication
with the residue monomials. -/
noncomputable def powerCoverQuotientBasis {ι : Type*}
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (I : Ideal (MvPolynomial (Fin n) R))
    (b : Module.Basis ι R (MvPolynomial (Fin n) R ⧸ I)) :
    Module.Basis (PowerResidues r × ι) R
      (MvPolynomial (Fin n) R ⧸ I.map (powerSubstitution r).toRingHom) :=
  ((Pi.basis fun _ : PowerResidues r ↦ b).map (powerCoverQuotientEquiv r hr I).symm).reindex
    (Equiv.sigmaEquivProd (PowerResidues r) ι)

 theorem powerCoverQuotientBasis_apply {ι : Type*}
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (I : Ideal (MvPolynomial (Fin n) R))
    (b : Module.Basis ι R (MvPolynomial (Fin n) R ⧸ I))
    (v : ι → MvPolynomial (Fin n) R) (hv : ∀ j, b j = Ideal.Quotient.mk I (v j))
    (c : PowerResidues r) (j : ι) :
    powerCoverQuotientBasis r hr I b (c, j) =
      Ideal.Quotient.mk (I.map (powerSubstitution r).toRingHom)
        (powerSubstitution r (v j) * monomial (residuePowerExponent c) 1) := by
  classical
  apply (powerCoverQuotientEquiv r hr I).injective
  simp only [powerCoverQuotientBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basis_apply]
  ext d
  change (Pi.single c (b j) : PowerResidues r → (MvPolynomial (Fin n) R ⧸ I)) d =
    Ideal.Quotient.mk I (powerCoverRepr r hr
      (powerSubstitution r (v j) * monomial (residuePowerExponent c) 1) d)
  rw [powerCoverRepr_substitution_mul, powerCoverRepr_residue_monomial,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hdc : d = c
  · subst d
    simp [hv]
  · simp [Pi.single_eq_of_ne hdc, Finsupp.single_eq_of_ne hdc]

end PaperVerification.Fermion
