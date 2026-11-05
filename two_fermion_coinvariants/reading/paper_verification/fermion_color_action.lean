module

public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionExteriorBaseChange
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The actual diagonal color action on strict moment algebras

The matrix acts on the two exterior generators at every index and fixes
all polynomial variables. The odd moments transform as the standard
representation and the mixed moment transforms by the determinant.
Consequently the literal two-sided strict moment ideal is preserved.

No group action is
postulated as an assumption of a paper-facing theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorAction

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev ColorMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- The same two-by-two linear color change at each genuine exterior index. -/
def linear (A : ColorMatrix R) : OddModule R n →ₗ[R] OddModule R n where
  toFun v := Sum.elim
    (fun i => A 0 0 * v (.inl i) + A 0 1 * v (.inr i))
    (fun i => A 1 0 * v (.inl i) + A 1 1 * v (.inr i))
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> ring
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply] <;> ring

@[simp] theorem linear_one : linear (n := n) (1 : ColorMatrix R) = LinearMap.id := by
  ext v j
  cases j <;> simp [linear, Matrix.one_apply]

theorem linear_mul (A B : ColorMatrix R) :
    linear (n := n) (A * B) = (linear A).comp (linear B) := by
  ext v j
  cases j <;> simp only [linear, LinearMap.coe_mk, AddHom.coe_mk,
    Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, Matrix.mul_apply,
    Fin.sum_univ_two] <;> ring

theorem linear_theta (A : ColorMatrix R) (i : Fin n) :
    linear A (Pi.single (.inl i) 1) =
      A 0 0 • Pi.single (.inl i) 1 + A 1 0 • Pi.single (.inr i) 1 := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases h : j = i
      · subst j; simp [linear, Pi.single_apply]
      · simp [linear, Pi.single_apply, h, Ne.symm h]
  | inr j =>
      by_cases h : j = i
      · subst j; simp [linear, Pi.single_apply]
      · simp [linear, Pi.single_apply, h, Ne.symm h]

theorem linear_xi (A : ColorMatrix R) (i : Fin n) :
    linear A (Pi.single (.inr i) 1) =
      A 0 1 • Pi.single (.inl i) 1 + A 1 1 • Pi.single (.inr i) 1 := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases h : j = i
      · subst j; simp [linear, Pi.single_apply]
      · simp [linear, Pi.single_apply, h, Ne.symm h]
  | inr j =>
      by_cases h : j = i
      · subst j; simp [linear, Pi.single_apply]
      · simp [linear, Pi.single_apply, h, Ne.symm h]

/-- A polynomial-linear endomorphism of the original tensor-product algebra. -/
def ambient (A : ColorMatrix R) :
    SuperRing R n →ₐ[PolynomialRing R n] SuperRing R n :=
  Algebra.TensorProduct.map (AlgHom.id (PolynomialRing R n) (PolynomialRing R n))
    (ExteriorAlgebra.map (linear A))

@[simp] theorem ambient_one :
    ambient (n := n) (1 : ColorMatrix R) = AlgHom.id (PolynomialRing R n) _ := by
  rw [ambient, linear_one, ExteriorAlgebra.map_id, Algebra.TensorProduct.map_id]

theorem ambient_mul (A B : ColorMatrix R) :
    ambient (n := n) (A * B) = (ambient A).comp (ambient B) := by
  simp only [ambient, linear_mul, ← ExteriorAlgebra.map_comp_map,
    Algebra.TensorProduct.map_id_comp]

@[simp] theorem ambient_theta (A : ColorMatrix R) (i : Fin n) :
    ambient A (theta R n i) =
      MvPolynomial.C (σ := Fin n) (A 0 0) • theta R n i +
        MvPolynomial.C (σ := Fin n) (A 1 0) • xi R n i := by
  change Algebra.TensorProduct.map
    (AlgHom.id (PolynomialRing R n) (PolynomialRing R n))
    (ExteriorAlgebra.map (linear A))
    ((1 : PolynomialRing R n) ⊗ₜ[R]
      ExteriorAlgebra.ι R (Pi.single (Sum.inl i) (1 : R) : OddModule R n)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    ExteriorAlgebra.map_apply_ι, linear_theta, map_add, map_smul, map_smul,
    TensorProduct.tmul_add]
  simp only [theta, xi, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_one]

@[simp] theorem ambient_xi (A : ColorMatrix R) (i : Fin n) :
    ambient A (xi R n i) =
      MvPolynomial.C (σ := Fin n) (A 0 1) • theta R n i +
        MvPolynomial.C (σ := Fin n) (A 1 1) • xi R n i := by
  change Algebra.TensorProduct.map
    (AlgHom.id (PolynomialRing R n) (PolynomialRing R n))
    (ExteriorAlgebra.map (linear A))
    ((1 : PolynomialRing R n) ⊗ₜ[R]
      ExteriorAlgebra.ι R (Pi.single (Sum.inr i) (1 : R) : OddModule R n)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    ExteriorAlgebra.map_apply_ι, linear_xi, map_add, map_smul, map_smul,
    TensorProduct.tmul_add]
  simp only [theta, xi, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_one]

theorem theta_square (i : Fin n) : theta R n i * theta R n i = 0 := by
  change Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι R _) *
    Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι R _) = _
  rw [← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]

theorem xi_square (i : Fin n) : xi R n i * xi R n i = 0 := by
  change Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι R _) *
    Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι R _) = _
  rw [← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]

theorem xi_theta (i : Fin n) : xi R n i * theta R n i = -(theta R n i * xi R n i) := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := R)
    (Pi.single (Sum.inr i) (1 : R) : OddModule R n)
    (Pi.single (Sum.inl i) (1 : R) : OddModule R n)
  have he := congrArg (Algebra.TensorProduct.includeRight
    (R := R) (A := PolynomialRing R n)) h
  have hh : xi R n i * theta R n i + theta R n i * xi R n i = 0 := by
    simpa only [map_add, map_mul, map_zero, theta, xi] using he
  exact eq_neg_of_add_eq_zero_left hh

/-- The determinant, with the actual mixed product and no weight coefficient. -/
theorem ambient_mixed (A : ColorMatrix R) (i : Fin n) :
    ambient A (theta R n i * xi R n i) =
      MvPolynomial.C (σ := Fin n) A.det • (theta R n i * xi R n i) := by
  rw [map_mul, ambient_theta, ambient_xi]
  simp only [add_mul, mul_add, smul_mul_smul_comm, theta_square, xi_square,
    smul_zero, zero_add, add_zero, xi_theta, smul_neg, ← sub_eq_add_neg,
    ← sub_smul, ← MvPolynomial.C_mul, ← MvPolynomial.C_sub, Matrix.det_fin_two]
  simp only [zero_sub, ← neg_smul, ← add_smul,
    ← MvPolynomial.C_neg, ← MvPolynomial.C_add] <;> congr 2 <;> ring

/-- All four infinite moment families transform inside their original ideal. -/
theorem ambient_strict_moment (A : ColorMatrix R)
    (phi : Fin n → PolynomialRing R n) (kind : MomentKind) (k : ℕ) :
    ambient A (moment phi (strictCoefficients (fun _ => 1) phi kind) k) =
      match kind with
      | .polynomial => moment phi (strictCoefficients (fun _ => 1) phi .polynomial) k
      | .theta =>
          MvPolynomial.C (σ := Fin n) (A 0 0) •
            moment phi (strictCoefficients (fun _ => 1) phi .theta) k +
          MvPolynomial.C (σ := Fin n) (A 1 0) •
            moment phi (strictCoefficients (fun _ => 1) phi .xi) k
      | .xi =>
          MvPolynomial.C (σ := Fin n) (A 0 1) •
            moment phi (strictCoefficients (fun _ => 1) phi .theta) k +
          MvPolynomial.C (σ := Fin n) (A 1 1) •
            moment phi (strictCoefficients (fun _ => 1) phi .xi) k
      | .mixed =>
          MvPolynomial.C (σ := Fin n) A.det •
            moment phi (strictCoefficients (fun _ => 1) phi .mixed) k := by
  cases kind <;> simp only [moment, strictCoefficients, MvPolynomial.C_1,
    one_mul, one_smul, map_sum, map_smul, map_one,
    ambient_theta, ambient_xi, ambient_mixed,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul, mul_comm]

/-- Invariance of the complete two-sided ideal follows on its actual generators. -/
theorem ambient_preserves_strictIdeal (A : ColorMatrix R)
    (phi : Fin n → PolynomialRing R n) {z : SuperRing R n}
    (hz : z ∈ strictIdeal (fun _ => 1) phi) :
    ambient A z ∈ strictIdeal (fun _ => 1) phi := by
  let I := strictIdeal (fun _ => (1 : R)) phi
  have hscalar (c : PolynomialRing R n) {y : SuperRing R n} (hy : y ∈ I) : c • y ∈ I := by
    rw [Algebra.smul_def c y]
    exact I.mul_mem_left _ _ hy
  induction hz using TwoSidedIdeal.span_induction with
  | mem z hz =>
      obtain ⟨⟨kind,k⟩,rfl⟩ := hz
      rw [ambient_strict_moment]
      have hm (j : MomentKind) : moment phi (strictCoefficients (fun _ => (1 : R)) phi j) k ∈ I :=
        TwoSidedIdeal.subset_span ⟨(j,k),rfl⟩
      cases kind
      · exact hm .polynomial
      · exact I.add_mem (hscalar _ (hm .theta)) (hscalar _ (hm .xi))
      · exact I.add_mem (hscalar _ (hm .theta)) (hscalar _ (hm .xi))
      · exact hscalar _ (hm .mixed)
  | zero => simpa only [map_zero] using I.zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using I.add_mem ihx ihy
  | neg x hx ih => simpa only [map_neg] using I.neg_mem ih
  | left_absorb x y hy ih => simpa only [map_mul] using I.mul_mem_left _ _ ih
  | right_absorb x y hx ih => simpa only [map_mul] using I.mul_mem_right _ _ ih

/-- An invertible color matrix gives an actual ambient algebra automorphism. -/
def ambientEquiv (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    SuperRing R n ≃ₐ[PolynomialRing R n] SuperRing R n :=
  AlgEquiv.ofAlgHom (ambient g.val) (ambient g.inv)
    (by rw [← ambient_mul, g.val_inv, ambient_one])
    (by rw [← ambient_mul, g.inv_val, ambient_one])

/-- The diagonal GL(2) automorphism of the actual strict quotient. -/
def quotientEquiv (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (phi : Fin n → PolynomialRing R n) :
    StrictQuotient (fun _ => (1 : R)) phi ≃ₐ[R]
      StrictQuotient (fun _ => (1 : R)) phi :=
  twoSidedQuotientEquiv ((ambientEquiv g).restrictScalars R)
    (strictIdeal (fun _ => 1) phi) (strictIdeal (fun _ => 1) phi)
    (fun _ hz => ambient_preserves_strictIdeal g.val phi hz)
    (fun _ hz => ambient_preserves_strictIdeal g.inv phi hz)

@[simp] theorem quotientEquiv_mk (g : Matrix.GeneralLinearGroup (Fin 2) R)
    (phi : Fin n → PolynomialRing R n) (z : SuperRing R n) :
    quotientEquiv g phi ((strictIdeal (fun _ => 1) phi).ringCon.mkₐ R z) =
      (strictIdeal (fun _ => 1) phi).ringCon.mkₐ R (ambient g.val z) := rfl

@[simp] theorem quotientEquiv_one (phi : Fin n → PolynomialRing R n) :
    quotientEquiv (1 : Matrix.GeneralLinearGroup (Fin 2) R) phi = 1 := by
  apply AlgEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ :=
    (strictIdeal (fun _ => (1 : R)) phi).ringCon.mkₐ_surjective (α := R) z
  change (strictIdeal (fun _ => (1 : R)) phi).ringCon.mkₐ R
    (ambient (1 : ColorMatrix R) x) = _
  rw [ambient_one]
  rfl

theorem quotientEquiv_mul (g h : Matrix.GeneralLinearGroup (Fin 2) R)
    (phi : Fin n → PolynomialRing R n) :
    quotientEquiv (g*h) phi = quotientEquiv g phi * quotientEquiv h phi := by
  apply AlgEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ :=
    (strictIdeal (fun _ => (1 : R)) phi).ringCon.mkₐ_surjective (α := R) z
  simp only [AlgEquiv.mul_apply,quotientEquiv_mk]
  change (strictIdeal (fun _ => (1 : R)) phi).ringCon.mkₐ R
    (ambient (g.val*h.val) x) = _
  rw [ambient_mul]
  rfl

/-- The group law is proved on the literal quotient, not assumed separately. -/
def quotientAction (phi : Fin n → PolynomialRing R n) :
    Matrix.GeneralLinearGroup (Fin 2) R →*
      (StrictQuotient (fun _ => (1 : R)) phi ≃ₐ[R]
        StrictQuotient (fun _ => (1 : R)) phi) where
  toFun g := quotientEquiv g phi
  map_one' := quotientEquiv_one phi
  map_mul' g h := quotientEquiv_mul g h phi

end PaperVerification.Fermion.ColorAction
