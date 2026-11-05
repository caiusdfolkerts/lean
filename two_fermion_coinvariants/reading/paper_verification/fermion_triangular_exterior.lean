module

public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Push

/-!
# Triangularity in an actual exterior-power basis

A triangular vector transformation is triangular after taking exterior
powers. We order finite subsets by the sum of their numerical ranks. Every
off-diagonal coefficient with at least the source weight vanishes; the
diagonal coefficient is the product of the original diagonal entries.
This gives exactly the triangular separation needed by the creator argument,
without replacing the exterior algebra by a combinatorial surrogate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section Minor

variable {R I : Type*} [CommRing R] {k : ℕ}

/-- A nonzero triangular determinant term forces componentwise inequalities
between the numerical ranks of its selected row and column indices. -/
theorem triangular_minor_zero_of_weight
    (rank : I → ℕ) (hinj : Function.Injective rank)
    (A : Matrix I I R) (hA : ∀ i j, rank j < rank i → A i j = 0)
    (s t : Fin k → I) (hne : Set.range s ≠ Set.range t)
    (hweight : (∑ i, rank (t i)) ≤ ∑ i, rank (s i)) :
    (Matrix.of fun i j : Fin k ↦ A (s i) (t j)).det = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hz : ∃ i : Fin k, A (s (σ i)) (t i) = 0 := by
    by_contra h
    push_neg at h
    have hle (i : Fin k) : rank (s (σ i)) ≤ rank (t i) := by
      by_contra hi
      exact h i (hA _ _ (Nat.lt_of_not_ge hi))
    have hsum : (∑ i, rank (s (σ i))) = ∑ i, rank (t i) := by
      apply le_antisymm (Finset.sum_le_sum fun i _ ↦ hle i)
      calc
        (∑ i, rank (t i)) ≤ ∑ i, rank (s i) := hweight
        _ = ∑ i, rank (s (σ i)) := (Equiv.sum_comp σ (fun i ↦ rank (s i))).symm
    have heq (i : Fin k) : s (σ i) = t i := by
      apply hinj
      exact (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp hsum i (Finset.mem_univ i)
    apply hne
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨σ.symm i, ?_⟩
      simpa only [Equiv.apply_symm_apply] using (heq (σ.symm i)).symm
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, heq i⟩
  obtain ⟨i, hi⟩ := hz
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, smul_zero]

/-- Every principal minor of a numerically triangular matrix is the product
of its selected diagonal entries, independently of the enumeration. -/
theorem triangular_principal_minor
    (rank : I → ℕ) (hinj : Function.Injective rank)
    (A : Matrix I I R) (hA : ∀ i j, rank j < rank i → A i j = 0)
    (s : Fin k → I) (hs : Function.Injective s) :
    (Matrix.of fun i j : Fin k ↦ A (s i) (s j)).det = ∏ i, A (s i) (s i) := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, one_smul, Matrix.of_apply]
  · intro σ _ hσ
    have hz : ∃ i : Fin k, A (s (σ i)) (s i) = 0 := by
      by_contra h
      push_neg at h
      have hle (i : Fin k) : rank (s (σ i)) ≤ rank (s i) := by
        by_contra hi
        exact h i (hA _ _ (Nat.lt_of_not_ge hi))
      have hsum : (∑ i, rank (s (σ i))) = ∑ i, rank (s i) := Equiv.sum_comp σ (fun i ↦ rank (s i))
      have heq (i : Fin k) : σ i = i := by
        apply hs
        apply hinj
        exact (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ hle j)).mp hsum i (Finset.mem_univ i)
      exact hσ (Equiv.ext heq)
    obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, smul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Minor

section Exterior

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [LinearOrder I] [Fintype I]

/-- The numerical weight of a basis wedge, using its increasing enumeration. -/
def exteriorIndexWeight (rank : I → ℕ) {k : ℕ} (s : Set.powersetCard I k) : ℕ :=
  ∑ i : Fin k, rank (Set.powersetCard.ofFinEmbEquiv.symm s i)

theorem exteriorIndex_enum_range {k : ℕ} (s : Set.powersetCard I k) :
    Set.range (Set.powersetCard.ofFinEmbEquiv.symm s) = (s.val : Set I) := by
  simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.range_orderEmbOfFin s.val s.property

/-- The actual coordinate of an exterior-power map is the corresponding
minor of the original coordinate matrix, in conventional row-column order. -/
theorem exterior_map_coordinate_minor (b : Module.Basis I R V)
    (f : V →ₗ[R] V) (k : ℕ) (s t : Set.powersetCard I k) :
    (b.exteriorPower k).repr (exteriorPower.map k f (b.exteriorPower k t)) s =
      (Matrix.of fun i j : Fin k ↦
        b.repr (f (b (Set.powersetCard.ofFinEmbEquiv.symm t j)))
          (Set.powersetCard.ofFinEmbEquiv.symm s i)).det := by
  rw [← LinearMap.toMatrix_apply, Module.Basis.toMatrix_exteriorPower_map]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, LinearMap.toMatrix_apply]

/-- Only strictly lower-weight wedges can occur off the diagonal. -/
theorem exterior_map_coordinate_zero
    (b : Module.Basis I R V) (f : V →ₗ[R] V)
    (rank : I → ℕ) (hinj : Function.Injective rank)
    (hf : ∀ i j, rank j < rank i → b.repr (f (b j)) i = 0)
    (k : ℕ) (s t : Set.powersetCard I k) (hst : s ≠ t)
    (hweight : exteriorIndexWeight rank t ≤ exteriorIndexWeight rank s) :
    (b.exteriorPower k).repr (exteriorPower.map k f (b.exteriorPower k t)) s = 0 := by
  rw [exterior_map_coordinate_minor]
  apply triangular_minor_zero_of_weight rank hinj
    (Matrix.of fun i j ↦ b.repr (f (b j)) i) hf _ _ _ hweight
  intro heq
  apply hst
  apply Subtype.ext
  apply Finset.coe_injective
  simpa only [exteriorIndex_enum_range] using heq

/-- The creator's coefficient at its own exterior pattern is the product of
its specified diagonal coefficients. -/
theorem exterior_map_coordinate_self
    (b : Module.Basis I R V) (f : V →ₗ[R] V)
    (rank : I → ℕ) (hinj : Function.Injective rank)
    (hf : ∀ i j, rank j < rank i → b.repr (f (b j)) i = 0)
    (k : ℕ) (t : Set.powersetCard I k) :
    (b.exteriorPower k).repr (exteriorPower.map k f (b.exteriorPower k t)) t =
      ∏ i : Fin k, b.repr
        (f (b (Set.powersetCard.ofFinEmbEquiv.symm t i)))
        (Set.powersetCard.ofFinEmbEquiv.symm t i) := by
  rw [exterior_map_coordinate_minor]
  exact triangular_principal_minor rank hinj
    (Matrix.of fun i j ↦ b.repr (f (b j)) i) hf _
    (Set.powersetCard.ofFinEmbEquiv.symm t).injective

/-- The coordinates of a homogeneous exterior vector agree in its exterior
power basis and in the full exterior-algebra basis. -/
theorem exteriorPower_coordinate_coe (b : Module.Basis I R V) (k : ℕ)
    (s : Set.powersetCard I k) (w : ⋀[R]^k V) :
    b.ExteriorAlgebra.repr (w : ExteriorAlgebra R V) s.val =
      (b.exteriorPower k).repr w s := by
  have h : (b.ExteriorAlgebra.coord s.val).comp (ExteriorAlgebra.exteriorPower R k V).subtype =
      (b.exteriorPower k).coord s := by
    apply (b.exteriorPower k).ext
    intro t
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
      ← ExteriorAlgebra.basis_eq_coe_basis, Module.Basis.repr_self, Finsupp.single_apply]
    congr 1
    exact propext Subtype.val_injective.eq_iff
  exact LinearMap.congr_fun h w

end Exterior

end PaperVerification.Fermion
