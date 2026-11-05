import CommAlg.KoszulComplex.Polynomial
import TauCeti.RingTheory.KoszulComplex.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Exterior-basis coordinates of the genuine tensor Koszul differential -/

noncomputable section

set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory TensorProduct

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]

lemma differential_eq_contraction {N : Type*} [AddCommGroup N] [Module R N]
    (φ : N →ₗ[R] R) (i : ℕ) :
    koszulComplex.d φ i = TauCeti.koszulDifferential φ i := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [koszulComplex.d, koszulComplex.dAlternating_apply,
    TauCeti.koszulDifferential_ιMulti]

/-- Tensor Koszul complex for an arbitrarily indexed finite sequence. -/
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R x))

/-- Its genuine exterior-basis coordinate equivalence. -/
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)

/-- The differential transported through the basis, not stipulated as a different complex. -/
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  (coefficientCoordinates x M i).toLinearMap ∘ₗ
    ((familyCoefficientComplex x M).d (i + 1) i).hom ∘ₗ
      (coefficientCoordinates x M (i + 1)).symm.toLinearMap

lemma coordinateDifferential_comp (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    coordinateDifferential x M i ∘ₗ coordinateDifferential x M (i + 1) = 0 := by
  apply LinearMap.ext
  intro a
  simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.zero_apply]
  have h := congrArg (fun f => ModuleCat.Hom.hom f
    ((coefficientCoordinates x M (i + 2)).symm a))
    ((familyCoefficientComplex x M).d_comp_d (i + 2) (i + 1) i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using congrArg (coefficientCoordinates x M i) h

/-- The coordinate chain complex is explicitly isomorphic to the tensor Koszul complex. -/
def coordinateComplex (x : V → R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of R (Set.powersetCard V i →₀ M))
    (fun i => ModuleCat.ofHom (coordinateDifferential x M i))
    (fun i => ModuleCat.hom_ext (coordinateDifferential_comp x M i))

@[simp] lemma coordinates_basis_tensor (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V i) (m : M) :
    coefficientCoordinates x M i
      (((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m) = Finsupp.single s m := by
  apply Finsupp.ext
  intro t
  change (TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i))
    (((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m) t = (Finsupp.single s m) t
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

@[simp] lemma coordinates_symm_single (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V i) (m : M) :
    (coefficientCoordinates x M i).symm (Finsupp.single s m) =
      ((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m := by
  apply (coefficientCoordinates x M i).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (coordinates_basis_tensor x M i s m).symm

/-- The canonical cardinality-correct index after deleting an exterior generator. -/
def eraseIndex {i : ℕ} (s : Set.powersetCard V (i + 1)) (j : {j // j ∈ s.val}) :
    Set.powersetCard V i :=
  ⟨s.val.erase j.val, by simp [Finset.card_erase_of_mem j.property, s.property]⟩

lemma basis_differential (x : V → R) (i : ℕ) (s : Set.powersetCard V (i + 1)) :
    koszulComplex.d (Fintype.linearCombination R x) i
      ((Pi.basisFun R V).exteriorPower (i + 1) s) =
      ∑ j : {j // j ∈ s.val}, x j.val •
        (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
          (Pi.basisFun R V).exteriorPower i (eraseIndex s j)) := by
  rw [differential_eq_contraction, Module.Basis.koszulDifferential_eq_sum (Pi.basisFun R V)]
  classical
  let f : V → ⋀[R]^i (V → R) := fun j =>
    (Fintype.linearCombination R x) ((Pi.basisFun R V) j) •
      TauCeti.koszulDifferential ((Pi.basisFun R V).coord j) i
        ((Pi.basisFun R V).exteriorPower (i + 1) s)
  change ∑ j, f j = _
  calc
    ∑ j, f j = ∑ j ∈ s.val, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hjnot
      simp only [f]
      rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem _ hjnot,
        smul_zero]
    _ = ∑ j : {j // j ∈ s.val}, f j.val :=
      Finset.sum_subtype s.val (fun _ => Iff.rfl) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem _ j.property]
      simp [eraseIndex, Set.powersetCard.ofCard, Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma family_d_tmul (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (w : ⋀[R]^(i + 1) (V → R)) (m : M) :
    ((familyCoefficientComplex x M).d (i + 1) i).hom (w ⊗ₜ[R] m) =
      koszulComplex.d (Fintype.linearCombination R x) i w ⊗ₜ[R] m := by
  change ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).map
    ((koszulComplex (Fintype.linearCombination R x)).d (i + 1) i) (w ⊗ₜ[R] m) = _
  rw [koszulComplex.d_eq_d]
  rfl

lemma coordinateDifferential_single (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V (i + 1)) (m : M) :
    coordinateDifferential x M i (Finsupp.single s m) =
      ∑ j : {j // j ∈ s.val}, Finsupp.single (eraseIndex s j)
        (x j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • m)) := by
  simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coordinates_symm_single]
  erw [family_d_tmul x M i ((Pi.basisFun R V).exteriorPower (i + 1) s) m]
  rw [basis_differential, TensorProduct.sum_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i))
    ((x j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
      (Pi.basisFun R V).exteriorPower i (eraseIndex s j))) ⊗ₜ[R] m) = _
  apply Finsupp.ext
  intro t
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  simp only [map_smul, map_zsmul_unit, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : eraseIndex s j = t
  · simp only [h, ↓reduceIte, one_smul]
    simpa [smul_smul] using smul_comm (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) (x j.val) m
  · simp [h]

@[simp] lemma coordinateComplex_d (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (coordinateComplex x M).d (i + 1) i =
      ModuleCat.ofHom (coordinateDifferential x M i) := by
  simp [coordinateComplex]

/-- This isomorphism justifies using the explicit coordinates for genuine derived homology. -/
def coordinateComplexIso (x : V → R) (M : ModuleCat.{u} R) :
    familyCoefficientComplex x M ≅ coordinateComplex x M :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (coefficientCoordinates x M i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [coordinateComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change coordinateDifferential x M j (coefficientCoordinates x M (j + 1) z) =
        coefficientCoordinates x M j (((familyCoefficientComplex x M).d (j + 1) j).hom z)
      simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply])

end CommAlg.Koszul
