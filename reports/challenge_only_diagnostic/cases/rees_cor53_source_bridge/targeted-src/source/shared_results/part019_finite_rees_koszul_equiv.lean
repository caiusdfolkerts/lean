module
public import graph_foundation.part013
public import shared_results.part019_filtered_kernel_comparison

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteReesKoszulEquiv -/
section

/-! # Transport of the proved monomial Rees homology generation theorem -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration
open scoped TensorProduct

universe u
variable {K : Type u} [CommRing K] [Nontrivial K]
  {d : ℕ} {n : Fin d → ℕ} (E : Finset (FiniteTuple n))

local notation "I" => finiteSublatticeIdeal n (k := K) E

def finiteReesKoszulCoefficientEquiv : ReesKoszulTensorAlgebra E K ≃ₐ[K] IdealReesKoszul I :=
  Algebra.TensorProduct.congr (finiteReesCoefficientEquiv (K := K) E)
    AlgEquiv.refl

@[simp] theorem finiteReesKoszulCoefficientEquiv_tmul
    (x : finiteReesImage E K) (z : Simplicial.Ambient (FiniteVariable.{u} n) K) :
    finiteReesKoszulCoefficientEquiv (K := K) E (x ⊗ₜ[K] z) =
      finiteReesCoefficientEquiv (K := K) E x ⊗ₜ[K] z := rfl

theorem finiteReesCoefficientEquiv_baseVariable (v : (FiniteVariable.{u} n)) :
    finiteReesCoefficientEquiv (K := K) E (finiteReesBaseVariable E v) = idealReesBaseVariable I v := by
  apply Subtype.ext
  rw [finiteReesCoefficientEquiv_val, finiteReesBaseVariable_val]
  change ((MvPolynomial.optionEquivLeft K (FiniteVariable.{u} n)) (MvPolynomial.X (some v))).toFinsupp =
    AddMonoidAlgebra.single 0 (MvPolynomial.X v)
  rw [MvPolynomial.optionEquivLeft_X_some]
  rfl

theorem finiteReesKoszulCoefficientEquiv_d (hE : finiteLatticeClosed n E)
    (x : ReesKoszulTensorAlgebra E K) :
    finiteReesKoszulCoefficientEquiv (K := K) E ((reesKoszulTensorDGA (k := K) hE).d x) =
      (idealReesKoszulDGA I).d (finiteReesKoszulCoefficientEquiv (K := K) E x) := by
  rw [reesKoszulTensorDGA_d]
  have he : (finiteReesKoszulCoefficientEquiv (K := K) E).toLinearMap.comp
      (reesKoszulTensorDifferential (E := E) (k := K)) =
      (idealReesKoszulDGA I).d.comp (finiteReesKoszulCoefficientEquiv (K := K) E).toLinearMap := by
    apply TensorProduct.ext'
    intro r z
    change finiteReesKoszulCoefficientEquiv (K := K) E (reesKoszulTensorDifferential (r ⊗ₜ[K] z)) =
      (idealReesKoszulDGA I).d (finiteReesKoszulCoefficientEquiv (K := K) E (r ⊗ₜ[K] z))
    rw [reesKoszulTensorDifferential_tmul, map_sum, finiteReesKoszulCoefficientEquiv_tmul]
    change _ = TensorExteriorKoszul.differential (idealReesBaseVariable I)
      (finiteReesCoefficientEquiv (K := K) E r ⊗ₜ[K] z)
    rw [TensorExteriorKoszul.differential_tmul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [finiteReesKoszulCoefficientEquiv_tmul, map_mul, finiteReesCoefficientEquiv_baseVariable]
    rfl
  exact LinearMap.congr_fun he x

def finiteReesKoszulHomologyEquiv (hE : finiteLatticeClosed n E) :
    ReesKoszulHomology (k := K) hE ≃ₐ[K] (idealReesKoszulDGA I).Homology :=
  ParityDifferential.homologyEquiv (reesKoszulTensorDGA hE) (idealReesKoszulDGA I)
    (finiteReesKoszulCoefficientEquiv (K := K) E) (finiteReesKoszulCoefficientEquiv_d E hE)

variable (m : MonomialOrder (FiniteVariable.{u} n)) (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) =
    (finiteSublatticeIdeal n (k := K) E) ^ s)
  (G : ℕ → Set (MvPolynomial (FiniteVariable.{u} n) K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

include hinit in
theorem finiteReesKoszulCoefficientEquiv_auxiliary (s : ℕ)
    (x : ReesKoszulTensorAlgebra E K) (hx : x ∈ actualReesDegreePiece (E := E) s) :
    finiteReesKoszulCoefficientEquiv (K := K) E x ∈ WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu s := by
  have hpowerInitial : ∀ r, initialIdealForBasis m (J ^ r) = I ^ r := hinit
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a, F⟩, ha, rfl⟩ := hx
      change a.val none = s at ha
      rw [reesTensorBasis, Module.Basis.tensorProduct_apply,
        finiteReesKoszulCoefficientEquiv_tmul]
      change _ ∈ Submodule.span K ((initialReesKoszulBasis m J I hpowerInitial G hG hu) '' {b | b.1.1 = s})
      rw [Module.Basis.mem_span_image]
      intro b hb
      have hne := Finsupp.mem_support_iff.mp hb
      change ((initialReesBasis m J I hpowerInitial G hG hu).tensorProduct (Simplicial.basis (V := FiniteVariable.{u} n) (k := K))).repr
        (_ ⊗ₜ[K] (Simplicial.basis (V := FiniteVariable.{u} n) (k := K)) F) b ≠ 0 at hne
      rw [Module.Basis.tensorProduct_repr_tmul_apply, initialReesBasis_repr] at hne
      have he : (finiteReesCoefficientEquiv (K := K) E (finiteReesImageBasis E K a)).val =
          AddMonoidAlgebra.single (a.val none) (monomial (finiteReesFineExponent a) (1 : K)) := by
        rw [finiteReesCoefficientEquiv_val, finiteReesImageBasis_val,
          optionPolynomialCoefficientEquiv_monomial]
      rw [he, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hne
      by_contra hs
      have haux : a.val none ≠ b.1.1 := fun h => hs (h.symm.trans ha)
      simp only [if_neg haux, MvPolynomial.coeff_zero, Finsupp.zero_apply, smul_zero] at hne
      exact hne rfl
  | zero => simpa only [map_zero] using (WeightedRees.initialAuxiliaryPiece m J I hpowerInitial G hG hu s).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (WeightedRees.initialAuxiliaryPiece m J I hpowerInitial G hG hu s).add_mem ihx ihy
  | smul r x hx ih => simpa only [map_smul] using
      (WeightedRees.initialAuxiliaryPiece m J I hpowerInitial G hG hu s).smul_mem r ih

include hinit in
/-- The existing generation result is transferred to exactly the initial
Koszul algebra used in the filtered comparison. -/
theorem initialReesKoszulHomology_generated_of_finite_generation (hE : finiteLatticeClosed n E)
    (hgen : Algebra.adjoin K (actualFirstReesClasses (k := K) hE) = ⊤) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu 1)) = ⊤ := by
  have hpowerInitial : ∀ r, initialIdealForBasis m (J ^ r) = I ^ r := hinit
  let e := finiteReesKoszulHomologyEquiv (K := K) E hE
  let L := Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
    (WeightedRees.initialAuxiliaryPiece m J I hpowerInitial G hG hu 1))
  have hle : (⊤ : Subalgebra K (ReesKoszulHomology (k := K) hE)) ≤ L.comap e.toAlgHom := by
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro u ⟨z, hz, rfl⟩
    apply Algebra.subset_adjoin
    refine ⟨ParityDifferential.cyclesEquiv _ _ (finiteReesKoszulCoefficientEquiv (K := K) E)
      (finiteReesKoszulCoefficientEquiv_d E hE) z,
      finiteReesKoszulCoefficientEquiv_auxiliary E m J hpowerInitial G hG hu 1 z.val hz, ?_⟩
    exact (ParityDifferential.homologyEquiv_classMap _ _ _ _ z).symm
  apply top_unique
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  exact hle (show x ∈ (⊤ : Subalgebra K (ReesKoszulHomology (k := K) hE)) from trivial)

end FourPapers.Sublattice

end
end
end


end
