module

public import PaperVerification.AlternatingFormsIntegerGrading
public import PaperVerification.TwoCentralKoszulOperator
public import PaperVerification.ExteriorDerivationTransport
public import TauCeti.Algebra.Module.GradedModule.Prod
import Lean.Elab.Tactic.Omega

/-!
# Cohomological degrees in the central exterior decomposition

The grading is the actual exterior degree. Under the explicit four-summand
decomposition, the original, one-central-generator, and two-central-generator
terms have degree shifts zero, one, and two. In terms of the internal Koszul
weights (zero, two, four), this is precisely the rule `cohomological = internal
minus Koszul position` used after Proposition 5.4.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoCentralExteriorGrading

open AlternatingForms TwoCentralExteriorDecomposition TwoCentralKoszulOperator

variable {K M N' : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N'] [Module K N']

/-- Exterior algebra functoriality preserves the genuine integer grading. -/
theorem exteriorMap_homogeneous (f : M →ₗ[K] N') :
    TauCeti.LinearMap.IsHomogeneous (ExteriorAlgebra.map f).toLinearMap
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  rw [add_zero]
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx ⊢
    exact ExteriorDerivationTransport.map_mem_exteriorPower f hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- Multiplication by an actual degree-r form has that integer degree. -/
theorem exteriorMultiplication_homogeneous {r : ℕ} (a : ⋀[K]^r M) :
    TauCeti.LinearMap.IsHomogeneous (LinearMap.mulLeft K (a : ExteriorAlgebra K M))
      exteriorIntegerGrading.piece exteriorIntegerGrading.piece (r : ℤ) := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q + (r : ℤ))]
    have hdeg : (q + (r : ℤ)).toNat = r + q.toNat := by omega
    rw [hdeg]
    exact SetLike.mul_mem_graded a.property hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- A degree-one map on every actual exterior power gives the corresponding
homogeneous map on the integer extension, including negative degrees. -/
theorem homogeneous_of_exterior_degree_one
    (D : Module.End K (ExteriorAlgebra K M))
    (hD : ∀ q x, x ∈ ⋀[K]^q M → D x ∈ ⋀[K]^(q+1) M) :
    TauCeti.LinearMap.IsHomogeneous D exteriorIntegerGrading.piece
      exteriorIntegerGrading.piece 1 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q x hx
  by_cases hq : 0 ≤ q
  · rw [exteriorIntegerGrading_piece_of_nonneg hq] at hx
    rw [exteriorIntegerGrading_piece_of_nonneg (by omega : 0 ≤ q+1)]
    have hdeg : (q+1).toNat = q.toNat+1 := by omega
    rw [hdeg]
    exact hD _ _ hx
  · rw [exteriorIntegerGrading_piece_negative (by omega)] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

/-- The original internal Koszul gradings, with positions subtracted to
obtain the actual cohomological grading. -/
def foldedExteriorGrading : TauCeti.InternalGrading K
    (E K M × ((E K M × E K M) × E K M)) :=
  exteriorIntegerGrading.prod
    ((((exteriorIntegerGrading.prod exteriorIntegerGrading).shift (-2)).shift 1).prod
      ((exteriorIntegerGrading.shift (-4)).shift 2))

/-- Inverse Koszul coordinates preserve the genuine exterior degree. -/
theorem koszulCoordinates_symm_homogeneous :
    TauCeti.LinearMap.IsHomogeneous
      (koszulCoordinates (R := K) (M := M)).symm.toLinearMap
      foldedExteriorGrading.piece exteriorIntegerGrading.piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro q z hz
  rw [add_zero]
  simp only [foldedExteriorGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece] at hz
  change z.1 ∈ (exteriorIntegerGrading (K := K) (M := M)).piece q ∧
    ((z.2.1.1 ∈ exteriorIntegerGrading.piece (q+1 + -2) ∧
      z.2.1.2 ∈ exteriorIntegerGrading.piece (q+1 + -2)) ∧
      z.2.2 ∈ exteriorIntegerGrading.piece (q+2 + -4)) at hz
  have hlift := exteriorMap_homogeneous (inc (R := K) (M := M))
  have ha : lift z.1 ∈ (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    simpa only [add_zero, lift, AlgHom.toLinearMap_apply] using hlift.map_mem hz.1
  have he₀ : e (R := K) (M := M) 0 ∈ ⋀[K]^1 (N K M) :=
    TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  have he₁ : e (R := K) (M := M) 1 ∈ ⋀[K]^1 (N K M) :=
    TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one _
  have hb : e 0 * lift z.2.1.1 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 0,he₀⟩).map_mem
      (hlift.map_mem hz.2.1.1)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_one, Nat.cast_ofNat, show q+1 + -2+0+(1 : ℤ) = q by omega] using hh
  have hc : e 1 * lift z.2.1.2 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 1,he₁⟩).map_mem
      (hlift.map_mem hz.2.1.2)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_one, Nat.cast_ofNat, show q+1 + -2+0+(1 : ℤ) = q by omega] using hh
  have he₂ : e (R := K) (M := M) 0 * e 1 ∈ ⋀[K]^2 (N K M) :=
    SetLike.mul_mem_graded he₀ he₁
  have hd : e 0 * e 1 * lift z.2.2 ∈
      (exteriorIntegerGrading (K := K) (M := N K M)).piece q := by
    have hh := (exteriorMultiplication_homogeneous ⟨e 0 * e 1,he₂⟩).map_mem
      (hlift.map_mem hz.2.2)
    simpa only [lift, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      Nat.cast_ofNat, show q+2 + -4+0+(2 : ℤ) = q by omega] using hh
  change lift z.1 + e 0 * lift z.2.1.1 + e 1 * lift z.2.1.2 +
    e 0 * e 1 * lift z.2.2 ∈ _
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ha hb) hc) hd

/-- The forward coordinate map also preserves actual cohomological degree. -/
theorem koszulCoordinates_homogeneous :
    TauCeti.LinearMap.IsHomogeneous
      (koszulCoordinates (R := K) (M := M)).toLinearMap
      exteriorIntegerGrading.piece foldedExteriorGrading.piece 0 :=
  TauCeti.LinearMap.IsHomogeneous.linearEquiv_symm koszulCoordinates_symm_homogeneous

end PaperVerification.TwoCentralExteriorGrading
