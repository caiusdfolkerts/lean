module

public import PaperVerification.FinitePavingChowRank
public import PaperVerification.SymmetricProjectiveEmpty
public import PaperVerification.GradedProjScalarMap
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# The one-plane boundary: the actual Chow rank of projective space

The proof inducts on the dimension of the vector space, using its genuine
projective hyperplane and complementary affine space. The rank-zero base
is the empty projective spectrum, so no projective-bundle formula or Chern
relation is used or assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TotalChow

open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

open SymmetricProjectiveEmpty

variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]

instance symmetricAlgebra_isNoetherian : IsNoetherianRing (SymmetricAlgebra ℂ M) := by
  letI := SymmetricProjective.Proper.BundleCycles.symmetricAlgebra_finiteType ℂ M
  exact Algebra.FiniteType.isNoetherianRing ℂ _

instance symmetricAffine_isNoetherian : AlgebraicGeometry.IsNoetherian
    (Spec (CommRingCat.of (SymmetricAlgebra ℂ M))) :=
  (AlgebraicGeometry.isNoetherian_Spec (R := CommRingCat.of (SymmetricAlgebra ℂ M))).mpr
    (symmetricAlgebra_isNoetherian M)

instance symmetricAffineToBase_finiteType : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M)))) := by
  letI := SymmetricProjective.Proper.BundleCycles.symmetricAlgebra_finiteType ℂ M
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The actual affine symmetric spectrum of a finite complex vector
space has total Chow rank at most one. -/
theorem symmetricAffine_total_rank :
    letI := symmetricAffine_isNoetherian M
    Module.Finite ℚ (TotalChowQ
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))))) ∧
      Module.finrank ℚ (TotalChowQ
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))))) ≤ 1 := by
  letI := symmetricAffine_isNoetherian M
  letI := symmetricAffineToBase_finiteType M
  let b := Module.finBasis ℂ M
  let e := Scheme.Spec.mapIso
    (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toCommRingCatIso.op
  exact finite_and_finrank_le_one_of_polynomialIso _ _ e
    (AlternatingForms.specAlgEquiv_hom_over (SymmetricAlgebra.equivMvPolynomial b))

/-- Adding a scalar summand adds one genuine affine stratum. -/
theorem symmetricProjective_total_rank_step
    (hM : Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M))) :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (ℂ × M))) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (ℂ × M))) ≤
        Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) + 1 := by
  let p := symmetricProjectiveToBase ℂ (ℂ × M)
  let j := SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion ℂ M
  let i := Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification ℂ M
  have hj : j ≫ p = symmetricProjectiveToBase ℂ M :=
    SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over _ _
  have hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℂ (SymmetricAlgebra ℂ M))) :=
    Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_over ℂ M
  have hc : Set.range j = (Set.range i)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range ℂ M
  have ha := symmetricAffine_total_rank M
  letI : Module.Finite ℚ (TotalChowQ (j ≫ p)) := by rw [hj]; exact hM
  letI : Module.Finite ℚ (TotalChowQ (i ≫ p)) := by rw [hi]; exact ha.1
  refine ⟨finite_of_closed_open i j p hc,?_⟩
  have h := finrank_le_closed_add_open i j p hc
  rw [hj,hi] at h
  exact h.trans (Nat.add_le_add_left ha.2 _)

/-- A coordinate vector space of rank n has projective Chow rank at most n,
including rank zero, whose actual projective spectrum is empty. -/
theorem coordinateProjective_total_rank (n : ℕ) :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (Fin n → ℂ))) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ (Fin n → ℂ))) ≤ n := by
  induction n with
  | zero =>
    letI := symmetricProjective_isEmpty_of_subsingleton ℂ (Fin 0 → ℂ)
    have h := finite_and_finrank_eq_zero_of_empty (symmetricProjectiveToBase ℂ (Fin 0 → ℂ))
    exact ⟨h.1,h.2.le⟩
  | succ n ih =>
    let e : (Fin (n+1) → ℂ) ≃ₗ[ℂ] ℂ × (Fin n → ℂ) :=
      LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n) ≪≫ₗ
        LinearEquiv.piOptionEquivProd ℂ
    let E := symmetricProjectiveIso e
    have hover : E.hom ≫ symmetricProjectiveToBase ℂ (ℂ × (Fin n → ℂ)) =
        symmetricProjectiveToBase ℂ (Fin (n+1) → ℂ) :=
      SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over
        e.symm.toLinearMap e.symm.surjective
    let C := totalChowEquiv E _ _ hover
    have h := symmetricProjective_total_rank_step (Fin n → ℂ) ih.1
    letI := h.1
    refine ⟨Module.Finite.equiv C.symm,?_⟩
    rw [C.finrank_eq]
    exact h.2.trans (Nat.add_le_add_right ih.2 1)

/-- The result is independent of a chosen basis and concerns the actual
projective spectrum of the given finite vector space. -/
theorem symmetricProjective_total_rank :
    Module.Finite ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) ∧
      Module.finrank ℚ (TotalChowQ (symmetricProjectiveToBase ℂ M)) ≤ Module.finrank ℂ M := by
  let e := symmetricProjectiveIso (Module.finBasis ℂ M).equivFun
  have hover : e.hom ≫ symmetricProjectiveToBase ℂ (Fin (Module.finrank ℂ M) → ℂ) =
      symmetricProjectiveToBase ℂ M :=
    SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over
      (Module.finBasis ℂ M).equivFun.symm.toLinearMap
      (Module.finBasis ℂ M).equivFun.symm.surjective
  let C := totalChowEquiv e _ _ hover
  have h := coordinateProjective_total_rank (Module.finrank ℂ M)
  letI := h.1
  exact ⟨Module.Finite.equiv C.symm,C.finrank_eq.trans_le h.2⟩

end PaperVerification.TotalChow
