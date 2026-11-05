module
public import graph_foundation.part014
public import shared_results.part021_sublattice_first_power_criterion

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealRename -/
section

/-! # Ordinary ideal Tor is invariant under actual variable renaming

Every coordinate equivalence below is induced by polynomial renaming and
by the functorial exterior map, with its genuine orientation signs. The
ordinary homogeneous pieces are characterized by their actual polynomial
coefficients. Thus the comparison is independent of the chosen Gröbner
presentation, and applies before any all-power Gröbner theorem is known.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

universe u
variable {K V W : Type u} [CommRing K] [Nontrivial K]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

/-- The intrinsic coefficient condition for the ordinary Koszul grading.
The exterior factor contributes exactly p to the actual total degree. -/
theorem actualIdealOrdinaryPiece_coeff_iff (P : QuotientGroebnerData V K)
    (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) (x : Set.powersetCard V p →₀ P.ideal) :
    x ∈ actualIdealOrdinaryPiece P q p ↔
      ∀ F : Set.powersetCard V p, ∀ a : Exponent V,
        (x F).val.coeff a ≠ 0 → a.degree + p = q := by
  rw [actualIdealOrdinaryPiece_mem_iff P hP, Grading.mem_piece]
  constructor
  · intro hx F a ha
    have h := hx ⟨F,⟨a,emptyFamily_allowed a⟩⟩
      (by simpa only [idealCoordinatesToAmbient_repr] using ha)
    have hF : F.val.card = p := F.property
    simpa only [quotientDegree, map_add, degree_faceExponent, hF] using h
  · intro hx a ha
    have h := hx a.1 a.2.val (by
      simpa only [idealCoordinatesToAmbient_repr] using ha)
    have hF : a.1.val.card = p := a.1.property
    simpa only [quotientDegree, map_add, degree_faceExponent, hF] using h

section Presentation
variable (P : QuotientGroebnerData V K) (Q : QuotientGroebnerData W K)
  (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
  (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : W => (1 : ℕ))))
  (e : V ≃ W) (c : P.ideal ≃ₗ[K] Q.ideal)
  (hc : ∀ f, (c f).val = MvPolynomial.rename e f.val)

include hP hc in
lemma idealRename_coefficient_homogeneous (a : NonstandardIndex P.order P.ideal) :
    MvPolynomial.IsHomogeneous
      (c (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading a)).val
      a.val.degree := by
  rw [hc]
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, Finsupp.degree_eq_weight_one, groebnerIdealBasis_apply] using!
    idealLift_homogeneous_withNatModule P.order P.ideal P.generators P.groebner P.unitLeading
      (fun _ : V => (1 : ℕ)) hP a

include hP hQ hc in
lemma renameCoordinates_ordinary_basis (p : ℕ) (a : ActualIdealIndex P p) :
    TensorExteriorKoszul.renameCoordinates e c p (actualIdealCoefficientBasis P p a) ∈
      actualIdealOrdinaryPiece Q (actualIdealDegree a).degree p := by
  rw [actualIdealCoefficientBasis_apply, TensorExteriorKoszul.renameCoordinates_single]
  let F : Set.powersetCard W p := ⟨a.1.val.image e,
    (Finset.card_image_iff.mpr e.injective.injOn).trans a.1.property⟩
  have hs : Finsupp.single F
      (c (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading a.2)) ∈
        actualIdealOrdinaryPiece Q (actualIdealDegree a).degree p := by
    rw [actualIdealOrdinaryPiece_coeff_iff Q hQ]
    intro F' b hb
    by_cases hF : F=F'
    · rw [Finsupp.single_apply, if_pos hF] at hb
      have hd : b.degree=a.2.val.degree := by
        by_contra h
        exact hb ((idealRename_coefficient_homogeneous P Q hP e c hc a.2).coeff_eq_zero h)
      have haF : a.1.val.card = p := a.1.property
      simp only [actualIdealDegree, map_add, degree_faceExponent, haF, hd]
    · rw [Finsupp.single_apply, if_neg hF] at hb
      exact (hb (by simp)).elim
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K]
  apply (actualIdealOrdinaryPiece Q (actualIdealDegree a).degree p).smul_mem
  simpa only [groebnerIdealBasis_apply] using! hs

include hP hQ hc in
theorem renameCoordinates_ordinary_mem (q p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) (hx : x ∈ actualIdealOrdinaryPiece P q p) :
    TensorExteriorKoszul.renameCoordinates e c p x ∈ actualIdealOrdinaryPiece Q q p :=
  map_mem_piece_of_basis_monoid (R := K)
    (X := Set.powersetCard V p →₀ P.ideal)
    (Y := Set.powersetCard W p →₀ Q.ideal)
    (I := ActualIdealIndex P p) (J := ActualIdealIndex Q p) (A := ℕ)
    (actualIdealCoefficientBasis P p) (actualIdealCoefficientBasis Q p)
    (fun a => (actualIdealDegree a).degree) (fun a => (actualIdealDegree a).degree)
    (TensorExteriorKoszul.renameCoordinates e c p).toLinearMap
    (renameCoordinates_ordinary_basis P Q hP hQ e c hc p) q hx

include hc in
lemma idealRename_symm_val (f : Q.ideal) :
    (c.symm f).val = MvPolynomial.rename e.symm f.val := by
  have he := hc (c.symm f)
  rw [LinearEquiv.apply_symm_apply] at he
  calc
    (c.symm f).val = (MvPolynomial.renameEquiv K e).symm
        ((MvPolynomial.renameEquiv K e) (c.symm f).val) :=
      ((MvPolynomial.renameEquiv K e).symm_apply_apply _).symm
    _ = MvPolynomial.rename e.symm f.val := by
      change MvPolynomial.rename e.symm (MvPolynomial.rename e (c.symm f).val) = _
      rw [← he]

/-- The equivalence retains the exact ordinary and exterior degrees. -/
def idealRenameOrdinaryEquiv (q p : ℕ) :
    actualIdealOrdinaryPiece P q p ≃ₗ[K] actualIdealOrdinaryPiece Q q p where
  toFun x := ⟨TensorExteriorKoszul.renameCoordinates e c p x.val,
    renameCoordinates_ordinary_mem P Q hP hQ e c hc q p x.val x.property⟩
  invFun y := ⟨(TensorExteriorKoszul.renameCoordinates e c p).symm y.val, by
    rw [TensorExteriorKoszul.renameCoordinates_symm_eq]
    exact renameCoordinates_ordinary_mem Q P hQ hP e.symm c.symm
      (idealRename_symm_val P Q e c hc) q p y.val y.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv y := Subtype.ext (LinearEquiv.apply_symm_apply _ y.val)
  map_add' x y := Subtype.ext ((TensorExteriorKoszul.renameCoordinates e c p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((TensorExteriorKoszul.renameCoordinates e c p).map_smul r x.val)

include hc in
lemma idealRename_variable (v : V) (f : P.ideal) :
    c ((X v : MvPolynomial V K) • f) = (X (e v) : MvPolynomial W K) • c f := by
  apply Subtype.ext
  simp only [hc, Submodule.coe_smul, smul_eq_mul, map_mul, MvPolynomial.rename_X]

lemma idealRenameOrdinaryEquiv_differential (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q (p+1)) :
    idealRenameOrdinaryEquiv P Q hP hQ e c hc q p (actualIdealOrdinaryDifferential P hP q p x) =
      actualIdealOrdinaryDifferential Q hQ q p
        (idealRenameOrdinaryEquiv P Q hP hQ e c hc q (p+1) x) := by
  apply Subtype.ext
  exact TensorExteriorKoszul.renameCoordinates_differential e c
    (idealRename_variable P Q e c hc) p x.val

lemma idealRenameOrdinaryEquiv_previous (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    idealRenameOrdinaryEquiv P Q hP hQ e c hc q p.pred (actualIdealOrdinaryPrevious P hP q p x) =
      actualIdealOrdinaryPrevious Q hQ q p
        (idealRenameOrdinaryEquiv P Q hP hQ e c hc q p x) := by
  cases p with
  | zero => simp only [actualIdealOrdinaryPrevious, LinearMap.zero_apply, map_zero]
  | succ p => exact idealRenameOrdinaryEquiv_differential P Q hP hQ e c hc q p x

/-- Renaming induces an equivalence of the literal ordinary-strand
kernel/image quotients, including homological degree zero. -/
def idealRenameOrdinaryHomologyEquiv (q p : ℕ) :
    actualIdealOrdinaryHomology P hP q p ≃ₗ[K] actualIdealOrdinaryHomology Q hQ q p :=
  threeTermHomologyEquiv (R := K)
    (X := actualIdealOrdinaryPiece P q (p+1))
    (Y := actualIdealOrdinaryPiece P q p)
    (Z := actualIdealOrdinaryPiece P q p.pred)
    (X' := actualIdealOrdinaryPiece Q q (p+1))
    (Y' := actualIdealOrdinaryPiece Q q p)
    (Z' := actualIdealOrdinaryPiece Q q p.pred)
    (actualIdealOrdinaryDifferential P hP q p) (actualIdealOrdinaryPrevious P hP q p)
    (actualIdealOrdinaryDifferential_comp P hP q p)
    (actualIdealOrdinaryDifferential Q hQ q p) (actualIdealOrdinaryPrevious Q hQ q p)
    (actualIdealOrdinaryDifferential_comp Q hQ q p)
    (idealRenameOrdinaryEquiv P Q hP hQ e c hc q (p+1))
    (idealRenameOrdinaryEquiv P Q hP hQ e c hc q p)
    (idealRenameOrdinaryEquiv P Q hP hQ e c hc q p.pred)
    (idealRenameOrdinaryEquiv_differential P Q hP hQ e c hc q p)
    (idealRenameOrdinaryEquiv_previous P Q hP hQ e c hc q p)

end Presentation

section ActualIdeals
variable (P : QuotientGroebnerData V K) (Q : QuotientGroebnerData W K) (e : V ≃ W)
  (hPQ : P.ideal.map (MvPolynomial.rename e).toRingHom = Q.ideal)

include hPQ in
lemma renameIdeal_restrictScalars_map :
    (P.ideal.restrictScalars K).map (MvPolynomial.renameEquiv K e).toLinearEquiv.toLinearMap =
      Q.ideal.restrictScalars K := by
  ext f
  change (∃ x, x ∈ P.ideal ∧ MvPolynomial.rename e x=f) ↔ f ∈ Q.ideal
  rw [← hPQ]
  exact (Ideal.mem_map_iff_of_surjective (MvPolynomial.rename e).toRingHom
    (MvPolynomial.renameEquiv K e).surjective).symm

def renameIdealEquiv : P.ideal ≃ₗ[K] Q.ideal :=
  (idealScalarRestrictionEquiv P.ideal).trans
    (((MvPolynomial.renameEquiv K e).toLinearEquiv.ofSubmodules
      (P.ideal.restrictScalars K) (Q.ideal.restrictScalars K)
      (renameIdeal_restrictScalars_map P Q e hPQ)).trans
        (idealScalarRestrictionEquiv Q.ideal).symm)

@[simp] theorem renameIdealEquiv_val (x : P.ideal) :
    (renameIdealEquiv P Q e hPQ x).val = MvPolynomial.rename e x.val := by
  change (((MvPolynomial.renameEquiv K e).toLinearEquiv.ofSubmodules
    (P.ideal.restrictScalars K) (Q.ideal.restrictScalars K)
    (renameIdeal_restrictScalars_map P Q e hPQ))
      (idealScalarRestrictionEquiv P.ideal x)).val = MvPolynomial.rename e x.val
  exact LinearEquiv.ofSubmodules_apply _ _ (idealScalarRestrictionEquiv P.ideal x)

variable
  (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
  (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : W => (1 : ℕ))))

def actualIdealRenameHomologyEquiv (q p : ℕ) :
    actualIdealOrdinaryHomology P hP q p ≃ₗ[K] actualIdealOrdinaryHomology Q hQ q p :=
  idealRenameOrdinaryHomologyEquiv P Q hP hQ e (renameIdealEquiv P Q e hPQ)
    (renameIdealEquiv_val P Q e hPQ) q p

end ActualIdeals

end FourPapers.Sublattice

namespace FourPapers.Sublattice

open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u

section Field
variable {K V W : Type u} [Field K]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  (P : QuotientGroebnerData V K) (Q : QuotientGroebnerData W K)
  (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
  (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : W => (1 : ℕ))))
  (e : V ≃ W) (hPQ : P.ideal.map (MvPolynomial.rename e).toRingHom = Q.ideal)

include hPQ in
/-- Equality of the genuine derived-Tor Betti numbers under variable
renaming, with both p and q unchanged. -/
theorem ordinaryIdealBettiNumber_rename (p q : ℕ) :
    ordinaryIdealBettiNumber P hP p q = ordinaryIdealBettiNumber Q hQ p q := by
  rw [ordinaryIdealBettiNumber_eq_finrank, ordinaryIdealBettiNumber_eq_finrank]
  exact (actualIdealRenameHomologyEquiv P Q e hPQ hP hQ q p).finrank_eq

end Field
end FourPapers.Sublattice

end
end
end


end
