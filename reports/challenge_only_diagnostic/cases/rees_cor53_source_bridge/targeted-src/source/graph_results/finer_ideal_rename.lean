module
public import shared_results.part023
public import shared_results.part021
public import graph_foundation.part014

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FinerIdealRename -/
section

/-!
# Finer graded Tor under variable renaming

The maps are induced by the actual polynomial renaming and the signed
exterior map. Arbitrary additive grading labels are allowed, and the
weights on the two variable sets need only correspond under the given
bijection. In particular, integer vertex and component row gradings are
retained without selecting an ordinary grading first.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u v
variable {K V W : Type u} [Field K]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {Γ : Type v} [AddCommMonoid Γ]

/-- Renaming an exponent retains its weighted degree when each variable
retains its assigned degree. -/
theorem weight_mapDomain_of_correspondence (ω : V → Γ) (ω' : W → Γ)
    (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v) (a : Exponent V) :
    Finsupp.weight ω' (a.mapDomain e) = Finsupp.weight ω a := by
  induction a using Finsupp.induction_linear with
  | zero => simp only [Finsupp.mapDomain_zero, map_zero]
  | add a b ha hb => simp only [Finsupp.mapDomain_add, map_add, ha, hb]
  | single v n => simp only [Finsupp.mapDomain_single, Finsupp.weight_single, hω]

theorem weightedHomogeneous_rename (ω : V → Γ) (ω' : W → Γ)
    (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v)
    {f : MvPolynomial V K} {γ : Γ} (hf : f.IsWeightedHomogeneous ω γ) :
    (MvPolynomial.rename e f).IsWeightedHomogeneous ω' γ := by
  intro a ha
  obtain ⟨b, rfl, hb⟩ := MvPolynomial.coeff_rename_ne_zero e f a ha
  rw [weight_mapDomain_of_correspondence ω ω' e hω]
  exact hf hb

/-- Homogeneous ideal generation is preserved by the actual variable map. -/
theorem homogeneousIdeal_rename_weighted (J : Ideal (MvPolynomial V K))
    (ω : V → Γ) (ω' : W → Γ) (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule K ω)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (weightedHomogeneousSubmodule K ω') := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (weightedHomogeneousSubmodule K ω) J).mp hJ
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro f ⟨g, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨γ, hγ⟩ := a.property
  exact ⟨γ, weightedHomogeneous_rename ω ω' e hω hγ⟩

theorem weight_faceExponent_image (ω : V → Γ) (ω' : W → Γ)
    (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v) (F : Finset V) :
    Finsupp.weight ω' (faceExponent (F.image e)) = Finsupp.weight ω (faceExponent F) := by
  simp only [faceExponent, map_sum, Finsupp.weight_single, one_nsmul]
  rw [Finset.sum_image]
  · simp only [hω]
  · exact fun _ _ _ _ h => e.injective h

/-- This is the intrinsic condition on every literal polynomial
coefficient, including the weighted exterior degree. -/
theorem finerIdealPiece_coeff_iff (P : QuotientGroebnerData V K) (ω : V → Γ)
    (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))
    (γ : Γ) (p : ℕ) (x : Set.powersetCard V p →₀ P.ideal) :
    x ∈ finerIdealPiece P ω γ p ↔
      ∀ F : Set.powersetCard V p, ∀ a : Exponent V,
        (x F).val.coeff a ≠ 0 → Finsupp.weight ω (a + faceExponent F.val) = γ := by
  rw [finerIdealPiece_eq_polynomial P ω hP]
  change idealCoordinatesToAmbient P.ideal p x ∈ Grading.Piece _ _ γ ↔ _
  rw [Grading.mem_piece]
  constructor
  · intro hx F a ha
    exact hx ⟨F, ⟨a, emptyFamily_allowed a⟩⟩
      (by simpa only [idealCoordinatesToAmbient_repr] using ha)
  · intro hx a ha
    exact hx a.1 a.2.val (by simpa only [idealCoordinatesToAmbient_repr] using ha)

section Presentation
variable (P : QuotientGroebnerData V K) (Q : QuotientGroebnerData W K)
  (ω : V → Γ) (ω' : W → Γ)
  (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))
  (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω'))
  (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v)
  (c : P.ideal ≃ₗ[K] Q.ideal) (hc : ∀ f, (c f).val = MvPolynomial.rename e f.val)

include hP hω hc in
lemma idealRename_coefficient_weighted (a : NonstandardIndex P.order P.ideal) :
    MvPolynomial.IsWeightedHomogeneous ω'
      (c (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading a)).val
      (Finsupp.weight ω a.val) := by
  rw [hc]
  apply weightedHomogeneous_rename ω ω' e hω
  simpa only [groebnerIdealBasis_apply] using!
    idealLift_homogeneous_withNatModule P.order P.ideal P.generators P.groebner
      P.unitLeading ω hP a

include hP hQ hω hc in
lemma renameCoordinates_finer_basis (p : ℕ) (a : ActualIdealIndex P p) :
    TensorExteriorKoszul.renameCoordinates e c p (actualIdealCoefficientBasis P p a) ∈
      finerIdealPiece Q ω' (Finsupp.weight ω (actualIdealDegree a)) p := by
  rw [actualIdealCoefficientBasis_apply, TensorExteriorKoszul.renameCoordinates_single]
  let F : Set.powersetCard W p := ⟨a.1.val.image e,
    (Finset.card_image_iff.mpr e.injective.injOn).trans a.1.property⟩
  have hs : Finsupp.single F
      (c (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading a.2)) ∈
      finerIdealPiece Q ω' (Finsupp.weight ω (actualIdealDegree a)) p := by
    rw [finerIdealPiece_coeff_iff Q ω' hQ]
    intro F' b hb
    by_cases hF : F = F'
    · rw [Finsupp.single_apply, if_pos hF] at hb
      have hd := idealRename_coefficient_weighted P Q ω ω' hP e hω c hc a.2 hb
      rw [map_add, hd, ← hF]
      change Finsupp.weight ω a.2.val + Finsupp.weight ω' (faceExponent (a.1.val.image e)) = _
      rw [weight_faceExponent_image ω ω' e hω]
      exact (map_add (Finsupp.weight ω) a.2.val (faceExponent a.1.val)).symm
    · rw [Finsupp.single_apply, if_neg hF] at hb
      exact (hb (by simp)).elim
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K]
  apply (finerIdealPiece Q ω' (Finsupp.weight ω (actualIdealDegree a)) p).smul_mem
  simpa only [groebnerIdealBasis_apply] using! hs

include hP hQ hω hc in
theorem renameCoordinates_finer_mem (γ : Γ) (p : ℕ)
    (x : Set.powersetCard V p →₀ P.ideal) (hx : x ∈ finerIdealPiece P ω γ p) :
    TensorExteriorKoszul.renameCoordinates e c p x ∈ finerIdealPiece Q ω' γ p :=
  map_mem_piece_of_basis_monoid (R := K)
    (X := Set.powersetCard V p →₀ P.ideal) (Y := Set.powersetCard W p →₀ Q.ideal)
    (I := ActualIdealIndex P p) (J := ActualIdealIndex Q p) (A := Γ)
    (actualIdealCoefficientBasis P p) (actualIdealCoefficientBasis Q p)
    (fun a => Finsupp.weight ω (actualIdealDegree a))
    (fun a => Finsupp.weight ω' (actualIdealDegree a))
    (TensorExteriorKoszul.renameCoordinates e c p).toLinearMap
    (renameCoordinates_finer_basis P Q ω ω' hP hQ e hω c hc p) γ hx

/-- The equivalence preserves the full grading label and the exterior degree. -/
def idealRenameFinerEquiv (γ : Γ) (p : ℕ) :
    finerIdealPiece P ω γ p ≃ₗ[K] finerIdealPiece Q ω' γ p where
  toFun x := ⟨TensorExteriorKoszul.renameCoordinates e c p x.val,
    renameCoordinates_finer_mem P Q ω ω' hP hQ e hω c hc γ p x.val x.property⟩
  invFun y := ⟨(TensorExteriorKoszul.renameCoordinates e c p).symm y.val, by
    rw [TensorExteriorKoszul.renameCoordinates_symm_eq]
    exact renameCoordinates_finer_mem Q P ω' ω hQ hP e.symm
      (fun w => by simpa only [Equiv.apply_symm_apply] using (hω (e.symm w)).symm)
      c.symm (idealRename_symm_val P Q e c hc) γ p y.val y.property⟩
  left_inv x := Subtype.ext (LinearEquiv.symm_apply_apply _ x.val)
  right_inv y := Subtype.ext (LinearEquiv.apply_symm_apply _ y.val)
  map_add' x y := Subtype.ext ((TensorExteriorKoszul.renameCoordinates e c p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((TensorExteriorKoszul.renameCoordinates e c p).map_smul r x.val)

lemma idealRenameFinerEquiv_differential (γ : Γ) (p : ℕ)
    (x : finerIdealPiece P ω γ (p + 1)) :
    idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ p (finerIdealDifferential P ω hP γ p x) =
      finerIdealDifferential Q ω' hQ γ p
        (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ (p + 1) x) := by
  apply Subtype.ext
  exact TensorExteriorKoszul.renameCoordinates_differential e c
    (idealRename_variable P Q e c hc) p x.val

lemma idealRenameFinerEquiv_previous (γ : Γ) (p : ℕ) (x : finerIdealPiece P ω γ p) :
    idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ p.pred (finerIdealPrevious P ω hP γ p x) =
      finerIdealPrevious Q ω' hQ γ p
        (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ p x) := by
  cases p with
  | zero => exact (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ 0).map_zero
  | succ p => exact idealRenameFinerEquiv_differential P Q ω ω' hP hQ e hω c hc γ p x

def idealRenameFinerHomologyEquiv (γ : Γ) (p : ℕ) :
    finerIdealHomology P ω hP γ p ≃ₗ[K] finerIdealHomology Q ω' hQ γ p :=
  threeTermHomologyEquiv (R := K)
    (X := finerIdealPiece P ω γ (p+1)) (Y := finerIdealPiece P ω γ p)
    (Z := finerIdealPiece P ω γ p.pred)
    (X' := finerIdealPiece Q ω' γ (p+1)) (Y' := finerIdealPiece Q ω' γ p)
    (Z' := finerIdealPiece Q ω' γ p.pred)
    (finerIdealDifferential P ω hP γ p) (finerIdealPrevious P ω hP γ p)
    (finerIdealDifferential_comp P ω hP γ p)
    (finerIdealDifferential Q ω' hQ γ p) (finerIdealPrevious Q ω' hQ γ p)
    (finerIdealDifferential_comp Q ω' hQ γ p)
    (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ (p + 1))
    (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ p)
    (idealRenameFinerEquiv P Q ω ω' hP hQ e hω c hc γ p.pred)
    (idealRenameFinerEquiv_differential P Q ω ω' hP hQ e hω c hc γ p)
    (idealRenameFinerEquiv_previous P Q ω ω' hP hQ e hω c hc γ p)

end Presentation

/-- This compares genuine derived-Tor pieces of the literal renamed ideals.
The polynomial presentation and its chosen Gröbner basis need not agree. -/
theorem finerIdealBettiNumber_rename
    (P : QuotientGroebnerData V K) (Q : QuotientGroebnerData W K)
    (ω : V → Γ) (ω' : W → Γ)
    (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω))
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K ω'))
    (e : V ≃ W) (hω : ∀ v, ω' (e v) = ω v)
    (hPQ : P.ideal.map (MvPolynomial.rename e).toRingHom = Q.ideal) (p : ℕ) (γ : Γ) :
    finerIdealBettiNumber P ω hP p γ = finerIdealBettiNumber Q ω' hQ p γ := by
  rw [finerIdealBettiNumber, finerIdealBettiNumber,
    ← (finerIdealGradedTorEquiv P ω hP γ p).finrank_eq,
    ← (finerIdealGradedTorEquiv Q ω' hQ γ p).finrank_eq]
  exact (idealRenameFinerHomologyEquiv P Q ω ω' hP hQ e hω
    (renameIdealEquiv P Q e hPQ) (renameIdealEquiv_val P Q e hPQ) γ p).finrank_eq

end FourPapers.Sublattice

end
end
end


end
