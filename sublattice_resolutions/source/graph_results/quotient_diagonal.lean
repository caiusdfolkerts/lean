module
public import shared_results.part023
public import graph_results.filtered_homology_dimension
public import shared_results.part003
public import Mathlib.Data.Finset.Powerset

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientDiagonal -/
section

/-!
# The diagonal of the Tor table of a proper monomial quotient

Only the variables contained in the ideal contribute to β(p,p). In that
strand every exterior-p coefficient is constant, the incoming group is
zero, and each surviving variable term of the outgoing differential detects
one unique coefficient. Thus the cycles have the actual exterior faces
contained in the linear-variable set as a basis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private lemma diagonal_face_degree (F : Finset V) : (faceExponent F).degree = F.card := by
  simp [faceExponent, map_sum, Finsupp.degree_single]

private lemma diagonal_face_injective : Function.Injective (faceExponent (V := V)) := by
  intro F H h
  apply Finset.ext
  intro v
  have hv := congrArg (fun a : Exponent V => a v) h
  by_cases hf : v ∈ F <;> by_cases hh : v ∈ H <;>
    simp [faceExponent_apply, hf, hh] at hv ⊢

/-- The literal variables killed by the given monomial ideal. -/
def quotientLinearVariables (B : Family V) : Finset V :=
  Finset.univ.filter (fun v => Contains B (Finsupp.single v 1))

variable (B : Family V) (hB : QuotientAllowed B 0)

abbrev DiagonalIndex (p : ℕ) := {a : QuotientIndex B p // (quotientDegree a).degree = p}

abbrev diagonalConstantIndex (p : ℕ) (F : Set.powersetCard V p) : QuotientIndex B p :=
  ⟨F, ⟨0, hB⟩⟩

@[simp] lemma diagonalConstantIndex_degree (p : ℕ) (F : Set.powersetCard V p) :
    quotientDegree (diagonalConstantIndex B hB p F) = faceExponent F.val := zero_add _

lemma diagonalIndex_coefficient_zero (p : ℕ) (a : DiagonalIndex B p) : a.val.2.val = 0 := by
  apply (Finsupp.degree_eq_zero_iff _).mp
  have ha := a.property
  change (a.val.2.val + faceExponent a.val.1.val).degree = p at ha
  rw [map_add, diagonal_face_degree, a.val.1.property] at ha
  omega

def diagonalIndexEquiv (p : ℕ) : DiagonalIndex B p ≃ Set.powersetCard V p where
  toFun a := a.val.1
  invFun F := ⟨diagonalConstantIndex B hB p F, by
    rw [diagonalConstantIndex_degree, diagonal_face_degree, F.property]⟩
  left_inv := by
    rintro ⟨⟨F, a⟩, ha⟩
    have ha0 : a = ⟨0, hB⟩ :=
      Subtype.ext (diagonalIndex_coefficient_zero B p ⟨⟨F, a⟩, ha⟩)
    cases ha0
    rfl
  right_inv _ := rfl

def diagonalQuotientBasis (p : ℕ) :
    Module.Basis (Set.powersetCard V p) k (ordinaryQuotientPiece (k := k) B p p) :=
  (Grading.restrictedBasis (quotientCoefficientBasis (k := k) B p)
    (fun a => (quotientDegree a).degree = p)).reindex (diagonalIndexEquiv B hB p)

@[simp] lemma diagonalQuotientBasis_val (p : ℕ) (F : Set.powersetCard V p) :
    (diagonalQuotientBasis (k := k) B hB p F).val =
      quotientCoefficientBasis B p (diagonalConstantIndex B hB p F) := by
  let b := Grading.restrictedBasis (quotientCoefficientBasis (k := k) B p)
    (fun a => (quotientDegree a).degree = p)
  change ((b.reindex (diagonalIndexEquiv B hB p)) F).val = _
  exact (congrArg Subtype.val (b.reindex_apply (diagonalIndexEquiv B hB p) F)).trans
    (Grading.restrictedBasis_val (quotientCoefficientBasis (k := k) B p)
      (fun a => (quotientDegree a).degree = p) ((diagonalIndexEquiv B hB p).symm F))

lemma ordinaryQuotientPiece_eq_bot_of_lt (q p : ℕ) (hqp : q < p) :
    ordinaryQuotientPiece (k := k) B q p = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change (quotientDegree a).degree = q at ha
  change (a.2.val + faceExponent a.1.val).degree = q at ha
  rw [map_add, diagonal_face_degree, a.1.property] at ha
  omega

/-- A single nonzero linear-variable term detects the coefficient of its
unique exterior face. The sign is a unit over every coefficient field. -/
lemma diagonalDifferential_basis_probe (p : ℕ)
    (F H : Set.powersetCard V (p+1)) (v : {v // v ∈ F.val})
    (hv : QuotientAllowed B (Finsupp.single v.val 1)) :
    (quotientCoefficientBasis (k := k) B p).repr
      (quotientDifferential B p
        (quotientCoefficientBasis B (p+1) (diagonalConstantIndex B hB (p+1) H)))
      ⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ =
      if H = F then TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val • (1 : k) else 0 := by
  by_cases hHF : H = F
  · subst H
    rw [if_pos rfl, quotientDifferential_basis]
    simp only [map_sum, Finsupp.finset_sum_apply]
    dsimp only [diagonalConstantIndex]
    rw [Finset.sum_eq_single v]
    · simp only [diagonalConstantIndex, zero_add, dif_pos hv, map_zsmul_unit,
        Finsupp.smul_apply, Module.Basis.repr_self]
      have hi : quotientDifferentialIndex (diagonalConstantIndex B hB (p+1) F) v
          (by simpa only [diagonalConstantIndex, zero_add] using hv) =
          (⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ : QuotientIndex B p) := by
        simp only [quotientDifferentialIndex, diagonalConstantIndex, zero_add]
      simp only [hi, Finsupp.single_eq_same]
    · intro j _ hj
      split_ifs with hjallow
      · rw [map_zsmul_unit, Finsupp.smul_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne]
        · exact smul_zero _
        · intro he
          have he' := congrArg (fun a : QuotientIndex B p => a.2.val j.val) he
          have hjv : j.val ≠ v.val := fun h => hj (Subtype.ext h)
          simp [quotientDifferentialIndex, diagonalConstantIndex, Finsupp.single_apply,
            hjv, Ne.symm hjv] at he'
      · simp only [map_zero, Finsupp.zero_apply]
    · intro h
      exact (h (Finset.mem_univ v)).elim
  · rw [if_neg hHF]
    by_contra hcoef
    have hhom := quotientDifferential_homogeneous (k := k) B
      (quotientDegree (diagonalConstantIndex B hB (p+1) H)) p
      (Grading.basis_mem_piece (quotientCoefficientBasis (k := k) B (p+1))
        quotientDegree (diagonalConstantIndex B hB (p+1) H))
    have he := (Grading.mem_piece (quotientCoefficientBasis (k := k) B p)
      quotientDegree _ _).mp hhom ⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ hcoef
    have ht : quotientDegree (⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ :
        QuotientIndex B p) = faceExponent F.val := by
      change Finsupp.single v.val 1 + faceExponent (F.val.erase v.val) = _
      rw [add_comm, faceExponent_erase_add v.property]
    rw [ht, diagonalConstantIndex_degree] at he
    exact hHF (Subtype.ext (diagonal_face_injective he).symm)

lemma diagonalPrevious_probe (p : ℕ) (F : Set.powersetCard V (p+1))
    (v : {v // v ∈ F.val}) (hv : QuotientAllowed B (Finsupp.single v.val 1))
    (x : ordinaryQuotientPiece (k := k) B (p+1) (p+1)) :
    (quotientCoefficientBasis (k := k) B p).repr
      (ordinaryQuotientPrevious B (p+1) (p+1) x).val
      ⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ =
      TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val •
        (diagonalQuotientBasis (k := k) B hB (p+1)).repr x F := by
  let lhs : ordinaryQuotientPiece (k := k) B (p+1) (p+1) →ₗ[k] k :=
    ((quotientCoefficientBasis (k := k) B p).coord
      ⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩).comp
      ((ordinaryQuotientPiece (k := k) B (p+1) p).subtype.comp
        (ordinaryQuotientPrevious B (p+1) (p+1)))
  let rhs : ordinaryQuotientPiece (k := k) B (p+1) (p+1) →ₗ[k] k :=
    (TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val • (1 : k)) •
      (diagonalQuotientBasis (k := k) B hB (p+1)).coord F
  have he : lhs = rhs := by
    apply (diagonalQuotientBasis (k := k) B hB (p+1)).ext
    intro H
    change (quotientCoefficientBasis (k := k) B p).repr
      (quotientDifferential B p (diagonalQuotientBasis B hB (p+1) H).val)
        ⟨eraseIndex F v, ⟨Finsupp.single v.val 1, hv⟩⟩ = _
    rw [diagonalQuotientBasis_val, diagonalDifferential_basis_probe]
    simp only [rhs, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hx := LinearMap.congr_fun he x
  simpa only [lhs, rhs, LinearMap.comp_apply, Submodule.subtype_apply,
    Module.Basis.coord_apply, LinearMap.smul_apply, smul_eq_mul,
    Units.smul_def, zsmul_eq_mul, mul_one] using hx

lemma diagonalQuotientBasis_cycle (p : ℕ) (F : Set.powersetCard V p)
    (hF : F.val ⊆ quotientLinearVariables B) :
    ordinaryQuotientPrevious (k := k) B p p (diagonalQuotientBasis B hB p F) = 0 := by
  cases p with
  | zero => rfl
  | succ p =>
      apply Subtype.ext
      change quotientDifferential B p (diagonalQuotientBasis B hB (p+1) F).val = 0
      rw [diagonalQuotientBasis_val, quotientDifferential_basis]
      apply Finset.sum_eq_zero
      intro v _
      have hv : ¬QuotientAllowed B (0 + Finsupp.single v.val 1) := by
        intro ha
        exact ha (by simpa only [zero_add] using (Finset.mem_filter.mp (hF v.property)).2)
      exact dif_neg hv

lemma diagonalCycle_iff (p : ℕ) (x : ordinaryQuotientPiece (k := k) B p p) :
    ordinaryQuotientPrevious B p p x = 0 ↔
      x ∈ Submodule.span k (diagonalQuotientBasis (k := k) B hB p ''
        {F | F.val ⊆ quotientLinearVariables B}) := by
  constructor
  · intro hx
    rw [(diagonalQuotientBasis (k := k) B hB p).mem_span_image]
    intro F hF v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hallow
    cases p with
    | zero =>
        have he : F.val = ∅ := Finset.card_eq_zero.mp F.property
        exact (Finset.notMem_empty v) (he ▸ hv)
    | succ p =>
        have he := diagonalPrevious_probe (k := k) B hB p F ⟨v,hv⟩ hallow x
        rw [hx, Submodule.coe_zero, map_zero, Finsupp.zero_apply] at he
        have hz : (diagonalQuotientBasis (k := k) B hB (p+1)).repr x F = 0 :=
          (smul_eq_zero_iff_eq _).mp he.symm
        exact (Finsupp.mem_support_iff.mp hF) hz
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨F,hF,rfl⟩ := hx
        exact diagonalQuotientBasis_cycle B hB p F hF
    | zero => exact map_zero _
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul c x hx ih => rw [map_smul, ih, smul_zero]

private def diagonalFaceEquiv (p : ℕ) :
    {F : Set.powersetCard V p // F.val ⊆ quotientLinearVariables B} ≃
      ↥((quotientLinearVariables B).powersetCard p) where
  toFun F := ⟨F.val.val, Finset.mem_powersetCard.mpr ⟨F.property,F.val.property⟩⟩
  invFun F := ⟨⟨F.val,(Finset.mem_powersetCard.mp F.property).2⟩,
    (Finset.mem_powersetCard.mp F.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hB in
/-- **Diagonal monomial quotient formula.** No condition is imposed on
higher-degree generators beyond properness of the actual ideal. -/
theorem ordinaryQuotientBetti_diagonal (p : ℕ) :
    ordinaryQuotientBettiNumber (k := k) B p p =
      Nat.choose (quotientLinearVariables B).card p := by
  let Y := ordinaryQuotientPiece (k := k) B p p
  let X := ordinaryQuotientPiece (k := k) B p (p+1)
  let g := ordinaryQuotientPrevious (k := k) B p p
  let f := ordinaryQuotientDifferential (k := k) B p p
  letI : Module.Finite k Y := Module.Finite.of_basis (diagonalQuotientBasis (k := k) B hB p)
  have hX : Subsingleton X := by
    change Subsingleton (ordinaryQuotientPiece (k := k) B p (p+1))
    rw [ordinaryQuotientPiece_eq_bot_of_lt B p (p+1) (Nat.lt_succ_self p)]
    infer_instance
  letI := hX
  letI : Module.Finite k X := inferInstance
  have hker : LinearMap.ker g = Submodule.span k (diagonalQuotientBasis (k := k) B hB p ''
      {F | F.val ⊆ quotientLinearVariables B}) := by
    ext x
    exact diagonalCycle_iff B hB p x
  have hrank : Module.finrank k (LinearMap.ker g) =
      Nat.choose (quotientLinearVariables B).card p := by
    rw [hker]
    rw [Module.finrank_eq_card_basis (Grading.restrictedBasis
      (diagonalQuotientBasis (k := k) B hB p) (fun F => F.val ⊆ quotientLinearVariables B))]
    rw [Fintype.card_congr (diagonalFaceEquiv B p), Fintype.card_coe, Finset.card_powersetCard]
  have hdim := threeTerm_homology_finrank_add f g (ordinaryQuotientDifferential_comp B p p)
  have hzX : Module.finrank k X = 0 := Module.finrank_zero_of_subsingleton
  have hzk : Module.finrank k (LinearMap.ker f) = 0 := Module.finrank_zero_of_subsingleton
  rw [hzX, hzk, add_zero, add_zero, hrank] at hdim
  exact hdim

end FourPapers.Sublattice

end
end
end


end
