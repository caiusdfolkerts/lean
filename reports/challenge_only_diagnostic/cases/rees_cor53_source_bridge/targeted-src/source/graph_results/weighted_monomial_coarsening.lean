module
public import shared_results.part020
public import graph_results.canonical_finer_monomial_homology
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.WeightedMonomialCoarsening -/
section

/-! # Finite coarsening of actual fine monomial Tor -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u v
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
  {Γ : Type v} [AddCommMonoid Γ]

local instance finerIndexFintype (ω : V → Γ) (γ : Γ) [Finite (FinerDegreeIndex ω γ)] :
    Fintype (FinerDegreeIndex ω γ) := Fintype.ofFinite _

def weightedMonomialPiece (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :
    Submodule k (Set.powersetCard V p →₀ monomialIdeal k B) :=
  Grading.Piece (monomialCoefficientBasis (k := k) B p)
    (fun a => Finsupp.weight ω (monomialDegree a)) γ

instance weightedMonomialPiece_addCommGroup (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :
    AddCommGroup (weightedMonomialPiece (k := k) B ω γ p) :=
  Submodule.addCommGroup (R := k) (M := Set.powersetCard V p →₀ monomialIdeal k B)
    (weightedMonomialPiece (k := k) B ω γ p)

instance weightedMonomialPiece_module (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :
    Module k (weightedMonomialPiece (k := k) B ω γ p) :=
  Submodule.module (R := k) (M := Set.powersetCard V p →₀ monomialIdeal k B)
    (weightedMonomialPiece (k := k) B ω γ p)

lemma monomialDifferential_weighted (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ)
    {x : Set.powersetCard V (p+1) →₀ monomialIdeal k B}
    (hx : x ∈ weightedMonomialPiece (k := k) B ω γ (p+1)) :
    monomialDifferential (k := k) B p x ∈ weightedMonomialPiece (k := k) B ω γ p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have hf := monomialDifferential_homogeneous (k := k) B (monomialDegree a) p
        (Grading.basis_mem_piece (monomialCoefficientBasis (k := k) B (p+1)) monomialDegree a)
      apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hf
      change monomialDegree i = monomialDegree a at hi
      change Finsupp.weight ω (monomialDegree i) = γ
      change Finsupp.weight ω (monomialDegree a) = γ at ha
      rw [hi, ha]
  | zero => simpa only [map_zero] using
      (Submodule.zero_mem (weightedMonomialPiece (k := k) B ω γ p))
  | add x y hx hy ihx ihy => simpa only [map_add] using
      (Submodule.add_mem (weightedMonomialPiece (k := k) B ω γ p) ihx ihy)
  | smul r x hx ih => simpa only [map_smul] using
      (Submodule.smul_mem (weightedMonomialPiece (k := k) B ω γ p) r ih)

def weightedMonomialDifferential (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :
    weightedMonomialPiece (k := k) B ω γ (p+1) →ₗ[k] weightedMonomialPiece (k := k) B ω γ p :=
  ((monomialDifferential (k := k) B p).domRestrict _).codRestrict _
    (fun x => monomialDifferential_weighted (k := k) B ω γ p x.property)

def weightedMonomialPrevious (B : Family V) (ω : V → Γ) (γ : Γ) : ∀ p : ℕ,
    weightedMonomialPiece (k := k) B ω γ p →ₗ[k] weightedMonomialPiece (k := k) B ω γ p.pred
  | 0 => 0
  | p+1 => weightedMonomialDifferential (k := k) B ω γ p

@[simp] lemma weightedMonomialPrevious_val (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ)
    (x : weightedMonomialPiece (k := k) B ω γ p) :
    (weightedMonomialPrevious (k := k) B ω γ p x).val = monomialPreviousDifferential (k := k) B p x.val := by
  cases p <;> rfl

lemma weightedMonomialDifferential_comp (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :
    (weightedMonomialPrevious (k := k) B ω γ p).comp
      (weightedMonomialDifferential (k := k) B ω γ p) = 0 := by
  cases p with
  | zero => simp only [weightedMonomialPrevious, LinearMap.zero_comp]
  | succ p =>
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (monomialDifferential_comp (k := k) B p) x.val

abbrev weightedMonomialHomology (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) :=
  FourPapers.FilteredHomology.Homology (K := k)
    (X := weightedMonomialPiece (k := k) B ω γ (p+1))
    (Y := weightedMonomialPiece (k := k) B ω γ p)
    (Z := weightedMonomialPiece (k := k) B ω γ p.pred)
    (weightedMonomialDifferential (k := k) B ω γ p)
    (weightedMonomialPrevious (k := k) B ω γ p) (weightedMonomialDifferential_comp (k := k) B ω γ p)

def weightedMonomialPieceEquivPi (B : Family V) (ω : V → Γ) (γ : Γ) [Finite (FinerDegreeIndex ω γ)] (p : ℕ) :
    weightedMonomialPiece (k := k) B ω γ p ≃ₗ[k]
      ∀ α : FinerDegreeIndex ω γ, homogeneousPiece (k := k) B α.val p where
  toFun x α := ⟨homogeneousProjection (k := k) B α.val p x.val,
    homogeneousProjection_mem (k := k) B α.val p x.val⟩
  invFun y := ⟨∑ α, (y α).val, by
    apply Submodule.sum_mem
    intro α _
    apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) (y α).property
    change monomialDegree i = α.val at hi
    change Finsupp.weight ω (monomialDegree i) = γ
    rw [hi, α.property]⟩
  left_inv x := by
    apply Subtype.ext
    apply (monomialCoefficientBasis (k := k) B p).repr.injective
    ext i
    simp only [map_sum, Finsupp.finset_sum_apply, homogeneousProjection,
      Grading.projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Grading.filterMap_apply, Finsupp.filter_apply]
    by_cases hz : (monomialCoefficientBasis (k := k) B p).repr x.val i = 0
    · simp only [hz, ite_self, Finset.sum_const_zero]
    · have hi := (Grading.mem_piece (monomialCoefficientBasis (k := k) B p) (fun i => Finsupp.weight ω (monomialDegree i)) γ x.val).mp
        x.property i hz
      let α : FinerDegreeIndex ω γ := ⟨monomialDegree i, hi⟩
      rw [Finset.sum_eq_single α]
      · simp only [α, ite_true]
      · intro β _ hβα
        apply if_neg
        intro he
        exact hβα (Subtype.ext he.symm)
      · simp
  right_inv y := by
    funext α
    apply Subtype.ext
    change homogeneousProjection (k := k) B α.val p (∑ β, (y β).val) = (y α).val
    rw [map_sum, Finset.sum_eq_single α]
    · exact Grading.projection_eq_self (y α).property
    · intro β _ hβα
      apply Grading.projection_eq_zero _ (y β).property
      intro he
      exact hβα (Subtype.ext he.symm)
    · simp
  map_add' x y := by
    funext α
    apply Subtype.ext
    exact map_add (homogeneousProjection (k := k) B α.val p) x.val y.val
  map_smul' r x := by
    funext α
    apply Subtype.ext
    exact map_smul (homogeneousProjection (k := k) B α.val p) r x.val

lemma weightedMonomialPieceEquivPi_differential (B : Family V) (ω : V → Γ) (γ : Γ) [Finite (FinerDegreeIndex ω γ)] (p : ℕ)
    (x : weightedMonomialPiece (k := k) B ω γ (p+1)) (α : FinerDegreeIndex ω γ) :
    weightedMonomialPieceEquivPi (k := k) B ω γ p (weightedMonomialDifferential (k := k) B ω γ p x) α =
      homogeneousDifferential (k := k) B α.val p (weightedMonomialPieceEquivPi (k := k) B ω γ (p+1) x α) := by
  apply Subtype.ext
  change homogeneousProjection (k := k) B α.val p
    (monomialDifferential (k := k) B p x.val) =
      monomialDifferential (k := k) B p
        (homogeneousProjection (k := k) B α.val (p+1) x.val)
  exact LinearMap.congr_fun (homogeneousProjection_differential (k := k) B α.val p) x.val

lemma weightedMonomialPieceEquivPi_previous (B : Family V) (ω : V → Γ) (γ : Γ) [Finite (FinerDegreeIndex ω γ)] (p : ℕ)
    (x : weightedMonomialPiece (k := k) B ω γ p) (α : FinerDegreeIndex ω γ) :
    weightedMonomialPieceEquivPi (k := k) B ω γ p.pred (weightedMonomialPrevious (k := k) B ω γ p x) α =
      monomialFinePrevious (k := k) B α.val p (weightedMonomialPieceEquivPi (k := k) B ω γ p x α) := by
  cases p with
  | zero =>
      apply Subtype.ext
      change Grading.projection (monomialCoefficientBasis (k := k) B 0)
        monomialDegree α.val 0 = 0
      exact map_zero _
  | succ p => exact weightedMonomialPieceEquivPi_differential (k := k) B ω γ p x α

/-- The literal ordinary cycle/boundary quotient is the finite product of
the literal fine cycle/boundary quotients, including homological degree zero. -/
def weightedMonomialHomologyEquivPi (B : Family V) (ω : V → Γ) (γ : Γ) [Finite (FinerDegreeIndex ω γ)] (p : ℕ) :
    weightedMonomialHomology (k := k) B ω γ p ≃ₗ[k]
      ∀ α : FinerDegreeIndex ω γ, monomialFineHomology (k := k) B α.val p := by
  let f := fun α : FinerDegreeIndex ω γ => homogeneousDifferential (k := k) B α.val p
  let g := fun α : FinerDegreeIndex ω γ => monomialFinePrevious (k := k) B α.val p
  let hfg := fun α : FinerDegreeIndex ω γ => monomialFineDifferential_comp (k := k) B α.val p
  refine (threeTermHomologyEquiv (R := k)
    (X := weightedMonomialPiece (k := k) B ω γ (p+1))
    (Y := weightedMonomialPiece (k := k) B ω γ p)
    (Z := weightedMonomialPiece (k := k) B ω γ p.pred)
    (X' := ∀ α : FinerDegreeIndex ω γ, homogeneousPiece (k := k) B α.val (p+1))
    (Y' := ∀ α : FinerDegreeIndex ω γ, homogeneousPiece (k := k) B α.val p)
    (Z' := ∀ α : FinerDegreeIndex ω γ, homogeneousPiece (k := k) B α.val p.pred)
    (weightedMonomialDifferential (k := k) B ω γ p) (weightedMonomialPrevious (k := k) B ω γ p)
    (weightedMonomialDifferential_comp (k := k) B ω γ p)
    (componentwiseMap f) (componentwiseMap g) (componentwiseMap_comp f g hfg)
    (weightedMonomialPieceEquivPi (k := k) B ω γ (p+1)) (weightedMonomialPieceEquivPi (k := k) B ω γ p)
    (weightedMonomialPieceEquivPi (k := k) B ω γ p.pred) ?_ ?_).trans
      (componentwiseHomologyEquiv f g hfg)
  · intro x
    funext α
    exact weightedMonomialPieceEquivPi_differential (k := k) B ω γ p x α
  · intro x
    funext α
    exact weightedMonomialPieceEquivPi_previous (k := k) B ω γ p x α


/-- The coarsened invariant is the homology of the actual weighted Koszul
component. Its sum over fine Tor is proved through the explicit component
projection equivalence above. -/
def weightedMonomialBettiNumber (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ) : ℕ :=
  Module.finrank k (weightedMonomialHomology (k := k) B ω γ p)

theorem weightedMonomialBettiNumber_eq_sum (B : Family V) (ω : V → Γ) (γ : Γ)
    [Finite (FinerDegreeIndex ω γ)] (p : ℕ) :
    weightedMonomialBettiNumber (k := k) B ω γ p =
      ∑ α : FinerDegreeIndex ω γ, bettiNumber (k := k) B α.val p := by
  rw [weightedMonomialBettiNumber,
    (weightedMonomialHomologyEquivPi (k := k) B ω γ p).finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro α _
  exact monomialFineHomology_finrank (k := k) B α.val p

theorem weightedMonomialPiece_mem_ambient (B : Family V) (ω : V → Γ) (γ : Γ) (p : ℕ)
    (x : Set.powersetCard V p →₀ monomialIdeal k B) :
    x ∈ weightedMonomialPiece (k := k) B ω γ p ↔
      idealCoordinatesToAmbient (monomialIdeal k B) p x ∈
        Grading.Piece (quotientCoefficientBasis (k := k) (∅ : Family V) p)
          (fun b => Finsupp.weight ω (quotientDegree b)) γ := by
  rw [weightedMonomialPiece, Grading.mem_piece, Grading.mem_piece]
  constructor
  · intro hx a ha
    rw [idealCoordinatesToAmbient_repr] at ha
    have haB : Contains B a.2.val :=
      (mem_monomialIdeal_iff B (x a.1).val).mp (x a.1).property
        a.2.val (MvPolynomial.mem_support_iff.mpr ha)
    exact hx ⟨a.1, ⟨a.2.val, haB⟩⟩
      (by simpa only [monomialCoefficientBasis_repr_coeff] using ha)
  · intro hx a ha
    exact hx ⟨a.1, ⟨a.2.val, emptyFamily_allowed a.2.val⟩⟩
      (by simpa only [idealCoordinatesToAmbient_repr, monomialCoefficientBasis_repr_coeff] using ha)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def canonicalWeightedMonomialPieceEquiv (o : MonomialOrder V) (B : Family V)
    (ω : V → Γ) (γ : Γ) (p : ℕ) :
    finerIdealPiece (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω γ p ≃ₗ[k]
      weightedMonomialPiece (k := k) B ω γ p :=
  LinearEquiv.ofEq _ _ (by
    ext x
    rw [finerIdealPiece_eq_polynomial _ ω (monomialIdeal_weighted_homogeneous B ω)]
    exact (weightedMonomialPiece_mem_ambient (k := k) B ω γ p x).symm)

def canonicalWeightedMonomialHomologyEquiv (o : MonomialOrder V) (B : Family V)
    (ω : V → Γ) (γ : Γ) (p : ℕ) :
    finerIdealHomology (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω
      (monomialIdeal_weighted_homogeneous B ω) γ p ≃ₗ[k]
      weightedMonomialHomology (k := k) B ω γ p := by
  apply threeTermHomologyEquiv (R := k)
    (X := finerIdealPiece (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω γ (p+1))
    (Y := finerIdealPiece (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω γ p)
    (Z := finerIdealPiece (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω γ p.pred)
    (X' := weightedMonomialPiece (k := k) B ω γ (p+1))
    (Y' := weightedMonomialPiece (k := k) B ω γ p)
    (Z' := weightedMonomialPiece (k := k) B ω γ p.pred)
    (finerIdealDifferential _ ω (monomialIdeal_weighted_homogeneous B ω) γ p)
    (finerIdealPrevious _ ω (monomialIdeal_weighted_homogeneous B ω) γ p)
    (finerIdealDifferential_comp _ ω (monomialIdeal_weighted_homogeneous B ω) γ p)
    (weightedMonomialDifferential (k := k) B ω γ p) (weightedMonomialPrevious (k := k) B ω γ p)
    (weightedMonomialDifferential_comp (k := k) B ω γ p)
    (canonicalWeightedMonomialPieceEquiv (k := k) o B ω γ (p+1))
    (canonicalWeightedMonomialPieceEquiv (k := k) o B ω γ p)
    (canonicalWeightedMonomialPieceEquiv (k := k) o B ω γ p.pred)
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    cases p <;> rfl

theorem canonicalWeightedMonomialBettiNumber_eq (o : MonomialOrder V) (B : Family V)
    (ω : V → Γ) (γ : Γ) (p : ℕ) :
    finerIdealBettiNumber (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω
        (monomialIdeal_weighted_homogeneous B ω) p γ =
      weightedMonomialBettiNumber (k := k) B ω γ p := by
  change Module.finrank k (finerIdealGradedTor
      (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω
      (monomialIdeal_weighted_homogeneous B ω) γ p) =
    Module.finrank k (weightedMonomialHomology (k := k) B ω γ p)
  exact (finerIdealGradedTorEquiv
    (canonicalQuotientGroebnerData o (monomialIdeal k B)) ω
    (monomialIdeal_weighted_homogeneous B ω) γ p).finrank_eq.symm.trans
      (canonicalWeightedMonomialHomologyEquiv (k := k) o B ω γ p).finrank_eq

/-- The finest weight is the actual exponent vector of a variable. -/
def finestVariableWeight (v : V) : Exponent V := Finsupp.single v 1

@[simp] theorem weight_finestVariableWeight (a : Exponent V) :
    Finsupp.weight (finestVariableWeight (V := V)) a = a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single v n =>
      simp only [Finsupp.weight_single, finestVariableWeight, Finsupp.smul_single,
        nsmul_eq_mul, mul_one, Nat.cast_id]

/-- Coarsening to the exponent lattice is the identity on the genuine fine
Tor dimensions. The fiber consists of the single actual exponent. -/
theorem weightedMonomialBettiNumber_finest (B : Family V) (α : Exponent V) (p : ℕ) :
    weightedMonomialBettiNumber (k := k) B finestVariableWeight α p =
      bettiNumber (k := k) B α p := by
  let a : FinerDegreeIndex (finestVariableWeight (V := V)) α :=
    ⟨α, weight_finestVariableWeight α⟩
  have hu : ∀ b : FinerDegreeIndex (finestVariableWeight (V := V)) α, b = a := by
    intro b
    apply Subtype.ext
    exact (weight_finestVariableWeight b.val).symm.trans b.property
  letI : Unique (FinerDegreeIndex (finestVariableWeight (V := V)) α) := ⟨⟨a⟩, hu⟩
  rw [weightedMonomialBettiNumber_eq_sum, Finset.sum_eq_single a]
  · intro b _ hba
    exact False.elim (hba (hu b))
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.weightedMonomialHomologyEquivPi

#print axioms FourPapers.Sublattice.weightedMonomialBettiNumber_eq_sum

#print axioms FourPapers.Sublattice.canonicalWeightedMonomialBettiNumber_eq

#print axioms FourPapers.Sublattice.weightedMonomialBettiNumber_finest

end
end
end


end
