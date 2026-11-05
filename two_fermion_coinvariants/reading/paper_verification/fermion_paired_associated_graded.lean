module

public import PaperVerification.FermionGradedAlgebraComparison
public import PaperVerification.FermionPairedInitial

/-!
# The paired associated graded is the actual homogeneous power algebra

The filtration is the image of the original weighted polynomial/exterior
monomials. Its multiplication is induced from the literal two-sided quotient.
The canonical comparison sends a bounded representative to its highest form.
Every input to the generic comparison is derived from the actual paired
relations and the proved original basis candidate.

-/

@[expose] public section
set_option maxHeartbeats 100000
set_option profiler true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct DirectSum

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedAssociatedGraded_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

private theorem exterior_empty_one :
    (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (∅ : Finset (OddIndex n))=1 := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  simp

theorem super_weighted_one_homogeneous (w : Fin n → ℕ) (ν : OddIndex n → ℕ) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (superMonomialWeight w ν) 0 1 := by
  have h := hasTop_tmul_word (K := R) w ν 1 1 0 (Filtered.HasTop.one w) ∅
  have he : (1 : PolynomialRing R n) ⊗ₜ[R]
      (Pi.basisFun R (OddIndex n)).ExteriorAlgebra ∅=(1 : SuperRing R n) := by
    rw [exterior_empty_one,Algebra.TensorProduct.one_def]
  simp only [wordPolynomialWeight,Finset.sum_empty,add_zero,he] at h
  have hh := BasisFiltered.homogeneous_component (superMonomialBasis (K := R))
    (superMonomialWeight w ν) 0 (1 : SuperRing R n)
  rwa [h.2] at hh

theorem super_weighted_basis_mul_homogeneous (w : Fin n → ℕ) (ν : OddIndex n → ℕ)
    (L T : SuperMonomialIndex n) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (superMonomialWeight w ν)
      (superMonomialWeight w ν L+superMonomialWeight w ν T)
      (superMonomialBasis L*superMonomialBasis T) := by
  have h := hasTop_basis_multiples (K := R) w ν 1 1 0 (Filtered.HasTop.one w) ∅ L T
  have he : (1 : PolynomialRing R n) ⊗ₜ[R]
      (Pi.basisFun R (OddIndex n)).ExteriorAlgebra ∅=(1 : SuperRing R n) := by
    rw [exterior_empty_one,Algebra.TensorProduct.one_def]
  simp only [wordPolynomialWeight,Finset.sum_empty,zero_add,add_zero,he,mul_one] at h
  have hh := BasisFiltered.homogeneous_component (superMonomialBasis (K := R))
    (superMonomialWeight w ν)
    (superMonomialWeight w ν L+superMonomialWeight w ν T)
    (superMonomialBasis L*superMonomialBasis T)
  rwa [h.2] at hh

def pairedSuperWeight (d : PairedData (K := R) (n := n)) : SuperMonomialIndex n → ℕ :=
  superMonomialWeight (coveringWeight d.r) (pairedOddWeight d)

/-- The actual filtration of the original paired quotient. -/
def pairedQuotientFiltration (d : PairedData (K := R) (n := n)) :
    FilteredAlgebra.Filtration R (PairedQuotient d.beta d.phi d.a d.b) :=
  BasisFiltered.quotientFiltration (superMonomialBasis (K := R)) (pairedSuperWeight d)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))

abbrev PairedAssociatedGraded (d : PairedData (K := R) (n := n)) :=
  FilteredAlgebra.AssociatedGraded (pairedQuotientFiltration d)

/-- The actual homogeneous degree piece in the power quotient. -/
def pairedPowerWeightedPiece (d : PairedData (K := R) (n := n)) (k : ℕ) :
    Submodule R (PairedQuotient d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (pairedSuperWeight d) k).map
    ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap

theorem pairedPower_kernel_eq_relationSpan (d : PairedData (K := R) (n := n)) :
    (((pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap).ker =
      Submodule.span R (Set.range (basisRelationMultiple (superMonomialBasis (K := R))
        (pairedPowerFiniteRelation d))) := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule,← pairedPowerFiniteRelation_ideal d,
    twoSidedIdealSubmodule_span]

theorem pairedPower_kernel_component (d : PairedData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n)
    (hx : x ∈ (((pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap).ker) :
    BasisFiltered.component (superMonomialBasis (K := R)) (pairedSuperWeight d) k x ∈
      (((pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap).ker := by
  rw [pairedPower_kernel_eq_relationSpan] at hx ⊢
  apply BasisFiltered.component_mem_span (superMonomialBasis (K := R)) (pairedSuperWeight d)
    (basisRelationMultiple superMonomialBasis (pairedPowerFiniteRelation d))
    (pairedRelationMultipleDegree d) _ x hx k
  intro z
  have h := BasisFiltered.homogeneous_component (superMonomialBasis (K := R)) (pairedSuperWeight d)
    (pairedRelationMultipleDegree d z)
    (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z)
  simp only [pairedSuperWeight] at h
  rwa [(pairedRelationMultiple_hasTop d z).2] at h

theorem pairedPowerWeighted_isInternal (d : PairedData (K := R) (n := n)) :
    DirectSum.IsInternal (pairedPowerWeightedPiece d) := by
  let q₀ : SuperRing R n →ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) :=
    (pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R
  have hclass (z : PairedPowerIndex d.r d.u d.v d.s) :
      q₀ (superMonomialBasis (z.2.val.val,z.1)) =
        pairedArbitraryRingBasis d.power z := by
    exact (congrArg q₀ (superMonomialBasis_apply (K := R) (z.2.val.val,z.1))).trans
      (pairedArbitraryRingBasis_apply d.power
        (show PairedPowerIndex d.power.r d.power.u d.power.v d.power.s from z)).symm
  exact BasisFiltered.homogeneousQuotient_isInternal
    (R := R) (M := SuperRing R n)
    (Q := PairedQuotient d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i))
    (I := SuperMonomialIndex n) (E := PairedPowerIndex d.r d.u d.v d.s)
    (superMonomialBasis (K := R)) (pairedSuperWeight d) q₀.toLinearMap
    (pairedArbitraryRingBasis d.power)
    (fun z : PairedPowerIndex d.r d.u d.v d.s ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ pairedSuperWeight d (z.2.val.val,z.1))
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    hclass (pairedPower_kernel_component d)

theorem paired_initial_kernel_le_power (d : PairedData (K := R) (n := n)) :
    BasisFiltered.initialSubmodule (superMonomialBasis (K := R)) (pairedSuperWeight d)
      (((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap).ker ≤
      (((pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap).ker := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule,quotient_kernel_eq_twoSidedIdealSubmodule]
  exact (paired_initialSubmodule_eq_power d).le

set_option diagnostics true

section SymbolicQuotients

variable (I I₀ : TwoSidedIdeal (SuperRing R n))
  (b : Module.Basis (SuperMonomialIndex n) R (SuperRing R n))
  (w : SuperMonomialIndex n → ℕ)
  (hone : BasisFiltered.Homogeneous b w 0 (1 : SuperRing R n))
  (hmul : ∀ i j, BasisFiltered.Homogeneous b w (w i + w j) (b i * b j))
  (f g : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n →
    SuperRing R n)
  (degree : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n → ℕ)
  (hf : ∀ j, BasisFiltered.HasTop b w (degree j) (f j) (g j))
  (hker : (I.ringCon.mkₐ R).toLinearMap.ker = Submodule.span R (Set.range f))
  (hker₀ : (I₀.ringCon.mkₐ R).toLinearMap.ker = Submodule.span R (Set.range g))
  (hinitial : BasisFiltered.initialSubmodule b w (I.ringCon.mkₐ R).toLinearMap.ker ≤
    (I₀.ringCon.mkₐ R).toLinearMap.ker)

set_option maxHeartbeats 100000 in
/-- Specialize the comparison at symbolic actual quotient ideals. This resolves
all RingCon/module dictionaries before any moment ideal is substituted. -/
def pairedSymbolicComparisonHom :
    FilteredAlgebra.AssociatedGraded
        (BasisFiltered.quotientFiltration
          (R := R) (A := SuperRing R n) (Q := I.ringCon.Quotient)
          (I := SuperMonomialIndex n) b w (I.ringCon.mkₐ R) hone hmul) →ₐ[R]
      I₀.ringCon.Quotient :=
by
  let result :=
    BasisFiltered.gradedAlgebraComparison
      (R := R) (A := SuperRing R n)
      (Q := I.ringCon.Quotient) (Q₀ := I₀.ringCon.Quotient)
      (I := SuperMonomialIndex n)
      (J := SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n)
      b w (I.ringCon.mkₐ R) (I₀.ringCon.mkₐ R) hone hmul
      f g degree hf (by
        apply Submodule.ext
        intro x
        change (I.ringCon.mkₐ R) x = 0 ↔ x ∈ Submodule.span R (Set.range f)
        exact (SetLike.ext_iff.mp hker) x) (by
        apply Submodule.ext
        intro x
        change (I₀.ringCon.mkₐ R) x = 0 ↔ x ∈ Submodule.span R (Set.range g)
        exact (SetLike.ext_iff.mp hker₀) x) (by
        intro x hx
        change (I₀.ringCon.mkₐ R) x = 0
        exact hinitial hx)
  exact result

set_option maxHeartbeats 100000 in
theorem pairedSymbolicComparisonHom_bijective
    (hgrading : DirectSum.IsInternal
      (fun k ↦ (BasisFiltered.homogeneousPiece b w k).map (I₀.ringCon.mkₐ R).toLinearMap)) :
    Function.Bijective
      (pairedSymbolicComparisonHom I I₀ b w hone hmul f g degree hf hker hker₀ hinitial) :=
by
  let result :=
    BasisFiltered.gradedAlgebraComparison_bijective
      (R := R) (A := SuperRing R n)
      (Q := I.ringCon.Quotient) (Q₀ := I₀.ringCon.Quotient)
      (I := SuperMonomialIndex n)
      (J := SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n)
      b w (I.ringCon.mkₐ R) (I₀.ringCon.mkₐ R) hone hmul
      f g degree hf (by
        apply Submodule.ext
        intro x
        change (I.ringCon.mkₐ R) x = 0 ↔ x ∈ Submodule.span R (Set.range f)
        exact (SetLike.ext_iff.mp hker) x) (by
        apply Submodule.ext
        intro x
        change (I₀.ringCon.mkₐ R) x = 0 ↔ x ∈ Submodule.span R (Set.range g)
        exact (SetLike.ext_iff.mp hker₀) x) (by
        intro x hx
        change (I₀.ringCon.mkₐ R) x = 0
        exact hinitial hx) (by
        constructor
        · intro x y hxy
          apply hgrading.1
          exact hxy
        · intro y
          obtain ⟨x,hx⟩ := hgrading.2 y
          exact ⟨x,hx⟩)
  exact result

end SymbolicQuotients

set_option maxHeartbeats 100000 in
/-- The actual highest-component algebra homomorphism, now using the comparison
already specialized at symbolic quotient ideals. -/
def pairedAssociatedGradedHom (d : PairedData (K := R) (n := n)) :
    PairedAssociatedGraded d →ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) :=
  pairedSymbolicComparisonHom (R := R) (n := n)
      (pairedIdeal d.beta d.phi d.a d.b)
      (pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i))
      (superMonomialBasis (K := R) (n := n)) (pairedSuperWeight d)
      (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
      (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
      (basisRelationMultiple (superMonomialBasis (K := R) (n := n))
        (pairedFiniteRelation d))
      (basisRelationMultiple (superMonomialBasis (K := R) (n := n))
        (pairedPowerFiniteRelation d))
      (pairedRelationMultipleDegree d) (pairedRelationMultiple_hasTop d)
      (paired_quotient_kernel_eq_relationSpan R d)
      (pairedPower_kernel_eq_relationSpan d)
      (paired_initial_kernel_le_power d)

set_option maxHeartbeats 100000 in
theorem pairedAssociatedGradedHom_bijective
    (d : PairedData (K := R) (n := n)) :
    Function.Bijective (pairedAssociatedGradedHom d) :=
  pairedSymbolicComparisonHom_bijective (R := R) (n := n)
      (pairedIdeal d.beta d.phi d.a d.b)
      (pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i))
      (superMonomialBasis (K := R) (n := n)) (pairedSuperWeight d)
      (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
      (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
      (basisRelationMultiple (superMonomialBasis (K := R) (n := n))
        (pairedFiniteRelation d))
      (basisRelationMultiple (superMonomialBasis (K := R) (n := n))
        (pairedPowerFiniteRelation d))
      (pairedRelationMultipleDegree d) (pairedRelationMultiple_hasTop d)
      (paired_quotient_kernel_eq_relationSpan R d)
      (pairedPower_kernel_eq_relationSpan d)
      (paired_initial_kernel_le_power d)
      (pairedPowerWeighted_isInternal d)

set_option maxHeartbeats 100000 in
/-- The exact algebra statement in the associated-graded clause of Theorem 1.1.
The ring structure on the source was constructed from actual quotient products. -/
def pairedAssociatedGradedEquiv (d : PairedData (K := R) (n := n)) :
    PairedAssociatedGraded d ≃ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) :=
  AlgEquiv.ofBijective (pairedAssociatedGradedHom d)
    (pairedAssociatedGradedHom_bijective d)

/-- On each actual filtered representative, the comparison is exactly the
class of its highest weighted form. -/
@[simp] theorem pairedAssociatedGradedEquiv_of_projection
    (d : PairedData (K := R) (n := n)) (k : ℕ)
    (x : BasisFiltered.boundPiece (superMonomialBasis (K := R)) (pairedSuperWeight d) k) :
    pairedAssociatedGradedEquiv d
      (DirectSum.of (FilteredAlgebra.GradedPiece (pairedQuotientFiltration d)) k
        (BasisFiltered.gradedProjection
          (R := R) (A := SuperRing R n) (Q := PairedQuotient d.beta d.phi d.a d.b)
          (I := SuperMonomialIndex n)
          (superMonomialBasis (K := R)) (pairedSuperWeight d)
          ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R)
          (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d)) (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d)) k x)) =
      ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
        (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R)
        (BasisFiltered.component (superMonomialBasis (K := R)) (pairedSuperWeight d) k x) :=
  BasisFiltered.associatedGradedComparison_of_projection
    _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      constructor
      · intro a b hab
        apply (pairedPowerWeighted_isInternal d).1
        exact hab
      · intro y
        obtain ⟨a,ha⟩ := (pairedPowerWeighted_isInternal d).2 y
        exact ⟨a,ha⟩) k x

/-- The canonical equivalence is graded: the image of every actual graded
summand is exactly the homogeneous power-quotient piece of the same weight. -/
theorem pairedAssociatedGradedEquiv_range (d : PairedData (K := R) (n := n)) (k : ℕ) :
    LinearMap.range ((pairedAssociatedGradedEquiv d).toLinearMap.comp
      (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (pairedQuotientFiltration d)) k)) =
      pairedPowerWeightedPiece d k :=
  BasisFiltered.associatedGradedComparison_range
    _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      constructor
      · intro a b hab
        apply (pairedPowerWeighted_isInternal d).1
        exact hab
      · intro y
        obtain ⟨a,ha⟩ := (pairedPowerWeighted_isInternal d).2 y
        exact ⟨a,ha⟩) k

end PaperVerification.Fermion
