module

public import Recovery.Unimodular.FlagKoszul.FlagWordMaps
public import Recovery.Unimodular.FlagKoszul.FlagQuotientGrading
public import Recovery.Unimodular.FlagKoszul.FreeBarGrading
public import Recovery.Unimodular.FlagKoszul.CoefficientDegree

/-!
# Homogeneous exactness of the genuine flag-algebra coefficient bar complexes

The proof uses the actual variable quotient modules and the actual multiplication
maps. All homogeneous lifting premises are established from their monomial bases.
The two inductions cover every finite set of variables and every internal degree.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.FlagKoszul.FlagBar

variable {E K : Type*} [Field K]

 theorem boundary_mem_piece (R : E → E → Prop) (S : Set E)
    {r N : ℕ} {z : Chain R S K} (hz : z ∈ piece R S (r + 1) N) :
    boundary R S z ∈ piece R S r N :=
  CoefficientDegree.differential_mem_piece (augmentedBasis R (K := K)) (quotientBasis R S)
    (positiveDegree R) (coefficientDegree R S) (product_degree R)
    (quotient_action_degree R S) hz

theorem boundary_zero_length (R : E → E → Prop) (S : Set E)
    {N : ℕ} {z : Chain R S K} (hz : z ∈ piece R S 0 N) : boundary R S z = 0 :=
  CoefficientDegree.differential_zero_length (augmentedBasis R (K := K)) (quotientBasis R S)
    (positiveDegree R) (coefficientDegree R S) hz

theorem option_degree (R : E → E → Prop) (o : Option (Positive R)) :
    FreeBarGrading.coefficientDegree (positiveDegree R) o =
      ((pointOptionEquiv R) o).1.degree := by
  cases o with
  | none => simp [FreeBarGrading.coefficientDegree, pointOptionEquiv, zeroPoint]
  | some u => rfl

theorem empty_toFree_degree (R : E → E → Prop) (u : Point R ∅) (o : Option (Positive R))
    (h : (augmentedBasis R (K := K)).repr (quotientEmptyEquiv R (quotientBasis R ∅ u)) o ≠ 0) :
    FreeBarGrading.coefficientDegree (positiveDegree R) o = coefficientDegree R ∅ u + 0 := by
  classical
  rw [quotientEmptyEquiv_basis_option, Module.Basis.repr_self] at h
  have he : (pointOptionEquiv R).symm u = o := by
    by_contra hne
    exact h (by simp [Finsupp.single_apply, hne])
  rw [← he, option_degree, Equiv.apply_symm_apply]
  exact (Nat.add_zero _).symm

theorem empty_fromFree_basis (R : E → E → Prop) (o : Option (Positive R)) :
    (quotientEmptyEquiv R (K := K)).symm (augmentedBasis R (K := K) o) =
      quotientBasis R ∅ ((pointOptionEquiv R) o) := by
  apply (quotientEmptyEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, quotientEmptyEquiv_basis_option, Equiv.symm_apply_apply]

theorem empty_fromFree_degree (R : E → E → Prop) (o : Option (Positive R)) (u : Point R ∅)
    (h : (quotientBasis R ∅ (K := K)).repr
      ((quotientEmptyEquiv R).symm (augmentedBasis R (K := K) o)) u ≠ 0) :
    coefficientDegree R ∅ u = FreeBarGrading.coefficientDegree (positiveDegree R) o + 0 := by
  classical
  rw [empty_fromFree_basis, Module.Basis.repr_self] at h
  have he : (pointOptionEquiv R) o = u := by
    by_contra hne
    exact h (by simp [Finsupp.single_apply, hne])
  rw [← he, option_degree]
  exact (Nat.add_zero _).symm

/-- Homogeneous exactness of A/J_empty is the explicitly contracted free bar
resolution, transported through the actual quotient-by-zero equivalence. -/
theorem empty_cycle_is_boundary (R : E → E → Prop) {r N : ℕ}
    (hN : 0 < N) {z : Chain R ∅ K} (hz : z ∈ piece R ∅ r N)
    (hdz : boundary R ∅ z = 0) : ∃ y ∈ piece R ∅ (r + 1) N, boundary R ∅ y = z := by
  let f := (quotientEmptyEquiv R (K := K)).toLinearMap
  let g := (quotientEmptyEquiv R (K := K)).symm.toLinearMap
  let w := CoefficientModuleBar.map f z
  have hw : w ∈ HomogeneousWords.piece (augmentedBasis R (K := K)) (positiveDegree R)
      (FreeBarGrading.coefficientDegree (positiveDegree R)) r N := by
    simpa only [Nat.add_zero, w, CoefficientModuleBar.map,
      Finsupp.mapRange.linearMap_apply, LinearMap.coe_restrictScalars,
      LinearMap.restrictScalars_apply] using HomogeneousWords.coefficientMap_mem_piece
      (quotientBasis R ∅) (augmentedBasis R (K := K)) (positiveDegree R) (coefficientDegree R ∅)
      (FreeBarGrading.coefficientDegree (positiveDegree R)) (f.restrictScalars K) 0
      (empty_toFree_degree R) hz
  have hdw : CoefficientModuleBar.differential (augmentedBasis R (K := K)) w = 0 := by
    change CoefficientModuleBar.differential (augmentedBasis R (K := K))
      (CoefficientModuleBar.map f z) = 0
    rw [← CoefficientModuleBar.map_differential]
    change CoefficientModuleBar.map f (boundary R ∅ z) = 0
    rw [hdz, map_zero]
  obtain ⟨v, hv, hdv⟩ := FreeBarGrading.homogeneous_cycle_is_boundary
    (augmentation R) (augmentedBasis R (K := K)) (augmentedBasis_none R)
    (augmentation_basis_some R) (positiveDegree R) hN hw hdw
  refine ⟨CoefficientModuleBar.map g v, ?_, ?_⟩
  · simpa only [Nat.add_zero, piece, CoefficientModuleBar.map,
      Finsupp.mapRange.linearMap_apply, LinearMap.coe_restrictScalars,
      LinearMap.restrictScalars_apply] using HomogeneousWords.coefficientMap_mem_piece
      (augmentedBasis R (K := K)) (quotientBasis R ∅) (positiveDegree R)
      (FreeBarGrading.coefficientDegree (positiveDegree R)) (coefficientDegree R ∅)
      (g.restrictScalars K) 0 (empty_fromFree_degree R) hv
  · change CoefficientModuleBar.differential (augmentedBasis R (K := K)) (CoefficientModuleBar.map g v) = z
    rw [← CoefficientModuleBar.map_differential, hdv]
    ext L
    exact (quotientEmptyEquiv R).symm_apply_apply (z L)

/-- In bar degree zero, positive internal-degree cycles in every variable
quotient lift to the explicitly contracted free coefficient complex. -/
theorem zero_cycle_is_boundary (R : E → E → Prop) (S : Set E) {N : ℕ}
    (hN : 0 < N) {z : Chain R S K} (hz : z ∈ piece R S 0 N) :
    ∃ y ∈ piece R S 1 N, boundary R S y = z := by
  obtain ⟨b, hb, hπb⟩ := projection_homogeneous_preimage R (Set.empty_subset S) hz
  obtain ⟨y, hy, hdy⟩ := empty_cycle_is_boundary R hN hb (boundary_zero_length R ∅ hb)
  refine ⟨projection R (Set.empty_subset S) y, projection_mem_piece R _ hy, ?_⟩
  rw [← projection_boundary, hdy, hπb]

def ExactAt (R : E → E → Prop) (S : Set E) (r N : ℕ) : Prop :=
  ∀ z : Chain R S K, z ∈ piece R S r N → boundary R S z = 0 →
    ∃ y ∈ piece R S (r + 1) N, boundary R S y = z

/-- The full Koszul-filtration conclusion, for the actual flag algebra and
its actual variable quotients. No exactness premise remains. -/
theorem exact_all_variable_quotients [Fintype E] {R : E → E → Prop}
    (hrefl : ∀ i, R i i) (hsymm : ∀ {i j}, R i j → R j i) :
    ∀ (S : Set E) (r N : ℕ), r < N → ExactAt (K := K) R S r N := by
  classical
  suffices hfin : ∀ (S : Finset E) (r N : ℕ), r < N → ExactAt (K := K) R (S : Set E) r N by
    intro S r N hN
    simpa only [Set.coe_toFinset] using hfin S.toFinset r N hN
  intro S r
  induction r generalizing S with
  | zero =>
    intro N hN z hz hdz
    exact zero_cycle_is_boundary R S hN hz
  | succ r ih =>
    intro N hNr
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty]
      intro z hz hdz
      exact empty_cycle_is_boundary (K := K) R (r := r + 1) (N := N) (by omega) hz hdz
    | @insert j S hj hS =>
      rw [Finset.coe_insert]
      intro z hz hdz
      obtain ⟨b, hb, hπb⟩ := projection_homogeneous_preimage (K := K) R
        (Set.subset_insert j (S : Set E)) (r := r + 1) (N := N) hz
      have hdb : boundary R (S : Set E) b ∈ piece R (S : Set E) r N :=
        boundary_mem_piece (K := K) R (S : Set E) (r := r) (N := N) hb
      have hπdb : projection R (Set.subset_insert j (S : Set E)) (boundary R S b) = 0 := by
        rw [projection_boundary, hπb, hdz]
      obtain ⟨a, ha, hιa⟩ := kernel_homogeneous_preimage (K := K)
        (R := R) (S := (S : Set E)) (j := j) hrefl hsymm hj
        (r := r) (N := N) (by omega) hdb hπdb
      have hda : boundary R ((S : Set E) ∪ neighbors R j) a = 0 := by
        apply injection_injective (K := K) (R := R) (S := (S : Set E)) (j := j) hrefl hsymm hj
        rw [map_zero, injection_boundary, hιa, boundary_squared]
      have hcolon : ExactAt (K := K) R ((S : Set E) ∪ neighbors R j) r (N - 1) := by
        simpa only [Set.coe_toFinset] using
          ih (((S : Set E) ∪ neighbors R j).toFinset) (N - 1) (by omega)
      obtain ⟨v, hv, hdv⟩ := hcolon a ha hda
      have hιv : injection hrefl hsymm hj v ∈ piece R (S : Set E) (r + 1) N := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using
          injection_mem_piece (K := K) (R := R) (S := (S : Set E)) (j := j)
            hrefl hsymm hj (r := r + 1) (N := N - 1) hv
      have hc : b - injection hrefl hsymm hj v ∈ piece R (S : Set E) (r + 1) N :=
        (piece R (S : Set E) (r + 1) N).sub_mem hb hιv
      have hdc : boundary R (S : Set E) (b - injection hrefl hsymm hj v) = 0 := by
        rw [map_sub, ← injection_boundary, hdv, hιa, sub_self]
      obtain ⟨y, hy, hdy⟩ := hS (b - injection hrefl hsymm hj v) hc hdc
      refine ⟨projection R (Set.subset_insert j (S : Set E)) y,
        projection_mem_piece R _ hy, ?_⟩
      rw [← projection_boundary, hdy, map_sub, injection_projection_zero, sub_zero, hπb]

#print axioms empty_cycle_is_boundary
#print axioms zero_cycle_is_boundary
#print axioms exact_all_variable_quotients

end Unimodular.FlagKoszul.FlagBar

#check Unimodular.FlagKoszul.FlagBar.exact_all_variable_quotients
