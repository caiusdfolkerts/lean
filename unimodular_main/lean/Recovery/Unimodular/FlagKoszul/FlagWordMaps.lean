module

public import Recovery.Unimodular.FlagKoszul.FlagBasis
public import Recovery.Unimodular.FlagKoszul.CoefficientExactness
public import Recovery.Unimodular.FlagKoszul.HomogeneousProjection

/-!
# The actual variable-ideal sequence on homogeneous bar chains

Every map is induced by the ordinary A-linear quotient or multiplication map.
Homogeneous preimages are obtained by the explicitly defined degree projection.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace Unimodular.FlagKoszul.FlagBar

variable {E K : Type*} [Field K]

abbrev Chain (R : E → E → Prop) (S : Set E) (K : Type*) [Field K] :=
  List (Positive R) →₀ QuotientModule R S K

def coefficientDegree (R : E → E → Prop) (S : Set E) (u : Point R S) : ℕ := u.1.degree

def piece (R : E → E → Prop) (S : Set E) (r N : ℕ) : Submodule K (Chain R S K) :=
  HomogeneousWords.piece (quotientBasis R S) (positiveDegree R) (coefficientDegree R S) r N

def boundary (R : E → E → Prop) (S : Set E) : Chain R S K →ₗ[FlagAlgebra R K] Chain R S K :=
  CoefficientModuleBar.differential (augmentedBasis R)

theorem boundary_squared (R : E → E → Prop) (S : Set E) (z : Chain R S K) :
    boundary R S (boundary R S z) = 0 :=
  CoefficientModuleBar.differential_squared (augmentation R) (augmentedBasis R)
    (augmentedBasis_none R) (augmentation_basis_some R) z

def projection (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T) :
    Chain R S K →ₗ[FlagAlgebra R K] Chain R T K :=
  CoefficientModuleBar.map (quotientProjection R hST)

theorem projection_boundary (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T)
    (z : Chain R S K) : projection R hST (boundary R S z) = boundary R T (projection R hST z) := by
  have h := CoefficientModuleBar.map_differential (augmentedBasis R) (quotientProjection R hST) z
  exact h

theorem projection_degree (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T)
    (u : Point R S) (v : Point R T)
    (h : (quotientBasis R T (K := K)).repr (quotientProjection R hST (quotientBasis R S u)) v ≠ 0) :
    coefficientDegree R T v = coefficientDegree R S u + 0 := by
  classical
  by_cases hu : Allowed R T u.1
  · let w : Point R T := ⟨u.1, hu⟩
    have he : quotientProjection R hST (quotientBasis R S (K := K) u) = quotientBasis R T w := by
      exact quotientProjection_basis_of_allowed R hST u hu
    rw [he, Module.Basis.repr_self] at h
    have hw : w = v := by
      by_contra hne
      exact h (by simp [Finsupp.single_apply, hne])
    subst v
    exact (Nat.add_zero _).symm
  · rw [quotientProjection_basis_of_not_allowed R hST u hu, map_zero, Finsupp.zero_apply] at h
    exact (h rfl).elim

theorem projection_mem_piece (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T)
    {r N : ℕ} {z : Chain R S K} (hz : z ∈ piece R S r N) :
    projection R hST z ∈ piece R T r N := by
  simpa only [Nat.add_zero, piece, projection, CoefficientModuleBar.map,
    Finsupp.mapRange.linearMap_apply, LinearMap.coe_restrictScalars, LinearMap.restrictScalars_apply] using
    HomogeneousWords.coefficientMap_mem_piece
    (quotientBasis R S) (quotientBasis R T) (positiveDegree R)
    (coefficientDegree R S) (coefficientDegree R T)
    ((quotientProjection R hST (K := K)).restrictScalars K) 0
    (projection_degree R hST) hz

theorem projection_homogeneous_preimage (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T)
    {r N : ℕ} {z : Chain R T K} (hz : z ∈ piece R T r N) :
    ∃ y ∈ piece R S r N, projection R hST y = z := by
  apply HomogeneousWords.exists_homogeneous_preimage
    (quotientBasis R S) (quotientBasis R T) (positiveDegree R)
    (coefficientDegree R S) (coefficientDegree R T)
    ((quotientProjection R hST (K := K)).restrictScalars K) 0
    (projection_degree R hST) (by simpa only [Nat.add_zero, piece] using hz)
  exact CoefficientModuleBar.map_surjective (quotientProjection R hST)
    (quotientProjection_surjective R hST) z

def injection {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    Chain R (S ∪ neighbors R j) K →ₗ[FlagAlgebra R K] Chain R S K :=
  CoefficientModuleBar.map (variableInjection hrefl hsymm hj)

theorem injection_injective {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    Function.Injective (injection hrefl hsymm hj (K := K)) :=
  CoefficientModuleBar.map_injective (variableInjection hrefl hsymm hj)
    (variableInjection_injective hrefl hsymm hj)

theorem injection_boundary {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (z : Chain R (S ∪ neighbors R j) K) :
    injection hrefl hsymm hj (boundary R (S ∪ neighbors R j) z) =
      boundary R S (injection hrefl hsymm hj z) := by
  have h := CoefficientModuleBar.map_differential (augmentedBasis R) (variableInjection hrefl hsymm hj) z
  exact h

theorem injection_projection_zero {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (z : Chain R (S ∪ neighbors R j) K) :
    projection R (Set.subset_insert j S) (injection hrefl hsymm hj z) = 0 :=
  CoefficientModuleBar.map_comp_zero (variableInjection hrefl hsymm hj)
    (quotientProjection R (Set.subset_insert j S))
    (variableInjection_projection_zero hrefl hsymm hj) z

theorem injection_degree {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    (u : Point R (S ∪ neighbors R j)) (v : Point R S)
    (h : (quotientBasis R S (K := K)).repr
      (variableInjection hrefl hsymm hj (quotientBasis R (S ∪ neighbors R j) u)) v ≠ 0) :
    coefficientDegree R S v = coefficientDegree R (S ∪ neighbors R j) u + 1 := by
  classical
  rw [variableInjection_basis, Module.Basis.repr_self] at h
  have he : raisePoint hrefl hsymm hj u = v := by
    by_contra hne
    exact h (by simp [Finsupp.single_apply, hne])
  subst v
  exact raisePoint_degree hrefl hsymm hj u

theorem injection_mem_piece {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    {r N : ℕ} {z : Chain R (S ∪ neighbors R j) K} (hz : z ∈ piece R (S ∪ neighbors R j) r N) :
    injection hrefl hsymm hj z ∈ piece R S r (N + 1) :=
  HomogeneousWords.coefficientMap_mem_piece
    (quotientBasis R (S ∪ neighbors R j)) (quotientBasis R S) (positiveDegree R)
    (coefficientDegree R (S ∪ neighbors R j)) (coefficientDegree R S)
    ((variableInjection hrefl hsymm hj (K := K)).restrictScalars K) 1
    (injection_degree hrefl hsymm hj) hz

theorem kernel_homogeneous_preimage {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S)
    {r N : ℕ} (hN : 0 < N) {z : Chain R S K} (hz : z ∈ piece R S r N)
    (hπz : projection R (Set.subset_insert j S) z = 0) :
    ∃ y ∈ piece R (S ∪ neighbors R j) r (N - 1), injection hrefl hsymm hj y = z := by
  apply HomogeneousWords.exists_homogeneous_preimage_sub
    (quotientBasis R (S ∪ neighbors R j)) (quotientBasis R S) (positiveDegree R)
    (coefficientDegree R (S ∪ neighbors R j)) (coefficientDegree R S)
    ((variableInjection hrefl hsymm hj (K := K)).restrictScalars K) 1
    (injection_degree hrefl hsymm hj) (by omega) hz
  exact CoefficientModuleBar.map_kernel_preimage (variableInjection hrefl hsymm hj)
    (quotientProjection R (Set.subset_insert j S))
    (variableProjection_kernel_preimage hrefl hsymm hj) z hπz

#print axioms projection_homogeneous_preimage
#print axioms injection_mem_piece
#print axioms kernel_homogeneous_preimage

end Unimodular.FlagKoszul.FlagBar

#check Unimodular.FlagKoszul.FlagBar.kernel_homogeneous_preimage
