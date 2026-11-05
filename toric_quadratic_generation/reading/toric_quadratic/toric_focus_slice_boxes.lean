module

public import PaperVerification.ToricFocusHeightDegrees
public import PaperVerification.ToricSliceBoxCoordinates
public import PaperVerification.ToricCanonicalSlices

@[expose] public section

/-!
# Whole tangent boxes in actual normal-height slices

The quotient-star relation is constructed from the original focus. Its
nonfiber primitive collections have the proved base-dimensional bound.
The actual displaced edge reserve and the scalar fiber degree therefore
supply every point of the ordinary or canonical tangent box.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem focus_bundle_base_dimension (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative)
    (c : (R.focusQuotientRelation hR b I hI).BundleCoordinates) :
    (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card := by
  rw [c.fiberIndices_card, R.focusQuotientRelation_fiberDimension hR b I hI]
  have hcard : I.card = R.negative.card := by
    rw [← hI, Finset.card_image_of_injective _ b.injective]
  omega

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem focus_slice_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (side : ℝ) (hside : 0 ≤ side)
    (hh : ∀ u ∈ R.negative, 0 ≤ normalHeight δ u)
    (htangent : ∀ j : Fin (n - I.card),
      0 ≤ normalHeight δ (b (complementaryEmbedding I j)) ∧
        normalHeight δ (b (complementaryEmbedding I j)) ≤ side)
    (hbudget : (∑ u ∈ R.negative, normalHeight δ u) +
      side * ((n - R.fiberDimension - R.negative.card : ℕ) : ℝ) ≤ e)
    (hfiber : side * R.fiberDimension ≤
      R.degree (displacedSupport (fun u => (a u : ℝ)) R.negative (normalHeight δ))) :
    v + δ ∈ «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let D := displacedSupport (fun u => (a u : ℝ)) (I.image b) (normalHeight δ)
  let C := «Σ».faceSupport b I hF D
  let R' := R.focusQuotientRelation hR b I hI
  let c := R'.bundleCoordinates
  have hR' : R'.IsCombinatoriallyContractible := R.focusQuotientRelation_contractible hR b I hI
  have hN' : R'.negative = ∅ := rfl
  have hr' : R'.fiberDimension = R.fiberDimension := R.focusQuotientRelation_fiberDimension hR b I hI
  have hb : (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card :=
    R.focus_bundle_base_dimension hR b I hI c
  have hhI : ∀ u ∈ I.image b, 0 ≤ normalHeight δ u := fun u hu => hh u (hI ▸ hu)
  have hsumBudget : (∑ u ∈ I.image b, normalHeight δ u) ≤ (e : ℝ) := by
    have hn : (0 : ℝ) ≤ (n - R.fiberDimension - R.negative.card : ℕ) := Nat.cast_nonneg _
    rw [hI]
    nlinarith [mul_nonneg hside hn]
  have hD : «Σ».IsNef D := «Σ».displacedSupport_isNef_of_edges hpure a ha hedges
    (I.image b) (normalHeight δ) hhI hsumBudget
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  let H := «Σ».faceSupportLattice b I hF a
  have hH : Ψ.IsStrictSupport (fun u => (H u : ℝ)) := by
    rw [show (fun u => (H u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  have hfiber' : side * R'.fiberDimension ≤ R'.degree C := by
    rw [hr', R.focusQuotientRelation_degree hR b I hI]
    simpa only [D, hI] using hfiber
  have hbase (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hQne : Q.positive ≠ R'.positive) :
      side * (((n - I.card) - c.fiberIndices.card : ℕ) : ℝ) ≤ Q.degree C := by
    rw [hb]
    have hlower := «Σ».displaced_faceSupport_degree_lower_bound b I hF hpure
      a ha he hedges (normalHeight δ) hhI hsumBudget Q hQ
    change (e : ℝ) - (∑ u ∈ I.image b, normalHeight δ u) ≤ Q.degree C at hlower
    rw [hI] at hlower
    linarith
  have hdegrees := c.all_contractible_degrees_of_fiber_and_base hR' hN' C side hside hfiber' hbase
  have hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈ Ψ.cones :=
    «Σ».quotient_of_full_basis_standard_cone b I hfull
  have hcoords := Ψ.coordinate_box_mem_fanPolytope hΨpure H hH C side hside hdegrees hstandard
    (fun j => normalHeight δ (b (complementaryEmbedding I j))) htangent
  have hpoint : (fun j => -C (Pi.basisFun ℤ (Fin (n - I.card)) j) +
      normalHeight δ (b (complementaryEmbedding I j))) = tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ := by
    funext j
    rw [show C (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) from
      «Σ».faceSupport_displaced_standard_coordinate b I hfull hF _ _ j]
    rfl
  rw [hpoint] at hcoords
  have hface : quotientFaceMap D b I (tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ) ∈
      «Σ».supportFace D (I.image b) := by
    rw [← «Σ».quotientFaceMap_image_fanPolytope b I hF hpure D hD]
    exact ⟨_, hcoords, rfl⟩
  rw [quotientFaceMap_tangentSliceCoordinates _ b I v δ hv] at hface
  rw [«Σ».displaced_supportFace_eq_slice _ _ _ hhI] at hface
  exact hface.1

theorem focus_inner_slice_box_mem
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ)))
    {e : ℕ} (he : 0 < e)
    (hedges : («Σ».supportLatticePolytope hpure a ha).EdgesAtLeast e)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hI : I.image b = R.negative) (hfull : Finset.univ.image b ∈ «Σ».cones)
    (v δ : Ambient n)
    (hv : ∀ i, (dotProductEquiv ℝ (Fin n) (embed n (b i))) v = -(a (b i) : ℝ))
    (hh : ∀ u ∈ R.negative, 1 ≤ normalHeight δ u)
    (htangent : ∀ j : Fin (n - I.card),
      1 ≤ normalHeight δ (b (complementaryEmbedding I j)) ∧
        normalHeight δ (b (complementaryEmbedding I j)) ≤ 2)
    (hbudget : (∑ u ∈ R.negative, normalHeight δ u) +
      (2 * (n - R.fiberDimension - R.negative.card : ℕ) + 1 : ℕ) ≤ e)
    (hfiber : (2 * R.fiberDimension + 1 : ℕ) ≤
      R.degree (displacedSupport (fun u => (a u : ℝ)) R.negative (normalHeight δ))) :
    v + δ ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))) := by
  let hF : I.image b ∈ «Σ».cones := hI.symm ▸ R.negative_cone
  let Ψ := «Σ».completeQuotientStarFan b I hF
  let D := displacedSupport (fun u => (a u : ℝ)) (I.image b) (normalHeight δ)
  let C := «Σ».faceSupport b I hF D
  let R' := R.focusQuotientRelation hR b I hI
  let c := R'.bundleCoordinates
  have hR' : R'.IsCombinatoriallyContractible := R.focusQuotientRelation_contractible hR b I hI
  have hN' : R'.negative = ∅ := rfl
  have hr' : R'.fiberDimension = R.fiberDimension := R.focusQuotientRelation_fiberDimension hR b I hI
  have hb : (n - I.card) - c.fiberIndices.card = n - R.fiberDimension - R.negative.card :=
    R.focus_bundle_base_dimension hR b I hI c
  have hhI : ∀ u ∈ I.image b, 1 ≤ normalHeight δ u := fun u hu => hh u (hI ▸ hu)
  have hhI0 : ∀ u ∈ I.image b, 0 ≤ normalHeight δ u := fun u hu => zero_le_one.trans (hhI u hu)
  have hsumBudget : (∑ u ∈ I.image b, normalHeight δ u) + 1 ≤ (e : ℝ) := by
    have hn : (0 : ℝ) ≤ (n - R.fiberDimension - R.negative.card : ℕ) := Nat.cast_nonneg _
    rw [hI]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hbudget
    linarith
  have hΨpure : Ψ.IsPure := «Σ».completeQuotientStarFan_isPure hpure b I hF
  let H := «Σ».faceSupportLattice b I hF a
  have hH : Ψ.IsStrictSupport (fun u => (H u : ℝ)) := by
    rw [show (fun u => (H u : ℝ)) = «Σ».faceSupport b I hF (fun u => (a u : ℝ)) from
      «Σ».faceSupportLattice_cast b I hF a]
    exact «Σ».faceSupport_isStrictSupport b I hF _ ha
  have hfiber' : (2 * R'.fiberDimension + 1 : ℕ) ≤ R'.degree C := by
    rw [hr', R.focusQuotientRelation_degree hR b I hI]
    simpa only [D, hI] using hfiber
  have hbase (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible)
      (hQne : Q.positive ≠ R'.positive) :
      (2 * ((n - I.card) - c.fiberIndices.card) + 1 : ℕ) ≤ Q.degree C := by
    rw [hb]
    have hlower := «Σ».displaced_faceSupport_degree_lower_bound b I hF hpure
      a ha he hedges (normalHeight δ) hhI0 (by linarith) Q hQ
    change (e : ℝ) - (∑ u ∈ I.image b, normalHeight δ u) ≤ Q.degree C at hlower
    rw [hI] at hlower
    linarith
  have hdegrees (Q : Ψ.PrimitiveRelation) (hQ : Q.IsCombinatoriallyContractible) :
      1 * (Q.fiberDimension : ℝ) ≤ Q.degree (fun u => C u - 1) := by
    simpa only [one_mul] using
      c.all_adjoint_contractible_degrees_of_fiber_and_base hR' hN' C hfiber' hbase Q hQ
  have hstandard : Finset.univ.image (Pi.basisFun ℤ (Fin (n - I.card))) ∈ Ψ.cones :=
    «Σ».quotient_of_full_basis_standard_cone b I hfull
  have hcoords := Ψ.coordinate_box_mem_fanPolytope hΨpure H hH (fun u => C u - 1)
    1 zero_le_one hdegrees hstandard
    (fun j => normalHeight δ (b (complementaryEmbedding I j)) - 1)
    (fun j => by obtain ⟨hlo, hhi⟩ := htangent j; constructor <;> linarith)
  have hpoint : (fun j => -(C (Pi.basisFun ℤ (Fin (n - I.card)) j) - 1) +
      (normalHeight δ (b (complementaryEmbedding I j)) - 1)) =
      tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ := by
    funext j
    rw [show C (Pi.basisFun ℤ (Fin (n - I.card)) j) = a (b (complementaryEmbedding I j)) from
      «Σ».faceSupport_displaced_standard_coordinate b I hfull hF _ _ j]
    dsimp only [tangentSliceCoordinates]
    ring
  rw [hpoint] at hcoords
  have hcanonical := «Σ».canonical_slice_eq_of_edges b I hF hpure a ha hedges
    (normalHeight δ) hhI hsumBudget
  have hslice : quotientFaceMap D b I (tangentSliceCoordinates (fun u => (a u : ℝ)) b I δ) ∈
      {x ∈ «Σ».fanPolytope (fun u => (a u : ℝ) - 1) | ∀ u ∈ I.image b,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + (a u : ℝ) = normalHeight δ u} := by
    rw [← hcanonical]
    exact ⟨_, hcoords, rfl⟩
  rw [quotientFaceMap_tangentSliceCoordinates _ b I v δ hv] at hslice
  exact «Σ».fanPolytope_sub_pos_subset_interior _ 1 zero_lt_one hslice.1

end SmoothCompleteFan

end PaperVerification.ToricGeometry
