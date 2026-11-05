module

public import Mathlib.Analysis.Convex.FunctionTopology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Local concavity away from finitely many codimension-two subspaces

Exact generic analytic proofs recovered from BondalThomsen commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb. Only the enclosing namespace is
renamed. No toric scheme, wall-degree hypothesis, or projectivity theorem
is imported. The source-section manifest records every retained body.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Module Filter
open scoped Topology

section
-- BEGIN BondalThomsen/Fan/Completeness.lean
namespace Unimodular.WallSupportGeometry

open Set

variable {Ambient Index : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]
    [FiniteDimensional ℝ Ambient] [Finite Index]

theorem dense_avoiding_proper_subspaces (subspaces : Index → Submodule ℝ Ambient)
    (proper : ∀ index, subspaces index ≠ ⊤) :
    Dense {point : Ambient | ∀ index, point ∉ subspaces index} := by
  have empty_interior : ∀ index, interior (subspaces index : Set Ambient) = ∅ := by
    intro index
    apply Set.not_nonempty_iff_eq_empty.mp
    intro nonempty
    exact proper index ((subspaces index).eq_top_of_nonempty_interior' nonempty)
  have dense := dense_iInter_of_isOpen
    (fun index => (subspaces index).closed_of_finiteDimensional.isOpen_compl)
    (fun index => interior_eq_empty_iff_dense_compl.mp (empty_interior index))
  have avoiding_eq : {point : Ambient | ∀ index, point ∉ subspaces index} =
      ⋂ index, (subspaces index : Set Ambient)ᶜ := by ext point; simp
  rw [avoiding_eq]
  exact dense

end Unimodular.WallSupportGeometry
-- END BondalThomsen/Fan/Completeness.lean
end

section
-- BEGIN BondalThomsen/Fan/ConeCoordinates.lean
namespace Unimodular.WallSupportGeometry

open Set Module Matrix

variable {Index Ambient : Type*} [Fintype Index] [NormedAddCommGroup Ambient]
    [NormedSpace ℝ Ambient]

theorem mem_basisCone_iff (basis : Basis Index ℝ Ambient) (point : Ambient) :
    point ∈ PointedCone.hull ℝ (Set.range basis) ↔
      ∀ index, 0 ≤ basis.repr point index := by
  classical
  constructor
  · intro member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨index, rfl⟩ := member
      intro row
      simp only [Basis.repr_self_apply]
      split_ifs <;> norm_num
    | zero => intro index; simp
    | add first second _ _ first_nonnegative second_nonnegative =>
      intro index
      simpa only [map_add, Finsupp.add_apply] using
        add_nonneg (first_nonnegative index) (second_nonnegative index)
    | smul scalar vector _ nonnegative =>
      intro index
      change 0 ≤ basis.repr ((scalar : ℝ) • vector) index
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
        mul_nonneg scalar.property (nonnegative index)
  · intro nonnegative
    rw [← basis.sum_repr point]
    exact Submodule.sum_mem _ fun index _ =>
      PointedCone.smul_mem _ (nonnegative index) (PointedCone.subset_hull ⟨index, rfl⟩)

theorem isOpen_positive_basisCoordinates (basis : Basis Index ℝ Ambient) :
    IsOpen {point : Ambient | ∀ index, 0 < basis.repr point index} := by
  let := Module.Finite.of_basis basis
  have locus_eq : {point : Ambient | ∀ index, 0 < basis.repr point index} =
      ⋂ index, {point : Ambient | 0 < basis.coord index point} := by ext point; simp
  rw [locus_eq]
  exact isOpen_iInter_of_finite fun index =>
    isOpen_lt continuous_const (basis.coord index).continuous_of_finiteDimensional

theorem mem_interior_basisCone_of_positive (basis : Basis Index ℝ Ambient)
    (point : Ambient) (positive : ∀ index, 0 < basis.repr point index) :
    point ∈ interior (PointedCone.hull ℝ (Set.range basis) : Set Ambient) := by
  have positive_interior :
      point ∈ interior {point : Ambient | ∀ index, 0 < basis.repr point index} := by
    rw [(isOpen_positive_basisCoordinates basis).interior_eq]
    exact positive
  exact interior_mono (fun vector member => (mem_basisCone_iff basis vector).mpr
    (fun index => (member index).le)) positive_interior

end Unimodular.WallSupportGeometry
-- END BondalThomsen/Fan/ConeCoordinates.lean
end

section
-- BEGIN BondalThomsen/Toric/Surface/GeometricNefSupport.lean
namespace Unimodular.WallSupportGeometry

theorem nonnegative_on_unitInterval_of_local_midpoint_concavity
    (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 1))
    (left_nonnegative : 0 ≤ function 0) (right_nonnegative : 0 ≤ function 1)
    (local_midpoint : ∀ point ∈ Ioo (0 : ℝ) 1, ∃ radius : ℝ, 0 < radius ∧
      ∀ offset : ℝ, 0 < offset → offset < radius →
        (function (point - offset) + function (point + offset)) / 2 ≤ function point) :
    ∀ point ∈ Icc (0 : ℝ) 1, 0 ≤ function point := by
  obtain ⟨minimum, minimum_member, minimal⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) continuous
  have minimum_nonnegative : 0 ≤ function minimum := by
    by_contra not_nonnegative
    have negative : function minimum < 0 := lt_of_not_ge not_nonnegative
    let minimizers := {point : ℝ | point ∈ Icc (0 : ℝ) 1 ∧ function point = function minimum}
    have compact_minimizers : IsCompact minimizers := by
      have closed_minimizers : IsClosed minimizers :=
        isClosed_Icc.isClosed_eq continuous
          (continuousOn_const : ContinuousOn (fun _ : ℝ => function minimum) (Icc 0 1))
      exact isCompact_Icc.of_isClosed_subset closed_minimizers (fun _ member => member.1)
    obtain ⟨first_minimum, first_member, first_minimal⟩ := compact_minimizers.exists_isMinOn
      ⟨minimum, minimum_member, rfl⟩ continuous_id.continuousOn
    have first_negative : function first_minimum < 0 := by
      rw [first_member.2]
      exact negative
    have interior_member : first_minimum ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · by_contra not_positive
        have same : first_minimum = 0 := le_antisymm (le_of_not_gt not_positive) first_member.1.1
        rw [same] at first_negative
        linarith
      · by_contra not_less
        have same : first_minimum = 1 := le_antisymm first_member.1.2 (le_of_not_gt not_less)
        rw [same] at first_negative
        linarith
    obtain ⟨radius, radius_positive, midpoint⟩ := local_midpoint first_minimum interior_member
    let offset := min radius (min first_minimum (1 - first_minimum)) / 2
    have minimum_positive : 0 < min radius (min first_minimum (1 - first_minimum)) := by
      exact lt_min radius_positive (lt_min interior_member.1 (sub_pos.mpr interior_member.2))
    have offset_positive : 0 < offset := half_pos minimum_positive
    have offset_lt_radius : offset < radius :=
      (half_lt_self minimum_positive).trans_le (min_le_left _ _)
    have offset_lt_first : offset < first_minimum :=
      (half_lt_self minimum_positive).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
    have offset_lt_last : offset < 1 - first_minimum :=
      (half_lt_self minimum_positive).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    have left_member : first_minimum - offset ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [first_member.1.1, first_member.1.2]
    have right_member : first_minimum + offset ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [first_member.1.1, first_member.1.2]
    have local_bound := midpoint offset offset_positive offset_lt_radius
    have left_bound := minimal left_member
    have right_bound := minimal right_member
    change function minimum ≤ function (first_minimum - offset) at left_bound
    change function minimum ≤ function (first_minimum + offset) at right_bound
    have same_value : function (first_minimum - offset) = function minimum := by
      rw [first_member.2] at local_bound
      linarith
    have earlier := first_minimal (show first_minimum - offset ∈ minimizers from
      ⟨left_member, same_value⟩)
    change first_minimum ≤ first_minimum - offset at earlier
    linarith
  intro point member
  exact minimum_nonnegative.trans (minimal member)

theorem unitIntervalChord_le_of_locally_concave
    (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 1))
    (locally_concave : ∀ point ∈ Ioo (0 : ℝ) 1,
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function) :
    ∀ point ∈ Icc (0 : ℝ) 1,
      (1 - point) * function 0 + point * function 1 ≤ function point := by
  let gap := fun point : ℝ => function point - ((1 - point) * function 0 + point * function 1)
  have gap_continuous : ContinuousOn gap (Icc (0 : ℝ) 1) :=
    continuous.sub
      (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        (continuousOn_id.mul continuousOn_const))
  have local_midpoint : ∀ point ∈ Ioo (0 : ℝ) 1, ∃ radius : ℝ, 0 < radius ∧
      ∀ offset : ℝ, 0 < offset → offset < radius →
        (gap (point - offset) + gap (point + offset)) / 2 ≤ gap point := by
    intro point member
    obtain ⟨radius, positive, concave⟩ := locally_concave point member
    refine ⟨radius, positive, ?_⟩
    intro offset offset_positive offset_small
    have left_member : point - offset ∈ Metric.ball point radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      have negative : point - offset - point ≤ 0 := by linarith
      rw [abs_of_nonpos negative]
      linarith
    have right_member : point + offset ∈ Metric.ball point radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      have positive : 0 ≤ point + offset - point := by linarith
      rw [abs_of_nonneg positive]
      linarith
    have midpoint := concave.2 left_member right_member
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    have center : (1 / 2 : ℝ) • (point - offset) + (1 / 2 : ℝ) • (point + offset) = point := by
      simp only [smul_eq_mul]
      ring
    rw [center] at midpoint
    simp only [smul_eq_mul] at midpoint
    dsimp only [gap]
    nlinarith
  have nonnegative := nonnegative_on_unitInterval_of_local_midpoint_concavity gap gap_continuous
    (by simp [gap]) (by simp [gap]) local_midpoint
  intro point member
  exact sub_nonneg.mp (nonnegative point member)

end Unimodular.WallSupportGeometry
-- END BondalThomsen/Toric/Surface/GeometricNefSupport.lean
end

section
-- BEGIN BondalThomsen/Toric/Positivity/HigherWallLocalConcavity.lean
namespace Unimodular.WallSupportGeometry

variable {Space : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space]

omit [FiniteDimensional ℝ Space] in
theorem adjacentBasis_omitted_coordinate_neg {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1) (point : Space) :
    basis.repr point removed = -adjacent.repr point removed := by
  have same : basis.coord removed = -adjacent.coord removed := by
    apply adjacent.ext
    intro index
    by_cases equal : index = removed
    · subst index
      simpa only [LinearMap.neg_apply, Basis.coord_apply, Basis.repr_self_apply,
        ite_true] using opposite
    · rw [LinearMap.neg_apply]
      change basis.repr (adjacent index) removed = -adjacent.repr (adjacent index) removed
      have original_zero : basis.repr (adjacent index) removed = 0 := by
        rw [shared index equal]
        simp [equal]
      rw [original_zero]
      simp [equal]
  exact LinearMap.congr_fun same point

omit [FiniteDimensional ℝ Space] in
theorem adjacentBasis_coordinates_on_facet {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (point : Space) (zero_coordinate : basis.repr point removed = 0)
    (index : Fin dimension) (distinct : index ≠ removed) :
    adjacent.repr point index = basis.repr point index := by
  classical
  change adjacent.coord index point = _
  conv_lhs => rw [← basis.sum_repr point]
  rw [map_sum, Finset.sum_eq_single index]
  · rw [map_smul, ← shared index distinct]
    simp
  · intro other _ different
    by_cases equal : other = removed
    · subst other
      rw [zero_coordinate, zero_smul, map_zero]
    · rw [map_smul, ← shared other equal]
      simp [Basis.coord_apply, different]
  · simp

theorem adjacentBasis_union_mem_nhds_of_positive_facet {dimension : ℕ}
    (basis adjacent : Basis (Fin dimension) ℝ Space) (removed : Fin dimension)
    (shared : ∀ index, index ≠ removed → adjacent index = basis index)
    (opposite : basis.repr (adjacent removed) removed = -1)
    (point : Space) (zero_coordinate : basis.repr point removed = 0)
    (positive_coordinates : ∀ index, index ≠ removed → 0 < basis.repr point index) :
    (PointedCone.hull ℝ (Set.range basis) : Set Space) ∪
      (PointedCone.hull ℝ (Set.range adjacent) : Set Space) ∈ 𝓝 point := by
  let neighborhood := {nearby : Space | ∀ index, index ≠ removed →
    0 < basis.repr nearby index ∧ 0 < adjacent.repr nearby index}
  have open_neighborhood : IsOpen neighborhood := by
    have presentation : neighborhood = ⋂ index : {index : Fin dimension | index ≠ removed},
        {nearby : Space | 0 < basis.coord index.val nearby} ∩
          {nearby : Space | 0 < adjacent.coord index.val nearby} := by
      ext nearby
      simp [neighborhood]
    rw [presentation]
    apply isOpen_iInter_of_finite
    intro index
    exact (isOpen_lt continuous_const (basis.coord index.val).continuous_of_finiteDimensional).inter
      (isOpen_lt continuous_const (adjacent.coord index.val).continuous_of_finiteDimensional)
  have contains : point ∈ neighborhood := by
    intro index distinct
    rw [adjacentBasis_coordinates_on_facet basis adjacent removed shared point
      zero_coordinate index distinct]
    exact ⟨positive_coordinates index distinct, positive_coordinates index distinct⟩
  apply Filter.mem_of_superset (open_neighborhood.mem_nhds contains)
  intro nearby member
  by_cases positive_side : 0 ≤ basis.repr nearby removed
  · apply Or.inl
    apply (mem_basisCone_iff basis nearby).mpr
    intro index
    by_cases equal : index = removed
    · simpa only [equal] using positive_side
    · exact (member index equal).1.le
  · apply Or.inr
    apply (mem_basisCone_iff adjacent nearby).mpr
    intro index
    by_cases equal : index = removed
    · subst index
      have coordinate := adjacentBasis_omitted_coordinate_neg basis adjacent removed
        shared opposite nearby
      linarith
    · exact (member index equal).2.le

end Unimodular.WallSupportGeometry
-- END BondalThomsen/Toric/Positivity/HigherWallLocalConcavity.lean
end

section
-- BEGIN BondalThomsen/Toric/Positivity/WallConcavityGlobalization.lean
namespace Unimodular.WallSupportGeometry

theorem basis_pair_ker_sup_span_singleton_ne_top
    {Space Index : Type} [AddCommGroup Space] [Module ℝ Space]
    (basis : Basis Index ℝ Space) (first second : Index) (distinct : first ≠ second)
    (point : Space) :
    (basis.coord first).ker ⊓ (basis.coord second).ker ⊔
      Submodule.span ℝ {point} ≠ ⊤ := by
  classical
  intro equality
  have decomposes : ∀ vector : Space, ∃ remainder : Space,
      remainder ∈ (basis.coord first).ker ⊓ (basis.coord second).ker ∧
        ∃ scalar : ℝ, remainder + scalar • point = vector := by
    intro vector
    have member : vector ∈ (basis.coord first).ker ⊓ (basis.coord second).ker ⊔
        Submodule.span ℝ {point} := by rw [equality]; trivial
    obtain ⟨remainder, remainder_member, multiple, multiple_member, sum_eq⟩ :=
      Submodule.mem_sup.mp member
    obtain ⟨scalar, scalar_eq⟩ := Submodule.mem_span_singleton.mp multiple_member
    exact ⟨remainder, remainder_member, scalar, scalar_eq ▸ sum_eq⟩
  by_cases zero_coordinate : basis.coord first point = 0
  · obtain ⟨remainder, remainder_member, scalar, sum_eq⟩ := decomposes (basis first)
    have coordinate_eq := congrArg (basis.coord first) sum_eq
    have remainder_zero : basis.coord first remainder = 0 := remainder_member.1
    simp only [map_add, map_smul, smul_eq_mul, remainder_zero, zero_coordinate,
      mul_zero, add_zero, Basis.coord_apply, Basis.repr_self_apply, ite_true] at coordinate_eq
    exact zero_ne_one coordinate_eq
  · obtain ⟨remainder, remainder_member, scalar, sum_eq⟩ := decomposes (basis second)
    have first_eq := congrArg (basis.coord first) sum_eq
    have second_eq := congrArg (basis.coord second) sum_eq
    have first_zero : basis.coord first remainder = 0 := remainder_member.1
    have second_zero : basis.coord second remainder = 0 := remainder_member.2
    have scalar_zero : scalar = 0 := by
      have product_zero : scalar * basis.coord first point = 0 := by
        simpa only [map_add, map_smul, smul_eq_mul, first_zero, zero_add,
          Basis.coord_apply, Basis.repr_self_apply, ite_eq_right distinct.symm] using first_eq
      exact (mul_eq_zero.mp product_zero).resolve_right zero_coordinate
    simp only [map_add, map_smul, smul_eq_mul, second_zero, scalar_zero,
      zero_mul, add_zero, Basis.coord_apply, Basis.repr_self_apply, ite_true] at second_eq
    exact zero_ne_one second_eq

theorem chord_le_of_continuous_locally_concave_off_finite_subspaces
    {Space Index : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] [Finite Index]
    (subspaces : Index → Submodule ℝ Space)
    (proper_extensions : ∀ index point,
      subspaces index ⊔ Submodule.span ℝ {point} ≠ ⊤)
    (function : Space → ℝ) (continuous : Continuous function)
    (locally_concave : ∀ point : Space, (∀ index, point ∉ subspaces index) →
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function)
    (first second : Space) (parameter : ℝ) (member : parameter ∈ Icc (0 : ℝ) 1) :
    (1 - parameter) * function first + parameter * function second ≤
      function (AffineMap.lineMap first second parameter) := by
  let extensions := fun index => subspaces index ⊔ Submodule.span ℝ {first}
  have generic := dense_avoiding_proper_subspaces extensions
    (fun index => proper_extensions index first)
  let chord_domain := {other : Space |
    (1 - parameter) * function first + parameter * function other ≤
      function (AffineMap.lineMap first other parameter)}
  have closed_domain : IsClosed chord_domain := by
    have path_continuous : Continuous
        (fun other : Space => AffineMap.lineMap first other parameter) := by
      simp only [AffineMap.lineMap_apply_module]
      exact continuous_const.add (continuous_const.smul continuous_id)
    exact isClosed_le
      (continuous_const.add (continuous_const.mul continuous))
      (continuous.comp path_continuous)
  have generic_chord : {other : Space | ∀ index, other ∉ extensions index} ⊆
      chord_domain := by
    intro other avoids
    let path : ℝ →ᵃ[ℝ] Space := AffineMap.lineMap first other
    have path_continuous : Continuous path := path.continuous_of_finiteDimensional
    have path_avoids : ∀ scalar ∈ Ioo (0 : ℝ) 1,
        ∀ index, path scalar ∉ subspaces index := by
      intro scalar scalar_member index path_member
      have scalar_nonzero : scalar ≠ 0 := ne_of_gt scalar_member.1
      have path_in_extension : path scalar ∈ extensions index :=
        Submodule.mem_sup_left path_member
      have first_in_extension : first ∈ extensions index :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self first)
      have multiple_in_extension : scalar • other ∈ extensions index := by
        have difference := (extensions index).sub_mem path_in_extension
          ((extensions index).smul_mem (1 - scalar) first_in_extension)
        simpa only [path, AffineMap.lineMap_apply_module, add_sub_cancel_left] using difference
      have other_in_extension := (extensions index).smul_mem scalar⁻¹ multiple_in_extension
      rw [smul_smul, inv_mul_cancel₀ scalar_nonzero, one_smul] at other_in_extension
      exact avoids index other_in_extension
    have local_path_concavity : ∀ scalar ∈ Ioo (0 : ℝ) 1,
        ∃ radius : ℝ, 0 < radius ∧
          ConcaveOn ℝ (Metric.ball scalar radius) (function ∘ path) := by
      intro scalar scalar_member
      obtain ⟨radius, radius_positive, concave⟩ := locally_concave (path scalar)
        (path_avoids scalar scalar_member)
      have neighborhood : path ⁻¹' Metric.ball (path scalar) radius ∈ 𝓝 scalar :=
        path_continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ radius_positive)
      obtain ⟨parameter_radius, positive, within⟩ := Metric.mem_nhds_iff.mp neighborhood
      exact ⟨parameter_radius, positive,
        (concave.comp_affineMap path).subset within (convex_ball scalar parameter_radius)⟩
    have chord := unitIntervalChord_le_of_locally_concave (function ∘ path)
      (continuous.comp path_continuous).continuousOn local_path_concavity
    change (1 - parameter) * function first + parameter * function other ≤
      function (AffineMap.lineMap first other parameter)
    simpa only [Function.comp_apply, path, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using chord parameter member
  have closure_bound := closure_minimal generic_chord closed_domain
  rw [generic.closure_eq] at closure_bound
  exact closure_bound (Set.mem_univ second)

theorem concaveOn_univ_of_continuous_locally_concave_off_finite_subspaces
    {Space Index : Type} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [FiniteDimensional ℝ Space] [Finite Index]
    (subspaces : Index → Submodule ℝ Space)
    (proper_extensions : ∀ index point,
      subspaces index ⊔ Submodule.span ℝ {point} ≠ ⊤)
    (function : Space → ℝ) (continuous : Continuous function)
    (locally_concave : ∀ point : Space, (∀ index, point ∉ subspaces index) →
      ∃ radius : ℝ, 0 < radius ∧ ConcaveOn ℝ (Metric.ball point radius) function) :
    ConcaveOn ℝ Set.univ function := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ first_weight second_weight first_nonnegative second_nonnegative weight_sum
  have parameter_member : second_weight ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact second_nonnegative
    · linarith
  have bound := chord_le_of_continuous_locally_concave_off_finite_subspaces
    subspaces proper_extensions function continuous locally_concave
    first second second_weight parameter_member
  have first_weight_eq : 1 - second_weight = first_weight := by linarith
  simpa only [AffineMap.lineMap_apply_module, first_weight_eq, smul_eq_mul] using bound

end Unimodular.WallSupportGeometry
-- END BondalThomsen/Toric/Positivity/WallConcavityGlobalization.lean
end
