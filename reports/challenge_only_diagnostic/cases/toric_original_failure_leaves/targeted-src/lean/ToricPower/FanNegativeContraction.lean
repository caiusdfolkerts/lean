module

public import ToricPower.FanRayCoordinates
public import ToricPower.CechSingular.RealizationEquivalence

/-! # Contracting a recession-compatible induced ray complex

For a complete regular fan, a nonzero linear functional determines a
negative open half-space. Any induced ray subcomplex containing every
strictly negative ray and no strictly positive ray is contractible. The
proof permits an arbitrary choice of zero rays.

We state the geometric construction for any finite vertex enumeration
whose faces are exactly the sets contained in a fan cone. This lets the
actual negative incidence realization use the construction directly,
without an additional sphere realization or a homotopy-equivalence axiom.
-/

@[expose] public noncomputable section

open TauCeti.Toric
open BondalThomsen.ConvexNerveRealizationEquivalence
open scoped Classical BigOperators

attribute [local instance] Fintype.ofFinite

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Vertex : Type} [Fintype Vertex]

variable (fan : Fan i) (complex : AbstractSimplicialComplex Vertex)
  (vertex : Vertex ↪ fan.Ray)

/-- The ordinary linear ray realization of a barycentric point. -/
def fanRealizationVector (point : AbstractSimplicialComplex.Realization complex) : V :=
  fanRayCombination fan (point.val.mapDomain vertex)

variable (faces : ∀ face : Finset Vertex, face ∈ complex ↔
  face.Nonempty ∧ ∃ σ : fan.cones, ∀ v ∈ face, (vertex v).toCone ≤ σ)

include faces in
theorem fanRealizationVector_profile
    (point : AbstractSimplicialComplex.Realization complex) :
    IsFanRayProfile fan (fanRealizationVector fan complex vertex point)
      (point.val.mapDomain vertex) := by
  refine ⟨?_, ?_⟩
  · intro ρ
    by_cases hρ : ρ ∈ (point.val.mapDomain vertex).support
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hρ)
      rw [Finsupp.mapDomain_apply_of_injective vertex.injective]
      exact AbstractSimplicialComplex.Realization.nonneg complex point v
    · rw [Finsupp.notMem_support_iff.mp hρ]
  · obtain ⟨nonempty, σ, contained⟩ := (faces point.val.support).mp
      (AbstractSimplicialComplex.support_mem complex point)
    refine ⟨σ, ?_, rfl⟩
    intro ρ hρ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hρ)
    exact contained v hv

include faces in
theorem fanRealizationVector_coordinates (regular : fan.IsRegular)
    (complete : fan.IsComplete) (point : AbstractSimplicialComplex.Realization complex) :
    fanRayCoordinates fan complete (fanRealizationVector fan complex vertex point) =
      point.val.mapDomain vertex :=
  fanRayProfile_unique fan regular (fanRayCoordinates_profile fan complete _)
    (fanRealizationVector_profile fan complex vertex faces point)

include faces in
theorem fanRealizationVector_coordinate (regular : fan.IsRegular)
    (complete : fan.IsComplete) (point : AbstractSimplicialComplex.Realization complex)
    (v : Vertex) :
    fanRayCoordinates fan complete (fanRealizationVector fan complex vertex point) (vertex v) =
      point.val v := by
  rw [fanRealizationVector_coordinates fan complex vertex faces regular complete]
  exact Finsupp.mapDomain_apply_of_injective vertex.injective point.val v

/-- The total coefficient retained by the selected vertex set. -/
def retainedFanCoordinateSum (complete : fan.IsComplete) (x : V) : ℝ :=
  ∑ v : Vertex, fanRayCoordinates fan complete x (vertex v)

include faces in
theorem retainedFanCoordinateSum_realization (regular : fan.IsRegular)
    (complete : fan.IsComplete) (point : AbstractSimplicialComplex.Realization complex) :
    retainedFanCoordinateSum fan vertex complete
      (fanRealizationVector fan complex vertex point) = 1 := by
  unfold retainedFanCoordinateSum
  simp only [fanRealizationVector_coordinate fan complex vertex faces regular complete]
  have h := (realizationToSimplex complex point).total
  change point.val.sum (fun _ r => r) = 1 at h
  rwa [Finsupp.sum_fintype point.val (fun _ r => r) (fun _ => rfl)] at h

variable (complete : fan.IsComplete)

theorem retainedFanCoordinateSum_nonnegative (x : V) :
    0 ≤ retainedFanCoordinateSum fan vertex complete x :=
  Finset.sum_nonneg (fun v _ => (fanRayCoordinates_profile fan complete x).1 (vertex v))

theorem fanRayCoordinates_linear_sum (d : V →ₗ[ℝ] ℝ) (x : V) :
    (∑ ρ : fan.Ray, fanRayCoordinates fan complete x ρ * d (fanRayRealVector fan ρ)) = d x := by
  classical
  obtain ⟨nonnegative, σ, supported, evaluate⟩ := fanRayCoordinates_profile fan complete x
  have h := congrArg d evaluate
  change d ((fanRayCoordinates fan complete x).sum
    (fun ρ a => a • fanRayRealVector fan ρ)) = d x at h
  rw [Finsupp.sum_fintype _ (fun ρ a => a • fanRayRealVector fan ρ)
    (fun _ => zero_smul _ _), map_sum] at h
  simpa only [map_smul, smul_eq_mul] using h

variable (d : V →ₗ[ℝ] ℝ)
  (containsNegative : ∀ ρ : fan.Ray, d (fanRayRealVector fan ρ) < 0 →
    ∃ v : Vertex, vertex v = ρ)

include containsNegative in
/-- Strict negativity forces a positive retained coefficient, even if
some of the zero rays have been discarded. -/
theorem retainedFanCoordinateSum_pos_of_negative {x : V} (negative : d x < 0) :
    0 < retainedFanCoordinateSum fan vertex complete x := by
  classical
  have nonnegative := (fanRayCoordinates_profile fan complete x).1
  have existsNegative : ∃ ρ : fan.Ray,
      0 < fanRayCoordinates fan complete x ρ ∧ d (fanRayRealVector fan ρ) < 0 := by
    by_contra h
    push_neg at h
    have hsum : 0 ≤ ∑ ρ : fan.Ray,
        fanRayCoordinates fan complete x ρ * d (fanRayRealVector fan ρ) := by
      apply Finset.sum_nonneg
      intro ρ _
      by_cases positive : 0 < fanRayCoordinates fan complete x ρ
      · exact mul_nonneg (nonnegative ρ) (h ρ positive)
      · have hz : fanRayCoordinates fan complete x ρ = 0 :=
          le_antisymm (le_of_not_gt positive) (nonnegative ρ)
        rw [hz, zero_mul]
    rw [fanRayCoordinates_linear_sum fan complete d x] at hsum
    exact (not_lt_of_ge hsum) negative
  obtain ⟨ρ, positive, rayNegative⟩ := existsNegative
  obtain ⟨v, rfl⟩ := containsNegative ρ rayNegative
  exact positive.trans_le (Finset.single_le_sum
    (fun v _ => nonnegative (vertex v)) (Finset.mem_univ v))

/-- Normalize the retained coordinates wherever their sum is positive. -/
def normalizedFanCoordinates (x : V)
    (positive : 0 < retainedFanCoordinateSum fan vertex complete x) :
    AbstractSimplicialComplex.Realization complex := by
  let weights : Vertex →₀ ℝ := Finsupp.equivFunOnFinite.symm
    (fun v => fanRayCoordinates fan complete x (vertex v) /
      retainedFanCoordinateSum fan vertex complete x)
  have nonnegative : ∀ v, 0 ≤ weights v := by
    intro v
    exact div_nonneg ((fanRayCoordinates_profile fan complete x).1 (vertex v)) positive.le
  have total : weights.sum (fun _ r => r) = 1 := by
    rw [Finsupp.sum_fintype weights (fun _ r => r) (fun _ => rfl)]
    change (∑ v, fanRayCoordinates fan complete x (vertex v) /
      retainedFanCoordinateSum fan vertex complete x) = 1
    rw [← Finset.sum_div]
    exact div_self positive.ne'
  apply simplexToRealization complex ⟨weights, nonnegative, total⟩
  apply (faces weights.support).mpr
  refine ⟨Finsupp.support_nonempty_iff.mpr ?_, ?_⟩
  · intro zero
    rw [zero] at total
    simpa using total
  · obtain ⟨_, σ, supported, _⟩ := fanRayCoordinates_profile fan complete x
    refine ⟨σ, ?_⟩
    intro v present
    apply supported (vertex v)
    apply Finsupp.mem_support_iff.mpr
    intro zero
    have : weights v = 0 := by
      change fanRayCoordinates fan complete x (vertex v) /
        retainedFanCoordinateSum fan vertex complete x = 0
      rw [zero, zero_div]
    exact Finsupp.mem_support_iff.mp present this

theorem normalizedFanCoordinates_apply (x : V)
    (positive : 0 < retainedFanCoordinateSum fan vertex complete x) (v : Vertex) :
    (normalizedFanCoordinates fan complex vertex faces complete x positive).val v =
      fanRayCoordinates fan complete x (vertex v) /
        retainedFanCoordinateSum fan vertex complete x := rfl

theorem normalizedFanCoordinates_realization (regular : fan.IsRegular)
    (point : AbstractSimplicialComplex.Realization complex)
    (positive : 0 < retainedFanCoordinateSum fan vertex complete
      (fanRealizationVector fan complex vertex point)) :
    normalizedFanCoordinates fan complex vertex faces complete
      (fanRealizationVector fan complex vertex point) positive = point := by
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rw [normalizedFanCoordinates_apply,
    fanRealizationVector_coordinate fan complex vertex faces regular complete,
    retainedFanCoordinateSum_realization fan complex vertex faces regular complete,
    div_one]

variable (nonpositive : ∀ v : Vertex, d (fanRayRealVector fan (vertex v)) ≤ 0)

include nonpositive in
theorem fanRealizationVector_nonpositive
    (point : AbstractSimplicialComplex.Realization complex) :
    d (fanRealizationVector fan complex vertex point) ≤ 0 := by
  unfold fanRealizationVector fanRayCombination
  rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
  simp only [Function.comp_apply]
  rw [Finsupp.sum_fintype point.val
    (fun v a => a • fanRayRealVector fan (vertex v)) (fun _ => zero_smul _ _), map_sum]
  apply Finset.sum_nonpos
  intro v _
  simpa only [map_smul, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos
      (AbstractSimplicialComplex.Realization.nonneg complex point v) (nonpositive v)

/-- A straight path to a strictly negative vector; at positive time it
lies in the negative open half-space. -/
def fanContractionVector (w : V)
    (p : unitInterval × AbstractSimplicialComplex.Realization complex) : V :=
  (1 - (p.1 : ℝ)) • fanRealizationVector fan complex vertex p.2 + (p.1 : ℝ) • w

include faces containsNegative nonpositive in
theorem fanContractionVector_retained_pos (regular : fan.IsRegular)
    (w : V) (negative : d w < 0)
    (p : unitInterval × AbstractSimplicialComplex.Realization complex) :
    0 < retainedFanCoordinateSum fan vertex complete
      (fanContractionVector fan complex vertex w p) := by
  by_cases zero : (p.1 : ℝ) = 0
  · have eq : fanContractionVector fan complex vertex w p =
        fanRealizationVector fan complex vertex p.2 := by
      simp only [fanContractionVector, zero, sub_zero, one_smul, zero_smul, add_zero]
    rw [eq, retainedFanCoordinateSum_realization fan complex vertex faces regular complete]
    exact zero_lt_one
  · apply retainedFanCoordinateSum_pos_of_negative fan vertex complete d containsNegative
    have positive : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.property.1 (Ne.symm zero)
    have first : (1 - (p.1 : ℝ)) *
        d (fanRealizationVector fan complex vertex p.2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr p.1.property.2)
        (fanRealizationVector_nonpositive fan complex vertex d nonpositive p.2)
    have second : (p.1 : ℝ) * d w < 0 := mul_neg_of_pos_of_neg positive negative
    simpa only [fanContractionVector, map_add, map_smul, smul_eq_mul] using
      add_neg_of_nonpos_of_neg first second

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]

theorem fanRealizationVector_continuous :
    Continuous (fanRealizationVector fan complex vertex) := by
  have formula (point : AbstractSimplicialComplex.Realization complex) :
      fanRealizationVector fan complex vertex point =
        ∑ v : Vertex, point.val v • fanRayRealVector fan (vertex v) := by
    unfold fanRealizationVector fanRayCombination
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
    simp only [Function.comp_apply]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have equality : fanRealizationVector fan complex vertex =
      fun point => ∑ v : Vertex, point.val v • fanRayRealVector fan (vertex v) := funext formula
  rw [equality]
  apply continuous_finset_sum
  intro v _
  exact ((continuous_apply v).comp (realizationCoordinates_continuous complex)).smul
    continuous_const

theorem retainedFanCoordinateSum_continuous (regular : fan.IsRegular) :
    Continuous (retainedFanCoordinateSum fan vertex complete) := by
  unfold retainedFanCoordinateSum
  apply continuous_finset_sum
  intro v _
  exact fanRayCoordinates_continuous_apply fan regular complete (vertex v)

theorem fanContractionVector_continuous (w : V) :
    Continuous (fanContractionVector fan complex vertex w) := by
  apply Continuous.add
  · exact (continuous_const.sub continuous_fst.subtype_val).smul
      ((fanRealizationVector_continuous fan complex vertex).comp continuous_snd)
  · exact continuous_fst.subtype_val.smul continuous_const

/-- The literal contraction, including both endpoints and continuity in
the ordinary topology of the finite geometric realization. -/
def fanNegativeRealizationContraction (regular : fan.IsRegular)
    (w : V) (negative : d w < 0) :
    (ContinuousMap.id (AbstractSimplicialComplex.Realization complex)).Homotopy
      (ContinuousMap.const _ (normalizedFanCoordinates fan complex vertex faces complete w
        (retainedFanCoordinateSum_pos_of_negative fan vertex complete d containsNegative negative))) where
  toFun p := normalizedFanCoordinates fan complex vertex faces complete
    (fanContractionVector fan complex vertex w p)
    (fanContractionVector_retained_pos fan complex vertex faces complete d containsNegative
      nonpositive regular w negative p)
  continuous_toFun := by
    apply (continuous_into_realization_iff complex _).mpr
    intro v
    simp only [normalizedFanCoordinates_apply]
    exact ((fanRayCoordinates_continuous_apply fan regular complete (vertex v)).comp
      (fanContractionVector_continuous fan complex vertex w)).div
      ((retainedFanCoordinateSum_continuous fan vertex complete regular).comp
        (fanContractionVector_continuous fan complex vertex w))
      (fun p => (fanContractionVector_retained_pos fan complex vertex faces complete d
        containsNegative nonpositive regular w negative p).ne')
  map_zero_left point := by
    apply Subtype.ext
    apply Finsupp.ext
    intro v
    change (normalizedFanCoordinates fan complex vertex faces complete
      (fanContractionVector fan complex vertex w (0, point)) _).val v = point.val v
    rw [normalizedFanCoordinates_apply]
    simp only [fanContractionVector, (show ((0 : unitInterval) : ℝ) = 0 from rfl), sub_zero,
      one_smul, zero_smul, add_zero]
    rw [fanRealizationVector_coordinate fan complex vertex faces regular complete,
      retainedFanCoordinateSum_realization fan complex vertex faces regular complete, div_one]
  map_one_left point := by
    apply Subtype.ext
    apply Finsupp.ext
    intro v
    simp only [normalizedFanCoordinates_apply, fanContractionVector,
      (show ((1 : unitInterval) : ℝ) = 1 from rfl), sub_self, zero_smul, one_smul, zero_add,
      ContinuousMap.const_apply]

include faces complete containsNegative nonpositive in
theorem fanNegativeRealization_contractible (regular : fan.IsRegular)
    (w : V) (negative : d w < 0) :
    ContractibleSpace (AbstractSimplicialComplex.Realization complex) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨_, ⟨fanNegativeRealizationContraction fan complex vertex faces complete d
    containsNegative nonpositive regular w negative⟩⟩

end Topology
end ToricPower
