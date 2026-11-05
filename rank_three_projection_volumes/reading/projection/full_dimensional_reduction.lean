module

public import Projection.AreaEquality
public import Projection.SegmentSupport
public import Projection.HyperplaneObstruction
public import VolumeVerification.ProjectionMeasureReduction

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped BigOperators Pointwise Matrix

namespace RankThreeProjection
open VolumePolynomials

/-!
This file proves the finite-measure reduction underlying Proposition 4.2.
`SegmentAreaRigidity` is an explicit hypothesis of this intermediate reduction.
The source in `Rigidity.FullDimensional` supplies it for full-dimensional repeated
bodies, and `Main` uses that proof in the unconditional principal statements.
It is neither an axiom nor included in any definition of convex bodies, mixed
volume, or the realization locus. The project's build and endpoint audit
reports record the verification status.
-/

/-- The precise equality-rigidity consequence needed by the polygon argument.
All measures and support functions in this proposition are the actual ones
constructed from convex bodies. `Rigidity.FullDimensional` supplies this
proposition for full-dimensional `K`. See the project's build and endpoint
audit reports for the verification status of the complete development. -/
def SegmentAreaRigidity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {d : ℕ} (K : ConvexBody E) (hdim : finrank ℝ E = d + 2) : Prop :=
  ∀ (A C : ConvexBody E) (a : ℝ), 0 < a →
    mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a →
    mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a →
    mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a →
    ∃ t : E, ∀ v : E,
      ∀ᵐ u ∂mixedAreaMeasure volume
        (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim,
        supportContinuous A u - supportContinuous C u = u.val t

section Coordinates
variable {n : ℕ}

def normalCoordinates (u : NormalSphere (Space n)) : Space n :=
  fun i => u.val (Pi.single i 1)

theorem continuous_normalCoordinates : Continuous (normalCoordinates (n := n)) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : NormalSphere (Space n) => u.val (Pi.single i 1))
  fun_prop

theorem normal_evaluation_coordinates (u : NormalSphere (Space n)) (v : Space n) :
    u.val v = ∑ i, v i * normalCoordinates u i := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Space n) := by
    ext j
    simp [Pi.single_apply]
  calc
    u.val v = ∑ i, u.val (v i • (Pi.single i 1 : Space n)) := by
      rw [← map_sum]
      exact congrArg u.val hv
    _ = ∑ i, v i * normalCoordinates u i := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [normalCoordinates, smul_eq_mul] using
        (map_smul u.val (v i) (Pi.single i 1 : Space n))

theorem mark_coordinate_identity (U : Fin n → Space n)
    (j : Fin n) (u : NormalSphere (Space n)) :
    VolumeVerification.EdgeMoments.coordinate U normalCoordinates j u = u.val (U j) := by
  exact (normal_evaluation_coordinates u (U j)).symm

end Coordinates

section Reduction
variable {n d : ℕ} [NeZero n]
  (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)

/-- The paper's actual normalized mixed area measures. -/
def markedAreaMeasure (v : Space n) : Measure (NormalSphere (Space n)) :=
  ENNReal.ofReal ((d + 1 : ℝ) / 2) •
    mixedAreaMeasure volume (Fin.cons (centeredSegment v) (fun _ : Fin d => K)) hdim

instance markedAreaMeasure_finite (v : Space n) : IsFiniteMeasure (markedAreaMeasure K hdim v) := by
  unfold markedAreaMeasure
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem markedAreaMeasure_pairing (u v : Space n) :
    (∫ x, |x.val v| ∂markedAreaMeasure K hdim u) =
      (d + 2 : ℝ) * (d + 1 : ℝ) * mixedVolume volume
        (Fin.cons (centeredSegment u)
          (Fin.cons (centeredSegment v) (fun _ : Fin d => K))) := by
  have he : (fun x : NormalSphere (Space n) => |x.val v|) =
      fun x => 2 * supportContinuous (centeredSegment v) x := by
    funext x
    rw [supportContinuous_centeredSegment]
    ring
  rw [he, markedAreaMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), integral_const_mul,
    mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap volume (centeredSegment v) (centeredSegment u)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem markedAreaMeasure_centered (u v : Space n) :
    (∫ x, x.val v ∂markedAreaMeasure K hdim u) = 0 := by
  rw [markedAreaMeasure, integral_smul_measure, mixedAreaMeasure_centered, smul_zero]

theorem markedAreaMeasure_kernel_relation
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (w : Fin n → ℝ) (hw : complementaryMixedMatrix (d := d) K U *ᵥ w = 0)
    (s : Set (NormalSphere (Space n))) :
    ∑ i, w i * (markedAreaMeasure K hdim (U i)).real s = 0 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by
    have hn : n = d + 2 := by simpa only [Space,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
    omega)
  have he := mixedAreaMeasure_kernel_relation volume (fun _ : Fin d => K) hdim
    (fun i => centeredSegment (U i)) (complementaryMixedMatrix (d := d) K U)
    ((d + 2 : ℝ) * (d + 1 : ℝ)) (by positivity)
    (fun _ _ => rfl) (complementaryMixedMatrix_symmetric K U)
    (complementaryMixedMatrix_diagonal K U) hpos w hw s
  simp only [markedAreaMeasure, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (d + 1 : ℝ) / 2)]
  calc
    _ = ((d + 1 : ℝ) / 2) *
        ∑ i, w i * (mixedAreaMeasure volume
          (Fin.cons (centeredSegment (U i)) (fun _ : Fin d => K)) hdim).real s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [he, mul_zero]

theorem markedAreaMeasure_kernel_rigidity
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hR : SegmentAreaRigidity K hdim)
    (w : Fin n → ℝ) (hw : complementaryMixedMatrix (d := d) K U *ᵥ w = 0) :
    ∃ l : Fin n → ℝ, ∀ i,
      ∀ᵐ u ∂markedAreaMeasure K hdim (U i),
        (∑ j, w j * |u.val (U j)|) = ∑ j, l j * normalCoordinates u j := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by
    have hn : n = d + 2 := by simpa only [Space,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
    omega)
  by_cases hw0 : w = 0
  · subst w
    exact ⟨0, fun _ => Filter.Eventually.of_forall (fun _ => by simp)⟩
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hAA, hAC, hCC⟩ :=
    mixedVolume_kernel_zonotopes_equal_positive volume (fun _ : Fin d => K)
      (fun i => centeredSegment (U i)) (complementaryMixedMatrix (d := d) K U)
      ((d + 2 : ℝ) * (d + 1 : ℝ)) (by positivity) (fun _ _ => rfl)
      (complementaryMixedMatrix_symmetric K U) (complementaryMixedMatrix_diagonal K U)
      hpos w hw hw0
  obtain ⟨t, ht⟩ := hR
    (∑ i, x i • centeredSegment (U i)) (∑ i, y i • centeredSegment (U i))
    a ha hAA hAC hCC
  refine ⟨fun j => 2 * t j, ?_⟩
  intro i
  have hae := Measure.ae_smul_measure (ht (U i)) (ENNReal.ofReal ((d + 1 : ℝ) / 2))
  filter_upwards [hae] with u hu
  rw [supportContinuous_weighted_segments U x hx,
    supportContinuous_weighted_segments U y hy] at hu
  have hparts : ∀ j, w j = x j - y j := by
    intro j
    exact (congrFun
      (VolumeVerification.PositiveHollowKernel.positivePart_sub_negativePart w) j).symm
  have hs : (∑ j, w j * |u.val (U j)|) =
      (∑ j, x j * |u.val (U j)|) - ∑ j, y j * |u.val (U j)| := by
    simp_rw [hparts, sub_mul, Finset.sum_sub_distrib]
  rw [normal_evaluation_coordinates] at hu
  rw [hs]
  have he : (∑ j, 2 * t j * normalCoordinates u j) =
      2 * ∑ j, t j * normalCoordinates u j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

/-- All area-measure and polygonal steps of Proposition 4.2, with the sole
remaining geometric rigidity obligation visible in the theorem type. -/
theorem full_dimensional_obstruction_from_segment_rigidity
    (hn : 5 ≤ n) (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank = 3)
    (hR : SegmentAreaRigidity K hdim) : False := by
  apply VolumeVerification.ProjectionMeasureReduction.impossible_measure_data hn
    (complementaryMixedMatrix (d := d) K U) U
    (complementaryMixedMatrix_symmetric K U) (complementaryMixedMatrix_diagonal K U)
    hpos hrank (fun i => markedAreaMeasure K hdim (U i))
    normalCoordinates continuous_normalCoordinates
  · intro i j
    simp only [mark_coordinate_identity]
    exact (markedAreaMeasure_pairing K hdim (U i) (U j)).symm
  · intro i j
    exact markedAreaMeasure_centered K hdim (U i) (Pi.single j 1)
  · intro w hw s _hs
    exact markedAreaMeasure_kernel_relation K hdim U hpos w hw s
  · intro w hw
    simpa only [mark_coordinate_identity] using
      markedAreaMeasure_kernel_rigidity K hdim U hpos hR w hw

end Reduction
end RankThreeProjection
