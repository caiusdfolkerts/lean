module

public import Solution

/-! Source bridges for the separate geometric supplement. New proof bodies
are prepared but uncompiled; no code-existence or exact-grid theorem is asserted. -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Module
open scoped BigOperators Pointwise Topology

namespace PalomarVolumeSupplement
universe uSupp vSupp

/-- The literal real plane and product-coordinate three-space. -/
abbrev Plane := ℝ × ℝ
abbrev Space := ℝ × Plane

section GenericVolume
variable {E : Type uSupp} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The volume polynomial is fixed by its values at every nonnegative weight.
Source existence and uniqueness identify this literal choice in Solution. -/
def literalVolumePolynomial {n : ℕ} (K : Fin n → ConvexBody E) :
    MvPolynomial (Fin n) ℝ :=
  Classical.epsilon (fun p : MvPolynomial (Fin n) ℝ =>
    p.IsHomogeneous (finrank ℝ E) ∧ (∀ m, 0 ≤ p.coeff m) ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
        MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E))

/-- The normalized squarefree coefficient of the actual volume polynomial. -/
def mixedVolume {d : ℕ} (K : Fin d → ConvexBody E) : ℝ :=
  (literalVolumePolynomial μ K).coeff
    (Finsupp.equivFunOnFinite.symm (fun _ : Fin d => 1)) / d.factorial
end GenericVolume

section Maps
variable {E : Type uSupp} {F : Type vSupp}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical image convexity, named to keep proof fields explicit. -/
theorem map_convex (f : E →L[ℝ] F) (K : ConvexBody E) :
    Convex ℝ (f '' (K : Set E)) := K.convex.linear_image f.toLinearMap
/-- Canonical compactness of the continuous image. -/
theorem map_compact (f : E →L[ℝ] F) (K : ConvexBody E) :
    IsCompact (f '' (K : Set E)) := K.isCompact.image f.continuous
/-- Canonical nonemptiness of the image. -/
theorem map_nonempty (f : E →L[ℝ] F) (K : ConvexBody E) :
    (f '' (K : Set E)).Nonempty := K.nonempty.image f

/-- The actual image body; no unproved geometric predicate is supplied. -/
def mapBody (f : E →L[ℝ] F) (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := map_convex f K
  isCompact' := map_compact f K
  nonempty' := map_nonempty f K
end Maps

/-- Width and height are actual lengths of the coordinate images. -/
def width (K : ConvexBody Plane) : ℝ := volume.real (Prod.fst '' (K : Set Plane))
def height (K : ConvexBody Plane) : ℝ := volume.real (Prod.snd '' (K : Set Plane))

/-- Coordinate-plane embeddings in the source order (z,(x,y)). -/
def embedXY : Plane →L[ℝ] Space :=
  (0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Plane)
def embedYZ : Plane →L[ℝ] Space :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ))
def embedXZ : Plane →L[ℝ] Space :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : Plane →L[ℝ] ℝ))

/-- Literal planar mixed area and the three-plane mixed volume. -/
def mixedArea (A B : ConvexBody Plane) : ℝ := mixedVolume volume ![A, B]
def triple (A B C : ConvexBody Plane) : ℝ :=
  mixedVolume volume ![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C]

/-- The complete mixed-volume identity defining an interaction body. -/
def IsInteraction (B C Q : ConvexBody Plane) : Prop :=
  width Q = 1 ∧ height Q = 1 ∧
    ∀ A : ConvexBody Plane,
      (Nat.cast 6 : ℝ) * triple A B C = (Nat.cast 2 : ℝ) * mixedArea A Q

/-- All normalized geometric constraints in the logarithmic slice. -/
def NormalizedRealizable (s z : ℝ) : Prop :=
  ∃ A B C : ConvexBody Plane, ∃ T : ℝ, 0 < T ∧
    width A = 1 ∧ height A = s ∧
    volume.real (A : Set Plane) = (Nat.cast 2 : ℝ) * s * T ∧
    width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
    volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
    (Nat.cast 6 : ℝ) * triple A B C = (Nat.cast 2 : ℝ) * T * z

/-- The actual fiber infimum and the larger comparison root. -/
def threshold (s : ℝ) : ℝ := sInf {z : ℝ | NormalizedRealizable s z}
def comparisonRoot (s : ℝ) : ℝ :=
  (1 + s + Real.sqrt (1 + s ^ 2)) / (Nat.cast 2 : ℝ)

/-- Polygonality means equality with the convex hull of a finite set. -/
def IsFiniteHull (C : Set Plane) : Prop := ∃ S : Set Plane, S.Finite ∧ C = convexHull ℝ S

/-- Explicit normalized scalar constants avoid proof-dependent numeral data. -/
def half : ℝ := (Nat.cast 1 : ℝ) / Nat.cast 2
def twoThirds : ℝ := (Nat.cast 2 : ℝ) / Nat.cast 3
def angle : ℝ := Real.arccos ((Nat.cast 1 : ℝ) / Nat.cast 3)

/-- The literal return map (x,y) ↦ (y,-x+2y/3). -/
def returnMap (p : Plane) : Plane := (p.2, -p.1 + twoThirds * p.2)
def returnContinuous : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-(ContinuousLinearMap.fst ℝ ℝ ℝ) +
      twoThirds • ContinuousLinearMap.snd ℝ ℝ ℝ)
def orbit (n : ℕ) : Plane := Nat.rec (1, 0) (fun _ p => returnMap p) n
def weightedOrbit (lam : ℝ) (n : ℕ) : Plane := lam ^ n • orbit n
def scaledReturn (lam : ℝ) : Plane →L[ℝ] Plane := lam • returnContinuous

/-- Every interval coefficient is included in the actual infinite segment sum. -/
abbrev SegmentChoice := ℕ → Icc (-half) half
def forcedSet (lam : ℝ) : Set Plane :=
  Set.range (fun t : SegmentChoice => ∑' n, (t n : ℝ) • weightedOrbit lam n)
def centeredSegment (v : Plane) : Set Plane :=
  {x | ∃ t : Icc (-half) half, x = (t : ℝ) • v}
def det (p q : Plane) : ℝ := p.1 * q.2 - p.2 * q.1

/-- The actual supporting functional perpendicular to each generating vector. -/
def orbitNormal (lam : ℝ) (j : ℕ) : Plane →L[ℝ] ℝ :=
  (weightedOrbit lam j).1 • ContinuousLinearMap.snd ℝ ℝ ℝ -
    (weightedOrbit lam j).2 • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The literal area formula, with every return-map iterate represented. -/
def areaSeries (lam : ℝ) : ℝ :=
  (∑' n : ℕ, |Real.sin (((n + 1 : ℕ) : ℝ) * angle)| * lam ^ (n + 1)) /
    ((1 - lam ^ 2) * Real.sin angle)

end PalomarVolumeSupplement

namespace PalomarVolumeSupplement
universe uBridge vBridge

private theorem cast_two : (Nat.cast 2 : ℝ) = 2 := by norm_num
private theorem cast_three : (Nat.cast 3 : ℝ) = 3 := by norm_num
private theorem cast_six : (Nat.cast 6 : ℝ) = 6 := by norm_num
private theorem cast_sixtyFour : (Nat.cast 64 : ℝ) = 64 := by norm_num
private theorem cast_oneTwentyEight : (Nat.cast 128 : ℝ) = 128 := by norm_num
private theorem cast_upperConstant : (Nat.cast 4352 : ℝ) = 4352 := by norm_num
private theorem cast_lowerDenominator : (Nat.cast 51200 : ℝ) = 51200 := by norm_num
private theorem cast_gapUpperConstant : (Nat.cast 34816 : ℝ) = 34816 := by norm_num
private theorem half_eq : half = (1 / 2 : ℝ) := by norm_num [half]
private theorem twoThirds_eq : twoThirds = (2 / 3 : ℝ) := by norm_num [twoThirds]

private theorem literalVolumePolynomial_eq
    {E : Type uBridge} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {n : ℕ} (K : Fin n → ConvexBody E) :
    literalVolumePolynomial μ K = VolumePolynomials.volumePolynomial μ K := by
  have hex : ∃ p : MvPolynomial (Fin n) ℝ,
      p.IsHomogeneous (finrank ℝ E) ∧ (∀ m, 0 ≤ p.coeff m) ∧
        ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
          MvPolynomial.eval t p = μ.real ((∑ i, t i • K i : ConvexBody E) : Set E) :=
    VolumePolynomials.hasPositiveVolumePolynomial μ K
  have hp := Classical.epsilon_spec hex
  exact (VolumePolynomials.volumePolynomial_eq_of_eval μ K _ hp.2.2).symm

private theorem mixedVolume_eq
    {E : Type uBridge} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {d : ℕ} (K : Fin d → ConvexBody E) :
    mixedVolume μ K = VolumePolynomials.mixedVolume μ K := by
  unfold mixedVolume VolumePolynomials.mixedVolume
  rw [literalVolumePolynomial_eq]
  rfl

private theorem mapBody_eq
    {E : Type uBridge} {F : Type vBridge}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (K : ConvexBody E) :
    mapBody f K = VolumePolynomials.mapBody f K := by rfl

private theorem width_eq : width = VolumePolynomials.PlanarCorner.width := by rfl
private theorem height_eq : height = VolumePolynomials.PlanarCorner.height := by rfl
private theorem embedXY_eq : embedXY = VolumePolynomials.PlanarInteraction.embedXY := by
  apply ContinuousLinearMap.ext
  intro p
  rfl
private theorem embedYZ_eq : embedYZ = VolumePolynomials.PlanarInteraction.embedYZ := by
  apply ContinuousLinearMap.ext
  intro p
  rfl
private theorem embedXZ_eq : embedXZ = VolumePolynomials.PlanarInteraction.embedXZ := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

private theorem mixedArea_eq :
    mixedArea = VolumePolynomials.PlanarMixedForm.mixedArea volume := by
  funext A B
  exact mixedVolume_eq volume ![A, B]

private theorem triple_eq : triple = VolumePolynomials.PlanarInteraction.triple := by
  funext A B C
  simp only [triple, VolumePolynomials.PlanarInteraction.triple,
    VolumePolynomials.PlanarInteraction.mixed3, mixedVolume_eq,
    embedXY_eq, embedYZ_eq, embedXZ_eq, mapBody_eq]

private theorem interaction_iff (B C Q : ConvexBody Plane) :
    IsInteraction B C Q ↔ VolumePolynomials.PlanarInteraction.IsInteraction B C Q := by
  simp only [IsInteraction, VolumePolynomials.PlanarInteraction.IsInteraction,
    width_eq, height_eq, triple_eq, mixedArea_eq, cast_six, cast_two]

private theorem normalized_iff (s z : ℝ) :
    NormalizedRealizable s z ↔ VolumePolynomials.PlanarInteraction.NormalizedRealizable s z := by
  unfold NormalizedRealizable VolumePolynomials.PlanarInteraction.NormalizedRealizable
  simp only [width_eq, height_eq, triple_eq, cast_two, cast_six]
  constructor
  · rintro ⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩
    exact ⟨⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩⟩
  · rintro ⟨D⟩
    exact ⟨D.A, D.B, D.C, D.T, D.T_pos, D.A_width, D.A_height, D.A_area,
      D.B_width, D.B_height, D.C_width, D.C_height, D.B_area, D.C_area, D.triple_value⟩

private theorem threshold_eq :
    threshold = VolumePolynomials.PlanarInteraction.normalizedThreshold := by
  funext s
  unfold threshold VolumePolynomials.PlanarInteraction.normalizedThreshold
  congr 1
  ext z
  exact normalized_iff s z

private theorem comparisonRoot_eq : comparisonRoot = VolumePolynomials.comparisonRoot := by
  funext s
  unfold comparisonRoot VolumePolynomials.comparisonRoot
  rw [cast_two]

private theorem finiteHull_iff (K : Set Plane) :
    IsFiniteHull K ↔ VolumePolynomials.PolytopeGeometry.IsFiniteHull K := by rfl

private theorem returnMap_eq : returnMap = VolumePolynomials.Holonomy.returnMap := by
  funext p
  unfold returnMap VolumePolynomials.Holonomy.returnMap
  rw [twoThirds_eq]

private theorem returnContinuous_eq :
    returnContinuous = VolumePolynomials.Holonomy.returnContinuous := by
  apply ContinuousLinearMap.ext
  intro p
  change returnMap p = VolumePolynomials.Holonomy.returnMap p
  exact congrFun returnMap_eq p

private theorem orbit_eq : orbit = VolumePolynomials.Holonomy.orbit := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      change returnMap (orbit n) =
        VolumePolynomials.Holonomy.returnMap (VolumePolynomials.Holonomy.orbit n)
      rw [returnMap_eq, ih]

private theorem weightedOrbit_eq : weightedOrbit = VolumePolynomials.Holonomy.weightedOrbit := by
  funext lam n
  unfold weightedOrbit VolumePolynomials.Holonomy.weightedOrbit
  rw [orbit_eq]

private theorem scaledReturn_eq : scaledReturn = VolumePolynomials.Holonomy.scaledReturn := by
  funext lam
  unfold scaledReturn VolumePolynomials.Holonomy.scaledReturn
  rw [returnContinuous_eq]

private theorem centeredSegment_eq :
    centeredSegment = (VolumePolynomials.centeredSegment : Plane → Set Plane) := by
  funext v
  unfold centeredSegment VolumePolynomials.centeredSegment
  rw [half_eq]

private theorem forcedSet_eq (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    forcedSet lam =
      (VolumePolynomials.Holonomy.forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
  rw [VolumePolynomials.Holonomy.forcedBody_carrier]
  change VolumePolynomials.PalomarGeometry.segmentSeries (weightedOrbit lam) = _
  rw [weightedOrbit_eq]
  exact VolumePolynomials.palomarSegmentSeries_eq_source _

private theorem orbitNormal_eq : orbitNormal = VolumePolynomials.Holonomy.orbitNormal := by
  funext lam j
  apply ContinuousLinearMap.ext
  intro x
  change (weightedOrbit lam j).1 * x.2 - (weightedOrbit lam j).2 * x.1 = _
  rw [weightedOrbit_eq]
  rfl

private theorem angle_eq : angle = VolumePolynomials.Holonomy.angle := by
  exact VolumePolynomials.palomarAngle_eq_source

private theorem areaSeries_eq :
    areaSeries = VolumePolynomials.realAreaSeries VolumePolynomials.Holonomy.angle := by
  funext lam
  unfold areaSeries VolumePolynomials.realAreaSeries
  rw [angle_eq]

end PalomarVolumeSupplement

namespace PalomarVolumeSupplement

/-- Corollary 5.3, retaining the explicit constant and every smallness/geometry hypothesis. -/
theorem corollary_5_3 {B C Q : ConvexBody Plane}
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : IsInteraction B C Q) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : (Nat.cast 2 : ℝ) * δ < min (1 / (Nat.cast 64 : ℝ)) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = half - δ)
    (hCa : volume.real (C : Set Plane) = half - δ) :
    half - volume.real (Q : Set Plane) ≤
      (Nat.cast 4352 : ℝ) * δ ^ 2 * Real.log (1 / δ) := by
  have h := VolumePolynomials.PlanarInteraction.corollary_5_3
    (by simpa only [width_eq] using hBw) (by simpa only [height_eq] using hBh)
    (by simpa only [width_eq] using hCw) (by simpa only [height_eq] using hCh)
    ((interaction_iff B C Q).mp hQ) hδ
    (by simpa only [cast_two, cast_sixtyFour] using hsmall)
    (by simpa only [half_eq] using hBa) (by simpa only [half_eq] using hCa)
  simpa only [half_eq, cast_upperConstant] using h

/-- The actual fiber minimum is attained, with no assumed realization oracle. -/
theorem threshold_attained {s : ℝ} (hs : 0 < s) (hsmall : s ≤ half) :
    NormalizedRealizable s (threshold s) ∧
      ∀ z : ℝ, NormalizedRealizable s z → threshold s ≤ z := by
  have h := VolumePolynomials.PlanarInteraction.normalized_threshold_attained hs
    (by simpa only [half_eq] using hsmall)
  simpa only [normalized_iff, threshold_eq] using h

/-- Theorem 5.5 with the source's explicit two-sided constants. -/
theorem logarithmic_gap {s : ℝ} (hs : 0 < s)
    (hsmall : s < min (1 / (Nat.cast 128 : ℝ)) (Real.exp (-1))) :
    ((Nat.cast 3 : ℝ) / Nat.cast 51200) * s ^ 3 * Real.log (1 / s) ≤
        comparisonRoot s - threshold s ∧
      comparisonRoot s - threshold s ≤
        (Nat.cast 34816 : ℝ) * s ^ 3 * Real.log (1 / s) := by
  have h := VolumePolynomials.PlanarInteraction.normalized_threshold_gap hs
    (by simpa only [cast_oneTwentyEight] using hsmall)
  simpa only [threshold_eq, comparisonRoot_eq, cast_three,
    cast_lowerDenominator, cast_gapUpperConstant] using h

/-- The lower logarithmic order is witnessed by genuine finite convex hulls. -/
theorem lower_polygon_witness {s : ℝ} (hs : 0 < s) (hsmall : s ≤ half) :
    ∃ A B C : ConvexBody Plane, ∃ T z : ℝ, 0 < T ∧
      width A = 1 ∧ height A = s ∧
      volume.real (A : Set Plane) = (Nat.cast 2 : ℝ) * s * T ∧
      width B = 1 ∧ height B = 1 ∧ width C = 1 ∧ height C = 1 ∧
      volume.real (B : Set Plane) = T ∧ volume.real (C : Set Plane) = T ∧
      (Nat.cast 6 : ℝ) * triple A B C = (Nat.cast 2 : ℝ) * T * z ∧
      ((Nat.cast 3 : ℝ) / Nat.cast 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - z ∧
      IsFiniteHull (A : Set Plane) ∧ IsFiniteHull (B : Set Plane) ∧ IsFiniteHull (C : Set Plane) := by
  have h := VolumePolynomials.PlanarInteraction.geometric_threshold_lower_polygons hs
    (by simpa only [half_eq] using hsmall)
  simpa only [width_eq, height_eq, triple_eq, comparisonRoot_eq, finiteHull_iff,
    cast_two, cast_six, cast_three, cast_lowerDenominator] using h

/-- The complete compact-convex fixed-point uniqueness assertion in Theorem 7.3. -/
theorem forced_body_unique (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃! K : ConvexBody Plane,
      (K : Set Plane) = centeredSegment (1, 0) + scaledReturn lam '' (K : Set Plane) := by
  simpa only [centeredSegment_eq, scaledReturn_eq] using
    VolumePolynomials.Holonomy.existsUnique_forced_body lam hlam₀ hlam₁

/-- Every geometric clause of Theorem 7.3: positive actual area, its series formula,
entire exposed segments, pairwise distinct directions, and nonsemialgebraicity. -/
theorem forced_body_geometric (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    (0 < volume.real (forcedSet lam)) ∧
    (volume.real (forcedSet lam) = areaSeries lam) ∧
    (∃ a : ℕ → Plane, ∀ j,
      (orbitNormal lam j).toExposed (forcedSet lam) =
        {x | ∃ t : Icc (-half) half, x = a j + (t : ℝ) • weightedOrbit lam j}) ∧
    (∀ i j : ℕ, i ≠ j → det (weightedOrbit lam i) (weightedOrbit lam j) ≠ 0) ∧
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹' forcedSet lam) := by
  rw [half_eq]
  simpa only [forcedSet_eq lam hlam₀ hlam₁, orbitNormal_eq, weightedOrbit_eq,
    det, VolumePolynomials.Holonomy.det, areaSeries_eq] using
    VolumePolynomials.Holonomy.theorem_7_3_geometric lam hlam₀ hlam₁

end PalomarVolumeSupplement
