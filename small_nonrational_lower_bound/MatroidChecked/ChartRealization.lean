module
public import MatroidChecked.ChartPolynomial
public import Papers.RationalityTenOrderedMinors
public import Papers.RankFourCertificateNormalization
public import Papers.RationalElimination

@[expose] public section
noncomputable section

/-!
# From a catalogue entry to an actual real chart

This file connects three independently checked objects: the finite basis
family, the scheduled normalization of an arbitrary real representation,
and the literal polynomial equations accepted by rational elimination.
The equations may prescribe a proper subset of the original zero minors;
that is needed when a single golden incidence is omitted.
-/

namespace Papers.RationalityTen.MatroidChecked.ChartRealization

open Matrix Set Filter Topology MvPolynomial
open ChartPolynomial
open VectorBasisFamilies (vectorBases mem_vectorBases det_ne_zero_iff_basis_image
  det_zero_iff_not_basis_image)
open BasisCertificates (checkedPermutation permutationFunction)
open Papers.RationalKernelCharts (RationalCoordinates)
open Papers.MatrixGaugeNormalization (ScheduledRankFourChart basisMatrix normalizeBasis
  normalizeBasis_basis normalizeBasis_zero_minor_iff coordinate_eq_exchange_minor
  certificateWeights checkSchedule exists_scheduled_rankFourChart ZeroRationalRealizations)
open RationalElimination MultiaffineDensity

/-- All data and proof obligations required of a finite chart. The variable
type is the actual type used by its polynomial elimination proof. -/
structure ChartCertificate (ι : Type*) (m u : ℕ)
    (family : Finset (Finset Point)) where
  entries : Coordinate → Coordinate → Entry ι
  positions : ι → Coordinate × Coordinate
  unitVariables : Fin u → ι
  labelCode : ℕ
  basisMark : Fin 70 → Bool
  requiredZero : Fin 70 → Bool
  polynomials : Fin 70 → MvPolynomial ι ℚ
  equations : Fin m → MvPolynomial ι ℚ
  units : Fin u → MvPolynomial ι ℚ
  roots : Finset Point
  steps : List (Point × Point)
  parameters : ParameterCertificate entries positions
  minors : MinorTableCertificate entries polynomials
  pattern : PatternCertificate family labelCode basisMark
  first_basis : basisMark 0 = true
  constraints : EntryConstraintCertificate family labelCode entries positions unitVariables
  equation_table : EquationTableCertificate requiredZero polynomials equations
  units_exact : ∀ k, units k = X (unitVariables k)
  required_nonbasis : ∀ i, requiredZero i = true → basisMark i ≠ true
  schedule : checkSchedule roots steps = true
  steps_are_ones : ∀ f ∈ steps,
    (∃ i j, f = (firstFour i,lastFour j) ∧ entries i j = .one) ∨
    (∃ i j, f = (lastFour j,firstFour i) ∧ entries i j = .one)
  ones_are_steps : ∀ i j, entries i j = .one →
    (firstFour i,lastFour j) ∈ steps ∨ (lastFour j,firstFour i) ∈ steps

def ChartCertificate.label {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (σ : Equiv.Perm Point) : Equiv.Perm Point :=
  (checkedPermutation 8 C.labelCode C.pattern.permutation_valid).trans σ.symm

/-- Explicit ordered-minor semantics after the catalogue permutation is
transported back to the original labels. -/
theorem relabelled_minor_ne_zero_iff
    (p : Matrix Point Coordinate ℝ) (e : Equiv.Perm Point) (s : Coordinate → Point) :
    ((p.submatrix e id).submatrix s id).det ≠ 0 ↔
      (Finset.univ.image s).image e ∈ vectorBases p := by
  have hmatrix : (p.submatrix e id).submatrix s id =
      (fun i j => p (e (s i)) j) := by
    ext i j
    rfl
  rw [hmatrix]
  simpa only [Finset.image_image,Function.comp_apply]
    using det_ne_zero_iff_basis_image p (e ∘ s)

theorem relabelled_minor_zero_iff
    (p : Matrix Point Coordinate ℝ) (e : Equiv.Perm Point) (s : Coordinate → Point) :
    ((p.submatrix e id).submatrix s id).det = 0 ↔
      (Finset.univ.image s).image e ∉ vectorBases p := by
  simpa only [not_not] using not_congr (relabelled_minor_ne_zero_iff p e s)

theorem normalized_coordinate_zero_iff
    (p : Matrix Point Coordinate ℝ) (e : Equiv.Perm Point)
    (hdet : (basisMatrix (p.submatrix e id) firstFour).det ≠ 0) (i j : Coordinate) :
    normalizeBasis (p.submatrix e id) firstFour (lastFour j) i = 0 ↔
      (exchangeSet i j).image e ∉ vectorBases p := by
  rw [← coordinate_eq_exchange_minor _ firstFour
      (normalizeBasis_basis _ firstFour hdet) (lastFour j) i,
    normalizeBasis_zero_minor_iff _ firstFour hdet,
    relabelled_minor_zero_iff]
  rfl

theorem scheduled_coordinate_zero_iff
    {p : Matrix Point Coordinate ℝ} {e : Equiv.Perm Point}
    {steps : List (Point × Point)} (N : ScheduledRankFourChart p e steps)
    (i j : Coordinate) :
    N.matrix (lastFour j) i = 0 ↔
      (exchangeSet i j).image e ∉ vectorBases p := by
  change N.displayBlock i j = 0 ↔ _
  rw [N.coordinate_zero_iff_exchange,relabelled_minor_zero_iff]
  rfl

theorem ChartCertificate.basis_nonsingular {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family) :
    (basisMatrix (p.submatrix (C.label σ) id) firstFour).det ≠ 0 := by
  apply (relabelled_minor_ne_zero_iff p (C.label σ) firstFour).mpr
  have h := (C.pattern.original_basis_iff σ hcatalogue 0).mpr C.first_basis
  simpa only [minorSet,minorRows_zero,ChartCertificate.label] using h

theorem ChartCertificate.scheduled_zero_iff {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family)
    (N : ScheduledRankFourChart p (C.label σ) C.steps) (i : Fin 70) :
    (N.matrix.submatrix (minorRows i) id).det = 0 ↔ C.basisMark i ≠ true := by
  rw [N.zero_minor_iff,relabelled_minor_zero_iff]
  exact not_congr (C.pattern.original_basis_iff σ hcatalogue i)

/-- A normalized representation together with its actual chart parameters.
The matrix equality ensures that no extra relation has been imposed on the
starting representation by the chosen polynomial parameterization. -/
structure RealizedChart {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point) where
  normalized : ScheduledRankFourChart p (C.label σ) C.steps
  point : ι → ℝ
  matrix_eq : valueMatrix C.entries point = normalized.matrix
  solution : point ∈ SolutionSet C.equations C.units

/-- Every representation whose actual basis family matches the catalogue
entry lies in the literal chart. Scheduled weights and parameter units are
derived from nonzero exchange minors, rather than assumed independently. -/
theorem ChartCertificate.realize {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family) :
    Nonempty (RealizedChart C p σ) := by
  let e := C.label σ
  have hlabel (S : Finset Point) :
      S.image e ∈ vectorBases p ↔ S.image (permutationFunction C.labelCode) ∈ family :=
    catalogue_label_membership (vectorBases p) family σ
      (checkedPermutation 8 C.labelCode C.pattern.permutation_valid) hcatalogue S
  have hdet := C.basis_nonsingular p σ hcatalogue
  have hone_ne (i j : Coordinate) (h : C.entries i j = .one) :
      normalizeBasis (p.submatrix e id) firstFour (lastFour j) i ≠ 0 := by
    intro hz
    have hn := (normalized_coordinate_zero_iff p e hdet i j).mp hz
    exact hn ((hlabel (exchangeSet i j)).mpr (C.constraints.one_nonzero i j h))
  have hweight : ∀ f ∈ C.steps,
      certificateWeights (normalizeBasis (p.submatrix e id) firstFour) f.1 f.2 ≠ 0 := by
    intro f hf
    rcases C.steps_are_ones f hf with ⟨i,j,rfl,hij⟩ | ⟨i,j,rfl,hij⟩
    · simpa only [Papers.MatrixGaugeNormalization.certificateWeights_left_right,
        Papers.MatrixGaugeNormalization.lowerBlock] using hone_ne i j hij
    · simpa only [Papers.MatrixGaugeNormalization.certificateWeights_right_left,
        Papers.MatrixGaugeNormalization.lowerBlock] using hone_ne i j hij
  obtain ⟨N⟩ := exists_scheduled_rankFourChart p e hdet C.roots C.steps C.schedule hweight
  let x := parametersOf C.positions N.matrix
  have hmatrix : valueMatrix C.entries x = N.matrix := by
    apply C.parameters.valueMatrix_parametersOf N.matrix N.basis_identity
    · intro i j hij
      apply (scheduled_coordinate_zero_iff N i j).mpr
      intro hmem
      exact C.constraints.zero_correct i j hij ((hlabel (exchangeSet i j)).mp hmem)
    · intro i j hij
      exact N.entries_one i j (C.ones_are_steps i j hij)
  have hE : EquationsHold C.equations x := by
    apply (equations_iff_required_zero_minors C.minors C.equation_table (Rat.castHom ℝ) x).mpr
    intro i hi
    rw [hmatrix]
    exact (C.scheduled_zero_iff p σ hcatalogue N i).mpr (C.required_nonbasis i hi)
  have hU : UnitsHold C.units x := by
    intro k
    rw [C.units_exact]
    simp only [evalRat,MvPolynomial.eval₂_X]
    change N.matrix (lastFour (C.positions (C.unitVariables k)).2)
      (C.positions (C.unitVariables k)).1 ≠ 0
    intro hz
    have hn := (scheduled_coordinate_zero_iff N
      (C.positions (C.unitVariables k)).1 (C.positions (C.unitVariables k)).2).mp hz
    exact hn ((hlabel _).mpr (C.constraints.unit_nonzero k))
  exact ⟨⟨N,x,hmatrix,hE,hU⟩⟩

/-- Rational matrices satisfying precisely the listed vanishing minors.
There is no assertion about any unlisted minor in this definition. -/
def PrescribedRationalMatrices (requiredZero : Fin 70 → Bool) :
    Set (Matrix Point Coordinate ℝ) :=
  {q | RationalCoordinates q ∧ ∀ i, requiredZero i = true →
    (q.submatrix (minorRows i) id).det = 0}

/-- Density for every actual real representation of a finite basis family,
including every relabeling of its ground set. -/
def FamilyRationallyDense (family : Finset (Finset Point)) : Prop :=
  ∀ p : Matrix Point Coordinate ℝ, ∀ σ : Equiv.Perm Point,
    (vectorBases p).image (fun S => S.image σ) = family →
      p ∈ closure (ZeroRationalRealizations p)

theorem continuous_valueMatrix {ι : Type*}
    (D : Coordinate → Coordinate → Entry ι) : Continuous (valueMatrix D :
      (ι → ℝ) → Matrix Point Coordinate ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun a => ?_) i
  · simp only [valueMatrix, rowMatrix_first]
    exact continuous_const
  · simp only [valueMatrix, rowMatrix_last]
    cases D j a with
    | zero => exact continuous_const
    | one => exact continuous_const
    | «variable» k => exact continuous_apply k

theorem rational_valueMatrix {ι : Type*}
    (D : Coordinate → Coordinate → Entry ι) (x : ι → ℝ) (hx : RationalVector x) :
    RationalCoordinates (valueMatrix D x) := by
  intro i j
  refine Fin.addCases (m := 4) (n := 4) (fun a => ?_) (fun a => ?_) i
  · by_cases h : a = j
    · exact ⟨1,by simp [valueMatrix,h]⟩
    · exact ⟨0,by simp [valueMatrix,h]⟩
  · change ∃ q : ℚ, (q : ℝ) = valueMatrix D x (lastFour a) j
    simp only [valueMatrix, rowMatrix_last]
    cases D j a with
    | zero => exact ⟨0,by simp [Entry.value]⟩
    | one => exact ⟨1,by simp [Entry.value]⟩
    | «variable» k => exact hx k

/-- The polynomial density theorem has its claimed geometric consequence:
rational matrices approach the actual matrix while every prescribed
determinant remains exactly zero. -/
theorem ChartCertificate.prescribed_density {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (hdense : RationallyDenseSystem C.equations C.units)
    (x : ι → ℝ) (hx : x ∈ SolutionSet C.equations C.units) :
    valueMatrix C.entries x ∈ closure (PrescribedRationalMatrices C.requiredZero) := by
  have hcl := mem_closure_image (continuous_valueMatrix C.entries).continuousAt (hdense x hx)
  apply closure_mono (s := valueMatrix C.entries '' _) ?_ hcl
  rintro _ ⟨q,⟨hq,hsolution⟩,rfl⟩
  exact ⟨rational_valueMatrix C.entries q hq,
    (equations_iff_required_zero_minors C.minors C.equation_table
      (Rat.castHom ℝ) q).mp hsolution.1⟩

/-- One-way preservation on the complete four-subset grid implies
preservation for all ordered four-tuples, including repetitions. -/
theorem ordered_zero_minors_of_grid
    (p q : Matrix Point Coordinate ℝ)
    (h : ∀ i : Fin 70, (p.submatrix (minorRows i) id).det = 0 →
      (q.submatrix (minorRows i) id).det = 0) :
    ∀ s : Coordinate → Point, (p.submatrix s id).det = 0 →
      (q.submatrix s id).det = 0 := by
  have hsub : vectorBases q ⊆ vectorBases p := by
    intro A hA
    obtain ⟨i,rfl⟩ := exists_minorSet A ((mem_vectorBases q A).mp hA).1
    by_contra hp
    have hpdet := (det_zero_iff_not_basis_image p (minorRows i)).mpr hp
    have hqdet := h i hpdet
    exact ((det_zero_iff_not_basis_image q (minorRows i)).mp hqdet) hA
  intro s hs
  apply (det_zero_iff_not_basis_image q s).mpr
  intro hmem
  exact ((det_zero_iff_not_basis_image p s).mp hs) (hsub hmem)

/-- For an ordinary chart all nonbases are required. Together with the
actual matroid correspondence, its density theorem therefore preserves
every zero maximal minor of the original representation. -/
theorem ChartCertificate.density {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (hcomplete : ∀ i, C.basisMark i ≠ true → C.requiredZero i = true)
    (hdense : RationallyDenseSystem C.equations C.units)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family) :
    p ∈ closure (ZeroRationalRealizations p) := by
  obtain ⟨R⟩ := C.realize p σ hcatalogue
  have hcl := C.prescribed_density hdense R.point R.solution
  rw [R.matrix_eq] at hcl
  apply R.normalized.density
  apply closure_mono ?_ hcl
  intro q hq
  refine ⟨hq.1,ordered_zero_minors_of_grid R.normalized.matrix q ?_⟩
  intro i hi
  exact hq.2 i (hcomplete i ((C.scheduled_zero_iff p σ hcatalogue R.normalized i).mp hi))

theorem ChartCertificate.family_density {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (hcomplete : ∀ i, C.basisMark i ≠ true → C.requiredZero i = true)
    (hdense : RationallyDenseSystem C.equations C.units) :
    FamilyRationallyDense family :=
  C.density hcomplete hdense

end Papers.RationalityTen.MatroidChecked.ChartRealization
