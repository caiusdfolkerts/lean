module
public import MatroidChecked.ChartRealization

@[expose] public section
noncomputable section

/-!
# Rationality of the scheduled normalization

A rational input has a rational normalized chart: every forest update uses
only multiplication and inversion. This refinement is used to prove that
no rational representation has the golden basis family. The density
arguments allow arbitrary real gauges and need no extra hypothesis.
-/

namespace Papers.RationalKernelCharts

theorem RatScalar.inv {x : ℝ} (hx : RatScalar x) : RatScalar x⁻¹ := by
  simpa only [one_div] using (show RatScalar 1 from ⟨1,by simp⟩).div hx

end Papers.RationalKernelCharts

namespace Papers.MatrixGaugeNormalization
open Matrix Papers.RationalKernelCharts

variable {ι : Type*} [DecidableEq ι]

theorem run_rational (w : ι → ι → ℝ) (hw : ∀ i j, RatScalar (w i j))
    (t : List (ι × ι)) (a : ι → ℝ) (ha : ∀ i, RatScalar (a i)) :
    ∀ i, RatScalar (run w t a i) := by
  induction t generalizing a with
  | nil => exact ha
  | cons e t ih =>
    obtain ⟨u,v⟩ := e
    apply ih
    intro i
    by_cases hi : i = v
    · subst i
      simpa only [step,Function.update_self] using ((hw u v).mul (ha u)).inv
    · simpa only [step,Function.update_of_ne hi] using ha i

theorem exists_rational_scheduled_rankFourChart (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hp : RationalCoordinates p)
    (e : Equiv.Perm (Fin 8))
    (hdet : (basisMatrix (p.submatrix e id) firstFour).det ≠ 0)
    (roots : Finset (Fin 8)) (edges : List (Fin 8 × Fin 8))
    (hcheck : checkSchedule roots edges = true)
    (hweight : ∀ f ∈ edges,
      certificateWeights (normalizeBasis (p.submatrix e id) firstFour) f.1 f.2 ≠ 0) :
    ∃ N : ScheduledRankFourChart p e edges, RationalCoordinates N.matrix := by
  classical
  let q := normalizeBasis (p.submatrix e id) firstFour
  have hp' : RationalCoordinates (p.submatrix e id) := fun i j => hp (e i) j
  have hq : RationalCoordinates q := rationalCoordinates_mul hp'
    (rationalCoordinates_inv (fun i j => hp' (firstFour i) j))
  have hwq : ∀ u v, RatScalar (certificateWeights q u v) := by
    intro u v
    refine Fin.addCases (m := 4) (n := 4) (fun i => ?_) (fun j => ?_) u
    · refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun l => ?_) v
      · simpa only [certificateWeights,Fin.addCases_left] using RatScalar.zero
      · simpa only [certificateWeights,Fin.addCases_left,Fin.addCases_right,lowerBlock]
          using hq (lastFour l) i
    · refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun l => ?_) v
      · simpa only [certificateWeights,Fin.addCases_left,Fin.addCases_right,lowerBlock]
          using hq (lastFour j) k
      · simpa only [certificateWeights,Fin.addCases_right] using RatScalar.zero
  let g := run (certificateWeights q) edges (fun _ => 1)
  have hgr : ∀ i, RatScalar (g i) := run_rational _ hwq edges _
    (fun _ => ⟨1,by simp⟩)
  obtain ⟨hg,_,hunit⟩ := run_correct (certificateWeights q)
    (validSteps_of_check (certificateWeights q) hcheck hweight)
    (fun _ => 1) (fun _ => one_ne_zero)
  let c : Fin 4 → ℝ := fun i => g (firstFour i)
  let a : Fin 8 → ℝ := fun k => Fin.addCases (fun i : Fin 4 => (c i)⁻¹)
    (fun j : Fin 4 => g (lastFour j)) k
  have hc : ∀ i, c i ≠ 0 := fun i => hg (firstFour i)
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
    · simpa only [a,Fin.addCases_left] using inv_ne_zero (hc j)
    · simpa only [a,Fin.addCases_right] using hg (lastFour j)
  have he (i j : Fin 4)
      (h : (firstFour i,lastFour j) ∈ edges ∨ (lastFour j,firstFour i) ∈ edges) :
      g (lastFour j) * lowerBlock q j i * g (firstFour i) = 1 := by
    rcases h with h | h
    · have hh := hunit (firstFour i,lastFour j) h
      simp only [certificateWeights_left_right] at hh
      calc
        _ = g (firstFour i) * lowerBlock q j i * g (lastFour j) := by ring
        _ = 1 := hh
    · simpa only [certificateWeights_right_left] using hunit (lastFour j,firstFour i) h
  refine ⟨{
    basis_nonsingular := hdet
    rowScale := a
    columnScale := c
    rowScale_nonzero := ha
    columnScale_nonzero := hc
    basis_identity := ?_
    entries_one := ?_ }, ?_⟩
  · apply scale_normalizeBasis_basis _ _ hdet
    intro i
    simpa only [a,firstFour,Fin.addCases_left] using inv_mul_cancel₀ (hc i)
  · intro i j h
    change a (lastFour j) * q (lastFour j) i * c i = 1
    simpa only [a,lastFour,Fin.addCases_right,lowerBlock,c] using he i j h
  · change RationalCoordinates (scaleRowsColumns q a c)
    apply scaleRowsColumns_rational q a c hq
    · intro i
      refine Fin.addCases (m := 4) (n := 4) (fun j => ?_) (fun j => ?_) i
      · simpa only [a,Fin.addCases_left,c] using (hgr (firstFour j)).inv
      · simpa only [a,Fin.addCases_right] using hgr (lastFour j)
    · exact fun i => hgr (firstFour i)

end Papers.MatrixGaugeNormalization

namespace Papers.RationalityTen.MatroidChecked.ChartRealization
open Matrix Set Filter Topology MvPolynomial ChartPolynomial
open VectorBasisFamilies (vectorBases)
open BasisCertificates (checkedPermutation permutationFunction)
open Papers.RationalKernelCharts (RationalCoordinates)
open Papers.MatrixGaugeNormalization (ScheduledRankFourChart basisMatrix normalizeBasis
  normalizeBasis_basis normalizeBasis_zero_minor_iff coordinate_eq_exchange_minor
  certificateWeights checkSchedule exists_rational_scheduled_rankFourChart)
open RationalElimination MultiaffineDensity

theorem ChartCertificate.realize_rational {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (p : Matrix Point Coordinate ℝ) (hp : RationalCoordinates p) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family) :
    ∃ R : RealizedChart C p σ, RationalVector R.point := by
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
  obtain ⟨N,hN⟩ := exists_rational_scheduled_rankFourChart p hp e hdet C.roots C.steps C.schedule hweight
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
  exact ⟨⟨N,x,hmatrix,hE,hU⟩,fun i => hN (lastFour (C.positions i).2) (C.positions i).1⟩

end Papers.RationalityTen.MatroidChecked.ChartRealization
