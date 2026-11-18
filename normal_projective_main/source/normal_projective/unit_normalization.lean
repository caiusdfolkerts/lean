module
public import normal_projective.canonical_model
public import normal_projective.uniform_bound
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
/-! # Positive row normalization into the canonical unit-normal model -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace NormalProjective
namespace UnitNormalization

abbrev Space := CanonicalModel.Space

def rowForm {d : ℕ} (a : Space d) : Space d →L[ℝ] ℝ :=
  ∑ j, a j • ContinuousLinearMap.proj j

@[simp] theorem rowForm_apply {d : ℕ} (a x : Space d) :
    rowForm a x = CanonicalModel.dot a x := by
  simp [rowForm, CanonicalModel.dot]

def coefficients {d : ℕ} (f : Space d →L[ℝ] ℝ) : Space d :=
  fun j => f (Pi.single j 1)

@[simp] theorem coefficients_zero {d : ℕ} :
    coefficients (0 : Space d →L[ℝ] ℝ) = 0 := by
  ext j
  rfl

theorem coefficient_expansion {d : ℕ} (f : Space d →L[ℝ] ℝ) (x : Space d) :
    (∑ j, coefficients f j * x j) = f x := by
  have hh := congrFun
    (facetCoefficientMatrix_mulVec (ι := Unit) (fun _ => f.toLinearMap) x) ()
  exact hh

@[simp] theorem coefficients_rowForm {d : ℕ} (a : Space d) :
    coefficients (rowForm a) = a := by
  ext j
  simp [coefficients, rowForm, Pi.single_apply]

def length {d : ℕ} (f : Space d →L[ℝ] ℝ) : ℝ :=
  Real.sqrt (∑ j, coefficients f j ^ 2)

theorem length_pos {d : ℕ} (f : Space d →L[ℝ] ℝ) (hf : f ≠ 0) :
    0 < length f := by
  apply Real.sqrt_pos.mpr
  have hn : 0 ≤ ∑ j, coefficients f j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hall : ∀ j, coefficients f j = 0 :=
    fun j => (Finset.sum_sq_eq_zero_iff Finset.univ (coefficients f)).mp hz.symm j (Finset.mem_univ j)
  apply hf
  ext x
  rw [← coefficient_expansion]
  simp [hall]

theorem length_sq {d : ℕ} (f : Space d →L[ℝ] ℝ) :
    length f ^ 2 = ∑ j, coefficients f j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def unitRow {d : ℕ} (f : Space d →L[ℝ] ℝ) : Space d :=
  fun j => coefficients f j / length f

theorem unitRow_unit {d : ℕ} (f : Space d →L[ℝ] ℝ) (hf : f ≠ 0) :
    (∑ j, (unitRow f j) ^ 2) = 1 := by
  simp only [unitRow, div_pow, ← Finset.sum_div, ← length_sq]
  exact div_self (pow_ne_zero 2 (ne_of_gt (length_pos f hf)))

theorem dot_unitRow {d : ℕ} (f : Space d →L[ℝ] ℝ) (x : Space d) :
    CanonicalModel.dot (unitRow f) x = f x / length f := by
  unfold CanonicalModel.dot unitRow
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, coefficient_expansion]

structure RegularData (d : ℕ) (ι : Type*) [Fintype ι] where
  data : HalfspaceData ι (Space d)
  normal_ne_zero : ∀ i, data.1 i ≠ 0
  compact : IsCompact (dataRegion data)
  full_dimensional : (interior (dataRegion data)).Nonempty
  strict_facet_point : ∀ i, ∃ x ∈ dataRegion data,
    data.1 i x = data.2 i ∧ ∀ j, j ≠ i → data.1 j x < data.2 j

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem normalized_region (p : RegularData d ι) :
    CanonicalModel.region (fun i => unitRow (p.data.1 i))
      (fun i => p.data.2 i / length (p.data.1 i)) = dataRegion p.data := by
  ext x
  change (∀ i, CanonicalModel.dot (unitRow (p.data.1 i)) x ≤
    p.data.2 i / length (p.data.1 i)) ↔ ∀ i, p.data.1 i x ≤ p.data.2 i
  simp_rw [dot_unitRow, div_le_div_iff_of_pos_right
    (length_pos _ (p.normal_ne_zero _))]

def presentation (p : RegularData d ι) : CanonicalModel.Presentation d ι where
  normal := fun i => unitRow (p.data.1 i)
  support := fun i => p.data.2 i / length (p.data.1 i)
  unit_normal := fun i => unitRow_unit _ (p.normal_ne_zero i)
  compact := (normalized_region p).symm ▸ p.compact
  full_dimensional := (normalized_region p).symm ▸ p.full_dimensional
  strict_facet_point := by
    intro i
    obtain ⟨x, hx, hxi, hxs⟩ := p.strict_facet_point i
    refine ⟨x, (normalized_region p).symm ▸ hx, ?_, ?_⟩
    · rw [dot_unitRow, hxi]
    · intro j hji
      rw [dot_unitRow, div_lt_div_iff_of_pos_right (length_pos _ (p.normal_ne_zero j))]
      exact hxs j hji

@[simp] theorem presentation_carrier (p : RegularData d ι) :
    (presentation p).carrier = dataRegion p.data := normalized_region p

theorem presentation_facet (p : RegularData d ι) (i : ι) :
    (presentation p).facet i =
      {x ∈ dataRegion p.data | p.data.1 i x = p.data.2 i} := by
  ext x
  change (x ∈ CanonicalModel.region (fun j => unitRow (p.data.1 j))
      (fun j => p.data.2 j / length (p.data.1 j)) ∧
      CanonicalModel.dot (unitRow (p.data.1 i)) x =
        p.data.2 i / length (p.data.1 i)) ↔ _
  rw [normalized_region, dot_unitRow,
    div_left_inj' (ne_of_gt (length_pos _ (p.normal_ne_zero i)))]
  rfl

/-- The source is a literal facet presentation of the same carrier. -/
def ofCanonical (P : CanonicalModel.Presentation d ι) : RegularData d ι where
  data := (fun i => rowForm (P.normal i), P.support)
  normal_ne_zero := by
    intro i hi
    have hz : P.normal i = 0 := by
      have := congrArg coefficients hi
      simpa only [coefficients_rowForm, coefficients_zero] using this
    have hh := P.unit_normal i
    rw [hz] at hh
    simpa using hh
  compact := by simpa [dataRegion, halfspaceRegion, CanonicalModel.region] using P.compact
  full_dimensional := by
    simpa [dataRegion, halfspaceRegion, CanonicalModel.region] using P.full_dimensional
  strict_facet_point := by
    simpa [dataRegion, halfspaceRegion, CanonicalModel.region] using P.strict_facet_point

theorem presentation_ofCanonical (P : CanonicalModel.Presentation d ι) :
    presentation (ofCanonical P) = P := by
  have hext {Q R : CanonicalModel.Presentation d ι}
      (hn : Q.normal = R.normal) (hh : Q.support = R.support) : Q = R := by
    cases Q
    cases R
    cases hn
    cases hh
    rfl
  have hlen (i : ι) : length (rowForm (P.normal i)) = 1 := by
    simp [length, coefficients_rowForm, P.unit_normal i]
  have hn : (presentation (ofCanonical P)).normal = P.normal := by
    funext i j
    change coefficients (rowForm (P.normal i)) j / length (rowForm (P.normal i)) = _
    rw [coefficients_rowForm, hlen i, div_one]
  have hh : (presentation (ofCanonical P)).support = P.support := by
    funext i
    change P.support i / length (rowForm (P.normal i)) = _
    rw [hlen i, div_one]
  exact hext hn hh

end UnitNormalization
end NormalProjective

