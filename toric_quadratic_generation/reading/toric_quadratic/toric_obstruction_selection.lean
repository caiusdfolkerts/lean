module

public import PaperVerification.ToricPrimitiveFinite
public import PaperVerification.ToricLargeLoci
public import PaperVerification.ToricSimultaneousStars
public import PaperVerification.ToricContractibleEdgeDegrees

@[expose] public section

/-!
# The complete finite collection of obstructing contractible classes

The index set is cut out from all primitive collections of the actual fan.
No coefficient bound or extremality restriction is imposed. Uniqueness of
the primitive relation transfers every unrestricted contractible class to
this finite collection. Large-fiber disjointness and the fiber-type
alternative are consequences of the actual degree bounds.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R S : «Σ».PrimitiveRelation)

theorem contractible_iff_of_positive_eq (hpos : R.positive = S.positive) :
    R.IsCombinatoriallyContractible ↔ S.IsCombinatoriallyContractible := by
  have hneg := R.negative_unique S hpos
  simp only [IsCombinatoriallyContractible, hpos, hneg]

theorem fiberDimension_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.fiberDimension = S.fiberDimension := by simp only [fiberDimension, hpos]

/-- The integer-valued degree of an integral support function. -/
def integerDegree (a : Lattice n → ℤ) : ℤ :=
  (∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℤ) * a v

theorem integerDegree_cast (a : Lattice n → ℤ) :
    (R.integerDegree a : ℝ) = R.degree (fun v => (a v : ℝ)) := by
  simp only [integerDegree, degree, Int.cast_sub, Int.cast_sum, Int.cast_mul,
    Int.cast_natCast]

def coefficientSum : ℕ := ∑ v ∈ R.negative, R.coefficient v

theorem negative_card_le_coefficientSum : R.negative.card ≤ R.coefficientSum := by
  calc
    R.negative.card = ∑ _ ∈ R.negative, 1 := by simp
    _ ≤ R.coefficientSum := Finset.sum_le_sum (fun v hv => R.coefficient_pos v hv)

theorem coefficientSum_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.coefficientSum = S.coefficientSum := by
  have hneg := R.negative_unique S hpos
  unfold coefficientSum
  calc
    (∑ v ∈ R.negative, R.coefficient v) = ∑ v ∈ R.negative, S.coefficient v :=
      Finset.sum_congr rfl (fun v hv => R.coefficient_unique_on_negative S hpos hv)
    _ = _ := by rw [hneg]

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Finite selection from every primitive collection of the actual fan. -/
def selectedPrimitiveCollections (test : «Σ».PrimitiveRelation → Prop) :
    Finset «Σ».primitiveCollections :=
  Finset.univ.filter (fun Q => («Σ».canonicalPrimitive Q).IsCombinatoriallyContractible ∧
    test («Σ».canonicalPrimitive Q))

def selectionRelation (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) : «Σ».PrimitiveRelation :=
  «Σ».canonicalPrimitive i

theorem selectionRelation_contractible (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) :
    («Σ».selectionRelation test i).IsCombinatoriallyContractible :=
  (Finset.mem_filter.mp i.property).2.1

theorem selectionRelation_test (test : «Σ».PrimitiveRelation → Prop)
    (i : «Σ».selectedPrimitiveCollections test) : test («Σ».selectionRelation test i) :=
  (Finset.mem_filter.mp i.property).2.2

theorem selectionRelation_positive_injective (test : «Σ».PrimitiveRelation → Prop) :
    Function.Injective (fun i : «Σ».selectedPrimitiveCollections test =>
      («Σ».selectionRelation test i).positive) := by
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  simpa only [selectionRelation, «Σ».canonicalPrimitive_positive] using hij

/-- Exact exhaustiveness up to the proved primitive-class equality. -/
theorem selectionRelation_exhaustive
    (test : «Σ».PrimitiveRelation → Prop)
    (hcongr : ∀ R S : «Σ».PrimitiveRelation, R.positive = S.positive → (test R ↔ test S))
    (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».selectedPrimitiveCollections test,
      R.positive = («Σ».selectionRelation test i).positive) ↔
      R.IsCombinatoriallyContractible ∧ test R := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(R.contractible_iff_of_positive_eq _ hi).mpr
      («Σ».selectionRelation_contractible test i),
      (hcongr R _ hi).mpr («Σ».selectionRelation_test test i)⟩
  · rintro ⟨hR, htest⟩
    let Q : «Σ».primitiveCollections :=
      ⟨R.positive, («Σ».mem_primitiveCollections R.positive).mpr R.primitive⟩
    have hpos : R.positive = («Σ».canonicalPrimitive Q).positive :=
      («Σ».canonicalPrimitive_positive Q).symm
    have hQ : Q ∈ «Σ».selectedPrimitiveCollections test := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ Q, (R.contractible_iff_of_positive_eq _ hpos).mp hR,
        (hcongr R _ hpos).mp htest⟩
    exact ⟨⟨Q, hQ⟩, hpos⟩

/-- Pairwise disjointness is derived for the complete selected family. -/
theorem selectionRelation_disjoint_of_large (hpure : «Σ».IsPure)
    (test : «Σ».PrimitiveRelation → Prop)
    (hlarge : ∀ i : «Σ».selectedPrimitiveCollections test,
      n < 2 * («Σ».selectionRelation test i).fiberDimension) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».selectionRelation test i).negative) := by
  intro i j hij
  apply «Σ».no_common_cone_of_two_large_relations hpure
    («Σ».selectionRelation test i) («Σ».selectionRelation test j)
    («Σ».selectionRelation_contractible test i) («Σ».selectionRelation_contractible test j)
    (hlarge i) (hlarge j)
  exact fun h => hij («Σ».selectionRelation_positive_injective test h)

/-- A selected fiber-type class is the only selected class. Otherwise all
selected focus cones are nonempty, exactly as needed by the common blowup. -/
theorem selectionRelation_focus_cases (test : «Σ».PrimitiveRelation → Prop)
    (hdisj : «Σ».PairwiseDisjointFoci (fun i => («Σ».selectionRelation test i).negative)) :
    (∃ i : «Σ».selectedPrimitiveCollections test,
      («Σ».selectionRelation test i).negative = ∅ ∧ ∀ j, j = i) ∨
      (∀ i : «Σ».selectedPrimitiveCollections test,
        («Σ».selectionRelation test i).negative.Nonempty) := by
  by_cases hex : ∃ i : «Σ».selectedPrimitiveCollections test,
      («Σ».selectionRelation test i).negative = ∅
  · obtain ⟨i, hi⟩ := hex
    left
    refine ⟨i, hi, ?_⟩
    intro j
    by_contra hji
    apply hdisj i j (Ne.symm hji)
    refine ⟨(«Σ».selectionRelation test j).negative,
      («Σ».selectionRelation test j).negative_cone, ?_⟩
    change («Σ».selectionRelation test i).negative ∪
      («Σ».selectionRelation test j).negative ⊆ («Σ».selectionRelation test j).negative
    intro v hv
    simpa only [hi, Finset.empty_union] using hv
  · right
    intro i
    exact Finset.nonempty_iff_ne_empty.mpr (fun hi => hex ⟨i, hi⟩)

/-- Failure of either of the two side-two corner thresholds. -/
def parityObstruction (a b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) : Prop :=
  R.degree a < 2 * (R.fiberDimension : ℝ) ∨
    R.degree b < 2 * (R.fiberDimension : ℝ)

theorem parityObstruction_congr (a b : Lattice n → ℝ)
    (R S : «Σ».PrimitiveRelation) (hpos : R.positive = S.positive) :
    «Σ».parityObstruction a b R ↔ «Σ».parityObstruction a b S := by
  simp only [parityObstruction, R.degree_unique S hpos a, R.degree_unique S hpos b,
    R.fiberDimension_eq_of_positive_eq S hpos]

abbrev paritySelection (a b : Lattice n → ℝ) :=
  «Σ».selectedPrimitiveCollections («Σ».parityObstruction a b)

def paritySelectedRelation (a b : Lattice n → ℝ) (i : «Σ».paritySelection a b) :
    «Σ».PrimitiveRelation := «Σ».selectionRelation («Σ».parityObstruction a b) i

theorem parity_selection_exhaustive (a b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».paritySelection a b, R.positive = («Σ».paritySelectedRelation a b i).positive) ↔
      R.IsCombinatoriallyContractible ∧
        (R.degree a < 2 * (R.fiberDimension : ℝ) ∨
          R.degree b < 2 * (R.fiberDimension : ℝ)) :=
  «Σ».selectionRelation_exhaustive _ («Σ».parityObstruction_congr a b) R

theorem parity_selection_large (a b : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree a)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree b)
    (i : «Σ».paritySelection a b) : n < 2 * («Σ».paritySelectedRelation a b i).fiberDimension := by
  let R := «Σ».paritySelectedRelation a b i
  have hR := «Σ».selectionRelation_contractible («Σ».parityObstruction a b) i
  have htest := «Σ».selectionRelation_test («Σ».parityObstruction a b) i
  have hh : (n : ℝ) < 2 * (R.fiberDimension : ℝ) := by
    rcases htest with h | h
    · exact (ha R hR).trans_lt h
    · exact (hb R hR).trans_lt h
  exact_mod_cast hh

theorem parity_selection_disjoint (hpure : «Σ».IsPure) (a b : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree a)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible → (n : ℝ) ≤ R.degree b) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».paritySelection a b =>
      («Σ».paritySelectedRelation a b i).negative) :=
  «Σ».selectionRelation_disjoint_of_large hpure _ («Σ».parity_selection_large a b ha hb)

theorem parity_unselected_degree_bounds (a b : Lattice n → ℝ)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hn : ∀ i : «Σ».paritySelection a b,
      R.positive ≠ («Σ».paritySelectedRelation a b i).positive) :
    2 * (R.fiberDimension : ℝ) ≤ R.degree a ∧
      2 * (R.fiberDimension : ℝ) ≤ R.degree b := by
  have ht : ¬ (R.degree a < 2 * (R.fiberDimension : ℝ) ∨
      R.degree b < 2 * (R.fiberDimension : ℝ)) := by
    intro hh
    obtain ⟨i, hi⟩ := («Σ».parity_selection_exhaustive a b R).mpr ⟨hR, hh⟩
    exact hn i hi
  simpa only [not_or, not_lt] using ht

/-- The exact adjoint obstruction in equation (12). -/
def adjointObstruction (b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) : Prop :=
  0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum

theorem adjointObstruction_congr (b : Lattice n → ℝ)
    (R S : «Σ».PrimitiveRelation) (hpos : R.positive = S.positive) :
    «Σ».adjointObstruction b R ↔ «Σ».adjointObstruction b S := by
  simp only [adjointObstruction, R.degree_unique S hpos b,
    R.fiberDimension_eq_of_positive_eq S hpos, R.coefficientSum_eq_of_positive_eq S hpos]

abbrev adjointSelection (b : Lattice n → ℝ) :=
  «Σ».selectedPrimitiveCollections («Σ».adjointObstruction b)

def adjointSelectedRelation (b : Lattice n → ℝ) (i : «Σ».adjointSelection b) :
    «Σ».PrimitiveRelation := «Σ».selectionRelation («Σ».adjointObstruction b) i

theorem adjoint_selection_exhaustive (b : Lattice n → ℝ) (R : «Σ».PrimitiveRelation) :
    (∃ i : «Σ».adjointSelection b, R.positive = («Σ».adjointSelectedRelation b i).positive) ↔
      R.IsCombinatoriallyContractible ∧
        0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum :=
  «Σ».selectionRelation_exhaustive _ («Σ».adjointObstruction_congr b) R

theorem adjoint_selection_large (b : Lattice n → ℝ)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      (n : ℝ) + 1 ≤ R.degree b)
    (i : «Σ».adjointSelection b) : n < 2 * («Σ».adjointSelectedRelation b i).fiberDimension := by
  let R := «Σ».adjointSelectedRelation b i
  have hR := «Σ».selectionRelation_contractible («Σ».adjointObstruction b) i
  have htest := «Σ».selectionRelation_test («Σ».adjointObstruction b) i
  have hdegree := hb R hR
  have hcoeff : (0 : ℝ) ≤ R.coefficientSum := Nat.cast_nonneg _
  have hh : (n : ℝ) < 2 * (R.fiberDimension : ℝ) := by
    change 0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum at htest
    linarith
  exact_mod_cast hh

theorem adjoint_selection_disjoint (hpure : «Σ».IsPure) (b : Lattice n → ℝ)
    (hb : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      (n : ℝ) + 1 ≤ R.degree b) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».adjointSelection b =>
      («Σ».adjointSelectedRelation b i).negative) :=
  «Σ».selectionRelation_disjoint_of_large hpure _ («Σ».adjoint_selection_large b hb)

theorem adjoint_unselected_degree_bound (b : Lattice n → ℝ)
    (R : «Σ».PrimitiveRelation) (hR : R.IsCombinatoriallyContractible)
    (hn : ∀ i : «Σ».adjointSelection b,
      R.positive ≠ («Σ».adjointSelectedRelation b i).positive) :
    2 * (R.fiberDimension : ℝ) + 1 ≤ R.degree b + R.coefficientSum := by
  by_contra hh
  have htest : 0 < 2 * (R.fiberDimension : ℝ) + 1 - R.degree b - R.coefficientSum := by
    linarith
  obtain ⟨i, hi⟩ := («Σ».adjoint_selection_exhaustive b R).mpr ⟨hR, htest⟩
  exact hn i hi

end SmoothCompleteFan

end PaperVerification.ToricGeometry
