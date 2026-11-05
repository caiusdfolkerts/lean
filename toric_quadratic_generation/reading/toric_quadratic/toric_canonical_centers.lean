module

public import PaperVerification.ToricCanonicalCorrections

@[expose] public section

/-!
# Centers for the exhaustive obstruction families

The families below are determined by the original two integral polytopes.
Every displacement is the exact integer ceiling appearing in the paper.
Nefness is deduced from the original edge hypotheses; no numerical repair
inequality or unselected-class positivity is an additional hypothesis.
The nonempty-focus hypothesis describes the branch complementary to the
fiber-type case and is discharged by `selectionRelation_focus_cases`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

abbrev parityIndices (P Q : LatticePolytope n) :=
  «Σ».paritySelection (fun u => (P.integralSupport u : ℝ))
    (fun u => (Q.integralSupport u : ℝ))

def parityFamily (P Q : LatticePolytope n) (i : «Σ».parityIndices P Q) :
    «Σ».PrimitiveRelation :=
  «Σ».paritySelectedRelation (fun u => (P.integralSupport u : ℝ))
    (fun u => (Q.integralSupport u : ℝ)) i

theorem parityFamily_contractible (P Q : LatticePolytope n)
    (i : «Σ».parityIndices P Q) :
    («Σ».parityFamily P Q i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem parityFamily_large (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (i : «Σ».parityIndices P Q) : n < 2 * («Σ».parityFamily P Q i).fiberDimension :=
  «Σ».parity_selection_large _ _
    (P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP)
    (Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ) i

theorem parityFamily_disjoint (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».parityFamily P Q i).negative) :=
  «Σ».parity_selection_disjoint_of_edges hpure P Q hP hQ hfanP hfanQ hboundP hboundQ

/-- The complete obstruction family either contains an empty focus, or
every focus is nonempty. In the former case the unique selected relation
supplies the bundle branch of the induction. -/
theorem parityFamily_focus_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    (∃ i : «Σ».parityIndices P Q, («Σ».parityFamily P Q i).negative = ∅) ∨
      (∀ i : «Σ».parityIndices P Q, («Σ».parityFamily P Q i).negative.Nonempty) := by
  rcases «Σ».selectionRelation_focus_cases
      («Σ».parityObstruction (fun u => (P.integralSupport u : ℝ))
        (fun u => (Q.integralSupport u : ℝ)))
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ) with
    ⟨i, hi, _⟩ | hne
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr hne

def parityDisplacements (P Q L : LatticePolytope n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (i : «Σ».parityIndices P Q) : ℤ :=
  («Σ».parityFamily P Q i).parityDisplacement (hne i) L.integralSupport

def parityCenter (P Q L : LatticePolytope n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».parityFamily P Q)
    (fun w => (L.integralSupport w : ℝ)) v - 1 -
      ∑ i, if v = «Σ».selectedRay («Σ».parityFamily P Q) i then
        («Σ».parityDisplacements P Q L hne i : ℝ) else 0

/-- Both centers are nef on the same actual selected fan. All selection,
degree, displacement and disjointness data are derived from the two
original smooth polytopes and their literal edge lengths. -/
theorem canonical_parity_centers_isNef (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty) :
    let «Σ'» := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    «Σ'».IsNef («Σ».parityCenter P Q P hne) ∧
      «Σ'».IsNef («Σ».parityCenter P Q Q hne) := by
  let R := «Σ».parityFamily P Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».parityFamily_contractible P Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  have make_center (L : LatticePolytope n) (hL : L.Smooth)
      (hfanL : «Σ».realCones = L.normalFan) (hboundL : L.EdgesAtLeast n)
      (hinactive : ∀ S : «Σ».PrimitiveRelation, S.IsCombinatoriallyContractible →
        (∀ i, S.positive ≠ (R i).positive) →
        2 * (S.fiberDimension : ℝ) ≤ S.degree (fun u => (L.integralSupport u : ℝ))) :
      («Σ».selectedFan R hne hdisj).IsNef («Σ».parityCenter P Q L hne) := by
    apply «Σ».parity_center_isNef R hR hne hdisj hpure L hL hfanL hboundL
      (fun i => («Σ».parityDisplacements P Q L hne i : ℝ))
    · intro i
      have hb := (R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL
      have hq : (1 : ℝ) ≤ (R i).negative.card := by
        exact_mod_cast Finset.card_pos.mpr (hne i)
      change ((R i).negative.card : ℝ) - 1 ≤
        ((R i).parityDisplacement (hne i) L.integralSupport : ℝ)
      linarith [hb.2.1]
    · intro i
      exact ((R i).parityDisplacement_bounds (hR i) (hne i) (hlarge i)
        hpure L hL hfanL hboundL).2.2.2.1
    · exact hinactive
  constructor
  · apply make_center P hP hfanP hboundP
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).1
  · apply make_center Q hQ hfanQ hboundQ
    intro S hS hn
    exact («Σ».parity_unselected_degree_bounds _ _ S hS hn).2

abbrev adjointIndices (Q : LatticePolytope n) :=
  «Σ».adjointSelection (fun u => (Q.integralSupport u : ℝ))

def adjointFamily (Q : LatticePolytope n) (i : «Σ».adjointIndices Q) :
    «Σ».PrimitiveRelation :=
  «Σ».adjointSelectedRelation (fun u => (Q.integralSupport u : ℝ)) i

theorem adjointFamily_contractible (Q : LatticePolytope n)
    (i : «Σ».adjointIndices Q) :
    («Σ».adjointFamily Q i).IsCombinatoriallyContractible :=
  «Σ».selectionRelation_contractible _ i

theorem adjointFamily_large (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1))
    (i : «Σ».adjointIndices Q) : n < 2 * («Σ».adjointFamily Q i).fiberDimension := by
  apply «Σ».adjoint_selection_large _ _ i
  intro S hS
  simpa only [Nat.cast_add, Nat.cast_one] using
    Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ S hS

theorem adjointFamily_disjoint (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    «Σ».PairwiseDisjointFoci (fun i => («Σ».adjointFamily Q i).negative) :=
  «Σ».adjoint_selection_disjoint_of_edges hpure Q hQ hfanQ hboundQ

theorem adjointFamily_focus_cases (hpure : «Σ».IsPure)
    (Q : LatticePolytope n) (hQ : Q.Smooth)
    (hfanQ : «Σ».realCones = Q.normalFan) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    (∃ i : «Σ».adjointIndices Q, («Σ».adjointFamily Q i).negative = ∅) ∨
      (∀ i : «Σ».adjointIndices Q, («Σ».adjointFamily Q i).negative.Nonempty) := by
  rcases «Σ».selectionRelation_focus_cases
      («Σ».adjointObstruction (fun u => (Q.integralSupport u : ℝ)))
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ) with
    ⟨i, hi, _⟩ | hne
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr hne

def adjointDisplacements (Q : LatticePolytope n)
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (i : «Σ».adjointIndices Q) : ℤ :=
  («Σ».adjointFamily Q i).adjointDisplacement (hne i) Q.integralSupport

def firstAdjointCenter (P Q : LatticePolytope n) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».adjointFamily Q)
    (fun w => (P.integralSupport w : ℝ)) v - 1 / 2 -
      ∑ i, if v = «Σ».selectedRay («Σ».adjointFamily Q) i then
        ((«Σ».adjointFamily Q i).negative.card : ℝ) - 1 else 0

def secondAdjointCenter (Q : LatticePolytope n)
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback («Σ».adjointFamily Q)
    (fun w => (Q.integralSupport w : ℝ)) v - 3 / 2 -
      ∑ i, if v = «Σ».selectedRay («Σ».adjointFamily Q) i then
        («Σ».adjointDisplacements Q hne i : ℝ) else 0

/-- The two unequal adjoint centers, with the exact original obstruction
test and integer correction. The second center is for boxes lying in the
interior lattice-point polytope of the second factor. -/
theorem canonical_adjoint_centers_isNef (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty) :
    let «Σ'» := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    «Σ'».IsNef («Σ».firstAdjointCenter P Q) ∧
      «Σ'».IsNef («Σ».secondAdjointCenter Q hne) := by
  let R := «Σ».adjointFamily Q
  have hR : ∀ i, (R i).IsCombinatoriallyContractible :=
    «Σ».adjointFamily_contractible Q
  have hlarge : ∀ i, n < 2 * (R i).fiberDimension :=
    «Σ».adjointFamily_large hpure Q hQ hfanQ hboundQ
  have hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  constructor
  · exact «Σ».first_adjoint_center_isNef R hR hne hdisj
      hpure P hP hfanP hboundP hlarge
  · apply «Σ».second_adjoint_center_isNef R hR hne hdisj
      hpure Q hQ hfanQ hboundQ
      (fun i => («Σ».adjointDisplacements Q hne i : ℝ))
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.1
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.2.1
    · intro i
      exact ((R i).adjointDisplacement_bounds (hR i) (hne i)
        hpure Q hQ hfanQ hboundQ («Σ».selectionRelation_test _ i)).2.2.2
    · intro S hS hn
      have h := «Σ».adjoint_unselected_degree_bound
        (fun u => (Q.integralSupport u : ℝ)) S hS hn
      simpa only [S.coefficientSum_cast] using h

end SmoothCompleteFan

end PaperVerification.ToricGeometry
