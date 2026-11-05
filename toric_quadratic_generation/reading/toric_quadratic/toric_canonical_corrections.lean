module

public import PaperVerification.ToricObstructionSelection
public import PaperVerification.ToricCentersNef

@[expose] public section

/-!
# Exact integer displacements from the actual primitive degrees

The ceiling corrections are evaluated on the genuine integral support
degree and the least actual negative coefficient. Their normal-height,
base-dimension, and fiber-repair bounds follow from the original literal
edge hypotheses.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem coefficientSum_cast : (R.coefficientSum : ℝ) = R.negativeCoefficientSum := by
  simp only [coefficientSum, negativeCoefficientSum, Nat.cast_sum]

def baseDimension : ℕ := n - R.fiberDimension - R.negative.card

theorem dimension_eq (hR : R.IsCombinatoriallyContractible) :
    n = R.fiberDimension + R.negative.card + R.baseDimension := by
  have h := R.contractible_dimension_bound hR
  unfold baseDimension
  omega

def parityDisplacement (hne : R.negative.Nonempty) (a : Lattice n → ℤ) : ℤ :=
  parityCorrection R.fiberDimension R.negative.card (R.integerDegree a)
    (R.minimumCoefficient hne)

def adjointDisplacement (hne : R.negative.Nonempty) (a : Lattice n → ℤ) : ℤ :=
  adjointCorrection R.fiberDimension R.negative.card (R.integerDegree a)
    R.coefficientSum (R.minimumCoefficient hne)

/-- Every scalar bound for the exact parity displacement, with its degree
and minimum coefficient derived from the original polytope. -/
theorem parityDisplacement_bounds
    (hR : R.IsCombinatoriallyContractible) (hne : R.negative.Nonempty)
    (hlarge : n < 2 * R.fiberDimension)
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n) :
    0 ≤ (R.parityDisplacement hne P.integralSupport : ℝ) ∧
      2 * ((R.negative.card : ℝ) - 1) ≤ R.parityDisplacement hne P.integralSupport ∧
      (R.parityDisplacement hne P.integralSupport : ℝ) ≤
        (n : ℝ) - 2 * R.baseDimension - 2 ∧
      (R.parityDisplacement hne P.integralSupport : ℝ) ≤
        (R.fiberDimension : ℝ) + R.negative.card - 2 ∧
      2 * (R.fiberDimension : ℝ) ≤ R.degree (fun u => (P.integralSupport u : ℝ)) +
        (R.minimumCoefficient hne : ℝ) * R.parityDisplacement hne P.integralSupport := by
  have hq : (1 : ℤ) ≤ R.negative.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hb : (0 : ℤ) ≤ R.baseDimension := Int.natCast_nonneg _
  have hm : (1 : ℤ) ≤ R.minimumCoefficient hne := by
    exact_mod_cast (R.minimumCoefficient_spec hne).1
  have hdim : (n : ℤ) = R.fiberDimension + R.negative.card + R.baseDimension := by
    exact_mod_cast R.dimension_eq hR
  have hl : (n : ℤ) < 2 * (R.fiberDimension : ℤ) := by exact_mod_cast hlarge
  have hdR := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR
  rw [← R.integerDegree_cast] at hdR
  have hd : (n : ℤ) ≤ R.integerDegree P.integralSupport := by exact_mod_cast hdR
  obtain ⟨h0, hlow, hup, hup', hrepair⟩ := parityCorrection_bounds
    n R.fiberDimension R.negative.card R.baseDimension
    (R.integerDegree P.integralSupport) (R.minimumCoefficient hne)
    hq hb hm hdim hl hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast h0
  · exact_mod_cast hlow
  · exact_mod_cast hup
  · exact_mod_cast hup'
  · rw [← R.integerDegree_cast]
    exact_mod_cast hrepair

/-- The exact adjoint correction, including its literal inner fiber-degree
repair and the complete normal-height budget. -/
theorem adjointDisplacement_bounds
    (hR : R.IsCombinatoriallyContractible) (hne : R.negative.Nonempty)
    (hpure : «Σ».IsPure) (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (hselected : «Σ».adjointObstruction (fun u => (P.integralSupport u : ℝ)) R) :
    n < 2 * R.fiberDimension ∧
      2 * ((R.negative.card : ℝ) - 1) ≤ R.adjointDisplacement hne P.integralSupport ∧
      (R.adjointDisplacement hne P.integralSupport : ℝ) ≤
        (n : ℝ) - 2 * R.baseDimension - 2 ∧
      2 * (R.fiberDimension : ℝ) + 1 ≤ R.degree (fun u => (P.integralSupport u : ℝ)) +
        R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
          ((R.adjointDisplacement hne P.integralSupport : ℝ) + 1 - R.negative.card) := by
  have hq : (1 : ℤ) ≤ R.negative.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hb : (0 : ℤ) ≤ R.baseDimension := Int.natCast_nonneg _
  have hm : (1 : ℤ) ≤ R.minimumCoefficient hne := by
    exact_mod_cast (R.minimumCoefficient_spec hne).1
  have hdim : (n : ℤ) = R.fiberDimension + R.negative.card + R.baseDimension := by
    exact_mod_cast R.dimension_eq hR
  have hdR := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR
  rw [← R.integerDegree_cast] at hdR
  have hd : (n : ℤ) + 1 ≤ R.integerDegree P.integralSupport := by exact_mod_cast hdR
  have hcoeff : (R.negative.card : ℤ) ≤ R.coefficientSum := by
    exact_mod_cast R.negative_card_le_coefficientSum
  have hsel : (0 : ℤ) < 2 * (R.fiberDimension : ℤ) + 1 -
      R.integerDegree P.integralSupport - R.coefficientSum := by
    change 0 < 2 * (R.fiberDimension : ℝ) + 1 -
      R.degree (fun u => (P.integralSupport u : ℝ)) - R.coefficientSum at hselected
    rw [← R.integerDegree_cast] at hselected
    exact_mod_cast hselected
  obtain ⟨hlarge, hlow, hup, hrepair⟩ := adjointCorrection_bounds
    n R.fiberDimension R.negative.card R.baseDimension
    (R.integerDegree P.integralSupport) R.coefficientSum (R.minimumCoefficient hne)
    hq hb hm hdim hd hcoeff hsel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hlarge
  · exact_mod_cast hlow
  · exact_mod_cast hup
  · rw [← R.integerDegree_cast, ← R.coefficientSum_cast]
    exact_mod_cast hrepair

end SmoothCompleteFan.PrimitiveRelation

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem parity_selection_disjoint_of_edges (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».paritySelection
      (fun u => (P.integralSupport u : ℝ)) (fun u => (Q.integralSupport u : ℝ)) =>
      («Σ».paritySelectedRelation
        (fun u => (P.integralSupport u : ℝ)) (fun u => (Q.integralSupport u : ℝ)) i).negative) :=
  «Σ».parity_selection_disjoint hpure _ _
    (P.contractible_degree_lower_bound hP «Σ» hpure hfanP hboundP)
    (Q.contractible_degree_lower_bound hQ «Σ» hpure hfanQ hboundQ)

theorem adjoint_selection_disjoint_of_edges (hpure : «Σ».IsPure)
    (P : LatticePolytope n) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1)) :
    «Σ».PairwiseDisjointFoci (fun i : «Σ».adjointSelection (fun u => (P.integralSupport u : ℝ)) =>
      («Σ».adjointSelectedRelation (fun u => (P.integralSupport u : ℝ)) i).negative) := by
  apply «Σ».adjoint_selection_disjoint hpure
  intro R hR
  simpa only [Nat.cast_add, Nat.cast_one] using
    P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound R hR

end SmoothCompleteFan

end PaperVerification.ToricGeometry
