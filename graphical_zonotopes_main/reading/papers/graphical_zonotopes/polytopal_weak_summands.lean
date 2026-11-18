module

public import Papers.GraphicalZonotopes.GraphDefinitions

/-! # Ordinary polytopal formulations of graphical weak summands

The compact convex complementary summand is automatically a finite polytope.
The indecomposability equivalence then allows the main statements to use
precisely the paper's quantification over polytopal Minkowski decompositions.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem LatticePolytope.finitePolytope {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) :
    IsFinitePolytope Q := by
  classical
  obtain ⟨P,hP⟩ := hQ
  refine ⟨P.image (fun x : V → ℤ => fun v => (x v : ℝ)),?_⟩
  simpa only [Finset.coe_image] using hP.symm

/-- Every actual compact convex complement of a finite graphical-zonotope
summand is itself a finite polytope. Nonemptiness of the first summand is
derived from the sum equality, rather than imposed as an extra hypothesis. -/
theorem finite_complement_of_graphical_sum
    {G : SimpleGraph V} {Q R : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hR : IsCompact R) (hcR : Convex ℝ R)
    (hnR : R.Nonempty) {a : ℝ} (ha : 0 ≤ a)
    (he : Q + R = a • graphicalZonotope G) :
    Q.Nonempty ∧ IsFinitePolytope R := by
  have hzn : Normalized (a • graphFunction G) := by
    change a * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hzs : Supermodular (a • graphFunction G) :=
    (graphFunction_supermodular G).smul ha
  have hsum : Q + R = basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G)
      (graphFunction_supermodular G) ha,baseGraphFunction_eq_graphicalZonotope]
    exact he
  obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
  rw [← hsum] at hx
  obtain ⟨q,hq,r,hr,hqr⟩ := hx
  have hnQ : Q.Nonempty := ⟨q,hq⟩
  have hsumR : R + Q = basePolytope (a • graphFunction G) := by
    rw [add_comm]
    exact hsum
  have hsm := summand_lowerSupport_supermodular hzn hzs hR hQ.compact hnR hnQ hsumR
  have hbody := summand_eq_basePolytope hzn hzs hR hQ.compact hcR hnR hnQ hsumR
  have hgp : IsGeneralizedPermutahedron R :=
    ⟨lowerSupport R,lowerSupport_normalized hR hnR,hsm,hbody⟩
  exact ⟨hnQ,hgp.finitePolytope⟩

/-- The fixed-dilation summand predicate is equivalent to the ordinary
finite-polytope complement formulation, including at dilation zero. -/
theorem isMinkowskiSummand_graphical_iff_finite_complement
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) {a : ℝ} (ha : 0 ≤ a) :
    IsMinkowskiSummand Q (a • graphicalZonotope G) ↔
      ∃ R : Set (V → ℝ),IsFinitePolytope R ∧ R.Nonempty ∧
        Q + R = a • graphicalZonotope G := by
  constructor
  · rintro ⟨R,hR,hcR,hnR,he⟩
    exact ⟨R,(finite_complement_of_graphical_sum hQ hR hcR hnR ha he).2,hnR,he⟩
  · rintro ⟨R,hR,hnR,he⟩
    exact ⟨R,hR.compact,hR.convex,hnR,he⟩

/-- A genuine weak summand of a graphical zonotope has a positive
dilation with a finite polytope as its complementary summand. -/
theorem isWeakMinkowskiSummand_graphical_iff_finite_complement
    {G : SimpleGraph V} {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ↔
      ∃ a : ℝ,0 < a ∧ ∃ R : Set (V → ℝ),IsFinitePolytope R ∧ R.Nonempty ∧
        Q + R = a • graphicalZonotope G := by
  constructor
  · rintro ⟨a,ha,h⟩
    exact ⟨a,ha,(isMinkowskiSummand_graphical_iff_finite_complement hQ ha.le).mp h⟩
  · rintro ⟨a,ha,h⟩
    exact ⟨a,ha,(isMinkowskiSummand_graphical_iff_finite_complement hQ ha.le).mpr h⟩

theorem weakSummand_indecomposable_iff_polytopal
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro hi
    exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩
  · intro hi
    obtain ⟨a,ha,R,hR,hcR,hnR,he⟩ := hw
    have hzn : Normalized (a • graphFunction G) := by
      change a * graphFunction G ∅ = 0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular (a • graphFunction G) :=
      (graphFunction_supermodular G).smul ha.le
    have hsum : Q + R = basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G)
        (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
      exact he
    have hn := lowerSupport_normalized hQ.compact hi.1
    have hsm := summand_lowerSupport_supermodular hzn hzs hQ.compact hR hi.1 hnR hsum
    have hbody := summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hi.1 hnR hsum
    exact (minkowskiIndecomposable_iff_polytopal
      ⟨lowerSupport Q,hn,hsm,hbody⟩).mpr hi

end GraphicalZonotopes
