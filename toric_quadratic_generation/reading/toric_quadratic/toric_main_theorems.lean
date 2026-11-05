module

public import PaperVerification.ToricCoveredTargets
public import PaperVerification.ToricNearSelectedParity
public import PaperVerification.ToricNearSelectedAdjoint
public import PaperVerification.ToricFanConstruction
public import PaperVerification.ToricMixedBaseCases
public import PaperVerification.ToricParityClasses
public import PaperVerification.ToricMainReduction

@[expose] public section

/-!
# The mixed theorems by induction on the actual dimension

The induction hypotheses below are precisely the original mixed assertions
in smaller dimensions. The obstruction families are constructed from all
contractible primitive relations that fail the stated degree tests. Their
focus alternatives and the exhaustive literal-height alternatives account
for every target. No local box, quotient, positivity, or decomposition
assertion is an additional hypothesis of the resulting theorem.

These declarations concern actual lattice polytopes. The separate
scheme/divisor correspondence is needed to transfer the mixed assertions
to the manuscript's scheme-theoretic input language.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical Pointwise

theorem parity_dimension_statement (n : ℕ) : ParityDimensionStatement n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
      intro P Q hP hQ hPQ hboundP hboundQ m hm p
      by_cases hn : n = 0
      · subst n
        exact P.mixed_parity_dimension_zero Q m p
      · obtain ⟨«Σ», hfanP, hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
        have hfanQ : «Σ».realCones = Q.normalFan := hfanP.trans hPQ
        rcases «Σ».parityFamily_focus_cases hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ with ⟨i, hi⟩ | hne
        · exact «Σ».polytope_fiber_type_parity hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ («Σ».parityFamily P Q i)
            («Σ».parityFamily_contractible P Q i) hi IH m hm p
        · rcases «Σ».parity_target_cases hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hm with
            ⟨u, hu, hu1⟩ | ⟨i, _, hi⟩ | ⟨hold, hcover⟩
          · exact «Σ».polytope_near_facet_parity hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ u hu m hm hu1 IH p
          · apply «Σ».polytope_near_selected_parity hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ («Σ».parityFamily P Q i)
              («Σ».parityFamily_contractible P Q i) (hne i)
              («Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ i)
              m hm _ IH p
            omega
          · exact «Σ».covered_parity_decomposition hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hold hcover p

/-- The full prescribed-parity theorem for smooth lattice polytopes
with the same actual normal fan, in every dimension. -/
theorem toric_theorem_1_2_polytope : Theorem1_2PolytopeStatement :=
  parity_dimension_statement

/-- The exact quotient-class formulation, with the actual quotient
`M / 2M` and an arbitrary prescribed class. -/
theorem toric_theorem_1_2_quotient_classes
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
      a + b = m ∧ parityClass n a = α :=
  theorem1_2_iff_quotient_classes.mp toric_theorem_1_2_polytope
    n P Q hP hQ hfan hboundP hboundQ m hm α

theorem adjoint_dimension_statement (n : ℕ) : AdjointDimensionStatement n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
      intro P Q hP hQ hPQ hboundP hboundQ m hm
      by_cases hn : n = 0
      · subst n
        exact (P.mixed_adjoint_dimension_zero Q m).mp hm
      · obtain ⟨«Σ», hfanP, hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
        have hfanQ : «Σ».realCones = Q.normalFan := hfanP.trans hPQ
        rcases «Σ».adjointFamily_focus_cases hpure Q hQ hfanQ hboundQ with
          ⟨i, hi⟩ | hne
        · exact «Σ».polytope_fiber_type_adjoint hpure P Q hP hQ hfanP hfanQ
            hboundP hboundQ («Σ».adjointFamily Q i)
            («Σ».adjointFamily_contractible Q i) hi IH m hm
        · rcases «Σ».adjoint_target_cases hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hm with
            ⟨u, hu, hu1⟩ | ⟨hold, i, _, hi⟩ | ⟨hold, hcover⟩
          · exact «Σ».polytope_near_facet_adjoint hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ u hu m hm hu1 IH
          · have ht : «Σ».adjointDisplacements Q hne i ≤
                (n : ℤ) - 2 * («Σ».adjointFamily Q i).baseDimension - 2 := by
              have hreal := ((«Σ».adjointFamily Q i).adjointDisplacement_bounds
                («Σ».adjointFamily_contractible Q i) (hne i) hpure Q hQ hfanQ hboundQ
                («Σ».selectionRelation_test _ i)).2.2.1
              exact_mod_cast hreal
            exact «Σ».polytope_near_selected_adjoint hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ («Σ».adjointFamily Q i)
              («Σ».adjointFamily_contractible Q i) (hne i)
              («Σ».adjointDisplacements Q hne i) ht m hm
              (fun u hu => hold u
                («Σ».ray_mem_of_mem_cone («Σ».adjointFamily Q i).negative_cone hu))
              hi IH
          · exact «Σ».covered_adjoint_decomposition hpure P Q hP hQ hfanP hfanQ
              hboundP hboundQ hne m hold hcover

/-- The full adjoint lattice-point equality, including both inclusions,
with no additional positivity or nondegeneracy hypothesis on the adjoint
polytope. -/
theorem toric_theorem_1_3_polytope : Theorem1_3PolytopeStatement :=
  theorem1_3_iff_interior_decomposition.mpr adjoint_dimension_statement

/-- The same adjoint statement written as the literal equality of
pointwise sums of lattice-point sets. -/
theorem toric_theorem_1_3_polytope_sets
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    {m : Lattice n | embed n m ∈ P.carrier} +
        {m : Lattice n | embed n m ∈ interior Q.carrier} =
      {m : Lattice n | embed n m ∈ interior (P.minkowskiSum Q)} := by
  ext m
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact (toric_theorem_1_3_polytope n P Q hP hQ hfan hboundP hboundQ m).mpr
      ⟨a, b, ha, hb, hab⟩
  · intro hm
    obtain ⟨a, b, ha, hb, hab⟩ :=
      (toric_theorem_1_3_polytope n P Q hP hQ hfan hboundP hboundQ m).mp hm
    exact ⟨a, ha, b, hb, hab⟩

/-- Theorem 1.1 over an arbitrary field: unrestricted integer
decomposition and equality of the actual polynomial kernel with the
ideal generated by all quadratic exchange binomials. -/
theorem toric_theorem_1_1 (k : Type*) [Field k] : Theorem1_1Statement k :=
  theorem1_1_of_mixed k toric_theorem_1_2_polytope toric_theorem_1_3_polytope

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.toric_theorem_1_2_polytope
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_2_quotient_classes
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_3_polytope
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_3_polytope_sets
#print axioms PaperVerification.ToricGeometry.toric_theorem_1_1
