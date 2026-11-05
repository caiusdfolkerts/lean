module

public import PaperVerification.ToricCenterTargets

@[expose] public section

/-!
# Exhaustive integral-height alternatives for the mixed induction

The alternatives use actual primitive facet slacks. The ceiling bounds
give the precise near-locus height budget; no target is discarded at a
boundary or at an unblown singleton focus.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem parity_target_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    (∃ u ∈ «Σ».rays, latticeSlack (P.integralSupport + Q.integralSupport) m u = 1) ∨
    (∃ i : «Σ».parityIndices P Q,
      (∑ u ∈ («Σ».parityFamily P Q i).negative,
        latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
          «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 1 ∧
      (∑ u ∈ («Σ».parityFamily P Q i).negative,
        latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
          2 * ((n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension) - 3) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∀ i, «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) := by
  have hpos := «Σ».latticeSlack_pos_of_interior_minkowski hpure P Q hfanP hfanQ m hm
  by_cases hold : ∀ u ∈ «Σ».rays,
      2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u
  · right
    by_cases hcover : ∀ i,
        «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
          ∑ u ∈ («Σ».parityFamily P Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u
    · exact Or.inr ⟨hold, hcover⟩
    · left
      push_neg at hcover
      obtain ⟨i, hi⟩ := hcover
      have hR := «Σ».parityFamily_contractible P Q i
      have hlarge := «Σ».parityFamily_large hpure P Q hP hQ hfanP hfanQ hboundP hboundQ i
      have hA := ((«Σ».parityFamily P Q i).parityDisplacement_bounds hR (hne i) hlarge
        hpure P hP hfanP hboundP).2.2.1
      have hB := ((«Σ».parityFamily P Q i).parityDisplacement_bounds hR (hne i) hlarge
        hpure Q hQ hfanQ hboundQ).2.2.1
      have htA : «Σ».parityDisplacements P Q P hne i ≤
          (n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension - 2 := by
        exact_mod_cast hA
      have htB : «Σ».parityDisplacements P Q Q hne i ≤
          (n : ℤ) - 2 * («Σ».parityFamily P Q i).baseDimension - 2 := by
        exact_mod_cast hB
      exact ⟨i, by omega, by omega⟩
  · left
    push_neg at hold
    obtain ⟨u, hu, hd⟩ := hold
    have hh := hpos u hu
    exact ⟨u, hu, by omega⟩

theorem adjoint_target_cases (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    (∃ u ∈ «Σ».rays, latticeSlack (P.integralSupport + Q.integralSupport) m u = 1) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∃ i : «Σ».adjointIndices Q,
        2 * ((«Σ».adjointFamily Q i).negative.card : ℤ) ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u ∧
        (∑ u ∈ («Σ».adjointFamily Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) ≤
            ((«Σ».adjointFamily Q i).negative.card : ℤ) + «Σ».adjointDisplacements Q hne i) ∨
    ((∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u) ∧
      ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
        «Σ».adjointDisplacements Q hne i + 1 ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u) := by
  have hpos := «Σ».latticeSlack_pos_of_interior_minkowski hpure P Q hfanP hfanQ m hm
  by_cases hold : ∀ u ∈ «Σ».rays,
      2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u
  · right
    by_cases hcover : ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
        «Σ».adjointDisplacements Q hne i + 1 ≤
          ∑ u ∈ («Σ».adjointFamily Q i).negative,
            latticeSlack (P.integralSupport + Q.integralSupport) m u
    · exact Or.inr ⟨hold, hcover⟩
    · left
      push_neg at hcover
      obtain ⟨i, hi⟩ := hcover
      refine ⟨hold, i, ?_, by omega⟩
      calc
        2 * ((«Σ».adjointFamily Q i).negative.card : ℤ) =
            ∑ _u ∈ («Σ».adjointFamily Q i).negative, (2 : ℤ) := by simp; ring
        _ ≤ _ := Finset.sum_le_sum (fun u hu => hold u
          («Σ».ray_mem_of_mem_cone («Σ».adjointFamily Q i).negative_cone hu))
  · left
    push_neg at hold
    obtain ⟨u, hu, hd⟩ := hold
    have hh := hpos u hu
    exact ⟨u, hu, by omega⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
