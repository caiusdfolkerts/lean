module

public import PaperVerification.ToricCanonicalBoxes
public import PaperVerification.ToricTargetCases

@[expose] public section

/-!
# Complete decompositions for targets satisfying the center inequalities

The finite obstruction selection, exact integer corrections, center
nefness, actual box containment, and lattice covering are all composed
here. The hypotheses contain no assumed box, nef divisor, primitive
degree bound, or decomposition. Only the original polytopes and the
literal height conditions for this branch remain.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open PaperVerification.ToricExchange
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem covered_parity_decomposition (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i,
      «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (p : Lattice n) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧
      x + y = m ∧ SameParity x p := by
  let R := «Σ».parityFamily P Q
  let hdisj := «Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ
  let Γ := «Σ».selectedFan R hne hdisj
  have hΓ : Γ.IsPure := «Σ».selectedFan_isPure R hne hdisj hpure
  obtain ⟨hnefP, hnefQ⟩ := «Σ».canonical_parity_centers_isNef hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  obtain ⟨hboxP, hboxQ⟩ := «Σ».canonical_parity_boxes hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  have hm := «Σ».parity_centers_cover_of_slacks hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne m hold hselected
  exact Γ.parity_summands_of_nef_centers hΓ P.carrier Q.carrier
    (convex_convexHull ℝ _) (convex_convexHull ℝ _)
    («Σ».parityCenter P Q P hne) («Σ».parityCenter P Q Q hne)
    hnefP hnefQ hboxP hboxQ m p hm

theorem covered_adjoint_decomposition (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
      «Σ».adjointDisplacements Q hne i + 1 ≤
        ∑ u ∈ («Σ».adjointFamily Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) :
    ∃ x y : Lattice n,
      embed n x ∈ P.carrier ∧ embed n y ∈ interior Q.carrier ∧ x + y = m := by
  let R := «Σ».adjointFamily Q
  let hdisj := «Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ
  let Γ := «Σ».selectedFan R hne hdisj
  have hΓ : Γ.IsPure := «Σ».selectedFan_isPure R hne hdisj hpure
  obtain ⟨hnefP, hnefQ⟩ := «Σ».canonical_adjoint_centers_isNef hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  obtain ⟨hboxP, hboxQ⟩ := «Σ».canonical_adjoint_boxes hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne
  have hm := «Σ».adjoint_centers_cover_of_slacks hpure
    P Q hP hQ hfanP hfanQ hboundP hboundQ hne m hold hselected
  exact Γ.integral_summands_of_nef_centers hΓ P.carrier (interior Q.carrier)
    (convex_convexHull ℝ _) (convex_convexHull ℝ _).interior
    («Σ».firstAdjointCenter P Q) («Σ».secondAdjointCenter Q hne)
    hnefP hnefQ hboxP hboxQ m hm

end PaperVerification.ToricGeometry.SmoothCompleteFan
