module

public import PaperVerification.ToricRationalCurveDegree
public import PaperVerification.ToricInvertiblePullback

@[expose] public section

/-!
# Existence of the ordinary degree for every invertible sheaf on a rational curve

Every invertible sheaf has an actual fractional Cartier presentation. On
the projective line its integer degree is the unique twist O(d). Pullback
by any genuine isomorphism with the projective line gives existence on a
rational curve; coordinate independence was proved separately.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes

variable (k : Type u) [Field k]

/-- The usual integer degree exists for every actual invertible sheaf
on the projective line, without a chosen divisor presentation. -/
theorem projectiveLineModule_existsUnique_degree
    (M : (projectiveLineScheme k).Modules) (hM : IsInvertibleModule M) :
    ∃! d : ℤ, ProjectiveLineHasDegree k M d := by
  obtain ⟨D,⟨F⟩⟩ := exists_cartierData_of_isInvertibleModule M hM
  obtain ⟨d,hd,_⟩ := projectiveLineCartier_existsUnique_degree k D
  have hMd : ProjectiveLineHasDegree k M d :=
    (projectiveLineHasDegree_iso k F d).mpr hd
  exact ⟨d,hMd,fun e he => projectiveLineHasDegree_unique k he hMd⟩

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]

/-- Every invertible sheaf on a curve genuinely isomorphic to P¹ has
exactly one degree. The isomorphism is over the original base field. -/
theorem rationalCurveModule_existsUnique_degree
    (M : C.Modules) (hM : IsInvertibleModule M)
    (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] :
    ∃! d : ℤ, RationalCurveHasDegree k M d := by
  obtain ⟨d,hd,_⟩ := projectiveLineModule_existsUnique_degree k
    ((Scheme.Modules.pullback e.inv).obj M)
    (isInvertibleModule_pullback e.inv hM)
  have hMd : RationalCurveHasDegree k M d :=
    (rationalCurveHasDegree_iff k M e d).mpr hd
  exact ⟨d,hMd,fun r hr => rationalCurveHasDegree_unique k hr hMd⟩

/-- The degree relation is nonempty precisely when the actual curve is
the projective line over k. In particular, a geometric classification
of invariant curves supplies existence for every restricted line bundle. -/
theorem rationalCurveHasDegree_exists_iff
    (M : C.Modules) (hM : IsInvertibleModule M) :
    (∃ d : ℤ, RationalCurveHasDegree k M d) ↔
      ∃ e : C ≅ projectiveLineScheme k,
        e.hom.IsOver (Spec (CommRingCat.of k)) := by
  constructor
  · rintro ⟨d,e,he,_⟩
    exact ⟨e,he⟩
  · rintro ⟨e,he⟩
    letI := he
    obtain ⟨d,hd,_⟩ := rationalCurveModule_existsUnique_degree k M hM e
    exact ⟨d,hd⟩

/-- Restricting any actual Cartier line bundle along any curve
immersion preserves invertibility, so its degree exists once the curve
has been identified with the projective line. -/
theorem restrictedCartier_existsUnique_degree
    {X : Scheme.{u}} [IsIntegral X]
    (D : CartierData X) (i : C ⟶ X)
    (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] :
    ∃! d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback i).obj D.sheaf) d :=
  rationalCurveModule_existsUnique_degree k _
    (isInvertibleModule_pullback i D.locallyFree) e

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.rationalCurveModule_existsUnique_degree
#print axioms PaperVerification.ToricGeometry.restrictedCartier_existsUnique_degree
