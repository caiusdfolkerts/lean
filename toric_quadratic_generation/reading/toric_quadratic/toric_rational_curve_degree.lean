module

public import PaperVerification.ToricProjectiveLineDegreeInvariant
public import PaperVerification.ToricDegreePolytopeBridge

@[expose] public section

/-!
# Intrinsic degree on a curve isomorphic to the projective line

Degree uses an actual isomorphism over the original field and the actual
pullback of the line bundle. The preceding automorphism theorem proves
that it is independent of this isomorphism. The wall-curve degree used in
the polytope comparison is then a special case of this intrinsic relation.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable (k : Type u) [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]

/-- The usual degree of a line bundle on an actual rational smooth
projective curve, with a genuine k-scheme isomorphism as its witness. -/
def RationalCurveHasDegree (M : C.Modules) (d : ℤ) : Prop :=
  ∃ e : C ≅ projectiveLineScheme k,
    e.hom.IsOver (Spec (CommRingCat.of k)) ∧
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d

theorem projectiveLineDegree_coordinate_independent
    (M : C.Modules) (e f : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))]
    [f.hom.IsOver (Spec (CommRingCat.of k))] {d : ℤ}
    (h : ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d) :
    ProjectiveLineHasDegree k ((Scheme.Modules.pullback f.inv).obj M) d := by
  let g : projectiveLineScheme k ≅ projectiveLineScheme k := f.symm.trans e
  letI : Scheme.Hom.IsOver g.hom (Spec (CommRingCat.of k)) := by
    change Scheme.Hom.IsOver (f.inv ≫ e.hom) (Spec (CommRingCat.of k))
    infer_instance
  have hg : g.hom≫e.inv=f.inv := by
    change (f.inv≫e.hom)≫e.inv=f.inv
    simp only [Category.assoc,e.hom_inv_id,Category.comp_id]
  let J : (Scheme.Modules.pullback g.hom).obj
      ((Scheme.Modules.pullback e.inv).obj M) ≅
        (Scheme.Modules.pullback f.inv).obj M :=
    (Scheme.Modules.pullbackComp g.hom e.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M
  exact (projectiveLineHasDegree_iso k J d).mp
    (projectiveLineHasDegree_pullbackModule k g h)

/-- Any actual k-isomorphism with the projective line computes the same
integer, so the existential choice in the definition carries no ambiguity. -/
theorem rationalCurveHasDegree_iff
    (M : C.Modules) (e : C ≅ projectiveLineScheme k)
    [e.hom.IsOver (Spec (CommRingCat.of k))] (d : ℤ) :
    RationalCurveHasDegree k M d ↔
      ProjectiveLineHasDegree k ((Scheme.Modules.pullback e.inv).obj M) d := by
  constructor
  · rintro ⟨f,hf,hd⟩
    letI := hf
    exact projectiveLineDegree_coordinate_independent k M f e hd
  · intro hd
    exact ⟨e,inferInstance,hd⟩

theorem rationalCurveHasDegree_unique {M : C.Modules} {d e : ℤ}
    (hd : RationalCurveHasDegree k M d) (he : RationalCurveHasDegree k M e) : d=e := by
  obtain ⟨f,hf,hfd⟩ := hd
  letI := hf
  exact projectiveLineHasDegree_unique k hfd
    ((rationalCurveHasDegree_iff k M f e).mp he)

theorem rationalCurveHasDegree_iso {M N : C.Modules} (F : M ≅ N) (d : ℤ) :
    RationalCurveHasDegree k M d ↔ RationalCurveHasDegree k N d := by
  constructor
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mp hd⟩
  · rintro ⟨e,he,hd⟩
    exact ⟨e,he,(projectiveLineHasDegree_iso k
      ((Scheme.Modules.pullback e.inv).mapIso F) d).mpr hd⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

instance oneDimensionalFanSchemeIso_isOver :
    (oneDimensionalFanSchemeIso Γ hd k).hom.IsOver (Spec (CommRingCat.of k)) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  change Scheme.Hom.IsOver (𝟙 (projectiveLineScheme k)) (Spec (CommRingCat.of k))
  infer_instance

theorem oneDimensionalHasDegree_iff_rationalCurve (M : (Γ.fanScheme k).Modules) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ RationalCurveHasDegree k M r :=
  (rationalCurveHasDegree_iff k M (oneDimensionalFanSchemeIso Γ hd k) r).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem wallCurve_hasDegree (hpure : «Σ».IsPure)
    (s : «Σ».fullCones) (j : Fin n) (D : CartierData («Σ».fanScheme k))
    (t : «Σ».fullCones) (w : Lattice n)
    (ht : t.val=insert w ((«Σ».wallIndices s j).image («Σ».fullConeBasis s)))
    (hw : («Σ».fullConeBasis s).repr w j = -1) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback («Σ».wallCurveInclusion s j k)).obj D.sheaf)
      («Σ».integerWallSlack («Σ».cartierCoefficients k hpure D) s w) :=
  ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    («Σ».wallIndices_codimension s j) _ _).mp
      («Σ».wallCurve_cartier_hasDegree s j k hpure D t w ht hw)

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.rationalCurveHasDegree_unique
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_hasDegree
