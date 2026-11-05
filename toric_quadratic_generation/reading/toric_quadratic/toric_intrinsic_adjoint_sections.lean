module

public import PaperVerification.ToricIntrinsicMixedTheorems
public import PaperVerification.ToricFanIntrinsicCanonical
public import PaperVerification.ToricIntrinsicDimension
public import PaperVerification.ToricInvertibleFractionalPresentation
public import PaperVerification.ToricModuleSectionMultiplication
public import PaperVerification.ToricCartierSchemeIso

@[expose] public section

/-!
# Intrinsic adjoint multiplication on the original toric variety

The canonical factor in the final statement is the genuine top exterior
power of the intrinsic Kähler sheaf. It is defined before choosing a fan.
The fan reconstruction and the actual differential calculation prove its
invertibility and produce a Cartier presentation. Surjectivity is then
transported through the actual scheme and sheaf isomorphisms, and the
presentation is removed from the final section-multiplication statement.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical Pointwise BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance («Σ» : SmoothCompleteFan n) : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

include T in
/-- A canonical Cartier presentation is derived from the genuine
intrinsic cotangent sheaf, with no fan or canonical-divisor input. -/
theorem exists_intrinsicCanonicalCartier
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ K : CartierData X.left,
      Nonempty (K.sheaf≅topDifferentialSheaf k X.left n) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hD
  let e₀ : «Σ».fanScheme k≅X.left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.inv.IsOver (Spec (CommRingCat.of k)) := ⟨e.inv.w⟩
  let b₀ : Module.Basis (Fin n) ℤ (Lattice n) := Pi.basisFun ℤ (Fin n)
  let «KΣ» := «Σ».differentialVolumeData k hpure b₀
  refine ⟨«KΣ».dominantPullback e₀.inv,⟨?_⟩⟩
  exact («KΣ».dominantPullbackSheafIso e₀.inv).symm ≪≫
    (Scheme.Modules.pullback e₀.inv).mapIso
      («Σ».intrinsicTopDifferentialVolumeIso k hpure b₀).symm ≪≫
    topDifferentialSheafPullbackIso e₀.inv n k

include T in
theorem intrinsicCanonical_isInvertible
    (D : CartierData X.left) (hD : D.IsAmple) :
    IsInvertibleModule (topDifferentialSheaf k X.left n) := by
  obtain ⟨K,⟨F⟩⟩ := T.exists_intrinsicCanonicalCartier D hD
  exact isInvertibleModule_of_iso F K.locallyFree

/-- An actual Cartier presentation whose underlying sheaf is literally
the intrinsic canonical sheaf. Its fractional embedding is constructed. -/
def intrinsicCanonicalCartier
    (D : CartierData X.left) (hD : D.IsAmple) : CartierData X.left :=
  invertibleFractionalPresentation (topDifferentialSheaf k X.left n)
    (T.intrinsicCanonical_isInvertible D hD)

@[simp] theorem intrinsicCanonicalCartier_sheaf
    (D : CartierData X.left) (hD : D.IsAmple) :
    (T.intrinsicCanonicalCartier D hD).sheaf=topDifferentialSheaf k X.left n := rfl

include T in
/-- The Cartier notation A, B+K has its usual multiplication meaning
for every genuine canonical presentation, independently of its rational
frame or its particular representative as a divisor. -/
theorem adjointSectionMultiplication_of_canonical
    (D E K : CartierData X.left)
    (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1))
    (hK : K.sheaf≅topDifferentialSheaf k X.left n) :
    Function.Surjective (D.sectionMultiplicationOver k (E.add K)) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hampleD
  letI := hequiv
  let e₀ : «Σ».fanScheme k≅X.left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.hom.IsOver (Spec (CommRingCat.of k)) := ⟨e.hom.w⟩
  let F := D.dominantPullback e₀.hom
  let G := E.dominantPullback e₀.hom
  let b₀ : Module.Basis (Fin n) ℤ (Lattice n) := Pi.basisFun ℤ (Fin n)
  let «KΣ» := «Σ».differentialVolumeData k hpure b₀
  have hF : «Σ».CartierWallDegreesAtLeast k F (n+1) :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k F (n+1)
      (invariantCurveDegreesAtLeast_pullbackIso e D (n+1) hD)
  have hG : «Σ».CartierWallDegreesAtLeast k G (n+1) :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k G (n+1)
      (invariantCurveDegreesAtLeast_pullbackIso e E (n+1) hE)
  let H : (K.dominantPullback e₀.hom).sheaf≅«KΣ».sheaf :=
    (K.dominantPullbackSheafIso e₀.hom).symm ≪≫
      (Scheme.Modules.pullback e₀.hom).mapIso hK ≪≫
      topDifferentialSheafPullbackIso e₀.hom n k ≪≫
      «Σ».intrinsicTopDifferentialVolumeIso k hpure b₀
  let J : ((E.add K).dominantPullback e₀.hom).sheaf≅(G.add «KΣ»).sheaf :=
    (E.dominantPullback_add_equivalent K e₀.hom).choose ≪≫
      G.addSheafIso G (K.dominantPullback e₀.hom) «KΣ» (Iso.refl G.sheaf) H
  apply (D.sectionMultiplicationOver_surjective_iff_schemeIso k e₀ (E.add K)).mpr
  apply (F.sectionMultiplicationOver_surjective_iff_sheafIso k F
    ((E.add K).dominantPullback e₀.hom) (G.add «KΣ») (Iso.refl F.sheaf) J).mpr
  exact «Σ».fanDivisor_adjointSectionMultiplication k hpure F G hF hG b₀

include T in
/-- Theorem 1.3, using the actual base-field tensor map of actual global
sections and the genuine intrinsic canonical sheaf. The theorem has no
assumption supplying a fan, a canonical presentation, a section-space
identification, or a classification theorem. -/
theorem toric_theorem_1_3_sections
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    Function.Surjective
      (moduleSectionMultiplicationOver k D.sheaf
        (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) := by
  let K := T.intrinsicCanonicalCartier D hampleD
  have hK : K.sheaf≅topDifferentialSheaf k X.left n := Iso.refl _
  exact D.moduleSectionMultiplicationOver_adjoint_of_cartier k E K
    (topDifferentialSheaf k X.left n) hK
    (T.adjointSectionMultiplication_of_canonical D E K hampleD hampleE hD hE hK)

/-- Both formulations of Theorem 1.3 on the original intrinsic variety. -/
theorem toric_theorem_1_3
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    ({m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)}) ∧
      Function.Surjective
        (moduleSectionMultiplicationOver k D.sheaf
          (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) :=
  ⟨T.toric_theorem_1_3_latticePoints D E hampleD hampleE hD hE,
    T.toric_theorem_1_3_sections D E hampleD hampleE hD hE⟩

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.intrinsicCanonical_isInvertible
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3_sections
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3
