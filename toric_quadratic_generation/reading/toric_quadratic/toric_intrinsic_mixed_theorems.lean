module

public import PaperVerification.ToricIntrinsicFanClassification
public import PaperVerification.ToricInvariantCurveBounds
public import PaperVerification.ToricIntrinsicSectionPolytopes
public import PaperVerification.ToricFanDivisorTheorems
public import PaperVerification.ToricPolytopeTranslation

@[expose] public section

/-!
# Intrinsic mixed lattice-point statements

The input is an ordinary smooth proper integral scheme with an actual
dense equivariant split torus and actual ample integral Cartier divisors.
Its polytopes are defined from its actual normalized global sections.
The fan, all wall curves, their degrees, the support polytopes, and both
integral translation vectors are derived. The two translations are
retained through the target sum and the prescribed quotient class.

The independent invariant-curve classification and degree-existence
dictionary completes the comparison of the geometric degree predicate
with the manuscript's usual degree condition. The separate intrinsic
canonical-sheaf comparison is needed for the section formulation.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical Pointwise

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance («Σ» : SmoothCompleteFan n) : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

/-- The reconstructed isomorphism preserves the actual actions because
it preserves the actual dense torus, not by an extra classification input. -/
theorem exists_equivariant_completeFan
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».IsPure ∧
      ∃ e : «Σ».fanSchemeOver k ≅ X,
        («Σ».intrinsicToricEmbedding k).torus≫e.hom=T.torus ∧
        IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom := by
  obtain ⟨P,«Σ»,e,hP,hfan,hpure,hbase,htorus⟩ := T.exists_smooth_complete_fan D hD
  let E : «Σ».fanSchemeOver k ≅ X := Over.isoMk e hbase
  letI : Smooth («Σ».fanSchemeStructureMap k) := by
    rw [← hbase]
    infer_instance
  letI : Smooth («Σ».fanSchemeOver k).hom :=
    inferInstanceAs (Smooth («Σ».fanSchemeStructureMap k))
  have hE : («Σ».intrinsicToricEmbedding k).torus≫E.hom=T.torus := by
    apply Over.OverMorphism.ext
    exact htorus
  exact ⟨«Σ»,hpure,E,hE,
    («Σ».intrinsicToricEmbedding k).iso_isModHom_of_torus_compatibility T E hE⟩

/-- A simultaneous fan model of the two actual divisors, including the
independent integral translations of their intrinsically defined polytopes. -/
theorem exists_mixed_divisor_fan_model
    (D E : CartierData X.left) (hampleD : D.IsAmple)
    (bound : ℕ) (hbound : 0<bound ∨ n=0)
    (hD : InvariantCurveDegreesAtLeast k n X D bound)
    (hE : InvariantCurveDegreesAtLeast k n X E bound) :
    ∃ «Σ» : SmoothCompleteFan n, ∃ hpure : «Σ».IsPure,
      ∃ e : «Σ».fanSchemeOver k ≅ X,
        let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
        let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
        «Σ».CartierWallDegreesAtLeast k F bound ∧
        «Σ».CartierWallDegreesAtLeast k G bound ∧
        ∃ v w : Lattice n,
          intrinsicSectionPolytope k n X.left T.torus.left D=
            translateSet (embed n v) («Σ».divisorPolytope k hpure F) ∧
          intrinsicSectionPolytope k n X.left T.torus.left E=
            translateSet (embed n w) («Σ».divisorPolytope k hpure G) := by
  obtain ⟨«Σ»,hpure,e,htorus,hequiv⟩ := T.exists_equivariant_completeFan D hampleD
  letI := hequiv
  let F₀ := torusNormalizedCartier k n X.left T.torus.left D
  let G₀ := torusNormalizedCartier k n X.left T.torus.left E
  let F := F₀.dominantPullback e.hom.left
  let G := G₀.dominantPullback e.hom.left
  have hF₀ : InvariantCurveDegreesAtLeast k n X F₀ bound :=
    (invariantCurveDegreesAtLeast_sheafIso k n X F₀ D
      (torusNormalizedCartier_linearlyEquivalent k n X.left T.torus.left D).some bound).mpr hD
  have hG₀ : InvariantCurveDegreesAtLeast k n X G₀ bound :=
    (invariantCurveDegreesAtLeast_sheafIso k n X G₀ E
      (torusNormalizedCartier_linearlyEquivalent k n X.left T.torus.left E).some bound).mpr hE
  have hF : «Σ».CartierWallDegreesAtLeast k F bound :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k F bound
      (invariantCurveDegreesAtLeast_pullbackIso e F₀ bound hF₀)
  have hG : «Σ».CartierWallDegreesAtLeast k G bound :=
    «Σ».cartierWallDegreesAtLeast_of_invariantCurveDegrees k G bound
      (invariantCurveDegreesAtLeast_pullbackIso e G₀ bound hG₀)
  have hnef (J : CartierData («Σ».fanScheme k))
      (hJ : «Σ».CartierWallDegreesAtLeast k J bound) :
      «Σ».IsNef (fun z => («Σ».cartierCoefficients k hpure J z : ℝ)) := by
    apply SmoothCompleteFan.IsStrictSupport.isNef
    rcases hbound with hb|hn
    · exact «Σ».cartierCoefficients_strictSupport_of_curveDegrees k hpure J bound hb hJ
    · exact SmoothCompleteFan.isStrictSupport_of_dimension_zero «Σ» hn _
  let e₀ : «Σ».fanScheme k ≅ X.left := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  letI : e₀.hom.IsOver (Spec (CommRingCat.of k)) := ⟨e.hom.w⟩
  have htorus₀ : «Σ».splitTorusOpenMap k≫e₀.hom=T.torus.left :=
    congrArg (fun f => f.left) htorus
  obtain ⟨v,hv,hPv⟩ := «Σ».intrinsic_sections_fan_translate k hpure X.left
    T.torus.left e₀ htorus₀ D (hnef F hF)
  obtain ⟨w,hw,hQw⟩ := «Σ».intrinsic_sections_fan_translate k hpure X.left
    T.torus.left e₀ htorus₀ E (hnef G hG)
  exact ⟨«Σ»,hpure,e,hF,hG,v,w,hPv,hQw⟩

/-- The prescribed-parity conclusion for intrinsically defined divisor
polytopes on an arbitrary smooth proper split-toric scheme. -/
theorem toric_theorem_1_2
    (D E : CartierData X.left) (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D n)
    (hE : InvariantCurveDegreesAtLeast k n X E n)
    (m : Lattice n)
    (hm : embed n m∈interior
      (intrinsicSectionPolytope k n X.left T.torus.left D+
        intrinsicSectionPolytope k n X.left T.torus.left E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈intrinsicSectionPolytope k n X.left T.torus.left D ∧
      embed n b∈intrinsicSectionPolytope k n X.left T.torus.left E ∧
      a+b=m ∧ parityClass n a=α := by
  have hn : 0<n ∨ n=0 := by omega
  obtain ⟨«Σ»,hpure,e,hF,hG,v,w,hP,hQ⟩ :=
    T.exists_mixed_divisor_fan_model D E hampleD n hn hD hE
  let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
  let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
  rw [hP,hQ] at hm ⊢
  exact prescribedParity_translate («Σ».divisorPolytope k hpure F)
    («Σ».divisorPolytope k hpure G)
    (fun z hz β => «Σ».fanDivisor_prescribedParity k hpure F G hF hG z hz β)
    v w m hm α

/-- The full adjoint lattice-point equality for intrinsically defined
divisor polytopes, with all dimensions and both inclusions retained. -/
theorem toric_theorem_1_3_latticePoints
    (D E : CartierData X.left) (hampleD : D.IsAmple) (_hampleE : E.IsAmple)
    (hD : InvariantCurveDegreesAtLeast k n X D (n+1))
    (hE : InvariantCurveDegreesAtLeast k n X E (n+1)) :
    {m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)} := by
  obtain ⟨«Σ»,hpure,e,hF,hG,v,w,hP,hQ⟩ :=
    T.exists_mixed_divisor_fan_model D E hampleD (n+1) (Or.inl (by omega)) hD hE
  let F := (torusNormalizedCartier k n X.left T.torus.left D).dominantPullback e.hom.left
  let G := (torusNormalizedCartier k n X.left T.torus.left E).dominantPullback e.hom.left
  rw [hP,hQ]
  exact adjointLatticePoints_translate («Σ».divisorPolytope k hpure F)
    («Σ».divisorPolytope k hpure G)
    («Σ».fanDivisor_adjointLatticePoints k hpure F G hF hG) v w

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_2
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_theorem_1_3_latticePoints
