module

public import Continuation.Runtime.OrdinaryVeryAmpleDefinition
public import Continuation.Runtime.DeeplyMonotoneSectionRings
public import Continuation.Runtime.SectionHomogeneousGeneration
public import Continuation.Runtime.SectionPullbackDegreeOne

/-!
# Actual degree-one embeddings of ordinary ample sheaves

The projectivity hypothesis is expressed by its literal finite closed
embedding over the scalar field. This is the projectivity already assumed in
Corollary 6.11. Ordinary ampleness and the checked degree-one section ring
presentation then give a closed section morphism whose actual pullback of
the independently constructed polynomial O(1) is the original input sheaf.

Projective normality and the quadratic ideal of the same embedding are
assembled in GraphicNormalEmbedding. The higher N_p clause is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open Unimodular.GraphicSectionRing
open Unimodular.GraphicSectionRing.ActualSections
open Unimodular.ActualVeryAmple

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type) [Field k]

include G in
/-- An ordinary ample invertible sheaf is embedded by its genuine original
degree-one sections. No invariant Cartier presentation is supplied by the user. -/
theorem ordinary_ample_isVeryAmple
    (hprojective : HasFiniteProjectiveEmbedding k (F.fanScheme k))
    (M : (F.fanScheme k).Modules) (hM : IsInvertibleModule M)
    (hample : Unimodular.NefBig.IsAmpleModule M) :
    VeryAmpleOverField k (F.fanScheme k) M := by
  letI : IsProper ((F.fanScheme k) ↘ Spec (CommRingCat.of k)) :=
    isProper_of_projective k (F.fanScheme k) hprojective
  let D := invertibleFractionalPresentation M hM
  let C := D.localCocycle
  let I := ULift (Point (G.constraints (F.cartierCoefficients k F.isPure D)))
  letI : Finite (Point (G.constraints (F.cartierCoefficients k F.isPure D))) :=
    G.points_finite _
  letI : Fintype I := Fintype.ofFinite I
  let Φ := G.liftedCartierPolynomialMap k D
  let s : I → Γ(C.sheaf, ⊤) := polynomialDegreeOneSection k C Φ
  have hC : Unimodular.NefBig.IsAmpleModule C.sheaf :=
    Unimodular.NefBig.isAmpleModule_of_iso D.presentationIso hample
  have hgen : ∀ (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)),
      ∃ p : MvPolynomial I k, p.IsHomogeneous N ∧
        C.sectionProjectiveFieldMap k s p =
          (C.pow N).toCartierData.sectionValue ⊤ t :=
    G.cartier_homogeneous_generation k D
  let cover := C.nonvanishing_cover_of_homogeneous_generation k s hC hgen
  let f := C.degreeOneSectionMorphism k s hC hgen
  have hf : IsClosedImmersion f :=
    C.degreeOneSectionMorphism_isClosedImmersion k s hC hgen
  refine ⟨I, inferInstance, f, hf, ?_, ?_⟩
  · exact C.sectionProjectiveMap_toSpec k s cover
  · exact ⟨C.sectionProjectiveMap_pullback_degreeOneIso k s cover ≪≫
      D.presentationIso.symm⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Unimodular.ActualVeryAmple

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type) [Field k]

/-- The very-ampleness clause with the paper's projectivity hypothesis,
literal unreflected anticanonical polytope, and every ordinary ample L. -/
theorem corollary_6_11_veryAmple_actual
    (hprojective : HasFiniteProjectiveEmbedding k (F.fanScheme k))
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)))
    (L : TauCeti.AlgebraicGeometry.InvertibleSheaf (F.fanScheme k))
    (hample : Unimodular.NefBig.IsAmpleModule L.obj) :
    VeryAmpleOverField k (F.fanScheme k) L.obj := by
  obtain ⟨G⟩ := F.exists_graphicCoordinates_of_actual_deeplyMonotone_anticanonical
    Q hQ hanti
  exact G.ordinary_ample_isVeryAmple k hprojective L.obj
    ((Unimodular.NefBig.isInvertibleModule_iff_standard L.obj).mpr L.property) hample

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms Unimodular.ActualVeryAmple.isProper_of_projective
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.ordinary_ample_isVeryAmple
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.corollary_6_11_veryAmple_actual

end
