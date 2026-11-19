module

public import Continuation.Runtime.IntrinsicFanPresentation
public import Continuation.Runtime.IntrinsicActualSections
public import Continuation.Runtime.IntrinsicBoundaryCartier
public import Continuation.Runtime.IntegralBoundaryGraph

/-!
# Deep anticanonical geometry on the independently specified scheme

Reconstruction uses the ordinary ample sheaf already present in the ample
clause. The original boundary points and their integer character valuations
are transported by the resulting actual scheme isomorphism. The unit
boundary divisor is proved to be the intrinsic Kähler anticanonical sheaf;
its literal unreflected inequalities and all original signed ray labels are
retained. No fan presentation or graphic representation is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open scoped Classical

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open Unimodular.NefBig Unimodular.CycleBounds
open Unimodular.GraphicRootedLattice Unimodular.IntegralBoundaryGraph
variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)
local instance originalLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The same unit boundary coefficients define an actual anticanonical
Cartier sheaf on the original scheme. Its lattice characters satisfy
exactly the displayed divisor inequalities. -/
theorem unitBoundary_is_intrinsicAnticanonical
    (M : X.left.Modules) (hM : IsInvertibleModule M) (hample : IsAmpleModule M) :
    ∃ D : CartierData X.left,
      T.HasBoundaryCoefficients D (fun _ => 1) ∧
      Nonempty (D.sheaf ≅ (topDifferentialSheaf k X.left n).dual) ∧
      ∀ m : Lattice n,
        T.intrinsicCharacter m ∈ D.sectionValueRange ⊤ ↔
          embed n m ∈ T.unitBoundaryDivisorPolytope := by
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple M hM hample
  let D := boundaryCartierOfPresentation F e (fun _ => 1)
  have hD := T.boundaryCartierOfPresentation_hasCoefficients F e ht (fun _ => 1)
  refine ⟨D, hD, ⟨T.unitBoundaryCartierAnticanonicalIso F e ht D hD⟩, ?_⟩
  intro m
  rw [T.boundaryCartier_character_section_iff F e ht D (fun _ => 1) hD m]
  change (∀ q : T.BoundaryPrime, -(1 : ℤ) ≤ integerPairing (T.boundaryValuation q) m) ↔
    ∀ q : T.BoundaryPrime, -(1 : ℝ) ≤ T.boundaryForm q (embed n m)
  apply forall_congr'
  intro q
  rw [boundaryForm, SmoothCompleteFan.normalRay_pairing_lattice]
  exact_mod_cast (Iff.rfl : (-(1 : ℤ) ≤ integerPairing (T.boundaryValuation q) m) ↔ _)

/-- Deep monotonicity produces a genuine integral graph presentation of
all the original signed boundary valuations. Every coordinate and graph
is constructed from the actual scheme hypotheses. -/
theorem exists_graphicBoundary_of_deeplyMonotone
    (M : X.left.Modules) (hM : IsInvertibleModule M) (hample : IsAmpleModule M)
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = T.unitBoundaryDivisorPolytope) :
    ∃ H : SimpleGraph (Option (Fin n)), Nonempty (T.IntegralGraphicBoundaryPresentation H) := by
  obtain ⟨F, e, ht⟩ := T.exists_fan_of_ordinaryAmple M hM hample
  have hQF : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ)) :=
    hanti.trans (T.unitBoundaryDivisorPolytope_presentation F e ht)
  have hcarrier : Q.reflected.carrier =
      {x : Unimodular.Ambient n | ∀ v ∈ F.rays, Unimodular.pairing x v ≤ 1} :=
    (Q.reflected_carrier.trans
      (congrArg (fun S : Set (Ambient n) => Neg.neg '' S) hQF)).trans
        F.reflected_anticanonical_polytope
  obtain ⟨G, _, _, δ, hinj, hδ⟩ := anticanonical_integral_incidence_no_K4 F
    Q.reflected (Q.deeplyMonotone_reflected_iff.mpr hQ) hcarrier
  have hr := T.completeBoundaryRaySet_presentation F e ht
  let j : T.completeBoundaryRaySet → F.rays := fun v =>
    ⟨v.val, by change v.val ∈ (F.rays : Set _); rw [← hr]; exact v.property⟩
  let s := G.source ∘ j
  let t := G.target ∘ j
  have hcolumns (v : T.completeBoundaryRaySet) :
      δ v.val = edge (s v) (t v) := by
    unfold edge
    convert hδ (j v) using 1 <;> congr 2 <;> apply Subsingleton.elim
  have hne (v : T.completeBoundaryRaySet) : s v ≠ t v := by
    intro he
    apply F.ray_ne_zero (j v).property
    apply hinj
    rw [map_zero, hcolumns, he, edge, sub_self]
  have hspan : Submodule.span ℤ (Set.range (fun v : T.completeBoundaryRaySet => v.val)) = ⊤ := by
    rw [hr]
    exact F.integerSpan_all_rays
  let H := familyGraph s t hne
  refine ⟨H, ⟨{
    equiv := incidenceEquiv (fun v : T.completeBoundaryRaySet => v.val) hspan δ hinj s t hne hcolumns
    source := s
    target := t
    adjacent := familyGraph_adj s t hne
    ray_image := ?_
  }⟩⟩
  intro v
  exact incidenceEquiv_apply (fun v : T.completeBoundaryRaySet => v.val)
    hspan δ hinj s t hne hcolumns v

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_fan_of_ordinaryAmple
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.unitBoundary_is_intrinsicAnticanonical
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_graphicBoundary_of_deeplyMonotone

end
