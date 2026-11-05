module

public import Continuation.CycleBounds.DeeplyMonotone

public import Continuation.CycleBounds.DeeplyMonotoneIncidence
public import Continuation.Divisor.ReflectedPolytope
public import Recovery.Unimodular.GraphicSectionRing.GraphicFanTheorem
public import Recovery.Unimodular.NefBig.CartierGlobalGeneration

@[expose] public section

/-!
# The section-ring clause of Corollary 6.11

The fan is the original smooth complete fan. The final endpoints take its
literal anticanonical polytope; intermediate endpoints use the reflected
inequality convention, and the reflection equivalence is proved internally.
The integral graphic coordinates are derived from deep monotonicity. Every
ordinary invertible sheaf is quantified; an equivariant structure or a Cartier
representative is never an input.

The checked graphic section-ring theorem is stronger than the nef-only clause
of the paper: it applies to every ordinary invertible sheaf. Its algebra is the
actual direct sum of tensor-power sections, with its canonical multiplication.

This file does not assert very ampleness, projective normality of an embedding,
or Property N_p. In particular a normally generated section algebra is not
silently substituted for the unproved degree-one embedding assertion.

-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry
open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

/-- Actual deeply monotone anticanonical geometry supplies the integral
character-coordinate transformation required by the graphic ring theorem. -/
theorem exists_graphicCoordinates_of_deeplyMonotone_anticanonical
    (P : Unimodular.SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hanti : P.carrier = Neg.neg '' F.fanPolytope (fun _ => (1 : ℝ))) :
    Nonempty F.GraphicCoordinates := by
  classical
  have hsub := Unimodular.CycleBounds.rays_subset_deeplyMonotone_normals F P hP
    (hanti.trans F.reflected_anticanonical_polytope)
  obtain ⟨b, s, t, hvec, _⟩ :=
    Unimodular.SeriesParallel.deeplyMonotone_integrally_graphic_no_K4 P hP
  let f : F.rays → {u : Unimodular.Lattice n // u ∈ P.normals} :=
    fun u => ⟨u.val, hsub u.property⟩
  have hcoordinate (p : Option (Fin n)) :
      b.equivFun (Unimodular.SeriesParallel.basisVertex b p) = coordinateNormal p := by
    cases p with
    | none => simp [Unimodular.SeriesParallel.basisVertex, coordinateNormal]
    | some i =>
      ext j
      simp [Unimodular.SeriesParallel.basisVertex, coordinateNormal,
        Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hray (u : F.rays) :
      b.equivFun u.val = coordinateNormal (s (f u)) - coordinateNormal (t (f u)) := by
    rw [show u.val = Unimodular.SeriesParallel.basisVertex b (s (f u)) -
      Unimodular.SeriesParallel.basisVertex b (t (f u)) from hvec (f u),
      map_sub, hcoordinate, hcoordinate]
  refine ⟨{
    equiv := dualCoordinates b.equivFun
    left := fun u => t (f u)
    right := fun u => s (f u)
    pairing := ?_
  }⟩
  intro u m
  change dotProduct u.val m =
    -difference (dualCoordinates b.equivFun m) (t (f u)) (s (f u))
  rw [dualCoordinates_pairing b.equivFun, hray, differenceNormal_pairing]
  unfold difference
  ring

universe u
variable (k : Type u) [Field k]

/-- The full first clause of Corollary 6.11 on the original fan scheme,
proved in the stronger form that quantifies every ordinary invertible sheaf.
The same derived integral coordinates work for all sheaves. The displayed
kernel and its initial ideal are those of the actual section-ring map. -/
theorem corollary_6_11_section_rings
    (P : Unimodular.SmoothReflexivePresentation n) (hP : P.DeeplyMonotone)
    (hanti : P.carrier = Neg.neg '' F.fanPolytope (fun _ => (1 : ℝ))) :
    ∃ G : F.GraphicCoordinates,
      ∀ L : TauCeti.AlgebraicGeometry.InvertibleSheaf (F.fanScheme k),
        let hL := (Unimodular.NefBig.isInvertibleModule_iff_standard L.obj).mpr L.property
        let C := G.constraints
          (F.cartierCoefficients k F.isPure (invertibleFractionalPresentation L.obj hL))
        let e := G.invertibleGraphicSectionRingEquiv k L.obj hL
        Function.Surjective (G.invertiblePolynomialMap k L.obj hL) ∧
        (∃ m : MonomialOrder.{0,0} (Point C),
          initialIdeal m (RingHom.ker (G.invertiblePolynomialMap k L.obj hL).toRingHom) =
            quadraticMonomialIdeal
              (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n) k ∧
          ∀ z ∈ forbiddenExponents
              (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n),
            z.degree = 2 ∧ ∀ i, z i ≤ 1) ∧
        PaperVerification.WeightedBar.HasDiagonalTor
          (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
          (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
          (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) := by
  obtain ⟨G⟩ := F.exists_graphicCoordinates_of_deeplyMonotone_anticanonical P hP hanti
  refine ⟨G, ?_⟩
  intro L
  exact G.theorem_6_10_coordinate_fan k L.obj
    ((Unimodular.NefBig.isInvertibleModule_iff_standard L.obj).mpr L.property)

/-- The literal anticanonical polytope may be supplied with its ordinary
inequality convention. Reflection is proved internally and changes neither
the original fan scheme nor the sheaf quantified in the conclusion. -/
theorem exists_graphicCoordinates_of_actual_deeplyMonotone_anticanonical
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ))) :
    Nonempty F.GraphicCoordinates := by
  apply F.exists_graphicCoordinates_of_deeplyMonotone_anticanonical Q.reflected
    (Q.deeplyMonotone_reflected_iff.mpr hQ)
  rw [Q.reflected_carrier, hanti]

/-- Corollary 6.11's section-ring clause for the literal, unreflected
anticanonical polytope and every ordinary invertible sheaf on the original
fan scheme. The conclusion retains the actual polynomial map and its kernel. -/
theorem corollary_6_11_section_rings_actual
    (Q : Unimodular.SmoothReflexivePresentation n) (hQ : Q.DeeplyMonotone)
    (hanti : Q.carrier = F.fanPolytope (fun _ => (1 : ℝ))) :
    ∃ G : F.GraphicCoordinates,
      ∀ L : TauCeti.AlgebraicGeometry.InvertibleSheaf (F.fanScheme k),
        let hL := (Unimodular.NefBig.isInvertibleModule_iff_standard L.obj).mpr L.property
        let C := G.constraints
          (F.cartierCoefficients k F.isPure (invertibleFractionalPresentation L.obj hL))
        let e := G.invertibleGraphicSectionRingEquiv k L.obj hL
        Function.Surjective (G.invertiblePolynomialMap k L.obj hL) ∧
        (∃ m : MonomialOrder.{0,0} (Point C),
          initialIdeal m (RingHom.ker (G.invertiblePolynomialMap k L.obj hL).toRingHom) =
            quadraticMonomialIdeal
              (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n) k ∧
          ∀ z ∈ forbiddenExponents
              (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n),
            z.degree = 2 ∧ ∀ i, z i ≤ 1) ∧
        PaperVerification.WeightedBar.HasDiagonalTor
          (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
          (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
          (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) := by
  apply F.corollary_6_11_section_rings k Q.reflected
    (Q.deeplyMonotone_reflected_iff.mpr hQ)
  rw [Q.reflected_carrier, hanti]

end PaperVerification.ToricGeometry.SmoothCompleteFan

end

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_graphicCoordinates_of_deeplyMonotone_anticanonical
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.corollary_6_11_section_rings
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.exists_graphicCoordinates_of_actual_deeplyMonotone_anticanonical
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.corollary_6_11_section_rings_actual
#check "UNIMODULAR_COROLLARY_6_11_SECTION_RINGS_EOF"
