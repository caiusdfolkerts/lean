module

public import Continuation.Divisor.NormalizedWalls
public import Continuation.Runtime.OrdinaryNefWalls
public import Continuation.Divisor.ThomsenNef

/-!
# Proposition 6.3 on the actual fan scheme

Ordinary nefness is quantified over all proper integral curves on the
original glued scheme. Its wall degrees force global support by the proved
local-to-global concavity theorem; the exact ceiling criterion then yields
the intrinsic positive-coordinate condition. The reverse direction uses
actual global generation, and the Fano conclusion uses the intrinsic
canonical bundle and an explicitly constructed projective embedding.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Unimodular.Thomsen

open PaperVerification.ToricGeometry CategoryTheory

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

local instance fanCartierOrdinaryInvertible (a : Lattice n → ℤ) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (F.fanScheme k)
      (F.fanCartierData k F.isPure a).sheaf :=
  (Unimodular.NefBig.cartierInvertibleSheaf (F.fanCartierData k F.isPure a)).property

/-- Ordinary nefness and global Cartier support agree for every integral
invariant divisor on the same smooth complete fan scheme. -/
theorem fanCartier_isNef_iff_convexSupport (a : Lattice n → ℤ) :
    AlgebraicGeometry.IsNef (baseField := k) (F.fanCartierData k F.isPure a).sheaf ↔
      F.IsNef (fun u => (a u : ℝ)) := by
  constructor
  · intro hn
    apply F.isNef_of_integerWallSlack_nonneg a
    intro s t j w ht hw
    exact F.integerWallSlack_nonneg_of_geometric_nef k a hn s j t w ht hw
  · intro hs
    have hgg := Unimodular.NefBig.fanCartier_isGloballyGenerated F k a hs
    let L := Unimodular.NefBig.cocycleInvertibleSheaf (F.fanCartierCocycle k F.isPure a)
    exact Unimodular.NefBig.isNef_of_isNefOnCurves k L
      (Unimodular.NefBig.isNefOnCurves_of_isGloballyGenerated k L hgg)

/-- The unrestricted equivalence in Proposition 6.3, with actual ordinary
nefness of the positive Thomsen line bundles. -/
theorem proposition_6_3_positiveThomsen_iff :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k) (positiveThomsenLineBundle F k θ).obj) ↔
    Unimodular.ConeBases.PositiveCriterion (Unimodular.FanInterfaces.dictionaryToricFan F) := by
  constructor
  · intro hn
    apply (positiveThomsen_convexSupport_iff_intrinsic F).mp
    intro θ
    exact (fanCartier_isNef_iff_convexSupport F k (positiveCoefficients θ)).mp (hn θ)
  · intro hc θ
    exact positiveThomsen_isNef F k hc θ

/-- All three criteria in Proposition 6.3, with literal normalized relation
coefficients and ordinary geometric nefness on the original fan scheme. -/
theorem proposition_6_3_criteria :
    ((∀ θ : Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k) (positiveThomsenLineBundle F k θ).obj) ↔
      Unimodular.ConeBases.PositiveCriterion
        (Unimodular.FanInterfaces.dictionaryToricFan F)) ∧
    (Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan F) ↔ F.AllNormalizedWallsNegativeMass) :=
  ⟨proposition_6_3_positiveThomsen_iff F k,
    F.normalizedWallCriterion_iff_positiveCriterion.symm⟩

/-- All positive Thomsen bundles nef implies the full geometric Fano
conclusion on the original fan scheme, including projectivity over the field. -/
theorem positiveThomsen_nef_implies_smooth_projective_fano
    (hn : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k) (positiveThomsenLineBundle F k θ).obj) :
    AlgebraicGeometry.Smooth (F.fanSchemeStructureMap k) ∧
    AlgebraicGeometry.IsProper (F.fanSchemeStructureMap k) ∧
    topologicalKrullDim (F.fanScheme k) = n ∧
    Unimodular.NefBig.IsAmpleModule (Unimodular.NefBig.anticanonicalLineBundle F k).obj ∧
    ∃ ha : F.IsStrictSupport (fun _ => ((1 : ℤ) : ℝ)),
      AlgebraicGeometry.IsClosedImmersion
        (Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k) ∧
      Unimodular.Projectivity.strictSupportProjectiveEmbedding F (fun _ => 1) ha k ≫
        Unimodular.Projectivity.polynomialProjectiveToSpec k
          (Unimodular.Projectivity.WeightIndex.{u} (F := F)) = F.fanSchemeStructureMap k :=
  smooth_projective_fano_of_positiveCriterion F k
    ((proposition_6_3_positiveThomsen_iff F k).mp hn)

/-- The associated fan-scheme Fano and deeply monotone conclusions follow
from nefness of all positive Thomsen bundles, with no projectivity assumed. -/
theorem positiveThomsen_nef_implies_deeplyMonotone
    (hn : ∀ θ : Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k) (positiveThomsenLineBundle F k θ).obj) :
    ∃ P : Unimodular.SmoothReflexivePresentation n,
      P.normals = F.rays ∧ P.DeeplyMonotone ∧
      ∀ x : Unimodular.Ambient n,
        x ∈ P.carrier ↔ -x ∈ F.fanPolytope (fun _ => 1) :=
  anticanonical_polytope_deeplyMonotone F
    ((proposition_6_3_positiveThomsen_iff F k).mp hn)

#print axioms fanCartier_isNef_iff_convexSupport
#print axioms proposition_6_3_positiveThomsen_iff
#print axioms proposition_6_3_criteria
#print axioms positiveThomsen_nef_implies_deeplyMonotone
#print axioms positiveThomsen_nef_implies_smooth_projective_fano

end Unimodular.Thomsen

namespace Unimodular.SmoothReflexivePresentation
open PaperVerification.ToricGeometry
variable {n : ℕ} (P : Unimodular.SmoothReflexivePresentation n)
  (k : Type u) [Field k]

/-- Every original deeply monotone polytope satisfies all three criteria on
its actual normal fan scheme, using the proved equality of geometric fans. -/
theorem deeplyMonotone_positiveThomsen_and_normalizedWalls (hP : P.DeeplyMonotone) :
    Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan P.schemeFan) ∧
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      AlgebraicGeometry.IsNef (baseField := k)
        (Unimodular.Thomsen.positiveThomsenLineBundle P.schemeFan k θ).obj) ∧
    P.schemeFan.AllNormalizedWallsNegativeMass := by
  have hc : Unimodular.ConeBases.PositiveCriterion
      (Unimodular.FanInterfaces.dictionaryToricFan P.schemeFan) := by
    rw [P.schemeFan_all_cones]
    exact P.normalFan_positiveCriterion hP
  exact ⟨hc, (Unimodular.Thomsen.proposition_6_3_positiveThomsen_iff P.schemeFan k).mpr hc,
    P.schemeFan.normalizedWallCriterion_iff_positiveCriterion.mpr hc⟩

#print axioms deeplyMonotone_positiveThomsen_and_normalizedWalls
end Unimodular.SmoothReflexivePresentation
