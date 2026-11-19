module

public import Continuation.Divisor.ReflexiveScheme
public import Continuation.Divisor.ProjectiveOverField
public import Continuation.Divisor.IntrinsicAmple
public import Continuation.Divisor.AnticanonicalDivisibility

/-!
# Ordinary smooth projective Fano schemes from the reflexive presentations

All conclusions concern the original fan scheme. The projective map is
an actual finite polynomial-Proj closed immersion over the field; the
anticanonical line bundle is the dual of the top Kähler exterior sheaf.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace Unimodular.SmoothReflexivePresentation
open AlgebraicGeometry CategoryTheory
open Unimodular.Projectivity Unimodular.NefBig
open PaperVerification.ToricSchemes
variable {n : ℕ} (P : SmoothReflexivePresentation n) (k : Type u) [Field k]

/-- Full actual geometric output, with projectivity, smoothness, dimension,
and intrinsic anticanonical ampleness all stated explicitly. -/
theorem smooth_projective_fano :
    Smooth (P.schemeFan.fanSchemeStructureMap k) ∧
    IsProper (P.schemeFan.fanSchemeStructureMap k) ∧
    IsClosedImmersion (P.projectiveEmbedding k) ∧
    P.projectiveEmbedding k ≫ polynomialProjectiveToSpec k
      (WeightIndex.{u} (F := P.schemeFan)) = P.schemeFan.fanSchemeStructureMap k ∧
    topologicalKrullDim (P.schemeFan.fanScheme k) = n ∧
    IsAmpleModule (anticanonicalLineBundle P.schemeFan k).obj := by
  exact ⟨fanScheme_smooth P.schemeFan k,
    P.projectiveVertexData.fanScheme_isProper k, inferInstance,
    P.projectiveVertexData.fanProjectiveEmbedding_toSpec k,
    P.schemeFan.fanScheme_topologicalKrullDim k P.schemeFan.isPure,
    anticanonical_isAmple_of_strictSupport P.schemeFan k P.schemeFan_strict_unit_support⟩

/-- A prescribed index is realized by a literal ordinary tensor-root of
the intrinsic anticanonical bundle, retaining the original integral
character and the original facet-normal coefficient relation. -/
def anticanonicalDivisibilityIso (d : ℕ) (D : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ u ∈ P.normals, (1 : ℤ) = (d : ℤ) * D u + integerPairing m u) :
    (anticanonicalLineBundle P.schemeFan k).obj ≅
      tensorSheafPower (P.schemeFan.fanCartierData k P.schemeFan.isPure D).sheaf d :=
  anticanonicalTensorPowerIso P.schemeFan k d D m
    (fun u hu => h u ((P.schemeFan_ray_iff u).mp hu))

#print axioms smooth_projective_fano
#print axioms anticanonicalDivisibilityIso
end Unimodular.SmoothReflexivePresentation
