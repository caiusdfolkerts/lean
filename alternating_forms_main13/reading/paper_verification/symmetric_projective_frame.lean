module

public import PaperVerification.SymmetricFreeProjectiveIso
public import PaperVerification.TwistingSheafMapLaws

/-!
# Twisting sheaves under an actual basis chart

The geometric projective-space isomorphism is the separately checked
`SymmetricFreeProjectiveIso.projectiveIso`. Its pullback identifies the
actual homogeneous-fraction twisting sheaves in every integer degree.
The basis/graded-algebra construction is imported with its unique owner.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricProjectiveFrame

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles

universe u

variable {R M I : Type} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev toPolynomial (b : Basis I R M) := SymmetricFreeProjectiveIso.toPolynomial b
abbrev fromPolynomial (b : Basis I R M) := SymmetricFreeProjectiveIso.fromPolynomial b

/-- An inverse pair of graded maps preserves the irrelevant ideal in the
precise direction required by the projective-spectrum functor. -/
theorem irrelevant_le_map_of_inverse
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro n hn x hx
  have hgf : f (g x) = x := congrArg (fun h : ℬ →+*ᵍ ℬ => h x) hfg
  rw [← hgf]
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn (g.map_mem hx))

/-- The previously constructed actual basis chart, with no second owner
for its graded-coordinate proof. -/
abbrev projectiveIso (b : Basis I R M) := SymmetricFreeProjectiveIso.projectiveIso b

/-- The canonical fraction map identifies every integer twist under the
actual geometric basis chart. -/
def twistingIso (b : Basis I R M) (n : ℤ) :
    (Scheme.Modules.pullback (projectiveIso b).hom).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n) ≅
      Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I R) n := by
  exact TwistingSheafMap.pullbackIso (toPolynomial b) (fromPolynomial b)
    (irrelevant_le_map_of_inverse _ _ (SymmetricFreeProjectiveIso.toPolynomial_fromPolynomial b))
    (irrelevant_le_map_of_inverse _ _ (SymmetricFreeProjectiveIso.fromPolynomial_toPolynomial b))
    (SymmetricFreeProjectiveIso.fromPolynomial_toPolynomial b)
    (SymmetricFreeProjectiveIso.toPolynomial_fromPolynomial b) n

end PaperVerification.SymmetricProjectiveFrame
