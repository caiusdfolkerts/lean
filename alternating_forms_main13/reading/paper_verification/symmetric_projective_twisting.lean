module

public import PaperVerification.TwistingSheafPullback
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme

/-!
# Actual twisting sheaves under generated symmetric-algebra maps

This adapter connects OAI's actual `Proj(Sym M)` morphisms to the
homogeneous-fraction twisting sheaves. It applies to all generated graded
maps, including quotients and coefficient localizations. A full change of
frame is a special case and fixes no distinguished coordinate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SymmetricProjectiveTwisting

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.AlgebraicGeometry.Divisors.LineBundles

universe u

variable {R S M N : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The genuine linear coordinate is homogeneous of degree one. -/
theorem ι_mem (m : M) : SymmetricAlgebra.ι R M m ∈
    Symmetric.Grading.BundleCycles.symmetricGrading R M 1 := by
  change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

/-- The actual degree-one opens cover the symmetric projective scheme,
with precisely the grading instance used by the cycle-theory sources. -/
theorem ι_cover :
    ⨆ m : M, Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M)
      (SymmetricAlgebra.ι R M m) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun m => ⟨1, ι_mem m⟩) (top_unique ?_)
  rintro a -
  have ha : a ∈ Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) := by
    rw [TauCeti.SymmetricAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- Every generated graded symmetric-algebra map preserves every actual
integer twist under ordinary sheaf pullback. -/
def generatedMapPullbackIso
    (g : Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ
      Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (hg : HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading S N) ≤
      (HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map g)
    (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (Proj.map g hg)).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n) ≅
      Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading S N) n :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover g hg
    (SymmetricAlgebra.ι R M) ι_mem ι_cover n

variable {P : Type u} [AddCommGroup P] [Module R P]

/-- Every integer twist is preserved by an arbitrary full linear change
of projective coordinates. -/
def twistingPullbackIso (e : M ≃ₗ[R] P) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).hom).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R P) n) ≅
      Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n :=
  generatedMapPullbackIso
    (Symmetric.GradedMap.BundleCycles.symmetricGradedMap e.symm.toLinearMap)
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant _ e.symm.surjective) n

end PaperVerification.SymmetricProjectiveTwisting
