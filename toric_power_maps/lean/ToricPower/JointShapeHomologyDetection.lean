module

public import ToricPower.JointExactDetection
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exact joint detectors in every complex shape

Zero detection by an exact family detects both monomorphisms and
 epimorphisms through the homology of the two elementary short complexes.
It consequently detects the original homology maps in any complex shape.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace ToricPower

universe u v w z t r

variable {B : Type u} [Category.{v} B] [Abelian B]
  {I : Type t} {D : I → Type w} [∀ i, Category.{z} (D i)] [∀ i, Abelian (D i)]
  (F : ∀ i, B ⥤ D i) [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (detect : ∀ M : B, (∀ i, IsZero ((F i).obj M)) → IsZero M)

include detect in
theorem isIso_of_jointly_detect_zero {M N : B} (f : M ⟶ N)
    (localIso : ∀ i, IsIso ((F i).map f)) : IsIso f := by
  let left : ShortComplex B := .mk (0 : 0 ⟶ M) f (by simp)
  let right : ShortComplex B := .mk f (0 : N ⟶ 0) (by simp)
  haveI mono : Mono f := (left.exact_iff_mono rfl).mp (by
    apply exact_of_jointly_detect_zero F detect left
    intro i
    letI := localIso i
    apply ((left.map (F i)).exact_iff_mono (by simp [left])).mpr
    change Mono ((F i).map f)
    infer_instance)
  haveI epi : Epi f := (right.exact_iff_epi rfl).mp (by
    apply exact_of_jointly_detect_zero F detect right
    intro i
    letI := localIso i
    apply ((right.map (F i)).exact_iff_epi (by simp [right])).mpr
    change Epi ((F i).map f)
    infer_instance)
  exact isIso_of_mono_of_epi f

include detect in
theorem quasiIso_of_jointly_detect_zero_shape {J : Type r} {shape : ComplexShape J}
    {K L : HomologicalComplex B shape} (f : K ⟶ L)
    (localIso : ∀ i, QuasiIso (((F i).mapHomologicalComplex shape).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_of_jointly_detect_zero F detect
  intro i
  letI := localIso i
  change IsIso ((ShortComplex.homologyFunctor B ⋙ F i).map
    ((shortComplexFunctor B shape q).map f))
  apply (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso (F i))
    ((shortComplexFunctor B shape q).map f)).mp
  change IsIso (homologyMap (((F i).mapHomologicalComplex shape).map f) q)
  exact (quasiIsoAt_iff_isIso_homologyMap _ q).mp inferInstance

end ToricPower

end

