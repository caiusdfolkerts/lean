module

public import ToricPower.JointExactDetection
public import ToricPower.MappingConeAcyclicCriterion

/-! # Exact joint detectors detect unbounded quasi-isomorphisms -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower

universe u v w z t

variable {B : Type u} [Category.{v} B] [Abelian B]
  {I : Type t} {D : I → Type w} [∀ i, Category.{z} (D i)] [∀ i, Abelian (D i)]
  (F : ∀ i, B ⥤ D i) [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (detect : ∀ M : B, (∀ i, IsZero ((F i).obj M)) → IsZero M)

include detect in
theorem acyclic_of_jointly_detect_zero (K : CochainComplex B ℤ)
    (vanishes : ∀ i, (((F i).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro q
  apply exact_of_jointly_detect_zero F detect (K.sc q)
  intro i
  exact vanishes i q

include detect in
theorem quasiIso_of_jointly_detect_zero {K L : CochainComplex B ℤ} (f : K ⟶ L)
    (localIso : ∀ i, QuasiIso (((F i).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  apply (quasiIso_iff_mappingCone_acyclic f).mpr
  apply acyclic_of_jointly_detect_zero F detect
  intro i q
  let e := mappingCone.mapHomologicalComplexIso f (F i)
  exact (exactAt_iff_of_quasiIsoAt e.hom q).mpr
    ((quasiIso_iff_mappingCone_acyclic
      (((F i).mapHomologicalComplex (.up ℤ)).map f)).mp (localIso i) q)

end ToricPower

end
