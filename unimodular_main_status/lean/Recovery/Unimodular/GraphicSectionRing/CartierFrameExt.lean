module

public import Recovery.Unimodular.GraphicSectionRing.SectionRingTensorProducts

/-!
# Equality of actual sheaf morphisms from their local frame values

A local frame generates every section over a smaller trivializing open.
Equality there extends to the whole open by injectivity of actual fractional
section values. No assertion that global pure tensors span all global sheaf
sections is used.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.CanonicalPowers

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes

variable {X : Scheme.{u}}

/-- The ordinary linear equivalence on sections induced by a sheaf isomorphism. -/
def sectionsIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) :=
  ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

@[simp] theorem sectionsIso_apply {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) : sectionsIso e U s = e.hom.app U s := rfl

@[simp] theorem sectionsIso_symm_apply {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(N, U)) : (sectionsIso e U).symm s = e.inv.app U s := rfl

variable [IsIntegral X]

/-- For a source isomorphic to an actual fractional line bundle, agreement on
one genuine local generator on each trivializing open implies equality of
morphisms to any actual fractional line bundle. -/
theorem hom_ext_of_frame (C : RationalCartierCocycle X) (D : CartierData X)
    {A : X.Modules} (e : A ≅ C.sheaf)
    (s : ∀ (i : C.index) (V : X.Opens), V ≤ C.openSet i → Γ(A, V))
    (hs : ∀ (i : C.index) (V : X.Opens) (hVi : V ≤ C.openSet i)
      (hV : Nonempty V),
      @CartierData.sectionValue X inferInstance C.toCartierData V hV
        (e.hom.app V (s i V hVi)) = (C.generator i : X.functionField))
    {f g : A ⟶ D.sheaf}
    (hfg : ∀ (i : C.index) (V : X.Opens) (hVi : V ≤ C.openSet i),
      f.app V (s i V hVi) = g.app V (s i V hVi)) : f = g := by
  classical
  apply Scheme.Modules.hom_ext
  intro U
  ext z
  by_cases hU : Nonempty U
  · letI := hU
    let x : U := Classical.choice hU
    obtain ⟨i, hi⟩ := C.covers x.val
    let V : X.Opens := U ⊓ C.openSet i
    letI : Nonempty V := ⟨⟨x.val, x.property, hi⟩⟩
    let j : V ⟶ U := homOfLE inf_le_left
    let zV : Γ(A, V) := A.presheaf.map j.op z
    let sV : Γ(A, V) := s i V inf_le_right
    let q := sectionsIso e V
    let c := C.localCoordinates i V inf_le_right
    have hc : c (q sV) = 1 := by
      apply X.germToFunctionField_injective V
      rw [C.localCoordinates_value, map_one]
      change C.toCartierData.sectionValue V (e.hom.app V sV) /
        (C.generator i : X.functionField) = 1
      rw [hs i V inf_le_right inferInstance, div_self (Units.ne_zero _)]
    have hz : zV = c (q zV) • sV := by
      apply q.injective
      apply c.injective
      rw [q.map_smul, c.map_smul, hc, smul_eq_mul, mul_one]
    have hV : f.app V zV = g.app V zV := by
      rw [hz, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
      exact congrArg (fun t => c (q zV) • t) (hfg i V inf_le_right)
    have hr : D.sheaf.presheaf.map j.op (f.app U z) =
        D.sheaf.presheaf.map j.op (g.app U z) := by
      calc
        D.sheaf.presheaf.map j.op (f.app U z) = f.app V zV :=
          (f.mapPresheaf.naturality_apply j.op z).symm
        _ = g.app V zV := hV
        _ = D.sheaf.presheaf.map j.op (g.app U z) :=
          g.mapPresheaf.naturality_apply j.op z
    apply D.sectionValue_injective U
    simpa only [D.sectionValue_restrict] using congrArg (D.sectionValue V) hr
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x, hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    letI := Module.subsingleton Γ(X, U) Γ(D.sheaf, U)
    exact Subsingleton.elim _ _

#print axioms hom_ext_of_frame

end Unimodular.GraphicSectionRing.CanonicalPowers

#check Unimodular.GraphicSectionRing.CanonicalPowers.hom_ext_of_frame
