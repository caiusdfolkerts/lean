module

public import PaperVerification.ToricRationalSheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section

/-!
# Local regularity of actual rational functions

A rational function on an integral scheme is a regular section on an open
set exactly when it belongs to each local ring there. The reverse direction
is proved by taking local representatives and applying the actual structure
sheaf gluing axiom.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual local ring, embedded in the actual function field. -/
def regularAtSubring (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem regular_germ_mem_regularAt (U : X.Opens) [Nonempty U]
    (s : Γ(X,U)) (x : X) (hx : x∈U) :
    X.germToFunctionField U s ∈ regularAtSubring X x :=
  ⟨X.presheaf.germ U x hx s,X.algebraMap_germ_eq_germToFunctionField hx s⟩

set_option backward.isDefEq.respectTransparency false in
/-- The direction from stalkwise regularity to an actual regular section. -/
theorem exists_regularSection_of_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) (hr : ∀ x∈U, r∈regularAtSubring X x) :
    ∃ s : Γ(X,U), X.germToFunctionField U s = r := by
  classical
  have hUne : Nonempty U := inferInstance
  have hloc : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ s : Γ(X,V), ∀ hV : Nonempty V,
        @Scheme.germToFunctionField X inferInstance V hV s = r := by
    intro x
    obtain ⟨t,ht⟩ := hr x x.property
    obtain ⟨W,hxW,s,hs⟩ := X.presheaf.exists_germ_eq t
    let V : X.Opens := W⊓U
    have hxV : x.val∈V := ⟨hxW,x.property⟩
    let sV : Γ(X,V) := X.presheaf.map (homOfLE inf_le_left).op s
    refine ⟨V,inf_le_right,hxV,sV,?_⟩
    intro hV
    letI := hV
    rw [← X.algebraMap_germ_eq_germToFunctionField hxV sV]
    change algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ V x.val hxV
        (X.presheaf.map (homOfLE inf_le_left).op s)) = r
    rw [X.presheaf.germ_res_apply,hs,ht]
  choose V hVU hxV s hs using hloc
  letI (x : U) : Nonempty (V x) := ⟨⟨x.val,hxV x⟩⟩
  have hcover : U≤⨆ x : U, V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hcompatible : X.presheaf.IsCompatible V s := by
    intro x y
    letI : Nonempty (V x⊓V y : X.Opens) :=
      ⟨⟨genericPoint X,genericPoint_mem_open X (V x),
        genericPoint_mem_open X (V y)⟩⟩
    apply X.germToFunctionField_injective (V x⊓V y)
    rw [germToFunctionField_restrict,germToFunctionField_restrict]
    exact (hs x inferInstance).trans (hs y inferInstance).symm
  obtain ⟨g,hg,-⟩ := X.sheaf.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hcompatible
  refine ⟨g,?_⟩
  let x : U := Classical.choice hUne
  calc
    X.germToFunctionField U g =
      X.germToFunctionField (V x) (X.presheaf.map (homOfLE (hVU x)).op g) :=
        (germToFunctionField_restrict X _ g).symm
    _ = X.germToFunctionField (V x) (s x) := congrArg _ (hg x)
    _ = r := hs x inferInstance

/-- Exact local-to-global regularity, with no normality or affine assumption. -/
theorem mem_regular_range_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, r∈regularAtSubring X x := by
  constructor
  · rintro ⟨s,rfl⟩ x hx
    exact regular_germ_mem_regularAt X U s x hx
  · exact exists_regularSection_of_stalkwise X U r

theorem regular_unit_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) (hr : r≠0) :
    (∃ s : Γ(X,U)ˣ, X.germToFunctionField U (s : Γ(X,U))=r) ↔
      (∀ x∈U, r∈regularAtSubring X x) ∧
      (∀ x∈U, r⁻¹∈regularAtSubring X x) := by
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨?_,?_⟩
    · rw [← hs]
      exact regular_germ_mem_regularAt X U s
    · have hinv : X.germToFunctionField U ((s⁻¹ : Γ(X,U)ˣ) : Γ(X,U))=r⁻¹ := by
        have hmul := congrArg (X.germToFunctionField U) s.val_inv
        rw [map_mul,map_one,hs] at hmul
        apply mul_left_cancel₀ hr
        rw [mul_inv_cancel₀ hr]
        exact hmul
      rw [← hinv]
      exact regular_germ_mem_regularAt X U (s⁻¹ : Γ(X,U)ˣ)
  · rintro ⟨h,hInv⟩
    obtain ⟨s,hs⟩ := exists_regularSection_of_stalkwise X U r h
    obtain ⟨t,ht⟩ := exists_regularSection_of_stalkwise X U r⁻¹ hInv
    have hst : s*t=1 := by
      apply X.germToFunctionField_injective U
      rw [map_mul,map_one,hs,ht,mul_inv_cancel₀ hr]
    exact ⟨⟨s,t,hst,by simpa only [mul_comm] using hst⟩,hs⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.mem_regular_range_iff_stalkwise
#print axioms PaperVerification.ToricSchemes.regular_unit_iff_stalkwise
