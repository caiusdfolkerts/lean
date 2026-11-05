module

public import PaperVerification.AlternatingSectionSheaf
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The genuine second exterior power of a line sheaf is zero

The exterior power is formed sectionwise and then sheafified.  The proof
uses actual local frames and the separatedness of the target sheaf; it
does not assume that global sections of a line bundle form a free module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

namespace PaperVerification.LineExteriorSquareZero

universe u v

theorem alternating_pair_eq_zero_of_frame
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : R ≃ₗ[R] M)
    (f : AlternatingMap R M N (Fin 2)) (v : Fin 2 → M) : f v = 0 := by
  have hv : v = fun i ↦ e.symm (v i) • e 1 := by
    funext i
    rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  have hz : f (fun _ : Fin 2 ↦ e 1) = 0 :=
    f.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  rw [hv]
  change f.toMultilinearMap (fun i ↦ e.symm (v i) • e 1) = 0
  rw [MultilinearMap.map_smul_univ]
  change (∏ i : Fin 2, e.symm (v i)) • f (fun _ ↦ e 1) = 0
  rw [hz, smul_zero]

/-- The actual exterior sheaf, with no alternative point model. -/
abbrev exteriorSquare {X : Scheme.{u}} (L : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 _)).obj
    ((PresheafOfModulesOfCommRing.exteriorPower 2).obj L.val)

variable {X : Scheme.{u}} (L : X.Modules)

local instance (V : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj V) :=
  inferInstanceAs (CommRing Γ(X, V.unop))

/-- Actual frames on a covering family force the sheafified exterior square
to be a zero object.  No condition is imposed on global section modules. -/
theorem isZero_of_local_frames {ι : Type v} (U : ι → X.Opens)
    (hcover : ⨆ i, U i = ⊤)
    (frame : ∀ i (V : X.Opens), V ≤ U i →
      Γ(X, V) ≃ₗ[Γ(X, V)] L.val.obj (op V)) :
    IsZero (exteriorSquare L) := by
  let P := (PresheafOfModulesOfCommRing.exteriorPower 2).obj L.val
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  let η := adj.unit.app P
  have hη : η = 0 := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change η.app V (ModuleCat.exteriorPower.mk v) = 0
    apply (Scheme.Modules.isSheaf (exteriorSquare L)).section_ext
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    let W := V.unop ⊓ U i
    let j : W ⟶ V.unop := homOfLE inf_le_left
    refine ⟨W, inf_le_left, ⟨hx, hi⟩, ?_⟩
    have hw : ModuleCat.exteriorPower.mk (M := L.val.obj (op W))
        (fun a : Fin 2 ↦ L.val.map j.op (v a)) = 0 :=
      alternating_pair_eq_zero_of_frame (frame i W inf_le_right)
        ModuleCat.exteriorPower.mk _
    have hnat := PresheafOfModulesOfCommRing.naturality_apply η j.op
      (ModuleCat.exteriorPower.mk v)
    change (exteriorSquare L).val.map j.op (η.app V (ModuleCat.exteriorPower.mk v)) =
      (exteriorSquare L).val.map j.op 0
    have hm : P.map j.op (ModuleCat.exteriorPower.mk v) = 0 :=
      (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk 2 L.val j.op v).trans hw
    let ηW : P.obj (op W) →ₗ[Γ(X, W)] (exteriorSquare L).val.obj (op W) :=
      (η.app (op W)).hom
    exact hnat.symm.trans ((congrArg ηW hm).trans
      ((map_zero ηW).trans
        (map_zero (((exteriorSquare L).val.map j.op).hom)).symm))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (adj.homEquiv P (exteriorSquare L)).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit]
  change η = η ≫ _
  rw [hη, zero_comp]

section Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every genuine Proj twist is a line sheaf on a degree-one cover, and
its actual second exterior-power sheaf is zero. -/
theorem twistingSheaf_exteriorSquare_isZero {ι : Type v} (a : ι → A)
    (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) (r : ℤ) :
    IsZero (exteriorSquare (Proj.twistingSheaf 𝒜 r)) :=
  isZero_of_local_frames (Proj.twistingSheaf 𝒜 r)
    (fun i ↦ Proj.basicOpen 𝒜 (a i)) hcover
    (fun i V hV ↦ Proj.twistingSheaf.chartSectionsLinearEquiv r (a i) (ha i) V hV)

end Proj

end PaperVerification.LineExteriorSquareZero
