module

public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
import all TauCeti.AlgebraicGeometry.Modules.TensorProduct

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
import all TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

public import Continuation.Divisor.TrivializationCoordinate
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
import all TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import all TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

@[expose] public section

/-! Nonvanishing of actual line-bundle sections commutes with arbitrary
scheme pullback. The locus is the ordinary locus where the section generates
the stalk. No flatness, surjectivity, integrality or positivity is assumed.

The proof first treats a globally trivial line bundle, then compares actual
restriction stalks and their scalar actions. Local triviality and the genuine
pullback-composition comparison give the unrestricted result.

Source and compilation provenance are recorded separately. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped MonoidalCategory

universe u

local instance unitInvertible (X : Scheme.{u}) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (𝟙_ X.Modules) :=
  TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_unit X

private lemma iso_inv_hom_app {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (s : Γ(M, U)) :
    e.inv.app U (e.hom.app U s) = s := by
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    congrArg (fun a : M ⟶ M => a.app U s) e.hom_inv_id

private lemma iso_hom_inv_app {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (s : Γ(N, U)) :
    e.hom.app U (e.inv.app U s) = s :=
  iso_inv_hom_app e.symm U s

/-- The nonvanishing locus for the actual structure sheaf is its usual
basic open. -/
theorem nonvanishingLocus_unit {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U)) :
    (𝟙_ X.Modules).nonvanishingLocus s = X.basicOpen s := by
  let t : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅
      (𝟙_ X.Modules).over U :=
    TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)
  rw [Scheme.Modules.nonvanishingLocus_eq_basicOpen t (𝟙 U)]
  congr 1
  have ht : Scheme.Modules.trivializationCoordinateIso (𝟙_ X.Modules) t =
      Iso.refl (SheafOfModules.unit (X.ringCatSheaf.over U)) := by
    have h := Scheme.Modules.trivializationCoordinateIso_of_unitIso (𝟙_ X.Modules)
        (Iso.refl (SheafOfModules.unit (X.ringCatSheaf.over U)))
    erw [Iso.refl_symm, Iso.trans_refl] at h
    exact h
  rw [Scheme.Modules.trivializationCoordinate_apply, ht]
  rfl

/-- The unit comparison sends the adjunction pullback of a regular function
to its genuine pullback on scheme sections. -/
theorem pullbackUnitIso_pullbackSections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
      (f.pullbackSections (𝟙_ Y.Modules) U r) = f.app U r := by
  have h := pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun a : (𝟙_ Y.Modules) ⟶
      (pushforward f).obj (𝟙_ X.Modules) => a.app U r) h

/-- Nonvanishing commutes with pullback for an actual global trivialization;
the section and the morphism remain arbitrary. -/
theorem nonvanishingLocus_pullbackSections_of_trivial {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (e : (𝟙_ Y.Modules) ≅ M) (U : Y.Opens) (s : Γ(M, U)) :
    ((pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s) =
      f ⁻¹ᵁ (M.nonvanishingLocus s) := by
  let r : Γ(Y, U) := e.inv.app U s
  have hs : e.hom.app U r = s := iso_hom_inv_app e U s
  let E : (𝟙_ X.Modules) ≅ (pullback f).obj M :=
    (pullbackObjUnitIso f).symm ≪≫ (pullback f).mapIso e
  have hu : (pullbackObjUnitIso f).inv.app (f ⁻¹ᵁ U) (f.app U r) =
      f.pullbackSections (𝟙_ Y.Modules) U r := by
    rw [← pullbackUnitIso_pullbackSections f U r]
    exact iso_inv_hom_app (pullbackObjUnitIso f) _ _
  have hE : E.hom.app (f ⁻¹ᵁ U) (f.app U r) =
      f.pullbackSections M U s := by
    change ((pullback f).map e.hom).app (f ⁻¹ᵁ U)
      ((pullbackObjUnitIso f).inv.app (f ⁻¹ᵁ U) (f.app U r)) = _
    rw [hu, f.pullbackSections_naturality (𝟙_ Y.Modules) U e.hom, hs]
  rw [← hE, Scheme.Modules.nonvanishingLocus_hom_app,
    nonvanishingLocus_unit, ← Scheme.preimage_basicOpen]
  congr 1
  rw [← hs, Scheme.Modules.nonvanishingLocus_hom_app, nonvanishingLocus_unit]

private lemma span_singleton_top_iff_of_semilinear_bijections
    {R S A B : Type*} [CommRing R] [CommRing S]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module S B]
    (φ : R → S) (ψ : A → B) (hφ : Function.Surjective φ)
    (hψ : Function.Bijective ψ) (hsmul : ∀ r a, ψ (r • a) = φ r • ψ a) (a : A) :
    Submodule.span R {a} = ⊤ ↔ Submodule.span S {ψ a} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff, Submodule.span_singleton_eq_top_iff]
  constructor
  · intro h b
    obtain ⟨a', rfl⟩ := hψ.surjective b
    obtain ⟨r, hr⟩ := h a'
    exact ⟨φ r, (hsmul r a).symm.trans (congrArg ψ hr)⟩
  · intro h a'
    obtain ⟨s, hs⟩ := h (ψ a')
    obtain ⟨r, rfl⟩ := hφ s
    exact ⟨r, hψ.injective ((hsmul r a).trans hs)⟩

section Restriction

variable {Y : Scheme.{u}} (V : Y.Opens) (M : Y.Modules)

/-- The actual stalk comparison for restriction is semilinear for the
actual isomorphism of the local rings. -/
theorem restrictStalk_smul (x : V) (r : V.toScheme.presheaf.stalk x)
    (m : (M.restrict V.ι).presheaf.stalk x) :
    (restrictStalkNatIso V.ι x).hom.app M (r • m) =
      (V.stalkIso x).hom r •
        (show M.presheaf.stalk x.val from (restrictStalkNatIso V.ι x).hom.app M m) := by
  obtain ⟨U, hxU, r, rfl⟩ := V.toScheme.presheaf.exists_germ_eq r
  obtain ⟨W, hxW, m, rfl⟩ := (M.restrict V.ι).presheaf.exists_germ_eq m
  let i : U ⊓ W ⟶ U := homOfLE inf_le_left
  let j : U ⊓ W ⟶ W := homOfLE inf_le_right
  have hx : x ∈ U ⊓ W := ⟨hxU, hxW⟩
  have hmod (O : V.toScheme.Opens) (hxO : x ∈ O) (a : Γ(M.restrict V.ι, O)) :
      (restrictStalkNatIso V.ι x).hom.app M
          ((M.restrict V.ι).presheaf.germ O x hxO a) =
        M.presheaf.germ (V.ι ''ᵁ O) x.val ⟨x, hxO, rfl⟩ a := by
    exact congrArg (fun b => b a) (germ_restrictStalkNatIso_hom_app V.ι x M hxO)
  have hring (O : V.toScheme.Opens) (hxO : x ∈ O) (a : Γ(V.toScheme, O)) :
      (V.stalkIso x).hom (V.toScheme.presheaf.germ O x hxO a) =
        Y.presheaf.germ (V.ι ''ᵁ O) x.val ⟨x, hxO, rfl⟩ a := by
    exact congrArg (fun b => b a) (V.germ_stalkIso_hom x hxO)
  rw [← TopCat.Presheaf.germ_res_apply V.toScheme.presheaf i x hx,
    ← TopCat.Presheaf.germ_res_apply (M.restrict V.ι).presheaf j x hx]
  rw [← Scheme.Modules.germ_smul, hmod, hring, hmod]
  change M.presheaf.germ (V.ι ''ᵁ (U ⊓ W)) x.val ⟨x, hx, rfl⟩
    ((V.ι.appIso (U ⊓ W)).inv (V.toScheme.presheaf.map i.op r) •
      (show Γ(M, V.ι ''ᵁ (U ⊓ W)) from (M.restrict V.ι).presheaf.map j.op m)) = _
  rw [V.ι_appIso]
  exact Scheme.Modules.germ_smul M x.val (V.ι ''ᵁ (U ⊓ W)) ⟨x, hx, rfl⟩ _ _

/-- The literal restriction of a section, read as a section on the open
subscheme, over the inverse image of its domain. -/
def restrictedSection (U : Y.Opens) (s : Γ(M, U)) :
    Γ(M.restrict V.ι, V.ι ⁻¹ᵁ U) :=
  M.presheaf.map (homOfLE (V.ι.image_preimage_le U)).op s

variable [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]

local instance : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
    V.toScheme (M.restrict V.ι) :=
  (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible V.toScheme).prop_of_iso
    ((restrictFunctorIsoPullback V.ι).app M).symm inferInstance

/-- Restriction identifies the ordinary nonvanishing loci, via the actual
stalk and local-ring isomorphisms. -/
theorem nonvanishingLocus_restrictedSection (U : Y.Opens) (s : Γ(M, U)) :
    (M.restrict V.ι).nonvanishingLocus (restrictedSection V M U s) =
      V.ι ⁻¹ᵁ (M.nonvanishingLocus s) := by
  ext x
  by_cases hx : x ∈ V.ι ⁻¹ᵁ U
  · change x ∈ (M.restrict V.ι).nonvanishingLocus (restrictedSection V M U s) ↔ _
    rw [Scheme.Modules.mem_nonvanishingLocus_iff_of_mem hx]
    change _ ↔ x.val ∈ M.nonvanishingLocus s
    erw [Scheme.Modules.mem_nonvanishingLocus_iff_of_mem (show x.val ∈ U from hx)]
    let e := (restrictStalkNatIso V.ι x).app M
    have hg : e.hom ((M.restrict V.ι).presheaf.germ _ x hx
        (restrictedSection V M U s)) = M.presheaf.germ U x.val hx s := by
      rw [show e.hom = (restrictStalkNatIso V.ι x).hom.app M from rfl]
      have h := congrArg (fun b => b (restrictedSection V M U s))
        (germ_restrictStalkNatIso_hom_app V.ι x M hx)
      exact h.trans (TopCat.Presheaf.germ_res_apply _ _ _ _ _)
    rw [← hg]
    exact span_singleton_top_iff_of_semilinear_bijections
      (V.stalkIso x).hom
      (fun z : (M.restrict V.ι).presheaf.stalk x =>
        (show M.presheaf.stalk x.val from e.hom z))
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
      (restrictStalk_smul V M x) _
  · constructor
    · intro h
      exact (hx (Scheme.Modules.nonvanishingLocus_le _ h)).elim
    · intro h
      exact (hx (Scheme.Modules.nonvanishingLocus_le s h)).elim

/-- The comparison between restriction and pullback preserves the actual
section supplied by their adjunction units. -/
theorem restrictIso_pullbackSections (U : Y.Opens) (s : Γ(M, U)) :
    ((restrictFunctorIsoPullback V.ι).inv.app M).app (V.ι ⁻¹ᵁ U)
      (V.ι.pullbackSections M U s) = restrictedSection V M U s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction V.ι) (pullbackPushforwardAdjunction V.ι) M
  have h' := congrArg (fun a : M ⟶ (pushforward V.ι).obj ((pullback V.ι).obj M) =>
    a.app U s) h
  change ((restrictFunctorIsoPullback V.ι).hom.app M).app (V.ι ⁻¹ᵁ U)
      (restrictedSection V M U s) = V.ι.pullbackSections M U s at h'
  rw [← h']
  exact iso_inv_hom_app ((restrictFunctorIsoPullback V.ι).app M) _ _

/-- Pullback along an open-subscheme inclusion preserves the ordinary
nonvanishing locus. This is derived from actual restriction stalks. -/
theorem nonvanishingLocus_pullbackSections_open (U : Y.Opens) (s : Γ(M, U)) :
    ((pullback V.ι).obj M).nonvanishingLocus (V.ι.pullbackSections M U s) =
      V.ι ⁻¹ᵁ (M.nonvanishingLocus s) := by
  rw [← nonvanishingLocus_restrictedSection V M U s,
    ← restrictIso_pullbackSections V M U s]
  exact (Scheme.Modules.nonvanishingLocus_hom_app
    ((restrictFunctorIsoPullback V.ι).app M).symm _).symm

end Restriction

/-- The actual pullback-composition comparison preserves the nonvanishing
locus of the pulled section. -/
theorem nonvanishingLocus_pullbackSections_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Z M]
    (U : Z.Opens) (s : Γ(M, U)) :
    ((pullback f).obj ((pullback g).obj M)).nonvanishingLocus
        (f.pullbackSections ((pullback g).obj M) (g ⁻¹ᵁ U)
          (g.pullbackSections M U s)) =
      ((pullback (f ≫ g)).obj M).nonvanishingLocus
        ((f ≫ g).pullbackSections M U s) := by
  letI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      ((pullback g ⋙ pullback f).obj M) := by
    change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      ((pullback f).obj ((pullback g).obj M))
    infer_instance
  rw [← g.pullbackSections_comp M U f s]
  exact Scheme.Modules.nonvanishingLocus_hom_app ((pullbackComp f g).app M).symm _

/-- The full nonvanishing-locus pullback theorem, for every morphism of
schemes, every invertible sheaf and every section on every open. -/
theorem nonvanishingLocus_pullbackSections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (U : Y.Opens) (s : Γ(M, U)) :
    ((pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s) =
      f ⁻¹ᵁ (M.nonvanishingLocus s) := by
  ext x
  obtain ⟨V, t, hxV⟩ := Scheme.Modules.exists_mem_trivialization M (f x)
  let x' : f ⁻¹ᵁ V := ⟨x, hxV⟩
  let e : (𝟙_ V.toScheme.Modules) ≅ (pullback V.ι).obj M :=
    TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict t ≪≫
      (restrictFunctorIsoPullback V.ι).app M
  have h : (f ⁻¹ᵁ V).ι ⁻¹ᵁ
        (((pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s)) =
      (f ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ (M.nonvanishingLocus s)) := by
    rw [← nonvanishingLocus_pullbackSections_open (f ⁻¹ᵁ V)
      ((pullback f).obj M) (f ⁻¹ᵁ U) (f.pullbackSections M U s),
      nonvanishingLocus_pullbackSections_comp, ← morphismRestrict_ι,
      ← nonvanishingLocus_pullbackSections_comp,
      nonvanishingLocus_pullbackSections_of_trivial (f ∣_ V)
        ((pullback V.ι).obj M) e,
      nonvanishingLocus_pullbackSections_open]
  have hp := Iff.of_eq (congrArg (fun W : (f ⁻¹ᵁ V).toScheme.Opens => x' ∈ W) h)
  change (x ∈ ((pullback f).obj M).nonvanishingLocus
    (f.pullbackSections M U s)) ↔ (V.ι ((f ∣_ V) x')) ∈ M.nonvanishingLocus s at hp
  change (x ∈ ((pullback f).obj M).nonvanishingLocus
    (f.pullbackSections M U s)) ↔ f x ∈ M.nonvanishingLocus s
  simpa only [Scheme.Opens.ι_apply, morphismRestrict_base_coe] using hp

/-- Pullback followed by restriction to any smaller source open has the
expected intersection as its actual nonvanishing locus. The global-section
case is obtained by taking both opens to be top. -/
theorem nonvanishingLocus_pullbackSectionsLE {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((pullback f).obj M).nonvanishingLocus (f.pullbackSectionsLE M U W hW s) =
      W ⊓ f ⁻¹ᵁ (M.nonvanishingLocus s) := by
  rw [Scheme.Hom.pullbackSectionsLE_apply,
    Scheme.Modules.nonvanishingLocus_map, nonvanishingLocus_pullbackSections]

end Unimodular.NefBig

#print axioms Unimodular.NefBig.nonvanishingLocus_pullbackSections
#print axioms Unimodular.NefBig.nonvanishingLocus_pullbackSectionsLE
