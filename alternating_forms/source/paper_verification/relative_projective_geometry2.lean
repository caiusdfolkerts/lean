module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Nat.Find
public import Mathlib.RingTheory.GradedAlgebra.Basic
import all Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
import all Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Localization.Basic
import all Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import all Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import all Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import all Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Localization.Module
import all Mathlib.RingTheory.Localization.Module
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Restriction criteria for quasicoherent modules on schemes

The equivalence between modules on an open subscheme and modules on its slice site preserves
quasicoherence in both directions. Consequently, quasicoherence can be checked on restrictions
to any open cover, or to all affine opens.

The criteria live in `TauCeti.AlgebraicGeometry` and use ordinary function application.
They transport quasicoherence with Mathlib's open-subscheme equivalence and descend it
with `SheafOfModules.IsQuasicoherent.of_coversTop`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- Quasicoherence can be checked after restriction along a scheme isomorphism. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict_iso {X Y : Scheme.{u}}
    (e : X ≅ Y) (M : X.Modules) [hM : (M.restrict e.inv).IsQuasicoherent] :
    M.IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor e.inv
  let G := Scheme.Modules.restrictFunctor e.hom
  have : (G.obj (F.obj M)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.hom _
  let i : G.obj (F.obj M) ≅ M :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app _ ≪≫
      Scheme.Modules.restrictFunctorId.app _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso i inferInstance

/-- The open-subscheme equivalence sends a quasicoherent module on the slice site to a
quasicoherent module on the open subscheme. -/
instance isQuasicoherent_overEquiv_functor {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.inverse
  have hcont (V : TopologicalSpace.Opens {x : X // x ∈ U}) : (Over.post (X := V) G).IsContinuous
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over V)
      (((Opens.grothendieckTopology X).over U).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  -- Pass the instances explicitly: the scheme and sheaf categories have different
  -- instance heads, although their carriers agree.
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- The inverse open-subscheme equivalence sends quasicoherent modules to quasicoherent
modules on the slice site. -/
instance isQuasicoherent_overEquiv_inverse {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [hM : M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let G := U.overEquivalence.functor
  have hcont (V : Over U) : (Over.post (X := V) G).IsContinuous
      (((Opens.grothendieckTopology X).over U).over V)
      ((Opens.grothendieckTopology {x : X // x ∈ U}).over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G _ _).overPost V)
  let ψ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have hψ : IsIso ψ := by dsimp [ψ]; infer_instance
  -- Pass the instances explicitly: the scheme and sheaf categories have different
  -- instance heads, although their carriers agree.
  exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ ψ
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ hψ hcont _ _ M hM

/-- Quasicoherence on an open subscheme implies quasicoherence on its slice site. -/
theorem isQuasicoherent_over_of_isQuasicoherent_restrict {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) [hM : (M.restrict U.ι).IsQuasicoherent] :
    (M.over U).IsQuasicoherent := by
  have h := isQuasicoherent_overEquiv_inverse U (M.restrict U.ι)
  let e := (Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
    (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso e.symm h

/-- Quasicoherence can be checked on restrictions to an open cover. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict {X : Scheme.{u}} {ι : Type u}
    (M : X.Modules) (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  have (i : ι) : (M.over (U i)).IsQuasicoherent := by
    have := h i
    exact isQuasicoherent_over_of_isQuasicoherent_restrict M (U i)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U
    (by rwa [Opens.coversTop_iff])

/-- Quasicoherence can be checked on restrictions to all affine open subschemes. -/
theorem isQuasicoherent_of_isQuasicoherent_restrict_affineOpens {X : Scheme.{u}}
    (M : X.Modules) (h : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent) :
    M.IsQuasicoherent :=
  isQuasicoherent_of_isQuasicoherent_restrict M (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) h

end

end TauCeti.AlgebraicGeometry
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction"

section ComponentSource_1
/- Original module: TauCeti.AlgebraicGeometry.Scheme.Opens -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
* `AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom` identifies restriction of
  structure-sheaf sections along the affine chart `Spec Γ(X, U)`.
* `AlgebraicGeometry.Scheme.Hom.iSup_affineOpens_le_preimage_eq_top`: the affine opens of `X`
  which a morphism `X ⟶ Y` maps into an affine open of `Y` cover `X`.
* `AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id` identifies the restriction maps of a scheme
  endomorphism equal to the identity.
* `AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le`: a condition on the restrictions of a
  section over `V` to all affine opens inside `V` is inherited by its restriction to any smaller
  open.
* `AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens`: sections over the affine opens,
  compatible with restriction, glue to a unique global section.
* `AlgebraicGeometry.Scheme.exists_finite_affineOpens_cover`: a quasi-compact open is covered by
  finitely many affine opens contained in it, in the form used by sheaf gluing.
* `AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self` and
  `AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality` compute the global sections of
  affine charts `Spec R ⟶ X` and their precomposites with `Spec.map φ`.
* `AlgebraicGeometry.IsAffineOpen.span_restrict_basicOpen_le_eq_top`: for affine opens `V ≤ U`,
  the restrictions of the functions on `U` whose basic open lies in `V` generate the unit ideal of
  `Γ(X, V)`.
* `AlgebraicGeometry.Scheme.inf_mem_range_basicOpen` and
  `AlgebraicGeometry.IsAffineOpen.exists_mem_range_basicOpen_le_sup`: the basic opens of `U` are
  closed under intersections, and for `U` affine, a basic open covered by a basic open `A` and
  finitely many basic opens `V i` is covered by `A` and one basic open inside the union of the
  `V i`.
* `AlgebraicGeometry.IsAffineOpen.finset_inf`: on a scheme with affine diagonal, nonempty finite
  intersections of affine opens are affine.
-/

open TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

public section

open _root_.CategoryTheory Opposite

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

/-- The preimages of two opens covering the target cover the source. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.preimage_sup_eq_top {Y : Scheme.{u}}
    (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ⊔ V = ⊤) :
    f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by
  rw [← f.preimage_sup, hUV, f.preimage_top]

/-- For a morphism `f : X ⟶ Y`, the affine opens of `X` which `f` maps into an affine open of `Y`
cover `X`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.iSup_affineOpens_le_preimage_eq_top {Y : Scheme.{u}}
    (f : X ⟶ Y) :
    ⨆ V : {V : X.affineOpens // ∃ U : Y.affineOpens, V.1 ≤ f ⁻¹ᵁ U.1}, V.1.1 = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩, hxV⟩

/-- On a scheme with affine diagonal, for instance a separated one, a nonempty finite intersection
of affine opens is affine. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.finset_inf
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) {U : ι → X.Opens} (hU : ∀ i ∈ s, IsAffineOpen (U i)) :
    IsAffineOpen (s.inf U) := by
  rw [Finset.inf_eq_iInf]
  exact IsAffineOpen.biInf _ s.finite_toSet hs hU

/-- If an endomorphism `f` of `X` equals the identity, then so does each of its restriction maps
`Γ(X, U) ⟶ Γ(X, U)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_id_of_eq_id {f : X ⟶ X}
    (hf : f = 𝟙 X) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U) : f.appLE U U e = 𝟙 _ := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- A condition imposed on the restrictions of a section `b` over `V` to all affine opens inside `V`
is inherited by the restriction of `b` to any smaller open `V'`. -/
theorem _root_.AlgebraicGeometry.Scheme.forall_affineOpens_map_of_le {V V' : X.Opens}
    (hV'V : V' ≤ V) {b : Γ(X, V)} {P : ∀ W : X.affineOpens, Γ(X, W) → Prop}
    (h : ∀ (W : X.affineOpens) (hWV : W.1 ≤ V), P W (X.presheaf.map (homOfLE hWV).op b))
    (W : X.affineOpens) (hWV' : W.1 ≤ V') :
    P W (X.presheaf.map (homOfLE hWV').op (X.presheaf.map (homOfLE hV'V).op b)) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  exact h W (hWV'.trans hV'V)

/-- **Sections glue along the affine opens.** A family of sections `s U ∈ Γ(X, U)`, one over each
affine open `U` of `X`, compatible with restriction from an affine open to a smaller one, consists
of the restrictions of a unique global section. -/
theorem _root_.AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens (X : Scheme.{u})
    (s : ∀ U : X.affineOpens, Γ(X, U.1))
    (hs : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), X.presheaf.map (homOfLE h).op (s U) = s V) :
    ∃! t : Γ(X, ⊤), ∀ U : X.affineOpens, X.presheaf.map (homOfLE le_top).op t = s U := by
  -- every open `V` is covered by the affine opens it contains
  have hcov (V : X.Opens) : V ≤ ⨆ W : {W : X.affineOpens // W.1 ≤ V}, W.1.1 := fun x hx ↦ by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
  refine X.sheaf.existsUnique_gluing' (fun U : X.affineOpens ↦ U.1) ⊤ (fun _ ↦ homOfLE le_top)
    (iSup_affineOpens_eq_top X).ge s fun U U' ↦ ?_
  -- on `U ⊓ U'`, the two restrictions agree on every affine open `W ⊆ U ⊓ U'`
  refine X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.1 ≤ U.1 ⊓ U'.1} ↦ W.1.1) _
    (fun W ↦ homOfLE W.2) (hcov _) _ _ fun W ↦ ?_
  -- stated through `X.presheaf`, the underlying presheaf of `X.sheaf`
  have h₁ : X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLELeft U.1 U'.1).op (s U)) =
      s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U W.1 (W.2.trans inf_le_left)
  have h₂ :
      X.presheaf.map (homOfLE W.2).op (X.presheaf.map (Opens.infLERight U.1 U'.1).op (s U')) =
        s W.1 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hs U' W.1 (W.2.trans inf_le_right)
  exact h₁.trans h₂.symm

/-- A quasi-compact open `U` is covered by finitely many affine opens contained in it. This is
`AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens` stated as a family of opens
below `U` whose supremum contains `U`, the form taken by the sheaf gluing lemmas
`TopCat.Sheaf.eq_of_locally_eq'` and `TopCat.Sheaf.existsUnique_gluing'`. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_finite_affineOpens_cover
    (hU : IsCompact (U : Set X)) :
    ∃ (s : Set X.affineOpens) (_ : Finite s), (∀ i : s, (i.1 : X.Opens) ≤ U) ∧
      U ≤ ⨆ i : s, (i.1 : X.Opens) := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  exact ⟨s, hs.to_subtype, fun i ↦ e ▸ le_biSup (fun j : X.affineOpens ↦ (j : X.Opens)) i.2,
    by rw [e, iSup_subtype']⟩

/-- Along the open immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` onto an affine open `U`,
restricting a section of `𝒪_X` from `U` to the image of an open `V` and transporting it to `V`
gives the restriction to `V` of the corresponding global section of `Spec Γ(X, U)`. -/
@[reassoc]
theorem _root_.AlgebraicGeometry.IsAffineOpen.presheaf_map_fromSpec_appIso_hom
    (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens) :
    X.presheaf.map (homOfLE (by
        simpa [hU.opensRange_fromSpec] using hU.fromSpec.image_le_opensRange V)).op ≫
      (hU.fromSpec.appIso V).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op := by
  rw [← hU.fromSpec.appLE_appIso_inv (by simp [hU.fromSpec_preimage_self]), Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp]
  rfl

/-- Pulling a section over an affine open `U` back to all of `Spec Γ(X, U)` along `hU.fromSpec`
is the inverse of the global-sections isomorphism of `Spec`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_self (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans
    ((Spec Γ(X, U)).presheaf.map_id _))).trans (Category.comp_id _)

/-- For affine opens `V ≤ U`, the restrictions to `V` of the functions on `U` whose basic open lies
in `V` generate the unit ideal of `Γ(X, V)`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.span_restrict_basicOpen_le_eq_top {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Ideal.span {g : Γ(X, V) | ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧
      X.presheaf.map (homOfLE hVU).op f = g} = ⊤ := by
  refine (hV.self_le_iSup_basicOpen_iff).mp fun x hx ↦ ?_
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hVU hx)
  refine Opens.mem_iSup.mpr ⟨⟨_, f, hfV, rfl⟩, ?_⟩
  rw [Scheme.basicOpen_res]
  exact ⟨hx, hxf⟩

/-- The basic opens `X.basicOpen f` of sections `f` over an open `U` are closed under binary
intersections. -/
theorem _root_.AlgebraicGeometry.Scheme.inf_mem_range_basicOpen :
    ∀ V ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
      ∀ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
        V ⊓ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f := by
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact ⟨f * g, Scheme.basicOpen_mul _ _ _⟩

/-- Let `U` be an affine open. If a basic open `Y` of `U` lies in the union of a basic open `A`
and of finitely many basic opens `V i`, `i ∈ s`, of `U`, then it lies in the union of `A` and of a
single basic open of `U` contained in the union of the `V i`. -/
theorem _root_.AlgebraicGeometry.IsAffineOpen.exists_mem_range_basicOpen_le_sup
    (hU : IsAffineOpen U) {Y A : X.Opens} (hY : Y ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f)
    (hA : A ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, V i ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f) (s : Finset ι)
    (h : Y ≤ A ⊔ s.sup V) : ∃ W ∈ Set.range fun f : Γ(X, U) ↦ X.basicOpen f,
      Y ≤ A ⊔ W ∧ W ≤ s.sup V := by
  classical
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨f, rfl⟩ := hA
  choose f' hf' using hV
  beta_reduce at h hf'
  let r : Γ(X, U) → Γ(X, X.basicOpen g) := fun a ↦ X.presheaf.map (homOfLE (X.basicOpen_le g)).op a
  have hr (a : Γ(X, U)) : X.basicOpen (r a) = X.basicOpen g ⊓ X.basicOpen a :=
    Scheme.basicOpen_res _ _ _
  let T : Set Γ(X, X.basicOpen g) := (fun i ↦ r (f' i)) '' ↑s
  -- the restrictions of `f` and of the `f' i` to `D(g)` generate the unit ideal there
  have hspan : Ideal.span (insert (r f) T) = ⊤ := by
    refine ((hU.basicOpen g).self_le_iSup_basicOpen_iff (s := insert (r f) T)).1 ?_
    intro x hx
    rcases Opens.mem_sup.1 (h hx) with hxf | hxs
    · exact Opens.mem_iSup.2 ⟨⟨r f, Set.mem_insert _ _⟩, by rw [hr]; exact ⟨hx, hxf⟩⟩
    · rw [Finset.sup_eq_iSup] at hxs
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.1 hxs
      obtain ⟨hi, hxi⟩ := Opens.mem_iSup.1 hxi
      exact Opens.mem_iSup.2 ⟨⟨r (f' i), Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩⟩,
        by rw [hr, hf']; exact ⟨hx, hxi⟩⟩
  obtain ⟨a, z, hz, haz⟩ := Ideal.mem_span_insert.1
    (hspan ▸ Submodule.mem_top : (1 : Γ(X, X.basicOpen g)) ∈ Ideal.span (insert (r f) T))
  obtain ⟨h', hh'⟩ := hU.basicOpen_basicOpen_is_basicOpen g z
  refine ⟨X.basicOpen h', ⟨h', rfl⟩, ?_, ?_⟩
  · rw [hh']
    calc X.basicOpen g = X.basicOpen (a * r f + z) := by rw [← haz, Scheme.basicOpen_one]
      _ ≤ X.basicOpen (a * r f) ⊔ X.basicOpen z := X.basicOpen_add_le _ _
      _ ≤ X.basicOpen f ⊔ X.basicOpen z := by
        refine sup_le_sup_right ?_ _
        rw [Scheme.basicOpen_mul, hr]
        exact inf_le_right.trans inf_le_right
  · -- a point of `D(z)` outside every `V i` would lie in the zero locus of the span of `T`
    rw [hh']
    intro x hx
    by_contra hxs
    have hxT : x ∈ X.zeroLocus T := by
      rw [Scheme.mem_zeroLocus_iff]
      rintro _ ⟨i, hi, rfl⟩ hxi
      rw [hr, hf'] at hxi
      exact hxs (Finset.le_sup (f := V) hi hxi.2)
    rw [← Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hxT
    exact hxT z hz hx

/-- Global sections of an affine chart `f : Spec R ⟶ Y` are natural in `R`: precomposing `f` with
`Spec.map φ` turns the induced map `Γ(Y, V) ⟶ R` into its composite with `φ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_ΓSpecIso_hom_naturality {R S : CommRingCat.{u}}
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) {q : Spec S ⟶ Y} (φ : R ⟶ S) (h : q = Spec.map φ ≫ f)
    {V : Y.Opens} (e : ⊤ ≤ f ⁻¹ᵁ V) (e' : ⊤ ≤ q ⁻¹ᵁ V) :
    q.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso S).hom =
      (f.appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
  subst h
  -- `Scheme.Hom.appLE_eq_app` at `⊤` applies because `Spec.map φ ⁻¹ᵁ ⊤` is `⊤` by definition.
  have h : (Spec.map φ ≫ f).appLE V ⊤ e' = f.appLE V ⊤ e ≫ (Spec.map φ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (Spec.map φ) f V ⊤ ⊤ e le_top).symm.trans
      (congrArg (f.appLE V ⊤ e ≫ ·) (Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤)))
  rw [h, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]

end

end

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

end Scheme

end AlgebraicGeometry

end TauCeti
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.AlgebraicGeometry.Scheme.Opens"

section ComponentSource_2
/- Original module: TauCeti.Algebra.Group.Action.Pow -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Strings of powers acting on a vector

For a monoid `M` acting on a type `V` with a zero, an element `x : M` and a vector `w : V`, the
`x`-string of `w` is the sequence `w, x • w, x² • w, …`. This file shows that if the string
contains `0` and `w ≠ 0`, then some nonzero term `xⁿ • w` is immediately followed by the zero
term `x • xⁿ • w`. The action need not fix `0`, so later terms of the string may be nonzero
again. Raising and lowering operators of representations, such as `E` and `F` for `U_q(sl₂)`,
use this to produce highest- and lowest-weight vectors. When the action fixes the zero, once a
term of the string vanishes all later terms vanish.

## Main results

* `TauCeti.exists_pow_smul_ne_zero_and_smul_eq_zero`: if `xⁿ • w = 0` for some `n` and `w ≠ 0`,
  then `xⁿ • w ≠ 0` and `x • xⁿ • w = 0` for some `n`.
* `TauCeti.pow_smul_eq_zero_of_le`: for an action fixing `0`, if `xᵐ • w = 0` and `m ≤ n`, then
  `xⁿ • w = 0`.
-/

public section

namespace TauCeti

variable {M V : Type*} [Monoid M] [MulAction M V] [Zero V]

/-- If some power of `x` kills a nonzero vector `w`, then the string `w, x • w, x² • w, …` has a
nonzero term `xⁿ • w` immediately followed by the zero term `x • xⁿ • w`. -/
theorem exists_pow_smul_ne_zero_and_smul_eq_zero {x : M} {w : V} (hw0 : w ≠ 0)
    (h : ∃ n : ℕ, x ^ n • w = 0) : ∃ n : ℕ, x ^ n • w ≠ 0 ∧ x • x ^ n • w = 0 := by
  classical
  have hn : 0 < Nat.find h :=
    Nat.pos_of_ne_zero fun hn ↦ hw0 (by simpa [hn] using Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hn]
  exact Nat.find_spec h

/-- If a power of `x` kills `w` and scalars fix `0`, then every higher power of `x` kills `w`.
This is the action counterpart of `pow_mul_eq_zero_of_le`. It only uses `x • 0 = 0` and
`(x * y) • w = x • y • w` (`IsScalarTower M M N`); no addition on `N` is needed. -/
theorem pow_smul_eq_zero_of_le {M N : Type*} [Monoid M] [Zero N] [SMulZeroClass M N]
    [IsScalarTower M M N] {x : M} {w : N} {m n : ℕ} (hmn : m ≤ n) (h : x ^ m • w = 0) :
    x ^ n • w = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, ← smul_eq_mul, smul_assoc, h, smul_zero]

end TauCeti
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.Algebra.Group.Action.Pow"

section ComponentSource_3
/- Original module: TauCeti.AlgebraicGeometry.Modules.Localization -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sections of quasi-coherent modules over basic opens

Let `M` be a quasi-coherent `𝒪_X`-module on a scheme `X`, let `U` be an affine open of `X` and
let `f ∈ Γ(X, U)`. Then the sections of `M` over the basic open `X.basicOpen f` are the
localization of the sections over `U` at the powers of `f`: the restriction map
`Γ(M, U) ⟶ Γ(M, X.basicOpen f)` is a localization of `Γ(X, U)`-modules. This is the module
counterpart of `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen` for the structure sheaf.

This is the affine-local description of quasi-coherent modules needed to build objects over `X`
from their sections over affine opens. For instance, it is the condition making a quasi-coherent
sheaf of algebras coequifibered over the structure sheaf on the small affine Zariski site, which
is the input of `AlgebraicGeometry.AffineZariskiSite.relativeGluingData`.

Over `Spec R` the statement is Mathlib's `AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing`;
this module extends that affine result to arbitrary schemes. Conversely, an `𝒪_X`-module whose
sections over the basic opens of the members of an affine open cover are such localizations is
quasi-coherent. This is how quasi-coherence is checked for modules built from explicit sections,
such as the twisting sheaves on `Proj`.

More generally, the restriction is a localization over every quasi-compact quasi-separated open
`U`. Sections over `U` are determined by their restrictions to a finite affine cover, and are
glued from sections that agree on the pairwise intersections, which are quasi-compact. On each
affine member a section over `X.basicOpen f` extends after multiplication by a power of `f`, and
on the quasi-compact intersections the extensions agree after multiplication by a further power.
This is the input for the quasi-coherence of pushforwards along quasi-compact quasi-separated
morphisms.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.moduleBasicOpen`: for `f ∈ Γ(X, U)`, the sections
  `Γ(M, X.basicOpen f)` form a `Γ(X, U)`-module by restriction of scalars;
* `AlgebraicGeometry.Scheme.Modules.basicOpenRestrict`: the restriction map
  `Γ(M, U) ⟶ Γ(M, X.basicOpen f)` as a `Γ(X, U)`-linear map;
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`: for quasi-coherent
  `M` and affine `U`, this restriction map is the localization at the powers of `f`.
* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map`: for quasi-coherent `M` and affine
  `U`, a section over `X.basicOpen f` times a power of `f` extends to `U`.
* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact`: for quasi-coherent `M`
  and quasi-compact `U`, a section over `U` vanishing on `X.basicOpen f` is killed by a power of
  `f`.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`: for
  quasi-coherent `M` and quasi-compact quasi-separated `U`, the restriction map
  `Γ(M, U) ⟶ Γ(M, X.basicOpen f)` is the localization at the powers of `f`.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule`: conversely, `M` is
  quasi-coherent if these restriction maps are localizations on the members of an affine open
  cover; `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_isLocalizedModule` is the
  resulting characterization.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma II.5.3.
* R. Vakil, *The Rising Sea*, the qcqs lemma; Mathlib's
  `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` is the structure-sheaf case.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I* (1971),
  Théorème 1.4.1.
-/

public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} {U : X.Opens}

variable (M : X.Modules)

/-- For `f ∈ Γ(X, U)`, the sections of an `𝒪_X`-module over `X.basicOpen f` form a
`Γ(X, U)`-module by restriction of scalars along `Γ(X, U) ⟶ Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.moduleBasicOpen (f : Γ(X, U)) :
    Module Γ(X, U) Γ(M, X.basicOpen f) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

/-- The `Γ(X, U)`-module structure on `Γ(M, X.basicOpen f)` factors through
`Γ(X, X.basicOpen f)`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isScalarTower_basicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
  IsScalarTower.of_compHom _ _ _

/-- A function `r` on `U` acts on sections over `X.basicOpen f` through its restriction to
`X.basicOpen f`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.basicOpen_smul_def (f r : Γ(X, U))
    (y : Γ(M, X.basicOpen f)) :
    r • y = X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • y :=
  rfl

/-- The restriction of sections of an `𝒪_X`-module from `U` to `X.basicOpen f`, as a
`Γ(X, U)`-linear map. -/
def _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict (f : Γ(X, U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' := map_add _
  map_smul' r x := M.map_smul _ r x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.basicOpenRestrict_apply (f : Γ(X, U))
    (x : Γ(M, U)) :
    M.basicOpenRestrict f x = M.presheaf.map (homOfLE (X.basicOpen_le f)).op x :=
  (rfl)

/-- A section `f ∈ Γ(X, U)` acts invertibly on the sections of an `𝒪_X`-module over the basic
open `X.basicOpen f`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_basicOpen (f : Γ(X, U)) :
    IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) f) := by
  rw [Module.End.isUnit_iff]
  -- by `moduleBasicOpen`, `f` acts through its restriction to `X.basicOpen f`, a unit there
  have : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) f) =
      algebraMap Γ(X, X.basicOpen f) (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f))
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    (rfl)
  rw [this, ← Module.End.isUnit_iff]
  exact (X.toRingedSpace.isUnit_res_basicOpen f).map _

/-- For an affine open `U`, the sections of an `𝒪_X`-module `M` over `U` are the global sections
of its restriction to the affine chart `Spec Γ(X, U) ⟶ X`, as `Γ(X, U)`-modules. Here
`Γ(X, U)` acts on the global sections of a module on `Spec Γ(X, U)` as their ring of
global functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.fromSpecSectionsEquiv (hU : IsAffineOpen U) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(M.restrict hU.fromSpec, ⊤) :=
  have h : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have : IsIso (homOfLE h.le) := homOfLE_isIso_of_eq _ h
  LinearEquiv.ofBijective
    { toFun := M.presheaf.map (homOfLE h.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv
      map_add' := map_add _
      -- Linearity is `presheaf_map_fromSpec_appIso_hom` at `⊤`.
      map_smul' r x := by
        rw [RingHom.id_apply, Scheme.Modules.smul_Spec_def, ConcreteCategory.comp_apply,
          M.map_smul, Scheme.Modules.smul_restrictAppIso_inv_apply,
          ← ConcreteCategory.comp_apply, hU.presheaf_map_fromSpec_appIso_hom ⊤]
        rfl }
    (ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (homOfLE h.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv))

/-- The identification `Γ(M, U) ≃ Γ(M.restrict hU.fromSpec, ⊤)` is restriction of sections to
the image of the affine chart, which is `U`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.fromSpecSectionsEquiv_apply (hU : IsAffineOpen U)
    (x : Γ(M, U)) :
    M.fromSpecSectionsEquiv hU x = (M.restrictAppIso hU.fromSpec ⊤).inv
      (M.presheaf.map (homOfLE (by
        rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op x) :=
  (rfl)

/-- The affine-chart identification of sections commutes with maps of module sheaves. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality
    {N : X.Modules} (f : M ⟶ N) (hU : IsAffineOpen U) (x : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctor hU.fromSpec).map f).app ⊤
        (M.fromSpecSectionsEquiv hU x) =
      N.fromSpecSectionsEquiv hU (f.app U x) := by
  rw [Scheme.Modules.fromSpecSectionsEquiv_apply,
    Scheme.Modules.fromSpecSectionsEquiv_apply]
  -- The restriction functor and its section isomorphism only change scalar structures.
  -- Their underlying maps are the components of `f` on the image open.
  exact PresheafOfModules.naturality_apply f.val _ x

open Scheme.Modules in
/-- For an affine open `U`, the restriction of `M` to the affine chart `Spec Γ(X, U)` is
localizing in the sense of Mathlib's `AlgebraicGeometry.IsLocalizing` iff, for every
`f ∈ Γ(X, U)`, the restriction of sections of `M` from `U` to `X.basicOpen f` is a localization
at `f`. -/
private theorem isLocalizing_restrict_fromSpec_iff (hU : IsAffineOpen U) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)) ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f) := by
  refine forall_congr' fun f ↦ ?_
  -- Compare the restriction maps along the identifications of `U` and `X.basicOpen f` with the
  -- images of `⊤` and `D(f)` under `hU.fromSpec`.
  let N := M.restrict hU.fromSpec
  let D : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  have h₁ : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have h₂ : hU.fromSpec ''ᵁ D = X.basicOpen f := hU.fromSpec_image_basicOpen f
  -- `e₁` identifies `Γ(M, U)` with `Γ(N, ⊤)`.
  let e₁ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, ⊤) := (M.fromSpecSectionsEquiv hU).toLinearMap
  -- `e₂` identifies `Γ(N, D(f))` with `Γ(M, X.basicOpen f)`; its linearity is
  -- `presheaf_map_fromSpec_appIso_hom` at `D(f)`, followed by restriction to `X.basicOpen f`.
  let e₂ : Γ(N, D) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) :=
    { toFun := (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op
      map_add' := map_add _
      map_smul' r x := by
        rw [RingHom.id_apply, smul_Spec_def, ConcreteCategory.comp_apply,
          smul_restrictAppIso_hom_apply, M.map_smul, ← algebraMap_smul Γ(X, X.basicOpen f) r]
        congr 1
        have hr : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map D.leTop.op ≫
            (hU.fromSpec.appIso D).inv ≫ X.presheaf.map (homOfLE h₂.ge).op =
            X.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
          rw [← Category.assoc, ← Category.assoc, ← hU.presheaf_map_fromSpec_appIso_hom D]
          simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
          rfl
        have := ConcreteCategory.congr_hom hr r
        simp only [ConcreteCategory.comp_apply] at this
        exact this }
  -- The restriction map of `N`.
  let φ : Γ(N, ⊤) →ₗ[Γ(X, U)] Γ(N, D) :=
    { toFun := N.presheaf.map D.leTop.op
      map_add' := map_add _
      map_smul' r x := N.map_smul_Spec _ r x }
  -- The restriction map of `M` is `φ` transported along the bijections `e₁` and `e₂`.
  have he : M.basicOpenRestrict f = e₂ ∘ₗ φ ∘ₗ e₁ := by
    have h : M.presheaf.map (homOfLE (X.basicOpen_le f)).op =
        (M.presheaf.map (homOfLE h₁.le).op ≫ (M.restrictAppIso hU.fromSpec ⊤).inv) ≫
          (M.restrict hU.fromSpec).presheaf.map D.leTop.op ≫
            (M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op := by
      simp only [Category.assoc, map_restrictAppIso_hom_assoc, Iso.inv_hom_id_assoc,
        ← Functor.map_comp]
      rfl
    exact LinearMap.ext fun x ↦ ConcreteCategory.congr_hom h x
  have h₂iso : IsIso (M.presheaf.map (homOfLE h₂.ge).op) := by
    have : IsIso (homOfLE h₂.ge) := homOfLE_isIso_of_eq _ h₂.symm
    infer_instance
  have he₁ : Function.Bijective e₁ := (M.fromSpecSectionsEquiv hU).bijective
  have he₂ : Function.Bijective e₂ := ConcreteCategory.bijective_of_isIso
    ((M.restrictAppIso hU.fromSpec D).hom ≫ M.presheaf.map (homOfLE h₂.ge).op)
  have key : IsLocalizedModule.Away f (M.basicOpenRestrict f) ↔ IsLocalizedModule.Away f φ := by
    unfold IsLocalizedModule.Away
    rw [he, IsLocalizedModule.comp_iff_of_bijective_left,
      IsLocalizedModule.comp_iff_of_bijective_right]
    exacts [he₁, he₂]
  -- `φ` is the restriction map of `modulesSpecToSheaf.obj N` from `⊤` to `D(f)`
  exact key.symm

open Scheme.Modules in
/-- The sections of a quasi-coherent `𝒪_X`-module over the basic open `X.basicOpen f` of an
affine open `U` are the localization of its sections over `U` at the powers of `f`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict
    [M.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (M.basicOpenRestrict f) :=
  (isLocalizing_restrict_fromSpec_iff M hU).1
    ((isIso_fromTildeΓ_iff_isLocalizing (M.restrict hU.fromSpec)).1 inferInstance) f

/-- **Quasi-coherence on an affine chart from localizations.** If, for an affine open `U`, the
sections of `M` over every basic open `X.basicOpen f` are the localization at `f` of the sections
over `U`, then the restriction of `M` to the affine chart `Spec Γ(X, U)` is quasi-coherent. This
is the converse of `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrict_fromSpec
    (hU : IsAffineOpen U) (h : ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f)) :
    (M.restrict hU.fromSpec).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).2
    ((isIso_fromTildeΓ_iff_isLocalizing _).2 ((isLocalizing_restrict_fromSpec_iff M hU).2 h))

/-- **Quasi-coherence from localizations on an affine open cover.** An `𝒪_X`-module `M` is
quasi-coherent as soon as `X` is covered by affine opens `U i` such that, for every
`f ∈ Γ(X, U i)`, the sections of `M` over `X.basicOpen f` are the localization at `f` of the
sections over `U i`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i (f : Γ(X, U i)), IsLocalizedModule.Away f (M.basicOpenRestrict f)) :
    M.IsQuasicoherent := by
  refine AlgebraicGeometry.isQuasicoherent_of_isQuasicoherent_restrict M U hcov fun i ↦ ?_
  have := M.isQuasicoherent_restrict_fromSpec (hU i) (h i)
  -- `U i` is isomorphic to the affine chart, through which `U.ι` factors
  have := Scheme.Modules.isQuasicoherent_restrictFunctor (hU i).isoSpec.hom
    (M.restrict (hU i).fromSpec)
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.restrictFunctorComp (hU i).isoSpec.hom (hU i).fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (hU i).isoSpec_hom_fromSpec).app M) this

/-- An `𝒪_X`-module is quasi-coherent iff, for every affine open `U` and every `f ∈ Γ(X, U)`,
its sections over `X.basicOpen f` are the localization at `f` of its sections over `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_iff_isLocalizedModule :
    M.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (M.basicOpenRestrict f) :=
  ⟨fun _ _ hU f ↦ M.isLocalizedModule_basicOpenRestrict hU f, fun h ↦
    M.isQuasicoherent_of_isLocalizedModule (fun U : X.affineOpens ↦ U.1) (fun U ↦ U.2)
      (iSup_affineOpens_eq_top X) fun U ↦ h U.1 U.2⟩

open Scheme.Modules in
/-- **Sections over a basic open extend after multiplication by a power of the function.** For a
quasi-coherent `𝒪_X`-module `M`, an affine open `U` and `f ∈ Γ(X, U)`, every section `x` of `M`
over the basic open `V = X.basicOpen f` has some `f ^ n • x` equal to the restriction of a
section over `U`. The open `V` is arbitrary up to the equality `X.basicOpen f = V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map [M.IsQuasicoherent]
    (hU : IsAffineOpen U) (f : Γ(X, U)) {V : X.Opens} (hV : X.basicOpen f = V) (hVU : V ≤ U)
    (x : Γ(M, V)) : ∃ (n : ℕ) (y : Γ(M, U)),
      X.presheaf.map (homOfLE hVU).op f ^ n • x = M.presheaf.map (homOfLE hVU).op y := by
  subst hV
  have := M.isLocalizedModule_basicOpenRestrict hU f
  obtain ⟨⟨y, _, n, rfl⟩, hy⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (M.basicOpenRestrict f) x
  -- `f ^ n` acts on sections over `X.basicOpen f` through its restriction
  simp only [Submonoid.smul_def] at hy
  rw [← IsScalarTower.algebraMap_smul Γ(X, X.basicOpen f), map_pow,
    basicOpenRestrict_apply] at hy
  exact ⟨n, y, hy⟩

open Scheme.Modules in
/-- **Sections vanishing on a basic open are killed by a power of the function.** For a
quasi-coherent `𝒪_X`-module `M`, a quasi-compact open `U` and `f ∈ Γ(X, U)`, a section of `M`
over `U` whose restriction to `X.basicOpen f` vanishes is killed by a power of `f`. For the
structure sheaf this is
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isCompact
    [M.IsQuasicoherent] (hU : IsCompact (U : Set X)) (f : Γ(X, U)) (x : Γ(M, U))
    (hx : M.basicOpenRestrict f x = 0) : ∃ n : ℕ, f ^ n • x = 0 := by
  obtain ⟨s, _, hVU, hUV⟩ := X.exists_finite_affineOpens_cover hU
  cases nonempty_fintype s
  -- On each affine `V i ≤ U`, the restriction of `x` is killed by a power of `f`.
  have H (i : s) : ∃ n : ℕ, X.presheaf.map (homOfLE (hVU i)).op f ^ n •
      M.presheaf.map (homOfLE (hVU i)).op x = 0 := by
    have := M.isLocalizedModule_basicOpenRestrict i.1.2 (X.presheaf.map (homOfLE (hVU i)).op f)
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (X.presheaf.map (homOfLE (hVU i)).op f))
      (f := M.basicOpenRestrict _) (x₁ := M.presheaf.map (homOfLE (hVU i)).op x) (x₂ := 0) (by
        have hle : X.basicOpen (X.presheaf.map (homOfLE (hVU i)).op f) ≤ X.basicOpen f :=
          X.basicOpen_restrict (homOfLE (hVU i)) f
        simpa only [basicOpenRestrict_apply, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
          map_zero] using
          congrArg (M.presheaf.map (homOfLE hle).op) hx)
    exact ⟨n, by simpa [Submonoid.smul_def] using hn⟩
  choose n hn using H
  -- The largest of these powers kills `x` on every `V i`, hence on `U`.
  refine ⟨Finset.univ.sup n, TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) (fun i : s ↦ (i.1 : X.Opens)) U
    (fun i ↦ homOfLE (hVU i)) hUV _ _ fun i ↦ ?_⟩
  -- The restriction maps of the sheaf `⟨M.presheaf, M.isSheaf⟩` are those of `M`.
  change M.presheaf.map _ _ = M.presheaf.map _ _
  rw [map_zero, M.map_smul, map_pow]
  exact pow_smul_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)

open Scheme.Modules in
/-- Let the opens `V i ≤ U` cover `U`, with quasi-compact pairwise intersections. Sections `x i`
over the `V i` whose restrictions to the opens `V i ⊓ V j ⊓ X.basicOpen f` agree glue to a
section over `U` after multiplication by a power of `f`. -/
private lemma exists_pow_smul_eq_of_isCompact_inf [M.IsQuasicoherent] {ι : Type*} [Finite ι]
    (V : ι → X.Opens) (hVU : ∀ i, V i ≤ U) (hUV : U ≤ ⨆ i, V i)
    (hV : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X)) (f : Γ(X, U))
    (x : ∀ i, Γ(M, V i))
    (hx : ∀ i j, M.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        V i ⊓ V j ⊓ X.basicOpen f ≤ V i)).op (x i) =
      M.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        V i ⊓ V j ⊓ X.basicOpen f ≤ V j)).op (x j)) :
    ∃ (m : ℕ) (g : Γ(M, U)), ∀ i,
      M.presheaf.map (homOfLE (hVU i)).op g = X.presheaf.map (homOfLE (hVU i)).op f ^ m • x i := by
  cases nonempty_fintype ι
  have hWU (p : ι × ι) : V p.1 ⊓ V p.2 ≤ U := inf_le_left.trans (hVU p.1)
  -- The restrictions of `x i` and `x j` to `V i ⊓ V j` agree after multiplication by a power of
  -- `f`, since their difference vanishes on `X.basicOpen (f|V i ⊓ V j)`.
  have H (p : ι × ι) : ∃ m : ℕ, X.presheaf.map (homOfLE (hWU p)).op f ^ m •
      (M.presheaf.map (homOfLE inf_le_left).op (x p.1) -
        M.presheaf.map (homOfLE inf_le_right).op (x p.2)) = 0 := by
    refine M.exists_pow_smul_eq_zero_of_isCompact (hV p.1 p.2) _ _ ?_
    have hle : X.basicOpen (X.presheaf.map (homOfLE (hWU p)).op f) ≤
        V p.1 ⊓ V p.2 ⊓ X.basicOpen f := (X.basicOpen_res _ _).le
    simpa only [basicOpenRestrict_apply, map_sub, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp,
      sub_eq_zero] using
      congrArg (M.presheaf.map (homOfLE hle).op) (hx p.1 p.2)
  choose m hm using H
  -- After multiplication by the largest of these powers, the sections are compatible.
  let K := Finset.univ.sup m
  let z (i : ι) : Γ(M, V i) := X.presheaf.map (homOfLE (hVU i)).op f ^ K • x i
  have hc : TopCat.Presheaf.IsCompatible M.presheaf V z := by
    intro i j
    have h := pow_smul_eq_zero_of_le (Finset.le_sup (f := m) (Finset.mem_univ (i, j))) (hm (i, j))
    rw [smul_sub, sub_eq_zero] at h
    -- The inclusions of `V i ⊓ V j` in `V i` and `V j` are `homOfLE`.
    change M.presheaf.map (homOfLE inf_le_left).op _ = M.presheaf.map (homOfLE inf_le_right).op _
    simpa only [z, M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using h
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) V U (fun i ↦ homOfLE (hVU i)) hUV z
    hc
  exact ⟨K, g, hg⟩

open Scheme.Modules in
/-- For a quasi-coherent `𝒪_X`-module `M`, a quasi-compact quasi-separated open `U` and
`f ∈ Γ(X, U)`, every section of `M` over `X.basicOpen f` has some `f ^ n • y` equal to the
restriction of a section over `U`. -/
private theorem exists_pow_smul_eq_basicOpenRestrict [M.IsQuasicoherent]
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U))
    (y : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (x : Γ(M, U)), f ^ n • y = M.basicOpenRestrict f x := by
  obtain ⟨s, _, hVU, hUV⟩ := X.exists_finite_affineOpens_cover hU
  cases nonempty_fintype s
  have hDV (i : s) : (i.1 : X.Opens) ⊓ X.basicOpen f ≤ i.1 := inf_le_left
  have hDf (i : s) : (i.1 : X.Opens) ⊓ X.basicOpen f ≤ X.basicOpen f := inf_le_right
  -- On each affine `V i`, some `f ^ n i • y` extends to a section `x i`.
  have H (i : s) := M.exists_pow_smul_eq_map i.1.2 (X.presheaf.map (homOfLE (hVU i)).op f)
    (X.basicOpen_res _ _) (hDV i) (M.presheaf.map (homOfLE (hDf i)).op y)
  choose n x hx using H
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hx
  -- After multiplication by powers of `f`, the `x i` extend the same multiple `f ^ N • y`.
  let N := Finset.univ.sup n
  let x' (i : s) : Γ(M, i.1) := X.presheaf.map (homOfLE (hVU i)).op f ^ (N - n i) • x i
  have hx' (i : s) : M.presheaf.map (homOfLE (hDV i)).op (x' i) =
      X.presheaf.map (homOfLE ((hDV i).trans (hVU i))).op f ^ N •
        M.presheaf.map (homOfLE (hDf i)).op y := by
    simp only [x', M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]
    rw [← hx i, smul_smul, pow_sub_mul_pow _ (Finset.le_sup (f := n) (Finset.mem_univ i))]
  -- Since `U` is quasi-separated, the `x' i` glue after multiplication by a further power.
  obtain ⟨K, g, hg⟩ := exists_pow_smul_eq_of_isCompact_inf M (fun i : s ↦ (i.1 : X.Opens)) hVU
    hUV (fun i j ↦ hU' _ _ (hVU i) i.1.1.isOpen i.1.2.isCompact (hVU j) j.1.1.isOpen
      j.1.2.isCompact) f x' fun i j ↦ by
    have hi : (i.1 : X.Opens) ⊓ j.1 ⊓ X.basicOpen f ≤ (i.1 : X.Opens) ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have hj : (i.1 : X.Opens) ⊓ j.1 ⊓ X.basicOpen f ≤ (j.1 : X.Opens) ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    -- Restrict `hx' i` and `hx' j` further to `V i ⊓ V j ⊓ X.basicOpen f`.
    have hi' := congrArg (M.presheaf.map (homOfLE hi).op) (hx' i)
    have hj' := congrArg (M.presheaf.map (homOfLE hj).op) (hx' j)
    simp only [M.map_smul, map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hi' hj'
    rw [hi', hj']
  -- The glued section restricts to `f ^ (N + K) • y` on each `V i ⊓ X.basicOpen f`.
  refine ⟨N + K, g, TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i : s ↦ (i.1 : X.Opens) ⊓ X.basicOpen f) (X.basicOpen f) (fun i ↦ homOfLE (hDf i))
    (by rw [← iSup_inf_eq]; exact le_inf ((X.basicOpen_le f).trans hUV) le_rfl) _ _
    fun i ↦ ?_⟩
  -- The restriction maps of the sheaf `⟨M.presheaf, M.isSheaf⟩` are those of `M`.
  change M.presheaf.map _ _ = M.presheaf.map _ _
  -- Restrict the gluing identity `hg i` further to `V i ⊓ X.basicOpen f`.
  have hg' := congrArg (M.presheaf.map (homOfLE (hDV i)).op) (hg i)
  rw [M.map_smul, hx', smul_smul] at hg'
  rw [basicOpenRestrict_apply, ← IsScalarTower.algebraMap_smul Γ(X, X.basicOpen f), M.map_smul]
  simpa only [map_pow, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp, ← pow_add, add_comm K,
    RingHom.algebraMap_toAlgebra] using hg'.symm

open Scheme.Modules in
/-- **The qcqs lemma for quasi-coherent modules.** The sections of a quasi-coherent
`𝒪_X`-module over the basic open `X.basicOpen f` of a quasi-compact quasi-separated open `U` are
the localization of its sections over `U` at the powers of `f`. This is the module counterpart of
`AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`, and generalizes
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict` from affine opens. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs
    [M.IsQuasicoherent] (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X))
    (f : Γ(X, U)) : IsLocalizedModule.Away f (M.basicOpenRestrict f) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (M.isUnit_algebraMap_end_basicOpen f).pow n
  surj y := by
    obtain ⟨n, x, h⟩ := exists_pow_smul_eq_basicOpenRestrict M hU hU' f y
    exact ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨n, hn⟩ := M.exists_pow_smul_eq_zero_of_isCompact hU f (x₁ - x₂) (by
      rw [map_sub, h, sub_self])
    exact ⟨⟨_, n, rfl⟩, by simpa [Submonoid.smul_def, smul_sub, sub_eq_zero] using hn⟩

end

end TauCeti
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.AlgebraicGeometry.Modules.Localization"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits -/

/-! # Zero Units -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits.BundleCycles

noncomputable section

/-! A unit of degree zero is already a unit in the actual degree-zero ring. -/

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedZero_isUnit (a : 𝒜 0) (ha : IsUnit a.val) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  have hmul : a.val * (↑u⁻¹ : A) = 1 := by rw [← hu]; exact u.val_inv
  let b : 𝒜 0 := DirectSum.decompose 𝒜 (↑u⁻¹ : A) 0
  have hproj := congrArg (fun z : A => ((DirectSum.decompose 𝒜 z 0).val : A)) hmul
  have he : a.val * b.val = 1 := by
    rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 a.property,
      DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)] at hproj
    exact hproj
  exact IsUnit.of_mul_eq_one b (Subtype.ext he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator -/

/-! # Localization Numerator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator.BundleCycles

noncomputable section

/-! Homogeneous elements in a localization by degree-zero elements have
homogeneous numerators of the same degree, via the actual decomposition maps. -/

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A)
    (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hD hlocal in
theorem gradedLocalization_homogeneousNumerator (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ ∃ d : D, b * f d.val = f a := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  obtain ⟨⟨a, d⟩, ha⟩ := IsLocalization.surj D b
  change b * f d.val = f a at ha
  refine ⟨(DirectSum.decompose 𝒜 a n).val, (DirectSum.decompose 𝒜 a n).property, d, ?_⟩
  have hm : b * f d.val ∈ ℬ n := by
    exact (show b * f d.val ∈ ℬ (n + 0) from SetLike.mul_mem_graded hb (f.map_mem (hD d)))
  have hp := congrArg (fun x : B => ((DirectSum.decompose ℬ x n).val : B)) ha
  rw [← GradedRingHom.map_directSumDecompose] at hp
  have hsame : (DirectSum.decompose ℬ (b * f d.val) n).val = b * f d.val :=
    DirectSum.decompose_of_mem_same ℬ hm
  exact hsame.symm.trans hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase -/

/-! # Map Base -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase.BundleCycles

noncomputable section

/-! Native Proj maps commute with the actual degree-zero structure map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

section Rings

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem gradedAwayMap_fromZero (s : A) (a : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 (Submonoid.powers s) a) =
      fromZeroRingHom ℬ (Submonoid.powers (f s)) (f.gradedZeroRingHom a) := by
  change HomogeneousLocalization.map f _ (HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩) =
    HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom a, 1, by simp⟩
  rw [HomogeneousLocalization.map_mk]
  congr 1
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · rfl
  · exact map_one f

end Rings

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem projectiveMap_toSpecZero
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  let n : ℕ := s.1.val
  let a : A := s.2.val
  have hn : 0 < n := s.1.property
  have ha : a ∈ 𝒜 n := s.2.property
  change Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫ (Proj.map f hf ≫ Proj.toSpecZero 𝒜) =
    Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫
      (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
  have hmap := Proj.awayι_comp_map f hf hn a ha
  rw [← Category.assoc, hmap, Category.assoc, Proj.awayι_toSpecZero,
    ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext z
  exact congrArg HomogeneousLocalization.val (gradedAwayMap_fromZero f a z)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs -/

/-! # Away Is -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs.BundleCycles

noncomputable section

section

/-! The genuine degree-zero denominators on each homogeneous affine chart
become units after the corresponding coefficient localization. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)

def gradedZeroDenominatorHom : D →* 𝒜 0 where
  toFun d := ⟨d.val, hD d⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def gradedAwayDenominatorHom (s : A) : D →* Away 𝒜 s :=
  (fromZeroRingHom 𝒜 (Submonoid.powers s)).toMonoidHom.comp (gradedZeroDenominatorHom 𝒜 D hD)

def gradedAwayDenominators (s : A) : Submonoid (Away 𝒜 s) :=
  MonoidHom.mrange (gradedAwayDenominatorHom 𝒜 D hD s)

theorem gradedAwayDenominatorHom_apply (s : A) (d : D) :
    gradedAwayDenominatorHom 𝒜 D hD s d = fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨d.val, hD d⟩ := rfl

variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ℕ → τ) [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAwayDenominator_image_isUnit (s : A) (d : D) :
    IsUnit (Away.map f s (gradedAwayDenominatorHom 𝒜 D hD s d)) := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  rw [gradedAwayDenominatorHom_apply, Projective.MapBase.BundleCycles.gradedAwayMap_fromZero]
  have hu : IsUnit (f.gradedZeroRingHom ⟨d.val, hD d⟩) :=
    ZeroUnits.BundleCycles.gradedZero_isUnit ℬ _ (IsLocalization.map_units B d)
  exact hu.map (fromZeroRingHom ℬ (Submonoid.powers (f s)))

end

section

/-! Homogeneous affine-chart fractions admit common denominators from
the actual degree-zero coefficient localization. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedFromZero_val (s : A) (c : 𝒜 0) :
    (fromZeroRingHom 𝒜 (Submonoid.powers s) c).val = Localization.mk c.val 1 := rfl

theorem gradedAway_mk_mul_degreeZero {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • k)) (c : 𝒜 0) :
    Away.mk 𝒜 hs n a ha * fromZeroRingHom 𝒜 (Submonoid.powers s) c =
      Away.mk 𝒜 hs n (a * c.val)
        (show a * c.val ∈ 𝒜 (n • k + 0) from SetLike.mul_mem_graded ha c.property) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, gradedFromZero_val, Localization.mk_mul, Away.val_mk]
  simp only [mul_one]

variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ℕ → τ) [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_localized_fraction {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (z : Away ℬ (f s)) : ∃ x : Away 𝒜 s, ∃ d : D,
      z * Away.map f s (gradedAwayDenominatorHom 𝒜 D hD s d) = Away.map f s x := by
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, d, hd⟩ := LocalizationNumerator.BundleCycles.gradedLocalization_homogeneousNumerator f D hD hlocal (n • k) b hb
  refine ⟨Away.mk 𝒜 hs n a ha, d, ?_⟩
  rw [gradedAwayDenominatorHom_apply, Projective.MapBase.BundleCycles.gradedAwayMap_fromZero]
  refine (gradedAway_mk_mul_degreeZero ℬ (f.map_mem hs) n b hb
    (f.gradedZeroRingHom ⟨d.val, hD d⟩)).trans ?_
  rw [Away.map_mk]
  congr 1

end

section

/-! Equality on a localized homogeneous affine chart is detected after
multiplication by an actual degree-zero denominator. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_clear_equality {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (x y : Away 𝒜 s) (hxy : Away.map f s x = Away.map f s y) :
    ∃ d : D, gradedAwayDenominatorHom 𝒜 D hD s d * x =
      gradedAwayDenominatorHom 𝒜 D hD s d * y := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hs y
  rw [Away.map_mk, Away.map_mk] at hxy
  have he := congrArg HomogeneousLocalization.val hxy
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at he
  obtain ⟨⟨t, ht⟩, he⟩ := he
  obtain ⟨l, rfl⟩ := ht
  have hcoeff : f (s ^ l * (s ^ m * a)) = f (s ^ l * (s ^ n * b)) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow]
    exact he
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := D) hcoeff
  refine ⟨d, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_mul, gradedAwayDenominatorHom_apply, gradedFromZero_val,
    Away.val_mk, Away.val_mk, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨s ^ l, ⟨l, rfl⟩⟩, ?_⟩
  change s ^ l * ((1 * s ^ m) * (d.val * a)) = s ^ l * ((1 * s ^ n) * (d.val * b))
  calc
    _ = d.val * (s ^ l * (s ^ m * a)) := by ring
    _ = d.val * (s ^ l * (s ^ n * b)) := hd
    _ = _ := by ring

end

/-! Localizing a graded ring at degree-zero elements localizes each
actual homogeneous affine chart at the corresponding scalar denominators. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A) (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hlocal in
theorem gradedAway_isLocalization {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    letI := (Away.map f s).toAlgebra
    IsLocalization (gradedAwayDenominators 𝒜 D hD s) (Away ℬ (f s)) := by
  let := (Away.map f s).toAlgebra
  apply (isLocalization_iff (gradedAwayDenominators 𝒜 D hD s) (Away ℬ (f s))).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨d, hd⟩
    obtain ⟨a, rfl⟩ := hd
    exact gradedAwayDenominator_image_isUnit 𝒜 D hD ℬ f hlocal s a
  · intro z
    obtain ⟨x, d, hd⟩ := gradedAway_localized_fraction 𝒜 ℬ f D hD hlocal hs z
    exact ⟨⟨x, ⟨gradedAwayDenominatorHom 𝒜 D hD s d, ⟨d, rfl⟩⟩⟩, hd⟩
  · intro x y hxy
    obtain ⟨d, hd⟩ := gradedAway_clear_equality 𝒜 ℬ f D hD hlocal hs x y hxy
    exact ⟨⟨gradedAwayDenominatorHom 𝒜 D hD s d, ⟨d, rfl⟩⟩, hd⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs.BundleCycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayIs"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator -/

/-! # Away Principal Denominator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator.BundleCycles

noncomputable section

/-! A single degree-zero localization element gives the corresponding
single scalar denominator on every homogeneous affine chart. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (r : A) (hr : r ∈ 𝒜 0)

include hr in
theorem gradedPowersDegreeZero (d : Submonoid.powers r) : d.val ∈ 𝒜 0 := by
  obtain ⟨n, hn⟩ := d.property
  rw [← hn]
  exact (show r ^ n ∈ 𝒜 (n • 0) from SetLike.pow_mem_graded n hr)

theorem gradedAwayDenominators_powers (s : A) :
    AwayIs.BundleCycles.gradedAwayDenominators 𝒜 (Submonoid.powers r) (gradedPowersDegreeZero 𝒜 r hr) s =
      Submonoid.powers (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) := by
  let d₀ : Submonoid.powers r := ⟨r, ⟨1, pow_one r⟩⟩
  let φ := AwayIs.BundleCycles.gradedAwayDenominatorHom 𝒜 (Submonoid.powers r) (gradedPowersDegreeZero 𝒜 r hr) s
  have hφ : φ d₀ = fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩ := rfl
  ext a
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨n, hn⟩ := d.property
    have hd : d₀ ^ n = d := Subtype.ext hn
    refine ⟨n, ?_⟩
    change (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) ^ n = φ d
    rw [← hφ, ← map_pow, hd]
  · rintro ⟨n, rfl⟩
    refine ⟨d₀ ^ n, ?_⟩
    change φ (d₀ ^ n) = (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩) ^ n
    rw [map_pow, hφ]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator.BundleCycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.AwayPrincipalDenominator"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization -/

/-! # Principal Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization.BundleCycles

noncomputable section

/-! The actual Proj map associated to localization at one degree-zero
element is an open immersion. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

theorem projectiveLocalization_injective (D : Submonoid A)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B) :
    Function.Injective (Proj.map f hf) := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  intro p q hpq
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  let p' : PrimeSpectrum B := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  let q' : PrimeSpectrum B := ⟨q.asHomogeneousIdeal.toIdeal, q.isPrime⟩
  have he : PrimeSpectrum.comap (algebraMap A B) p' = PrimeSpectrum.comap (algebraMap A B) q' := by
    apply PrimeSpectrum.ext
    exact congrArg (fun z : Proj 𝒜 => z.asHomogeneousIdeal.toIdeal) hpq
  exact congrArg PrimeSpectrum.asIdeal (PrimeSpectrum.localization_comap_injective B D he)

theorem gradedAway_principal_isOpenImmersion (r : A) (hr : r ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B)
    (s : A) (k : ℕ) (hs : s ∈ 𝒜 k) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) := by
  let := (Away.map f s).toAlgebra
  have h := Graded.AwayIs.BundleCycles.gradedAway_isLocalization 𝒜 ℬ f (Submonoid.powers r)
    (Graded.AwayPrincipalDenominator.BundleCycles.gradedPowersDegreeZero 𝒜 r hr) hlocal hs
  rw [Graded.AwayPrincipalDenominator.BundleCycles.gradedAwayDenominators_powers] at h
  let := h
  exact IsOpenImmersion.of_isLocalization (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨r, hr⟩)

theorem projectivePrincipalLocalization_isOpenImmersion (r : A) (hr : r ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B) : IsOpenImmersion (Proj.map f hf) := by
  apply IsOpenImmersion.of_openCover_source (Proj.map f hf) (Proj.mapAffineOpenCover f hf).openCover
    (projectiveLocalization_injective 𝒜 ℬ f hf (Submonoid.powers r) hlocal)
  intro t
  let n : ℕ := t.1.val
  let a : A := t.2.val
  have hn : 0 < n := t.1.property
  have ha : a ∈ 𝒜 n := t.2.property
  have he := Proj.awayι_comp_map f hf hn a ha
  change IsOpenImmersion (Proj.awayι ℬ (f a) (f.map_mem ha) hn ≫ Proj.map f hf)
  rw [he]
  let := gradedAway_principal_isOpenImmersion 𝒜 ℬ f r hr hlocal a n ha
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization.BundleCycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalLocalization"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange -/

/-! # Localization Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange.BundleCycles

noncomputable section

/-! The image of the actual projective localization map is precisely
the nonvanishing open of its degree-zero denominator. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)

theorem gradedMap_irrelevant_le :
    (HomogeneousIdeal.irrelevant 𝒜).map f ≤ HomogeneousIdeal.irrelevant ℬ := by
  change Ideal.map f (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ (HomogeneousIdeal.irrelevant ℬ).toIdeal
  apply Ideal.map_le_iff_le_comap.mpr
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro n hn a ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hn (f.map_mem ha)

theorem projectivePrincipalLocalization_range
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (r : A) (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization.Away r B) :
    Set.range (Proj.map f hf) = Proj.basicOpen 𝒜 r := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change f r ∉ q.asHomogeneousIdeal.toIdeal
    have hu : IsUnit (f r) := IsLocalization.map_units B ⟨r, Submonoid.mem_powers r⟩
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · intro hp
    let p' : PrimeSpectrum A := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
    have hrange : p' ∈ Set.range (PrimeSpectrum.comap (algebraMap A B)) := by
      rw [PrimeSpectrum.localization_away_comap_range B r]
      exact hp
    obtain ⟨q, hq⟩ := hrange
    have hqI : q.asIdeal.comap f = p.asHomogeneousIdeal.toIdeal := congrArg PrimeSpectrum.asIdeal hq
    have hmap : (p.asHomogeneousIdeal.map f).toIdeal = q.asIdeal := by
      change Ideal.map f p.asHomogeneousIdeal.toIdeal = q.asIdeal
      rw [← hqI]
      exact IsLocalization.map_under (Submonoid.powers r) B q.asIdeal
    have hback : (p.asHomogeneousIdeal.map f).toIdeal.comap f = p.asHomogeneousIdeal.toIdeal :=
      (congrArg (Ideal.comap f) hmap).trans hqI
    let qP : Proj ℬ :=
      { asHomogeneousIdeal := p.asHomogeneousIdeal.map f
        isPrime := hmap.symm ▸ q.isPrime
        not_irrelevant_le := by
          intro h
          have hl := (gradedMap_irrelevant_le 𝒜 ℬ f).trans h
          have hc : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
              (p.asHomogeneousIdeal.map f).toIdeal.comap f := Ideal.map_le_iff_le_comap.mp hl
          rw [hback] at hc
          exact p.not_irrelevant_le hc }
    refine ⟨qP, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    exact hback

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange.BundleCycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.LocalizationRange"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading -/

/-! # Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading.BundleCycles

noncomputable section

/-! The actual symmetric algebra is internally graded by the powers of
its degree-one module. The decomposition is constructed by its universal property. -/

open scoped DirectSum

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

def symmetricGrading (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

instance symmetricGrading_gradedMonoid : SetLike.GradedMonoid (symmetricGrading R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

def symmetricGradedGenerator : M →ₗ[R] ⨁ n : ℕ, symmetricGrading R M n :=
  DirectSum.lof R ℕ (fun n => symmetricGrading R M n) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun m => by
      change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
      simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

theorem symmetricGradedGenerator_apply (m : M) :
    symmetricGradedGenerator R M m = DirectSum.of (fun n => symmetricGrading R M n) 1
      ⟨SymmetricAlgebra.ι R M m, by
        change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
        simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m⟩ := rfl

def symmetricDecompose : SymmetricAlgebra R M →ₐ[R] ⨁ n : ℕ, symmetricGrading R M n :=
  SymmetricAlgebra.lift (symmetricGradedGenerator R M)

theorem symmetricDecompose_homogeneous (n : ℕ) (x : symmetricGrading R M n) :
    symmetricDecompose R M x = DirectSum.of (fun n => symmetricGrading R M n) n x := by
  obtain ⟨x, hx⟩ := x
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  dsimp only [Subtype.coe_mk]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, DirectSum.algebraMap_apply]
    rfl
  | add x y n hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]
    rfl
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, ih]
    change SymmetricAlgebra.lift (symmetricGradedGenerator R M) (SymmetricAlgebra.ι R M a) * _ = _
    rw [SymmetricAlgebra.lift_ι_apply, symmetricGradedGenerator_apply, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

instance symmetricGradedAlgebra : GradedAlgebra (symmetricGrading R M) :=
  GradedAlgebra.ofAlgHom _ (symmetricDecompose R M)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext m
      change DirectSum.coeAlgHom (symmetricGrading R M)
        (SymmetricAlgebra.lift (symmetricGradedGenerator R M) (SymmetricAlgebra.ι R M m)) = _
      rw [SymmetricAlgebra.lift_ι_apply, symmetricGradedGenerator_apply, DirectSum.coeAlgHom_of]
      rfl)
    (symmetricDecompose_homogeneous R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading.BundleCycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Grading"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap -/

/-! # Graded Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap.BundleCycles

noncomputable section

/-! The symmetric-algebra universal map preserves the actual grading
whenever its linear generators have degree one. -/

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (f : M →ₗ[R] A) (hf : ∀ m, f m ∈ 𝒜 1)

include hf in
theorem symmetricLift_mem_grade (n : ℕ) (x : SymmetricAlgebra R M) (hx : x ∈ Grading.BundleCycles.symmetricGrading R M n) :
    SymmetricAlgebra.lift f x ∈ 𝒜 n := by
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact SetLike.algebraMap_mem_graded 𝒜 r
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact (𝒜 n).add_mem ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, SymmetricAlgebra.lift_ι_apply]
    simpa only [add_comm 1 n] using SetLike.mul_mem_graded (hf a) ih

def symmetricGradedLift : Grading.BundleCycles.symmetricGrading R M →+*ᵍ 𝒜 where
  __ := (SymmetricAlgebra.lift f).toRingHom
  map_mem {n} {x} hx := symmetricLift_mem_grade 𝒜 f hf n x hx

theorem symmetricGradedLift_generator (m : M) :
    symmetricGradedLift 𝒜 f hf (SymmetricAlgebra.ι R M m) = f m :=
  SymmetricAlgebra.lift_ι_apply f m

variable {N : Type*} [AddCommMonoid N] [Module R N]

def symmetricGradedMap (g : M →ₗ[R] N) : Grading.BundleCycles.symmetricGrading R M →+*ᵍ Grading.BundleCycles.symmetricGrading R N :=
  symmetricGradedLift (Grading.BundleCycles.symmetricGrading R N) ((SymmetricAlgebra.ι R N).comp g) (fun m => by
    change SymmetricAlgebra.ι R N (g m) ∈ LinearMap.range (SymmetricAlgebra.ι R N) ^ 1
    simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R N) (g m))

theorem symmetricGradedMap_generator (g : M →ₗ[R] N) (m : M) :
    symmetricGradedMap g (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (g m) :=
  symmetricGradedLift_generator _ _ _ m

theorem symmetricGradedMap_id : symmetricGradedMap (LinearMap.id : M →ₗ[R] M) = .id (Grading.BundleCycles.symmetricGrading R M) := by
  apply GradedRingHom.coe_ringHom_injective
  have h : SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp LinearMap.id) =
      AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp LinearMap.id)
      (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M m
    exact SymmetricAlgebra.lift_ι_apply _ m
  exact congrArg AlgHom.toRingHom h

theorem symmetricGradedMap_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    (symmetricGradedMap h).comp (symmetricGradedMap g) = symmetricGradedMap (h.comp g) := by
  apply GradedRingHom.coe_ringHom_injective
  have he : (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp h)).comp
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g)) =
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp (h.comp g)) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp h)
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g) (SymmetricAlgebra.ι R M m)) =
        SymmetricAlgebra.lift ((SymmetricAlgebra.ι R P).comp (h.comp g)) (SymmetricAlgebra.ι R M m)
    rw [SymmetricAlgebra.lift_ι_apply, SymmetricAlgebra.lift_ι_apply]
    exact SymmetricAlgebra.lift_ι_apply _ (g m)
  exact congrArg AlgHom.toRingHom he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap.BundleCycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradedMap"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradingIdeals -/

/-! # Grading Ideals -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradingIdeals.BundleCycles

noncomputable section

/-! The degree-zero ring of the actual symmetric algebra is the base
ring, and its irrelevant ideal is generated by the actual module elements. -/

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

def symmetricDegreeZero : R ≃+* Grading.BundleCycles.symmetricGrading R M 0 where
  toFun r := ⟨algebraMap R (SymmetricAlgebra R M) r, by
    change algebraMap R (SymmetricAlgebra R M) r ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 0
    rw [pow_zero]
    exact Submodule.algebraMap_mem r⟩
  invFun x := SymmetricAlgebra.algebraMapInv x.val
  left_inv r := SymmetricAlgebra.algebraMap_leftInverse M r
  right_inv x := by
    apply Subtype.ext
    have hx := x.property
    change x.val ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 0 at hx
    rw [pow_zero, Submodule.mem_one] at hx
    obtain ⟨r, hr⟩ := hx
    change algebraMap R (SymmetricAlgebra R M) (SymmetricAlgebra.algebraMapInv x.val) = x.val
    rw [← hr, SymmetricAlgebra.algebraMap_leftInverse M r]
  map_mul' r s := Subtype.ext (map_mul (algebraMap R (SymmetricAlgebra R M)) r s)
  map_add' r s := Subtype.ext (map_add (algebraMap R (SymmetricAlgebra R M)) r s)

theorem symmetricDegreeZero_coe (r : R) :
    (symmetricDegreeZero R M r : SymmetricAlgebra R M) = algebraMap R (SymmetricAlgebra R M) r := rfl

theorem symmetricPositive_mem_generatorIdeal (n : ℕ) (hn : 0 < n)
    (x : SymmetricAlgebra R M) (hx : x ∈ Grading.BundleCycles.symmetricGrading R M n) :
    x ∈ Ideal.span (Set.range (SymmetricAlgebra.ι R M)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ (k + 1) at hx
  rw [pow_succ] at hx
  have h : LinearMap.range (SymmetricAlgebra.ι R M) ^ k * LinearMap.range (SymmetricAlgebra.ι R M) ≤
      (Ideal.span (Set.range (SymmetricAlgebra.ι R M))).restrictScalars R := by
    apply Submodule.mul_le.mpr
    intro a ha b hb
    obtain ⟨m, rfl⟩ := hb
    exact Ideal.mul_mem_left _ a (Ideal.subset_span ⟨m, rfl⟩)
  exact h hx

theorem symmetricIrrelevant_eq_generatorIdeal :
    (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).toIdeal =
      Ideal.span (Set.range (SymmetricAlgebra.ι R M)) := by
  apply le_antisymm
  · apply (HomogeneousIdeal.toIdeal_irrelevant_le (Grading.BundleCycles.symmetricGrading R M)).mpr
    exact symmetricPositive_mem_generatorIdeal R M
  · apply Ideal.span_le.mpr
    rintro x ⟨m, rfl⟩
    apply HomogeneousIdeal.mem_irrelevant_of_mem (Grading.BundleCycles.symmetricGrading R M) (by decide : 0 < 1)
    change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
    simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradingIdeals.BundleCycles
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.GradingIdeals"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme -/

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme.BundleCycles

noncomputable section

/-! Actual projective spectra of symmetric algebras, with maps induced
by surjective module maps and isomorphisms induced by changes of frame. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

abbrev symmetricProjectiveScheme : Scheme.{u} := Proj (Symmetric.Grading.BundleCycles.symmetricGrading R M)

def symmetricProjectiveToBase : symmetricProjectiveScheme R M ⟶ Spec (.of R) :=
  Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)

variable {R M} {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem symmetricGradedMap_irrelevant (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) := by
  change (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N)).toIdeal ≤
    Ideal.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).toIdeal
  rw [Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal, Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨n, rfl⟩
  obtain ⟨m, rfl⟩ := hf n
  rw [← Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator f m]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, rfl⟩)

def symmetricProjectiveMap (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    symmetricProjectiveScheme R N ⟶ symmetricProjectiveScheme R M :=
  Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (symmetricGradedMap_irrelevant f hf)

theorem symmetricProjectiveMap_congr {f g : M →ₗ[R] N} (h : f = g)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    symmetricProjectiveMap f hf = symmetricProjectiveMap g hg := by
  subst g
  rfl

private theorem gradedProjectiveMap_congr
    {a b : Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ Symmetric.Grading.BundleCycles.symmetricGrading R N} (h : a = b)
    (ha : HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map a)
    (hb : HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≤
      (HomogeneousIdeal.irrelevant (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map b) : Proj.map a ha = Proj.map b hb := by
  subst b
  rfl

theorem symmetricProjectiveMap_id :
    symmetricProjectiveMap (LinearMap.id : M →ₗ[R] M) Function.surjective_id = 𝟙 (symmetricProjectiveScheme R M) := by
  exact (gradedProjectiveMap_congr Symmetric.GradedMap.BundleCycles.symmetricGradedMap_id _ (by simp)).trans Proj.map_id

theorem symmetricProjectiveMap_comp (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (g : N →ₗ[R] P) (hg : Function.Surjective g) :
    symmetricProjectiveMap (g.comp f) (hg.comp hf) =
      symmetricProjectiveMap g hg ≫ symmetricProjectiveMap f hf := by
  exact (gradedProjectiveMap_congr (Symmetric.GradedMap.BundleCycles.symmetricGradedMap_comp f g).symm _
    (HomogeneousIdeal.irrelevant_le_map_comp (symmetricGradedMap_irrelevant f hf)
      (symmetricGradedMap_irrelevant g hg))).trans
        (Proj.map_comp (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g)
          (symmetricGradedMap_irrelevant f hf) (symmetricGradedMap_irrelevant g hg))

def symmetricProjectiveIso (e : M ≃ₗ[R] N) :
    symmetricProjectiveScheme R M ≅ symmetricProjectiveScheme R N where
  hom := symmetricProjectiveMap e.symm.toLinearMap e.symm.surjective
  inv := symmetricProjectiveMap e.toLinearMap e.surjective
  hom_inv_id := by
    rw [← symmetricProjectiveMap_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext m; exact e.symm_apply_apply m
    exact (symmetricProjectiveMap_congr h _ Function.surjective_id).trans symmetricProjectiveMap_id
  inv_hom_id := by
    rw [← symmetricProjectiveMap_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext n; exact e.apply_symm_apply n
    exact (symmetricProjectiveMap_congr h _ Function.surjective_id).trans symmetricProjectiveMap_id

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme.BundleCycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension -/

/-! # Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual symmetric-algebra extension with its proved generator formula -/

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [CommSemiring A] [Algebra R A]

def symmetricExtension (f : M →ₗ[R] A) :
    {g : SymmetricAlgebra R M →+* A //
      (∀ m, g (SymmetricAlgebra.ι R M m) = f m) ∧
      ∀ r, g (algebraMap R (SymmetricAlgebra R M) r) = algebraMap R A r} :=
  ⟨(SymmetricAlgebra.lift f).toRingHom, SymmetricAlgebra.lift_ι_apply f, (SymmetricAlgebra.lift f).commutes⟩

theorem symmetricExtension_generator (f : M →ₗ[R] A) (m : M) :
    (symmetricExtension f).val (SymmetricAlgebra.ι R M m) = f m :=
  (symmetricExtension f).property.1 m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension.BundleCycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.Extension"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap -/

/-! # Scalar Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual symmetric-algebra maps under a change of coefficient ring -/

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]

abbrev symmetricScalarAlgebra (f : R →+* S) : Algebra R (SymmetricAlgebra S N) :=
  ((algebraMap S (SymmetricAlgebra S N)).comp f).toAlgebra

def symmetricScalarLinear (f : R →+* S) (g : M →ₛₗ[f] N) :
    letI := symmetricScalarAlgebra (N := N) f
    M →ₗ[R] SymmetricAlgebra S N := by
  let := symmetricScalarAlgebra (N := N) f
  exact {
    toFun := fun m => SymmetricAlgebra.ι S N (g m)
    map_add' := fun m n => by rw [map_add, map_add]
    map_smul' := fun r m => by
      rw [g.map_smulₛₗ, map_smul]
      change f r • SymmetricAlgebra.ι S N (g m) = r • SymmetricAlgebra.ι S N (g m)
      simp only [Algebra.smul_def]
      rfl
  }

def symmetricScalarMapData (f : R →+* S) (g : M →ₛₗ[f] N) :
    {h : SymmetricAlgebra R M →+* SymmetricAlgebra S N //
      (∀ m, h (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (g m)) ∧
      ∀ r, h (algebraMap R (SymmetricAlgebra R M) r) = algebraMap S (SymmetricAlgebra S N) (f r)} := by
  let e := @Extension.BundleCycles.symmetricExtension R M (SymmetricAlgebra S N) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) (symmetricScalarAlgebra f)
    (symmetricScalarLinear f g)
  exact ⟨e.val, e.property.1, e.property.2⟩

def symmetricScalarMap (f : R →+* S) (g : M →ₛₗ[f] N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  (symmetricScalarMapData f g).val

theorem symmetricScalarMap_generator (f : R →+* S) (g : M →ₛₗ[f] N) (m : M) :
    symmetricScalarMap f g (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (g m) :=
  (symmetricScalarMapData f g).property.1 m

theorem symmetricScalarMap_algebraMap (f : R →+* S) (g : M →ₛₗ[f] N) (r : R) :
    symmetricScalarMap f g (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (f r) :=
  (symmetricScalarMapData f g).property.2 r

theorem symmetricRingHom_ext {T : Type} [CommRing T]
    (f g : SymmetricAlgebra R M →+* T)
    (hc : ∀ r, f (algebraMap R (SymmetricAlgebra R M) r) = g (algebraMap R (SymmetricAlgebra R M) r))
    (hm : ∀ m, f (SymmetricAlgebra.ι R M m) = g (SymmetricAlgebra.ι R M m)) : f = g := by
  apply RingHom.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact hc r
  | ι m => exact hm m
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap.BundleCycles
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading -/

/-! # Scalar Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading.BundleCycles

noncomputable section

/-! The actual coefficient-change maps of symmetric algebras preserve
grading. A map whose module image spans gives an everywhere-defined Proj map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

theorem symmetricScalarMap_mem_grade (n : ℕ) (x : SymmetricAlgebra R M)
    (hx : x ∈ Grading.BundleCycles.symmetricGrading R M n) : ScalarMap.BundleCycles.symmetricScalarMap f g x ∈ Grading.BundleCycles.symmetricGrading S N n := by
  change x ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    exact SetLike.algebraMap_mem_graded (Grading.BundleCycles.symmetricGrading S N) (f r)
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact (Grading.BundleCycles.symmetricGrading S N n).add_mem ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, ScalarMap.BundleCycles.symmetricScalarMap_generator]
    have hg : SymmetricAlgebra.ι S N (g a) ∈ Grading.BundleCycles.symmetricGrading S N 1 := by
      change SymmetricAlgebra.ι S N (g a) ∈ LinearMap.range (SymmetricAlgebra.ι S N) ^ 1
      simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι S N) (g a)
    simpa only [add_comm 1 n] using SetLike.mul_mem_graded hg ih

def symmetricScalarGradedMap : Grading.BundleCycles.symmetricGrading R M →+*ᵍ Grading.BundleCycles.symmetricGrading S N where
  __ := ScalarMap.BundleCycles.symmetricScalarMap f g
  map_mem {n} {x} hx := symmetricScalarMap_mem_grade f g n x hx

theorem symmetricScalarGradedMap_irrelevant (hgen : Submodule.span S (Set.range g) = ⊤) :
    HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading S N) ≤
      (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).map (symmetricScalarGradedMap f g) := by
  let I := Ideal.map (ScalarMap.BundleCycles.symmetricScalarMap f g) (Ideal.span (Set.range (SymmetricAlgebra.ι R M)))
  have hN : ∀ n : N, SymmetricAlgebra.ι S N n ∈ I := by
    intro n
    have hn : n ∈ Submodule.span S (Set.range g) := by rw [hgen]; trivial
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [← ScalarMap.BundleCycles.symmetricScalarMap_generator f g m]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, rfl⟩)
    | zero => rw [map_zero]; exact I.zero_mem
    | add x y hx hy ihx ihy => rw [map_add]; exact I.add_mem ihx ihy
    | smul s n hn ih => rw [map_smul]; exact (I.restrictScalars S).smul_mem s ih
  change (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading S N)).toIdeal ≤
    Ideal.map (symmetricScalarGradedMap f g) (HomogeneousIdeal.irrelevant (Grading.BundleCycles.symmetricGrading R M)).toIdeal
  rw [GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal, GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact hN n

def symmetricScalarProjectiveMap (hgen : Submodule.span S (Set.range g) = ⊤) :
    SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme S N ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  Proj.map (symmetricScalarGradedMap f g) (symmetricScalarGradedMap_irrelevant f g hgen)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading.BundleCycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarGrading"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift -/

/-! # Localization Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual scalar maps into the localization of a symmetric algebra -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R)

def symmetricDenominators : Submonoid (SymmetricAlgebra R M) :=
  D.map (algebraMap R (SymmetricAlgebra R M))

abbrev LocalizedSymmetricAlgebra := Localization (symmetricDenominators M D)

abbrev localizedSymmetricBaseAlgebra : Algebra R (LocalizedSymmetricAlgebra M D) :=
  inferInstance

attribute [local instance] localizedSymmetricBaseAlgebra

instance localizedSymmetricBase_tower : IsScalarTower R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) :=
  inferInstance

theorem localizedSymmetricScalar_units (d : D) :
    IsUnit (algebraMap R (LocalizedSymmetricAlgebra M D) d.val) := by
  let d' : symmetricDenominators M D :=
    ⟨algebraMap R (SymmetricAlgebra R M) d.val, Submonoid.mem_map_of_mem _ d.property⟩
  rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D)]
  exact IsLocalization.map_units (LocalizedSymmetricAlgebra M D) d'

variable (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]

def localizedSymmetricScalarMap : S →+* LocalizedSymmetricAlgebra M D :=
  IsLocalization.lift (localizedSymmetricScalar_units M D)

theorem localizedSymmetricScalarMap_algebraMap (r : R) :
    localizedSymmetricScalarMap M D S (algebraMap R S r) =
      algebraMap R (LocalizedSymmetricAlgebra M D) r :=
  IsLocalization.lift_eq (localizedSymmetricScalar_units M D) r

abbrev localizedSymmetricAlgebra : Algebra S (LocalizedSymmetricAlgebra M D) :=
  (localizedSymmetricScalarMap M D S).toAlgebra

attribute [local instance] localizedSymmetricAlgebra

instance localizedSymmetricScalar_tower : IsScalarTower R S (LocalizedSymmetricAlgebra M D) :=
  IsScalarTower.of_algebraMap_eq fun r => (localizedSymmetricScalarMap_algebraMap M D S r).symm

def localizedSymmetricGenerator : M →ₗ[R] LocalizedSymmetricAlgebra M D :=
  (IsScalarTower.toAlgHom R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D)).toLinearMap.comp
    (SymmetricAlgebra.ι R M)

theorem localizedSymmetricGenerator_units (d : D) :
    IsUnit (algebraMap R (Module.End R (LocalizedSymmetricAlgebra M D)) d.val) := by
  apply (Module.End.isUnit_iff _).mpr
  have h : Function.Bijective (fun x : LocalizedSymmetricAlgebra M D =>
      algebraMap R (LocalizedSymmetricAlgebra M D) d.val • x) :=
    (localizedSymmetricScalar_units M D d).smul_bijective
  change Function.Bijective (fun x : LocalizedSymmetricAlgebra M D => d.val • x)
  have he : (fun x : LocalizedSymmetricAlgebra M D =>
      algebraMap R (LocalizedSymmetricAlgebra M D) d.val • x) = (fun x => d.val • x) := by
    funext x
    change algebraMap R (LocalizedSymmetricAlgebra M D) d.val * x = d.val • x
    exact (Algebra.smul_def d.val x).symm
  exact he ▸ h

end

/-! # LineBundleCycles: the actual inverse map from the symmetric algebra of a localized module -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R) (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]
    {N : Type} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

attribute [local instance] localizedSymmetricBaseAlgebra localizedSymmetricAlgebra

def symmetricLocalizationLiftLinear : N →ₗ[S] LocalizedSymmetricAlgebra M D :=
  (IsLocalizedModule.lift D f (localizedSymmetricGenerator M D)
    (localizedSymmetricGenerator_units M D)).extendScalarsOfIsLocalization D S

theorem symmetricLocalizationLiftLinear_apply (m : M) :
    symmetricLocalizationLiftLinear M D S f (f m) =
      algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m) :=
  IsLocalizedModule.lift_apply D f (localizedSymmetricGenerator M D)
    (localizedSymmetricGenerator_units M D) m

def symmetricLocalizationLiftData :
    {g : SymmetricAlgebra S N →+* LocalizedSymmetricAlgebra M D //
      (∀ m, g (SymmetricAlgebra.ι S N (f m)) =
        algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m)) ∧
      ∀ s, g (algebraMap S (SymmetricAlgebra S N) s) = localizedSymmetricScalarMap M D S s} := by
  let e := @Extension.BundleCycles.symmetricExtension S N (LocalizedSymmetricAlgebra M D) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) (localizedSymmetricAlgebra M D S)
    (symmetricLocalizationLiftLinear M D S f)
  refine ⟨e.val, ?_, e.property.2⟩
  intro m
  exact (e.property.1 (f m)).trans (symmetricLocalizationLiftLinear_apply M D S f m)

def symmetricLocalizationLift : SymmetricAlgebra S N →+* LocalizedSymmetricAlgebra M D :=
  (symmetricLocalizationLiftData M D S f).val

theorem symmetricLocalizationLift_generator (m : M) :
    symmetricLocalizationLift M D S f (SymmetricAlgebra.ι S N (f m)) =
      algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m) :=
  (symmetricLocalizationLiftData M D S f).property.1 m

theorem symmetricLocalizationLift_algebraMap (s : S) :
    symmetricLocalizationLift M D S f (algebraMap S (SymmetricAlgebra S N) s) =
      localizedSymmetricScalarMap M D S s :=
  (symmetricLocalizationLiftData M D S f).property.2 s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift.BundleCycles
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap -/

/-! # Localization Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual map from localized symmetric polynomials to localized-module polynomials -/

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]

def scalarExtensionSemilinear (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r m := by rw [f.map_smul, algebraMap_smul]

def symmetricModuleMap (f : M →ₗ[R] N) : SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  ScalarMap.BundleCycles.symmetricScalarMap (algebraMap R S) (scalarExtensionSemilinear f)

theorem symmetricModuleMap_generator (f : M →ₗ[R] N) (m : M) :
    symmetricModuleMap (S := S) f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (f m) :=
  ScalarMap.BundleCycles.symmetricScalarMap_generator _ _ _

theorem symmetricModuleMap_algebraMap (f : M →ₗ[R] N) (r : R) :
    symmetricModuleMap (S := S) f (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (algebraMap R S r) :=
  ScalarMap.BundleCycles.symmetricScalarMap_algebraMap _ _ _

variable (D : Submonoid R) [IsLocalization D S] (f : M →ₗ[R] N)

theorem symmetricModuleMap_units (d : LocalizationLift.BundleCycles.symmetricDenominators M D) :
    IsUnit (symmetricModuleMap (S := S) f d.val) := by
  obtain ⟨r, hr, he⟩ := d.property
  change algebraMap R (SymmetricAlgebra R M) r = d.val at he
  rw [← he, symmetricModuleMap_algebraMap]
  exact (IsLocalization.map_units S (⟨r, hr⟩ : D)).map (algebraMap S (SymmetricAlgebra S N))

def symmetricLocalizationMap : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D →+* SymmetricAlgebra S N :=
  IsLocalization.lift (symmetricModuleMap_units D f)

theorem symmetricLocalizationMap_algebraMap (a : SymmetricAlgebra R M) :
    symmetricLocalizationMap (S := S) D f (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) a) =
      symmetricModuleMap (S := S) f a :=
  IsLocalization.lift_eq (symmetricModuleMap_units D f) a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap.BundleCycles
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization -/

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization.BundleCycles

noncomputable section

/-! Localizing a module gives the native projective-spectrum restriction
map, because its actual image spans the localized module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (D : Submonoid R) [IsLocalization D S]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

include D in
theorem localizedModule_span_range : Submodule.span S (Set.range (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear (S := S) f)) = ⊤ := by
  have h := span_eq_top_of_isLocalizedModule S D f (v := Set.univ) (by simp : Submodule.span R (Set.univ : Set M) = ⊤)
  rw [Set.image_univ] at h
  exact h

def localizedSymmetricProjectiveMap : Scheme.BundleCycles.symmetricProjectiveScheme S N ⟶ Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f) (localizedModule_span_range D f)

theorem localizedSymmetricProjectiveMap_preimage (x : SymmetricAlgebra R M) :
    localizedSymmetricProjectiveMap D f ⁻¹ᵁ Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) x =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading S N) (Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f x) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization.BundleCycles
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Localization"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base -/

/-! # Base -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base.BundleCycles

noncomputable section

section

/-! Projectivized coefficient changes commute with the actual maps to
the spectra of the coefficient rings. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (f : R →+* S) (g : M →ₛₗ[f] N)

theorem symmetricScalarDegreeZero_square :
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f g).gradedZeroRingHom.comp (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom =
      (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero S N).toRingHom.comp f := by
  ext r
  exact Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap f g r

theorem symmetricScalarProjectiveMap_over (hgen : Submodule.span S (Set.range g) = ⊤) :
    Symmetric.ScalarGrading.BundleCycles.symmetricScalarProjectiveMap f g hgen ≫ Scheme.BundleCycles.symmetricProjectiveToBase R M =
      Scheme.BundleCycles.symmetricProjectiveToBase S N ≫ Spec.map (CommRingCat.ofHom f) := by
  change Proj.map (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap f g) _ ≫
      (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)) =
    (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading S N) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero S N).toRingHom)) ≫ _
  rw [← Category.assoc, Projective.MapBase.BundleCycles.projectiveMap_toSpecZero, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun h : R →+* Symmetric.Grading.BundleCycles.symmetricGrading S N 0 => Spec.map (CommRingCat.ofHom h))
    (symmetricScalarDegreeZero_square f g)

end

/-! Projectivized surjective module maps preserve the actual base projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)

theorem symmetricProjectiveMap_over :
    Scheme.BundleCycles.symmetricProjectiveMap g hg ≫ Scheme.BundleCycles.symmetricProjectiveToBase R M = Scheme.BundleCycles.symmetricProjectiveToBase R N := by
  have hz : (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g).gradedZeroRingHom.comp (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom =
      (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R N).toRingHom := by
    ext r
    exact (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp g)).commutes r
  change Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap g) _ ≫
    (Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R M) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom)) =
    Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≫ Spec.map (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R N).toRingHom)
  rw [← Category.assoc, Projective.MapBase.BundleCycles.projectiveMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  exact congrArg (fun h : R →+* Symmetric.Grading.BundleCycles.symmetricGrading R N 0 =>
    Proj.toSpecZero (Symmetric.Grading.BundleCycles.symmetricGrading R N) ≫ Spec.map (CommRingCat.ofHom h)) hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base.BundleCycles
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Base"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt -/

/-! # Localized Symmetric Ext -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual localized module generators determine symmetric-algebra maps -/

variable {R S M N T : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
    (D : Submonoid R) [IsLocalization D S] (f : M →ₗ[R] N) [IsLocalizedModule D f]

include D in
theorem localizedSymmetricRingHom_ext (g h : SymmetricAlgebra S N →+* T)
    (hc : ∀ s, g (algebraMap S (SymmetricAlgebra S N) s) = h (algebraMap S (SymmetricAlgebra S N) s))
    (hm : ∀ m, g (SymmetricAlgebra.ι S N (f m)) = h (SymmetricAlgebra.ι S N (f m))) : g = h := by
  refine Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext g h hc ?_
  intro n
  obtain ⟨⟨m, d⟩, hn⟩ := IsLocalizedModule.surj D f n
  have he : algebraMap S (SymmetricAlgebra S N) (algebraMap R S d.val) * SymmetricAlgebra.ι S N n =
      SymmetricAlgebra.ι S N (f m) := by
    rw [← Algebra.smul_def, ← map_smul, algebraMap_smul]
    exact congrArg (SymmetricAlgebra.ι S N) hn
  have hu := ((IsLocalization.map_units S d).map (algebraMap S (SymmetricAlgebra S N))).map g
  apply hu.mul_right_inj.mp
  rw [← map_mul g, he, hc (algebraMap R S d.val), ← map_mul h, he]
  exact hm m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt.BundleCycles
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv -/

/-! # Localization Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual symmetric-algebra localization isomorphism -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R) (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]
    {N : Type} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

attribute [local instance] LocalizationLift.BundleCycles.localizedSymmetricBaseAlgebra

omit [IsLocalizedModule D f] in
theorem symmetricLocalizationMap_scalar (s : S) :
    LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S s) =
      algebraMap S (SymmetricAlgebra S N) s := by
  have h : (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f).comp (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S) =
      algebraMap S (SymmetricAlgebra S N) := by
    apply IsLocalization.ringHom_ext D
    apply RingHom.ext
    intro r
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S (algebraMap R S r)) = _
    rw [LocalizationLift.BundleCycles.localizedSymmetricScalarMap_algebraMap,
      IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D),
      LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_algebraMap]
    rfl
  exact DFunLike.congr_fun h s

theorem symmetricLocalizationLift_comp_map :
    (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f).comp (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f) =
      RingHom.id (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) := by
  apply IsLocalization.ringHom_ext (LocalizationLift.BundleCycles.symmetricDenominators M D)
  refine ScalarMap.BundleCycles.symmetricRingHom_ext (R := R) (M := M) (T := LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) _ _ ?_ ?_
  · intro r
    change LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f
      (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) (algebraMap R (SymmetricAlgebra R M) r))) = _
    rw [LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_algebraMap,
      LocalizationLift.BundleCycles.symmetricLocalizationLift_algebraMap, LocalizationLift.BundleCycles.localizedSymmetricScalarMap_algebraMap]
    exact IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) r
  · intro m
    change LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f
      (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m))) = _
    rw [LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_generator,
      LocalizationLift.BundleCycles.symmetricLocalizationLift_generator]
    rfl

theorem symmetricLocalizationMap_comp_lift :
    (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f).comp (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f) =
      RingHom.id (SymmetricAlgebra S N) := by
  apply LocalizedSymmetricExt.BundleCycles.localizedSymmetricRingHom_ext D f
  · intro s
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f
      (algebraMap S (SymmetricAlgebra S N) s)) = _
    rw [LocalizationLift.BundleCycles.symmetricLocalizationLift_algebraMap, symmetricLocalizationMap_scalar]
    rfl
  · intro m
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f
      (SymmetricAlgebra.ι S N (f m))) = _
    rw [LocalizationLift.BundleCycles.symmetricLocalizationLift_generator, LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap,
      LocalizationMap.BundleCycles.symmetricModuleMap_generator]
    rfl

def symmetricLocalizationEquiv : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D ≃+* SymmetricAlgebra S N :=
  RingEquiv.ofRingHom (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f) (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f)
    (symmetricLocalizationMap_comp_lift M D S f) (symmetricLocalizationLift_comp_map M D S f)

theorem symmetricModuleMap_isLocalization :
    letI := (LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
    IsLocalization (LocalizationLift.BundleCycles.symmetricDenominators M D) (SymmetricAlgebra S N) := by
  let := (LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
  let e : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D ≃ₐ[SymmetricAlgebra R M] SymmetricAlgebra S N := {
    symmetricLocalizationEquiv M D S f with
    commutes' := LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap D f
  }
  exact IsLocalization.isLocalization_of_algEquiv (LocalizationLift.BundleCycles.symmetricDenominators M D) e

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv.BundleCycles
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen -/

/-! # Principal Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen.BundleCycles

noncomputable section

/-! Actual principal coefficient localization gives an open immersion
between the projective spectra of the module's symmetric algebras. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N]
    [IsScalarTower R S N] (r : R) [IsLocalization.Away r S]
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricModuleMap_principalLocalization :
    letI := (Symmetric.LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
    IsLocalization.Away (algebraMap R (SymmetricAlgebra R M) r) (SymmetricAlgebra S N) := by
  have h := Symmetric.LocalizationEquiv.BundleCycles.symmetricModuleMap_isLocalization M (Submonoid.powers r) S f
  simpa only [Symmetric.LocalizationLift.BundleCycles.symmetricDenominators, Submonoid.map_powers] using h

theorem localizedSymmetricProjectiveMap_isOpenImmersion :
    IsOpenImmersion (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f) := by
  apply Projective.PrincipalLocalization.BundleCycles.projectivePrincipalLocalization_isOpenImmersion (Symmetric.Grading.BundleCycles.symmetricGrading R M) (Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f))
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f))
    (algebraMap R (SymmetricAlgebra R M) r) (SetLike.algebraMap_mem_graded (Symmetric.Grading.BundleCycles.symmetricGrading R M) r)
  exact symmetricModuleMap_principalLocalization (S := S) r f

theorem localizedSymmetricProjectiveMap_range :
    Set.range (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f) =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) (algebraMap R (SymmetricAlgebra R M) r) :=
  Projective.LocalizationRange.BundleCycles.projectivePrincipalLocalization_range (Symmetric.Grading.BundleCycles.symmetricGrading R M) (Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f))
    (Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _ (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f))
    (algebraMap R (SymmetricAlgebra R M) r) (symmetricModuleMap_principalLocalization (S := S) r f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen.BundleCycles
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.PrincipalOpen"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen -/

/-! # Scalar Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen.BundleCycles

noncomputable section

/-! The actual Proj structure map contracts a homogeneous prime to its
degree-zero part. This identifies scalar nonvanishing opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem projectiveBasicOpenToSpec_native (s : A) :
    (Proj.basicOpenToSpec 𝒜 s).toLRSHom = ProjectiveSpectrum.Proj.toSpec 𝒜 s := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

theorem projectiveBasicOpenToSpec_mem (s : A) (p : (Proj.basicOpen 𝒜 s).toScheme)
    (z : NumDenSameDeg 𝒜 (Submonoid.powers s)) :
    HomogeneousLocalization.mk z ∈ (Proj.basicOpenToSpec 𝒜 s p).asIdeal ↔ z.num.val ∈ p.val.asHomogeneousIdeal := by
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 p z
  have he := congrArg (fun j => j.base p) (projectiveBasicOpenToSpec_native 𝒜 s)
  exact (congrArg (fun q : PrimeSpectrum (Away 𝒜 s) => HomogeneousLocalization.mk z ∈ q.asIdeal) he).to_iff.trans h

theorem projectiveToSpecZero_mem (p : Proj 𝒜) (a : 𝒜 0) :
    a ∈ (Proj.toSpecZero 𝒜 p).asIdeal ↔ a.val ∈ p.asHomogeneousIdeal := by
  let t : Proj 𝒜 ⟶ (Proj.basicOpen 𝒜 1).toScheme :=
    (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv
  have ht : t ≫ (Proj.basicOpen 𝒜 1).ι = 𝟙 (Proj 𝒜) := by
    change ((Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ (Proj.basicOpen_one 𝒜)).inv) ≫ _ = _
    rw [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  let q : (Proj.basicOpen 𝒜 1).toScheme := t p
  have hq : q.val = p := congrArg (fun j : Proj 𝒜 ⟶ Proj 𝒜 => j p) ht
  change HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩ ∈
    (Proj.basicOpenToSpec 𝒜 1 q).asIdeal ↔ a.val ∈ p.asHomogeneousIdeal
  exact (projectiveBasicOpenToSpec_mem 𝒜 1 q _).trans
    (congrArg (fun z : Proj 𝒜 => a.val ∈ z.asHomogeneousIdeal) hq).to_iff

theorem projectiveToSpecZero_preimage (a : 𝒜 0) :
    Proj.toSpecZero 𝒜 ⁻¹ᵁ (PrimeSpectrum.basicOpen a : (Spec (.of (𝒜 0))).Opens) =
      Proj.basicOpen 𝒜 a.val := by
  ext p
  exact not_congr (projectiveToSpecZero_mem 𝒜 p a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen.BundleCycles
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ScalarOpen"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback -/

/-! # Projective Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback.BundleCycles

noncomputable section

/-! The actual projective symmetric construction has the expected
principal-open pullback over the coefficient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricProjectiveToBase_preimage_basicOpen (r : R) :
    Scheme.BundleCycles.symmetricProjectiveToBase R M ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens) =
      Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M) (algebraMap R (SymmetricAlgebra R M) r) := by
  ext p
  exact not_congr (Projective.ScalarOpen.BundleCycles.projectiveToSpecZero_mem (Symmetric.Grading.BundleCycles.symmetricGrading R M) p (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M r))

variable {R M} {S N : Type} [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (r : R) [IsLocalization.Away r S] (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f]

theorem symmetricProjective_principal_isPullback :
    IsPullback (Scheme.BundleCycles.symmetricProjectiveToBase S N)
      (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Scheme.BundleCycles.symmetricProjectiveToBase R M) := by
  let := PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_isOpenImmersion (S := S) r f
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := IsOpenImmersion.of_isLocalization r
  apply IsOpenImmersion.isPullback
  · exact Base.BundleCycles.symmetricScalarProjectiveMap_over (algebraMap R S) (Symmetric.LocalizationMap.BundleCycles.scalarExtensionSemilinear f)
      (Localization.BundleCycles.localizedModule_span_range (S := S) (Submonoid.powers r) f)
  · have hS : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := PrimeSpectrum.localization_away_comap_range S r
    have hP := PrincipalOpen.BundleCycles.localizedSymmetricProjectiveMap_range (S := S) r f
    ext p
    change Scheme.BundleCycles.symmetricProjectiveToBase R M p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      p ∈ Set.range (Localization.BundleCycles.localizedSymmetricProjectiveMap (S := S) (Submonoid.powers r) f)
    rw [hS, hP]
    exact SetLike.ext_iff.mp (symmetricProjectiveToBase_preimage_basicOpen R M r) p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback.BundleCycles
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ProjectivePullback"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr -/

/-! # Map Congr -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles

noncomputable section

/-! Equality of actual graded homomorphisms identifies their Proj maps. -/

open _root_.AlgebraicGeometry

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem projectiveMap_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr"

section ComponentSource_28
/- Original module: PaperVerification.ProjectivizationOfModuleSheaf -/


/-!
# The actual projectivization of a quasicoherent module sheaf

On an affine open `U`, take `Proj Sym_{Γ(U)} Γ(M,U)`. Restriction to a
principal affine open is an actual localization of the module of sections.
The corresponding projective spectra form cartesian squares, so relative
scheme gluing constructs their global projectivization over the original
scheme. No projectivization or local comparison is postulated.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ProjectivizationOfModuleSheaf

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite
open OAI.AlgebraicGeometry.Divisors.LineBundles

variable {X : _root_.AlgebraicGeometry.Scheme.{0}} (M : X.Modules) [M.IsQuasicoherent]

/-- The actual projective symmetric scheme of the module of sections. -/
abbrev chart (U : X.AffineZariskiSite) : _root_.AlgebraicGeometry.Scheme :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme Γ(X, U.val) Γ(M, U.val)

/-- Restriction of a module section, with its actual semilinear scalar map. -/
def restriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Γ(M, V.val) →ₛₗ[(X.presheaf.map (homOfLE (toOpens_mono i.le)).op).hom]
      Γ(M, U.val) where
  toFun := M.presheaf.map (homOfLE (toOpens_mono i.le)).op
  map_add' := map_add _
  map_smul' a m := M.map_smul _ a m

/-- Quasicoherent restriction generates all sections after scalar extension. -/
theorem restriction_span {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    Submodule.span Γ(X, U.val) (Set.range (restriction M i)) = ⊤ := by
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  letI : IsLocalization.Away r Γ(X, X.basicOpen r) := V.property.isLocalization_basicOpen r
  letI := _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict M V.property r
  exact SymmetricProjective.Localization.BundleCycles.localizedModule_span_range
    (S := Γ(X, X.basicOpen r)) (Submonoid.powers r) (M.basicOpenRestrict r)

/-- The degree-preserving map of the actual symmetric algebras. -/
def gradedRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap
    (X.presheaf.map (homOfLE (toOpens_mono i.le)).op).hom (restriction M i)

theorem gradedRestriction_irrelevant {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, U.val) Γ(M, U.val)) ≤
      (HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, V.val) Γ(M, V.val))).map
          (gradedRestriction M i) :=
  Symmetric.ScalarGrading.BundleCycles.symmetricScalarGradedMap_irrelevant _ _
    (restriction_span M i)

/-- The induced morphism between actual projective affine-base charts. -/
def chartMap {U V : X.AffineZariskiSite} (i : U ⟶ V) : chart M U ⟶ chart M V :=
  Proj.map (gradedRestriction M i) (gradedRestriction_irrelevant M i)

theorem gradedRestriction_id (U : X.AffineZariskiSite) :
    gradedRestriction M (𝟙 U) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
      (algebraMap _ _ a) = algebraMap _ _ a
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ X.presheaf).map_id (.op U)) a
  · intro m
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
      (SymmetricAlgebra.ι _ _ m) = SymmetricAlgebra.ι _ _ m
    rw [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ M.presheaf).map_id (.op U)) m

theorem gradedRestriction_comp {U V W : X.AffineZariskiSite}
    (f : U ⟶ V) (g : V ⟶ W) :
    gradedRestriction M (f ≫ g) = (gradedRestriction M f).comp (gradedRestriction M g) := by
  apply GradedRingHom.coe_ringHom_injective
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro a
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (algebraMap _ _ a) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
        (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (algebraMap _ _ a))
    simp only [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_algebraMap]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ X.presheaf).map_comp g.op f.op) a
  · intro m
    change Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (SymmetricAlgebra.ι _ _ m) =
      Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _
        (Symmetric.ScalarMap.BundleCycles.symmetricScalarMap _ _ (SymmetricAlgebra.ι _ _ m))
    simp only [Symmetric.ScalarMap.BundleCycles.symmetricScalarMap_generator]
    congr 1
    exact ConcreteCategory.congr_hom
      (((toOpensFunctor X).op ⋙ M.presheaf).map_comp g.op f.op) m

/-- The actual projective charts and restriction morphisms form a functor. -/
def diagram : X.AffineZariskiSite ⥤ _root_.AlgebraicGeometry.Scheme where
  obj U := chart M U
  map i := chartMap M i
  map_id U :=
    (_root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles.projectiveMap_congr (gradedRestriction_id M U) _
      (by simp)).trans Proj.map_id
  map_comp f g :=
    (_root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr.BundleCycles.projectiveMap_congr (gradedRestriction_comp M f g) _
      (HomogeneousIdeal.irrelevant_le_map_comp (gradedRestriction_irrelevant M g)
        (gradedRestriction_irrelevant M f))).trans
      (Proj.map_comp (gradedRestriction M g) (gradedRestriction M f)
        (gradedRestriction_irrelevant M g) (gradedRestriction_irrelevant M f))

/-- The projection to the actual spectra of the base section rings. -/
def toCoefficients : diagram M ⟶
    toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ _root_.AlgebraicGeometry.Scheme.Spec where
  app U := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase Γ(X, U.val) Γ(M, U.val)
  naturality {_U _V} i :=
    SymmetricProjective.Base.BundleCycles.symmetricScalarProjectiveMap_over _ _
      (restriction_span M i)

/-- Principal localization gives the required genuine cartesian squares. -/
theorem toCoefficients_equifibered : (toCoefficients M).Equifibered := by
  intro U V i
  obtain ⟨r, hr⟩ := i.le
  have hU : V.basicOpen r = U := Subtype.ext hr
  subst U
  letI : IsLocalization.Away r Γ(X, X.basicOpen r) := V.property.isLocalization_basicOpen r
  letI := _root_.AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict M V.property r
  exact (SymmetricProjective.ProjectivePullback.BundleCycles.symmetricProjective_principal_isPullback
    (S := Γ(X, X.basicOpen r)) r (M.basicOpenRestrict r)).flip

/-- Relative scheme gluing data over the actual affine Zariski cover. -/
def glueData : (directedCover X).RelativeGluingData where
  functor := diagram M
  natTrans := toCoefficients M ≫ (restrictIsoSpec X).inv
  equifibered :=
    (toCoefficients_equifibered M).comp
      (NatTrans.Equifibered.of_isIso (restrictIsoSpec X).inv)

instance glueData_isLocallyDirected :
    ((glueData M).functor ⋙ _root_.AlgebraicGeometry.Scheme.forget).IsLocallyDirected :=
  _root_.AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The projectivization of the original quasicoherent sheaf. -/
def projectivization : _root_.AlgebraicGeometry.Scheme := (glueData M).glued

/-- Its actual morphism to the original base scheme. -/
def projection : projectivization M ⟶ X := (glueData M).toBase

/-- The projective affine-base charts form an actual open cover. -/
def openCover : (projectivization M).OpenCover := (glueData M).cover

/-- Each chart is exactly the pullback of the global projectivization to
the original affine open of the base. -/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((glueData M).natTrans.app U) ((openCover M).f U) U.val.ι (projection M) :=
  (glueData M).isPullback_natTrans_ι_toBase U

end PaperVerification.ProjectivizationOfModuleSheaf
end
end
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectivizationOfModuleSheaf"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.ProjectivizationOfModuleSheaf.restriction_span, "theorem"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.gradedRestriction_id, "theorem"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.gradedRestriction_comp, "theorem"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.diagram, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.toCoefficients, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.toCoefficients_equifibered, "theorem"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.glueData, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.projectivization, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.projection, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.openCover, "definition"),
    (`PaperVerification.ProjectivizationOfModuleSheaf.chart_isPullback, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "aa17481249c68e4069d33f904ffbc897"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:aa17481249c68e4069d33f904ffbc897"
