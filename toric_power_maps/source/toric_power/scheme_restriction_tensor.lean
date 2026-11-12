module

public import ToricPower.CoherentFoundations

/-!
# Tensor products and actual restriction to an open subscheme

The canonical tensor comparison for restriction along an open immersion is
an isomorphism for arbitrary module sheaves. The proof computes the tensor
compatibility of the actual restriction adjunction on sections, then applies
the already proved doctrinal-adjunction identities. The corresponding
oplax tensor comparison for actual pullback is invertible as well.

The proof bodies below are recovered from TauCeti commit
6b896c7c411221eb78639e4be8ead6e479a62893, with only the import graph adapted.
No statement about arbitrary-scheme pullback or tensor preservation is assumed.
The original source files and selection manifest are retained in
`third_party/restriction_tensor_sources`.
-/

/-! ## Recovered genuine proof body: `TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Adjunction`
Original SHA256: 285961e8e035386df12c2146582706bd9a73d4e6bbf4faa2ea503b1dc364e5bb.
-/
section RestrictionTensorSource0


/-!
# Pushforward along a left adjoint of sites is strong monoidal

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, both continuous, and let `φ` and `ψ` be
compatible morphisms of sheaves of rings along `F` and `G`. Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` makes the pushforward of sheaves of modules along `φ`
left adjoint to the pushforward along `ψ`. For the inclusion of an open subset `U` of a
topological space, `F` is the inclusion of the opens of `U` into the opens of the space and the
pushforward along `φ` is restriction to `U`.

Both pushforwards carry their canonical lax monoidal structures
(`TauCeti.SheafOfModules.pushforwardLaxMonoidal`), whose tensor maps send `m ⊗ n` to `m ⊗ n` on
sections. This file shows that the unit and the counit of the adjunction are compatible with
these tensor maps (`SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor` and
`SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor`); on sections both are restriction
maps. By doctrinal adjunction (`CategoryTheory.Adjunction.isIso_μ_of_unit_of_counit`) the tensor
map of the left adjoint is then invertible: pushforward along `φ` commutes with tensor products
(`SheafOfModules.isIso_pushforward_μ_of_adjunction`). The inverse is the mate of the tensor map
of the right adjoint, which is the tensor comparison of the left adjoint as an oplax monoidal
functor. This identification of the canonical tensor map, rather than the construction of some
isomorphism `φ_* (M ⊗ N) ≅ φ_* M ⊗ φ_* N` as in `SheafOfModules.pushforwardTensorProductIso`,
is what lets it be compared, through mates, with the tensor comparison of a pullback.

## Main declarations

* `TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor` and
  `TauCeti.SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor`: the unit and counit of the
  adjunction are compatible with the tensor maps;
* `TauCeti.SheafOfModules.isIso_pushforward_μ_of_adjunction`: the tensor map of the pushforward
  along the left adjoint is invertible, with inverse computed by
  `TauCeti.SheafOfModules.inv_pushforward_μ_of_adjunction`.

## References

* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

section Adjunction

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J] (adj : F ⊣ G)
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj (ringCatSheaf S))
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (ringCatSheaf R).obj =
    ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)

/-- The unit `M ⟶ ψ_* φ_* M` of the adjunction between pushforwards is compatible with the tensor
maps of the two pushforwards. On sections both sides send `m ⊗ n` to its restriction. -/
theorem pushforwardPushforwardAdj_unit_app_tensor
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app (M ⊗ N) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M ⊗ₘ
          (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app N) ≫
        μ (_root_.SheafOfModules.pushforward ψ) _ _ ≫
          (_root_.SheafOfModules.pushforward ψ).map
            (μ (_root_.SheafOfModules.pushforward φ) M N) := by
  apply tensor_hom_ext
  ext V : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  set η := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  have hnat := congrArg (fun f ↦ f.app V (m ⊗ₜ[R.obj.obj V] n))
    (μ_natural (_root_.SheafOfModules.forget (ringCatSheaf R)) (η.app M) (η.app N))
  have hψ := pushforward_μ_app_tmul ψ ((_root_.SheafOfModules.pushforward φ).obj M)
    ((_root_.SheafOfModules.pushforward φ).obj N) V ((η.app M).val.app V m)
      ((η.app N).val.app V n)
  have hφ := pushforward_μ_app_tmul φ M N (G.op.obj V)
    ((η.app M).val.app V m) ((η.app N).val.app V n)
  -- On sections over `V`, the unit is restriction along the counit `F (G V) ⟶ V`; move it past
  -- the tensor map of `forget`, then compute the right side through the two tensor maps.
  refine (PresheafOfModules.naturality_apply
    (μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N) (adj.counit.app V.unop).op
      (m ⊗ₜ[R.obj.obj V] n)).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ ((_root_.SheafOfModules.forget (ringCatSheaf R)).map
    (μ (_root_.SheafOfModules.pushforward ψ) ((_root_.SheafOfModules.pushforward φ).obj M)
      ((_root_.SheafOfModules.pushforward φ).obj N) ≫
        (_root_.SheafOfModules.pushforward ψ).map
          (μ (_root_.SheafOfModules.pushforward φ) M N))).app V z) hnat)
  exact hφ.symm.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
    (μ (_root_.SheafOfModules.pushforward φ) M N)).app (G.op.obj V)) hψ.symm)

/-- The counit `φ_* ψ_* A ⟶ A` of the adjunction between pushforwards is compatible with the
tensor maps of the two pushforwards. On sections both sides send `a ⊗ b` to its restriction. -/
theorem pushforwardPushforwardAdj_counit_app_tensor
    (A B : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    μ (_root_.SheafOfModules.pushforward φ) ((_root_.SheafOfModules.pushforward ψ).obj A)
        ((_root_.SheafOfModules.pushforward ψ).obj B) ≫
      (_root_.SheafOfModules.pushforward φ).map (μ (_root_.SheafOfModules.pushforward ψ) A B) ≫
        (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app (A ⊗ B) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app A ⊗ₘ
        (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app B) := by
  apply tensor_hom_ext
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  set ε := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit
  have hnat := congrArg (fun f ↦ f.app U (a ⊗ₜ[S.obj.obj U] b))
    (μ_natural (_root_.SheafOfModules.forget (ringCatSheaf S)) (ε.app A) (ε.app B))
  have hφ := pushforward_μ_app_tmul φ ((_root_.SheafOfModules.pushforward ψ).obj A)
    ((_root_.SheafOfModules.pushforward ψ).obj B) U a b
  have hψ := pushforward_μ_app_tmul ψ A B (F.op.obj U) a b
  -- Compute the left side through the two tensor maps; on sections over `U`, the counit is
  -- restriction along the unit `U ⟶ G (F U)`, which then moves past the tensor map of `forget`.
  refine Eq.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
    ((_root_.SheafOfModules.pushforward φ).map (μ (_root_.SheafOfModules.pushforward ψ) A B) ≫
      ε.app (A ⊗ B))).app U) hφ) ?_
  refine Eq.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
      (ε.app (A ⊗ B))).app U) hψ) ?_
  refine Eq.trans ?_ hnat
  exact (PresheafOfModules.naturality_apply
    (μ (_root_.SheafOfModules.forget (ringCatSheaf S)) A B) (adj.unit.app U.unop).op
      (a ⊗ₜ[S.obj.obj (G.op.obj (F.op.obj U))] b)).symm

include adj ψ H₁ H₂ in
/-- **Pushforward along a left adjoint of sites commutes with tensor products**: the tensor map
`φ_* M ⊗ φ_* N ⟶ φ_* (M ⊗ N)` of the pushforward along `φ` is an isomorphism. -/
theorem isIso_pushforward_μ_of_adjunction (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso (μ (_root_.SheafOfModules.pushforward φ) M N) :=
  (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).isIso_μ_of_unit_of_counit
    (pushforwardPushforwardAdj_unit_app_tensor adj φ ψ H₁ H₂)
    (pushforwardPushforwardAdj_counit_app_tensor adj φ ψ H₁ H₂) M N

/-- The inverse of the tensor map of the pushforward along a left adjoint is the mate, under the
adjunction between pushforwards, of the tensor map of the right adjoint. -/
theorem inv_pushforward_μ_of_adjunction (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := isIso_pushforward_μ_of_adjunction adj φ ψ H₁ H₂ M N
    inv (μ (_root_.SheafOfModules.pushforward φ) M N) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).homEquiv _ _).symm
        (((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M ⊗ₘ
          (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app N) ≫
            μ (_root_.SheafOfModules.pushforward ψ) _ _) :=
  letI := isIso_pushforward_μ_of_adjunction adj φ ψ H₁ H₂ M N
  (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).inv_μ_eq_homEquiv_symm
    (pushforwardPushforwardAdj_counit_app_tensor adj φ ψ H₁ H₂) M N

end Adjunction

end SheafOfModules

end

end TauCeti

end

end RestrictionTensorSource0

/-! ## Recovered genuine proof body: `TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent`
Original SHA256: 1dfcbd0fca49bb0a8349d0f662423d63d6b5d02dfcec6631730d9edf01b887cd.
-/
section RestrictionTensorSource1


/-!
# Pullback of tensor products with a quasicoherent factor

For a morphism of schemes `f : X ⟶ Y`, the canonical comparison `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`,
the tensor map of the oplax monoidal pullback, is an isomorphism whenever either factor is
quasicoherent (`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent` and
`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent_right`). The target `Y` is arbitrary and the
other factor is an arbitrary sheaf of modules; no flatness or finiteness is assumed.

Pullback along an open immersion `j : U ⟶ Y` is strong monoidal for all sheaves of modules
(`Scheme.Modules.isIso_pullback_δ_of_isOpenImmersion`), and restriction along `j` is lax monoidal
with invertible tensor map (`Scheme.Modules.restrictFunctorLaxMonoidal`,
`Scheme.Modules.isIso_restrictFunctor_μ`).

These isomorphisms say that pulling back along `f` turns tensor products into tensor products as
long as one factor is quasicoherent; in particular they apply to line bundles. This is what makes
pullback of line-bundle classes multiplicative (`LineBundleClass.pullback_mul`), so that every
morphism of schemes induces a homomorphism of Picard groups `Pic(Y) →* Pic(X)`
(`LineBundleClass.pullbackHom`), as the Picard functor `T ↦ Pic(X_T)` requires.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The morphism of sheaves of rings along `j.opensFunctor`, given on sections by the inverses of
the isomorphisms `Scheme.Hom.appIso`, along which `Scheme.Modules.restrictFunctor j` is the
pushforward of sheaves of modules. -/
-- Exposed because the exported instance `restrictFunctorLaxMonoidal` is checked by unfolding
-- `restrictFunctor j` to the pushforward along this morphism.
@[expose]
def restrictRingCatSheafHom :
    U.ringCatSheaf ⟶ (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
  letI α : U.presheaf ⟶ j.opensFunctor.op ⋙ Y.presheaf := { app W := (j.appIso W.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- Restriction of modules along an open immersion `j` is lax monoidal, as the pushforward of
sheaves of modules along the functor of opens `j.opensFunctor`
(`TauCeti.SheafOfModules.pushforwardLaxMonoidal`). -/
instance restrictFunctorLaxMonoidal : (restrictFunctor j).LaxMonoidal :=
  TauCeti.SheafOfModules.pushforwardLaxMonoidal (restrictRingCatSheafHom j)

/-- The unit `M ⟶ j_* (M|_U)` of the restriction--pushforward adjunction along an open immersion
is compatible with the tensor maps of restriction and pushforward. -/
lemma restrictAdjunction_unit_app_tensor (M N : Y.Modules) :
    (restrictAdjunction j).unit.app (M ⊗ N) =
      ((restrictAdjunction j).unit.app M ⊗ₘ (restrictAdjunction j).unit.app N) ≫
        μ (pushforward j) _ _ ≫ (pushforward j).map (μ (restrictFunctor j) M N) :=
  -- The adjunction of opens is stated for `IsOpenMap.functor`, which is `j.opensFunctor`; `show`
  -- restates it in the form the sheaf-level lemma unifies with `restrictAdjunction j`.
  TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor
    (show j.opensFunctor ⊣ TopologicalSpace.Opens.map j.base from
      j.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom j) j.toRingCatSheafHom _ _
    M N

/-- The counit `(j_* A)|_U ⟶ A` of the restriction--pushforward adjunction along an open
immersion is compatible with the tensor maps of restriction and pushforward. -/
lemma restrictAdjunction_counit_app_tensor (A B : U.Modules) :
    μ (restrictFunctor j) ((pushforward j).obj A) ((pushforward j).obj B) ≫
      (restrictFunctor j).map (μ (pushforward j) A B) ≫
        (restrictAdjunction j).counit.app (A ⊗ B) =
      ((restrictAdjunction j).counit.app A ⊗ₘ (restrictAdjunction j).counit.app B) :=
  -- As in `restrictAdjunction_unit_app_tensor`, the adjunction of opens is restated with `show`.
  TauCeti.SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor
    (show j.opensFunctor ⊣ TopologicalSpace.Opens.map j.base from
      j.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom j) j.toRingCatSheafHom _ _
    A B

/-- Restriction of modules along an open immersion commutes with tensor products: its tensor
map `M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U` is an isomorphism. -/
instance isIso_restrictFunctor_μ (M N : Y.Modules) : IsIso (μ (restrictFunctor j) M N) :=
  (restrictAdjunction j).isIso_μ_of_unit_of_counit (restrictAdjunction_unit_app_tensor j)
    (restrictAdjunction_counit_app_tensor j) M N

/-- **Pullback along an open immersion is strong monoidal**: the tensor comparison
`j^*(M ⊗ N) ⟶ j^*M ⊗ j^*N` is an isomorphism for all sheaves of modules `M` and `N`. -/
instance isIso_pullback_δ_of_isOpenImmersion (M N : Y.Modules) :
    IsIso (δ (pullback j) M N) := by
  -- Compare with restriction, carrying the oplax structure of a left adjoint of `pushforward j`.
  let := (restrictAdjunction j).leftAdjointOplaxMonoidal
  let σ := (Adjunction.leftAdjointUniq (restrictAdjunction j) (pullbackPushforwardAdjunction j)).inv
  have hσ : conjugateEquiv (restrictAdjunction j) (pullbackPushforwardAdjunction j) σ = 𝟙 _ := by
    simp [σ, Adjunction.leftAdjointUniq]
  have h := Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _ hσ M N
  have : IsIso (δ (restrictFunctor j) M N) := by
    rw [Adjunction.leftAdjointOplaxMonoidal_δ]
    exact (restrictAdjunction j).inv_μ_eq_homEquiv_symm (restrictAdjunction_counit_app_tensor j)
      M N ▸ IsIso.inv_isIso (f := μ (restrictFunctor j) M N)
  have : IsIso (δ (pullback j) M N ≫ (σ.app M ⊗ₘ σ.app N)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (σ.app M ⊗ₘ σ.app N)

end OpenImmersion

end
end Modules
end Scheme
end AlgebraicGeometry
end

end RestrictionTensorSource1

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The actual restriction of a tensor product, expressed as the tensor
product of the two actual restrictions. Its inverse is the canonical tensor
map of the restriction functor. -/
def restrictTensorIso (M N : Y.Modules) :
    (M ⊗ N).restrict j ≅ M.restrict j ⊗ N.restrict j :=
  (asIso (μ (restrictFunctor j) M N)).symm

@[simp]
theorem restrictTensorIso_inv (M N : Y.Modules) :
    (restrictTensorIso j M N).inv = μ (restrictFunctor j) M N := rfl

/-- The actual pullback tensor comparison along an open immersion. -/
def pullbackTensorIsoOfOpenImmersion (M N : Y.Modules) :
    (pullback j).obj (M ⊗ N) ≅ (pullback j).obj M ⊗ (pullback j).obj N :=
  asIso (δ (pullback j) M N)

@[simp]
theorem pullbackTensorIsoOfOpenImmersion_hom (M N : Y.Modules) :
    (pullbackTensorIsoOfOpenImmersion j M N).hom = δ (pullback j) M N := rfl

end AlgebraicGeometry.Scheme.Modules

end
