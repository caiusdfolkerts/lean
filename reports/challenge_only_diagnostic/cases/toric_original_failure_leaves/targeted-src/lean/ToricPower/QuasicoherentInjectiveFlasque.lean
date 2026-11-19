module

public import ToricPower.QuasicoherentEnoughInjectives

/-!
# Quasicoherent injectives are actual flasque module sheaves

On a Noetherian separated scheme with a finite affine cover, an actual
quasicoherent sheaf embeds into the explicitly constructed flasque
quasicoherent sheaf from the affine injective modules. If the source is
injective in `QCoh`, that embedding splits in `QCoh`; flasqueness descends
to the resulting actual sheaf retract.

Thus positive ordinary sheaf cohomology vanishes on these injectives.
This supplies the acyclicity input for comparisons of derived functors,
without asserting that quasicoherent injectives are injective among all
module sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u v w

/-- Every presheaf retract of a flasque presheaf is flasque. The proof
uses the actual naturality squares and the component split epimorphisms. -/
theorem presheafFlasque_of_retract {X : TopCat.{u}}
    {A : Type v} [Category.{w} A] {F G : TopCat.Presheaf A X}
    (i : F ⟶ G) (r : G ⟶ F) (h : i ≫ r = 𝟙 F) [G.IsFlasque] : F.IsFlasque where
  epi {U V} f := by
    letI : IsSplitEpi (r.app V) := IsSplitEpi.mk'
      ⟨i.app V, by
        have hv := congr_app h V
        change i.app V ≫ r.app V = 𝟙 (F.obj V) at hv
        exact hv⟩
    have he : Epi (r.app U ≫ F.map f) := by
      rw [← r.naturality f]
      infer_instance
    exact @epi_of_epi _ _ _ _ _ (r.app U) (F.map f) he

/-- The preceding retract lemma applies to the literal underlying
abelian presheaves of module sheaves. -/
theorem moduleFlasque_of_retract {X : Scheme.{u}} {M N : X.Modules}
    (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M) [N.presheaf.IsFlasque] :
    M.presheaf.IsFlasque := by
  letI : ((Scheme.Modules.toPresheaf X).obj N).IsFlasque := by
    change N.presheaf.IsFlasque
    infer_instance
  apply presheafFlasque_of_retract
    ((Scheme.Modules.toPresheaf X).map i) ((Scheme.Modules.toPresheaf X).map r)
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]

/-- An actual injective of `QCoh X` is flasque when a finite affine cover
is provided. The splitting takes place in the actual quasicoherent category. -/
theorem quasicoherentInjective_isFlasque_of_cover
    (cover : Scheme.AffineOpenCover.{u} X) [Finite cover.I₀]
    (J : QCoh X) [Injective J] : (Scheme.Modules.presheaf J.obj).IsFlasque := by
  letI : Finite cover.openCover.I₀ := inferInstanceAs (Finite cover.I₀)
  letI (i : cover.I₀) : IsAffineHom (cover.f i) :=
    BondalThomsen.QuasicoherentFlasqueTowerConstruction.affineSource_isAffineHom (cover.f i)
  letI : ∀ i : cover.openCover.I₀, IsAffineHom (cover.openCover.f i) :=
    fun i => inferInstanceAs (IsAffineHom (cover.f i))
  let data := BondalThomsen.FiniteAffineCoverQuasicoherentExtensions.noetherianLocalFlasqueEmbedding cover J.obj
  let M : QCoh X := ⟨data.middle, data.middle_isQuasicoherent⟩
  let f : J ⟶ M := ObjectProperty.homMk data.inclusion
  letI : Mono data.inclusion := data.inclusion_mono
  letI : Mono f := (quasicoherentInclusion X).mono_of_mono_map
    (inferInstanceAs (Mono data.inclusion))
  let r : M ⟶ J := Injective.factorThru (𝟙 J) f
  letI : (Scheme.Modules.presheaf M.obj).IsFlasque := data.middle_isFlasque
  apply moduleFlasque_of_retract f.hom r.hom
  exact congrArg (fun t => t.hom) (Injective.comp_factorThru (𝟙 J) f)

/-- Noetherian separated schemes with quasicompact underlying space have
flasque actual quasicoherent injectives. -/
instance quasicoherentInjective_isFlasque [CompactSpace X]
    (J : QCoh X) [Injective J] : (Scheme.Modules.presheaf J.obj).IsFlasque :=
  quasicoherentInjective_isFlasque_of_cover
    (BondalThomsen.FiniteAffineCoverQuasicoherentExtensions.finiteAffineOpenCover X) J

/-- Positive ordinary sheaf cohomology vanishes for actual quasicoherent
injectives, with no replacement of the meaning of cohomology. -/
theorem quasicoherentInjective_cohomology_subsingleton [CompactSpace X]
    (J : QCoh X) [Injective J] (n : ℕ) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology J.obj (n+1)) :=
  BondalThomsen.FiniteQuasicoherentCohomologyTower.isCohomologicallyAcyclic_of_isFlasque J.obj n

end ToricPower

end
