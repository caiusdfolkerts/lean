module

public import ToricPower.CoherentImages
public import ToricPower.CoherentEpimorphismLifting

/-!
# A coherent subsheaf agreeing on finitely many selected opens

The selected opens need not cover the ambient scheme. Finite local
generating families and actual Cartier section extensions produce a
finite Cartier sum whose map is epimorphic on each selected open.
Its coherent image is consequently isomorphic to the target on each
of those opens. This is the finite construction used for extension
across the toric boundary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}}

/-- Factoring a genuine generating family proves epimorphy on the
specified open, without an ambient covering hypothesis. -/
theorem epi_over_of_generator_factorizations
    {Q M : X.Modules} (p : Q ⟶ M) (U : X.Opens)
    (G : (M.over U).GeneratingSections)
    (source : G.I → X.Modules) (lift : ∀ a, source a ⟶ Q)
    (frame : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over U ⟶ (source a).over U)
    (factor : ∀ a, (frame a ≫ (lift a).over U) ≫ p.over U =
      overSectionHom M U ((G.s a).val (op (Over.mk (𝟙 U))))) :
    Epi (p.over U) := by
  constructor
  intro T f g equality
  apply (cancel_epi G.π).mp
  apply T.freeHomEquiv.injective
  funext a
  change T.unitHomEquiv (SheafOfModules.ιFree a ≫ G.π ≫ f) =
    T.unitHomEquiv (SheafOfModules.ιFree a ≫ G.π ≫ g)
  apply congrArg T.unitHomEquiv
  rw [← Category.assoc,← Category.assoc,generatingSections_ι_π,← factor a]
  simp only [Category.assoc]
  rw [equality]

variable [IsIntegral X] {I : Type v} [Finite I] (opens : I → X.Opens)
  (extensions : HasCartierSectionExtensions opens)
  (E : X.Modules) [E.IsQuasicoherent]
  (G : ∀ j, (E.over (opens j)).GeneratingSections) [∀ j, (G j).IsFiniteType]

include extensions G

/-- A single finite Cartier sum generates the target on all the
specified opens simultaneously. -/
theorem exists_finiteCartier_map_epi_over :
    ∃ (J : Type (max u v)) (finite : Finite J),
      letI := finite
      ∃ (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
        (q : (⨁ fun a => (D a).sheaf) ⟶ E), ∀ j, Epi (q.over (opens j)) := by
  classical
  choose divisors frames maps frameValue using fun j a =>
    extensions j E (((G j).s a).val (op (Over.mk (𝟙 (opens j)))))
  let J := Σ j, (G j).I
  letI : Fintype J := Fintype.ofFinite J
  let family : J → X.Modules := fun a => (divisors a.1 a.2).sheaf
  let q : (⨁ family) ⟶ E := biproduct.desc fun a => maps a.1 a.2
  refine ⟨J,inferInstance,(fun a => divisors a.1 a.2),q,?_⟩
  intro j
  apply epi_over_of_generator_factorizations q (opens j) (G j)
    (fun a => (divisors j a).sheaf)
    (fun a => biproduct.ι family ⟨j,a⟩) (fun a => (frames j a).hom)
  intro a
  have sumValue : biproduct.ι family ⟨j,a⟩ ≫ q = maps j a := biproduct.ι_desc _ _
  calc
    _ = (frames j a).hom ≫ (biproduct.ι family ⟨j,a⟩ ≫ q).over (opens j) := by
      simp only [SheafOfModules.Hom.over,CategoryTheory.Functor.map_comp,Category.assoc]
    _ = (frames j a).hom ≫ (maps j a).over (opens j) := by rw [sumValue]
    _ = _ := frameValue j a

/-- The actual image gives a coherent extension on all selected opens.
Neither quasicoherence nor finite presentation of this image is a
supplied assumption. -/
theorem exists_coherent_image_iso_over [IsLocallyNoetherian X] :
    ∃ (P : X.Modules) (_ : P.IsFinitePresentation) (f : P ⟶ E),
      Mono f ∧ ∀ j, IsIso (f.over (opens j)) := by
  obtain ⟨J,finite,D,q,localEpi⟩ :=
    exists_finiteCartier_map_epi_over opens extensions E G
  letI := finite
  letI := (finiteCartierBiproduct_finiteLocallyFree D).2
  letI := finitePresentation_image_of_coherent_source q
  refine ⟨image q,inferInstance,image.ι q,inferInstance,?_⟩
  intro j
  letI := localEpi j
  have factor : (factorThruImage q).over (opens j) ≫ (image.ι q).over (opens j) =
      q.over (opens j) := by
    change (SheafOfModules.overFunctor X.ringCatSheaf (opens j)).map (factorThruImage q) ≫
      (SheafOfModules.overFunctor X.ringCatSheaf (opens j)).map (image.ι q) = _
    rw [← CategoryTheory.Functor.map_comp,image.fac]
  letI : Epi ((image.ι q).over (opens j)) := epi_of_epi_fac factor
  letI : Mono ((image.ι q).over (opens j)) := by
    letI : Mono (image.ι q).val := inferInstanceAs
      (Mono ((SheafOfModules.forget X.ringCatSheaf).map (image.ι q)))
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro W
    exact PresheafOfModules.injective_of_mono (image.ι q).val (op W.unop.left)
  exact isIso_of_mono_of_epi ((image.ι q).over (opens j))

end ToricPower

end
