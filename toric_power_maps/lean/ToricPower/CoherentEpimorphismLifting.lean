module

public import ToricPower.SheafLocalGeneratorsEpimorphism
public import ToricPower.CoherentQuasicoherentInclusion
public import ToricPower.ExtComparisonEpiLifting
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Coherent domination of quasi-coherent epimorphisms

If sections on a finite affine cover extend as images of local Cartier
bases, a quasi-coherent epimorphism onto a coherent sheaf is dominated by
an epimorphism from a finite sum of Cartier line bundles. The construction
uses finite generating families and genuine local section surjectivity.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace ToricPower

universe u v

variable {X : Scheme.{u}} [IsIntegral X]
  {Index : Type v} (opens : Index → X.Opens)

/-- Every section on a selected open is the image of a local Cartier
basis under an actual global morphism. -/
def HasCartierSectionExtensions : Prop :=
  ∀ (j : Index) (M : X.Modules) [M.IsQuasicoherent] (s : Γ(M, opens j)),
    ∃ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
      (frame : (SheafOfModules.unit X.ringCatSheaf).over (opens j) ≅
        D.sheaf.over (opens j)) (mapping : D.sheaf ⟶ M),
      frame.hom ≫ mapping.over (opens j) = overSectionHom M (opens j) s

/-- A finite sum of actual Cartier line bundles dominates the given
quasi-coherent epimorphism. The individual line bundles are retained. -/
theorem exists_finiteCartier_epimorphism_lift [Finite Index]
    (covers : IsOpenCover opens) (affine : ∀ j, IsAffineOpen (opens j))
    (extend : HasCartierSectionExtensions opens)
    {E F : X.Modules} [E.IsQuasicoherent] [F.IsFinitePresentation]
    (p : E ⟶ F) [Epi p] :
    ∃ (J : Type (max u v)) (finite : Finite J),
      letI := finite
      ∃ (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
        (q : (⨁ fun a => (D a).sheaf) ⟶ E), Epi (q ≫ p) := by
  classical
  choose G finiteG using fun j =>
    exists_finite_generatingSections_over_affine F ⟨opens j, affine j⟩
  letI (j : Index) : (G j).IsFiniteType := finiteG j
  let values (j : Index) (a : (G j).I) : Γ(F, opens j) :=
    ((G j).s a).val (op (Over.mk (𝟙 (opens j))))
  choose lifted liftValue using fun j a =>
    affineSections_surjective_of_epi p (affine j) (values j a)
  choose divisors frames maps frameValue using fun j a => extend j E (lifted j a)
  let J := Σ j, (G j).I
  letI : Fintype J := Fintype.ofFinite J
  let family : J → X.Modules := fun a => (divisors a.1 a.2).sheaf
  let q : (⨁ family) ⟶ E := biproduct.desc fun a => maps a.1 a.2
  refine ⟨J, inferInstance, (fun a => divisors a.1 a.2), q, ?_⟩
  apply epi_of_local_generator_factorizations opens covers (q ≫ p) G
    (fun j a => (divisors j a).sheaf)
    (fun j a => biproduct.ι family ⟨j, a⟩)
    (fun j a => (frames j a).hom)
  intro j a
  have sumValue : biproduct.ι family ⟨j, a⟩ ≫ q = maps j a :=
    biproduct.ι_desc _ _
  calc
    _ = (frames j a).hom ≫ ((biproduct.ι family ⟨j, a⟩ ≫ q) ≫ p).over (opens j) := by
      simp only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (frames j a).hom ≫ (maps j a ≫ p).over (opens j) := by rw [sumValue]
    _ = ((frames j a).hom ≫ (maps j a).over (opens j)) ≫ p.over (opens j) := by
      simp only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_comp, Category.assoc]
    _ = overSectionHom E (opens j) (lifted j a) ≫ p.over (opens j) := by rw [frameValue]
    _ = overSectionHom F (opens j) (values j a) := by
      rw [overSectionHom_comp, liftValue]

/-- The constructed finite Cartier sum is a finite locally free sheaf. -/
theorem finiteCartierBiproduct_finiteLocallyFree {J : Type v} [Finite J]
    (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X) :
    SheafOfModules.isFiniteLocallyFree X.ringCatSheaf (⨁ fun a => (D a).sheaf) := by
  letI : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).IsClosedUnderFiniteProducts :=
    TauCeti.SheafOfModules.isClosedUnderFiniteProducts_isFiniteLocallyFree
      (R := X.ringCatSheaf)
  apply (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).prop_of_isLimit_fan
    (biproduct.isLimit fun a => (D a).sheaf)
  intro a
  letI := (D a).isInvertible_sheaf
  exact ⟨inferInstance, inferInstance⟩

/-- The same lift has a genuinely coherent source; this is the form
needed by the all-degree Ext comparison. -/
theorem exists_coherent_epimorphism_lift [Finite Index]
    (covers : IsOpenCover opens) (affine : ∀ j, IsAffineOpen (opens j))
    (extend : HasCartierSectionExtensions opens)
    {E F : X.Modules} [E.IsQuasicoherent] [F.IsFinitePresentation]
    (p : E ⟶ F) [Epi p] :
    ∃ (Q : X.Modules) (_ : Q.IsFinitePresentation) (q : Q ⟶ E), Epi (q ≫ p) := by
  obtain ⟨J, finite, D, q, epi⟩ :=
    exists_finiteCartier_epimorphism_lift opens covers affine extend p
  letI := finite
  exact ⟨_, (finiteCartierBiproduct_finiteLocallyFree D).2, q, epi⟩

/-- The geometric section-extension construction gives precisely the
epimorphism-lifting hypothesis for the actual full coherent inclusion. -/
theorem coherentToQuasicoherent_hasEpimorphismLifts_of_extensions
    [IsLocallyNoetherian X] [Finite Index]
    (covers : IsOpenCover opens) (affine : ∀ j, IsAffineOpen (opens j))
    (extend : HasCartierSectionExtensions opens) :
    HasEpimorphismLifts (coherentToQuasicoherent X) := by
  intro F E p hp
  letI := hp
  let p' : E.obj ⟶ F.obj := (quasicoherentInclusion X).map p
  letI : Epi p' := inferInstanceAs (Epi ((quasicoherentInclusion X).map p))
  obtain ⟨Q, hQ, q, hqp⟩ :=
    exists_coherent_epimorphism_lift opens covers affine extend p'
  letI := hQ
  let coherent : Coh X := ⟨Q, hQ⟩
  let q' : (coherentToQuasicoherent X).obj coherent ⟶ E := ObjectProperty.homMk q
  refine ⟨coherent, q', ?_⟩
  apply (quasicoherentInclusion X).epi_of_epi_map
  exact hqp

end ToricPower

end
