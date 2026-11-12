module

public import ToricPower.OpenClosedScalar
public import ToricPower.CellularClosedConstantSections
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # The actual open/closed coefficient sequence of face diagrams

The open coefficient object is a genuine scalar submodule. Its quotient
is the actual right extension of the constant closed-face diagram.
Every face map is retained, and the resulting sequence is short exact
in the full abelian category of diagrams.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

def openScalarDiagram : B ⥤ ModuleCat.{u} k where
  obj b := ModuleCat.of k (MorseCoefficients.openScalar k (P b))
  map f := ModuleCat.ofHom (MorseCoefficients.openScalarMap k (downward f.le))
  map_id _ := rfl
  map_comp _ _ := rfl

def openScalarInclusion : openScalarDiagram k P downward ⟶ constantDiagram k B where
  app b := ModuleCat.ofHom (MorseCoefficients.openScalar k (P b)).subtype
  naturality {_ _} _ := rfl

/-- On an actual open-support cell the canonical inclusion is an
isomorphism, with no choice of a separate scalar identification. -/
theorem openScalarInclusion_app_isIso (b : B) (outside : ¬ P b) :
    IsIso ((openScalarInclusion k P downward).app b) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨Subtype.val_injective,fun a =>
    ⟨⟨a,fun h => (outside h).elim⟩,rfl⟩⟩

def openClosedCoefficientSequence : ShortComplex (B ⥤ ModuleCat.{u} k) :=
  ShortComplex.mk (openScalarInclusion k P downward) (constantToClosed k P downward)
    (by
      apply NatTrans.ext
      funext b
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext h
      exact x.property h.down)

theorem openClosedCoefficientSequence_evaluation_exact (b : B) :
    ((openClosedCoefficientSequence k P downward).map
      ((evaluation B (ModuleCat.{u} k)).obj b)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact MorseCoefficients.openScalar_range_eq_kernel k (P b)

instance openScalarInclusion_mono : Mono (openScalarInclusion k P downward) := by
  rw [NatTrans.mono_iff_mono_app]
  intro b
  rw [ModuleCat.mono_iff_injective]
  exact MorseCoefficients.openScalar_subtype_injective k (P b)

instance constantToClosed_epi : Epi (constantToClosed k P downward) := by
  rw [NatTrans.epi_iff_epi_app]
  intro b
  rw [ModuleCat.epi_iff_surjective]
  exact MorseCoefficients.closedScalarQuotient_surjective k (P b)

theorem openClosedCoefficientSequence_shortExact :
    (openClosedCoefficientSequence k P downward).ShortExact where
  exact := by
    let S := openClosedCoefficientSequence k P downward
    rw [S.exact_iff_isZero_homology]
    apply S.homology.isZero
    intro b
    exact ((S.map ((evaluation B (ModuleCat.{u} k)).obj b)).exact_iff_isZero_homology.mp
      (openClosedCoefficientSequence_evaluation_exact k P downward b)).of_iso
        (S.mapHomologyIso ((evaluation B (ModuleCat.{u} k)).obj b)).symm
  mono_f := inferInstanceAs (Mono (openScalarInclusion k P downward))
  epi_g := inferInstanceAs (Epi (constantToClosed k P downward))

end ToricPower.Cellular

end
