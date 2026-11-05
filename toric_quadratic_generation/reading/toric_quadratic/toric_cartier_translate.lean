module

public import PaperVerification.ToricCartierAmple
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

/-!
# Principal translates and linear equivalence of actual Cartier sheaves

A nonzero rational function acts by an actual automorphism of the rational
function sheaf. Postcomposing a fractional embedding by this automorphism
changes the Cartier divisor by a principal divisor, while preserving its
actual invertible sheaf. This is linear equivalence, distinguished from the
embedding-preserving equivalence of presentations of the same divisor.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

def rationalScaleEquivNonempty (q : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  let e : X.functionField ≃ₗ[X.functionField] X.functionField :=
    LinearEquiv.smulOfUnit q
  exact (rationalValueLinearEquiv X U).trans
    ((e.restrictScalars Γ(X,U)).trans (rationalValueLinearEquiv X U).symm)

def rationalScaleEquiv (q : X.functionFieldˣ) (U : X.Opens) :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    exact rationalScaleEquivNonempty q U
  · exact LinearEquiv.refl _ _

@[simp] theorem rationalScaleEquiv_value (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(rationalFunctions X,U)) :
    rationalValue X U (rationalScaleEquiv q U s) =
      (q : X.functionField)*rationalValue X U s := by
  simp only [rationalScaleEquiv,dif_pos (show Nonempty U from inferInstance)]
  change (rationalValueLinearEquiv X U)
      ((rationalValueLinearEquiv X U).symm
        ((q : X.functionField) * (rationalValueLinearEquiv X U) s)) =
    (q : X.functionField) * (rationalValueLinearEquiv X U) s
  exact (rationalValueLinearEquiv X U).apply_symm_apply _

theorem rationalScaleEquiv_restrict (q : X.functionFieldˣ)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(rationalFunctions X,U)) :
    rationalScaleEquiv q V ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctions X).presheaf.map i.op (rationalScaleEquiv q U s) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply (rationalValue X V).injective
    rw [rationalScaleEquiv_value,rationalValue_restrict,rationalValue_restrict,
      rationalScaleEquiv_value]
  · have hbot : V=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hV ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X V hbot
    letI := Module.subsingleton Γ(X,V) Γ(rationalFunctions X,V)
    exact Subsingleton.elim _ _

/-- Multiplication by a rational unit is an actual sheaf automorphism. -/
def rationalScaleIso (q : X.functionFieldˣ) : rationalFunctions X ≅ rationalFunctions X :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U=>(rationalScaleEquiv q U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        exact rationalScaleEquiv_restrict q f.unop s)

namespace CartierData

variable (D E F : CartierData X)

/-- Linear equivalence records an isomorphism of the actual invertible
sheaves. It does not require equality of their rational embeddings. -/
def LinearlyEquivalent : Prop := Nonempty (D.sheaf ≅ E.sheaf)

theorem linearlyEquivalent_refl : D.LinearlyEquivalent D := ⟨Iso.refl _⟩

theorem linearlyEquivalent_symm (h : D.LinearlyEquivalent E) : E.LinearlyEquivalent D :=
  ⟨h.some.symm⟩

theorem linearlyEquivalent_trans (hDE : D.LinearlyEquivalent E)
    (hEF : E.LinearlyEquivalent F) : D.LinearlyEquivalent F := ⟨hDE.some ≪≫ hEF.some⟩

theorem Equivalent.linearlyEquivalent (h : D.Equivalent E) : D.LinearlyEquivalent E :=
  ⟨h.choose⟩

/-- Principal translation multiplies the actual fractional embedding by q.
The underlying actual sheaf is unchanged by construction. -/
def scale (q : X.functionFieldˣ) : CartierData X where
  sheaf := D.sheaf
  inclusion := D.inclusion ≫ (rationalScaleIso q).hom
  inclusion_injective U :=
    (rationalScaleEquiv q U).injective.comp (D.inclusion_injective U)
  locallyFree := D.locallyFree

def scaleSheafIso (q : X.functionFieldˣ) : (D.scale q).sheaf ≅ D.sheaf := Iso.refl _

theorem scale_linearlyEquivalent (q : X.functionFieldˣ) :
    (D.scale q).LinearlyEquivalent D := ⟨D.scaleSheafIso q⟩

@[simp] theorem scale_sectionValue (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf,U)) :
    (D.scale q).sectionValue U s = (q : X.functionField)*D.sectionValue U s :=
  rationalScaleEquiv_value q U (D.inclusion.app U s)

theorem scale_equivalent_scale (h : D.Equivalent E) (q : X.functionFieldˣ) :
    (D.scale q).Equivalent (E.scale q) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e,?_⟩
  change e.hom ≫ (E.inclusion ≫ (rationalScaleIso q).hom) =
    D.inclusion ≫ (rationalScaleIso q).hom
  rw [← Category.assoc,he]

/-- The principal translation changes every local rational generator by
the same explicit factor, so no character shift is lost. -/
theorem scale_frameRationalGenerator (q : X.functionFieldˣ)
    {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    (D.scale q).frameRationalGenerator e =
      (q : X.functionField)*D.frameRationalGenerator e :=
  D.scale_sectionValue q U (D.frameGenerator e U le_rfl)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.rationalScaleIso
#print axioms PaperVerification.ToricSchemes.CartierData.scale_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.CartierData.scale_frameRationalGenerator
