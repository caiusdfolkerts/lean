module

public import ToricPower.SerrePairingHomology
public import ToricPower.SerrePairingCochainNaturality

/-!
# Naturality of the signed short-complex pairing

The three-term pairing around degree zero is natural in the arbitrary
source complex. Its final component carries the minus sign already
required by the differential calculation. The induced comparison on
actual homology is therefore natural as well.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex Opposite
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]

/-- The literal signed Hom complex, contravariant in its source. -/
def linearHomComplexContravariant (J : CochainComplex A ℤ) :
    (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} k) ℤ where
  obj E := linearHomComplex k E.unop J
  map h := linearHomComplexPrecomp k h.unop J
  map_id E := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change homCochainPrecomp k (𝟙 E.unop) J n f = f
    apply Cochain.ext
    intro p q hpq
    simp only [homCochainPrecomp_v, HomologicalComplex.id_f, Category.id_comp]
  map_comp h g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change homCochainPrecomp k (g.unop ≫ h.unop) J n f =
      homCochainPrecomp k g.unop J n (homCochainPrecomp k h.unop J n f)
    apply Cochain.ext
    intro p q hpq
    simp only [homCochainPrecomp_v, HomologicalComplex.comp_f, Category.assoc]

variable (T : A ⥤ A) [T.Additive]
variable (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
variable (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
variable (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))

def finiteCochainPairingShortNatIso' :
    linearHomComplexContravariant k J ⋙
        HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (.up ℤ) (-1) 0 1 ≅
      ((linearHomComplexFunctor k (mappedCochainComplex T J)) ⋙
        HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (.up ℤ) (-1) 0 1).op ⋙
        ShortComplex.opFunctor (ModuleCat.{u} k) ⋙ (scalarDual k).mapShortComplex :=
  NatIso.ofComponents
    (fun E => cochainPairingShortComplexIso' k T J pairing E.unop compatible support outside)
    (by
      intro E F h
      apply ShortComplex.Hom.ext
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        change finiteCochainPairingEquiv k T J pairing F.unop support outside (-1)
          (homCochainPrecomp k h.unop J (-1) f) g =
            finiteCochainPairingEquiv k T J pairing E.unop support outside (-1) f
              (homCochainPostcomp k (mappedCochainComplex T J) h.unop 1 g)
        exact finiteCochainPairingEquiv_source_naturality k T J pairing
          h.unop support outside (-1) f g
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        change finiteCochainPairingEquiv k T J pairing F.unop support outside 0
          (homCochainPrecomp k h.unop J 0 f) g =
            finiteCochainPairingEquiv k T J pairing E.unop support outside 0 f
              (homCochainPostcomp k (mappedCochainComplex T J) h.unop 0 g)
        exact finiteCochainPairingEquiv_source_naturality k T J pairing
          h.unop support outside 0 f g
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro g
        change (1 : ℤ).negOnePow •
          finiteCochainPairingEquiv k T J pairing F.unop support outside 1
            (homCochainPrecomp k h.unop J 1 f) g =
          (1 : ℤ).negOnePow •
            finiteCochainPairingEquiv k T J pairing E.unop support outside 1 f
              (homCochainPostcomp k (mappedCochainComplex T J) h.unop (-1) g)
        exact congrArg (fun x : k => (1 : ℤ).negOnePow • x)
          (finiteCochainPairingEquiv_source_naturality k T J pairing
            h.unop support outside 1 f g))

def finiteCochainPairingShortNatIso :
    linearHomComplexContravariant k J ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0 ≅
      ((linearHomComplexFunctor k (mappedCochainComplex T J)) ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0).op ⋙
        ShortComplex.opFunctor (ModuleCat.{u} k) ⋙ (scalarDual k).mapShortComplex :=
  Functor.isoWhiskerLeft (linearHomComplexContravariant k J)
      (HomologicalComplex.natIsoSc' _ _ (-1) 0 1 (by simp) (by simp)) ≪≫
    finiteCochainPairingShortNatIso' k T J pairing compatible support outside ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (Functor.isoWhiskerLeft (linearHomComplexFunctor k (mappedCochainComplex T J))
          (HomologicalComplex.natIsoSc' _ _ (-1) 0 1 (by simp) (by simp))))
        (ShortComplex.opFunctor (ModuleCat.{u} k) ⋙ (scalarDual k).mapShortComplex)

theorem finiteCochainPairingShortNatIso_app (E : CochainComplex A ℤ) :
    (finiteCochainPairingShortNatIso k T J pairing compatible support outside).app (op E) =
      cochainPairingShortComplexIso k T J pairing E compatible support outside := rfl

end ToricPower.SerrePairing

end
