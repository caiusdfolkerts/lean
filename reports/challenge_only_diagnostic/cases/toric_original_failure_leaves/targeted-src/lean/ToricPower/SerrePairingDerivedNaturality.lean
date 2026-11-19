module

public import ToricPower.SerrePairingHomologyNaturality
public import ToricPower.LinearDerivedHomNaturality
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Naturality against arbitrary derived morphisms

The signed pairing first descends to actual cohomology classes. Its
source naturality then passes through actual localization: a general
derived map is a roof, and the two chain-map naturality identities
cancel its inverted quasi-isomorphism. No boundedness or finite
dimension is imposed on either source object.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v w
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]
variable (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
variable (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
variable (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))

theorem finiteCochainSerreClassEquiv_apply
    (E : CochainComplex A ℤ) (x : CohomologyClass E J 0)
    (y : CohomologyClass (mappedCochainComplex T J) E 0) :
    finiteCochainSerreClassEquiv k T J pairing E compatible support outside x y =
      (show (linearHomComplex k (mappedCochainComplex T J) E).homology 0 ⟶
          ModuleCat.of k k from
        (finiteCochainSerreHomologyIso k T J pairing E compatible support outside).hom
          ((HomComplex.homologyLinearEquiv k E J 0).symm x))
        ((HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).symm y) := rfl

theorem finiteCochainSerreClassEquiv_source_naturality
    {E F : CochainComplex A ℤ} (h : E ⟶ F) (x : CohomologyClass F J 0)
    (y : CohomologyClass (mappedCochainComplex T J) E 0) :
    finiteCochainSerreClassEquiv k T J pairing E compatible support outside
        (homClassPrecomp k h J 0 x) y =
      finiteCochainSerreClassEquiv k T J pairing F compatible support outside x
        (homClassPostcomp k (mappedCochainComplex T J) h 0 y) := by
  have hx : (HomComplex.homologyLinearEquiv k E J 0).symm
      (homClassPrecomp k h J 0 x) =
        HomologicalComplex.homologyMap (linearHomComplexPrecomp k h J) 0
          ((HomComplex.homologyLinearEquiv k F J 0).symm x) := by
    apply (HomComplex.homologyLinearEquiv k E J 0).injective
    rw [LinearEquiv.apply_symm_apply, homologyLinearEquiv_precomp,
      LinearEquiv.apply_symm_apply]
  have hy : (HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) F 0).symm
      (homClassPostcomp k (mappedCochainComplex T J) h 0 y) =
        HomologicalComplex.homologyMap (linearHomComplexMap k (mappedCochainComplex T J) h) 0
          ((HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).symm y) := by
    apply (HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) F 0).injective
    rw [LinearEquiv.apply_symm_apply, homologyLinearEquiv_postcomp,
      LinearEquiv.apply_symm_apply]
  rw [finiteCochainSerreClassEquiv_apply, finiteCochainSerreClassEquiv_apply, hx, hy]
  exact congrArg
    (fun f : (linearHomComplex k F J).homology 0 ⟶
        (scalarDual k).obj (Opposite.op
          ((linearHomComplex k (mappedCochainComplex T J) E).homology 0)) =>
      (show (linearHomComplex k (mappedCochainComplex T J) E).homology 0 ⟶
          ModuleCat.of k k from
        f ((HomComplex.homologyLinearEquiv k F J 0).symm x))
          ((HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).symm y))
    (finiteCochainSerreHomologyIso_source_naturality k T J pairing compatible support outside h)

variable [HasDerivedCategory.{w} A]
variable [J.IsKInjective] [(mappedCochainComplex T J).IsKProjective]

theorem finiteDerivedSerreEquiv_apply
    (E : CochainComplex A ℤ)
    (f : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj J)
    (g : DerivedCategory.Q.obj (mappedCochainComplex T J) ⟶ DerivedCategory.Q.obj E) :
    finiteDerivedSerreEquiv k T J pairing E compatible support outside f g =
      finiteCochainSerreClassEquiv k T J pairing E compatible support outside
        ((homClassDerivedZeroEquivOfKInjective k E J).symm f)
        ((homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) E).symm g) := rfl

theorem finiteDerivedSerreEquiv_source_chain_naturality
    {E F : CochainComplex A ℤ} (h : E ⟶ F)
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj J)
    (g : DerivedCategory.Q.obj (mappedCochainComplex T J) ⟶ DerivedCategory.Q.obj E) :
    finiteDerivedSerreEquiv k T J pairing E compatible support outside
        (DerivedCategory.Q.map h ≫ f) g =
      finiteDerivedSerreEquiv k T J pairing F compatible support outside f
        (g ≫ DerivedCategory.Q.map h) := by
  have hf : (homClassDerivedZeroEquivOfKInjective k E J).symm
      (DerivedCategory.Q.map h ≫ f) =
        homClassPrecomp k h J 0 ((homClassDerivedZeroEquivOfKInjective k F J).symm f) := by
    apply (homClassDerivedZeroEquivOfKInjective k E J).injective
    rw [LinearEquiv.apply_symm_apply, homClassDerivedZeroEquivOfKInjective_precomp,
      LinearEquiv.apply_symm_apply]
  have hg : (homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) F).symm
      (g ≫ DerivedCategory.Q.map h) =
        homClassPostcomp k (mappedCochainComplex T J) h 0
          ((homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) E).symm g) := by
    apply (homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) F).injective
    rw [LinearEquiv.apply_symm_apply, homClassDerivedZeroEquivOfKProjective_postcomp,
      LinearEquiv.apply_symm_apply]
  rw [finiteDerivedSerreEquiv_apply, finiteDerivedSerreEquiv_apply, hf, hg]
  exact finiteCochainSerreClassEquiv_source_naturality k T J pairing compatible support outside h _ _

/-- Naturality for every actual derived morphism, including maps between
unbounded objects which need not be represented by a single chain map. -/
theorem finiteDerivedSerreEquiv_source_naturality
    {E F : CochainComplex A ℤ}
    (h : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (f : DerivedCategory.Q.obj F ⟶ DerivedCategory.Q.obj J)
    (g : DerivedCategory.Q.obj (mappedCochainComplex T J) ⟶ DerivedCategory.Q.obj E) :
    finiteDerivedSerreEquiv k T J pairing E compatible support outside (h ≫ f) g =
      finiteDerivedSerreEquiv k T J pairing F compatible support outside f (g ≫ h) := by
  obtain ⟨L, s, hs, t, rfl⟩ := DerivedCategory.right_fac h
  letI := hs
  have h₁ := finiteDerivedSerreEquiv_source_chain_naturality k T J pairing compatible support outside
    s ((inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map t) ≫ f)
      (g ≫ inv (DerivedCategory.Q.map s))
  have h₂ := finiteDerivedSerreEquiv_source_chain_naturality k T J pairing compatible support outside
    t f (g ≫ inv (DerivedCategory.Q.map s))
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id,
    Category.comp_id] at h₁ h₂ ⊢
  exact h₁.symm.trans h₂

end ToricPower.SerrePairing

end
