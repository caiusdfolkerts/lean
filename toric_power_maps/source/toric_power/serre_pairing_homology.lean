module

public import ToricPower.SerrePairingDifferential
public import ToricPower.LinearDualHomology
public import ToricPower.LinearDerivedHomComparison

/-!
# Serre duality on actual Hom-complex cohomology

The three terms around degree zero form an actual short-complex
isomorphism with the scalar dual of the reversed Hom complex. Its last
component is negated to match the signed Hom differential. Exact scalar
duality then gives the pairing of actual cohomology classes, and hence
of derived morphisms when the usual K-injective/K-projective conditions
hold. The unbounded argument is never dualized twice.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex Opposite
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v w
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]
variable (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
variable (E : CochainComplex A ℤ)
variable (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
variable (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))

def cochainPairingModuleIso (n : ℤ) :
    ModuleCat.of k (Cochain E J n) ≅
      (scalarDual k).obj (op (ModuleCat.of k (Cochain (mappedCochainComplex T J) E (-n)))) :=
  ((finiteCochainPairingEquiv k T J pairing E support outside n).trans
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := ModuleCat.of k (Cochain (mappedCochainComplex T J) E (-n)))
      (N := ModuleCat.of k k)).symm).toModuleIso

def cochainPairingShortComplexIso' :
    (linearHomComplex k E J).sc' (-1) 0 1 ≅
      (((linearHomComplex k (mappedCochainComplex T J) E).sc' (-1) 0 1).op).map
        (scalarDual k) := by
  let e₁ := cochainPairingModuleIso k T J pairing E support outside (-1)
  let e₂ := cochainPairingModuleIso k T J pairing E support outside 0
  let e₃ := cochainPairingModuleIso k T J pairing E support outside 1 ≪≫
    (degreeSignEquiv k
      ((scalarDual k).obj (op (ModuleCat.of k
        (Cochain (mappedCochainComplex T J) E (-1))))) 1).toModuleIso
  refine ShortComplex.isoMk e₁ e₂ e₃ ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change finiteCochainPairingEquiv k T J pairing E support outside (-1) f
        (δ 0 1 g) =
      finiteCochainPairingEquiv k T J pairing E support outside 0 (δ (-1) 0 f) g
    have h := (finiteCochainPairingEquiv_differential k T J pairing E compatible
      support outside (-1) f g).symm
    norm_num only [Int.negOnePow_zero, one_smul] at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change finiteCochainPairingEquiv k T J pairing E support outside 0 f
        (δ (-1) 0 g) =
      (1 : ℤ).negOnePow •
        finiteCochainPairingEquiv k T J pairing E support outside 1 (δ 0 1 f) g
    have h := congrArg Neg.neg
      (finiteCochainPairingEquiv_differential k T J pairing E compatible
        support outside 0 f g).symm
    norm_num only [Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg] at h ⊢
    exact h

def cochainPairingShortComplexIso :
    (linearHomComplex k E J).sc 0 ≅
      (((linearHomComplex k (mappedCochainComplex T J) E).sc 0).op).map (scalarDual k) :=
  (linearHomComplex k E J).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    cochainPairingShortComplexIso' k T J pairing E compatible support outside ≪≫
    (scalarDual k).mapShortComplex.mapIso
      ((ShortComplex.opFunctor _).mapIso
        ((linearHomComplex k (mappedCochainComplex T J) E).isoSc'
          (-1) 0 1 (by simp) (by simp)).op)

def finiteCochainSerreHomologyIso :
    (linearHomComplex k E J).homology 0 ≅
      (scalarDual k).obj (op ((linearHomComplex k (mappedCochainComplex T J) E).homology 0)) :=
  ShortComplex.homologyMapIso
    (cochainPairingShortComplexIso k T J pairing E compatible support outside) ≪≫
    (((linearHomComplex k (mappedCochainComplex T J) E).sc 0).op).mapHomologyIso
      (scalarDual k) ≪≫
    (scalarDual k).mapIso
      ((linearHomComplex k (mappedCochainComplex T J) E).sc 0).homologyOpIso

def finiteCochainSerreClassEquiv :
    CohomologyClass E J 0 ≃ₗ[k]
      Module.Dual k (CohomologyClass (mappedCochainComplex T J) E 0) :=
  (HomComplex.homologyLinearEquiv k E J 0).symm.trans
    ((finiteCochainSerreHomologyIso k T J pairing E compatible support outside).toLinearEquiv.trans
      ((ModuleCat.homLinearEquiv (R := k) (S := k)
        (M := (linearHomComplex k (mappedCochainComplex T J) E).homology 0)
        (N := ModuleCat.of k k)).trans
          (HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).symm.dualMap))

end ToricPower.SerrePairing

end
