module

public import ToricPower.SerrePairingShortComplexNaturality

/-!
# Naturality of Serre duality on Hom-complex homology

The maps here are the actual homology maps of precomposition and
postcomposition. Exact scalar duality supplies a natural comparison
with dual homology, including for infinite-dimensional source objects.
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

def shortComplexDualHomologyIso (S : ShortComplex (ModuleCat.{u} k)) :
    (S.op.map (scalarDual k)).homology ≅ (scalarDual k).obj (op S.homology) :=
  S.op.mapHomologyIso (scalarDual k) ≪≫ (scalarDual k).mapIso S.homologyOpIso

theorem shortComplexDualHomologyIso_naturality
    {S₁ S₂ : ShortComplex (ModuleCat.{u} k)} (f : S₁ ⟶ S₂) :
    ShortComplex.homologyMap ((scalarDual k).mapShortComplex.map (ShortComplex.opMap f)) ≫
        (shortComplexDualHomologyIso k S₁).hom =
      (shortComplexDualHomologyIso k S₂).hom ≫
        (scalarDual k).map (ShortComplex.homologyMap f).op := by
  have h := ShortComplex.mapHomologyIso_hom_naturality (ShortComplex.opMap f) (scalarDual k)
  simp only [shortComplexDualHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp,
    ShortComplex.homologyOpIso_hom_naturality, CategoryTheory.Functor.map_comp,
    Category.assoc]

variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]
variable (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
variable (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
variable (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))

theorem finiteCochainSerreHomologyIso_source_naturality
    {E F : CochainComplex A ℤ} (h : E ⟶ F) :
    HomologicalComplex.homologyMap (linearHomComplexPrecomp k h J) 0 ≫
        (finiteCochainSerreHomologyIso k T J pairing E compatible support outside).hom =
      (finiteCochainSerreHomologyIso k T J pairing F compatible support outside).hom ≫
        (scalarDual k).map
          (HomologicalComplex.homologyMap
            (linearHomComplexMap k (mappedCochainComplex T J) h) 0).op := by
  let S := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0
  have hshort := (finiteCochainPairingShortNatIso k T J pairing compatible support outside).hom.naturality h.op
  have hH := congrArg ((ShortComplex.homologyFunctor (ModuleCat.{u} k)).map) hshort
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hH
  change HomologicalComplex.homologyMap (linearHomComplexPrecomp k h J) 0 ≫
      ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairing E compatible support outside).hom =
    ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairing F compatible support outside).hom ≫
      ShortComplex.homologyMap ((scalarDual k).mapShortComplex.map
        (ShortComplex.opMap (S.map
          (linearHomComplexMap k (mappedCochainComplex T J) h)))) at hH
  change HomologicalComplex.homologyMap (linearHomComplexPrecomp k h J) 0 ≫
      (ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairing E compatible support outside).hom ≫
        (shortComplexDualHomologyIso k
          ((linearHomComplex k (mappedCochainComplex T J) E).sc 0)).hom) =
    (ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairing F compatible support outside).hom ≫
        (shortComplexDualHomologyIso k
          ((linearHomComplex k (mappedCochainComplex T J) F).sc 0)).hom) ≫ _
  rw [← Category.assoc, hH, Category.assoc,
    shortComplexDualHomologyIso_naturality, Category.assoc]
  rfl

end ToricPower.SerrePairing

end
