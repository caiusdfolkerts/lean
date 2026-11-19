module

public import ToricPower.SerrePairingHomologyNaturality

/-!
# Target naturality of the signed pairing

This comparison allows different finite degree supports for the two
targets. A map compatible with the termwise pairings intertwines the
actual Hom-complex pairing, including the contravariant map induced by
its image under inverse Nakayama.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex Opposite
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

private theorem compose_pairing_square
    {D : Type*} [Category* D]
    {A B A' B' C D' C' D'' : D}
    (a : A ⟶ B) (a' : A' ⟶ B') (b : C ⟶ D') (b' : C' ⟶ D'')
    (lA : A ⟶ A') (lB : B ⟶ B') (rC : C' ⟶ C) (rD : D'' ⟶ D')
    (p : A' ⟶ C') (q : B' ⟶ D'')
    (left : a ≫ lB = lA ≫ a') (middle : a' ≫ q = p ≫ b')
    (right : b' ≫ rD = rC ≫ b) :
    a ≫ (lB ≫ q ≫ rD) = (lA ≫ p ≫ rC) ≫ b := by
  calc
    a ≫ (lB ≫ q ≫ rD) = lA ≫ (a' ≫ q) ≫ rD := by
      rw [← Category.assoc, left]
      simp only [Category.assoc]
    _ = lA ≫ (p ≫ b') ≫ rD := by rw [middle]
    _ = (lA ≫ p ≫ rC) ≫ b := by
      simp only [Category.assoc]
      rw [right]

universe u v
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]
variable (J K : CochainComplex A ℤ)
variable (pairingJ : ∀ q, CodomainPairing k T (J.X q))
variable (pairingK : ∀ q, CodomainPairing k T (K.X q))
variable (dJ : ∀ p q, Compatible k (pairingJ p) (pairingJ q) (J.d p q))
variable (dK : ∀ p q, Compatible k (pairingK p) (pairingK q) (K.d p q))
variable (h : J ⟶ K)
variable (compatible : ∀ q, Compatible k (pairingJ q) (pairingK q) (h.f q))
variable (supportJ : Finset ℤ) (outsideJ : ∀ q, q ∉ supportJ → IsZero (J.X q))
variable (supportK : Finset ℤ) (outsideK : ∀ q, q ∉ supportK → IsZero (K.X q))
variable (E : CochainComplex A ℤ)

include compatible

theorem cochainPairingShortComplexIso'_target_naturality :
    (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (.up ℤ) (-1) 0 1).map
        (linearHomComplexMap k E h) ≫
      (cochainPairingShortComplexIso' k T K pairingK E dK supportK outsideK).hom =
    (cochainPairingShortComplexIso' k T J pairingJ E dJ supportJ outsideJ).hom ≫
      (scalarDual k).mapShortComplex.map
        (ShortComplex.opMap
          ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (.up ℤ) (-1) 0 1).map
            (linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E))) := by
  apply ShortComplex.Hom.ext
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact finiteCochainPairingEquiv_target_naturality k T J K pairingJ pairingK h compatible E
      supportJ outsideJ supportK outsideK (-1) f g
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact finiteCochainPairingEquiv_target_naturality k T J K pairingJ pairingK h compatible E
      supportJ outsideJ supportK outsideK 0 f g
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact congrArg (fun x : k => (1 : ℤ).negOnePow • x)
      (finiteCochainPairingEquiv_target_naturality k T J K pairingJ pairingK h compatible E
        supportJ outsideJ supportK outsideK 1 f g)

theorem cochainPairingShortComplexIso_target_naturality :
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0).map
        (linearHomComplexMap k E h) ≫
      (cochainPairingShortComplexIso k T K pairingK E dK supportK outsideK).hom =
    (cochainPairingShortComplexIso k T J pairingJ E dJ supportJ outsideJ).hom ≫
      (scalarDual k).mapShortComplex.map
        (ShortComplex.opMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0).map
            (linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E))) := by
  let S := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0
  let S' := HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} k) (.up ℤ) (-1) 0 1
  let α : S ≅ S' := HomologicalComplex.natIsoSc' _ _ (-1) 0 1 (by simp) (by simp)
  let D := ShortComplex.opFunctor (ModuleCat.{u} k) ⋙ (scalarDual k).mapShortComplex
  let a := linearHomComplexMap k E h
  let b := linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E
  have left := α.hom.naturality a
  have right := congrArg (fun f => D.map f.op) (α.hom.naturality b)
  simp only [op_comp, CategoryTheory.Functor.map_comp] at right
  exact compose_pairing_square (S.map a) (S'.map a)
    (D.map (S.map b).op) (D.map (S'.map b).op)
    (α.hom.app _) (α.hom.app _) (D.map (α.hom.app _).op) (D.map (α.hom.app _).op)
    (cochainPairingShortComplexIso' k T J pairingJ E dJ supportJ outsideJ).hom
    (cochainPairingShortComplexIso' k T K pairingK E dK supportK outsideK).hom
    left (cochainPairingShortComplexIso'_target_naturality k T J K pairingJ pairingK dJ dK h
      compatible supportJ outsideJ supportK outsideK E) right.symm

theorem finiteCochainSerreHomologyIso_target_naturality :
    HomologicalComplex.homologyMap (linearHomComplexMap k E h) 0 ≫
        (finiteCochainSerreHomologyIso k T K pairingK E dK supportK outsideK).hom =
      (finiteCochainSerreHomologyIso k T J pairingJ E dJ supportJ outsideJ).hom ≫
        (scalarDual k).map
          (HomologicalComplex.homologyMap
            (linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E) 0).op := by
  have hH := congrArg ((ShortComplex.homologyFunctor (ModuleCat.{u} k)).map)
    (cochainPairingShortComplexIso_target_naturality k T J K pairingJ pairingK dJ dK h
      compatible supportJ outsideJ supportK outsideK E)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hH
  change HomologicalComplex.homologyMap (linearHomComplexMap k E h) 0 ≫
      ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T K pairingK E dK supportK outsideK).hom =
    ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairingJ E dJ supportJ outsideJ).hom ≫
      ShortComplex.homologyMap ((scalarDual k).mapShortComplex.map
        (ShortComplex.opMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (.up ℤ) 0).map
            (linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E)))) at hH
  change HomologicalComplex.homologyMap (linearHomComplexMap k E h) 0 ≫
      (ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T K pairingK E dK supportK outsideK).hom ≫
        (shortComplexDualHomologyIso k
          ((linearHomComplex k (mappedCochainComplex T K) E).sc 0)).hom) =
    (ShortComplex.homologyMap
        (cochainPairingShortComplexIso k T J pairingJ E dJ supportJ outsideJ).hom ≫
        (shortComplexDualHomologyIso k
          ((linearHomComplex k (mappedCochainComplex T J) E).sc 0)).hom) ≫ _
  rw [← Category.assoc, hH, Category.assoc,
    shortComplexDualHomologyIso_naturality, Category.assoc]
  rfl

end ToricPower.SerrePairing

end
