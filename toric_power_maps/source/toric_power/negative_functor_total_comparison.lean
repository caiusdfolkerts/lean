module

public import ToricPower.NegativeFunctorTotalMap

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  {Φ Ψ : A ⥤ ChainComplex B ℕ} [Φ.Additive] [Ψ.Additive]
  (τ : Φ ⟶ Ψ)

def coefficientRowMap {width : ℕ} (K : CochainComplex A ℤ) (q : Fin width) :
    row Φ K q ⟶ row Ψ K q :=
  (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (chainDegree q : ℤ)).map
    (((whiskerRight τ (HomologicalComplex.eval B (.down ℕ) (chainDegree q))).mapHomologicalComplex
      (.up ℤ)).app K)

@[simp]
theorem coefficientRowMap_f {width : ℕ} (K : CochainComplex A ℤ)
    (q : Fin width) (a : ℤ) :
    (coefficientRowMap τ K q).f a = (τ.app (K.X (a + (chainDegree q : ℤ)))).f (chainDegree q) := rfl

theorem transportedHorizontal_comparison (K : CochainComplex A ℤ)
    (x y : ℤ) (p q : ℕ) (equality : x = y) :
    (τ.app (K.X x)).f p ≫ transportedHorizontal Ψ K x y p q equality =
      transportedHorizontal Φ K x y p q equality ≫ (τ.app (K.X y)).f q := by
  subst equality
  simpa only [transportedHorizontal,eqToHom_refl,Category.comp_id] using
    (τ.app (K.X x)).comm p q

theorem offEntry_comparison {width : ℕ} (K : CochainComplex A ℤ)
    (a : ℤ) (p q : Fin width) :
    (coefficientRowMap τ K p).f a ≫ offEntry Ψ K a p q =
      offEntry Φ K a p q ≫ (coefficientRowMap τ K q).f (a+1) := by
  classical
  unfold offEntry
  split_ifs with next
  · exact transportedHorizontal_comparison τ K _ _ (chainDegree p) (chainDegree q) _
  · simp only [zero_comp,comp_zero]

theorem off_comparison {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ) :
    FiniteTotal.mapTerm (row Φ K (width := width)) (row Ψ K)
      (coefficientRowMap τ K) a ≫ off Ψ K a =
      off Φ K a ≫ FiniteTotal.mapTerm (row Φ K) (row Ψ K)
        (coefficientRowMap τ K) (a+1) := by
  simp only [FiniteTotal.mapTerm,off,biproduct.map_matrix,biproduct.matrix_map]
  congr 1
  funext p q
  exact offEntry_comparison τ K a p q

def coefficientMap (width : ℕ) (K : CochainComplex A ℤ) :
    total Φ width K ⟶ total Ψ width K :=
  FiniteTotal.map (row Φ K) (row Ψ K) (off Φ K) (off Ψ K)
    (off_coherent Φ K) (off_coherent Ψ K) (coefficientRowMap τ K) (off_comparison τ K)

@[simp]
theorem coefficientMap_f (width : ℕ) (K : CochainComplex A ℤ) (a : ℤ) :
    (coefficientMap τ width K).f a =
      biproduct.map (fun q : Fin width => (τ.app (K.X (a + (chainDegree q : ℤ)))).f (chainDegree q)) := rfl

theorem coefficientMap_f_rows (width : ℕ) (K : CochainComplex A ℤ) (a : ℤ) :
    (coefficientMap τ width K).f a =
      biproduct.map (fun q : Fin width => (coefficientRowMap τ K q).f a) := rfl

theorem coefficientRowMap_naturality {width : ℕ}
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : Fin width) :
    rowMap Φ f q ≫ coefficientRowMap τ L q =
      coefficientRowMap τ K q ≫ rowMap Ψ f q := by
  have h := congrArg
    ((CategoryTheory.shiftFunctor (CochainComplex B ℤ) (chainDegree q : ℤ)).map)
    (((whiskerRight τ (HomologicalComplex.eval B (.down ℕ) (chainDegree q))).mapHomologicalComplex
      (.up ℤ)).naturality f)
  simp only [Functor.map_comp] at h
  exact h

def comparison (width : ℕ) : functor Φ width ⟶ functor Ψ width where
  app K := coefficientMap τ width K
  naturality {K L} f := by
    apply HomologicalComplex.Hom.ext
    funext a
    apply biproduct.hom_ext
    intro q
    simp only [HomologicalComplex.comp_f,Category.assoc]
    change (map Φ width f).f a ≫ (coefficientMap τ width L).f a ≫ biproduct.π _ q =
      (coefficientMap τ width K).f a ≫ (map Ψ width f).f a ≫ biproduct.π _ q
    simp only [coefficientMap_f_rows,map_f,Category.assoc,biproduct.map_π,biproduct.map_π_assoc]
    have h := congrArg (fun h => biproduct.π (fun q : Fin width => (row Φ K q).X a) q ≫ h.f a)
      (coefficientRowMap_naturality τ f q)
    simp only [HomologicalComplex.comp_f,Category.assoc] at h
    exact h

/-- A natural isomorphism of coefficient chains induces an isomorphism of totals. -/
def comparisonIso (e : Φ ≅ Ψ) (width : ℕ) : functor Φ width ≅ functor Ψ width := by
  have components : ∀ K, IsIso ((comparison e.hom width).app K) := by
    intro K
    have degreeIso : ∀ a, IsIso (((comparison e.hom width).app K).f a) := by
      intro a
      change IsIso (biproduct.map (fun q : Fin width =>
        (e.hom.app (K.X (a+(chainDegree q : ℤ)))).f (chainDegree q)))
      exact (biproduct.mapIso (fun q : Fin width =>
        HomologicalComplex.Hom.isoApp (e.app (K.X (a+(chainDegree q : ℤ)))) (chainDegree q))).isIso_hom
    exact HomologicalComplex.Hom.isIso_of_components _
  letI := components
  letI := NatIso.isIso_of_isIso_app (comparison e.hom width)
  exact asIso (comparison e.hom width)

end ToricPower.NegativeFunctorTotal

end

