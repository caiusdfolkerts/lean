module

public import ToricPower.FiniteFunctorTotal
public import ToricPower.FiniteTwistedMap

/-!
# Functoriality of the actual finite signed total

Every coefficient chain map acts by its original maps on every
horizontal row. Both horizontal and vertical commutation are proved
before localization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive]

def rowMap {width : ℕ} {K L : CochainComplex A ℤ} (f : K ⟶ L) (q : Fin width) :
    row Φ K q ⟶ row Φ L q :=
  (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(q.val : ℤ))).map
    (((degree Φ q.val).mapHomologicalComplex (.up ℤ)).map f)

theorem transportedHorizontal_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (x y : ℤ) (p q : ℕ) (equality : x = y) :
    (Φ.map (f.f x)).f p ≫ transportedHorizontal Φ L x y p q equality =
      transportedHorizontal Φ K x y p q equality ≫ (Φ.map (f.f y)).f q := by
  subst equality
  simpa only [transportedHorizontal,eqToHom_refl,Category.comp_id] using
    (Φ.map (f.f x)).comm p q

theorem offEntry_naturality {width : ℕ} {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (a : ℤ) (p q : Fin width) :
    (rowMap Φ f p).f a ≫ offEntry Φ L a p q =
      offEntry Φ K a p q ≫ (rowMap Φ f q).f (a+1) := by
  classical
  unfold offEntry
  split_ifs with next
  · exact transportedHorizontal_naturality Φ f _ _ p.val q.val _
  · simp only [zero_comp,comp_zero]

theorem off_naturality {width : ℕ} {K L : CochainComplex A ℤ} (f : K ⟶ L) (a : ℤ) :
    FiniteTotal.mapTerm (row Φ K (width := width)) (row Φ L) (rowMap Φ f) a ≫ off Φ L a =
      off Φ K a ≫ FiniteTotal.mapTerm (row Φ K) (row Φ L) (rowMap Φ f) (a+1) := by
  simp only [FiniteTotal.mapTerm,off,biproduct.map_matrix,biproduct.matrix_map]
  congr 1
  funext p q
  exact offEntry_naturality Φ f a p q

/-- The literal morphism of finite total complexes. -/
def map (width : ℕ) {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    total Φ width K ⟶ total Φ width L :=
  FiniteTotal.map (row Φ K) (row Φ L) (off Φ K) (off Φ L)
    (off_coherent Φ K) (off_coherent Φ L) (rowMap Φ f) (off_naturality Φ f)

@[simp]
theorem map_f (width : ℕ) {K L : CochainComplex A ℤ} (f : K ⟶ L) (a : ℤ) :
    (map Φ width f).f a = biproduct.map (fun q : Fin width => (rowMap Φ f q).f a) := rfl

@[simp]
theorem rowMap_id {width : ℕ} (K : CochainComplex A ℤ) (q : Fin width) :
    rowMap Φ (𝟙 K) q = 𝟙 (row Φ K q) := by
  simp only [rowMap,CategoryTheory.Functor.map_id]

@[simp]
theorem rowMap_comp {width : ℕ} {K L M : CochainComplex A ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (q : Fin width) :
    rowMap Φ (f ≫ g) q = rowMap Φ f q ≫ rowMap Φ g q := by
  simp only [rowMap,Functor.map_comp]

/-- The actual finite signed total is functorial on all unbounded
coefficient complexes. -/
def functor (width : ℕ) : CochainComplex A ℤ ⥤ CochainComplex B ℤ where
  obj := total Φ width
  map := map Φ width
  map_id K := by
    apply HomologicalComplex.Hom.ext
    funext a
    apply biproduct.hom_ext
    intro q
    simp only [map_f,rowMap_id,HomologicalComplex.id_f,biproduct.map_π,
      Category.comp_id,Category.id_comp]
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext a
    apply biproduct.hom_ext
    intro q
    simp only [map_f,rowMap_comp,HomologicalComplex.comp_f,Category.assoc,
      biproduct.map_π,biproduct.map_π_assoc]

instance functor_additive (width : ℕ) : (functor Φ width).Additive where
  map_add {K L} f g := by
    apply HomologicalComplex.Hom.ext
    funext a
    apply biproduct.hom_ext
    intro q
    change (map Φ width (f+g)).f a ≫ biproduct.π _ q =
      ((map Φ width f).f a + (map Φ width g).f a) ≫ biproduct.π _ q
    simp only [map_f,rowMap,Functor.map_add,HomologicalComplex.add_f_apply,
      biproduct.map_π,add_comp,comp_add]

end ToricPower.FunctorTotal

end
