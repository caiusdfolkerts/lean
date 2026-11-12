module

public import ToricPower.ArrangementIncidenceCategory
public import ToricPower.DiagonalGlobalSquare
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Cellular complexes with genuine incidence-diagram coefficients

Each nonzero periodic cellular incidence determines a literal translated
face inclusion. Applying an arbitrary coefficient functor to those actual
arrows gives the cellular differential. Its square is zero because the
original periodic incidence columns satisfy the proved convolution law.

The construction is functorial in the complete coefficient diagram. In
particular, it can be applied to a covariant diagram of actual Cartier
sheaves tensored with an arbitrary cellular vector-space diagram. No
resolution, exactness, or reconstruction premise is built into it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Topology Set
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

universe v u

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance cellularCoefficientPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

/-- The geometric incidence condition for a specified translation. -/
def IncidenceTranslation (c d : IncidenceObject A) (a : Fin n → ℤ) : Prop :=
  ∀ x ∈ incidenceClosedCell A c, x + latticeLift a ∈ incidenceClosedCell A d

/-- Nonzero cellular incidence implies inclusion of the entire closed
face, so it determines an arrow of the actual incidence category. -/
theorem incidenceTranslation_of_column_ne_zero
    (k : Type) [Ring k] (q : ℕ) (j : NormalizedCell A (q + 1))
    (i : NormalizedCell A q) (a : Fin n → ℤ)
    (nonzero : diagonalGlobalColumn k A q j (i, a) ≠ 0) :
    IncidenceTranslation A ⟨q, i⟩ ⟨q + 1, j⟩ a := by
  have actual : TauCeti.cellularIncidence (arrangementCarrier A) k q
      (translateCell A a i.val) j.val ≠ 0 := by
    rwa [diagonalGlobalColumn_apply] at nonzero
  apply (incidence_mem_iff_closedCell_subset A ⟨q, i⟩ ⟨q + 1, j⟩ a).mpr
  rw [← closure_cell (augmentedForms A)
    (fun r => (augmentedForms A r).continuous_of_finiteDimensional)
    (translateCell A a i.val).val.1 (translateCell A a i.val).val.2
    (translateCell A a i.val).property.1]
  exact closure_minimal
    (fun _ h => point_mem_closedCell_of_incidence_ne_zero A k
      (translateCell A a i.val) j.val actual h)
    (closedCell_isClosed (augmentedForms A)
      (fun r => (augmentedForms A r).continuous_of_finiteDimensional)
      j.val.val.1 j.val.val.2)

/-- Composition is literal addition of the two incidence translations. -/
theorem incidenceTranslation_comp {c d e : IncidenceObject A}
    {a b : Fin n → ℤ} (ha : IncidenceTranslation A d e a)
    (hb : IncidenceTranslation A c d b) : IncidenceTranslation A c e (a + b) := by
  intro x hx
  have h := ha _ (hb x hx)
  rw [latticeLift_add, add_comm (latticeLift a) (latticeLift b), ← add_assoc]
  exact h

variable (k : Type) [CommRing k]
  {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B]
  [HasFiniteBiproducts B]
  (P : (IncidenceObject A)ᵒᵖ ⥤ B)

local instance cellularCoefficientCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- An actual coefficient map for each lattice translation; a vector
which is not a geometric incidence contributes zero. -/
def cellularCoefficientHom {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ) :
    P.obj (op ⟨e, j⟩) ⟶ P.obj (op ⟨d, i⟩) :=
  if h : IncidenceTranslation A ⟨d, i⟩ ⟨e, j⟩ a then
    P.map (Quiver.Hom.op (⟨a, h⟩ : (⟨d, i⟩ : IncidenceObject A) ⟶ ⟨e, j⟩))
  else 0

/-- The supported coefficient maps compose by the actual functor law. -/
theorem cellularCoefficientHom_comp {d e r : ℕ}
    (j : NormalizedCell A r) (i : NormalizedCell A e) (h : NormalizedCell A d)
    (a b : Fin n → ℤ)
    (ha : IncidenceTranslation A ⟨e, i⟩ ⟨r, j⟩ a)
    (hb : IncidenceTranslation A ⟨d, h⟩ ⟨e, i⟩ b) :
    cellularCoefficientHom A P j i a ≫ cellularCoefficientHom A P i h b =
      cellularCoefficientHom A P j h (a + b) := by
  rw [cellularCoefficientHom, dif_pos ha, cellularCoefficientHom, dif_pos hb,
    cellularCoefficientHom, dif_pos (incidenceTranslation_comp A ha hb)]
  rw [← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun f : (⟨d, h⟩ : IncidenceObject A) ⟶ ⟨r, j⟩ => P.map f.op)
    (Subtype.ext (add_comm b a))

/-- The finite sum of genuine coefficient objects in a cellular degree. -/
def arrangementCellularTerm (q : ℕ) : B :=
  ⨁ fun i : NormalizedCell A q => P.obj (op ⟨q, i⟩)

/-- The original geometric finite-support column, evaluated in the
actual coefficient functor. -/
def arrangementCellularColumn (q : ℕ) (j : NormalizedCell A (q + 1)) :
    P.obj (op ⟨q + 1, j⟩) ⟶ arrangementCellularTerm A P q :=
  Finsupp.linearCombination k
    (fun p : NormalizedCell A q × (Fin n → ℤ) =>
      cellularCoefficientHom A P j p.1 p.2 ≫
        biproduct.ι (fun i : NormalizedCell A q => P.obj (op ⟨q, i⟩)) p.1)
    (diagonalGlobalColumn k A q j)

/-- The actual cellular boundary with arbitrary contravariant labels. -/
def arrangementCellularBoundary (q : ℕ) :
    arrangementCellularTerm A P (q + 1) ⟶ arrangementCellularTerm A P q :=
  biproduct.desc (arrangementCellularColumn A k P q)

@[reassoc]
theorem arrangementCellularBoundary_column (q : ℕ) (j : NormalizedCell A (q + 1)) :
    biproduct.ι (fun i : NormalizedCell A (q + 1) => P.obj (op ⟨q + 1, i⟩)) j ≫
        arrangementCellularBoundary A k P q = arrangementCellularColumn A k P q j := by
  simp only [arrangementCellularBoundary, biproduct.ι_desc]

/-- Square-zero follows from genuine cellular convolution, independently
of any properties of the coefficient functor beyond functoriality. -/
theorem arrangementCellularBoundary_square (q : ℕ) :
    arrangementCellularBoundary A k P (q + 1) ≫
      arrangementCellularBoundary A k P q = 0 := by
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, arrangementCellularBoundary_column, comp_zero]
  let w : (NormalizedCell A q × (Fin n → ℤ)) →
      (P.obj (op ⟨q + 2, j⟩) ⟶ arrangementCellularTerm A P q) :=
    fun p => cellularCoefficientHom A P j p.1 p.2 ≫
      biproduct.ι (fun i : NormalizedCell A q => P.obj (op ⟨q, i⟩)) p.1
  let evaluate := Finsupp.linearCombination k w
  have path (p : NormalizedCell A (q + 1) × (Fin n → ℤ))
      (hp : p ∈ (diagonalGlobalColumn k A (q + 1) j).support) :
      (cellularCoefficientHom A P j p.1 p.2 ≫
        biproduct.ι (fun i : NormalizedCell A (q + 1) => P.obj (op ⟨q + 1, i⟩)) p.1) ≫
          arrangementCellularBoundary A k P q =
        evaluate (Finsupp.mapDomain (fun r => (r.1, p.2 + r.2))
          (diagonalGlobalColumn k A q p.1)) := by
    rw [Category.assoc, arrangementCellularBoundary_column]
    change (Linear.leftComp k (arrangementCellularTerm A P q)
        (cellularCoefficientHom A P j p.1 p.2))
      (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q p.1)) = _
    erw [Finsupp.apply_linearCombination]
    change Finsupp.linearCombination k
        (fun r : NormalizedCell A q × (Fin n → ℤ) =>
          cellularCoefficientHom A P j p.1 p.2 ≫
            cellularCoefficientHom A P p.1 r.1 r.2 ≫
              biproduct.ι (fun i : NormalizedCell A q => P.obj (op ⟨q, i⟩)) r.1)
        (diagonalGlobalColumn k A q p.1) =
      Finsupp.linearCombination k w
        (Finsupp.mapDomain (fun r => (r.1, p.2 + r.2))
          (diagonalGlobalColumn k A q p.1))
    rw [Finsupp.linearCombination_mapDomain]
    simp only [Finsupp.linearCombination_apply]
    apply Finsupp.sum_congr
    intro r hr
    congr 1
    have ha := incidenceTranslation_of_column_ne_zero A k (q + 1)
      j p.1 p.2 (Finsupp.mem_support_iff.mp hp)
    have hb := incidenceTranslation_of_column_ne_zero A k q
      p.1 r.1 r.2 (Finsupp.mem_support_iff.mp hr)
    rw [← Category.assoc, cellularCoefficientHom_comp A P j p.1 r.1 p.2 r.2 ha hb]
    rfl
  calc
    arrangementCellularColumn A k P (q + 1) j ≫ arrangementCellularBoundary A k P q =
        (diagonalGlobalColumn k A (q + 1) j).sum (fun p r => r •
          ((cellularCoefficientHom A P j p.1 p.2 ≫
            biproduct.ι (fun i : NormalizedCell A (q + 1) => P.obj (op ⟨q + 1, i⟩)) p.1) ≫
            arrangementCellularBoundary A k P q)) := by
      change (Linear.rightComp k (P.obj (op ⟨q + 2, j⟩))
        (arrangementCellularBoundary A k P q))
          (Finsupp.linearCombination k _ (diagonalGlobalColumn k A (q + 1) j)) = _
      rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
      rfl
    _ = (diagonalGlobalColumn k A (q + 1) j).sum
        (fun p r => r • evaluate (Finsupp.mapDomain (fun t => (t.1, p.2 + t.2))
          (diagonalGlobalColumn k A q p.1))) := by
      apply Finsupp.sum_congr
      intro p hp
      rw [path p hp]
    _ = evaluate (diagonalGlobalComposedColumn k A q j) := by
      simp only [diagonalGlobalComposedColumn, map_finsuppSum, map_smul]
    _ = 0 := by rw [diagonalGlobalComposedColumn_eq_zero, map_zero]

/-- The finite cellular chain complex with every actual incidence map. -/
def arrangementCellularChainComplex : ChainComplex B ℕ :=
  ChainComplex.of (arrangementCellularTerm A P)
    (arrangementCellularBoundary A k P) (arrangementCellularBoundary_square A k P)

@[simp]
theorem arrangementCellularChainComplex_d (q : ℕ) :
    (arrangementCellularChainComplex A k P).d (q + 1) q =
      arrangementCellularBoundary A k P q := by
  change ChainComplex.of.d (arrangementCellularTerm A P)
    (arrangementCellularBoundary A k P) (q + 1) q = _
  exact ChainComplex.of_d _ _ q

variable {P} {Q : (IncidenceObject A)ᵒᵖ ⥤ B} (α : P ⟶ Q)

@[reassoc]
theorem cellularCoefficientHom_naturality {e d : ℕ}
    (j : NormalizedCell A e) (i : NormalizedCell A d) (a : Fin n → ℤ) :
    cellularCoefficientHom A P j i a ≫ α.app (op ⟨d, i⟩) =
      α.app (op ⟨e, j⟩) ≫ cellularCoefficientHom A Q j i a := by
  by_cases h : IncidenceTranslation A ⟨d, i⟩ ⟨e, j⟩ a
  · simp only [cellularCoefficientHom, dif_pos h]
    exact α.naturality (Quiver.Hom.op (⟨a, h⟩ : (⟨d, i⟩ : IncidenceObject A) ⟶ ⟨e, j⟩))
  · simp only [cellularCoefficientHom, dif_neg h, zero_comp, comp_zero]

/-- The actual termwise finite sum of the coefficient natural transformation. -/
def arrangementCellularTermMap (q : ℕ) :
    arrangementCellularTerm A P q ⟶ arrangementCellularTerm A Q q :=
  biproduct.map (fun i : NormalizedCell A q => α.app (op ⟨q, i⟩))

@[reassoc]
theorem arrangementCellularTermMap_ι (q : ℕ) (i : NormalizedCell A q) :
    biproduct.ι (fun i : NormalizedCell A q => P.obj (op ⟨q, i⟩)) i ≫
      arrangementCellularTermMap A α q =
    α.app (op ⟨q, i⟩) ≫
      biproduct.ι (fun i : NormalizedCell A q => Q.obj (op ⟨q, i⟩)) i := by
  simp only [arrangementCellularTermMap, biproduct.ι_map]

/-- Naturality of every actual incidence gives naturality of the full
finite column, with its original cellular coefficients. -/
theorem arrangementCellularColumn_naturality (q : ℕ)
    (j : NormalizedCell A (q + 1)) :
    arrangementCellularColumn A k P q j ≫ arrangementCellularTermMap A α q =
      α.app (op ⟨q + 1, j⟩) ≫ arrangementCellularColumn A k Q q j := by
  change (Linear.rightComp k (P.obj (op ⟨q + 1, j⟩))
      (arrangementCellularTermMap A α q))
      (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j)) =
    (Linear.leftComp k (arrangementCellularTerm A Q q) (α.app (op ⟨q + 1, j⟩)))
      (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j))
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
  apply congrArg (fun w : (NormalizedCell A q × (Fin n → ℤ)) →
    (P.obj (op ⟨q + 1, j⟩) ⟶ arrangementCellularTerm A Q q) =>
      Finsupp.linearCombination k w (diagonalGlobalColumn k A q j))
  funext p
  change (cellularCoefficientHom A P j p.1 p.2 ≫ _) ≫ _ = _
  rw [Category.assoc, arrangementCellularTermMap_ι,
    ← Category.assoc, cellularCoefficientHom_naturality, Category.assoc]
  rfl

/-- The actual boundary is natural for arbitrary coefficient diagrams. -/
theorem arrangementCellularBoundary_naturality (q : ℕ) :
    arrangementCellularBoundary A k P q ≫ arrangementCellularTermMap A α q =
      arrangementCellularTermMap A α (q + 1) ≫ arrangementCellularBoundary A k Q q := by
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, arrangementCellularBoundary_column,
    ← Category.assoc, arrangementCellularTermMap_ι, Category.assoc,
    arrangementCellularBoundary_column]
  exact arrangementCellularColumn_naturality A k α q j

/-- The induced morphism of the actual finite cellular complexes. -/
def arrangementCellularChainMap :
    arrangementCellularChainComplex A k P ⟶ arrangementCellularChainComplex A k Q :=
  ChainComplex.ofHom (arrangementCellularTermMap A α)
    (fun q => by
      rw [arrangementCellularChainComplex_d, arrangementCellularChainComplex_d]
      exact (arrangementCellularBoundary_naturality A k α q).symm)

/-- The complete cellular construction is a functor of actual coefficient diagrams. -/
def arrangementCellularChainFunctor :
    ((IncidenceObject A)ᵒᵖ ⥤ B) ⥤ ChainComplex B ℕ where
  obj := arrangementCellularChainComplex A k
  map := arrangementCellularChainMap A k
  map_id P := by
    ext q
    change arrangementCellularTermMap A (𝟙 P) q =
      𝟙 (arrangementCellularTerm A P q)
    apply biproduct.hom_ext'
    intro i
    simp only [arrangementCellularTermMap, biproduct.ι_map,
      NatTrans.id_app, Category.id_comp]
    exact (Category.comp_id _).symm
  map_comp α β := by
    ext q
    change arrangementCellularTermMap A (α ≫ β) q =
      arrangementCellularTermMap A α q ≫ arrangementCellularTermMap A β q
    apply biproduct.hom_ext'
    intro i
    simp only [arrangementCellularTermMap, biproduct.ι_map,
      NatTrans.comp_app, HomologicalComplex.comp_f, Category.assoc,
      biproduct.ι_map_assoc]

local instance cellularCoefficientOppositeBiproducts : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Covariant cellular cochains are the same actual incidence complex
in the opposite coefficient category, with all arrows reversed back. -/
def arrangementCellularCochainComplex (F : IncidenceObject A ⥤ B) :
    CochainComplex B ℕ :=
  (arrangementCellularChainComplex A k F.op).unop

/-- The covariant coefficient construction is functorial before any
derived localization or homology calculation. -/
def arrangementCellularCochainFunctor :
    (IncidenceObject A ⥤ B) ⥤ CochainComplex B ℕ := by
  let H : (IncidenceObject A ⥤ B)ᵒᵖ ⥤ ChainComplex Bᵒᵖ ℕ :=
    Functor.opHom (IncidenceObject A) B ⋙ arrangementCellularChainFunctor A k
  exact opOp (IncidenceObject A ⥤ B) ⋙ H.op ⋙
    HomologicalComplex.unopFunctor B (.down ℕ)

@[simp]
theorem arrangementCellularCochainFunctor_obj (F : IncidenceObject A ⥤ B) :
    (arrangementCellularCochainFunctor A k).obj F =
      arrangementCellularCochainComplex A k F := rfl

/-- The length bound follows from actual cell dimensions, without
truncating a larger complex or dropping any incidence. -/
theorem arrangementCellularChainComplex_isZero_X_above
    (P : (IncidenceObject A)ᵒᵖ ⥤ B) (q : ℕ) (above : n < q) :
    IsZero ((arrangementCellularChainComplex A k P).X q) := by
  rw [IsZero.iff_id_eq_zero]
  change (𝟙 (arrangementCellularTerm A P q)) = 0
  apply biproduct.hom_ext'
  intro i
  exact (not_lt_of_ge (cell_dimension_le A i.val) above).elim

/-- Covariant cellular cochains have the same genuine finite length. -/
theorem arrangementCellularCochainComplex_isZero_X_above
    (F : IncidenceObject A ⥤ B) (q : ℕ) (above : n < q) :
    IsZero ((arrangementCellularCochainComplex A k F).X q) :=
  (arrangementCellularChainComplex_isZero_X_above A k F.op q above).unop

end ToricPower.IntegralArrangement
