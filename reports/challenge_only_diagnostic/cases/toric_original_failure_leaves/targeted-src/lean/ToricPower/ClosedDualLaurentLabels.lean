module

public import ToricPower.ClosedSliceDualRegion
public import ToricPower.ArrangementClosedSubtorus
public import ToricPower.ArrangementLaurentLabels

/-! # The full Laurent diagram in the dual closed-slice calculation

The coefficient at a cell is the literal inverse-label monomial module,
with the original line-bundle coefficient added. Contravariant incidence
maps add the actual incidence character. The resulting indices are all
original universal cells in the closed weak-inequality region.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s)) (b : Fin s → ℤ)

def DualLaurentWeight (c : IncidenceObject A) :=
  {m : Fin n → ℤ // ∀ r ∈ S,
    reflectedCeiling A c.2.val r ≤ rayPairing A m r+b r}

def dualLaurentWeightMap {c d : IncidenceObject A} (f : c ⟶ d) :
    DualLaurentWeight A S b d → DualLaurentWeight A S b c :=
  fun m => ⟨m.val+f.val,by
    intro r member
    have original := m.property r member
    have multiplier := (incidence_ceiling_bounds A f r).1
    rw [rayPairing_add]
    omega⟩

def ClosedDualLaurentCellIndex (c : IncidenceObject A) :=
  Σ _ : PLift (closedIntegralRowsSupport A selected c), DualLaurentWeight A S b c

def closedDualLaurentIndexMap {c d : IncidenceObject A} (f : c ⟶ d) :
    ClosedDualLaurentCellIndex A selected S b d →
      ClosedDualLaurentCellIndex A selected S b c :=
  fun p => ⟨⟨closedIntegralRowsSupport_incidence A selected f p.1.down⟩,
    dualLaurentWeightMap A S b f p.2⟩

@[simp]
theorem closedDualLaurentIndexMap_id (c : IncidenceObject A) :
    closedDualLaurentIndexMap A selected S b (𝟙 c) = id := by
  funext p
  rcases p with ⟨⟨supported⟩,m⟩
  dsimp only [closedDualLaurentIndexMap,Function.id_def]
  apply Sigma.ext (Subsingleton.elim _ _)
  apply heq_of_eq
  apply Subtype.ext
  change m.val+0=m.val
  exact add_zero _

@[simp]
theorem closedDualLaurentIndexMap_comp {c d e : IncidenceObject A}
    (f : c ⟶ d) (g : d ⟶ e) :
    closedDualLaurentIndexMap A selected S b (f ≫ g) =
      closedDualLaurentIndexMap A selected S b f ∘
        closedDualLaurentIndexMap A selected S b g := by
  funext p
  dsimp only [closedDualLaurentIndexMap,Function.comp_apply]
  apply Sigma.ext (Subsingleton.elim _ _)
  apply heq_of_eq
  apply Subtype.ext
  change p.2.val+(f.val+g.val)=(p.2.val+g.val)+f.val
  abel

variable (k : Type) [CommRing k]

/-- Every actual allowed character and every actual incidence, with
no cutoff on the full lattice or its parallel components. -/
def closedDualLaurentDiagram : (IncidenceObject A)ᵒᵖ ⥤ ModuleCat.{0} k where
  obj c := ModuleCat.of k (ClosedDualLaurentCellIndex A selected S b c.unop →₀ k)
  map f := ModuleCat.ofHom
    (Finsupp.lmapDomain k k (closedDualLaurentIndexMap A selected S b f.unop))
  map_id c := by
    rw [unop_id,closedDualLaurentIndexMap_id,Finsupp.lmapDomain_id]
    rfl
  map_comp f g := by
    rw [unop_comp,closedDualLaurentIndexMap_comp,Finsupp.lmapDomain_comp]
    rfl

@[simp]
theorem closedDualLaurentDiagram_map_single {c d : IncidenceObject A}
    (f : c ⟶ d) (p : ClosedDualLaurentCellIndex A selected S b d) (r : k) :
    (closedDualLaurentDiagram A selected S b k).map f.op (Finsupp.single p r) =
      Finsupp.single (closedDualLaurentIndexMap A selected S b f p) r :=
  Finsupp.mapDomain_single

omit k in
theorem translatedCell_closedLower_iff {q : ℕ} (c : NormalizedCell A q)
    (m : Fin n → ℤ) :
    cellCenter (augmentedForms A) (translateCell A m c.val) ∈
        closedLowerWeightRegion A S (fun r => -b r) ↔
      ∀ r ∈ S, reflectedCeiling A c.val r ≤ rayPairing A m r+b r := by
  rw [closedLowerWeightRegion_cell_iff A S (fun r => -b r)
    (translateCell A m c.val) (cellCenter_mem _ _)]
  apply forall₂_congr
  intro r member
  rw [reflectedCeiling_translate,neg_neg]
  omega

omit k in
def ClosedDualSupportCell (q : ℕ) :=
  {c : Cell (augmentedForms A) q // selected ⊆ c.val.2 ∧
    cellCenter (augmentedForms A) c ∈ closedLowerWeightRegion A S (fun r => -b r)}

omit k in
/-- The positive translation is forced by contravariant label Hom.
It keeps the original universal-cell characteristic disks. -/
def closedDualLaurentCellEquiv (q : ℕ) :
    (Σ c : NormalizedCell A q, ClosedDualLaurentCellIndex A selected S b ⟨q,c⟩) ≃
      ClosedDualSupportCell A selected S b q := by
  let first : (Σ c : NormalizedCell A q, ClosedDualLaurentCellIndex A selected S b ⟨q,c⟩) ≃
      {p : NormalizedCell A q × (Fin n → ℤ) //
        closedIntegralRowsSupport A selected ⟨q,p.1⟩ ∧
          ∀ r ∈ S, reflectedCeiling A p.1.val r ≤ rayPairing A p.2 r+b r} :=
    { toFun := fun p => ⟨⟨p.1,p.2.2.val⟩,p.2.1.down,p.2.2.property⟩
      invFun := fun p => ⟨p.val.1,⟨⟨p.property.1⟩,⟨p.val.2,p.property.2⟩⟩⟩
      left_inv := fun p => by rcases p with ⟨c,⟨h⟩,m,hm⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨c,m⟩,hc,hm⟩; rfl }
  refine first.trans ((cellOrbitEquiv A q).symm.subtypeEquiv ?_)
  intro p
  change (closedIntegralRowsSupport A selected ⟨q,p.1⟩ ∧ _) ↔
    (selected ⊆ (translateCell A p.2 p.1.val).val.2 ∧ _)
  exact and_congr Iff.rfl (translatedCell_closedLower_iff A S b p.1 p.2).symm

end ToricPower.IntegralArrangement

end
