module

public import ToricPower.CellularDependency08
public import ToricPower.ArrangementEquivariant

/-! # Incidence numbers from actual equivariant characteristic maps

The cellular differential is the relative singular-homology connecting map.
Its naturality, together with an equality of actual characteristic maps,
therefore transports cellular basis vectors and their incidence coefficients.
For the integral arrangement the required equality is proved from literal
lattice translation of the chosen disk parameter.

Candidate until the complete dependency closure compiles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower

section Naturality

universe w

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]
  {f : TopCat.of C ⟶ TopCat.of C'} (hf : TauCeti.IsCellular C C' f)
  (R : Type w) [Ring R]

/-- The actual pair-map equality transports the fundamental class, with no
independently postulated choice of boundary signs. -/
theorem cellularChainGroupMap_basis_of_characteristic {d : ℕ}
    (j : cell C d) (j' : cell C' d)
    (hχ : TauCeti.characteristicCellPairMap C j ≫
      TauCeti.skeletonPairMap C C' hf d = TauCeti.characteristicCellPairMap C' j') :
    TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d
      (TauCeti.cellularChainBasis C R d j) =
      TauCeti.cellularChainBasis C' R d j' := by
  have hmap :
      Sigma.ι (fun _ : cell C d => ModuleCat.of R R) j ≫
        (TauCeti.cellularChainGroupIso C (ModuleCat.of R R) d).inv ≫
        TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d =
      Sigma.ι (fun _ : cell C' d => ModuleCat.of R R) j' ≫
        (TauCeti.cellularChainGroupIso C' (ModuleCat.of R R) d).inv := by
    rw [← Category.assoc,
      TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
      TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap,
      Category.assoc, TauCeti.cellularChainGroupMap_def]
    congr 1
    rw [TopPair.singularHomologyMap, TopPair.singularHomologyMap,
      ← SSetPair.homologyMap_comp, ← Functor.map_comp, hχ]
  simpa only [ConcreteCategory.comp_apply, TauCeti.cellularChainBasis_apply] using
    ConcreteCategory.congr_hom hmap (1 : R)

/-- Coordinates transform by the actual induced cell bijection. -/
theorem cellularChainGroupMap_coordinates (e : ∀ d, cell C d ≃ cell C' d)
    (hχ : ∀ d j, TauCeti.characteristicCellPairMap C j ≫
      TauCeti.skeletonPairMap C C' hf d =
        TauCeti.characteristicCellPairMap C' (e d j))
    (d : ℕ) (v : (TauCeti.cellularChainGroup C (ModuleCat.of R R) d : ModuleCat R)) :
    (TauCeti.cellularChainBasis C' R d).repr
      (TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d v) =
        (Finsupp.domLCongr (e d) : (cell C d →₀ R) ≃ₗ[R] (cell C' d →₀ R))
          ((TauCeti.cellularChainBasis C R d).repr v) := by
  have hlin :
      (TauCeti.cellularChainBasis C' R d).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap C C' hf (ModuleCat.of R R) d).hom =
      (Finsupp.domLCongr (e d) : (cell C d →₀ R) ≃ₗ[R] (cell C' d →₀ R)).toLinearMap.comp
        (TauCeti.cellularChainBasis C R d).repr.toLinearMap := by
    apply (TauCeti.cellularChainBasis C R d).ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      cellularChainGroupMap_basis_of_characteristic C C' hf R j (e d j) (hχ d j),
      Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact DFunLike.congr_fun hlin v

/-- Cellular incidence is invariant under a cellular bijection which keeps
the literal characteristic-disk parameter. -/
theorem cellularIncidence_natural (e : ∀ d, cell C d ≃ cell C' d)
    (hχ : ∀ d j, TauCeti.characteristicCellPairMap C j ≫
      TauCeti.skeletonPairMap C C' hf d =
        TauCeti.characteristicCellPairMap C' (e d j))
    (d : ℕ) (a : cell C d) (b : cell C (d+1)) :
    TauCeti.cellularIncidence C' R d (e d a) (e (d+1) b) =
      TauCeti.cellularIncidence C R d a b := by
  have hd := ConcreteCategory.congr_hom
    (TauCeti.cellularChainGroupMap_comp_cellularDifferential C C' hf
      (ModuleCat.of R R) d) (TauCeti.cellularChainBasis C R (d+1) b)
  simp only [ConcreteCategory.comp_apply,
    cellularChainGroupMap_basis_of_characteristic C C' hf R b
      (e (d+1) b) (hχ (d+1) b)] at hd
  rw [TauCeti.cellularIncidence_def, hd,
    cellularChainGroupMap_coordinates C C' hf R e hχ]
  simpa only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, TauCeti.cellularIncidence_def] using
      (rfl : TauCeti.cellularIncidence C R d a b =
        TauCeti.cellularIncidence C R d a b)

end Naturality

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

def translationCellEquiv (z : Fin n → ℤ) (d : ℕ) :
    Cell (augmentedForms A) d ≃ Cell (augmentedForms A) d where
  toFun := translateCell A z
  invFun := translateCell A (-z)
  left_inv c := by simp only [translateCell_add, add_neg_cancel, translateCell_zero]
  right_inv c := by simp only [translateCell_add, neg_add_cancel, translateCell_zero]

/-- The literal continuous translation on the carrier of the actual CW
complex, with its ordinary Euclidean topology. -/
def arrangementTranslation (_A : Fin s → Fin n → ℤ) (z : Fin n → ℤ) :
    TopCat.of (Set.univ : Set (Fin n → ℝ)) ⟶
      TopCat.of (Set.univ : Set (Fin n → ℝ)) :=
  TopCat.ofHom ⟨fun x => ⟨x.val + latticeLift z, Set.mem_univ _⟩,
    (continuous_subtype_val.add continuous_const).subtype_mk _⟩

theorem arrangementTranslation_cellular (z : Fin n → ℤ) :
    letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
    TauCeti.IsCellular (Set.univ : Set (Fin n → ℝ))
      (Set.univ : Set (Fin n → ℝ)) (arrangementTranslation A z) := by
  letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
  intro m x hx
  obtain ⟨d, hd, c, hc⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  apply CWComplex.mem_skeletonLT_iff.mpr
  refine ⟨d, hd, translateCell A z c, ?_⟩
  change x.val ∈ periodicCellMap A c '' Metric.ball 0 1 at hc
  obtain ⟨v, hv, he⟩ := hc
  change x.val + latticeLift z ∈
    periodicCellMap A (translateCell A z c) '' Metric.ball 0 1
  exact ⟨v, hv, by rw [periodicCellMap_translate, he]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The translated characteristic map is equality of actual topological
pairs, not merely an equality of their image sets. -/
theorem arrangementTranslation_characteristic (z : Fin n → ℤ) (d : ℕ)
    (c : Cell (augmentedForms A) d) :
    letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
    TauCeti.characteristicCellPairMap (Set.univ : Set (Fin n → ℝ)) c ≫
      TauCeti.skeletonPairMap _ _ (arrangementTranslation_cellular A z) d =
    TauCeti.characteristicCellPairMap (Set.univ : Set (Fin n → ℝ))
      (translateCell A z c) := by
  letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
  apply TopPair.hom_ext_of_fst
  rw [TopPair.Hom.fst_comp, TauCeti.skeletonPairMap_fst]
  ext x
  erw [ConcreteCategory.comp_apply]
  apply Subtype.ext
  let y : TauCeti.skeletonObj (Set.univ : Set (Fin n → ℝ)) (d + 1) :=
    TopPair.Hom.fst (TauCeti.characteristicCellPairMap (Set.univ : Set (Fin n → ℝ)) c) x
  let v := (EuclideanSpace.equiv (Fin d) ℝ).unitBallHomeomorph (x : TopCat.disk d).down
  have sourceValue : (y : Fin n → ℝ) = periodicCellMap A c v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply (Set.univ : Set (Fin n → ℝ)) c x
  have targetValue :
      ((TopPair.Hom.fst (TauCeti.characteristicCellPairMap
        (Set.univ : Set (Fin n → ℝ)) (translateCell A z c))) x).val =
      periodicCellMap A (translateCell A z c) v :=
    TauCeti.coe_characteristicCellPairMap_fst_apply
      (Set.univ : Set (Fin n → ℝ)) (translateCell A z c) x
  have translatedValue := congrArg Subtype.val
    (TauCeti.skeletonMap_apply (Set.univ : Set (Fin n → ℝ))
      (Set.univ : Set (Fin n → ℝ)) (arrangementTranslation_cellular A z) (d + 1) y)
  change _ = (y : Fin n → ℝ) + latticeLift z at translatedValue
  exact translatedValue.trans ((congrArg (fun w => w + latticeLift z) sourceValue).trans
    ((periodicCellMap_translate A z c v).symm.trans targetValue.symm))

/-- The genuine cellular incidence coefficients of the augmented integral
arrangement are invariant under every lattice translation. -/
theorem arrangement_cellularIncidence_translate (R : Type) [Ring R]
    (z : Fin n → ℤ) (d : ℕ) (a : Cell (augmentedForms A) d)
    (b : Cell (augmentedForms A) (d+1)) :
    letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
    TauCeti.cellularIncidence (Set.univ : Set (Fin n → ℝ)) R d
      (translateCell A z a) (translateCell A z b) =
      TauCeti.cellularIncidence (Set.univ : Set (Fin n → ℝ)) R d a b := by
  letI : CWComplex (Set.univ : Set (Fin n → ℝ)) := periodicArrangementCWComplex A
  exact cellularIncidence_natural _ _ (arrangementTranslation_cellular A z) R
    (translationCellEquiv A z) (arrangementTranslation_characteristic A z) d a b

end IntegralArrangement

end ToricPower
