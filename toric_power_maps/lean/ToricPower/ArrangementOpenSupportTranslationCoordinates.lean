module

public import ToricPower.ArrangementOpenSupportTranslation
public import ToricPower.ArrangementOpenSupportCoordinates

/-!
# Translation in the actual supported characteristic-cell basis

The chain map is inverse translation and partial coefficient restriction.
On finite cell supports its scalar dual is translation followed by
extension by zero. Every coefficient is computed from the original
characteristic disks, including cells absorbed by the complementary base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  {U V : OpenCellSupport A} (z : Fin n → ℤ)
  (h : translatedRegion (U.val : Set (Fin n → ℝ)) (latticeLift z) ⊆ V.val)

local instance : CWComplex (arrangementCarrier A) := periodicArrangementCWComplex A

/-- Actual lattice translation on the cells in the support. Cellwise
membership, rather than equivariance of an arbitrary chosen center,
justifies membership of the translated center. -/
def openSupportCellTranslation (q : ℕ) :
    OpenSupportCell A U q → OpenSupportCell A V q := fun c =>
  ⟨translateCell A z c.val, by
    have shifted : cellCenter (augmentedForms A) c.val + latticeLift z ∈
        cell (augmentedForms A) (translateCell A z c.val).val.1
          (translateCell A z c.val).val.2 :=
      (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A z) _).mpr
        (cellCenter_mem _ c.val)
    exact (V.property _ _ shifted (cellCenter_mem _ _)).mp (h ⟨_, c.property, rfl⟩)⟩

@[simp]
theorem openSupportCellTranslation_val (q : ℕ) (c : OpenSupportCell A U q) :
    (openSupportCellTranslation A z h q c).val = translateCell A z c.val := rfl

theorem openSupportCellTranslation_injective (q : ℕ) :
    Function.Injective (openSupportCellTranslation A z h q) := by
  intro c d equal
  apply Subtype.ext
  exact (translationCellEquiv A z q).injective
    (congrArg (fun p : OpenSupportCell A V q => p.val) equal)

/-- Inverse translation hits a supported source cell precisely at its
literal translated image. -/
theorem openSupportCellTranslation_iff (q : ℕ)
    (i : OpenSupportCell A V q) (j : OpenSupportCell A U q) :
    translateCell A (-z) i.val = j.val ↔ i = openSupportCellTranslation A z h q j := by
  constructor
  · intro equal
    apply Subtype.ext
    change i.val = translateCell A z j.val
    have translated := congrArg (translateCell A z) equal
    simpa only [translateCell_add, neg_add_cancel, translateCell_zero] using translated
  · rintro rfl
    simp only [openSupportCellTranslation_val, translateCell_add, add_neg_cancel,
      translateCell_zero]

variable (R : Type) [Ring R]

/-- Literal coefficient restriction along the injective translated-cell
map, with zero automatically imposed on absorbed cells. -/
def openSupportTranslationLinear (q : ℕ) :
    (OpenSupportCell A V q →₀ R) →ₗ[R] (OpenSupportCell A U q →₀ R) :=
  Finsupp.lcomapDomain (openSupportCellTranslation A z h q)
    (openSupportCellTranslation_injective A z h q)

/-- The original relative chain map has exactly the translated
Kronecker coefficients. -/
theorem openSupportChainGroupTranslation_coefficient (q : ℕ)
    (i : OpenSupportCell A V q) (j : OpenSupportCell A U q) :
    (openSupportBasis A R U q).repr
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (openSupportComplement A V))
          (relativeCWCarrier (openSupportComplement A U))
          (relativeCWMap_cellular (openSupportComplement A V) (openSupportComplement A U)
            (arrangementTranslation A (-z))
            (arrangementTranslation_cellular A (-z))
            (openSupportChainTranslation_base A z h))
          (ModuleCat.of R R) q (openSupportBasis A R V q i)) j =
      if i = openSupportCellTranslation A z h q j then 1 else 0 := by
  simp only [openSupportBasis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  refine (relativeCWChainGroupMap_basis_coefficient
    (arrangementCarrier A) (arrangementCarrier A)
    (openSupportComplement A V) (openSupportComplement A U)
    (arrangementTranslation A (-z)) (arrangementTranslation_cellular A (-z))
    (openSupportChainTranslation_base A z h) R q
    ((openSupportCellEquiv A V q).symm i)
    ((openSupportCellEquiv A U q).symm j) (translateCell A (-z) i.val)
    (arrangementTranslation_characteristic A (-z) q _)).trans ?_
  have same : translateCell A (-z) i.val = ((openSupportCellEquiv A U q).symm j).val ↔
      i = openSupportCellTranslation A z h q j :=
    openSupportCellTranslation_iff A z h q i j
  by_cases equal : i = openSupportCellTranslation A z h q j
  · rw [if_pos (same.mpr equal), if_pos equal]
  · rw [if_neg (fun h' => equal (same.mp h')), if_neg equal]

/-- The entire actual cellular group map in its original basis. -/
theorem openSupportChainGroupTranslation_coordinates (q : ℕ) :
    (openSupportBasis A R U q).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (openSupportComplement A V))
          (relativeCWCarrier (openSupportComplement A U))
          (relativeCWMap_cellular (openSupportComplement A V) (openSupportComplement A U)
            (arrangementTranslation A (-z))
            (arrangementTranslation_cellular A (-z))
            (openSupportChainTranslation_base A z h))
          (ModuleCat.of R R) q).hom =
      (openSupportTranslationLinear A z h R q).comp
        (openSupportBasis A R V q).repr.toLinearMap := by
  apply (openSupportBasis A R V q).ext
  intro i
  ext j
  change (openSupportBasis A R U q).repr
      (TauCeti.cellularChainGroupMap _ _ _ (ModuleCat.of R R) q
        (openSupportBasis A R V q i)) j =
    openSupportTranslationLinear A z h R q
      ((openSupportBasis A R V q).repr (openSupportBasis A R V q i)) j
  rw [openSupportChainGroupTranslation_coefficient, Module.Basis.repr_self]
  change (if i = openSupportCellTranslation A z h q j then (1 : R) else 0) =
    Finsupp.single i (1 : R) (openSupportCellTranslation A z h q j)
  simp only [Finsupp.single_apply]

/-- The chain-complex coordinate formula includes all canonical
transports from actual cellular chain groups to actual chain terms. -/
theorem openSupportChainTranslation_coordinates (q : ℕ)
    (v : (openSupportChainComplex A (ModuleCat.of R R) V).X q) :
    openSupportChainCoordinates A R U q
        ((openSupportChainTranslation A z h (ModuleCat.of R R)).f q v) =
      openSupportTranslationLinear A z h R q (openSupportChainCoordinates A R V q v) := by
  let C := relativeCWCarrier (openSupportComplement A V)
  let D := relativeCWCarrier (openSupportComplement A U)
  let hf := relativeCWMap_cellular (openSupportComplement A V) (openSupportComplement A U)
            (arrangementTranslation A (-z))
    (arrangementTranslation_cellular A (-z)) (openSupportChainTranslation_base A z h)
  have square : (openSupportChainTranslation A z h (ModuleCat.of R R)).f q ≫
      eqToHom (TauCeti.cellularChainComplex_X D (ModuleCat.of R R) q) =
    eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) ≫
      TauCeti.cellularChainGroupMap C D hf (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplexMap C D hf (ModuleCat.of R R)).f q ≫ _ = _
    rw [TauCeti.cellularChainComplexMap_f]
    simp
  exact (congrArg (openSupportBasis A R U q).repr
    (ConcreteCategory.congr_hom square v)).trans
      (DFunLike.congr_fun (openSupportChainGroupTranslation_coordinates A z h R q)
        (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) v))

section Field

variable (k : Type) [Field k]

/-- On proved finite supports, the actual cochain map is precisely
translation followed by extension by zero. -/
theorem openSupportCochainTranslation_coordinates (q : ℕ)
    [Finite (OpenSupportCell A U q)] [Finite (OpenSupportCell A V q)]
    (φ : (openSupportCochainComplex A k U).X q) :
    openSupportCochainCoordinates A k V q
        ((openSupportCochainTranslation A z h k).f q φ) =
      Finsupp.mapDomain (openSupportCellTranslation A z h q)
        (openSupportCochainCoordinates A k U q φ) := by
  let eU := (openSupportChainCoordinates A k U q).toModuleIso
  let eV := (openSupportChainCoordinates A k V q).toModuleIso
  have conjugate : eV.inv ≫ (openSupportChainTranslation A z h (ModuleCat.of k k)).f q =
      ModuleCat.ofHom (openSupportTranslationLinear A z h k q) ≫ eU.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply (openSupportChainCoordinates A k U q).injective
    change openSupportChainCoordinates A k U q
        ((openSupportChainTranslation A z h (ModuleCat.of k k)).f q
          ((openSupportChainCoordinates A k V q).symm v)) =
      openSupportChainCoordinates A k U q
        ((openSupportChainCoordinates A k U q).symm
          (openSupportTranslationLinear A z h k q v))
    rw [openSupportChainTranslation_coordinates, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  change finiteFreeScalarDualEquiv k _
      ((eV.inv ≫ ((openSupportChainTranslation A z h (ModuleCat.of k k)).f q ≫ φ)) ≫ 𝟙 _) =
    Finsupp.mapDomain (openSupportCellTranslation A z h q)
      (finiteFreeScalarDualEquiv k _ ((eU.inv ≫ φ) ≫ 𝟙 _))
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, conjugate, Category.assoc]
  exact finiteFreeScalarDualEquiv_comapDomain k
    (openSupportCellTranslation A z h q) (openSupportCellTranslation_injective A z h q)
    (eU.inv ≫ φ)

end Field
end ToricPower.IntegralArrangement
