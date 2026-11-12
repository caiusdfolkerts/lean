module

public import ToricPower.ArrangementOpenSupport
public import ToricPower.CWRelativeCellularBasisMap
public import ToricPower.ArrangementRepresentableFunctor

/-!
# Literal coordinates and support maps of arrangement cochains

The relative characteristic-cell basis is reindexed by the actual cells
whose centers lie in the open support. The actual chain support map is
restriction of these coefficients. On finite supports its scalar dual
is consequently extension by zero. These formulas precede taking a
filtered colimit and justify its finite-support interpretation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local instance openCoordinatesPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

def OpenSupportCell (U : OpenCellSupport A) (q : ℕ) :=
  {c : Cell (augmentedForms A) q // cellCenter (augmentedForms A) c ∈ U.val}

/-- The actual relative-cell subtype is precisely the cells in the open
support; no closed-cell support condition is substituted. -/
def openSupportCellEquiv (U : OpenCellSupport A) (q : ℕ) :
    Topology.RelCWComplex.cell (relativeCWCarrier (openSupportComplement A U)) q ≃
      OpenSupportCell A U q where
  toFun c := ⟨c.val, by
    have h := c.property
    change ¬¬cellCenter (augmentedForms A) c.val ∈ U.val at h
    exact not_not.mp h⟩
  invFun c := ⟨c.val, by
    change ¬¬cellCenter (augmentedForms A) c.val ∈ U.val
    exact not_not.mpr c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def openSupportCellInclusion {U V : OpenCellSupport A} (h : U ≤ V) (q : ℕ) :
    OpenSupportCell A U q → OpenSupportCell A V q := fun c => ⟨c.val, h c.property⟩

theorem openSupportCellInclusion_injective {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) : Function.Injective (openSupportCellInclusion A h q) := by
  intro c d equal
  exact Subtype.ext (congrArg (fun z : OpenSupportCell A V q => z.val) equal)

variable (R : Type) [Ring R]

/-- The genuine characteristic-cell basis with the independent support
indexing displayed above. -/
def openSupportBasis (U : OpenCellSupport A) (q : ℕ) :
    Module.Basis (OpenSupportCell A U q) R
      (TauCeti.cellularChainGroup (relativeCWCarrier (openSupportComplement A U))
        (ModuleCat.of R R) q : ModuleCat R) :=
  (TauCeti.cellularChainBasis (relativeCWCarrier (openSupportComplement A U)) R q).reindex
    (openSupportCellEquiv A U q)

/-- The literal coordinate restriction map. -/
def openSupportRestrictionLinear {U V : OpenCellSupport A} (h : U ≤ V) (q : ℕ) :
    (OpenSupportCell A V q →₀ R) →ₗ[R] (OpenSupportCell A U q →₀ R) :=
  Finsupp.lcomapDomain (openSupportCellInclusion A h q)
    (openSupportCellInclusion_injective A h q)

/-- Each coefficient of the actual support map is the Kronecker
coefficient of the same surviving characteristic disk. -/
theorem openSupportChainGroupRestriction_coefficient {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) (i : OpenSupportCell A V q) (j : OpenSupportCell A U q) :
    (openSupportBasis A R U q).repr
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (openSupportComplement A V))
          (relativeCWCarrier (openSupportComplement A U))
          (relativeBaseInclusion_cellular _ _ (openSupportComplement_antitone A h))
          (ModuleCat.of R R) q (openSupportBasis A R V q i)) j =
      if i = openSupportCellInclusion A h q j then 1 else 0 := by
  simp only [openSupportBasis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  have characteristic :
      TauCeti.characteristicCellPairMap (arrangementCarrier A) i.val ≫
          TauCeti.skeletonPairMap (arrangementCarrier A) (arrangementCarrier A)
            (TauCeti.isCellular_id (arrangementCarrier A)) q =
        TauCeti.characteristicCellPairMap (arrangementCarrier A) i.val := by
    rw [TauCeti.skeletonPairMap_id, Category.comp_id]
  refine (relativeCWChainGroupMap_basis_coefficient
    (arrangementCarrier A) (arrangementCarrier A)
    (openSupportComplement A V) (openSupportComplement A U)
    (𝟙 (TopCat.of (arrangementCarrier A))) (TauCeti.isCellular_id _)
    (fun _ outside inside => outside (h inside)) R q
    ((openSupportCellEquiv A V q).symm i)
    ((openSupportCellEquiv A U q).symm j) i.val characteristic).trans ?_
  have same : i = openSupportCellInclusion A h q j ↔
      i.val = ((openSupportCellEquiv A U q).symm j).val := Subtype.ext_iff
  by_cases equal : i = openSupportCellInclusion A h q j
  · rw [if_pos (same.mp equal), if_pos equal]
  · rw [if_neg (fun h' => equal (same.mpr h')), if_neg equal]

/-- The complete actual map in characteristic-cell coordinates is
restriction along the literal inclusion of supported cells. -/
theorem openSupportChainGroupRestriction_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) :
    (openSupportBasis A R U q).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (openSupportComplement A V))
          (relativeCWCarrier (openSupportComplement A U))
          (relativeBaseInclusion_cellular _ _ (openSupportComplement_antitone A h))
          (ModuleCat.of R R) q).hom =
      (openSupportRestrictionLinear A R h q).comp
        (openSupportBasis A R V q).repr.toLinearMap := by
  apply (openSupportBasis A R V q).ext
  intro i
  ext j
  change (openSupportBasis A R U q).repr
      (TauCeti.cellularChainGroupMap _ _ _ (ModuleCat.of R R) q
        (openSupportBasis A R V q i)) j =
    openSupportRestrictionLinear A R h q
      ((openSupportBasis A R V q).repr (openSupportBasis A R V q i)) j
  rw [openSupportChainGroupRestriction_coefficient A R h q, Module.Basis.repr_self]
  change (if i = openSupportCellInclusion A h q j then (1 : R) else 0) =
    Finsupp.single i (1 : R) (openSupportCellInclusion A h q j)
  simp only [Finsupp.single_apply]

/-- Actual chain-complex terms in the same cell coordinates. -/
def openSupportChainCoordinates (U : OpenCellSupport A) (q : ℕ) :
    (openSupportChainComplex A (ModuleCat.of R R) U).X q ≃ₗ[R]
      (OpenSupportCell A U q →₀ R) :=
  (eqToIso (TauCeti.cellularChainComplex_X
      (relativeCWCarrier (openSupportComplement A U)) (ModuleCat.of R R) q)).toLinearEquiv.trans
    (openSupportBasis A R U q).repr

/-- The same coordinate formula includes the canonical chain-term
transports of the original cellular complex. -/
theorem openSupportChainRestriction_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ)
    (v : (openSupportChainComplex A (ModuleCat.of R R) V).X q) :
    openSupportChainCoordinates A R U q
        ((openSupportChainRestriction A (ModuleCat.of R R) h).f q v) =
      openSupportRestrictionLinear A R h q (openSupportChainCoordinates A R V q v) := by
  let C := relativeCWCarrier (openSupportComplement A V)
  let D := relativeCWCarrier (openSupportComplement A U)
  let hf := relativeBaseInclusion_cellular _ _ (openSupportComplement_antitone A h)
  have square : (openSupportChainRestriction A (ModuleCat.of R R) h).f q ≫
      eqToHom (TauCeti.cellularChainComplex_X D (ModuleCat.of R R) q) =
    eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) ≫
      TauCeti.cellularChainGroupMap C D hf (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplexMap C D hf (ModuleCat.of R R)).f q ≫ _ = _
    rw [TauCeti.cellularChainComplexMap_f]
    simp
  exact (congrArg (openSupportBasis A R U q).repr
    (ConcreteCategory.congr_hom square v)).trans
      (DFunLike.congr_fun (openSupportChainGroupRestriction_coordinates A R h q)
        (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) v))

section Field

variable (k : Type) [Field k]

/-- On a proved finite cell support, scalar cochains are literally
finitely supported functions in the original characteristic basis. -/
def openSupportCochainCoordinates (U : OpenCellSupport A) (q : ℕ)
    [Finite (OpenSupportCell A U q)] :
    (openSupportCochainComplex A k U).X q ≃ₗ[k] (OpenSupportCell A U q →₀ k) :=
  (CategoryTheory.Linear.homCongr k (openSupportChainCoordinates A k U q).toModuleIso
    (Iso.refl (ModuleCat.of k k))).trans (finiteFreeScalarDualEquiv k _)

/-- The actual scalar-dual support map is literal extension by zero,
including all coefficients of the finite cellular term. -/
theorem openSupportCochainExtension_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) [Finite (OpenSupportCell A U q)]
    [Finite (OpenSupportCell A V q)] (φ : (openSupportCochainComplex A k U).X q) :
    openSupportCochainCoordinates A k V q
        ((openSupportCochainExtension A k h).f q φ) =
      Finsupp.mapDomain (openSupportCellInclusion A h q)
        (openSupportCochainCoordinates A k U q φ) := by
  let eU := (openSupportChainCoordinates A k U q).toModuleIso
  let eV := (openSupportChainCoordinates A k V q).toModuleIso
  have conjugate : eV.inv ≫ (openSupportChainRestriction A (ModuleCat.of k k) h).f q =
      ModuleCat.ofHom (openSupportRestrictionLinear A k h q) ≫ eU.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply (openSupportChainCoordinates A k U q).injective
    change openSupportChainCoordinates A k U q
        ((openSupportChainRestriction A (ModuleCat.of k k) h).f q
          ((openSupportChainCoordinates A k V q).symm v)) =
      openSupportChainCoordinates A k U q
        ((openSupportChainCoordinates A k U q).symm
          (openSupportRestrictionLinear A k h q v))
    rw [openSupportChainRestriction_coordinates, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  change finiteFreeScalarDualEquiv k _
      ((eV.inv ≫ ((openSupportChainRestriction A (ModuleCat.of k k) h).f q ≫ φ)) ≫ 𝟙 _) =
    Finsupp.mapDomain (openSupportCellInclusion A h q)
      (finiteFreeScalarDualEquiv k _ ((eU.inv ≫ φ) ≫ 𝟙 _))
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, conjugate, Category.assoc]
  exact finiteFreeScalarDualEquiv_comapDomain k
    (openSupportCellInclusion A h q) (openSupportCellInclusion_injective A h q) (eU.inv ≫ φ)

end Field
end ToricPower.IntegralArrangement
