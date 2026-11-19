module

public import ToricPower.LinearSliceOpenSupport
public import ToricPower.ArrangementBoundedCells
public import ToricPower.ArrangementOpenSupportCoordinates

/-! # Literal finite-window coordinates on the closed slice

The actual relative cell index retains its original periodic
characteristic map and its membership in the closed slice. In these
coordinates the genuine support restriction is coefficient restriction,
and its scalar dual is extension by zero. Finiteness is proved for every
bounded window, before any scalar dual is identified with finite support.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (zeroRows : Set (Fin s ⊕ Fin n))

local notation "E" => Fin n → ℝ
local notation "L" => arrangementZeroSlice (augmentedForms A) zeroRows

local instance sliceCoordinateAmbientCW : CWComplex (arrangementCarrier A) := periodicArrangementCWComplex A
local instance sliceCoordinateInheritedCW : CWComplex (L : Set E) :=
  inferInstanceAs (CWComplex (periodicLinearSliceSubcomplex A zeroRows : Set E))

def LinearSliceCell (q : ℕ) :=
  {c : Cell (augmentedForms A) q // cellCenter (augmentedForms A) c ∈ L}

def SliceSupportCell (U : OpenCellSupport A) (q : ℕ) :=
  {c : LinearSliceCell A zeroRows q // cellCenter (augmentedForms A) c.val ∈ U.val}

def sliceSupportCellEquiv (U : OpenCellSupport A) (q : ℕ) :
    Topology.RelCWComplex.cell (relativeCWCarrier (sliceSupportComplement A zeroRows U)) q ≃
      SliceSupportCell A zeroRows U q where
  toFun c := ⟨c.val,by
    have excluded := c.property
    change ¬ (cellCenter (augmentedForms A) c.val.val ∈ L ∧
      cellCenter (augmentedForms A) c.val.val ∉ U.val) at excluded
    exact Classical.not_not.mp (fun outside => excluded ⟨c.val.property,outside⟩)⟩
  invFun c := ⟨c.val,by
    change ¬ (cellCenter (augmentedForms A) c.val.val ∈ L ∧
      cellCenter (augmentedForms A) c.val.val ∉ U.val)
    exact fun excluded => excluded.2 c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def sliceSupportCellInclusion {U V : OpenCellSupport A} (h : U ≤ V) (q : ℕ) :
    SliceSupportCell A zeroRows U q → SliceSupportCell A zeroRows V q :=
  fun c => ⟨c.val,h c.property⟩

theorem sliceSupportCellInclusion_injective {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) : Function.Injective (sliceSupportCellInclusion A zeroRows h q) := by
  intro c d equal
  exact Subtype.ext (congrArg (fun z : SliceSupportCell A zeroRows V q => z.val) equal)

theorem sliceSupportCell_finite (U : OpenCellSupport A)
    (bounded : Bornology.IsBounded (U.val : Set E)) (q : ℕ) :
    Finite (SliceSupportCell A zeroRows U q) := by
  letI := boundedRegion_cells_finite A U.val bounded q
  let f : SliceSupportCell A zeroRows U q →
      {c : Cell (augmentedForms A) q // cellCenter (augmentedForms A) c ∈ U.val} :=
    fun c => ⟨c.val.val,c.property⟩
  exact Finite.of_injective f (by
    intro c d equal
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {c : Cell (augmentedForms A) q //
      cellCenter (augmentedForms A) c ∈ U.val} => z.val) equal)

variable (R : Type) [Ring R]

/-- The genuine characteristic-cell basis with the independent support
indexing displayed above. -/
def sliceSupportBasis (U : OpenCellSupport A) (q : ℕ) :
    Module.Basis (SliceSupportCell A zeroRows U q) R
      (TauCeti.cellularChainGroup (relativeCWCarrier (sliceSupportComplement A zeroRows U))
        (ModuleCat.of R R) q : ModuleCat R) :=
  (TauCeti.cellularChainBasis (relativeCWCarrier (sliceSupportComplement A zeroRows U)) R q).reindex
    (sliceSupportCellEquiv A zeroRows U q)

/-- The literal coordinate restriction map. -/
def sliceSupportRestrictionLinear {U V : OpenCellSupport A} (h : U ≤ V) (q : ℕ) :
    (SliceSupportCell A zeroRows V q →₀ R) →ₗ[R] (SliceSupportCell A zeroRows U q →₀ R) :=
  Finsupp.lcomapDomain (sliceSupportCellInclusion A zeroRows h q)
    (sliceSupportCellInclusion_injective A zeroRows h q)

/-- Each coefficient of the actual support map is the Kronecker
coefficient of the same surviving characteristic disk. -/
theorem sliceSupportChainGroupRestriction_coefficient {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) (i : SliceSupportCell A zeroRows V q) (j : SliceSupportCell A zeroRows U q) :
    (sliceSupportBasis A zeroRows R U q).repr
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (sliceSupportComplement A zeroRows V))
          (relativeCWCarrier (sliceSupportComplement A zeroRows U))
          (relativeBaseInclusion_cellular _ _ (sliceSupportComplement_antitone A zeroRows h))
          (ModuleCat.of R R) q (sliceSupportBasis A zeroRows R V q i)) j =
      if i = sliceSupportCellInclusion A zeroRows h q j then 1 else 0 := by
  simp only [sliceSupportBasis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  have characteristic :
      TauCeti.characteristicCellPairMap (L : Set E) i.val ≫
          TauCeti.skeletonPairMap (L : Set E) (L : Set E)
            (TauCeti.isCellular_id (L : Set E)) q =
        TauCeti.characteristicCellPairMap (L : Set E) i.val := by
    rw [TauCeti.skeletonPairMap_id, Category.comp_id]
  refine (relativeCWChainGroupMap_basis_coefficient
    (L : Set E) (L : Set E)
    (sliceSupportComplement A zeroRows V) (sliceSupportComplement A zeroRows U)
    (𝟙 (TopCat.of (L : Set E))) (TauCeti.isCellular_id _)
    (fun _ hx => ⟨hx.1,fun hu => hx.2 (h hu)⟩) R q
    ((sliceSupportCellEquiv A zeroRows V q).symm i)
    ((sliceSupportCellEquiv A zeroRows U q).symm j) i.val characteristic).trans ?_
  have same : i = sliceSupportCellInclusion A zeroRows h q j ↔
      i.val = ((sliceSupportCellEquiv A zeroRows U q).symm j).val := Subtype.ext_iff
  by_cases equal : i = sliceSupportCellInclusion A zeroRows h q j
  · rw [if_pos (same.mp equal), if_pos equal]
  · rw [if_neg (fun h' => equal (same.mpr h')), if_neg equal]

/-- The complete actual map in characteristic-cell coordinates is
restriction along the literal inclusion of supported cells. -/
theorem sliceSupportChainGroupRestriction_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) :
    (sliceSupportBasis A zeroRows R U q).repr.toLinearMap.comp
        (TauCeti.cellularChainGroupMap
          (relativeCWCarrier (sliceSupportComplement A zeroRows V))
          (relativeCWCarrier (sliceSupportComplement A zeroRows U))
          (relativeBaseInclusion_cellular _ _ (sliceSupportComplement_antitone A zeroRows h))
          (ModuleCat.of R R) q).hom =
      (sliceSupportRestrictionLinear A zeroRows R h q).comp
        (sliceSupportBasis A zeroRows R V q).repr.toLinearMap := by
  apply (sliceSupportBasis A zeroRows R V q).ext
  intro i
  ext j
  change (sliceSupportBasis A zeroRows R U q).repr
      (TauCeti.cellularChainGroupMap _ _ _ (ModuleCat.of R R) q
        (sliceSupportBasis A zeroRows R V q i)) j =
    sliceSupportRestrictionLinear A zeroRows R h q
      ((sliceSupportBasis A zeroRows R V q).repr (sliceSupportBasis A zeroRows R V q i)) j
  rw [sliceSupportChainGroupRestriction_coefficient A zeroRows R h q, Module.Basis.repr_self]
  change (if i = sliceSupportCellInclusion A zeroRows h q j then (1 : R) else 0) =
    Finsupp.single i (1 : R) (sliceSupportCellInclusion A zeroRows h q j)
  simp only [Finsupp.single_apply]

/-- Actual chain-complex terms in the same cell coordinates. -/
def sliceSupportChainCoordinates (U : OpenCellSupport A) (q : ℕ) :
    (sliceSupportChainComplex A zeroRows (ModuleCat.of R R) U).X q ≃ₗ[R]
      (SliceSupportCell A zeroRows U q →₀ R) :=
  (eqToIso (TauCeti.cellularChainComplex_X
      (relativeCWCarrier (sliceSupportComplement A zeroRows U)) (ModuleCat.of R R) q)).toLinearEquiv.trans
    (sliceSupportBasis A zeroRows R U q).repr

/-- The same coordinate formula includes the canonical chain-term
transports of the original cellular complex. -/
theorem sliceSupportChainRestriction_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ)
    (v : (sliceSupportChainComplex A zeroRows (ModuleCat.of R R) V).X q) :
    sliceSupportChainCoordinates A zeroRows R U q
        ((sliceSupportChainRestriction A zeroRows (ModuleCat.of R R) h).f q v) =
      sliceSupportRestrictionLinear A zeroRows R h q (sliceSupportChainCoordinates A zeroRows R V q v) := by
  let C := relativeCWCarrier (sliceSupportComplement A zeroRows V)
  let D := relativeCWCarrier (sliceSupportComplement A zeroRows U)
  let hf := relativeBaseInclusion_cellular _ _ (sliceSupportComplement_antitone A zeroRows h)
  have square : (sliceSupportChainRestriction A zeroRows (ModuleCat.of R R) h).f q ≫
      eqToHom (TauCeti.cellularChainComplex_X D (ModuleCat.of R R) q) =
    eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) ≫
      TauCeti.cellularChainGroupMap C D hf (ModuleCat.of R R) q := by
    change (TauCeti.cellularChainComplexMap C D hf (ModuleCat.of R R)).f q ≫ _ = _
    rw [TauCeti.cellularChainComplexMap_f]
    simp
  exact (congrArg (sliceSupportBasis A zeroRows R U q).repr
    (ConcreteCategory.congr_hom square v)).trans
      (DFunLike.congr_fun (sliceSupportChainGroupRestriction_coordinates A zeroRows R h q)
        (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of R R) q) v))

section Field

variable (k : Type) [Field k]

/-- On a proved finite cell support, scalar cochains are literally
finitely supported functions in the original characteristic basis. -/
def sliceSupportCochainCoordinates (U : OpenCellSupport A) (q : ℕ)
    [Finite (SliceSupportCell A zeroRows U q)] :
    (sliceSupportCochainComplex A zeroRows k U).X q ≃ₗ[k] (SliceSupportCell A zeroRows U q →₀ k) :=
  (CategoryTheory.Linear.homCongr k (sliceSupportChainCoordinates A zeroRows k U q).toModuleIso
    (Iso.refl (ModuleCat.of k k))).trans (finiteFreeScalarDualEquiv k _)

/-- The actual scalar-dual support map is literal extension by zero,
including all coefficients of the finite cellular term. -/
theorem sliceSupportCochainExtension_coordinates {U V : OpenCellSupport A}
    (h : U ≤ V) (q : ℕ) [Finite (SliceSupportCell A zeroRows U q)]
    [Finite (SliceSupportCell A zeroRows V q)] (φ : (sliceSupportCochainComplex A zeroRows k U).X q) :
    sliceSupportCochainCoordinates A zeroRows k V q
        ((sliceSupportCochainExtension A zeroRows k h).f q φ) =
      Finsupp.mapDomain (sliceSupportCellInclusion A zeroRows h q)
        (sliceSupportCochainCoordinates A zeroRows k U q φ) := by
  let eU := (sliceSupportChainCoordinates A zeroRows k U q).toModuleIso
  let eV := (sliceSupportChainCoordinates A zeroRows k V q).toModuleIso
  have conjugate : eV.inv ≫ (sliceSupportChainRestriction A zeroRows (ModuleCat.of k k) h).f q =
      ModuleCat.ofHom (sliceSupportRestrictionLinear A zeroRows k h q) ≫ eU.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply (sliceSupportChainCoordinates A zeroRows k U q).injective
    change sliceSupportChainCoordinates A zeroRows k U q
        ((sliceSupportChainRestriction A zeroRows (ModuleCat.of k k) h).f q
          ((sliceSupportChainCoordinates A zeroRows k V q).symm v)) =
      sliceSupportChainCoordinates A zeroRows k U q
        ((sliceSupportChainCoordinates A zeroRows k U q).symm
          (sliceSupportRestrictionLinear A zeroRows k h q v))
    rw [sliceSupportChainRestriction_coordinates, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  change finiteFreeScalarDualEquiv k _
      ((eV.inv ≫ ((sliceSupportChainRestriction A zeroRows (ModuleCat.of k k) h).f q ≫ φ)) ≫ 𝟙 _) =
    Finsupp.mapDomain (sliceSupportCellInclusion A zeroRows h q)
      (finiteFreeScalarDualEquiv k _ ((eU.inv ≫ φ) ≫ 𝟙 _))
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, conjugate, Category.assoc]
  exact finiteFreeScalarDualEquiv_comapDomain k
    (sliceSupportCellInclusion A zeroRows h q) (sliceSupportCellInclusion_injective A zeroRows h q) (eU.inv ≫ φ)

end Field
end ToricPower.IntegralArrangement
