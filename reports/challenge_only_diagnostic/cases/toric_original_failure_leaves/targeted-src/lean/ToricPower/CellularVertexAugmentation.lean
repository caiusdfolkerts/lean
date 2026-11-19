module

public import ToricPower.DiagonalZerothExactness
public import ToricPower.CellularComparisonNaturality
public import ToricPower.SingularAugmentationNaturality

/-!
# The cellular augmentation sends every vertex to one

The degree-zero disk orientation in the recovered cellular theory is
defined by the ordinary singular augmentation. Naturality for the actual
characteristic pair map therefore identifies each cellular vertex generator
with a point class of augmentation one. This fixes the normalization needed
to compare the local cellular augmentation with the global diagonal map.

The computation uses the actual disk-pair homology isomorphism and actual
cellular--singular comparison. No choice of sign or rescaling is assumed.
Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical

namespace ToricPower

universe w

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- Relative homology modulo an empty subspace has its canonical
ordinary degree-zero augmentation. -/
def emptyPairZeroAugmentation (P : TopPair.{w}) [IsEmpty P.snd] :
    P.singularHomology M 0 ⟶ M :=
  inv (P.singularHomologyπ M 0) ≫ P.fst.singularHomology₀ε M

@[reassoc]
theorem emptyPairZeroAugmentation_naturality {P Q : TopPair.{w}}
    [IsEmpty P.snd] [IsEmpty Q.snd] (f : P ⟶ Q) :
    TopPair.singularHomologyMap f M 0 ≫ emptyPairZeroAugmentation M Q =
      emptyPairZeroAugmentation M P := by
  apply (cancel_epi (P.singularHomologyπ M 0)).mp
  have hπ := SSetPair.homologyπ_naturality (TopPair.toSSetPair.map f) M 0
  rw [TopPair.toSSetPair_map_right] at hπ
  change ((singularHomologyFunctor (ModuleCat.{w} k) 0).obj M).map
        (TopPair.Hom.fst f) ≫ Q.singularHomologyπ M 0 =
      P.singularHomologyπ M 0 ≫ TopPair.singularHomologyMap f M 0 at hπ
  simp only [emptyPairZeroAugmentation,Category.assoc,IsIso.hom_inv_id_assoc]
  rw [← Category.assoc,← hπ]
  simp only [Category.assoc,IsIso.hom_inv_id_assoc]
  exact singularHomologyZeroAugmentation_naturality (TopPair.Hom.fst f) M

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

local instance emptySkeletonZero : IsEmpty (TauCeti.skeletonObj C 0) := by
  refine ⟨fun x => ?_⟩
  have hx := x.property
  simpa only [Nat.cast_zero,skeletonLT_zero_eq_base,Set.mem_empty_iff_false] using hx

local instance emptySkeletonPairZero : IsEmpty (TauCeti.skeletonPair C 0).snd := by
  change IsEmpty (TauCeti.skeletonObj C 0)
  infer_instance

/-- The actual cellular chain-group augmentation, via the canonical
cellular--singular homology comparison. -/
def cellularZeroAugmentation : TauCeti.cellularChainGroup C M 0 ⟶ M :=
  eqToHom (TauCeti.cellularChainComplex_X C M 0).symm ≫
    (TauCeti.cellularChainComplex C M).cycles₀Iso.inv ≫
    (TauCeti.cellularChainComplex C M).homologyπ 0 ≫
      (absoluteCellularSingularIso C M 0).hom ≫ (TopCat.of C).singularHomology₀ε M

/-- In degree zero the cycles identification is literally the identity
on the skeletal relative homology, after the canonical chain/cycles iso. -/
@[reassoc]
theorem cellularCyclesIso_zero_normalization :
    eqToHom (TauCeti.cellularChainComplex_X C M 0).symm ≫
      (TauCeti.cellularChainComplex C M).cycles₀Iso.inv ≫
      (TauCeti.cellularCyclesIso C M 0).hom = 𝟙 _ := by
  apply (cancel_mono (TauCeti.cellularCyclesIso C M 0).inv).mp
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
  apply (cancel_mono ((TauCeti.cellularChainComplex C M).iCycles 0)).mp
  rw [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
    TauCeti.cellularCyclesIso_inv_comp_iCycles,
    TauCeti.skeletonBasePairToSkeletonPair_zero,TopPair.singularHomologyMap_id]
  simp only [TauCeti.cellularChainComplex_X,eqToHom_refl,Category.id_comp,Category.comp_id]

/-- The degree-zero cellular augmentation agrees with the ordinary
augmentation on the actual zero-skeleton pair. -/
theorem cellularZeroAugmentation_eq_emptyPair :
    cellularZeroAugmentation M C = emptyPairZeroAugmentation M (TauCeti.skeletonPair C 0) := by
  unfold cellularZeroAugmentation absoluteCellularSingularIso
  simp only [Iso.trans_hom,Iso.symm_hom,asIso_inv,Category.assoc]
  rw [TauCeti.homologyπ_comp_cellularSingularHomologyIso_hom_assoc,
    cellularCyclesIso_zero_normalization_assoc]
  exact emptyPairZeroAugmentation_naturality M (TauCeti.skeletonBasePairToComplex C 0)

/-- The characteristic generator of every vertex has augmentation one,
as an equality of morphisms of the coefficient module. -/
@[reassoc]
theorem cellularZeroAugmentation_vertex (j : cell C 0) :
    Sigma.ι (fun _ : cell C 0 => M) j ≫
      (TauCeti.cellularChainGroupIso C M 0).inv ≫ cellularZeroAugmentation M C = 𝟙 M := by
  rw [TauCeti.ι_cellularChainGroupIso_inv_eq_singularHomologyMap_characteristicCellPairMap_assoc,
    cellularZeroAugmentation_eq_emptyPair,
    emptyPairZeroAugmentation_naturality]
  change (TauCeti.singularHomologyDiskBoundaryPairIso M 0).inv ≫
    inv ((TauCeti.diskBoundaryPair 0).singularHomologyπ M 0) ≫
      (TopCat.disk 0).singularHomology₀ε M = 𝟙 M
  rw [← TauCeti.singularHomologyDiskBoundaryPairIso_zero_hom]
  exact Iso.inv_hom_id _

theorem cellularZeroAugmentation_basis (j : cell C 0) :
    cellularZeroAugmentation (ModuleCat.of k k) C (TauCeti.cellularChainBasis C k 0 j) = 1 := by
  have h := congrArg (fun f : ModuleCat.of k k ⟶ ModuleCat.of k k => f 1)
    (cellularZeroAugmentation_vertex (ModuleCat.of k k) C j)
  simpa only [TauCeti.cellularChainBasis_apply,ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] using h

/-- The canonical cellular augmentation kills the actual differential.
This follows from its homology definition, independently of the vertex
coordinate computation. -/
@[reassoc]
theorem cellularZeroAugmentation_boundary :
    TauCeti.cellularDifferential C M 0 ≫ cellularZeroAugmentation M C = 0 := by
  let K := TauCeti.cellularChainComplex C M
  have hquot : K.pOpcycles 0 ≫ K.isoHomologyι₀.inv =
      K.cycles₀Iso.inv ≫ K.homologyπ 0 := by
    rw [← cancel_mono (K.homologyι 0),Category.assoc,
      HomologicalComplex.isoHomologyι_inv_hom_id,Category.comp_id,
      Category.assoc,HomologicalComplex.homology_π_ι,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc]
  have hd : eqToHom (TauCeti.cellularChainComplex_X C M 1).symm ≫ K.d 1 0 =
      TauCeti.cellularDifferential C M 0 ≫
        eqToHom (TauCeti.cellularChainComplex_X C M 0).symm := by
    change eqToHom (TauCeti.cellularChainComplex_X C M 1).symm ≫
        (TauCeti.cellularChainComplex C M).d 1 0 = _
    rw [TauCeti.cellularChainComplex_d]
    simp
  change TauCeti.cellularDifferential C M 0 ≫
      eqToHom (TauCeti.cellularChainComplex_X C M 0).symm ≫
        K.cycles₀Iso.inv ≫ K.homologyπ 0 ≫
      (absoluteCellularSingularIso C M 0).hom ≫
        (TopCat.of C).singularHomology₀ε M = 0
  rw [← Category.assoc (TauCeti.cellularDifferential C M 0), ← hd, Category.assoc]
  rw [← Category.assoc K.cycles₀Iso.inv (K.homologyπ 0),← hquot]
  simp only [← Category.assoc,K.d_pOpcycles,zero_comp,comp_zero]

/-- The total signed incidence of the boundary of an actual one-cell
is zero. Multiple translated incidences remain distinct in the sum. -/
theorem cellularBoundaryColumn_sum_zero (j : cell C 1) :
    (TauCeti.cellularBoundaryColumn C k 0 j).sum (fun _ r => r) = 0 := by
  have h := congrArg
    (fun f : TauCeti.cellularChainGroup C (ModuleCat.of k k) 1 ⟶ ModuleCat.of k k =>
      f (TauCeti.cellularChainBasis C k 1 j))
    (cellularZeroAugmentation_boundary (ModuleCat.of k k) C)
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  rw [TauCeti.cellularDifferential_basis, map_finsuppSum] at h
  simp only [map_smul] at h
  refine Eq.trans ?_ h
  apply Finsupp.sum_congr
  intro a ha
  simpa only [smul_eq_mul, mul_one] using
    (congrArg (fun v : k => (TauCeti.cellularBoundaryColumn C k 0 j) a * v)
      (cellularZeroAugmentation_basis C a)).symm

namespace IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s)) (u : Fin n → ℤ)

local instance cellularVertexPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A
local instance cellularVertexStripCW : CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

/-- The weight augmentation in the actual cellular basis has coefficient
one on each geometric vertex, with its canonical orientation. -/
theorem diagonalWeightAugmentationCoordinates_vertex
    (hne : (diagonalStrip A S T u).Nonempty)
    (c : Topology.RelCWComplex.cell (diagonalStripCarrier A S T u) 0) (r : k) :
    diagonalWeightAugmentationCoordinates k A S T u hne (Finsupp.single c r) = r := by
  let C := diagonalStripCarrier A S T u
  let K := diagonalWeightCellComplex A (ModuleCat.of k k) S T u
  have hquot : K.pOpcycles 0 ≫ K.isoHomologyι₀.inv = K.cycles₀Iso.inv ≫ K.homologyπ 0 := by
    rw [← cancel_mono (K.homologyι 0),Category.assoc,
      HomologicalComplex.isoHomologyι_inv_hom_id,Category.comp_id,
      Category.assoc,HomologicalComplex.homology_π_ι,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc]
  have haug : (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) 0).symm ≫
      ModuleCat.ofHom (zeroHomologyQuotient K
        (diagonalWeightCellHomologyZeroIso A (ModuleCat.of k k) S T u hne))).hom =
        (cellularZeroAugmentation (ModuleCat.of k k) C).hom := by
    unfold zeroHomologyQuotient cellularZeroAugmentation
    rw [← Category.assoc,hquot,diagonalWeightCellHomologyZeroIso_hom]
    rfl
  change (eqToHom (TauCeti.cellularChainComplex_X C (ModuleCat.of k k) 0).symm ≫
      ModuleCat.ofHom (zeroHomologyQuotient K
        (diagonalWeightCellHomologyZeroIso A (ModuleCat.of k k) S T u hne))).hom
        ((TauCeti.cellularChainBasis C k 0).repr.symm (Finsupp.single c r)) = r
  rw [haug,Module.Basis.repr_symm_single,map_smul,
    cellularZeroAugmentation_basis,smul_eq_mul,mul_one]

end IntegralArrangement

end ToricPower
