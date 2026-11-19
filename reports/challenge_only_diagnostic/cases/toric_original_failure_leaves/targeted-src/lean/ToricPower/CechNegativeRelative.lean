module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Tactic.LinearCombination

public import ToricPower.CechNegativeSupportGeneric
public import ToricPower.CechProductElements
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Relative incidence cohomology and the negative chart nerve

The short exact sequence is formed from actual tuple functions, with an
explicit zero-extension proving surjectivity. The ambient full simplex
is contracted by an actual insertion operator. Its long exact sequence
therefore identifies relative cohomology with reduced cohomology of the
negative chart nerve, in positive degrees.

This is the chart nerve. Identifying it with the induced complex on
negative rays requires a separate genuine Dowker/nerve comparison.
Candidate source, pending pinned compilation.

Generic bodies are ported from BondalThomsen commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb:
NefCechAcyclicity.lean, lines 25–63, and the complete generic
NegativeSupportRelativeCohomology.lean body.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open ToricPower.CechProductElements
open ToricPower.NegativeSupportCech
open scoped Classical Simplicial

namespace ToricPower.NegativeSupportRelative

variable (𝕜 : Type) [Field 𝕜]

def scalarSimplexDifferential {Index : Type*} (degree : ℕ)
    (cochain : (Fin (degree + 1) → Index) → 𝕜)
    (tuple : Fin (degree + 2) → Index) : 𝕜 :=
  ∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ deleted.val *
    cochain (tuple ∘ deleted.succAbove)

def scalarSimplexContraction {Index : Type*} (anchor : Index) (degree : ℕ)
    (cochain : (Fin (degree + 2) → Index) → 𝕜)
    (tuple : Fin (degree + 1) → Index) : 𝕜 :=
  cochain (Fin.cons anchor tuple)

theorem scalarSimplexContraction_identity {Index : Type*} (anchor : Index) (degree : ℕ)
    (cochain : (Fin (degree + 2) → Index) → 𝕜) (tuple : Fin (degree + 2) → Index) :
    scalarSimplexDifferential 𝕜 degree (scalarSimplexContraction 𝕜 anchor degree cochain) tuple +
      scalarSimplexContraction 𝕜 anchor (degree + 1)
        (scalarSimplexDifferential 𝕜 (degree + 1) cochain) tuple = cochain tuple := by
  unfold scalarSimplexDifferential scalarSimplexContraction
  dsimp only
  rw [Fin.sum_univ_succ (fun deleted : Fin (degree + 3) =>
    (-1 : 𝕜) ^ deleted.val * cochain (Fin.cons anchor tuple ∘ deleted.succAbove))]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.cons_comp_succ, Fin.val_succ,
    Fin.cons_comp_succ_succAbove]
  have cancellation :
      (∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ deleted.val *
        cochain (Fin.cons anchor (tuple ∘ deleted.succAbove))) +
      (∑ deleted : Fin (degree + 2), (-1 : 𝕜) ^ (deleted.val + 1) *
        cochain (Fin.cons anchor (tuple ∘ deleted.succAbove))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro deleted _
    rw [pow_succ]
    ring
  have remove_eq (deleted : Fin (degree + 2)) :
      deleted.removeNth tuple = tuple ∘ deleted.succAbove := by
    funext entry
    exact Fin.removeNth_apply deleted tuple entry
  simp_rw [remove_eq]
  linear_combination cancellation

variable {Ray : Type*} {Chart : Type}

def forbiddenTuple (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (degree : ℕ) :=
  {tuple : Fin (degree + 1) → Chart // tupleForbidden incidence negative degree tuple}

noncomputable def fullDegree (Chart : Type) (degree : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of ((Fin (degree + 1) → Chart) → 𝕜)

noncomputable def negativeDegree (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (forbiddenTuple incidence negative degree → 𝕜)

def fullTupleRestriction {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1)) :
    ((Fin (degree + 1) → Chart) → 𝕜) →+ ((Fin (next + 1) → Chart) → 𝕜) where
  toFun cochain tuple := cochain (tuple ∘ selection)
  map_zero' := rfl
  map_add' _first _second := rfl

def negativeTupleRestriction (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1)) :
    (forbiddenTuple incidence negative degree → 𝕜) →+
      (forbiddenTuple incidence negative next → 𝕜) where
  toFun cochain tuple := cochain ⟨tuple.val ∘ selection,
    tupleForbidden_precomp incidence negative selection tuple.val tuple.property⟩
  map_zero' := rfl
  map_add' _first _second := rfl

noncomputable def fullCosimplicial (Chart : Type) : CosimplicialObject AddCommGrpCat where
  obj simplex := fullDegree 𝕜 Chart simplex.len
  map selection := AddCommGrpCat.ofHom (fullTupleRestriction 𝕜 selection.toOrderHom)
  map_id _simplex := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl
  map_comp _first _second := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

noncomputable def negativeCosimplicial (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : CosimplicialObject AddCommGrpCat where
  obj simplex := negativeDegree 𝕜 incidence negative simplex.len
  map selection := AddCommGrpCat.ofHom
    (negativeTupleRestriction 𝕜 incidence negative selection.toOrderHom)
  map_id _simplex := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl
  map_comp _first _second := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

def relativeCoefficientValues (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (∀ tuple, relativeCoefficient 𝕜 incidence negative degree tuple) →+
      ((Fin (degree + 1) → Chart) → 𝕜) where
  toFun cochain tuple := (cochain tuple).val
  map_zero' := rfl
  map_add' _first _second := rfl

noncomputable def relativeDegreeInclusion (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    relativeDegree 𝕜 incidence negative degree ⟶ fullDegree 𝕜 Chart degree :=
  AddCommGrpCat.ofHom
    ((relativeCoefficientValues 𝕜 incidence negative degree).comp
        (productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)).toAddMonoidHom)

theorem relativeDegreeInclusion_apply (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : relativeDegree 𝕜 incidence negative degree) (tuple : Fin (degree + 1) → Chart) :
    relativeDegreeInclusion 𝕜 incidence negative degree cochain tuple =
      (Limits.Pi.π (relativeCoefficient 𝕜 incidence negative degree) tuple cochain).val := by
  exact congrArg Subtype.val
    (productElementsEquiv_apply (relativeCoefficient 𝕜 incidence negative degree) cochain tuple)

def negativeDegreeRestriction (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    ((Fin (degree + 1) → Chart) → 𝕜) →+ (forbiddenTuple incidence negative degree → 𝕜) where
  toFun cochain tuple := cochain tuple.val
  map_zero' := rfl
  map_add' _first _second := rfl

noncomputable def relativeCosimplicialInclusion (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    relativeCosimplicial 𝕜 incidence negative ⟶ fullCosimplicial 𝕜 Chart where
  app simplex := relativeDegreeInclusion 𝕜 incidence negative simplex.len
  naturality {source target} selection := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    funext tuple
    change relativeDegreeInclusion 𝕜 incidence negative target.len
        (relativeTupleMap 𝕜 incidence negative selection.toOrderHom cochain) tuple =
      relativeDegreeInclusion 𝕜 incidence negative source.len cochain
        (tuple ∘ selection.toOrderHom)
    rw [relativeDegreeInclusion_apply, relativeDegreeInclusion_apply]
    have coordinate := ConcreteCategory.congr_hom
      (Limits.Pi.lift_comp_π (fun targetTuple =>
        Limits.Pi.π (relativeCoefficient 𝕜 incidence negative source.len)
            (targetTuple ∘ selection.toOrderHom) ≫
          AddCommGrpCat.ofHom (relativeScalarRestriction 𝕜 incidence negative
            selection.toOrderHom targetTuple)) tuple) cochain
    exact congrArg Subtype.val coordinate

noncomputable def negativeCosimplicialRestriction (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : fullCosimplicial 𝕜 Chart ⟶ negativeCosimplicial 𝕜 incidence negative where
  app simplex := AddCommGrpCat.ofHom (negativeDegreeRestriction 𝕜 incidence negative simplex.len)
  naturality {source target} _selection := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cochain
    rfl

noncomputable def fullComplex (Chart : Type) : CochainComplex AddCommGrpCat ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (fullCosimplicial 𝕜 Chart)

noncomputable def negativeComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    CochainComplex AddCommGrpCat ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (negativeCosimplicial 𝕜 incidence negative)

noncomputable def relativeComplexInclusion (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : relativeComplex 𝕜 incidence negative ⟶ fullComplex 𝕜 Chart :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (relativeCosimplicialInclusion 𝕜 incidence negative)

noncomputable def negativeComplexRestriction (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : fullComplex 𝕜 Chart ⟶ negativeComplex 𝕜 incidence negative :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (negativeCosimplicialRestriction 𝕜 incidence negative)

theorem relativeComplexInclusion_restriction (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) :
    relativeComplexInclusion 𝕜 incidence negative ≫ negativeComplexRestriction 𝕜 incidence negative = 0 := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  funext tuple
  change relativeDegreeInclusion 𝕜 incidence negative degree cochain tuple.val = 0
  rw [relativeDegreeInclusion_apply]
  exact (Limits.Pi.π (relativeCoefficient 𝕜 incidence negative degree) tuple.val cochain).property
    tuple.property

noncomputable def relativeShortComplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    ShortComplex (CochainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (relativeComplexInclusion 𝕜 incidence negative)
    (negativeComplexRestriction 𝕜 incidence negative) (relativeComplexInclusion_restriction 𝕜 incidence negative)

theorem relativeDegreeInclusion_injective (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    Function.Injective (relativeDegreeInclusion 𝕜 incidence negative degree) := by
  intro first second equal
  apply (productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)).injective
  funext tuple
  apply Subtype.ext
  have coordinates := congrFun equal tuple
  change ((productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)) first tuple).val =
    ((productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)) second tuple).val at coordinates
  exact coordinates

noncomputable def negativeDegreeZeroExtension (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (cochain : forbiddenTuple incidence negative degree → 𝕜)
    (tuple : Fin (degree + 1) → Chart) : 𝕜 :=
  if forbidden : tupleForbidden incidence negative degree tuple then cochain ⟨tuple, forbidden⟩ else 0

theorem negativeDegreeRestriction_surjective (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    Function.Surjective (negativeDegreeRestriction 𝕜 incidence negative degree) := by
  intro cochain
  refine ⟨negativeDegreeZeroExtension 𝕜 incidence negative degree cochain, ?_⟩
  funext tuple
  simp [negativeDegreeRestriction, negativeDegreeZeroExtension, tuple.property]

theorem relativeShortComplex_shortExact (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (relativeShortComplex 𝕜 incidence negative).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro degree
  apply ShortComplex.ShortExact.mk'
  · apply (ShortComplex.ab_exact_iff _).mpr
    intro cochain vanishes
    change negativeDegreeRestriction 𝕜 incidence negative degree cochain = 0 at vanishes
    have forbiddenZero (tuple : Fin (degree + 1) → Chart)
        (forbidden : tupleForbidden incidence negative degree tuple) : cochain tuple = 0 := by
      exact congrFun vanishes ⟨tuple, forbidden⟩
    let relativeCochain : ∀ tuple, relativeCoefficient 𝕜 incidence negative degree tuple :=
      fun tuple => ⟨cochain tuple, forbiddenZero tuple⟩
    refine ⟨(productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)).symm
      relativeCochain, ?_⟩
    change relativeDegreeInclusion 𝕜 incidence negative degree _ = cochain
    funext tuple
    change ((productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree))
      ((productElementsEquiv (relativeCoefficient 𝕜 incidence negative degree)).symm relativeCochain)
      tuple).val = cochain tuple
    rw [AddEquiv.apply_symm_apply]
  · exact (AddCommGrpCat.mono_iff_injective _).mpr
      (relativeDegreeInclusion_injective 𝕜 incidence negative degree)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (negativeDegreeRestriction_surjective 𝕜 incidence negative degree)

theorem fullComplex_d_apply (degree : ℕ)
    (cochain : (fullComplex 𝕜 Chart).X degree) (tuple : Fin (degree + 2) → Chart) :
    (fullComplex 𝕜 Chart).d degree (degree + 1) cochain tuple =
      scalarSimplexDifferential 𝕜 degree cochain tuple := by
  let evaluation : ((fullComplex 𝕜 Chart).X degree ⟶ (fullComplex 𝕜 Chart).X (degree + 1)) →+ 𝕜 :=
    (Pi.evalAddMonoidHom (fun _tuple : Fin (degree + 2) → Chart => 𝕜) tuple).comp
      ((AddMonoidHom.eval cochain).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom)
  change evaluation ((fullComplex 𝕜 Chart).d degree (degree + 1)) = _
  have differential : (fullComplex 𝕜 Chart).d degree (degree + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (fullCosimplicial 𝕜 Chart) degree := by
    simp only [fullComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rw [differential]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum]
  unfold scalarSimplexDifferential
  apply Finset.sum_congr rfl
  intro deleted _present
  rw [map_zsmul]
  change ((-1 : ℤ) ^ deleted.val) • cochain (tuple ∘ deleted.succAbove) = _
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

def fullContraction (anchor : Chart) (degree : ℕ) :
    (fullComplex 𝕜 Chart).X (degree + 1) →+ (fullComplex 𝕜 Chart).X degree where
  toFun cochain tuple := cochain (Fin.cons anchor tuple)
  map_zero' := rfl
  map_add' _first _second := rfl

theorem fullContraction_identity (anchor : Chart) (degree : ℕ)
    (cochain : (fullComplex 𝕜 Chart).X (degree + 1)) :
    (fullComplex 𝕜 Chart).d degree (degree + 1) (fullContraction 𝕜 anchor degree cochain) +
      fullContraction 𝕜 anchor (degree + 1)
        ((fullComplex 𝕜 Chart).d (degree + 1) (degree + 2) cochain) = cochain := by
  funext tuple
  change (fullComplex 𝕜 Chart).d degree (degree + 1) _ tuple +
    (fullComplex 𝕜 Chart).d (degree + 1) (degree + 2) cochain (Fin.cons anchor tuple) = cochain tuple
  rw [fullComplex_d_apply, fullComplex_d_apply]
  exact scalarSimplexContraction_identity 𝕜 anchor degree cochain tuple

theorem fullComplex_exactAt_positive (anchor : Chart) (degree : ℕ) :
    (fullComplex 𝕜 Chart).ExactAt (degree + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ degree (degree + 1) (degree + 2)
    (by simp) (by simp)).mpr
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cochain cycle
  refine ⟨fullContraction 𝕜 anchor degree cochain, ?_⟩
  have identity := fullContraction_identity 𝕜 anchor degree cochain
  change (fullComplex 𝕜 Chart).d (degree + 1) (degree + 2) cochain = 0 at cycle
  rwa [cycle, map_zero, add_zero] at identity

theorem fullComplex_homology_positive_isZero (anchor : Chart) (degree : ℕ) :
    IsZero ((fullComplex 𝕜 Chart).homology (degree + 1)) :=
  (fullComplex_exactAt_positive 𝕜 anchor degree).isZero_homology

def fullDegreeZeroConstant : 𝕜 →+ ((Fin 1 → Chart) → 𝕜) where
  toFun scalar _tuple := scalar
  map_zero' := rfl
  map_add' _first _second := rfl

theorem fullDegreeZeroConstant_d :
    AddCommGrpCat.ofHom (fullDegreeZeroConstant 𝕜 (Chart := Chart)) ≫
      (fullComplex 𝕜 Chart).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  funext tuple
  change (fullComplex 𝕜 Chart).d 0 1 (fun _tuple => scalar) tuple = 0
  rw [fullComplex_d_apply]
  simp [scalarSimplexDifferential, Fin.sum_univ_two]

theorem fullDegreeZeroCycle_constant (anchor : Chart)
    (cochain : (fullComplex 𝕜 Chart).X 0) (cycle : (fullComplex 𝕜 Chart).d 0 1 cochain = 0)
    (tuple : Fin 1 → Chart) : cochain tuple = cochain (fun _column => anchor) := by
  let pair : Fin 2 → Chart := Fin.cons anchor (fun _column => tuple 0)
  have firstFace : pair ∘ (0 : Fin 2).succAbove = tuple := by
    funext column
    have columnZero : column = 0 := Subsingleton.elim _ _
    subst column
    rfl
  have secondFace : pair ∘ (1 : Fin 2).succAbove = fun _column => anchor := by
    funext column
    have columnZero : column = 0 := Subsingleton.elim _ _
    subst column
    rfl
  have evaluated := congrFun cycle pair
  rw [fullComplex_d_apply] at evaluated
  change scalarSimplexDifferential 𝕜 0 cochain pair = (0 : 𝕜) at evaluated
  unfold scalarSimplexDifferential at evaluated
  rw [Fin.sum_univ_two] at evaluated
  simp only [Fin.val_zero, pow_zero,
    one_mul, Fin.val_one, pow_one, firstFace, secondFace, neg_one_mul] at evaluated
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using evaluated)

noncomputable def fullCyclesDegreeZeroIso (anchor : Chart) :
    AddCommGrpCat.of 𝕜 ≅ (fullComplex 𝕜 Chart).cycles 0 where
  hom := (fullComplex 𝕜 Chart).liftCycles (AddCommGrpCat.ofHom (fullDegreeZeroConstant 𝕜)) 1
    (by simp) (fullDegreeZeroConstant_d 𝕜)
  inv := (fullComplex 𝕜 Chart).iCycles 0 ≫
    AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun _tuple : Fin 1 → Chart => 𝕜)
      (fun _column => anchor))
  hom_inv_id := by
    rw [← Category.assoc, HomologicalComplex.liftCycles_i]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro scalar
    rfl
  inv_hom_id := by
    apply (cancel_mono ((fullComplex 𝕜 Chart).iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.liftCycles_i, Category.id_comp]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro cycle
    funext tuple
    have closed := ConcreteCategory.congr_hom ((fullComplex 𝕜 Chart).iCycles_d 0 1) cycle
    exact (fullDegreeZeroCycle_constant 𝕜 anchor ((fullComplex 𝕜 Chart).iCycles 0 cycle)
      closed tuple).symm

noncomputable def fullHomologyDegreeZeroIso (anchor : Chart) :
    AddCommGrpCat.of 𝕜 ≅ (fullComplex 𝕜 Chart).homology 0 :=
  fullCyclesDegreeZeroIso 𝕜 anchor ≪≫ asIso ((fullComplex 𝕜 Chart).homologyπ 0)

noncomputable def negativeConstantAugmentation (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) :
    AddCommGrpCat.of 𝕜 ⟶ (negativeComplex 𝕜 incidence negative).homology 0 :=
  (fullHomologyDegreeZeroIso 𝕜 anchor).hom ≫
    HomologicalComplex.homologyMap (negativeComplexRestriction 𝕜 incidence negative) 0

noncomputable def negativeAugmentedDegreeZero (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) : AddCommGrpCat :=
  cokernel (negativeConstantAugmentation 𝕜 incidence negative anchor)

noncomputable def negativePositiveHomologyShiftIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) (degree : ℕ) :
    (negativeComplex 𝕜 incidence negative).homology (degree + 1) ≅
      (relativeComplex 𝕜 incidence negative).homology (degree + 2) :=
  (relativeShortComplex_shortExact 𝕜 incidence negative).δIso (degree + 1) (degree + 2) (by simp)
    (fullComplex_homology_positive_isZero 𝕜 anchor degree)
    (fullComplex_homology_positive_isZero 𝕜 anchor (degree + 1))

noncomputable def negativeReducedDegreeZero (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : AddCommGrpCat :=
  cokernel (HomologicalComplex.homologyMap (negativeComplexRestriction 𝕜 incidence negative) 0)

noncomputable def negativeReducedDegreeZeroShiftIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) :
    negativeReducedDegreeZero 𝕜 incidence negative ≅ (relativeComplex 𝕜 incidence negative).homology 1 := by
  let exactSequence := (relativeShortComplex_shortExact 𝕜 incidence negative).homology_exact₃ 0 1 (by simp)
  letI : Epi ((relativeShortComplex_shortExact 𝕜 incidence negative).δ 0 1 (by simp)) :=
    (relativeShortComplex_shortExact 𝕜 incidence negative).epi_δ 0 1 (by simp)
      (fullComplex_homology_positive_isZero 𝕜 anchor 0)
  exact (cokernelIsCokernel
    (HomologicalComplex.homologyMap (negativeComplexRestriction 𝕜 incidence negative) 0)).coconePointUniqueUpToIso
      exactSequence.gIsCokernel

noncomputable def negativeAugmentedDegreeZeroShiftIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) :
    negativeAugmentedDegreeZero 𝕜 incidence negative anchor ≅
      (relativeComplex 𝕜 incidence negative).homology 1 := by
  let augmentedCokernel := (cokernel.ofIsoComp
    (HomologicalComplex.homologyMap (negativeComplexRestriction 𝕜 incidence negative) 0)
    (negativeConstantAugmentation 𝕜 incidence negative anchor)
    (fullHomologyDegreeZeroIso 𝕜 anchor).symm (by simp [negativeConstantAugmentation]))
  exact (cokernelIsCokernel (negativeConstantAugmentation 𝕜 incidence negative anchor)).coconePointUniqueUpToIso
    augmentedCokernel ≪≫ (negativeReducedDegreeZeroShiftIso 𝕜 incidence negative anchor)



/-- Reduced degree minus one is the kernel of the actual constant
augmentation. This retains the empty-complex convention. -/
def negativeReducedMinusOne (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) : AddCommGrpCat :=
  kernel (negativeConstantAugmentation 𝕜 incidence negative anchor)

/-- The initial part of the same actual long exact sequence, including
cohomological degree zero. -/
def relativeHomologyDegreeZeroIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) :
    (relativeComplex 𝕜 incidence negative).homology 0 ≅
      negativeReducedMinusOne 𝕜 incidence negative anchor := by
  let inclusion := relativeComplexInclusion 𝕜 incidence negative
  let restriction := negativeComplexRestriction 𝕜 incidence negative
  letI : Mono (inclusion.f 0) :=
    (AddCommGrpCat.mono_iff_injective _).mpr
      (relativeDegreeInclusion_injective 𝕜 incidence negative 0)
  letI : Mono (HomologicalComplex.homologyMap inclusion 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel inclusion 0
      (fun degree => by simp)
  letI : Mono (HomologicalComplex.homologyMap
      (relativeShortComplex 𝕜 incidence negative).f 0) := by
    change Mono (HomologicalComplex.homologyMap inclusion 0)
    infer_instance
  let exactSequence := (relativeShortComplex_shortExact 𝕜 incidence negative).homology_exact₂ 0
  exact exactSequence.fIsKernel.conePointUniqueUpToIso
      (kernelIsKernel (HomologicalComplex.homologyMap restriction 0)) ≪≫
    (kernelIsIsoComp (fullHomologyDegreeZeroIso 𝕜 anchor).hom
      (HomologicalComplex.homologyMap restriction 0)).symm

/-- The integer degree `p-1`, encoded by the nonnegative integer `p`.
At `p=0` this is the genuine augmented degree-minus-one kernel. -/
def negativeReducedShifted (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) : ℕ → AddCommGrpCat
  | 0 => negativeReducedMinusOne 𝕜 incidence negative anchor
  | 1 => negativeAugmentedDegreeZero 𝕜 incidence negative anchor
  | degree + 2 => (negativeComplex 𝕜 incidence negative).homology (degree + 1)

/-- All degrees of the relative incidence comparison, including the
empty-negative-complex degree-zero case. -/
def relativeHomologyReducedIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) (degree : ℕ) :
    (relativeComplex 𝕜 incidence negative).homology degree ≅
      negativeReducedShifted 𝕜 incidence negative anchor degree := by
  rcases degree with _ | (_ | degree)
  · exact relativeHomologyDegreeZeroIso 𝕜 incidence negative anchor
  · exact (negativeAugmentedDegreeZeroShiftIso 𝕜 incidence negative anchor).symm
  · exact (negativePositiveHomologyShiftIso 𝕜 incidence negative anchor degree).symm

end ToricPower.NegativeSupportRelative
