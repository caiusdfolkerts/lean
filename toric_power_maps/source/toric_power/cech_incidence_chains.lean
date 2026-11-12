module

public import ToricPower.CechNegativeRelative
public import ToricPower.CechAcyclicCarrier
public import TauCeti.AlgebraicTopology.SimplicialComplex.IsCone
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Tactic.FinCases

/-!
# Actual incidence chains, their dual cochains, and cone contractions

The simplicial set consists of the actual forbidden chart tuples. Its
integral chains have the actual coproduct-of-generators construction.
Evaluation on a generator identifies the scalar dual complex with the
literal negative-chart cochain complex. A genuine cone predicate gives
an explicit extra degeneracy, hence a chain contraction and actual
augmented/positive exactness.

Generic bodies are extracted from BondalThomsen commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb; precise source blocks and hashes
are recorded in audit/divisor_weights/cech_incidence_chains_provenance.json.
No convex realization or unproved nerve equivalence is imported.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace ToricPower.CechIncidenceChains

section IncidenceChains

variable {Ray : Type*} {Chart : Type}

def incidenceSimplicialSet (incidence : Ray → Chart → Prop) (negative : Ray → Prop) : SSet.{0} where
  obj simplex := forbiddenTuple incidence negative simplex.unop.len
  map selection := ↾fun tuple => ⟨tuple.val ∘ selection.unop.toOrderHom,
    tupleForbidden_precomp incidence negative selection.unop.toOrderHom tuple.val tuple.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable abbrev incidenceChains (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  (incidenceSimplicialSet incidence negative).chainComplex (AddCommGrpCat.of ℤ)

noncomputable def incidenceChainInclusion (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    AddCommGrpCat.of ℤ ⟶ (incidenceChains incidence negative).X degree :=
  (incidenceSimplicialSet incidence negative).ιChainComplex (R := AddCommGrpCat.of ℤ) tuple


end IncidenceChains

section ScalarDual

variable (𝕜 : Type) [Field 𝕜]

noncomputable def scalarCoefficientDual : AddCommGrpCat.{0}ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  CategoryTheory.preadditiveYoneda.obj (AddCommGrpCat.of 𝕜)

variable {𝕜} in
instance scalarCoefficientDual_additive : (scalarCoefficientDual 𝕜).Additive :=
  CategoryTheory.additive_yonedaObj' _

noncomputable abbrev dualChainComplex (complex : ChainComplex AddCommGrpCat.{0} ℕ) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  ((scalarCoefficientDual 𝕜).mapHomologicalComplex _).obj complex.op

noncomputable def dualChainMap {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    (mapping : source ⟶ target) : dualChainComplex 𝕜 target ⟶ dualChainComplex 𝕜 source :=
  ((scalarCoefficientDual 𝕜).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map mapping.op)

theorem dualChainMap_id (complex : ChainComplex AddCommGrpCat.{0} ℕ) :
    dualChainMap 𝕜 (𝟙 complex) = 𝟙 (dualChainComplex 𝕜 complex) := by
  simp [dualChainMap]

theorem dualChainMap_comp {source middle target : ChainComplex AddCommGrpCat.{0} ℕ}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    dualChainMap 𝕜 (first ≫ second) = dualChainMap 𝕜 second ≫ dualChainMap 𝕜 first := by
  simp [dualChainMap]

noncomputable def dualChainHomotopy {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    {first second : source ⟶ target} (homotopy : Homotopy first second) :
    Homotopy (dualChainMap 𝕜 first) (dualChainMap 𝕜 second) :=
  (scalarCoefficientDual 𝕜).mapHomotopy homotopy.op

noncomputable def dualChainHomotopyEquiv {source target : ChainComplex AddCommGrpCat.{0} ℕ}
    (equivalence : HomotopyEquiv source target) :
    HomotopyEquiv (dualChainComplex 𝕜 source) (dualChainComplex 𝕜 target) where
  hom := dualChainMap 𝕜 equivalence.inv
  inv := dualChainMap 𝕜 equivalence.hom
  homotopyHomInvId := by
    have homotopy := dualChainHomotopy 𝕜 equivalence.homotopyHomInvId
    simpa only [dualChainMap_comp, dualChainMap_id] using homotopy
  homotopyInvHomId := by
    have homotopy := dualChainHomotopy 𝕜 equivalence.homotopyInvHomId
    simpa only [dualChainMap_comp, dualChainMap_id] using homotopy


variable {Chart : Type}

theorem negativeComplex_d_apply {Ray : Type*} (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree)
    (tuple : forbiddenTuple incidence negative (degree + 1)) :
    (negativeComplex 𝕜 incidence negative).d degree (degree + 1) cochain tuple =
      ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
        cochain ⟨tuple.val ∘ deleted.succAbove,
          tupleForbidden_precomp incidence negative deleted.succAbove tuple.val tuple.property⟩ := by
  let evaluation : ((negativeComplex 𝕜 incidence negative).X degree ⟶
      (negativeComplex 𝕜 incidence negative).X (degree + 1)) →+ 𝕜 :=
    (Pi.evalAddMonoidHom (fun _tuple : forbiddenTuple incidence negative (degree + 1) => 𝕜) tuple).comp
      ((AddMonoidHom.eval cochain).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom)
  change evaluation ((negativeComplex 𝕜 incidence negative).d degree (degree + 1)) = _
  have differential : (negativeComplex 𝕜 incidence negative).d degree (degree + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD (negativeCosimplicial 𝕜 incidence negative) degree := by
    simp only [negativeComplex, AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rw [differential, AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum]
  apply Finset.sum_congr rfl
  intro deleted _present
  rw [map_zsmul]
  rfl

section DualIdentification

variable {Ray : Type*} {Chart : Type}

noncomputable def incidenceDualEvaluation (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree ⟶
      (negativeComplex 𝕜 incidence negative).X degree :=
  AddCommGrpCat.ofHom {
    toFun := fun cochain tuple => (incidenceChainInclusion incidence negative degree tuple ≫ cochain) (1 : ℤ)
    map_zero' := by funext tuple; simp
    map_add' := by intro first second; funext tuple; simp
  }

noncomputable def incidenceDualExtension (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree :=
  Sigma.desc (fun tuple => AddCommGrpCat.ofHom (zmultiplesHom 𝕜 (cochain tuple)))

theorem incidenceDualEvaluation_extension (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree) :
    incidenceDualEvaluation 𝕜 incidence negative degree
      (incidenceDualExtension 𝕜 incidence negative degree cochain) = cochain := by
  funext tuple
  change (incidenceChainInclusion incidence negative degree tuple ≫
    incidenceDualExtension 𝕜 incidence negative degree cochain) (1 : ℤ) = cochain tuple
  rw [incidenceChainInclusion, incidenceDualExtension, SSet.ιChainComplex, Sigma.ι_comp_desc]
  change (zmultiplesHom 𝕜 (cochain tuple)) (1 : ℤ) = cochain tuple
  exact one_zsmul _

theorem incidenceDualEvaluation_injective (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    Function.Injective (incidenceDualEvaluation 𝕜 incidence negative degree) := by
  intro first second equal
  apply SSet.chainComplex_hom_ext
  intro tuple
  apply AddCommGrpCat.hom_ext
  have values : (incidenceChainInclusion incidence negative degree tuple ≫ first) (1 : ℤ) =
      (incidenceChainInclusion incidence negative degree tuple ≫ second) (1 : ℤ) := congrFun equal tuple
  exact (zmultiplesHom 𝕜).symm.injective values

noncomputable def incidenceDualDegreeIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).X degree ≅
      (negativeComplex 𝕜 incidence negative).X degree := by
  letI : IsIso (incidenceDualEvaluation 𝕜 incidence negative degree) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨incidenceDualEvaluation_injective 𝕜 incidence negative degree,
        fun cochain => ⟨incidenceDualExtension 𝕜 incidence negative degree cochain,
          incidenceDualEvaluation_extension 𝕜 incidence negative degree cochain⟩⟩
  exact asIso (incidenceDualEvaluation 𝕜 incidence negative degree)

theorem incidenceDualEvaluation_d (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (degree : ℕ) :
    (dualChainComplex 𝕜 (incidenceChains incidence negative)).d degree (degree + 1) ≫
      incidenceDualEvaluation 𝕜 incidence negative (degree + 1) =
    incidenceDualEvaluation 𝕜 incidence negative degree ≫
      (negativeComplex 𝕜 incidence negative).d degree (degree + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro cochain
  change (incidenceChains incidence negative).X degree ⟶ AddCommGrpCat.of 𝕜 at cochain
  funext tuple
  change ((incidenceChainInclusion incidence negative (degree + 1) tuple ≫
    (incidenceChains incidence negative).d (degree + 1) degree) ≫ cochain) (1 : ℤ) =
      (negativeComplex 𝕜 incidence negative).d degree (degree + 1)
        (incidenceDualEvaluation 𝕜 incidence negative degree cochain) tuple
  rw [incidenceChainInclusion, SSet.ιChainComplex_d,
    negativeComplex_d_apply, sum_comp]
  change AddCommGrpCat.homAddEquiv
    (∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val •
      (incidenceSimplicialSet incidence negative).ιChainComplex
        ((incidenceSimplicialSet incidence negative).δ deleted tuple)) ≫ cochain) (1 : ℤ) = _
  rw [map_sum]
  simp only [zsmul_comp, map_zsmul]
  rw [AddMonoidHom.finsetSum_apply]
  simp only [AddMonoidHom.zsmul_apply]
  rfl

noncomputable def incidenceDualComparison (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    dualChainComplex 𝕜 (incidenceChains incidence negative) ⟶ negativeComplex 𝕜 incidence negative :=
  CochainComplex.ofHom (incidenceDualEvaluation 𝕜 incidence negative)
    (fun degree => (incidenceDualEvaluation_d 𝕜 incidence negative degree).symm)

noncomputable def incidenceDualIso (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    dualChainComplex 𝕜 (incidenceChains incidence negative) ≅ negativeComplex 𝕜 incidence negative := by
  letI : ∀ degree, IsIso ((incidenceDualComparison 𝕜 incidence negative).f degree) :=
    fun degree => (incidenceDualDegreeIso 𝕜 incidence negative degree).isIso_hom
  letI := HomologicalComplex.Hom.isIso_of_components (incidenceDualComparison 𝕜 incidence negative)
  exact asIso (incidenceDualComparison 𝕜 incidence negative)

end DualIdentification

section ConeCochains

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (anchor : Chart)
variable (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def coneTuple (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    forbiddenTuple incidence negative (degree + 1) :=
  ⟨Fin.cons anchor tuple.val, by
    apply (tupleForbidden_iff_face incidence negative (degree + 1) _).mpr
    have enlarged := cone.insert_mem
      ((tupleForbidden_iff_face incidence negative degree tuple.val).mp tuple.property)
    convert enlarged using 1
    ext chart
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨column, rfl⟩
      refine Fin.cases ?_ (fun previous => ?_) column
      · exact Or.inl (Fin.cons_zero _ _)
      · exact Or.inr ⟨previous, by simp⟩
    · rintro (rfl | ⟨column, rfl⟩)
      · exact ⟨0, Fin.cons_zero _ _⟩
      · exact ⟨column.succ, Fin.cons_succ _ _ _⟩⟩

end ConeCochains


end ScalarDual

section IntegralCones

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

noncomputable abbrev incidenceAugmentationObject : AddCommGrpCat.{0} :=
  ∐ fun _point : Unit => AddCommGrpCat.of ℤ

def augmentedIncidenceSet : SimplicialObject.Augmented (Type) where
  left := incidenceSimplicialSet incidence negative
  right := Unit
  hom := { app := fun _simplex => ↾fun _tuple => () }

noncomputable def incidenceChainAugmentationMap :
    incidenceChains incidence negative ⟶
      (ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((SimplicialObject.Augmented.whiskering (Type) AddCommGrpCat.{0}).obj
      (sigmaConst.obj (AddCommGrpCat.of ℤ))).obj (augmentedIncidenceSet incidence negative))

noncomputable def incidenceChainAugmentation :
    (incidenceChains incidence negative).X 0 ⟶ incidenceAugmentationObject :=
  (incidenceChainAugmentationMap incidence negative).f 0

theorem incidenceChainAugmentation_generator (tuple : forbiddenTuple incidence negative 0) :
    incidenceChainInclusion incidence negative 0 tuple ≫ incidenceChainAugmentation incidence negative =
      Sigma.ι (fun _point : Unit => AddCommGrpCat.of ℤ) () := by
  unfold incidenceChainAugmentation incidenceChainAugmentationMap
  rw [AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change Sigma.ι (fun _tuple : forbiddenTuple incidence negative 0 => AddCommGrpCat.of ℤ) tuple ≫
    Sigma.map' (g := fun _tuple : forbiddenTuple incidence negative 0 => AddCommGrpCat.of ℤ)
      (f := fun _point : Unit => AddCommGrpCat.of ℤ)
      (fun _tuple => ()) (fun _tuple => 𝟙 (AddCommGrpCat.of ℤ)) = _
  simp

theorem incidenceChainAugmentation_zero :
    (incidenceChains incidence negative).d 1 0 ≫ incidenceChainAugmentation incidence negative = 0 := by
  have identity := (incidenceChainAugmentationMap incidence negative).comm 1 0
  rw [HomologicalComplex.single_obj_d] at identity
  rw [comp_zero] at identity
  exact identity.symm

variable (anchor : Chart) (cone : PreAbstractSimplicialComplex.IsCone
  (negativeChartComplex incidence negative) anchor)

def coneVertexTuple : forbiddenTuple incidence negative 0 :=
  ⟨fun _column => anchor, by
    obtain ⟨ray, negativeRay, contains⟩ := cone.apex_mem.2
    exact ⟨ray, negativeRay, fun _column => contains anchor (Finset.mem_singleton_self _)⟩⟩

def incidenceConeExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedIncidenceSet incidence negative) where
  s' := ↾fun _point => coneVertexTuple incidence negative anchor cone
  s degree := ↾coneTuple incidence negative anchor cone degree
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro point
    rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    fin_cases column
    rfl
  s_comp_δ₀ degree := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    simp [SimplicialObject.δ, SimplexCategory.δ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
  s_comp_δ degree deleted := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    dsimp [SimplicialObject.δ, SimplexCategory.δ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
    cases column using Fin.cases <;> simp
  s_comp_σ degree repeated := by
    apply ConcreteCategory.hom_ext
    intro tuple
    apply Subtype.ext
    funext column
    dsimp [SimplicialObject.σ, SimplexCategory.σ, incidenceSimplicialSet,
      coneTuple, augmentedIncidenceSet]
    cases column using Fin.cases <;> simp

noncomputable def incidenceConeChainHomotopyEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj (∐ fun _point : Unit => AddCommGrpCat.of ℤ)) :=
  ((incidenceConeExtraDegeneracy incidence negative anchor cone).map
    (sigmaConst.obj (AddCommGrpCat.of ℤ))).homotopyEquiv

noncomputable def incidenceConeChainContraction (degree : ℕ) :
    (incidenceChains incidence negative).X degree ⟶
      (incidenceChains incidence negative).X (degree + 1) :=
  -((incidenceConeChainHomotopyEquiv incidence negative anchor cone).homotopyHomInvId.hom
    degree (degree + 1))

theorem incidenceConeChainContraction_identity_zero :
    incidenceConeChainContraction incidence negative anchor cone 0 ≫
      (incidenceChains incidence negative).d 1 0 =
    𝟙 ((incidenceChains incidence negative).X 0) -
      incidenceChainAugmentation incidence negative ≫
        (incidenceConeChainHomotopyEquiv incidence negative anchor cone).inv.f 0 := by
  let equivalence := incidenceConeChainHomotopyEquiv incidence negative anchor cone
  have identity := equivalence.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, zero_add, Homotopy.prevD_chainComplex] at identity
  change incidenceChainAugmentation incidence negative ≫ equivalence.inv.f 0 = _ at identity
  change (-equivalence.homotopyHomInvId.hom 0 1) ≫ _ = _
  rw [neg_comp]
  have rearranged := congrArg (fun value => 𝟙 ((incidenceChains incidence negative).X 0) - value) identity
  have reversed := rearranged.symm
  change 𝟙 ((incidenceChains incidence negative).X 0) -
    (equivalence.homotopyHomInvId.hom 0 1 ≫ (incidenceChains incidence negative).d 1 0 +
      𝟙 ((incidenceChains incidence negative).X 0)) = _ at reversed
  have cancellation : ∀ value : (incidenceChains incidence negative).X 0 ⟶
      (incidenceChains incidence negative).X 0,
      𝟙 _ - (value + 𝟙 _) = -value := by intro value; abel
  rw [cancellation] at reversed
  exact reversed

include anchor cone in
theorem incidenceConeChains_augmentedExact :
    (ShortComplex.mk ((incidenceChains incidence negative).d 1 0)
      (incidenceChainAugmentation incidence negative) (incidenceChainAugmentation_zero incidence negative)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro cycle closed
  refine ⟨incidenceConeChainContraction incidence negative anchor cone 0 cycle, ?_⟩
  have identity := ConcreteCategory.congr_hom
    (incidenceConeChainContraction_identity_zero incidence negative anchor cone) cycle
  change (incidenceChains incidence negative).d 1 0
    (incidenceConeChainContraction incidence negative anchor cone 0 cycle) =
    cycle - (incidenceConeChainHomotopyEquiv incidence negative anchor cone).inv.f 0
      (incidenceChainAugmentation incidence negative cycle) at identity
  simpa only [closed, map_zero, sub_zero] using identity

include anchor cone in
theorem incidenceConeChains_homology_positive_isZero (degree : ℕ) :
    IsZero ((incidenceChains incidence negative).homology (degree + 1)) := by
  have singleZero : IsZero
      (((ChainComplex.single₀ AddCommGrpCat.{0}).obj
        (∐ fun _point : Unit => AddCommGrpCat.of ℤ)).X (degree + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  exact (HomologicalComplex.ExactAt.of_isZero singleZero).isZero_homology.of_iso
    ((incidenceConeChainHomotopyEquiv incidence negative anchor cone).toHomologyIso (degree + 1))

include anchor cone in
theorem incidenceConeChains_exactAt_positive (degree : ℕ) :
    (incidenceChains incidence negative).ExactAt (degree + 1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (incidenceConeChains_homology_positive_isZero incidence negative anchor cone degree)

end IntegralCones

end ToricPower.CechIncidenceChains
