module

public import Mathlib.Algebra.Category.Grp.Zero

public import ToricPower.CechIncidenceChains

/-!
# Constant augmentation without choosing a vertex

The constant degree-zero cochain exists even when the vertex type is empty.
Its cycle class defines the canonical augmentation. Reduced degree minus
one is its kernel, degree zero its cokernel, and higher degrees the actual
cochain homology. This retains the empty-complex convention without a
chosen negative ray.

The existing relative-complex comparison is transported to this canonical
augmentation using the actual constant cochain formula. Candidate source,
pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open ToricPower.NegativeSupportRelative ToricPower.CechIncidenceChains
open scoped Classical

namespace ToricPower.CechCanonicalAugmentation

variable (𝕜 : Type) [Field 𝕜]
variable {Ray : Type*} {Chart : Type}

/-- The literal constant cochain on the actual allowed vertices. -/
def negativeConstantCochain (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    AddCommGrpCat.of 𝕜 ⟶ (negativeComplex 𝕜 incidence negative).X 0 :=
  AddCommGrpCat.ofHom
    { toFun := fun scalar _tuple => scalar
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem negativeConstantCochain_d (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    negativeConstantCochain 𝕜 incidence negative ≫
      (negativeComplex 𝕜 incidence negative).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  funext tuple
  change (negativeComplex 𝕜 incidence negative).d 0 1 (fun _tuple => scalar) tuple = 0
  rw [negativeComplex_d_apply]
  change (∑ deleted : Fin 2, ((-1 : ℤ) ^ deleted.val) • scalar) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, add_neg_cancel]

/-- Actual constant cycles, with no nonempty-vertex assumption. -/
def negativeConstantCycles (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    AddCommGrpCat.of 𝕜 ⟶ (negativeComplex 𝕜 incidence negative).cycles 0 :=
  (negativeComplex 𝕜 incidence negative).liftCycles
    (negativeConstantCochain 𝕜 incidence negative) 1 (by simp)
    (negativeConstantCochain_d 𝕜 incidence negative)

/-- Canonical constant augmentation, also defined on an empty complex. -/
def canonicalNegativeAugmentation (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    AddCommGrpCat.of 𝕜 ⟶ (negativeComplex 𝕜 incidence negative).homology 0 :=
  negativeConstantCycles 𝕜 incidence negative ≫
    (negativeComplex 𝕜 incidence negative).homologyπ 0

@[reassoc (attr := simp)]
theorem negativeConstantCycles_i (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    negativeConstantCycles 𝕜 incidence negative ≫
      (negativeComplex 𝕜 incidence negative).iCycles 0 =
        negativeConstantCochain 𝕜 incidence negative :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- Restricting an ambient constant cochain gives exactly a constant
cochain on the actual negative tuples. -/
theorem fullConstant_restriction (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    AddCommGrpCat.ofHom (fullDegreeZeroConstant 𝕜 (Chart := Chart)) ≫
      (negativeComplexRestriction 𝕜 incidence negative).f 0 =
        negativeConstantCochain 𝕜 incidence negative := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  rfl

/-- The anchor in the old construction affects only the inverse of the
full-simplex isomorphism. Its augmentation is this canonical constant map. -/
theorem negativeConstantAugmentation_eq_canonical
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) (anchor : Chart) :
    negativeConstantAugmentation 𝕜 incidence negative anchor =
      canonicalNegativeAugmentation 𝕜 incidence negative := by
  have cycles : (fullCyclesDegreeZeroIso 𝕜 anchor).hom ≫
      HomologicalComplex.cyclesMap (negativeComplexRestriction 𝕜 incidence negative) 0 =
        negativeConstantCycles 𝕜 incidence negative := by
    apply (cancel_mono ((negativeComplex 𝕜 incidence negative).iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc]
    dsimp only [fullCyclesDegreeZeroIso]
    rw [HomologicalComplex.liftCycles_i, negativeConstantCycles_i]
    exact fullConstant_restriction 𝕜 incidence negative
  change ((fullCyclesDegreeZeroIso 𝕜 anchor).hom ≫
      (fullComplex 𝕜 Chart).homologyπ 0) ≫
        HomologicalComplex.homologyMap (negativeComplexRestriction 𝕜 incidence negative) 0 = _
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, cycles]
  rfl

/-- Degree `p-1` of reduced cohomology, including the degree-minus-one
kernel. No anchor and no nonempty-vertex type are required. -/
def canonicalNegativeReducedShifted (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) : ℕ → AddCommGrpCat
  | 0 => kernel (canonicalNegativeAugmentation 𝕜 incidence negative)
  | 1 => cokernel (canonicalNegativeAugmentation 𝕜 incidence negative)
  | degree + 2 => (negativeComplex 𝕜 incidence negative).homology (degree + 1)

def negativeReducedShiftedCanonicalIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) (degree : ℕ) :
    negativeReducedShifted 𝕜 incidence negative anchor degree ≅
      canonicalNegativeReducedShifted 𝕜 incidence negative degree := by
  rcases degree with _ | (_ | degree)
  · change kernel (negativeConstantAugmentation 𝕜 incidence negative anchor) ≅
      kernel (canonicalNegativeAugmentation 𝕜 incidence negative)
    exact eqToIso (by rw [negativeConstantAugmentation_eq_canonical])
  · change cokernel (negativeConstantAugmentation 𝕜 incidence negative anchor) ≅
      cokernel (canonicalNegativeAugmentation 𝕜 incidence negative)
    exact eqToIso (by rw [negativeConstantAugmentation_eq_canonical])
  · exact Iso.refl _

/-- Only the actual ambient chart cover needs an anchor in the relative
comparison. The resulting reduced complex itself requires none. -/
def relativeHomologyCanonicalReducedIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (anchor : Chart) (degree : ℕ) :
    (ToricPower.NegativeSupportCech.relativeComplex 𝕜 incidence negative).homology degree ≅
      canonicalNegativeReducedShifted 𝕜 incidence negative degree :=
  relativeHomologyReducedIso 𝕜 incidence negative anchor degree ≪≫
    negativeReducedShiftedCanonicalIso 𝕜 incidence negative anchor degree

section EmptyComplex

variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable [IsEmpty (forbiddenTuple incidence negative 0)]

/-- If there are no actual vertices, every tuple degree is empty. -/
theorem forbiddenTuple_isEmpty_of_no_vertices (degree : ℕ) :
    IsEmpty (forbiddenTuple incidence negative degree) := by
  refine ⟨fun tuple => ?_⟩
  let vertex : forbiddenTuple incidence negative 0 :=
    ⟨fun _column => tuple.val 0,
      ToricPower.NegativeSupportCech.tupleForbidden_precomp incidence negative
        (fun _column : Fin 1 => (0 : Fin (degree + 1))) tuple.val tuple.property⟩
  exact isEmptyElim vertex

theorem negativeHomology_isZero_of_no_vertices (degree : ℕ) :
    IsZero ((negativeComplex 𝕜 incidence negative).homology degree) := by
  letI := forbiddenTuple_isEmpty_of_no_vertices incidence negative degree
  have zeroDegree : IsZero ((negativeComplex 𝕜 incidence negative).X degree) := by
    change IsZero (AddCommGrpCat.of (forbiddenTuple incidence negative degree → 𝕜))
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact (HomologicalComplex.ExactAt.of_isZero zeroDegree).isZero_homology

theorem canonicalNegativeAugmentation_eq_zero_of_no_vertices :
    canonicalNegativeAugmentation 𝕜 incidence negative = 0 := by
  have zeroCochain : negativeConstantCochain 𝕜 incidence negative = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro scalar
    funext tuple
    exact isEmptyElim tuple
  have zeroCycles : negativeConstantCycles 𝕜 incidence negative = 0 := by
    apply (cancel_mono ((negativeComplex 𝕜 incidence negative).iCycles 0)).mp
    rw [negativeConstantCycles_i, zeroCochain, zero_comp]
  unfold canonicalNegativeAugmentation
  rw [zeroCycles, zero_comp]

/-- The empty-complex reduced degree minus one is literally the scalar
coefficient group, established through the actual kernel of the zero map. -/
def canonicalReducedMinusOneIsoOfNoVertices :
    canonicalNegativeReducedShifted 𝕜 incidence negative 0 ≅ AddCommGrpCat.of 𝕜 := by
  change kernel (canonicalNegativeAugmentation 𝕜 incidence negative) ≅ AddCommGrpCat.of 𝕜
  calc
    kernel (canonicalNegativeAugmentation 𝕜 incidence negative) ≅
        kernel (0 : AddCommGrpCat.of 𝕜 ⟶ (negativeComplex 𝕜 incidence negative).homology 0) :=
      eqToIso (by rw [canonicalNegativeAugmentation_eq_zero_of_no_vertices])
    _ ≅ AddCommGrpCat.of 𝕜 := kernelZeroIsoSource

theorem canonicalReducedPositive_isZero_of_no_vertices (degree : ℕ) :
    IsZero (canonicalNegativeReducedShifted 𝕜 incidence negative (degree + 1)) := by
  rcases degree with _ | degree
  · change IsZero (cokernel (canonicalNegativeAugmentation 𝕜 incidence negative))
    exact (negativeHomology_isZero_of_no_vertices 𝕜 incidence negative 0).of_iso
      (eqToIso (by rw [canonicalNegativeAugmentation_eq_zero_of_no_vertices]) ≪≫
        cokernelZeroIsoTarget)
  · exact negativeHomology_isZero_of_no_vertices 𝕜 incidence negative (degree + 1)

end EmptyComplex

section Naturality

variable {Ray' : Type*} {Chart' : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable (incidence' : Ray' → Chart' → Prop) (negative' : Ray' → Prop)

/-- Every actual cochain map preserving constant cochains preserves the
canonical augmentation on homology. -/
theorem canonicalNegativeAugmentation_naturality
    (mapping : negativeComplex 𝕜 incidence negative ⟶ negativeComplex 𝕜 incidence' negative')
    (constant : negativeConstantCochain 𝕜 incidence negative ≫ mapping.f 0 =
      negativeConstantCochain 𝕜 incidence' negative') :
    canonicalNegativeAugmentation 𝕜 incidence negative ≫
      HomologicalComplex.homologyMap mapping 0 =
        canonicalNegativeAugmentation 𝕜 incidence' negative' := by
  have cycles : negativeConstantCycles 𝕜 incidence negative ≫
      HomologicalComplex.cyclesMap mapping 0 =
        negativeConstantCycles 𝕜 incidence' negative' := by
    apply (cancel_mono ((negativeComplex 𝕜 incidence' negative').iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      negativeConstantCycles_i_assoc, negativeConstantCycles_i]
    exact constant
  unfold canonicalNegativeAugmentation
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, cycles]

/-- The actual homology isomorphisms and their augmented degree-zero
square induce the isomorphism in every reduced degree. -/
def canonicalReducedIsoOfHomologyIso
    (equivalences : ∀ degree,
      (negativeComplex 𝕜 incidence negative).homology degree ≅
        (negativeComplex 𝕜 incidence' negative').homology degree)
    (constant : canonicalNegativeAugmentation 𝕜 incidence negative ≫
      (equivalences 0).hom = canonicalNegativeAugmentation 𝕜 incidence' negative')
    (degree : ℕ) :
    canonicalNegativeReducedShifted 𝕜 incidence negative degree ≅
      canonicalNegativeReducedShifted 𝕜 incidence' negative' degree := by
  rcases degree with _ | (_ | degree)
  · exact kernel.mapIso _ _ (Iso.refl _) (equivalences 0)
      (by simpa only [Iso.refl_hom, Category.id_comp] using constant)
  · exact cokernel.mapIso _ _ (Iso.refl _) (equivalences 0)
      (by simpa only [Iso.refl_hom, Category.id_comp] using constant)
  · exact equivalences (degree + 1)

/-- In particular, a genuine constant-preserving cochain homotopy
equivalence gives every reduced-cohomology isomorphism. -/
def canonicalReducedIsoOfHomotopyEquiv
    (equivalence : HomotopyEquiv (negativeComplex 𝕜 incidence negative)
      (negativeComplex 𝕜 incidence' negative'))
    (constant : negativeConstantCochain 𝕜 incidence negative ≫ equivalence.hom.f 0 =
      negativeConstantCochain 𝕜 incidence' negative') (degree : ℕ) :
    canonicalNegativeReducedShifted 𝕜 incidence negative degree ≅
      canonicalNegativeReducedShifted 𝕜 incidence' negative' degree :=
  canonicalReducedIsoOfHomologyIso 𝕜 incidence negative incidence' negative'
    (fun degree => equivalence.toHomologyIso degree)
    (canonicalNegativeAugmentation_naturality 𝕜 incidence negative incidence' negative'
      equivalence.hom constant) degree

end Naturality

section AugmentedChainDuality

variable {Ray' : Type*} {Chart' : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable (incidence' : Ray' → Chart' → Prop) (negative' : Ray' → Prop)

/-- The character sending the integral augmentation generator to a scalar. -/
def augmentationScalar (scalar : 𝕜) : incidenceAugmentationObject ⟶ AddCommGrpCat.of 𝕜 :=
  Sigma.desc (fun _point : Unit => AddCommGrpCat.ofHom (zmultiplesHom 𝕜 scalar))

theorem incidenceDualExtension_constant (scalar : 𝕜) :
    incidenceDualExtension 𝕜 incidence negative 0 (fun _tuple => scalar) =
      incidenceChainAugmentation incidence negative ≫ augmentationScalar 𝕜 scalar := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  change incidenceChainInclusion incidence negative 0 tuple ≫ _ =
    incidenceChainInclusion incidence negative 0 tuple ≫ _
  rw [← Category.assoc, incidenceChainAugmentation_generator]
  unfold incidenceDualExtension incidenceChainInclusion augmentationScalar
  rw [SSet.ιChainComplex, Sigma.ι_comp_desc, Sigma.ι_comp_desc]

/-- The inverse of the actual cochain comparison is exactly extension
from values on the free integral tuple generators. -/
theorem incidenceDualIso_inv_apply (degree : ℕ)
    (cochain : (negativeComplex 𝕜 incidence negative).X degree) :
    (incidenceDualIso 𝕜 incidence negative).inv.f degree cochain =
      incidenceDualExtension 𝕜 incidence negative degree cochain := by
  apply incidenceDualEvaluation_injective 𝕜 incidence negative degree
  have inverse := congrArg
    (fun mapping : negativeComplex 𝕜 incidence negative ⟶ negativeComplex 𝕜 incidence negative =>
      mapping.f degree) (incidenceDualIso 𝕜 incidence negative).inv_hom_id
  have values := ConcreteCategory.congr_hom inverse cochain
  change incidenceDualEvaluation 𝕜 incidence negative degree
    ((incidenceDualIso 𝕜 incidence negative).inv.f degree cochain) = cochain at values
  exact values.trans (incidenceDualEvaluation_extension 𝕜 incidence negative degree cochain).symm

/-- An actual map of integral incidence chains induces the actual scalar
cochain map, with the correct contravariant direction. -/
def negativeComplexDualMap
    (mapping : incidenceChains incidence negative ⟶ incidenceChains incidence' negative') :
    negativeComplex 𝕜 incidence' negative' ⟶ negativeComplex 𝕜 incidence negative :=
  (incidenceDualIso 𝕜 incidence' negative').inv ≫ dualChainMap 𝕜 mapping ≫
    (incidenceDualIso 𝕜 incidence negative).hom

theorem negativeComplexDualMap_apply
    (mapping : incidenceChains incidence negative ⟶ incidenceChains incidence' negative')
    (degree : ℕ) (cochain : (negativeComplex 𝕜 incidence' negative').X degree) :
    (negativeComplexDualMap 𝕜 incidence negative incidence' negative' mapping).f degree cochain =
      incidenceDualEvaluation 𝕜 incidence negative degree
        (mapping.f degree ≫ incidenceDualExtension 𝕜 incidence' negative' degree cochain) := by
  change incidenceDualEvaluation 𝕜 incidence negative degree
    ((dualChainMap 𝕜 mapping).f degree
      ((incidenceDualIso 𝕜 incidence' negative').inv.f degree cochain)) = _
  rw [incidenceDualIso_inv_apply]
  rfl

/-- Literal preservation of the integral augmentation implies literal
preservation of constant cochains, including on empty tuple complexes. -/
theorem negativeComplexDualMap_constant
    (mapping : incidenceChains incidence negative ⟶ incidenceChains incidence' negative')
    (augmented : mapping.f 0 ≫ incidenceChainAugmentation incidence' negative' =
      incidenceChainAugmentation incidence negative) :
    negativeConstantCochain 𝕜 incidence' negative' ≫
      (negativeComplexDualMap 𝕜 incidence negative incidence' negative' mapping).f 0 =
        negativeConstantCochain 𝕜 incidence negative := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  change (negativeComplexDualMap 𝕜 incidence negative incidence' negative' mapping).f 0
    (fun _tuple => scalar) = (fun _tuple => scalar)
  rw [negativeComplexDualMap_apply, incidenceDualExtension_constant,
    ← Category.assoc, augmented, ← incidenceDualExtension_constant,
    incidenceDualEvaluation_extension]

/-- The scalar-dual homotopy equivalence transported through the actual
incidence-to-cochain isomorphisms. -/
def negativeComplexHomotopyEquiv
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      (incidenceChains incidence' negative')) :
    HomotopyEquiv (negativeComplex 𝕜 incidence negative)
      (negativeComplex 𝕜 incidence' negative') :=
  ((HomotopyEquiv.ofIso (incidenceDualIso 𝕜 incidence negative).symm).trans
    (dualChainHomotopyEquiv 𝕜 equivalence)).trans
      (HomotopyEquiv.ofIso (incidenceDualIso 𝕜 incidence' negative'))

/-- A genuine augmented integral chain equivalence preserves every reduced
cohomology degree. There is no choice of a vertex in either complex. -/
def canonicalReducedIsoOfAugmentedChainHomotopyEquiv
    (equivalence : HomotopyEquiv (incidenceChains incidence negative)
      (incidenceChains incidence' negative'))
    (augmentedInverse : equivalence.inv.f 0 ≫ incidenceChainAugmentation incidence negative =
      incidenceChainAugmentation incidence' negative') (degree : ℕ) :
    canonicalNegativeReducedShifted 𝕜 incidence negative degree ≅
      canonicalNegativeReducedShifted 𝕜 incidence' negative' degree :=
  canonicalReducedIsoOfHomotopyEquiv 𝕜 incidence negative incidence' negative'
    (negativeComplexHomotopyEquiv 𝕜 incidence negative incidence' negative' equivalence)
    (by
      change negativeConstantCochain 𝕜 incidence negative ≫
        ((incidenceDualIso 𝕜 incidence negative).inv ≫ dualChainMap 𝕜 equivalence.inv ≫
          (incidenceDualIso 𝕜 incidence' negative').hom).f 0 = _
      exact negativeComplexDualMap_constant 𝕜 incidence' negative' incidence negative
        equivalence.inv augmentedInverse) degree

end AugmentedChainDuality

end ToricPower.CechCanonicalAugmentation
