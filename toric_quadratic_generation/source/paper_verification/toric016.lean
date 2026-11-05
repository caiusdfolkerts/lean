module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import paper_verification.toric002
public import paper_verification.toric010
public import paper_verification.toric013
public import paper_verification.toric022
public import paper_verification.toric024
public import paper_verification.toric025
public import paper_verification.toric032
public import paper_verification.toric033

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicPowerCharacters
section Source_ToricIntrinsicPowerCharacters

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicSectionCoaction
-- original header: public import PaperVerification.ToricFiniteCharacterSubspaces
-- original header: public import PaperVerification.ToricCartierTensorPowers

-- original header: @[expose] public section

/-!
# Actual tensor-power characters and finite spanning eigenvector families

The powers use the original normalized fractional frame raised to the
actual integer power. No new independently chosen torus trivialization
is introduced. Every finite family of genuine power sections is spanned
by finitely many genuine sections with literal character rational values.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricCharacters
open scoped Classical PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

theorem normalizedPower_unitFrames (D : CartierData X.left) (r : ℕ) :
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).localCocycle.HasUnitFramesOn
      T.torusOpen :=
  (torusNormalizedCartier k n X.left T.torus.left D).hasUnitFramesOn_nsmul
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D) r

def normalizedPowerCharacters (D : CartierData X.left) (r : ℕ) :
    Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusSectionCharacters k n X.left T.torus.left
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)

theorem normalizedPowerCharacters_isCharacterStable (D : CartierData X.left) (r : ℕ) :
    IsCharacterStable k (T.normalizedPowerCharacters D r) :=
  T.torusSectionCharacters_isCharacterStable_of_unitFrames
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r)

def normalizedPowerSectionCoordinates (D : CartierData X.left) (r : ℕ) :
    Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤) ≃ₗ[k]
      T.normalizedPowerCharacters D r :=
  torusSectionCoordinates k n X.left T.torus.left
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r)

theorem normalizedPowerSectionCoordinates_value (D : CartierData X.left) (r : ℕ)
    (s : Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤)) :
    openTorusRationalAlgHom k n X.left T.torus.left
      ((T.normalizedPowerSectionCoordinates D r s).val) =
      ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).globalSectionValue k s :=
  torusSectionCoordinates_value k n X.left T.torus.left _ _ s

/-- No finite-dimensionality of all global sections is needed: a finite
family has a finite spanning family of actual character-valued sections. -/
theorem exists_finite_torus_eigensections_of_unitFrames
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    {I : Type v} [Fintype I] (s : I→Γ(E.sheaf,⊤)) :
    ∃ F : Finset (Fin n→ℤ), ∃ e : F→Γ(E.sheaf,⊤),
      (∀ m : F,openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single m.val (1:k))=E.globalSectionValue k (e m)) ∧
      (∀ i : I,s i∈Submodule.span k (Set.range e)) := by
  let V := torusSectionCharacters k n X.left T.torus.left E
  let c := torusSectionCoordinates k n X.left T.torus.left E hE
  let L : Γ(E.sheaf,⊤) →ₗ[k] AddMonoidAlgebra k (Fin n→ℤ) :=
    V.subtype.comp c.toLinearMap
  have hLinj : Function.Injective L := Subtype.val_injective.comp c.injective
  let Q : Finset (AddMonoidAlgebra k (Fin n→ℤ)) := Finset.univ.image (fun i=>L (s i))
  have hQV : ∀ f∈Q,f∈V := by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact (c (s i)).property
  obtain ⟨F,hQF,hFV,-⟩ := exists_finite_character_subspace k V
    (T.torusSectionCharacters_isCharacterStable_of_unitFrames E hE) Q hQV
  have hsingle (m : F) : AddMonoidAlgebra.single m.val (1:k)∈V := by
    apply hFV
    rw [characterModule_eq_span]
    exact Submodule.subset_span ⟨m.val,m.property,rfl⟩
  let e : F→Γ(E.sheaf,⊤) := fun m=>c.symm ⟨AddMonoidAlgebra.single m.val 1,hsingle m⟩
  have hLe (m : F) : L (e m)=AddMonoidAlgebra.single m.val (1:k) := by
    change (c (c.symm ⟨AddMonoidAlgebra.single m.val 1,hsingle m⟩)).val=_
    rw [LinearEquiv.apply_symm_apply]
  have himage : L '' Set.range e =
      (fun m : Fin n→ℤ=>AddMonoidAlgebra.single m (1:k)) '' (F : Set (Fin n→ℤ)) := by
    ext f
    constructor
    · rintro ⟨t,⟨m,rfl⟩,rfl⟩
      exact ⟨m.val,m.property,(hLe m).symm⟩
    · rintro ⟨m,hm,rfl⟩
      exact ⟨e ⟨m,hm⟩,⟨⟨m,hm⟩,rfl⟩,hLe ⟨m,hm⟩⟩
  have hspan : (Submodule.span k (Set.range e)).map L = characterModule k (F : Set (Fin n→ℤ)) := by
    rw [Submodule.map_span,himage,characterModule_eq_span]
  refine ⟨F,e,?_,?_⟩
  · intro m
    have hv := torusSectionCoordinates_value k n X.left T.torus.left E hE (e m)
    change openTorusRationalAlgHom k n X.left T.torus.left (L (e m))=_ at hv
    rwa [hLe] at hv
  · intro i
    have hi : L (s i)∈(Submodule.span k (Set.range e)).map L := by
      rw [hspan]
      exact hQF (L (s i)) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨t,ht,hts⟩ := Submodule.mem_map.mp hi
    simpa only [hLinj hts] using ht

/-- The finite eigenvector replacement for genuine tensor powers used
in the intrinsic ample projective embedding. -/
theorem exists_finite_normalizedPower_eigensections
    (D : CartierData X.left) (r : ℕ) {I : Type v} [Fintype I]
    (s : I→Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤)) :
    ∃ F : Finset (Fin n→ℤ),
      ∃ e : F→Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤),
      (∀ m : F,openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single m.val (1:k))=
          ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).globalSectionValue k (e m)) ∧
      (∀ i : I,s i∈Submodule.span k (Set.range e)) :=
  T.exists_finite_torus_eigensections_of_unitFrames
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r) s

end PaperVerification.ToricSchemes.SplitToricEmbedding
end
end Source_ToricIntrinsicPowerCharacters
-- END ORIGINAL PaperVerification.ToricIntrinsicPowerCharacters


-- BEGIN ORIGINAL PaperVerification.ToricSectionLinearSystems
section Source_ToricSectionLinearSystems

-- original header: module

-- original header: public import PaperVerification.ToricSectionChartGenerators
-- original header: public import PaperVerification.ToricBaseSectionNaturality
-- original header: public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

-- original header: @[expose] public section

/-! # Linear changes of an actual finite system of Cartier sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι : Type u}

def sectionLinearForm (c : ι→₀k) : MvPolynomial ι k :=
  c.sum (fun i a=>MvPolynomial.C a*MvPolynomial.X i)

theorem sectionLinearForm_isHomogeneous (c : ι→₀k) :
    (sectionLinearForm k c).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem sectionLinearForm_eval {R : Type u} [CommRing R]
    (F : k→+*R) (v : ι→R) (c : ι→₀k) :
    MvPolynomial.eval₂Hom F v (sectionLinearForm k c)=
      c.sum (fun i a=>F a*v i) := by
  simp only [sectionLinearForm,Finsupp.sum,map_sum,map_mul,
    MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X']

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The local coefficients of genuine sections are linear over the
actual base ring. -/
def localCoefficientLinear (i : C.index) :
    Γ(C.sheaf,⊤)→ₗ[k]Γ(X,C.openSet i) where
  toFun := C.localCoefficient i
  map_add' s t := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      have hst : C.toCartierData.sectionValue ⊤ (s+t) =
          C.toCartierData.sectionValue ⊤ s+C.toCartierData.sectionValue ⊤ t :=
        (C.toCartierData.globalSectionValue k).map_add s t
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (s+t)) =
            C.toCartierData.sectionValue ⊤ (s+t)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (s+t)
        _ = C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)+
            C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField) := by
          rw [hst,add_div]
        _ = X.germToFunctionField (C.openSet i) (C.localCoefficient i s)+
            X.germToFunctionField (C.openSet i) (C.localCoefficient i t) :=
          congrArg₂ (·+·) (C.localCoefficient_value i s).symm
            (C.localCoefficient_value i t).symm
        _ = X.germToFunctionField (C.openSet i)
            (C.localCoefficient i s+C.localCoefficient i t) :=
          (map_add (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _
  map_smul' a s := by
    by_cases hU : Nonempty (C.openSet i)
    · letI := hU
      apply X.germToFunctionField_injective (C.openSet i)
      change X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s))=
        X.germToFunctionField (C.openSet i)
          (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s)
      calc
        X.germToFunctionField (C.openSet i) (C.localCoefficient i (a • s)) =
            C.toCartierData.globalSectionValue k (a • s)/(C.generator i : X.functionField) :=
          C.localCoefficient_value i (a • s)
        _ = (algebraMap k X.functionField a*C.toCartierData.globalSectionValue k s)/
            (C.generator i : X.functionField) :=
          congrArg (fun z : X.functionField=>z/(C.generator i : X.functionField))
            ((C.toCartierData.globalSectionValue k).map_smul a s)
        _ = algebraMap k X.functionField a*
            (C.toCartierData.globalSectionValue k s/(C.generator i : X.functionField)) :=
          mul_div_assoc _ _ _
        _ = X.germToFunctionField (C.openSet i) (BaseSections.scalarMap k X (C.openSet i) a)*
            X.germToFunctionField (C.openSet i) (C.localCoefficient i s) :=
          congrArg₂ (·*·) (BaseSections.germ_scalarMap k (C.openSet i) a).symm
            (C.localCoefficient_value i s).symm
        _ = X.germToFunctionField (C.openSet i)
            (BaseSections.scalarMap k X (C.openSet i) a*C.localCoefficient i s) :=
          (map_mul (X.germToFunctionField (C.openSet i)).hom _ _).symm
    · have hbot : C.openSet i=⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hU ⟨⟨x,hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
      exact Subsingleton.elim _ _

theorem localCoefficient_linearCombination (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k)
    (i : C.index) :
    C.localCoefficient i (Finsupp.linearCombination k s c)=
      c.sum (fun j a=>BaseSections.scalarMap k X (C.openSet i) a*
        C.localCoefficient i (s j)) := by
  change C.localCoefficientLinear k i (Finsupp.linearCombination k s c)=_
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    localCoefficientLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def]
  all_goals rfl

/-- The nonvanishing open of a linear combination lies in the union of
the nonvanishing opens of the genuine sections in that combination. -/
theorem nonvanishingOpen_linearCombination_le (s : ι→Γ(C.sheaf,⊤))
    (c : ι→₀k) :
    C.nonvanishingOpen (Finsupp.linearCombination k s c)≤
      ⨆ j,C.nonvanishingOpen (s j) := by
  intro x hx
  by_contra hnone
  have hnone' (j : ι) : x∉C.nonvanishingOpen (s j) :=
    fun hj=>hnone (Opens.mem_iSup.mpr ⟨j,hj⟩)
  obtain ⟨i,hxi⟩ := C.covers x
  have ht := (C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i _ x hxi).mp hx
  apply ht
  rw [C.localCoefficient_linearCombination k s c i]
  simp only [Finsupp.sum,map_sum,map_mul]
  apply Ideal.sum_mem
  intro j hj
  apply Ideal.mul_mem_left
  exact not_not.mp (fun h=>hnone' j
    ((C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i (s j) x hxi).mpr h))

theorem nonvanishing_cover_of_spans {κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    (hspan : ∀ i,∃ c : κ→₀k,Finsupp.linearCombination k t c=s i) :
    (⨆ j,C.nonvanishingOpen (t j))=⊤ := by
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  obtain ⟨c,hc⟩ := hspan i
  rw [← hc]
  exact C.nonvanishingOpen_linearCombination_le k t c

theorem sectionLinearForm_fieldValue (s : ι→Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionProjectiveFieldMap k s (sectionLinearForm k c)=
      C.toCartierData.sectionValue ⊤ (Finsupp.linearCombination k s c) := by
  rw [sectionProjectiveFieldMap,sectionLinearForm_eval]
  change _=C.toCartierData.globalSectionValue k (Finsupp.linearCombination k s c)
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
    Algebra.smul_def,RingHom.comp_apply]
  rfl

def sectionRatioPolynomialMap (s : ι→Γ(C.sheaf,⊤)) (den : Γ(C.sheaf,⊤)) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen den) :=
  MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.nonvanishingOpen den))
    (fun j=>C.ratioSection (s j) den)

theorem sectionRatioPolynomialMap_germ (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) [Nonempty (C.nonvanishingOpen den)] :
    (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
        (C.sectionRatioPolynomialMap k s den)=
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ den)⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    simp only [RingHom.comp_apply,sectionRatioPolynomialMap,MvPolynomial.eval₂Hom_X',
      C.ratioSection_value,div_eq_mul_inv,mul_comm]

theorem sectionRatioPolynomialMap_linearForm (s : ι→Γ(C.sheaf,⊤))
    (den : Γ(C.sheaf,⊤)) (c : ι→₀k) :
    C.sectionRatioPolynomialMap k s den (sectionLinearForm k c)=
      C.ratioSection (Finsupp.linearCombination k s c) den := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen den)
    rw [C.ratioSection_value]
    change ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)) (sectionLinearForm k c)=_
    rw [C.sectionRatioPolynomialMap_germ k s den]
    rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled _ _ _ _ 1
      (sectionLinearForm_isHomogeneous k c),pow_one]
    rw [← C.sectionLinearForm_fieldValue k s c]
    simp only [sectionProjectiveFieldMap,MvPolynomial.coe_eval₂Hom,div_eq_mul_inv,mul_comm]
  · have hbot : C.nonvanishingOpen den=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen den) hbot
    exact Subsingleton.elim _ _

theorem sectionProjectiveMap_generic (s : ι→Γ(C.sheaf,⊤))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    X.fromSpecStalk (genericPoint X) ≫ C.sectionProjectiveMap k s hcover =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  rw [← (C.nonvanishingOpen (s i)).fromSpecStalkOfMem_ι
    (genericPoint X) (genericPoint_mem_open X _),Category.assoc,
    C.sectionProjectiveMap_chart k s hcover i]
  exact C.sectionProjectiveChart_generic k s i _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishing_cover_of_spans
end
end Source_ToricSectionLinearSystems
-- END ORIGINAL PaperVerification.ToricSectionLinearSystems


-- BEGIN ORIGINAL PaperVerification.ToricSectionLinearCharts
section Source_ToricSectionLinearCharts

-- original header: module

-- original header: public import PaperVerification.ToricSectionLinearSystems

-- original header: @[expose] public section

/-! # Genuine projective charts at linear combinations of sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {ι κ : Type u}

def sectionLinearGradedMap (c : ι→κ→₀k) :
    MvPolynomial.homogeneousSubmodule ι k →+*ᵍ
      MvPolynomial.homogeneousSubmodule κ k where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C (fun i=>sectionLinearForm k (c i))
  map_mem {i} {p} hp := by
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have hp' : p.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i p).mp hp
    simpa only [MvPolynomial.coe_eval₂Hom,one_mul] using
      hp'.eval₂ MvPolynomial.C (fun j=>sectionLinearForm k (c j))
        (MvPolynomial.isHomogeneous_C κ) (fun j=>sectionLinearForm_isHomogeneous k (c j))

@[simp] theorem sectionLinearGradedMap_X (c : ι→κ→₀k) (i : ι) :
    sectionLinearGradedMap k c (MvPolynomial.X i)=sectionLinearForm k (c i) := by
  simp [sectionLinearGradedMap]

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_linearForm_preimage (i : ι) (c : ι→₀k) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ
        C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  have he : unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (sectionLinearForm_isHomogeneous k c)))=
        C.ratioSection (Finsupp.linearCombination k s c) (s i) := by
    unfold HomogeneousLocalization.Away.isLocalizationElem
    rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
    simp only [pow_one]
    exact C.sectionRatioPolynomialMap_linearForm k s (s i) c
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (sectionLinearForm_isHomogeneous k c))
      (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

theorem sectionProjectiveMap_linearForm_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (c : ι→₀k) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c)=
      C.nonvanishingOpen (Finsupp.linearCombination k s c) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_linearForm_preimage k s i c)
  have hpre' : C.sectionProjectiveChart k s i ⟨x,hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x,hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x,hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (sectionLinearForm k c) ↔
      x ∈ C.nonvanishingOpen (Finsupp.linearCombination k s c)
  rw [hchart]
  exact hpre'

variable (den : Γ(C.sheaf,⊤)) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous 1)
    (hvalue : C.sectionProjectiveFieldMap k s p=C.toCartierData.sectionValue ⊤ den)

theorem sectionRatioPolynomialMap_eq_one
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    IsUnit (C.sectionRatioPolynomialMap k s den p) := hunit ▸ isUnit_one

def sectionLinearChartCoordinates
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k) p→+*
      Γ(X,C.nonvanishingOpen den) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den) p (hunit ▸ isUnit_one)

def sectionLinearChart
    (hunit : C.sectionRatioPolynomialMap k s den p=1) :
    (C.nonvanishingOpen den).toScheme⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen den).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (C.sectionLinearChartCoordinates k s den p hunit)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) p
      ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)

theorem sectionLinearChart_generic
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    [Nonempty (C.nonvanishingOpen den)]
    (hη : genericPoint X∈C.nonvanishingOpen den) :
    (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionLinearChart k s den p hp hunit =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) p
        ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den) := by
  have hd := C.sectionValue_ne_zero_of_nonvanishing den
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (i : ι) := C.toCartierData.sectionValue ⊤ (s i)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionRatioPolynomialMap k s den)
    (X.germToFunctionField (C.nonvanishingOpen den)).hom p (hunit ▸ isUnit_one)
  let E := MvPolynomial.eval₂Hom F
    (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i)
  have hEq : (X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (C.sectionRatioPolynomialMap k s den)=E :=
    C.sectionRatioPolynomialMap_germ k s den
  have hEp : E p=1 := by
    calc
      E p = (X.germToFunctionField (C.nonvanishingOpen den)).hom
          (C.sectionRatioPolynomialMap k s den p) :=
        congrArg (fun Q : MvPolynomial ι k→+*X.functionField => Q p) hEq.symm
      _ = 1 := by rw [hunit,map_one]
  have hEi : IsUnit (E p) := hEp ▸ isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k→+*X.functionField)
      (hF : F₁=F₂) (h₁ : IsUnit (F₁ p)) (h₂ : IsUnit (F₂ p)) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₁ p h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k) F₂ p h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans (heval _ E hEq _ hEi)
  unfold sectionLinearChart sectionLinearChartCoordinates
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((X.germToFunctionField (C.nonvanishingOpen den)).hom.comp
      (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun i=>(C.toCartierData.sectionValue ⊤ den)⁻¹*v i))
      p ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
        (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (C.toCartierData.sectionValue ⊤ den)⁻¹
    (inv_ne_zero hd) p hp (by decide) (by
      change C.sectionProjectiveFieldMap k s p≠0
      exact hvalue.symm ▸ hd)

include hvalue in
theorem sectionLinearChart_eq
    (hunit : C.sectionRatioPolynomialMap k s den p=1)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionLinearChart k s den p hp hunit=
      (C.nonvanishingOpen den).ι ≫ C.sectionProjectiveMap k s hcover := by
  by_cases hU : Nonempty (C.nonvanishingOpen den)
  · letI := hU
    have hη := genericPoint_mem_open X (C.nonvanishingOpen den)
    let η := (C.nonvanishingOpen den).fromSpecStalkOfMem (genericPoint X) hη
    letI : IsDominant η := genericStalkMapToOpen_isDominant _ hη
    have hηcover : genericPoint X∈⨆ i,C.nonvanishingOpen (s i) := by
      rw [hcover]; trivial
    obtain ⟨i,hηi⟩ := Opens.mem_iSup.mp hηcover
    letI : Nonempty (C.nonvanishingOpen (s i)) := ⟨⟨genericPoint X,hηi⟩⟩
    apply ext_of_isDominant η
    rw [C.sectionLinearChart_generic k s den p hp hvalue hunit hη,
      ← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_ι,
      C.sectionProjectiveMap_generic k s hcover i]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      p (MvPolynomial.X i) ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp)
      (polynomialVariable_mem_degreeOne k i)
      (by decide) (by decide)
      (by exact hvalue.symm ▸ C.sectionValue_ne_zero_of_nonvanishing den)
      (by simpa only [sectionProjectiveFieldMap,MvPolynomial.eval₂Hom_X'] using
        C.sectionValue_ne_zero_of_nonvanishing (s i))
  · letI : IsEmpty (C.nonvanishingOpen den) := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionLinearChart_eq
end
end Source_ToricSectionLinearCharts
-- END ORIGINAL PaperVerification.ToricSectionLinearCharts


-- BEGIN ORIGINAL PaperVerification.ToricSectionSpanningEmbedding
section Source_ToricSectionSpanningEmbedding

-- original header: module

-- original header: public import PaperVerification.ToricSectionLinearCharts

-- original header: @[expose] public section

/-!
# Replacing an embedding system by a finite spanning character system

The old affine coordinate ring is a quotient of its homogeneous chart.
A genuine graded substitution sends every old coordinate to its linear
combination of new coordinates. The resulting map of homogeneous
localizations proves that every old affine coordinate generator remains
available. Thus the replacement preserves the actual closed immersion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι κ : Type u}
    (s : ι→Γ(C.sheaf,⊤)) (t : κ→Γ(C.sheaf,⊤))
    (c : ι→κ→₀k) (hc : ∀ i,Finsupp.linearCombination k t (c i)=s i)

include hc in
theorem sectionLinearSubstitution_ratioMap (i : ι) :
    (C.sectionRatioPolynomialMap k t (s i)).comp
        (sectionLinearGradedMap k c).toRingHom=
      C.sectionProjectiveChartRingMap k s i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionLinearGradedMap,MvPolynomial.eval₂Hom_C,
      sectionRatioPolynomialMap,sectionProjectiveChartRingMap]
  · intro j
    change C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X j)) =
        C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)
    rw [sectionLinearGradedMap_X k c j,
      C.sectionRatioPolynomialMap_linearForm k t (s i) (c j),hc j]
    exact (C.sectionProjectiveChartRingMap_X k s i j).symm

include hc in
theorem sectionLinearSubstitution_unit (i : ι) :
    C.sectionRatioPolynomialMap k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))=1 := by
  change ((C.sectionRatioPolynomialMap k t (s i)).comp
    (sectionLinearGradedMap k c).toRingHom) (MvPolynomial.X i)=1
  rw [C.sectionLinearSubstitution_ratioMap k s t c hc]
  exact C.sectionProjectiveChartRingMap_self k s i

include hc in
theorem sectionLinearSubstitution_fieldValue (i : ι) :
    C.sectionProjectiveFieldMap k t
      (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.toCartierData.sectionValue ⊤ (s i) := by
  rw [sectionLinearGradedMap_X k c i,C.sectionLinearForm_fieldValue k t (c i),hc i]

theorem sectionLinearSubstitution_chartCoordinates (i : ι) :
    (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
      (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
        (MvPolynomial.X i))=
      C.sectionProjectiveChartCoordinates k s i := by
  ext z
  obtain ⟨m,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule ι k) (polynomialVariable_mem_degreeOne k i) z
  rw [RingHom.comp_apply,HomogeneousLocalization.Away.map_mk]
  unfold sectionLinearChartCoordinates sectionProjectiveChartCoordinates
  rw [unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionLinearSubstitution_unit k s t c hc i),
    unitHomogeneousAwayEvaluation_mk_of_eq_one _ _
      (C.sectionProjectiveChartRingMap_self k s i)]
  exact congrArg (fun F=>F p) (C.sectionLinearSubstitution_ratioMap k s t c hc i)

theorem sectionLinearSubstitution_chartCoordinates_surjective (i : ι)
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    Function.Surjective (C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)) := by
  apply Function.Surjective.of_comp
    (g := HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
      (MvPolynomial.X i))
  change Function.Surjective
    ((C.sectionLinearChartCoordinates k t (s i)
      (sectionLinearGradedMap k c (MvPolynomial.X i))
      (C.sectionLinearSubstitution_unit k s t c hc i)).comp
        (HomogeneousLocalization.Away.map (sectionLinearGradedMap k c)
          (MvPolynomial.X i)))
  rw [C.sectionLinearSubstitution_chartCoordinates k s t c hc i]
  exact hgen

include hc in
theorem sectionLinearSubstitution_localPreimmersion
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι)
    (ha : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion ((C.nonvanishingOpen (s i)).ι ≫
      C.sectionProjectiveMap k t hnew) := by
  let p := sectionLinearGradedMap k c (MvPolynomial.X i)
  have hp : p.IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 p).mp
      ((sectionLinearGradedMap k c).map_mem (polynomialVariable_mem_degreeOne k i))
  have hunit := C.sectionLinearSubstitution_unit k s t c hc i
  rw [← C.sectionLinearChart_eq k t (s i) p hp
    (C.sectionLinearSubstitution_fieldValue k s t c hc i) hunit hnew]
  letI : IsAffine (C.nonvanishingOpen (s i)) := ha
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← ha.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (C.sectionLinearChartCoordinates k t (s i) p hunit))) :=
    IsClosedImmersion.spec_of_surjective _
      (C.sectionLinearSubstitution_chartCoordinates_surjective k s t c hc i hgen)
  let q := Spec.map (CommRingCat.ofHom
    (C.sectionLinearChartCoordinates k t (s i) p hunit))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule κ k) p
    ((MvPolynomial.mem_homogeneousSubmodule 1 p).mpr hp) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

include hc in
theorem sectionLinearSubstitution_preimage
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤) (i : ι) :
    C.sectionProjectiveMap k t hnew ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
        (sectionLinearGradedMap k c (MvPolynomial.X i))=
      C.nonvanishingOpen (s i) := by
  rw [sectionLinearGradedMap_X k c i,
    C.sectionProjectiveMap_linearForm_preimage k t hnew (c i),hc i]

include hc in
/-- A spanning replacement of a genuine embedding system remains a
genuine closed immersion, including when the new sections are characters. -/
theorem sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hnew : (⨆ j,C.nonvanishingOpen (t j))=⊤)
    {α : Type u} (chooseChart : α→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k t hnew) := by
  let f := C.sectionProjectiveMap k t hnew
  let U (i : α) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : α) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
    (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
  have hlocal (i : α) : IsPreimmersion ((U i).ι ≫ f) :=
    C.sectionLinearSubstitution_localPreimmersion k s t c hc hnew
      (chooseChart i) (ha i) (hgen i)
  letI : SurjectiveOnStalks f := IsZariskiLocalAtSource.of_iSup_eq_top U hchosen
    (fun i=>by letI := hlocal i; infer_instance)
  letI : IsPreimmersion f := by
    refine { isEmbedding := ?_ }
    apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
      (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
    · rintro y ⟨x,rfl⟩
      have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
      obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
      apply Opens.mem_iSup.mpr
      refine ⟨i,?_⟩
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      change x∈C.sectionProjectiveMap k t hnew ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule κ k)
          (sectionLinearGradedMap k c (MvPolynomial.X (chooseChart i)))
      rw [hp]
      exact hxi
    · exact fun i=>(U i).ι.continuous
    · intro i x hx
      have hp := C.sectionLinearSubstitution_preimage k s t c hc hnew (chooseChart i)
      have hxi : x∈U i := by
        change x∈C.nonvanishingOpen (s (chooseChart i))
        rw [← hp]
        exact hx
      exact ⟨⟨x,hxi⟩,rfl⟩
    · intro i
      letI := hlocal i
      exact ((U i).ι ≫ f).isEmbedding
  letI : IsProper f := C.sectionProjectiveMap_isProper k t hnew
  change IsClosedImmersion f
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
end
end Source_ToricSectionSpanningEmbedding
-- END ORIGINAL PaperVerification.ToricSectionSpanningEmbedding


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicProjectiveEmbedding
section Source_ToricIntrinsicProjectiveEmbedding

-- original header: module

-- original header: public import PaperVerification.ToricAmpleProjectiveEmbedding
-- original header: public import PaperVerification.ToricSectionSpanningEmbedding
-- original header: public import PaperVerification.ToricIntrinsicPowerCharacters

-- original header: @[expose] public section

/-!
# A genuine finite character embedding of an intrinsic smooth toric scheme

The argument starts with an arbitrary actual ample Cartier sheaf. Its
proved rational normalization preserves ampleness. Denominator clearing
constructs a finite projective embedding, and the genuine section
coaction supplies a finite character family spanning those sections.
The graded substitution theorem preserves the closed immersion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory
open scoped Classical BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- An actual finite character-valued section system defining a genuine
closed immersion of the original scheme into polynomial projective space.
The character equation retains the actual dense-torus function-field map. -/
theorem exists_character_projective_embedding
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ (C : RationalCartierCocycle X.left)
      (F : Finset (Fin n→ℤ)) (e : ULift.{u} F→Γ(C.sheaf,⊤)),
      (∀ m : ULift.{u} F,C.toCartierData.sectionValue ⊤ (e m)=
        openTorusRationalAlgHom k n X.left T.torus.left
          (AddMonoidAlgebra.single m.down.val (1:k))) ∧
      ∃ hcover : (⨆ m : ULift.{u} F,C.nonvanishingOpen (e m))=⊤,
        IsClosedImmersion (C.sectionProjectiveMap k e hcover) := by
  letI : IsProper (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsProper X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let E := torusNormalizedCartier k n X.left T.torus.left D
  have hE : E.IsAmple :=
    (torusNormalizedCartier_isAmple_iff k n X.left T.torus.left D).mpr hD
  let C₀ := E.localCocycle
  letI : CompactSpace X.left := hE.1
  have hC₀ : C₀.HasUnitFramesOn T.torusOpen :=
    torusNormalizedCartier_unitFrames k n X.left T.torus.left D
  obtain ⟨a,ha,I,hI,s,hnonempty,haff,hcover⟩ :=
    (show C₀.IsAmple from hE).exists_common_power_nonempty_affine_cover
  letI : Fintype I := hI
  obtain ⟨b,hb,J,hJ,t,chooseChart,ht,hall,hchosen,haff',hgen⟩ :=
    (C₀.pow a).exists_power_chart_generators k s hnonempty haff hcover
  letI : Fintype J := hJ
  let C := (C₀.pow a).pow b
  have hC : C.toCartierData.localCocycle.HasUnitFramesOn T.torusOpen :=
    ((hC₀.pow a).pow b).of_equivalent C.toCartierData.localCocycle
      C.toCartierData.equivalent_localCocycle
  obtain ⟨F,e₀,he₀,hspan₀⟩ := T.exists_finite_torus_eigensections_of_unitFrames
    C.toCartierData hC t
  let e : ULift.{u} F→Γ(C.sheaf,⊤) := fun m => e₀ m.down
  have hrange : Set.range e = Set.range e₀ := by
    ext q
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨m.down,rfl⟩
    · rintro ⟨m,rfl⟩
      exact ⟨ULift.up m,rfl⟩
  have hspan (i : J) : t i ∈ Submodule.span k (Set.range e) := by
    rw [hrange]
    exact hspan₀ i
  have hrepr (i : J) : ∃ c : ULift.{u} F→₀k,Finsupp.linearCombination k e c=t i := by
    simpa only [Finsupp.linearCombination_apply] using
      (Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan i))
  choose c hc using hrepr
  have hnew : (⨆ m : ULift.{u} F,C.nonvanishingOpen (e m))=⊤ :=
    C.nonvanishing_cover_of_spans k t e hall (fun i=>⟨c i,hc i⟩)
  refine ⟨C,F,e,(fun m=>(he₀ m.down).symm),hnew,?_⟩
  exact C.sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
    k t e c hc hnew chooseChart hchosen haff' hgen

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_character_projective_embedding
end
end Source_ToricIntrinsicProjectiveEmbedding
-- END ORIGINAL PaperVerification.ToricIntrinsicProjectiveEmbedding


-- BEGIN ORIGINAL PaperVerification.ToricAffineGenericPoint
section Source_ToricAffineGenericPoint

-- original header: module

-- original header: public import PaperVerification.ToricFunctionFieldBridge
-- original header: public import PaperVerification.ToricSectionProjectiveMap

-- original header: @[expose] public section

/-! # The actual generic morphism in affine coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : CommRingCat.{u}) [IsDomain R]

theorem affine_genericPointMap :
    Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField))=
      (Spec R).fromSpecStalk (genericPoint (Spec R)) := by
  calc
    Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) =
        Spec.map ((Scheme.ΓSpecIso R).inv≫(Spec R).germToFunctionField ⊤) := rfl
    _ = Spec.map ((Spec R).germToFunctionField ⊤)≫Spec.map (Scheme.ΓSpecIso R).inv :=
      Spec.map_comp _ _
    _ = (Spec R).fromSpecStalk (genericPoint (Spec R))≫(Spec R).toSpecΓ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by
      exact congrArg (fun f => f ≫ Spec.map (Scheme.ΓSpecIso R).inv)
        (Scheme.fromSpecStalk_toSpecΓ (Spec R) (genericPoint (Spec R))).symm
    _ = _ := by
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv,Category.comp_id]

variable {X : Scheme.{u}} [IsIntegral X]
    (j : Spec R⟶X) [IsOpenImmersion j]

theorem affineOpenCoordinateMap_genericPoint :
    Spec.map (CommRingCat.ofHom (affineOpenCoordinateMap R j))≫j=
      X.fromSpecStalk (genericPoint X) := by
  let e := openImmersionFunctionFieldIso j
  have he : Spec.map e.hom≫X.fromSpecStalk (genericPoint X)=
      (Spec R).fromSpecStalk (genericPoint (Spec R))≫j := by
    simp only [e,openImmersionFunctionFieldIso,Iso.trans_hom,Spec.map_comp,
      TopCat.Presheaf.stalkCongr_hom,asIso_hom,Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hcoord : CommRingCat.ofHom (affineOpenCoordinateMap R j)=
      CommRingCat.ofHom (algebraMap R (Spec R).functionField)≫e.inv := rfl
  rw [hcoord,Spec.map_comp,Category.assoc,affine_genericPointMap R,← he,
    ← Category.assoc,← Spec.map_comp,Iso.hom_inv_id,Spec.map_id]
  exact Category.id_comp _

theorem affineOpenCoordinateMap_isDominant :
    IsDominant (Spec.map (CommRingCat.ofHom (affineOpenCoordinateMap R j))) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  have hinj : Function.Injective (affineOpenCoordinateMap R j) :=
    (openImmersionGlobalToFunctionField_injective j).comp
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective
  change RingHom.ker (affineOpenCoordinateMap R j) ≤ nilradical R
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveMap_generic_of_value_ne_zero
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    (hi : C.toCartierData.sectionValue ⊤ (s i)≠0) :
    X.fromSpecStalk (genericPoint X)≫C.sectionProjectiveMap k s hcover=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_X'] using hi) := by
  have hη : genericPoint X∈C.nonvanishingOpen (s i) := by
    obtain ⟨j,hj⟩ := C.covers (genericPoint X)
    rw [C.nonvanishing_iff_value j (s i) (genericPoint X) hj]
    refine ⟨hi,?_⟩
    refine ⟨(C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ (s i),?_⟩
    simp only [RingHom.algebraMap_toAlgebra,TopCat.Presheaf.stalkSpecializes_refl,
      CommRingCat.id_apply]
  letI : Nonempty (C.nonvanishingOpen (s i)) := ⟨⟨genericPoint X,hη⟩⟩
  rw [← (C.nonvanishingOpen (s i)).fromSpecStalkOfMem_ι
    (genericPoint X) hη,Category.assoc,C.sectionProjectiveMap_chart k s hcover i]
  exact C.sectionProjectiveChart_generic k s i hη

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineOpenCoordinateMap_genericPoint
end
end Source_ToricAffineGenericPoint
-- END ORIGINAL PaperVerification.ToricAffineGenericPoint


-- BEGIN ORIGINAL PaperVerification.ToricGradedProjQuotient
section Source_ToricGradedProjQuotient

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveRatios
-- original header: public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- original header: @[expose] public section

/-!
# Surjective graded homomorphisms and genuine closed Proj embeddings

A homogeneous element of a graded quotient has a homogeneous preimage:
take the required degree component of any preimage. Consequently the
degree-zero localized maps are surjective. The actual Proj morphism is
therefore a closed immersion on the standard affine open cover.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical
open HomogeneousIdeal

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ→σ} {ℬ : ℕ→τ} [GradedRing 𝒜] [GradedRing ℬ]

theorem graded_surjective_homogeneous_preimage (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {b : B} (hb : b∈ℬ d) :
    ∃ a : A,a∈𝒜 d ∧ f a=b := by
  obtain ⟨a,rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a d,(DirectSum.decompose 𝒜 a d).property,?_⟩
  rw [f.map_directSumDecompose,DirectSum.decompose_of_mem_same ℬ hb]

theorem irrelevant_le_map_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) : ℬ₊≤𝒜₊.map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro d hd b hb
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

theorem homogeneousAway_map_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) {d : ℕ} {s : A} (hs : s∈𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨m,b,hb,rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a,ha,rfl⟩ := graded_surjective_homogeneous_preimage f hf hb
  exact ⟨Away.mk 𝒜 hs m a ha,by simp⟩

/-- The literal Proj morphism of a graded quotient is a closed immersion.
The proof uses surjectivity of its actual affine coordinate homomorphisms. -/
theorem projMap_isClosedImmersion_of_surjective (f : 𝒜→+*ᵍℬ)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hf)) := by
  let h := irrelevant_le_map_of_surjective f hf
  let F := Proj.map f h
  let J := Σ d : {d : ℕ // 0<d}, {s : A // s∈𝒜 d.val}
  let U (j : J) := Proj.basicOpen 𝒜 j.2.val
  have hcover : (⨆ j,U j)=⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
    intro d hd a ha
    exact Ideal.subset_span ⟨⟨⟨d,hd⟩,⟨a,ha⟩⟩,rfl⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U hcover
  intro j
  let eA := Proj.basicOpenIsoSpec 𝒜 j.2.val j.2.property j.1.property
  let eB := Proj.basicOpenIsoSpec ℬ (f j.2.val)
    (f.map_mem j.2.property) j.1.property
  let g := Spec.map (CommRingCat.ofHom (Away.map f j.2.val))
  letI : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective _
    (homogeneousAway_map_surjective f hf j.2.property)
  let r : (Proj.basicOpen ℬ (f j.2.val)).toScheme ⟶
      (Proj.basicOpen 𝒜 j.2.val).toScheme := F ∣_ U j
  have hsq : (eB.inv ≫ (Proj.basicOpen ℬ (f j.2.val)).ι) ≫ F =
      g ≫ eA.inv ≫ (U j).ι :=
    Proj.awayι_comp_map f h j.1.property j.2.val j.2.property
  have hcanonical : (Proj.basicOpen ℬ (f j.2.val)).ι ≫ F =
      (eB.hom ≫ g ≫ eA.inv) ≫ (U j).ι := by
    have h := congrArg (fun q => eB.hom ≫ q) hsq
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h
  have heq : r = eB.hom ≫ g ≫ eA.inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 j.2.val).ι).mp
    exact (morphismRestrict_ι F (U j)).trans hcanonical
  letI : IsClosedImmersion (g ≫ eA.inv) := IsClosedImmersion.comp g eA.inv
  have hclosed : IsClosedImmersion (eB.hom ≫ g ≫ eA.inv) :=
    IsClosedImmersion.comp eB.hom (g ≫ eA.inv)
  change IsClosedImmersion r
  exact heq.symm ▸ hclosed

variable {K : Type u} [Field K]

theorem homogeneousAwayEvaluation_gradedMap (f : 𝒜→+*ᵍℬ)
    (F : B→+*K) {d : ℕ} {s : A} (hs : s∈𝒜 d) (hne : F (f s)≠0) :
    (homogeneousAwayEvaluation ℬ F (f s) hne).comp (Away.map f s)=
      homogeneousAwayEvaluation 𝒜 (F.comp f.toRingHom) s hne := by
  ext z
  obtain ⟨m,a,ha,rfl⟩ := Away.mk_surjective 𝒜 hs z
  simp only [RingHom.comp_apply,Away.map_mk,homogeneousAwayEvaluation_mk]
  rfl

theorem projectiveFieldChart_gradedMap (f : 𝒜→+*ᵍℬ)
    (h : ℬ₊≤𝒜₊.map f) (F : B→+*K) {d : ℕ} {s : A}
    (hs : s∈𝒜 d) (hd : 0<d) (hne : F (f s)≠0) :
    projectiveFieldChart ℬ F (f s) (f.map_mem hs) hd hne≫Proj.map f h=
      projectiveFieldChart 𝒜 (F.comp f.toRingHom) s hs hd hne := by
  unfold projectiveFieldChart
  rw [Category.assoc,Proj.awayι_comp_map f h hd s hs,
    ← Category.assoc,← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (homogeneousAwayEvaluation_gradedMap f F hs hne)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projMap_isClosedImmersion_of_surjective
end
end Source_ToricGradedProjQuotient
-- END ORIGINAL PaperVerification.ToricGradedProjQuotient


-- BEGIN ORIGINAL PaperVerification.ToricMonomialAffineCharts
section Source_ToricMonomialAffineCharts

-- original header: module

-- original header: public import PaperVerification.ToricCharacterRegularity
-- original header: public import Mathlib.Algebra.MvPolynomial.Eval
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

-- original header: @[expose] public section

/-!
# Coordinate rings of actual affine monomial images

The algebra generated by a family of characters is exactly the semigroup
algebra of the additive monoid generated by their exponents, embedded in
the ambient character algebra. Thus the polynomial coordinate map is
surjective onto this actual chart ring and gives a closed immersion of
affine schemes. This is an affine ingredient of the projective toric
dictionary, not an assertion of that dictionary.
-/

noncomputable section

universe u v w

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open AlgebraicGeometry CategoryTheory

section Algebra

variable (k : Type*) [CommRing k]
variable {M : Type*} [AddCommMonoid M]

/-- Taking the additive closure of the exponents and taking the algebra
generated by their characters commute, as actual subalgebras of `k[M]`. -/
theorem monoidChartAlgebra_closure (S : Set M) :
    monoidChartAlgebra k (AddSubmonoid.closure S) =
      Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S) := by
  apply le_antisymm
  · change (monoidChartAlgebra k (AddSubmonoid.closure S)).toSubmodule ≤
      (Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S)).toSubmodule
    rw [monoidChartAlgebra_toSubmodule, characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact Algebra.subset_adjoin ⟨m, hm, rfl⟩
    | zero =>
        change single (0 : M) (1 : k) ∈
          Algebra.adjoin k ((fun m : M => single m (1 : k)) '' S)
        simpa only [AddMonoidAlgebra.one_def] using (Algebra.adjoin k
          ((fun m : M => single m (1 : k)) '' S)).one_mem
    | add x y hx hy ihx ihy =>
        simpa using (Algebra.adjoin k
          ((fun m : M => single m (1 : k)) '' S)).mul_mem ihx ihy
  · apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨m, hm, rfl⟩
    change single m (1 : k) ∈
      (monoidChartAlgebra k (AddSubmonoid.closure S)).toSubmodule
    rw [monoidChartAlgebra_toSubmodule, characterModule_eq_span]
    exact Submodule.subset_span ⟨m, AddSubmonoid.subset_closure hm, rfl⟩

variable {ι : Type*} (e : ι → M)

/-- The literal polynomial map sending the coordinate indexed by `i`
to the character with exponent `e i`. -/
def affineMonomialMap : MvPolynomial ι k →ₐ[k] AddMonoidAlgebra k M :=
  MvPolynomial.aeval (fun i => single (e i) (1 : k))

@[simp] theorem affineMonomialMap_X (i : ι) :
    affineMonomialMap k e (MvPolynomial.X i) = single (e i) (1 : k) := by
  simp [affineMonomialMap]

theorem affineMonomialMap_range :
    (affineMonomialMap k e).range =
      monoidChartAlgebra k (AddSubmonoid.closure (Set.range e)) := by
  rw [affineMonomialMap, MvPolynomial.aeval_range, monoidChartAlgebra_closure]
  congr 1
  exact Set.range_comp (fun m : M => single m (1 : k)) e

def affineMonomialMapToChart :
    MvPolynomial ι k →ₐ[k]
      monoidChartAlgebra k (AddSubmonoid.closure (Set.range e)) :=
  (affineMonomialMap k e).codRestrict _ (fun f => by
    rw [← affineMonomialMap_range]
    exact ⟨f, rfl⟩)

theorem affineMonomialMapToChart_surjective :
    Function.Surjective (affineMonomialMapToChart k e) := by
  rintro ⟨f, hf⟩
  rw [← affineMonomialMap_range] at hf
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, Subtype.ext hg⟩

end Algebra

variable (k : Type (max u v w)) [CommRing k]
    {M : Type v} [AddCommMonoid M] {ι : Type w} (e : ι → M)

/-- A scheme-theoretic closed immersion into actual affine coordinate
space, derived from the surjective polynomial ring map. -/
theorem affineMonomialChart_isClosedImmersion :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (affineMonomialMapToChart k e).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (affineMonomialMapToChart_surjective k e)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monoidChartAlgebra_closure
#print axioms PaperVerification.ToricCharacters.affineMonomialChart_isClosedImmersion
end
end Source_ToricMonomialAffineCharts
-- END ORIGINAL PaperVerification.ToricMonomialAffineCharts


-- BEGIN ORIGINAL PaperVerification.ToricHomogeneousMonoidCharts
section Source_ToricHomogeneousMonoidCharts

-- original header: module

-- original header: public import PaperVerification.ToricMonomialAffineCharts
-- original header: public import Mathlib.Algebra.MonoidAlgebra.Grading
-- original header: public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
-- original header: public import Mathlib.RingTheory.Localization.Away.Basic
-- original header: public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
-- original header: public import Mathlib.Tactic.Abel

-- original header: @[expose] public section

/-!
# Literal affine charts of a homogeneous monomial ring

For a family of lattice weights `a`, the homogeneous monoid is generated
by `(1,a i)`.  Dehomogenizing at the weight `a j` identifies the actual
degree-zero localization with the subalgebra generated by the characters
`a i-a j`.  The map is the literal character-ratio map.  In particular,
the statement identifies the actual Proj chart, rather than declaring an
abstract affine toric model to be that chart.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open AlgebraicGeometry CategoryTheory
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)

def homogeneousWeightMonoid : AddSubmonoid (ℕ × M) :=
  AddSubmonoid.closure (Set.range (fun i => (1,a i)))

def homogeneousWeight (i : ι) : homogeneousWeightMonoid a :=
  ⟨(1,a i),AddSubmonoid.subset_closure (Set.mem_range_self i)⟩

def homogeneousWeightDegree : homogeneousWeightMonoid a →+ ℕ :=
  (AddMonoidHom.fst ℕ M).comp (homogeneousWeightMonoid a).subtype

@[simp] theorem homogeneousWeightDegree_generator (i : ι) :
    homogeneousWeightDegree a (homogeneousWeight a i)=1 := rfl

def differenceWeightMonoid (j : ι) : AddSubmonoid M :=
  AddSubmonoid.closure (Set.range (fun i => a i-a j))

def weightDifference (j : ι) : (ℕ × M) →+ M where
  toFun p := p.2-p.1 • a j
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add,Prod.snd_add,add_nsmul]
    abel

def homogeneousWeightDifference (j : ι) : homogeneousWeightMonoid a →+ M :=
  (weightDifference a j).comp (homogeneousWeightMonoid a).subtype

@[simp] theorem homogeneousWeightDifference_generator (j i : ι) :
    homogeneousWeightDifference a j (homogeneousWeight a i)=a i-a j := by
  simp [homogeneousWeightDifference,weightDifference,homogeneousWeight]

theorem homogeneousWeightDifference_mem (j : ι) (p : homogeneousWeightMonoid a) :
    homogeneousWeightDifference a j p∈differenceWeightMonoid a j := by
  rcases p with ⟨p,hp⟩
  change weightDifference a j p∈differenceWeightMonoid a j
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact AddSubmonoid.subset_closure ⟨i,by simp [weightDifference]⟩
  | zero => simpa using (differenceWeightMonoid a j).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (differenceWeightMonoid a j).add_mem ihx ihy

theorem homogeneousWeightDifference_injOn_degree (j : ι) (d : ℕ) :
    Set.InjOn (homogeneousWeightDifference a j)
      {p | homogeneousWeightDegree a p=d} := by
  intro p hp q hq hpq
  apply Subtype.ext
  apply Prod.ext
  · exact hp.trans hq.symm
  · change p.val.2-p.val.1 • a j=q.val.2-q.val.1 • a j at hpq
    change p.val.1=d at hp
    change q.val.1=d at hq
    rw [hp,hq] at hpq
    exact sub_left_inj.mp hpq

variable (k : Type*) [CommRing k]

abbrev homogeneousWeightGrading : ℕ → Submodule k
    (AddMonoidAlgebra k (homogeneousWeightMonoid a)) :=
  AddMonoidAlgebra.gradeBy k (homogeneousWeightDegree a)

def homogeneousWeightCharacter (i : ι) :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) :=
  single (homogeneousWeight a i) 1

theorem homogeneousWeightCharacter_homogeneous (i : ι) :
    homogeneousWeightCharacter a k i∈homogeneousWeightGrading a k 1 :=
  AddMonoidAlgebra.single_mem_gradeBy _ _ _

def dehomogeneousWeightMap (j : ι) :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k (homogeneousWeightDifference a j)

@[simp] theorem dehomogeneousWeightMap_single (j : ι)
    (p : homogeneousWeightMonoid a) (r : k) :
    dehomogeneousWeightMap a k j (single p r)=
      single (homogeneousWeightDifference a j p) r := by
  simp [dehomogeneousWeightMap]

@[simp] theorem dehomogeneousWeightMap_self (j : ι) :
    dehomogeneousWeightMap a k j (homogeneousWeightCharacter a k j)=1 := by
  simp [homogeneousWeightCharacter,AddMonoidAlgebra.one_def]

/-- Dehomogenization is injective on each individual homogeneous grade.
This is the injectivity needed for degree-zero localization; the map on
the entire homogeneous ring is intentionally not asserted injective. -/
theorem dehomogeneousWeightMap_eq_zero_iff {j : ι} {d : ℕ}
    {f : AddMonoidAlgebra k (homogeneousWeightMonoid a)}
    (hf : f∈homogeneousWeightGrading a k d) :
    dehomogeneousWeightMap a k j f=0 ↔ f=0 := by
  constructor
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    ext p
    by_cases hp : homogeneousWeightDegree a p=d
    · have hcoef := congrArg (fun g : AddMonoidAlgebra k M =>
          g.coeff (homogeneousWeightDifference a j p)) h
      change f.coeff.mapDomain (homogeneousWeightDifference a j)
          (homogeneousWeightDifference a j p)=0 at hcoef
      rw [Finsupp.mapDomain_apply' {q | homogeneousWeightDegree a q=d}
        f.coeff hf (homogeneousWeightDifference_injOn_degree a j d) hp] at hcoef
      exact hcoef
    · have : f.coeff p=0 := by
        by_contra hne
        exact hp (hf p (Finsupp.mem_support_iff.mpr hne))
      simpa using this
  · intro h
    simp [h]

abbrev homogeneousWeightChart (j : ι) :=
  HomogeneousLocalization.Away (homogeneousWeightGrading a k)
    (homogeneousWeightCharacter a k j)

def homogeneousWeightZeroMap : k →+* homogeneousWeightGrading a k 0 where
  toFun r := ⟨single 0 r,AddMonoidAlgebra.single_mem_gradeBy _ _ _⟩
  map_zero' := by ext; simp
  map_one' := by apply Subtype.ext; exact AddMonoidAlgebra.one_def.symm
  map_add' r s := by ext; simp
  map_mul' r s := by ext; simp

instance homogeneousWeightChartAlgebra (j : ι) : Algebra k (homogeneousWeightChart a k j) :=
  ((HomogeneousLocalization.fromZeroRingHom (homogeneousWeightGrading a k)
    (Submonoid.powers (homogeneousWeightCharacter a k j))).comp
      (homogeneousWeightZeroMap a k)).toAlgebra

def dehomogeneousChartMap (j : ι) :
    homogeneousWeightChart a k j →ₐ[k] AddMonoidAlgebra k M where
  toRingHom :=
    (Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j)
      (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))).comp
        (algebraMap (homogeneousWeightChart a k j)
          (Localization.Away (homogeneousWeightCharacter a k j)))
  commutes' r := by
    change Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j)
      (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))
      (Localization.mk (single 0 r) ⟨1,0,by simp⟩)=algebraMap k _ r
    simpa using Localization.awayLift_mk
      (dehomogeneousWeightMap a k j).toRingHom
      (homogeneousWeightCharacter a k j) (single 0 r) 1
      (by simp) 0

theorem dehomogeneousChartMap_mk (j : ι) (d : ℕ)
    (f : AddMonoidAlgebra k (homogeneousWeightMonoid a))
    (hf : f∈homogeneousWeightGrading a k (d • (1 : ℕ))) :
    dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) d f hf)=
      dehomogeneousWeightMap a k j f := by
  change Localization.awayLift (dehomogeneousWeightMap a k j).toRingHom
    (homogeneousWeightCharacter a k j)
    (by simpa using (isUnit_one : IsUnit (1 : AddMonoidAlgebra k M)))
    (Localization.mk f ⟨homogeneousWeightCharacter a k j ^ d,d,rfl⟩)=_
  simpa using Localization.awayLift_mk
    (dehomogeneousWeightMap a k j).toRingHom
    (homogeneousWeightCharacter a k j) f 1 (by simp) d

theorem dehomogeneousChartMap_injective (j : ι) :
    Function.Injective (dehomogeneousChartMap a k j) := by
  apply (RingHom.injective_iff_ker_eq_bot (dehomogeneousChartMap a k j).toRingHom).mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
  change dehomogeneousChartMap a k j _=0 at hx
  rw [dehomogeneousChartMap_mk] at hx
  have hf0 : f=0 := (dehomogeneousWeightMap_eq_zero_iff a k hf).mp hx
  subst f
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk,Localization.mk_zero]

theorem dehomogeneousWeightMap_mem_chart (j : ι)
    (f : AddMonoidAlgebra k (homogeneousWeightMonoid a)) :
    dehomogeneousWeightMap a k j f∈monoidChartAlgebra k (differenceWeightMonoid a j) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of p =>
      change dehomogeneousWeightMap a k j (single p 1)∈_
      rw [dehomogeneousWeightMap_single]
      apply (mem_monoidChartAlgebra k _ _).mpr
      intro m hm
      have hm' : m=homogeneousWeightDifference a j p :=
        Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
      simpa [hm'] using homogeneousWeightDifference_mem a j p
  | add f g hf hg =>
      rw [map_add]
      exact (monoidChartAlgebra k _).add_mem hf hg
  | smul r f hf =>
      rw [map_smul]
      exact (monoidChartAlgebra k _).smul_mem hf r

theorem dehomogeneousChartMap_range (j : ι) :
    (dehomogeneousChartMap a k j).range=
      monoidChartAlgebra k (differenceWeightMonoid a j) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
    change dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) d f hf)∈_
    rw [dehomogeneousChartMap_mk]
    exact dehomogeneousWeightMap_mem_chart a k j f
  · rw [differenceWeightMonoid,monoidChartAlgebra_closure]
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
    refine ⟨HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) 1
      (homogeneousWeightCharacter a k i) (by
        simpa using homogeneousWeightCharacter_homogeneous a k i),?_⟩
    change dehomogeneousChartMap a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) 1
        (homogeneousWeightCharacter a k i) (by
          simpa using homogeneousWeightCharacter_homogeneous a k i)) = single (a i-a j) 1
    rw [dehomogeneousChartMap_mk]
    simp only [homogeneousWeightCharacter,dehomogeneousWeightMap_single,
      homogeneousWeightDifference_generator]

/-- The actual degree-zero localization is the actual difference-character
subalgebra of the character ring. -/
def homogeneousWeightChartEquiv (j : ι) :
    homogeneousWeightChart a k j ≃ₐ[k]
      monoidChartAlgebra k (differenceWeightMonoid a j) :=
  (AlgEquiv.ofInjective (dehomogeneousChartMap a k j)
    (dehomogeneousChartMap_injective a k j)).trans
      (Subalgebra.equivOfEq _ _ (dehomogeneousChartMap_range a k j))

@[simp] theorem homogeneousWeightChartEquiv_character_ratio (j i : ι) :
    (homogeneousWeightChartEquiv a k j
      (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k j) 1
        (homogeneousWeightCharacter a k i) (by
          simpa using homogeneousWeightCharacter_homogeneous a k i)) :
        AddMonoidAlgebra k M)=single (a i-a j) 1 := by
  change dehomogeneousChartMap a k j
    (HomogeneousLocalization.Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) 1
      (homogeneousWeightCharacter a k i) _) = _
  rw [dehomogeneousChartMap_mk]
  simp only [homogeneousWeightCharacter,dehomogeneousWeightMap_single,
    homogeneousWeightDifference_generator]

/-- The actual projective scheme of the homogeneous character algebra. -/
def monomialProjectiveScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (homogeneousWeightGrading a k)

/-- The canonical affine open at a homogeneous coordinate, identified
with the literal difference-character algebra. -/
def monomialProjectiveChartIso (j : ι) :
    (AlgebraicGeometry.Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k j)).toScheme ≅
      AlgebraicGeometry.Spec (CommRingCat.of
        (monoidChartAlgebra k (differenceWeightMonoid a j))) :=
  (AlgebraicGeometry.Proj.basicOpenIsoSpec (homogeneousWeightGrading a k)
    (homogeneousWeightCharacter a k j)
    (homogeneousWeightCharacter_homogeneous a k j) (by decide)).trans
      (AlgebraicGeometry.Scheme.Spec.mapIso
        (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.symm.op)

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.dehomogeneousChartMap_injective
#print axioms PaperVerification.ToricCharacters.homogeneousWeightChartEquiv
end
end Source_ToricHomogeneousMonoidCharts
-- END ORIGINAL PaperVerification.ToricHomogeneousMonoidCharts


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveMonomialMaps
section Source_ToricProjectiveMonomialMaps

-- original header: module

-- original header: public import PaperVerification.ToricHomogeneousMonoidCharts
-- original header: public import PaperVerification.ToricProjectiveRatios
-- original header: public import PaperVerification.ToricChartOpenImmersions
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Separated
-- original header: public import Mathlib.RingTheory.Spectrum.Prime.Topology

-- original header: @[expose] public section

/-!
# Character maps into the actual monomial Proj

The chart morphisms are the genuine Proj affine-chart open immersions.
Their restrictions to the character torus agree as scheme morphisms,
proved through homogeneous ratios in the actual fraction field and
separatedness. Their mutual inverse-image opens are the basic opens of
the literal weight-difference characters.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory HomogeneousLocalization
open PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)
    (k : Type u) [Field k]
    [IsDomain (AddMonoidAlgebra k M)]

def homogeneousExponentMap : homogeneousWeightMonoid a →+ M :=
  (AddMonoidHom.snd ℕ M).comp (homogeneousWeightMonoid a).subtype

def homogeneousExponentAlgHom :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k (homogeneousExponentMap a)

@[simp] theorem homogeneousExponentAlgHom_single (p : homogeneousWeightMonoid a) (r : k) :
    homogeneousExponentAlgHom a k (single p r)=single p.val.2 r := by
  simp [homogeneousExponentAlgHom,homogeneousExponentMap]

@[simp] theorem homogeneousExponentAlgHom_character (j : ι) :
    homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j)=single (a j) 1 := by
  exact homogeneousExponentAlgHom_single a k (homogeneousWeight a j) 1

theorem homogeneousExponentAlgHom_factor {d : ℕ}
    {f : AddMonoidAlgebra k (homogeneousWeightMonoid a)}
    (hf : f∈homogeneousWeightGrading a k d) (j : ι) :
    homogeneousExponentAlgHom a k f=
      single (d • a j) (1 : k)*dehomogeneousWeightMap a k j f := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hdegree : p.val.1=d := hf p hp
  simp only [homogeneousExponentAlgHom_single,dehomogeneousWeightMap_single,
    single_mul_single,one_mul]
  congr 1
  change p.val.2=d • a j+(p.val.2-p.val.1 • a j)
  rw [hdegree]
  abel

def homogeneousExponentFractionMap :
    AddMonoidAlgebra k (homogeneousWeightMonoid a) →+*
      FractionRing (AddMonoidAlgebra k M) :=
  (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).comp
    (homogeneousExponentAlgHom a k).toRingHom

theorem homogeneousExponentFractionMap_character_ne_zero (j : ι) :
    homogeneousExponentFractionMap a k (homogeneousWeightCharacter a k j)≠0 := by
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
    (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j))≠0
  rw [homogeneousExponentAlgHom_character]
  simpa only [map_zero] using (IsFractionRing.injective
    (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).ne
      (show single (a j) (1 : k)≠0 by simp)

theorem dehomogeneousChartMap_fraction (j : ι) :
    (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).comp
      (dehomogeneousChartMap a k j).toRingHom=
      homogeneousAwayEvaluation (homogeneousWeightGrading a k)
        (homogeneousExponentFractionMap a k) (homogeneousWeightCharacter a k j)
        (homogeneousExponentFractionMap_character_ne_zero a k j) := by
  ext x
  obtain ⟨d,f,hf,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneousWeightGrading a k) (homogeneousWeightCharacter_homogeneous a k j) x
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
    (dehomogeneousChartMap a k j (Away.mk (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k j) d f hf)) = _
  rw [dehomogeneousChartMap_mk,homogeneousAwayEvaluation_mk]
  change algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (dehomogeneousWeightMap a k j f) =
    algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (homogeneousExponentAlgHom a k f) /
        (algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
          (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k j))) ^ d
  rw [homogeneousExponentAlgHom_character,homogeneousExponentAlgHom_factor a k hf j]
  simp only [smul_eq_mul,mul_one,map_mul,← map_pow,single_pow,one_pow]
  have hne : algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
      (single (d • a j) 1)≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective
      (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))).ne
        (show single (d • a j) (1 : k)≠0 by simp)
  exact (mul_div_cancel_left₀ _ hne).symm

def monomialTorusChart (j : ι) :
    Spec (CommRingCat.of (AddMonoidAlgebra k M))⟶monomialProjectiveScheme a k :=
  Spec.map (CommRingCat.ofHom (dehomogeneousChartMap a k j).toRingHom)≫
    Proj.awayι (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)

theorem monomialTorusChart_fraction (j : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))))≫monomialTorusChart a k j=
      projectiveFieldChart (homogeneousWeightGrading a k)
        (homogeneousExponentFractionMap a k) (homogeneousWeightCharacter a k j)
        (homogeneousWeightCharacter_homogeneous a k j) (by decide)
        (homogeneousExponentFractionMap_character_ne_zero a k j) := by
  unfold monomialTorusChart projectiveFieldChart
  erw [← Category.assoc,← Spec.map_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (dehomogeneousChartMap_fraction a k j)

theorem monomialTorusChart_independent (i j : ι) :
    monomialTorusChart a k i=monomialTorusChart a k j := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
    (FractionRing (AddMonoidAlgebra k M))))
  letI : IsDominant g := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))) ≤ nilradical (AddMonoidAlgebra k M)
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)]
    exact bot_le
  letI : (monomialProjectiveScheme a k).IsSeparated :=
    inferInstanceAs ((Proj (homogeneousWeightGrading a k)).IsSeparated)
  apply ext_of_isDominant g
  rw [monomialTorusChart_fraction,monomialTorusChart_fraction]
  exact projectiveFieldChart_independent _ _ _ _
    (homogeneousWeightCharacter_homogeneous a k i)
    (homogeneousWeightCharacter_homogeneous a k j) (by decide) (by decide)
    (homogeneousExponentFractionMap_character_ne_zero a k i)
    (homogeneousExponentFractionMap_character_ne_zero a k j)

def monomialCoordinateChartMap (j : ι) :
    monoidChartScheme k (differenceWeightMonoid a j)⟶monomialProjectiveScheme a k :=
  Spec.map (CommRingCat.ofHom (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom)≫
    Proj.awayι (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)

instance monomialCoordinateChartMap_isOpenImmersion (j : ι) :
    IsOpenImmersion (monomialCoordinateChartMap a k j) := by
  letI : IsIso (CommRingCat.ofHom
      (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom) :=
    (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold monomialCoordinateChartMap
  infer_instance

theorem monomialCoordinateChartMap_torus (j : ι) :
    Spec.map (CommRingCat.ofHom (monoidChartAlgebra k
      (differenceWeightMonoid a j)).val.toRingHom)≫monomialCoordinateChartMap a k j=
        monomialTorusChart a k j := by
  unfold monomialCoordinateChartMap monomialTorusChart
  erw [← Category.assoc,← Spec.map_comp]
  rfl

theorem monomialCoordinateChartMap_opensRange (j : ι) :
    (monomialCoordinateChartMap a k j).opensRange=
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j) := by
  letI : IsIso (CommRingCat.ofHom
      (homogeneousWeightChartEquiv a k j).toAlgHom.toRingHom) :=
    (homogeneousWeightChartEquiv a k j).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold monomialCoordinateChartMap
  erw [Scheme.Hom.opensRange_comp_of_isIso,
    Proj.opensRange_awayι]

/-- The second projective coordinate becomes exactly the difference
character on the first affine chart. -/
theorem monomialCoordinateChartMap_preimage_basicOpen (i j : ι) :
    monomialCoordinateChartMap a k i ⁻¹ᵁ
      Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)=
        PrimeSpectrum.basicOpen (chartCharacter k (differenceWeightMonoid a i)
          (a j-a i) (AddSubmonoid.subset_closure (Set.mem_range_self j))) := by
  unfold monomialCoordinateChartMap
  erw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k i) (by decide)
      (homogeneousWeightCharacter_homogeneous a k j) (by decide)]
  change PrimeSpectrum.basicOpen ((homogeneousWeightChartEquiv a k i)
    (HomogeneousLocalization.Away.isLocalizationElem
      (homogeneousWeightCharacter_homogeneous a k i)
      (homogeneousWeightCharacter_homogeneous a k j)))=_
  congr 1
  apply Subtype.ext
  simpa only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,chartCharacter_coe] using
    homogeneousWeightChartEquiv_character_ratio a k i j

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialTorusChart_independent
#print axioms PaperVerification.ToricCharacters.monomialCoordinateChartMap_preimage_basicOpen
end
end Source_ToricProjectiveMonomialMaps
-- END ORIGINAL PaperVerification.ToricProjectiveMonomialMaps


-- BEGIN ORIGINAL PaperVerification.ToricPointedMonoids
section Source_ToricPointedMonoids

-- original header: module

-- original header: public import Mathlib.GroupTheory.Finiteness
-- original header: public import Mathlib.Algebra.Group.Submonoid.BigOperators
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.Push

-- original header: @[expose] public section

/-!
# Minimal generators of a pointed affine semigroup

For a pointed submonoid of an abelian group, every member of a minimal
finite generating set is indecomposable. The proof uses only cancellation
and pointedness, without assuming saturation or normality. This is the
semigroup ingredient of the direct smoothness/cotangent argument.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped Classical

variable {M : Type*} [AddCommGroup M]

def IsPointedMonoid (S : AddSubmonoid M) : Prop :=
  ∀ x∈S, ∀ y∈S, x+y=0 → x=0 ∧ y=0

def IsMonoidAtom (S : AddSubmonoid M) (m : M) : Prop :=
  m∈S ∧ m≠0 ∧ ∀ x∈S, ∀ y∈S, x+y=m → x=0 ∨ y=0

theorem minimalGenerator_not_mem_eraseClosure (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g∉AddSubmonoid.closure (G.erase g : Set M) := by
  intro hbad
  have heq : AddSubmonoid.closure (G.erase g : Set M)=S := by
    apply le_antisymm
    · rw [← hG.prop]
      exact AddSubmonoid.closure_mono (Finset.erase_subset g G)
    · rw [← hG.prop]
      apply AddSubmonoid.closure_le.mpr
      intro x hx
      by_cases h : x=g
      · simpa [h] using hbad
      · exact AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩)
  exact hG.not_prop_of_lt (Finset.erase_ssubset hg) heq

theorem minimalGenerator_ne_zero (S : AddSubmonoid M)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : g≠0 := by
  intro hz
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  rw [hz]
  exact AddSubmonoid.zero_mem _

/-- Every generated element either avoids one selected generator, or
contains that generator plus another semigroup element. -/
theorem mem_closure_erase_or_add (S : AddSubmonoid M)
    (G : Finset M) (hG : AddSubmonoid.closure (G : Set M)=S)
    (g : M) {x : M} (hx : x∈S) :
    x∈AddSubmonoid.closure (G.erase g : Set M) ∨ ∃ z∈S,x=g+z := by
  rw [← hG] at hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      by_cases h : x=g
      · exact Or.inr ⟨0,S.zero_mem,by simpa [h]⟩
      · exact Or.inl (AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨h,hx⟩))
  | zero => exact Or.inl (AddSubmonoid.zero_mem _)
  | add x y hx hy ihx ihy =>
      have hxS : x∈S := hG ▸ hx
      have hyS : y∈S := hG ▸ hy
      rcases ihx with hx'|⟨z,hz,rfl⟩
      · rcases ihy with hy'|⟨z,hz,rfl⟩
        · exact Or.inl (AddSubmonoid.add_mem _ hx' hy')
        · exact Or.inr ⟨x+z,S.add_mem hxS hz,by abel⟩
      · exact Or.inr ⟨z+y,S.add_mem hz hyS,by abel⟩

theorem minimalGenerator_isAtom (S : AddSubmonoid M) (hS : IsPointedMonoid S)
    {G : Finset M} (hG : Minimal (fun T : Finset M => AddSubmonoid.closure (T : Set M)=S) G)
    {g : M} (hg : g∈G) : IsMonoidAtom S g := by
  refine ⟨hG.prop ▸ AddSubmonoid.subset_closure hg,
    minimalGenerator_ne_zero S hG hg, ?_⟩
  intro x hx y hy hxy
  by_contra h
  push_neg at h
  have hx' : x∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hx with hx'|⟨z,hz,hxg⟩
    · exact hx'
    · have hzy : z+y=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+y) = x+y := by rw [hxg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.2 (hS z hz y hy hzy).2).elim
  have hy' : y∈AddSubmonoid.closure (G.erase g : Set M) := by
    rcases mem_closure_erase_or_add S G hG.prop g hy with hy'|⟨z,hz,hyg⟩
    · exact hy'
    · have hzx : z+x=0 := by
        apply add_left_cancel (a := g)
        calc
          g+(z+x) = x+y := by rw [hyg]; abel
          _ = g+0 := by simpa using hxy
      exact (h.1 (hS z hz x hx hzx).2).elim
  apply minimalGenerator_not_mem_eraseClosure S hG hg
  have hsum : x+y∈AddSubmonoid.closure (G.erase g : Set M) :=
    AddSubmonoid.add_mem _ hx' hy'
  simpa only [hxy] using hsum

theorem exists_finite_atom_generators (S : AddSubmonoid M)
    (hS : IsPointedMonoid S) (hfg : S.FG) :
    ∃ G : Finset M, AddSubmonoid.closure (G : Set M)=S ∧
      ∀ g∈G,IsMonoidAtom S g := by
  obtain ⟨G,hG⟩ := hfg.exists_minimal_closure_eq
  exact ⟨G,hG.prop,fun g hg => minimalGenerator_isAtom S hS hG hg⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.exists_finite_atom_generators
end
end Source_ToricPointedMonoids
-- END ORIGINAL PaperVerification.ToricPointedMonoids


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveVertexMonoids
section Source_ToricProjectiveVertexMonoids

-- original header: module

-- original header: public import PaperVerification.ToricHomogeneousMonoidCharts
-- original header: public import PaperVerification.ToricPointedMonoids
-- original header: public import PaperVerification.ToricVertexCone
-- original header: public import PaperVerification.ToricStatements
-- original header: public import Mathlib.Tactic.Linarith

-- original header: @[expose] public section

/-!
# Pointedness of actual monomial vertex charts

At an actual vertex of the convex hull of the weights, strict separation
gives a nonnegative functional on all weight differences, vanishing only
at zero. Additive closure preserves this property, so the corresponding
actual affine Proj chart has a pointed exponent monoid.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open scoped Classical

theorem nonnegative_strict_on_closure {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    ∀ x∈AddSubmonoid.closure S,0≤f x ∧ (f x=0 → x=0) := by
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      refine ⟨add_nonneg ihx.1 ihy.1,?_⟩
      intro h
      have hx0 : f x=0 := by linarith [ihy.1]
      have hy0 : f y=0 := by linarith [ihx.1]
      rw [ihx.2 hx0,ihy.2 hy0,zero_add]

theorem pointed_closure_of_positive_functional {M : Type*} [AddCommGroup M]
    (S : Set M) (f : M →+ ℝ)
    (hS : ∀ x∈S,0≤f x ∧ (f x=0 → x=0)) :
    IsPointedMonoid (AddSubmonoid.closure S) := by
  intro x hx y hy hxy
  have hx' := nonnegative_strict_on_closure S f hS x hx
  have hy' := nonnegative_strict_on_closure S f hS y hy
  have he : f x+f y=0 := by rw [← map_add,hxy,map_zero]
  exact ⟨hx'.2 (by linarith),hy'.2 (by linarith)⟩

/-- Every actual vertex weight gives a pointed difference semigroup,
including a one-point hull in dimension zero or in a proper subspace. -/
theorem differenceWeightMonoid_pointed_at_vertex {ι : Type*} [Fintype ι]
    {n : ℕ} (a : ι → Lattice n) (j : ι)
    (hj : embed n (a j)∈
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ) :
    IsPointedMonoid (differenceWeightMonoid a j) := by
  let s : Finset (Ambient n) := Finset.univ.image (fun i=>embed n (a i))
  have hj' : embed n (a j)∈(convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa [s] using hj
  obtain ⟨h,hh⟩ := exists_strict_vertex_functional s hj'
  let f : Lattice n →+ ℝ := h.toLinearMap.toAddMonoidHom.comp (embed n)
  apply pointed_closure_of_positive_functional _ f
  rintro x ⟨i,rfl⟩
  by_cases he : a i=a j
  · simp [he,f]
  · have her : embed n (a i)≠embed n (a j) := (embed_injective n).ne he
    have hpos : 0<f (a i-a j) := by
      simpa [f,map_sub] using hh (embed n (a i))
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) her
    exact ⟨hpos.le,fun hz=>(hpos.ne' hz).elim⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.differenceWeightMonoid_pointed_at_vertex
end
end Source_ToricProjectiveVertexMonoids
-- END ORIGINAL PaperVerification.ToricProjectiveVertexMonoids


-- BEGIN ORIGINAL PaperVerification.ToricRationalFeasibility
section Source_ToricRationalFeasibility

-- original header: module

-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Data.Rat.Cast.Order
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Push

-- original header: @[expose] public section

/-!
# Rational solutions of finite rational weak linear systems

Fourier--Motzkin elimination is proved over an arbitrary ordered field.
For a system whose coefficients are rational, the same finite eliminated
system works over the rationals and over the reals. Induction on the
number of variables therefore supplies an actual rational solution to
every nonempty real rational polyhedron. Boundary solutions are included;
no strict-feasibility or full-dimensionality assumption is used.
-/

noncomputable section

namespace PaperVerification.ToricRationalGeometry

open scoped BigOperators Classical

theorem exists_linear_inequality_variable_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (a b : ι → K) :
    (∃ t : K,∀ i,0≤a i*t+b i) ↔
      (∀ i,a i=0 → 0≤b i) ∧
      (∀ i j,0<a i → a j<0 → -b i/a i≤-b j/a j) := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa [hi] using ht i,?_⟩
    intro i j hi hj
    have hlo : -b i/a i≤t := (div_le_iff₀ hi).mpr (by nlinarith [ht i])
    have hup : t≤-b j/a j := (le_div_iff_of_neg hj).mpr (by nlinarith [ht j])
    exact hlo.trans hup
  · rintro ⟨hz,hpair⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0<a i)
    let U : Finset ι := Finset.univ.filter (fun i => a i<0)
    have hrow (t : K) (hlo : ∀ i,0<a i → -b i/a i≤t)
        (hup : ∀ i,a i<0 → t≤-b i/a i) : ∀ i,0≤a i*t+b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi|hi|hi
      · have := (le_div_iff_of_neg hi).mp (hup i hi)
        nlinarith
      · simpa [hi] using hz i hi
      · have := (div_le_iff₀ hi).mp (hlo i hi)
        nlinarith
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,hmax⟩ := L.exists_max_image (fun i => -b i/a i) hL
      have hi0 : 0<a i := (Finset.mem_filter.mp hi).2
      refine ⟨-b i/a i,hrow _ ?_ ?_⟩
      · intro j hj
        exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
      · intro j hj
        exact hpair i j hi0 hj
    · by_cases hU : U.Nonempty
      · obtain ⟨j,hj,hmin⟩ := U.exists_min_image (fun i => -b i/a i) hU
        refine ⟨-b j/a j,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
      · refine ⟨0,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact (hU ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim

structure RationalAffineRow (n : ℕ) where
  constant : ℚ
  coefficient : Fin n → ℚ

namespace RationalAffineRow

variable {n : ℕ}

def eval {K : Type*} [Field K] [CharZero K] (r : RationalAffineRow n)
    (x : Fin n → K) : K :=
  (r.constant : K)+∑ i,(r.coefficient i : K)*x i

def zeroRow : RationalAffineRow n := ⟨0,fun _=>0⟩

def linearCombination (c d : ℚ) (r s : RationalAffineRow n) : RationalAffineRow n :=
  ⟨c*r.constant+d*s.constant,fun i=>c*r.coefficient i+d*s.coefficient i⟩

@[simp] theorem eval_zero {K : Type*} [Field K] [CharZero K] (x : Fin n → K) :
    (zeroRow : RationalAffineRow n).eval x=0 := by simp [eval,zeroRow]

@[simp] theorem eval_linearCombination {K : Type*} [Field K] [CharZero K]
    (c d : ℚ) (r s : RationalAffineRow n) (x : Fin n → K) :
    (linearCombination c d r s).eval x=(c : K)*r.eval x+(d : K)*s.eval x := by
  simp only [eval,linearCombination,Rat.cast_add,Rat.cast_mul,add_mul,
    Finset.sum_add_distrib,mul_add,mul_assoc,← Finset.mul_sum]
  ring

def zeroFirst (r : RationalAffineRow (n+1)) : RationalAffineRow n :=
  ⟨r.constant,fun i=>r.coefficient i.succ⟩

theorem eval_cons {K : Type*} [Field K] [CharZero K]
    (r : RationalAffineRow (n+1)) (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x)=(r.coefficient 0 : K)*t+r.zeroFirst.eval x := by
  simp [eval,zeroFirst,Fin.sum_univ_succ,add_assoc,add_comm,add_left_comm]

def eliminate {ι : Type*} (r : ι → RationalAffineRow (n+1)) :
    (ι ⊕ (ι × ι)) → RationalAffineRow n
  | Sum.inl i => if (r i).coefficient 0=0 then (r i).zeroFirst else zeroRow
  | Sum.inr (i,j) =>
      if 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 then
        linearCombination ((r i).coefficient 0)⁻¹ (-((r j).coefficient 0)⁻¹)
          (r i).zeroFirst (r j).zeroFirst
      else zeroRow

theorem eliminate_feasible_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (r : ι → RationalAffineRow (n+1)) (x : Fin n → K) :
    (∀ j,0≤(eliminate r j).eval x) ↔
      ∃ t : K,∀ i,0≤(r i).eval (Fin.cons t x) := by
  simp only [eval_cons]
  rw [exists_linear_inequality_variable_iff]
  constructor
  · intro hx
    refine ⟨?_,?_⟩
    · intro i hi
      have hiQ : (r i).coefficient 0=0 := by exact_mod_cast hi
      simpa [eliminate,hiQ] using hx (Sum.inl i)
    · intro i j hi hj
      have hiQ : 0<(r i).coefficient 0 := by exact_mod_cast hi
      have hjQ : (r j).coefficient 0<0 := by exact_mod_cast hj
      have h := hx (Sum.inr (i,j))
      have hijQ : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 := ⟨hiQ,hjQ⟩
      simp only [eliminate,if_pos hijQ,eval_linearCombination,
        Rat.cast_inv,Rat.cast_neg] at h
      simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg (sub_nonneg.mp
        (show 0≤((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x-
          ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x by nlinarith)))
  · rintro ⟨hz,hpairs⟩ row
    rcases row with i|⟨i,j⟩
    · by_cases hi : (r i).coefficient 0=0
      · simpa [eliminate,hi] using hz i (by exact_mod_cast hi)
      · simp [eliminate,hi]
    · by_cases hij : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0
      · have h := hpairs i j (by exact_mod_cast hij.1) (by exact_mod_cast hij.2)
        simp only [eliminate,if_pos hij,eval_linearCombination,
          Rat.cast_inv,Rat.cast_neg]
        have h' : ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x≤
            ((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x := by
          simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg h)
        nlinarith
      · simp [eliminate,hij]

end RationalAffineRow

open RationalAffineRow

/-- Every real solution of finitely many rational weak affine
inequalities can be replaced by a rational solution. -/
theorem rational_feasible_of_real_feasible (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] (r : ι → RationalAffineRow n),
      (∃ x : Fin n → ℝ,∀ i,0≤(r i).eval x) →
        ∃ y : Fin n → ℚ,∀ i,0≤(r i).eval y := by
  induction n with
  | zero =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      refine ⟨fun i=>Fin.elim0 i,?_⟩
      intro i
      have hi : 0≤((r i).constant : ℝ) := by simpa [eval] using hx i
      simpa [eval] using (Rat.cast_nonneg (K := ℝ)).mp hi
  | succ n ih =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      have hreal : ∃ x' : Fin n → ℝ,∀ j,0≤(eliminate r j).eval x' := by
        refine ⟨Fin.tail x,(eliminate_feasible_iff r (Fin.tail x)).mpr ⟨x 0,?_⟩⟩
        simpa using hx
      obtain ⟨y,hy⟩ := ih (eliminate r) hreal
      obtain ⟨t,ht⟩ := (eliminate_feasible_iff r y).mp hy
      exact ⟨Fin.cons t y,ht⟩

/-- The same statement with an arbitrary finite variable index. -/
theorem rational_matrix_feasible_of_real_feasible {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : ι → κ → ℚ) (b : ι → ℚ)
    (h : ∃ x : κ → ℝ,∀ i,0≤(b i : ℝ)+∑ j,(A i j : ℝ)*x j) :
    ∃ y : κ → ℚ,∀ i,0≤b i+∑ j,A i j*y j := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : ι → RationalAffineRow (Fintype.card κ) :=
    fun i=>⟨b i,fun j=>A i (e j)⟩
  obtain ⟨x,hx⟩ := h
  have hreal : ∃ z : Fin (Fintype.card κ) → ℝ,∀ i,0≤(r i).eval z := by
    refine ⟨fun j=>x (e j),?_⟩
    intro i
    simpa [r,eval,← e.sum_comp] using hx i
  obtain ⟨y,hy⟩ := rational_feasible_of_real_feasible _ r hreal
  refine ⟨fun j=>y (e.symm j),?_⟩
  intro i
  simpa [r,eval,← e.sum_comp] using hy i

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.rational_matrix_feasible_of_real_feasible
end
end Source_ToricRationalFeasibility
-- END ORIGINAL PaperVerification.ToricRationalFeasibility


-- BEGIN ORIGINAL PaperVerification.ToricRationalConvexRelations
section Source_ToricRationalConvexRelations

-- original header: module

-- original header: public import PaperVerification.ToricRationalFeasibility
-- original header: public import PaperVerification.ToricStatements
-- original header: public import Mathlib.Analysis.Convex.Combination
-- original header: public import Mathlib.Data.Rat.Lemmas
-- original header: public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
-- original header: public import Mathlib.Tactic.FieldSimp

-- original header: @[expose] public section

/-!
# Integral homogeneous relations from rational convex geometry

An integral point of the real convex hull of finitely many integral
points admits an integer homogeneous relation with those points and a
strictly positive total degree. This is derived from rational feasibility
and explicit denominator clearing. It applies on all faces, including
zero-dimensional hulls.
-/

noncomputable section

namespace PaperVerification.ToricRationalGeometry

open PaperVerification.ToricGeometry
open scoped BigOperators Classical

theorem rational_weights_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Fin n → ℚ) (m : Fin n → ℚ)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∀ j,∑ i,w i*(v i j : ℝ)=(m j : ℝ)) :
    ∃ q : κ → ℚ,(∀ i,0≤q i) ∧ ∑ i,q i=1 ∧ ∀ j,∑ i,q i*v i j=m j := by
  let I := κ ⊕ ((Unit ⊕ Fin n) × Bool)
  let A : I → κ → ℚ := fun row i => match row with
    | Sum.inl j => if i=j then 1 else 0
    | Sum.inr (Sum.inl _,false) => 1
    | Sum.inr (Sum.inl _,true) => -1
    | Sum.inr (Sum.inr j,false) => v i j
    | Sum.inr (Sum.inr j,true) => -v i j
  let b : I → ℚ := fun row => match row with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _,false) => -1
    | Sum.inr (Sum.inl _,true) => 1
    | Sum.inr (Sum.inr j,false) => -m j
    | Sum.inr (Sum.inr j,true) => m j
  have hfeasible : ∃ x : κ → ℝ,∀ row,0≤(b row : ℝ)+∑ i,(A row i : ℝ)*x i := by
    refine ⟨w,?_⟩
    intro row
    rcases row with i|⟨tag,sign⟩
    · simpa [A,b,apply_ite,ite_mul] using hw0 i
    · rcases tag with u|j <;> cases sign
      · simp [A,b,hw1]
      · simp [A,b,hw1,Finset.sum_neg_distrib]
      · simp [A,b,mul_comm,hwm j]
      · simp [A,b,mul_comm,hwm j,Finset.sum_neg_distrib]
  obtain ⟨q,hq⟩ := rational_matrix_feasible_of_real_feasible A b hfeasible
  refine ⟨q,?_,?_,?_⟩
  · intro i
    simpa [A,b] using hq (Sum.inl i)
  · have hlo := hq (Sum.inr (Sum.inl (),false))
    have hup := hq (Sum.inr (Sum.inl (),true))
    simp only [A,b,one_mul,neg_one_mul,Finset.sum_neg_distrib] at hlo hup
    linarith
  · intro j
    have hlo := hq (Sum.inr (Sum.inr j,false))
    have hup := hq (Sum.inr (Sum.inr j,true))
    simp only [A,b,neg_mul,Finset.sum_neg_distrib] at hlo hup
    simpa [mul_comm] using le_antisymm (by linarith : ∑ i,v i j*q i≤m j)
      (by linarith : m j≤∑ i,v i j*q i)

/-- A common positive denominator gives nonnegative integer weights. -/
theorem clear_nonnegative_rational_denominators {κ : Type*} [Fintype κ]
    (q : κ → ℚ) (hq : ∀ i,0≤q i) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,∀ i,(c i : ℚ)=(N : ℚ)*q i := by
  let N : ℕ := ∏ i,(q i).den
  have hN : 0<N := Finset.prod_pos (fun i hi => (q i).den_pos)
  let c : κ → ℕ := fun i => (q i).num.toNat*(N/(q i).den)
  refine ⟨N,hN,c,?_⟩
  intro i
  have hdiv : (q i).den∣N := Finset.dvd_prod_of_mem (fun i=>(q i).den)
    (Finset.mem_univ i)
  have hmul : (q i).den*(N/(q i).den)=N := Nat.mul_div_cancel' hdiv
  have hnum : 0≤(q i).num := Rat.num_nonneg.mpr (hq i)
  have hnumcast : ((q i).num.toNat : ℚ)=((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hNcast : (N : ℚ)=((q i).den : ℚ)*((N/(q i).den : ℕ) : ℚ) := by
    exact_mod_cast hmul.symm
  change (((q i).num.toNat*(N/(q i).den) : ℕ) : ℚ)=(N : ℚ)*q i
  rw [Nat.cast_mul,hnumcast]
  have hd : ((q i).den : ℚ)≠0 := by exact_mod_cast (q i).den_ne_zero
  calc
    ((q i).num : ℚ) * ((N/(q i).den : ℕ) : ℚ) =
        (N : ℚ) * (((q i).num : ℚ) / ((q i).den : ℚ)) := by
      rw [hNcast]
      field_simp
    _ = (N : ℚ) * q i := congrArg ((N : ℚ) * ·) (q i).num_div_den

theorem integral_relation_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Lattice n) (m : Lattice n)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∑ i,w i • embed n (v i)=embed n m) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  let vQ : κ → Fin n → ℚ := fun i j=>(v i j : ℚ)
  let mQ : Fin n → ℚ := fun j=>(m j : ℚ)
  have hcoord (j : Fin n) : ∑ i,w i*(vQ i j : ℝ)=(mQ j : ℝ) := by
    have := congrFun hwm j
    simpa [vQ,mQ,embed,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using this
  obtain ⟨q,hq0,hq1,hqm⟩ := rational_weights_of_real_weights vQ mQ w hw0 hw1 hcoord
  obtain ⟨N,hN,c,hc⟩ := clear_nonnegative_rational_denominators q hq0
  refine ⟨N,hN,c,?_,?_⟩
  · have hsum : (∑ i,(c i : ℚ))=(N : ℚ) := by
      simp only [hc,← Finset.mul_sum,hq1,mul_one]
    exact_mod_cast hsum
  · ext j
    have hsum : ∑ i,(c i : ℚ)*(v i j : ℚ)=(N : ℚ)*(m j : ℚ) := by
      simp only [hc,mul_assoc,← Finset.mul_sum]
      exact congrArg ((N : ℚ)*·) (hqm j)
    simpa [Finset.sum_apply,Pi.smul_apply,nsmul_eq_mul] using
      (show ∑ i,(c i : ℤ)*v i j=(N : ℤ)*m j by exact_mod_cast hsum)

theorem integral_relation_of_mem_convexHull {n : ℕ} (V : Finset (Lattice n))
    (m : Lattice n) (hm : embed n m∈convexHull ℝ (embed n '' (V : Set (Lattice n)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : V → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • i.val=N • m := by
  have hm' : embed n m∈convexHull ℝ (V.image (embed n) : Set (Ambient n)) := by
    simpa using hm
  obtain ⟨w,hw0,hw1,hwm⟩ := Finset.mem_convexHull'.mp hm'
  have hsum : ∑ i : V,w (embed n i.val)=1 := by
    calc
      ∑ i : V,w (embed n i.val)=∑ i∈V,w (embed n i) := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i))
      _ = 1 := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hw1
  have hvec : ∑ i : V,w (embed n i.val) • embed n i.val=embed n m := by
    calc
      ∑ i : V,w (embed n i.val) • embed n i.val=
          ∑ i∈V,w (embed n i) • embed n i := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i) • embed n i)
      _ = embed n m := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hwm
  exact integral_relation_of_real_weights (fun i : V=>i.val) m
    (fun i=>w (embed n i.val))
    (fun i=>hw0 _ (Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩)) hsum hvec

theorem integral_relation_of_mem_convexHull_range {κ : Type*} [Fintype κ]
    {n : ℕ} (v : κ → Lattice n) (m : Lattice n)
    (hm : embed n m∈convexHull ℝ (Set.range (fun i=>embed n (v i)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  rw [convexHull_range_eq_exists_affineCombination] at hm
  obtain ⟨s,w,hw0,hw1,hwm⟩ := hm
  let w' : κ → ℝ := fun i=>if i∈s then w i else 0
  have hw'0 (i : κ) : 0≤w' i := by
    by_cases hi : i∈s
    · simpa [w',hi] using hw0 i hi
    · simp [w',hi]
  have hw'1 : ∑ i,w' i=1 := by simpa [w'] using hw1
  have hvec : ∑ i,w' i • embed n (v i)=embed n m := by
    rw [Finset.affineCombination_eq_linear_combination s _ _ hw1] at hwm
    simpa [w',ite_smul] using hwm
  exact integral_relation_of_real_weights v m w' hw'0 hw'1 hvec

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.integral_relation_of_mem_convexHull
end
end Source_ToricRationalConvexRelations
-- END ORIGINAL PaperVerification.ToricRationalConvexRelations


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveVertexCover
section Source_ToricProjectiveVertexCover

-- original header: module

-- original header: public import PaperVerification.ToricProjectiveVertexMonoids
-- original header: public import PaperVerification.ToricRationalConvexRelations
-- original header: public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
-- original header: public import Mathlib.RingTheory.Ideal.Operations
-- original header: public import Lean.Elab.Tactic.Omega

-- original header: @[expose] public section

/-!
# The actual monomial Proj is covered by its vertex charts

All homogeneous coordinate charts first give the usual Proj cover.
An integral homogeneous relation expresses a power of every coordinate
as a product of vertex coordinates. Hence each coordinate chart lies in
a vertex chart. The finite family of vertex charts therefore covers the
actual projective scheme, with no assumed orbit-face correspondence.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open PaperVerification.ToricRationalGeometry
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)
    (k : Type*) [CommRing k]

theorem homogeneousWeightCharacter_adjoin :
    Algebra.adjoin (homogeneousWeightGrading a k 0)
      (Set.range (homogeneousWeightCharacter a k))=⊤ := by
  let A := Algebra.adjoin (homogeneousWeightGrading a k 0)
    (Set.range (homogeneousWeightCharacter a k))
  have hchar (p : homogeneousWeightMonoid a) : single p (1 : k)∈A := by
    refine AddSubmonoid.closure_induction
      (motive := fun x hx => single (⟨x,hx⟩ : homogeneousWeightMonoid a) (1 : k)∈A)
      ?_ ?_ ?_ p.property
    · intro x hx
      obtain ⟨i,rfl⟩ := hx
      exact Algebra.subset_adjoin (Set.mem_range_self i)
    · change (1 : AddMonoidAlgebra k (homogeneousWeightMonoid a))∈A
      exact A.one_mem
    · intro x y hx hy ihx ihy
      change single ((⟨x,hx⟩ : homogeneousWeightMonoid a)+⟨y,hy⟩) (1 : k)∈A
      simpa only [single_mul_single,mul_one] using A.mul_mem ihx ihy
  apply top_unique
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_on with
  | of p => exact hchar p
  | add f g hf hg => exact A.add_mem hf hg
  | smul r f hf =>
      have hr : algebraMap k (AddMonoidAlgebra k (homogeneousWeightMonoid a)) r∈A := by
        exact A.algebraMap_mem (homogeneousWeightZeroMap a k r)
      rw [Algebra.smul_def]
      exact A.mul_mem hr hf

theorem monomialProjective_coordinate_cover :
    (⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i))=⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i=>⟨1,homogeneousWeightCharacter_homogeneous a k i⟩)
    (homogeneousWeightCharacter_adjoin a k)

theorem homogeneousWeightCharacter_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    homogeneousWeightCharacter a k j ^ N=
      ∏ i,homogeneousWeightCharacter a k (v i) ^ c i := by
  have he : N • homogeneousWeight a j=∑ i,c i • homogeneousWeight a (v i) := by
    apply Subtype.ext
    apply Prod.ext
    · simpa [homogeneousWeight,Prod.fst_sum] using hsum.symm
    · simpa [homogeneousWeight,Prod.snd_sum] using hweight.symm
  simp [homogeneousWeightCharacter,single_pow,prod_single,he]

theorem basicOpen_le_vertex_cover_of_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (hN : 0<N) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)≤
      ⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter a k (v i)) := by
  have hcpos : ∃ i,0<c i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i,c i=0 := fun i=>Nat.eq_zero_of_le_zero (h i)
    have : N=0 := by simpa [hzero] using hsum.symm
    omega
  obtain ⟨i,hi⟩ := hcpos
  have hdiv : homogeneousWeightCharacter a k (v i)∣homogeneousWeightCharacter a k j ^ N := by
    rw [homogeneousWeightCharacter_relation a k j v N c hsum hweight]
    exact (dvd_pow_self _ (ne_of_gt hi)).trans
      (Finset.dvd_prod_of_mem (fun i=>homogeneousWeightCharacter a k (v i)^c i)
        (Finset.mem_univ i))
  have h := Proj.basicOpen_mono (homogeneousWeightGrading a k) _ _ hdiv
  rw [Proj.basicOpen_pow _ _ N hN] at h
  exact h.trans (le_iSup_of_le i le_rfl)

variable [Fintype ι] {n : ℕ}

def vertexWeightIndices (a : ι → Lattice n) : Finset ι :=
  Finset.univ.filter (fun i=>embed n (a i)∈
    (convexHull ℝ (Set.range (fun j=>embed n (a j)))).extremePoints ℝ)

theorem range_vertexWeightIndices (a : ι → Lattice n) :
    Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))=
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact (Finset.mem_filter.mp i.property).2
  · intro hx
    obtain ⟨i,rfl⟩ := extremePoints_convexHull_subset hx
    exact ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩⟩,rfl⟩

theorem hull_vertexWeightIndices (a : ι → Lattice n) :
    convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  rw [range_vertexWeightIndices]
  simpa using finite_hull_eq_hull_extremePoints
    (Finset.univ.image (fun i=>embed n (a i)))

/-- Actual vertex-coordinate basic opens cover the actual Proj of the
homogeneous monomial algebra. -/
theorem monomialProjective_vertex_cover (a : ι → Lattice n) :
    (⨆ i : vertexWeightIndices a,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i.val))=⊤ := by
  apply top_le_iff.mp
  rw [← monomialProjective_coordinate_cover a k]
  apply iSup_le
  intro j
  have hj : embed n (a j)∈convexHull ℝ
      (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))) := by
    rw [hull_vertexWeightIndices]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨N,hN,c,hsum,hweight⟩ := integral_relation_of_mem_convexHull_range
    (fun i : vertexWeightIndices a=>a i.val) (a j) hj
  exact basicOpen_le_vertex_cover_of_relation a k j Subtype.val N hN c hsum hweight

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialProjective_vertex_cover
end
end Source_ToricProjectiveVertexCover
-- END ORIGINAL PaperVerification.ToricProjectiveVertexCover


-- BEGIN ORIGINAL PaperVerification.ToricMonomialProjectiveEmbedding
section Source_ToricMonomialProjectiveEmbedding

-- original header: module

-- original header: public import PaperVerification.ToricGradedProjQuotient
-- original header: public import PaperVerification.ToricProjectiveMonomialMaps
-- original header: public import PaperVerification.ToricProjectiveVertexCover
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

-- original header: @[expose] public section

/-!
# The actual monomial projective closed immersion

The graded polynomial quotient sends the i-th projective coordinate to
the homogeneous character (1,aᵢ). Its Proj is embedded by the actual
graded-ring morphism. All coordinate charts are domains, and the common
character torus is schematically dense. Thus this Proj is the genuine
scheme-theoretic monomial orbit closure, rather than an assumed model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u v

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra AlgebraicGeometry CategoryTheory HomogeneousLocalization
open PaperVerification.ToricSchemes
open scoped BigOperators Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι : Type u} {M : Type v} [AddCommGroup M] (a : ι→M)
    (k : Type (max u v)) [Field k]

def homogeneousMonomialMap :
    MvPolynomial ι k→ₐ[k]AddMonoidAlgebra k (homogeneousWeightMonoid a) :=
  MvPolynomial.aeval (homogeneousWeightCharacter a k)

@[simp] theorem homogeneousMonomialMap_X (i : ι) :
    homogeneousMonomialMap a k (MvPolynomial.X i)=homogeneousWeightCharacter a k i := by
  simp [homogeneousMonomialMap]

theorem homogeneousMonomialMap_mem {d : ℕ} {p : MvPolynomial ι k}
    (hp : p∈MvPolynomial.homogeneousSubmodule ι k d) :
    homogeneousMonomialMap a k p∈homogeneousWeightGrading a k d := by
  rw [← p.support_sum_monomial_coeff,map_sum]
  apply Submodule.sum_mem
  intro m hm
  rw [homogeneousMonomialMap,MvPolynomial.aeval_monomial,← Algebra.smul_def]
  apply Submodule.smul_mem
  have hd := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm
  have hprod := SetLike.prod_pow_mem_graded (homogeneousWeightGrading a k)
    (fun _ : ι=>1) (homogeneousWeightCharacter a k) m
      (F := m.support) (fun i _=>homogeneousWeightCharacter_homogeneous a k i)
  simpa only [Finsupp.prod,smul_eq_mul,mul_one,← hd] using hprod

def homogeneousMonomialGradedMap :
    MvPolynomial.homogeneousSubmodule ι k→+*ᵍhomogeneousWeightGrading a k where
  __ := (homogeneousMonomialMap a k).toRingHom
  map_mem := homogeneousMonomialMap_mem a k

@[simp] theorem homogeneousMonomialGradedMap_X (i : ι) :
    homogeneousMonomialGradedMap a k (MvPolynomial.X i)=
      homogeneousWeightCharacter a k i := homogeneousMonomialMap_X a k i

theorem homogeneousMonomialMap_surjective :
    Function.Surjective (homogeneousMonomialMap a k) := by
  have hchar (p : homogeneousWeightMonoid a) :
      ∃ q : MvPolynomial ι k,homogeneousMonomialMap a k q=single p 1 := by
    refine AddSubmonoid.closure_induction
      (motive := fun x hx=>∃ q : MvPolynomial ι k,
        homogeneousMonomialMap a k q=single (⟨x,hx⟩ : homogeneousWeightMonoid a) 1)
      ?_ ?_ ?_ p.property
    · rintro x ⟨i,rfl⟩
      exact ⟨MvPolynomial.X i,by simp [homogeneousWeightCharacter,homogeneousWeight]⟩
    · exact ⟨1,by rw [map_one]; rfl⟩
    · intro x y hx hy ihx ihy
      obtain ⟨p,hp⟩ := ihx
      obtain ⟨q,hq⟩ := ihy
      exact ⟨p*q,by rw [map_mul,hp,hq]; simp only [single_mul_single,mul_one]; rfl⟩
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of p => exact hchar p
  | add f g hf hg =>
      obtain ⟨p,rfl⟩ := hf
      obtain ⟨q,rfl⟩ := hg
      exact ⟨p+q,map_add _ _ _⟩
  | smul r f hf =>
      obtain ⟨p,rfl⟩ := hf
      exact ⟨r • p,map_smul _ _ _⟩

theorem homogeneousMonomialGradedMap_surjective :
    Function.Surjective (homogeneousMonomialGradedMap a k) :=
  homogeneousMonomialMap_surjective a k

def monomialProjectiveEmbedding :
    monomialProjectiveScheme a k⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  Proj.map (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))

instance monomialProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (monomialProjectiveEmbedding a k) :=
  projMap_isClosedImmersion_of_surjective _ (homogeneousMonomialGradedMap_surjective a k)

@[simp] theorem monomialProjectiveEmbedding_preimage (i : ι) :
    monomialProjectiveEmbedding a k ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)=
        Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k i) := by
  unfold monomialProjectiveEmbedding
  rw [Proj.map_preimage_basicOpen,homogeneousMonomialGradedMap_X]

variable [IsDomain (AddMonoidAlgebra k M)]

def projectiveMonomialFieldMap :
    MvPolynomial ι k→+*FractionRing (AddMonoidAlgebra k M) :=
  (homogeneousExponentFractionMap a k).comp (homogeneousMonomialGradedMap a k).toRingHom

@[simp] theorem projectiveMonomialFieldMap_X (i : ι) :
    projectiveMonomialFieldMap a k (MvPolynomial.X i)=
      algebraMap (AddMonoidAlgebra k M) (FractionRing (AddMonoidAlgebra k M))
        (single (a i) 1) := by
  simp [projectiveMonomialFieldMap,homogeneousMonomialGradedMap,
    homogeneousMonomialMap,homogeneousExponentFractionMap,homogeneousWeightCharacter,
    homogeneousWeight]

theorem monomialProjectiveEmbedding_torus_generic (i : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra k M)
      (FractionRing (AddMonoidAlgebra k M))))≫
        monomialTorusChart a k i≫monomialProjectiveEmbedding a k=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (projectiveMonomialFieldMap a k) (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
        (by decide)
        (by
          change homogeneousExponentFractionMap a k
            (homogeneousMonomialGradedMap a k (MvPolynomial.X i))≠0
          rw [homogeneousMonomialGradedMap_X]
          exact homogeneousExponentFractionMap_character_ne_zero a k i) := by
  erw [← Category.assoc,monomialTorusChart_fraction]
  have hne : homogeneousExponentFractionMap a k
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i)) ≠ 0 := by
    rw [homogeneousMonomialGradedMap_X]
    exact homogeneousExponentFractionMap_character_ne_zero a k i
  have h := projectiveFieldChart_gradedMap (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))
    (homogeneousExponentFractionMap a k) (s := MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
    (by decide) hne
  simpa only [homogeneousMonomialGradedMap_X,monomialProjectiveEmbedding,
    projectiveMonomialFieldMap] using h

variable {K : Type (max u v)} [Field K]

theorem monomialTorusChart_fieldMap (ρ : AddMonoidAlgebra k M→+*K)
    (hρ : Function.Injective ρ) (i : ι) :
    Spec.map (CommRingCat.ofHom ρ)≫monomialTorusChart a k i=
      projectiveFieldChart (homogeneousWeightGrading a k)
        (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
        (homogeneousWeightCharacter a k i)
        (homogeneousWeightCharacter_homogeneous a k i) (by decide)
        (by
          change ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i))≠0
          rw [homogeneousExponentAlgHom_character]
          simpa only [map_zero] using
            hρ.ne (show single (a i) (1:k)≠0 by simp)) := by
  have hne : ρ (single (a i) 1)≠0 := by
    simpa only [map_zero] using hρ.ne (show single (a i) (1:k)≠0 by simp)
  have hE : ρ.comp (dehomogeneousChartMap a k i).toRingHom=
      homogeneousAwayEvaluation (homogeneousWeightGrading a k)
        (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
        (homogeneousWeightCharacter a k i) (by
          change ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i))≠0
          rw [homogeneousExponentAlgHom_character]
          exact hne) := by
    ext z
    obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter_homogeneous a k i) z
    change ρ (dehomogeneousChartMap a k i
      (Away.mk (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter_homogeneous a k i) d p hp)) = _
    rw [dehomogeneousChartMap_mk,homogeneousAwayEvaluation_mk]
    change ρ (dehomogeneousWeightMap a k i p) =
      ρ (homogeneousExponentAlgHom a k p) /
        ρ (homogeneousExponentAlgHom a k (homogeneousWeightCharacter a k i)) ^ d
    rw [homogeneousExponentAlgHom_character,homogeneousExponentAlgHom_factor a k hp i]
    simp only [smul_eq_mul,mul_one]
    rw [map_mul]
    have hpow : ρ (single (d • a i) 1)=ρ (single (a i) 1)^d := by
      rw [← map_pow,single_pow,one_pow]
    rw [hpow,mul_div_cancel_left₀ _ (pow_ne_zero d hne)]
  unfold monomialTorusChart projectiveFieldChart
  erw [← Category.assoc,← Spec.map_comp]
  exact congrArg (fun F=>Spec.map (CommRingCat.ofHom F)≫_) hE

theorem monomialProjectiveEmbedding_torus_fieldMap
    (ρ : AddMonoidAlgebra k M→+*K) (hρ : Function.Injective ρ) (i : ι) :
    Spec.map (CommRingCat.ofHom ρ)≫monomialTorusChart a k i≫
        monomialProjectiveEmbedding a k=
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        ((ρ.comp (homogeneousExponentAlgHom a k).toRingHom).comp
          (homogeneousMonomialGradedMap a k).toRingHom)
        (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
        (by decide)
        (by
          change ρ (homogeneousExponentAlgHom a k
            (homogeneousMonomialGradedMap a k (MvPolynomial.X i)))≠0
          rw [homogeneousMonomialGradedMap_X,homogeneousExponentAlgHom_character]
          simpa only [map_zero] using
            hρ.ne (show single (a i) (1:k)≠0 by simp)) := by
  erw [← Category.assoc,monomialTorusChart_fieldMap a k ρ hρ i]
  have hne : (ρ.comp (homogeneousExponentAlgHom a k).toRingHom)
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i)) ≠ 0 := by
    change ρ (homogeneousExponentAlgHom a k
      (homogeneousMonomialGradedMap a k (MvPolynomial.X i))) ≠ 0
    rw [homogeneousMonomialGradedMap_X,homogeneousExponentAlgHom_character]
    simpa only [map_zero] using hρ.ne (show single (a i) (1:k)≠0 by simp)
  have h := projectiveFieldChart_gradedMap (homogeneousMonomialGradedMap a k)
    (irrelevant_le_map_of_surjective _ (homogeneousMonomialGradedMap_surjective a k))
    (ρ.comp (homogeneousExponentAlgHom a k).toRingHom) (s := MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
    (by decide) hne
  simpa only [homogeneousMonomialGradedMap_X,monomialProjectiveEmbedding] using h

instance monomialChart_isDomain (i : ι) :
    IsDomain (monoidChartAlgebra k (differenceWeightMonoid a i)) := by
  exact Function.Injective.isDomain
    (monoidChartAlgebra k (differenceWeightMonoid a i)).val.toRingHom Subtype.val_injective

def monomialCoordinateOpenCover : (monomialProjectiveScheme a k).OpenCover :=
  Scheme.Cover.mkOfCovers ι
    (fun i=>monoidChartScheme k (differenceWeightMonoid a i))
    (monomialCoordinateChartMap a k) (by
    intro x
    have hx : x∈⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter a k i) := by
      rw [monomialProjective_coordinate_cover]; trivial
    obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    rw [← monomialCoordinateChartMap_opensRange] at hi
    obtain ⟨y,hy⟩ := hi
    exact ⟨i,y,hy⟩)

instance monomialProjective_isReduced : IsReduced (monomialProjectiveScheme a k) := by
  letI : ∀ i : (monomialCoordinateOpenCover a k).I₀,
      IsReduced ((monomialCoordinateOpenCover a k).X i) := fun i => by
    change IsReduced (monoidChartScheme k (differenceWeightMonoid a i))
    unfold monoidChartScheme
    infer_instance
  exact IsReduced.of_openCover _ (monomialCoordinateOpenCover a k)

def monomialCoordinateGenericPoint (i : ι) :
    monoidChartScheme k (differenceWeightMonoid a i) := ⟨⊥,inferInstance⟩

theorem monomialCoordinateGenericPoint_isGenericPoint (i : ι) :
    IsGenericPoint (monomialCoordinateGenericPoint a k i) Set.univ := by
  change closure ({monomialCoordinateGenericPoint a k i} :
    Set (PrimeSpectrum (monoidChartAlgebra k (differenceWeightMonoid a i))))=Set.univ
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

theorem monomialTorusChart_denseRange (j : ι) : DenseRange (monomialTorusChart a k j) := by
  let η : Spec (CommRingCat.of (AddMonoidAlgebra k M)) := ⟨⊥,inferInstance⟩
  have hη (i : ι) :
      monomialCoordinateChartMap a k i (monomialCoordinateGenericPoint a k i)=
        monomialTorusChart a k j η := by
    rw [← monomialTorusChart_independent a k i j,
      ← monomialCoordinateChartMap_torus]
    change _=monomialCoordinateChartMap a k i _
    congr 1
    apply PrimeSpectrum.ext
    exact (Ideal.comap_bot_of_injective _ Subtype.val_injective).symm
  intro x
  obtain ⟨i,y,rfl⟩ := (monomialCoordinateOpenCover a k).exists_eq x
  have hclosed : IsClosed ((monomialCoordinateChartMap a k i) ⁻¹'
      closure (Set.range (monomialTorusChart a k j))) :=
    isClosed_closure.preimage (monomialCoordinateChartMap a k i).continuous
  have hmem : monomialCoordinateGenericPoint a k i∈
      (monomialCoordinateChartMap a k i) ⁻¹'
        closure (Set.range (monomialTorusChart a k j)) := by
    change monomialCoordinateChartMap a k i (monomialCoordinateGenericPoint a k i) ∈
      closure (Set.range (monomialTorusChart a k j))
    rw [hη]
    exact subset_closure (Set.mem_range_self η)
  exact ((monomialCoordinateGenericPoint_isGenericPoint a k i).mem_closed_set_iff hclosed).mp
    hmem (Set.mem_univ y)

instance monomialTorusChart_isDominant (j : ι) : IsDominant (monomialTorusChart a k j) :=
  ⟨monomialTorusChart_denseRange a k j⟩

instance monomialTorusChart_isSchemeTheoreticallyDominant (j : ι) :
    IsSchemeTheoreticallyDominant (monomialTorusChart a k j) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialProjectiveEmbedding_isClosedImmersion
#print axioms PaperVerification.ToricCharacters.monomialTorusChart_isSchemeTheoreticallyDominant
end
end Source_ToricMonomialProjectiveEmbedding
-- END ORIGINAL PaperVerification.ToricMonomialProjectiveEmbedding


-- BEGIN ORIGINAL PaperVerification.ToricMonomialImageComparison
section Source_ToricMonomialImageComparison

-- original header: module

-- original header: public import PaperVerification.ToricMonomialProjectiveEmbedding
-- original header: public import PaperVerification.ToricAffineGenericPoint
-- original header: public import PaperVerification.ToricIntrinsicSectionCharacters
-- original header: public import PaperVerification.ToricSectionProjectiveEmbedding

-- original header: @[expose] public section

/-!
# Equality with the genuine closed monomial image

Two closed immersions receiving the same schematically dense torus have
the same kernel ideal sheaf. The universal property of closed immersions
therefore gives an actual scheme isomorphism. Character-valued genuine
sections give precisely the same projective torus morphism, as checked
in the actual generic stalk.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical BaseSections

theorem closedImmersion_ker_eq_of_dense_composite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    (h : j≫f=q≫g) : f.ker=g.ker := by
  have H := congrArg Scheme.Hom.ker h
  simpa only [Scheme.Hom.ker_comp,Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using H

def closedImageIsoOfDenseComposite
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : j≫f=q≫g) : X≅Y := by
  let H := (closedImmersion_ker_eq_of_dense_composite j q f g h).symm
  letI := IsClosedImmersion.isIso_lift g f H
  exact asIso (IsClosedImmersion.lift g f H.le)

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_embedding
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    (closedImageIsoOfDenseComposite j q f g h).hom≫g=f := by
  exact IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)] theorem closedImageIsoOfDenseComposite_torus
    {T X Y Z : Scheme.{u}} (j : T⟶X) (q : T⟶Y)
    (f : X⟶Z) (g : Y⟶Z)
    [IsSchemeTheoreticallyDominant j] [IsSchemeTheoreticallyDominant q]
    [IsClosedImmersion f] [IsClosedImmersion g] (h : j≫f=q≫g) :
    j≫(closedImageIsoOfDenseComposite j q f g h).hom=q := by
  apply (cancel_mono g).mp
  rw [Category.assoc,closedImageIsoOfDenseComposite_embedding]
  exact h

namespace RationalCartierCocycle

variable (k : Type u) [Field k] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ)⟶X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u}
    (a : ι→(Fin n→ℤ)) (s : ι→Γ(C.sheaf,⊤))
    (hvalue : ∀ i,C.toCartierData.sectionValue ⊤ (s i)=
      openTorusRationalAlgHom k n X j (AddMonoidAlgebra.single (a i) (1:k)))

local instance : IsDomain (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusCoordinateRing_isDomain k n

include hvalue in
theorem character_sectionProjectiveFieldMap :
    C.sectionProjectiveFieldMap k s=
      ((openTorusRationalAlgHom k n X j).toRingHom.comp
        (homogeneousExponentAlgHom a k).toRingHom).comp
        (homogeneousMonomialGradedMap a k).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_C,
      RingHom.comp_apply, BaseSections.germ_scalarMap]
    change algebraMap k X.functionField c =
      openTorusRationalAlgHom k n X j
        (homogeneousExponentAlgHom a k
          (homogeneousMonomialMap a k (algebraMap k (MvPolynomial ι k) c)))
    exact ((congrArg
      (fun x => openTorusRationalAlgHom k n X j (homogeneousExponentAlgHom a k x))
      ((homogeneousMonomialMap a k).commutes c)).trans
      ((congrArg (openTorusRationalAlgHom k n X j)
        ((homogeneousExponentAlgHom a k).commutes c)).trans
        ((openTorusRationalAlgHom k n X j).commutes c))).symm
  · intro i
    simpa [sectionProjectiveFieldMap,homogeneousMonomialGradedMap,
      homogeneousMonomialMap,homogeneousWeightCharacter,homogeneousWeight] using hvalue i

include hvalue in
/-- The actual section embedding has the literal projective monomial
map on the actual open torus. -/
theorem character_sectionProjectiveMap_torus
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι) :
    j≫C.sectionProjectiveMap k s hcover=
      monomialTorusChart a k i≫monomialProjectiveEmbedding a k := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  let jR : Spec R ⟶ X := j
  letI : IsOpenImmersion jR := inferInstanceAs (IsOpenImmersion j)
  let ρ := openTorusRationalAlgHom k n X j
  let η := Spec.map (CommRingCat.ofHom ρ.toRingHom)
  letI : IsDominant η := affineOpenCoordinateMap_isDominant R jR
  apply ext_of_isDominant η
  have hi : C.toCartierData.sectionValue ⊤ (s i)≠0 := by
    rw [hvalue i]
    simpa only [map_zero] using (openTorusRationalAlgHom_injective k n X j).ne
      (show AddMonoidAlgebra.single (a i) (1:k)≠0 by simp)
  have hη : η≫j=X.fromSpecStalk (genericPoint X) :=
    affineOpenCoordinateMap_genericPoint R jR
  have hleft := ((Category.assoc η jR (C.sectionProjectiveMap k s hcover)).symm.trans
    (congrArg (fun q => q ≫ C.sectionProjectiveMap k s hcover) hη)).trans
      (C.sectionProjectiveMap_generic_of_value_ne_zero k s hcover i hi)
  have hmonomial := monomialProjectiveEmbedding_torus_fieldMap a k ρ.toRingHom
    (openTorusRationalAlgHom_injective k n X j) i
  have hfield : C.sectionProjectiveFieldMap k s =
      (ρ.toRingHom.comp (homogeneousExponentAlgHom a k).toRingHom).comp
        (homogeneousMonomialGradedMap a k).toRingHom :=
    C.character_sectionProjectiveFieldMap k j a s hvalue
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule ι k) :=
    MvPolynomial.gradedAlgebra
  have hcharts (φ ψ : MvPolynomial ι k →+* X.functionField)
      (h : φ = ψ) (hφ : φ (MvPolynomial.X i) ≠ 0)
      (hψ : ψ (MvPolynomial.X i) ≠ 0) :
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k) φ (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (MvPolynomial.isHomogeneous_X k i)) (by decide) hφ =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k) ψ (MvPolynomial.X i)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
          (MvPolynomial.isHomogeneous_X k i)) (by decide) hψ := by
    subst ψ
    rfl
  have hφ : C.sectionProjectiveFieldMap k s (MvPolynomial.X i) ≠ 0 := by
    simpa only [sectionProjectiveFieldMap, MvPolynomial.eval₂Hom_X'] using hi
  have hψ : ((ρ.toRingHom.comp (homogeneousExponentAlgHom a k).toRingHom).comp
      (homogeneousMonomialGradedMap a k).toRingHom) (MvPolynomial.X i) ≠ 0 :=
    hfield ▸ hφ
  exact hleft.trans ((hcharts _ _ hfield hφ hψ).trans hmonomial.symm)

def characterMonomialImageIso
    (hj : DenseRange j)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [IsClosedImmersion (C.sectionProjectiveMap k s hcover)] :
    X≅monomialProjectiveScheme a k := by
  letI : IsDominant j := ⟨hj⟩
  letI : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let q : splitTorus k (Fin n → ℤ) ⟶ monomialProjectiveScheme a k :=
    monomialTorusChart a k i
  letI : IsSchemeTheoreticallyDominant q :=
    monomialTorusChart_isSchemeTheoreticallyDominant a k i
  exact closedImageIsoOfDenseComposite j q
    (C.sectionProjectiveMap k s hcover) (monomialProjectiveEmbedding a k)
    (C.character_sectionProjectiveMap_torus k j a s hvalue hcover i)

theorem characterMonomialImageIso_torus
    (hj : DenseRange j)
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι)
    [IsClosedImmersion (C.sectionProjectiveMap k s hcover)] :
    j≫(C.characterMonomialImageIso k j a s hvalue hj hcover i).hom=
      monomialTorusChart a k i := by
  letI : IsDominant j := ⟨hj⟩
  letI : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let q : splitTorus k (Fin n → ℤ) ⟶ monomialProjectiveScheme a k :=
    monomialTorusChart a k i
  letI : IsSchemeTheoreticallyDominant q :=
    monomialTorusChart_isSchemeTheoreticallyDominant a k i
  exact closedImageIsoOfDenseComposite_torus j q
    (C.sectionProjectiveMap k s hcover) (monomialProjectiveEmbedding a k)
    (C.character_sectionProjectiveMap_torus k j a s hvalue hcover i)

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.characterMonomialImageIso
end
end Source_ToricMonomialImageComparison
-- END ORIGINAL PaperVerification.ToricMonomialImageComparison


-- BEGIN ORIGINAL PaperVerification.ToricInvariantAffineAlgebras
section Source_ToricInvariantAffineAlgebras

-- original header: module

-- original header: public import PaperVerification.ToricCharacterSubrepresentations
-- original header: public import PaperVerification.ToricMonomialAffineCharts
-- original header: public import Mathlib.RingTheory.FiniteType
-- original header: public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

-- original header: @[expose] public section

/-!
# Actual invariant affine coordinate algebras are semigroup algebras

The exponent monoid is recovered from the characters actually contained
in a subalgebra of the Laurent algebra. Algebraic coaction stability
implies equality with its semigroup algebra. Finite type implies finite
generation of that monoid. A common actual fraction field implies that
its differences generate the whole character lattice. Normality, when
available, implies saturation by the monic equation `T^N-χ^(Nm)`.
None of these conclusions is included in the definition of the monoid.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

/-- The characters literally belonging to the given affine algebra. -/
def affineExponentMonoid (A : Subalgebra k (AddMonoidAlgebra k M)) : AddSubmonoid M where
  carrier := {m | single m (1 : k) ∈ A}
  zero_mem' := by
    change single (0 : M) (1 : k) ∈ A
    simpa only [AddMonoidAlgebra.one_def] using A.one_mem
  add_mem' := by
    intro m p hm hp
    change single (m+p) (1 : k) ∈ A
    simpa using A.mul_mem hm hp

@[simp] theorem mem_affineExponentMonoid
    (A : Subalgebra k (AddMonoidAlgebra k M)) (m : M) :
    m ∈ affineExponentMonoid k A ↔ single m (1 : k) ∈ A := Iff.rfl

theorem invariantAffineAlgebra_eq_semigroup
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    A = monoidChartAlgebra k (affineExponentMonoid k A) := by
  apply Subalgebra.toSubmodule_injective
  rw [monoidChartAlgebra_toSubmodule]
  exact stable_eq_characterModule k A.toSubmodule hA

/-- The constructed isomorphism retains the literal character embedding
into the ambient Laurent algebra. -/
def invariantAffineSemigroupEquiv
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    AddMonoidAlgebra k (affineExponentMonoid k A) ≃ₐ[k] A :=
  (monoidChartAlgebraEquiv k (affineExponentMonoid k A)).trans
    (Subalgebra.equivOfEq _ _ (invariantAffineAlgebra_eq_semigroup k A hA).symm)

@[simp] theorem invariantAffineSemigroupEquiv_single
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) (m : affineExponentMonoid k A) (r : k) :
    ((invariantAffineSemigroupEquiv k A hA (single m r) : A) : AddMonoidAlgebra k M) =
      single (m : M) r := by
  change monoidChartMap k (affineExponentMonoid k A) (single m r) = _
  exact monoidChartMap_single k _ m r

theorem affineExponentMonoid_finitelyGenerated
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    AddMonoid.FG (affineExponentMonoid k A) := by
  letI : Algebra.FiniteType k (AddMonoidAlgebra k (affineExponentMonoid k A)) :=
    Algebra.FiniteType.equiv inferInstance (invariantAffineSemigroupEquiv k A hA).symm
  exact AddMonoidAlgebra.fg_of_finiteType (R := k)

theorem exists_finite_affine_exponent_generators
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    ∃ S : Finset M, AddSubmonoid.closure (S : Set M) = affineExponentMonoid k A := by
  letI := affineExponentMonoid_finitelyGenerated k A hA
  exact AddSubmonoid.exists_of_isAddFG _

section Coaction

variable {R : Type*} [CommRing R] [Algebra k R]
    (f : R →ₐ[k] AddMonoidAlgebra k M)
    (δ : R →ₗ[k] AddMonoidAlgebra k M ⊗[k] R)

/-- An actual equivariant comorphism gives stability of its actual range.
The equality involves the Hopf comultiplication over all test algebras. -/
theorem range_isCharacterStable_of_coaction
    (hδ : ∀ r : R,
      Coalgebra.comul (R := k) (f r) =
        TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
          f.toLinearMap (δ r)) :
    IsCharacterStable k f.range.toSubmodule := by
  rintro z ⟨r, rfl⟩
  let fr : R →ₗ[k] f.range := f.rangeRestrict.toLinearMap
  refine ⟨TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
    fr (δ r), ?_⟩
  have hmaps :
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        f.range.toSubmodule.subtype).comp
          (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) fr) =
      TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) f.toLinearMap := by
    ext a b
    rfl
  exact (congrArg (fun g => g (δ r)) hmaps).trans (hδ r).symm

end Coaction

section FractionField

variable (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule)
    (K : Type*) [Field K] [Algebra (AddMonoidAlgebra k M) K]
    [Algebra A K]

/-- In this common-fraction-field interface, the scalar tower refers to
the chosen algebra map A→K, rather than the separate inherited action
of the ambient Laurent algebra on K. -/
local instance affineFractionAlgebraSMul : SMul A K :=
  (inferInstance : Algebra A K).toSMul

variable [IsScalarTower A (AddMonoidAlgebra k M) K]
    [IsFractionRing A K]
    (hinj : Function.Injective (algebraMap (AddMonoidAlgebra k M) K))

include hA hinj in
/-- Every lattice character is a quotient of characters from the actual
affine monoid. This follows from the common fraction field, not from a
generating-lattice premise attached to the affine chart. -/
theorem exists_affine_exponent_difference (m : M) :
    ∃ p ∈ affineExponentMonoid k A, ∃ q ∈ affineExponentMonoid k A, m = p-q := by
  letI : IsDomain A := Function.Injective.isDomain (algebraMap A K)
    (IsFractionRing.injective A K)
  obtain ⟨a,b,hb,hfrac⟩ := IsFractionRing.div_surjective A
    (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))
  have hb0 : (b : AddMonoidAlgebra k M) ≠ 0 := by
    intro h
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact Subtype.ext h
  have hK0 : algebraMap A K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul : single m (1:k) * (b : AddMonoidAlgebra k M) = a := by
    apply hinj
    have hbmap : algebraMap (AddMonoidAlgebra k M) K (b : AddMonoidAlgebra k M) =
        algebraMap A K b :=
      (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K b).symm
    have hamap : algebraMap A K a =
        algebraMap (AddMonoidAlgebra k M) K (a : AddMonoidAlgebra k M) :=
      IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K a
    exact (map_mul (algebraMap (AddMonoidAlgebra k M) K)
      (single m (1:k)) (b : AddMonoidAlgebra k M)).trans
        ((congrArg (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)) * ·)
          hbmap).trans (((div_eq_iff hK0).mp hfrac).symm.trans hamap))
  obtain ⟨q,hq⟩ := Finsupp.support_nonempty_iff.mpr (by
    intro hz
    apply hb0
    exact AddMonoidAlgebra.ext hz)
  have hq0 : (b : AddMonoidAlgebra k M).coeff q ≠ 0 := Finsupp.mem_support_iff.mp hq
  have hqA : q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA b b.property q hq0
  have hp0 : (a : AddMonoidAlgebra k M).coeff (m+q) ≠ 0 := by
    rw [← hmul, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
    exact hq0
  have hpA : m+q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA a a.property (m+q) hp0
  exact ⟨m+q,hpA,q,hqA,by abel⟩

include hA hinj in
theorem affineExponentMonoid_groupClosure :
    AddSubgroup.closure (affineExponentMonoid k A : Set M) = ⊤ := by
  apply eq_top_iff.mpr
  intro m hm
  obtain ⟨p,hp,q,hq,rfl⟩ := exists_affine_exponent_difference k A hA K hinj m
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hp)
    (AddSubgroup.subset_closure hq)

include hinj in
/-- Saturation is forced by integral closedness of the actual affine
coordinate ring in its actual fraction field. -/
theorem affineExponentMonoid_saturated [IsIntegrallyClosed A]
    (m : M) {N : ℕ} (hN : 0<N)
    (hm : N • m ∈ affineExponentMonoid k A) :
    m ∈ affineExponentMonoid k A := by
  let x := algebraMap (AddMonoidAlgebra k M) K (single m (1:k))
  let a : A := ⟨single (N • m) 1, hm⟩
  have hpow : x^N = algebraMap A K a := by
    change (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))^N = _
    rw [← map_pow, IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K]
    simp [a]
  have hx : IsIntegral A (x^N) := by
    rw [hpow]
    exact isIntegral_algebraMap
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hN hx
  have he : (y : AddMonoidAlgebra k M) = single m (1:k) := by
    apply hinj
    exact (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K y).symm.trans hy
  change single m (1:k) ∈ A
  exact he ▸ y.property

end FractionField

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.invariantAffineAlgebra_eq_semigroup
#print axioms PaperVerification.ToricCharacters.affineExponentMonoid_finitelyGenerated
#print axioms PaperVerification.ToricCharacters.affineExponentMonoid_groupClosure
end
end Source_ToricInvariantAffineAlgebras
-- END ORIGINAL PaperVerification.ToricInvariantAffineAlgebras


-- BEGIN ORIGINAL PaperVerification.ToricMonoidCotangent
section Source_ToricMonoidCotangent

-- original header: module

-- original header: public import PaperVerification.ToricPointedMonoids
-- original header: public import PaperVerification.ToricCoordinateDifferentials
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Tower
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

/-!
# Independent actual cotangent vectors of semigroup atoms

At the rational point of a pointed semigroup algebra which kills all
nonconstant characters, the coefficient of an indecomposable exponent
is a genuine derivation. Its universal Kähler functional isolates the
corresponding cotangent vector. Consequently distinct atoms give
linearly independent vectors in the actual cotangent fibre, in every
characteristic.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped TensorProduct BigOperators Classical

variable (k : Type*) [Field k] (S : Type*) [AddCommMonoid S]
    (hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0)

def pointedEvaluationMonoid : Multiplicative S →* k where
  toFun s := if s.toAdd=0 then 1 else 0
  map_one' := by simp
  map_mul' s t := by
    by_cases hs : s.toAdd=0 <;> by_cases ht : t.toAdd=0
    · simp [hs,ht]
    · simp [hs,ht]
    · simp [hs,ht]
    · have hst : s.toAdd+t.toAdd≠0 := fun h => hs (hzero _ _ h).1
      simp [hs,ht,hst]

/-- The actual rational closed-orbit point of a pointed semigroup algebra. -/
def pointedAugmentation : AddMonoidAlgebra k S →ₐ[k] k :=
  AddMonoidAlgebra.lift k k S (pointedEvaluationMonoid k S hzero)

@[simp] theorem pointedAugmentation_single (m : S) (r : k) :
    pointedAugmentation k S hzero (single m r) = if m=0 then r else 0 := by
  by_cases hm : m=0 <;>
    simp [pointedAugmentation,pointedEvaluationMonoid,hm]

def pointedAlgebra : Algebra (AddMonoidAlgebra k S) k :=
  (pointedAugmentation k S hzero).toRingHom.toAlgebra

def pointedScalarTower :
    letI := pointedAlgebra k S hzero
    IsScalarTower k (AddMonoidAlgebra k S) k := by
  letI := pointedAlgebra k S hzero
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((pointedAugmentation k S hzero).commutes r).symm

abbrev PointedCotangentFiber : Type _ :=
  letI := pointedAlgebra k S hzero
  k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]

abbrev pointedCotangentFiber_addCommGroup :
    AddCommGroup (PointedCotangentFiber k S hzero) := by
  letI := pointedAlgebra k S hzero
  exact inferInstanceAs (AddCommGroup (k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]))

abbrev pointedCotangentFiber_module : Module k (PointedCotangentFiber k S hzero) := by
  letI := pointedAlgebra k S hzero
  exact inferInstanceAs (Module k (k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]))

def pointedCotangentVector (m : S) : PointedCotangentFiber k S hzero := by
  letI := pointedAlgebra k S hzero
  exact 1 ⊗ₜ[AddMonoidAlgebra k S] D k (AddMonoidAlgebra k S) (single m 1)

/-- A coefficient at an atom satisfies Leibniz at the actual augmentation. -/
def atomCoefficientDerivation (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) :
    letI := pointedAlgebra k S hzero
    Derivation k (AddMonoidAlgebra k S) k := by
  letI := pointedAlgebra k S hzero
  refine
    { (AddMonoidAlgebra.basis S k).coord p with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · change (1 : AddMonoidAlgebra k S).coeff p=0
    simp [AddMonoidAlgebra.one_def,hp0,Ne.symm hp0]
  · intro f g
    change (f*g).coeff p =
      pointedAugmentation k S hzero f * g.coeff p +
        pointedAugmentation k S hzero g * f.coeff p
    induction f using AddMonoidAlgebra.induction_on with
    | of a =>
        induction g using AddMonoidAlgebra.induction_on with
        | of b =>
            change (single a (1:k)*single b 1).coeff p = _
            by_cases ha : a=0
            · subst a
              simp [hp0,Ne.symm hp0]
            by_cases hb : b=0
            · subst b
              simp [hp0,Ne.symm hp0]
            have hab : a+b≠p := by
              intro hh
              rcases hpatom a b hh with h|h
              · exact ha h
              · exact hb h
            simp [single_mul_single,ha,hb,hab,Ne.symm hab]
        | add g g' hg hg' =>
            simp only [mul_add,map_add,coeff_add,Finsupp.add_apply,hg,hg']
            ring
        | smul r g hg =>
            simp only [mul_smul_comm,coeff_smul,map_smul,Finsupp.smul_apply,smul_eq_mul,hg]
            ring
    | add f f' hf hf' =>
        simp only [add_mul,map_add,coeff_add,Finsupp.add_apply,hf,hf']
        ring
    | smul r f hf =>
        simp only [smul_mul_assoc,coeff_smul,map_smul,Finsupp.smul_apply,smul_eq_mul,hf]
        ring

def atomCotangentCoordinate (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) :
    PointedCotangentFiber k S hzero →ₗ[k] k := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  exact (atomCoefficientDerivation k S hzero p hp0 hpatom).liftKaehlerDifferential.liftBaseChange k

@[simp] theorem atomCotangentCoordinate_vector
    (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) (m : S) :
    atomCotangentCoordinate k S hzero p hp0 hpatom
      (pointedCotangentVector k S hzero m) = if m=p then 1 else 0 := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  change (atomCoefficientDerivation k S hzero p hp0 hpatom).liftKaehlerDifferential.liftBaseChange k
    (1 ⊗ₜ[AddMonoidAlgebra k S] D k (AddMonoidAlgebra k S) (single m 1)) = _
  rw [LinearMap.liftBaseChange_tmul,one_smul,Derivation.liftKaehlerDifferential_comp_D]
  change (single m (1:k)).coeff p = _
  simp only [coeff_single,Finsupp.single_apply]

theorem linearIndependent_pointedCotangentAtoms
    {ι : Type*} (p : ι → S) (hpinj : Function.Injective p)
    (hp0 : ∀ i,p i≠0)
    (hpatom : ∀ i,∀ a b : S,a+b=p i → a=0 ∨ b=0) :
    LinearIndependent k (fun i => pointedCotangentVector k S hzero (p i)) := by
  rw [linearIndependent_iff']
  intro s c h i hi
  have hc := congrArg (atomCotangentCoordinate k S hzero (p i) (hp0 i) (hpatom i)) h
  simpa only [map_sum,map_smul,map_zero,atomCotangentCoordinate_vector,
    hpinj.eq_iff,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',hi,if_pos] using hc

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.linearIndependent_pointedCotangentAtoms
end
end Source_ToricMonoidCotangent
-- END ORIGINAL PaperVerification.ToricMonoidCotangent


-- BEGIN ORIGINAL PaperVerification.ToricSmoothCotangentRank
section Source_ToricSmoothCotangentRank

-- original header: module

-- original header: public import PaperVerification.ToricMonoidCotangent
-- original header: public import PaperVerification.ToricFractionDifferentials
-- original header: public import Mathlib.RingTheory.Smooth.Basic
-- original header: public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
-- original header: public import Mathlib.LinearAlgebra.Dimension.Localization

-- original header: @[expose] public section

/-!
# Smooth cotangent fibres have the actual generic differential rank

Smoothness makes the Kähler module finite projective, hence finite flat.
The existing rank-at-prime theorem then identifies its fibre dimension
with its fraction-field rank. This argument requires no additional
regular-local-ring or normality hypothesis.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open KaehlerDifferential
open scoped TensorProduct Classical

section GenericRank

variable (k R K : Type*) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K] {n : ℕ}
    (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem kaehler_finrank_eq_generic_basis : Module.finrank R Ω[R⁄k] = n := by
  calc
    Module.finrank R Ω[R⁄k] = Module.finrank R Ω[K⁄k] :=
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R)
        (KaehlerDifferential.map k k R K) le_rfl).symm
    _ = Module.finrank K Ω[K⁄k] :=
      (IsFractionRing.finrank_right_eq R K Ω[K⁄k]).symm
    _ = n := by simpa using Module.finrank_eq_card_basis bK

variable [Algebra.Smooth k R] [Algebra R k] [IsScalarTower k R k]

include bK in
/-- The point is specified by the actual algebra structure R→k. -/
theorem smooth_rational_cotangent_finrank :
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = n := by
  let p₀ : PrimeSpectrum k := ⟨⊥,inferInstance⟩
  let p : PrimeSpectrum R := p₀.comap (algebraMap R k)
  have hb := Module.rankAtStalk_baseChange (R := R) (M := Ω[R⁄k]) p₀
  rw [Module.rankAtStalk_eq_finrank_of_free] at hb
  calc
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = Module.rankAtStalk Ω[R⁄k] p := hb
    _ = Module.finrank R Ω[R⁄k] := by
      rw [Module.rankAtStalk_eq]
      exact p.asIdeal.finrank_fiber_eq_finrank
    _ = n := kaehler_finrank_eq_generic_basis k R K bK

end GenericRank

section Pointed

variable (k : Type*) [Field k] (S : Type*) [AddCommMonoid S]
    (hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0)
    [IsDomain (AddMonoidAlgebra k S)] [Algebra.Smooth k (AddMonoidAlgebra k S)]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k S) K]
    [IsScalarTower k (AddMonoidAlgebra k S) K]
    [IsFractionRing (AddMonoidAlgebra k S) K]
    {n : ℕ} (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem pointedCotangentFiber_finrank :
    Module.finrank k (PointedCotangentFiber k S hzero) = n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  exact smooth_rational_cotangent_finrank k (AddMonoidAlgebra k S) K bK

include hzero bK in
theorem pointed_atoms_card_le {ι : Type*} [Fintype ι]
    (p : ι → S) (hpinj : Function.Injective p)
    (hp0 : ∀ i,p i≠0)
    (hpatom : ∀ i,∀ a b : S,a+b=p i → a=0 ∨ b=0) :
    Fintype.card ι ≤ n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  have hli := linearIndependent_pointedCotangentAtoms k S hzero p hpinj hp0 hpatom
  have hcard := hli.fintype_card_le_finrank
  rw [pointedCotangentFiber_finrank k S hzero K bK] at hcard
  exact hcard

end Pointed

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smooth_rational_cotangent_finrank
#print axioms PaperVerification.ToricCharacters.pointed_atoms_card_le
end
end Source_ToricSmoothCotangentRank
-- END ORIGINAL PaperVerification.ToricSmoothCotangentRank


