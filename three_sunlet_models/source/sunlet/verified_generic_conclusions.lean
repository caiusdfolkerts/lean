module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import sunlet.normalization
public import sunlet.verified_generic_open

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_GENERIC_CONCLUSIONS_IMPORTS_READY"



section Stage_NormalizedGenericParameters



/-! The faithful independent parameter-field presentation of the literal normalized model, separated from the generic degree calculation. -/

noncomputable section


namespace Sunlet.IteratedRationalField

variable {k I J : Type*} [Field k]

abbrev Rational (k I : Type*) [Field k] := FractionRing (MvPolynomial I k)

def coordinateVariable (i : I) : Rational k I :=
  algebraMap (MvPolynomial I k) (Rational k I) (MvPolynomial.X i)

theorem independent : AlgebraicIndependent k (coordinateVariable (k := k) (I := I)) := by
  exact (MvPolynomial.algebraicIndependent_X (R := k) (σ := I)).map'
    (f := IsScalarTower.toAlgHom k (MvPolynomial I k) (Rational k I))
    (IsFractionRing.injective (MvPolynomial I k) (Rational k I))

theorem generated : IntermediateField.adjoin k (Set.range (coordinateVariable (k := k) (I := I))) = ⊤ := by
  apply top_unique
  intro x _
  let F := IntermediateField.adjoin k (Set.range (coordinateVariable (k := k) (I := I)))
  have hp : ∀ p : MvPolynomial I k, algebraMap (MvPolynomial I k) (Rational k I) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact F.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using F.add_mem hp hq
    | mul_X p i hp =>
        simpa only [map_mul, coordinateVariable] using
          F.mul_mem hp (IntermediateField.subset_adjoin k _ ⟨i, rfl⟩)
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial I k) x
  exact F.div_mem (hp p) (hp q)

abbrev Iterated := Rational (Rational k I) J

def combined : J ⊕ I → Iterated (k := k) (I := I) (J := J) :=
  Sum.elim (coordinateVariable (k := Rational k I))
    (algebraMap (Rational k I) (Iterated (k := k) (I := I) (J := J)) ∘ coordinateVariable (k := k))

theorem combined_independent : AlgebraicIndependent k (combined (k := k) (I := I) (J := J)) :=
  (independent (k := k) (I := I)).sumElim_comp (independent (k := Rational k I) (I := J))

theorem combined_generated :
    IntermediateField.adjoin k (Set.range (combined (k := k) (I := I) (J := J))) = ⊤ := by
  let E := Rational k I
  let D := Iterated (k := k) (I := I) (J := J)
  let F := IntermediateField.adjoin k (Set.range (combined (k := k) (I := I) (J := J)))
  have hx : ∀ i : I, algebraMap E D (coordinateVariable (k := k) i) ∈ F := by
    intro i
    exact IntermediateField.subset_adjoin k _ ⟨Sum.inr i, rfl⟩
  have he : ∀ e : E, algebraMap E D e ∈ F := by
    intro e
    have hp : ∀ p : MvPolynomial I k,
        algebraMap E D (algebraMap (MvPolynomial I k) E p) ∈ F := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
          change algebraMap E D (algebraMap k E a) ∈ F
          rw [← IsScalarTower.algebraMap_apply k E D]
          exact F.algebraMap_mem a
      | add p q hp hq => simpa only [map_add] using F.add_mem hp hq
      | mul_X p i hp => simpa only [map_mul, coordinateVariable] using F.mul_mem hp (hx i)
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial I k) e
    simpa only [map_div₀] using F.div_mem (hp p) (hp q)
  have hz : ∀ j : J, coordinateVariable (k := E) j ∈ F := by
    intro j
    exact IntermediateField.subset_adjoin k _ ⟨Sum.inl j, rfl⟩
  have hp : ∀ p : MvPolynomial J E, algebraMap (MvPolynomial J E) D p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact he a
    | add p q hp hq => simpa only [map_add] using F.add_mem hp hq
    | mul_X p j hp => simpa only [map_mul, coordinateVariable] using F.mul_mem hp (hz j)
  apply top_unique
  intro x _
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial J E) x
  exact F.div_mem (hp p) (hp q)

/-- The full parameter field is a rational-function field on exactly the
union of the two displayed sets of variables. -/
def combinedEquiv : Rational k (J ⊕ I) ≃ₐ[k] Iterated (k := k) (I := I) (J := J) :=
  (combined_independent (k := k) (I := I) (J := J)).aevalEquivField.trans
    ((IntermediateField.equivOfEq (combined_generated (k := k) (I := I) (J := J))).trans
      IntermediateField.topEquiv)

@[simp] theorem combinedEquiv_variable (j : J ⊕ I) :
    combinedEquiv (k := k) (I := I) (J := J) (coordinateVariable (k := k) j) = combined j := by
  change ((combined_independent (k := k) (I := I) (J := J)).aevalEquivField
    (algebraMap (MvPolynomial (J ⊕ I) k) _ (MvPolynomial.X j))).val = _
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]

end Sunlet.IteratedRationalField


namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

abbrev OffDiagonalField := FunctionField (k := k) (ι := L.NonidentityColor) o
abbrev NormalizedSourceField :=
  RationalBaseChange.ExtendedField (E := L.OffDiagonalField (k := k) o) (J := Ω)

instance normalizedSourceField_charZero : CharZero (L.NormalizedSourceField (k := k) o) :=
  charZero_of_injective_algebraMap (algebraMap k (L.NormalizedSourceField (k := k) o)).injective

def normalizedSourceEmbedding : L.OffDiagonalField (k := k) o →ₐ[k]
    L.NormalizedSourceField (k := k) o := IsScalarTower.toAlgHom k _ _

def genericNormalizedParameters :
    Normalization.Parameters (L.NormalizedSourceField (k := k) o) ι Ω L.identity o where
  z := RationalBaseChange.diagonal
  k := embeddedTorus o (L.normalizedSourceEmbedding (k := k) o) false
  l := embeddedTorus o (L.normalizedSourceEmbedding (k := k) o) true
  u := embeddedCoefficient o (L.normalizedSourceEmbedding (k := k) o) false
  v := embeddedCoefficient o (L.normalizedSourceEmbedding (k := k) o) true
  k_base := embeddedTorus_base o _ false
  l_base := embeddedTorus_base o _ true

def normalizedCoordinateIndex : Ω ⊕ (L.NonidentityColor × Ω) ≃ ι × Ω where
  toFun
    | .inl x => (L.identity, x)
    | .inr ax => (ax.1.val, ax.2)
  invFun ax := if ha : ax.1 = L.identity then .inl ax.2 else .inr (⟨ax.1, ha⟩, ax.2)
  left_inv := by
    rintro (x | ⟨a, x⟩)
    · simp
    · simp [a.property]
  right_inv := by
    rintro ⟨a, x⟩
    by_cases ha : a = L.identity
    · simp [ha]
    · simp [ha]

abbrev NormalizedImageField := IntermediateField.adjoin k
  (Set.range (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o)))

/-- Every independent parameter of the normalized source is retained;
the iterated presentation has no algebraic relations among those variables. -/
def normalizedSourceEquiv :
    FractionRing (MvPolynomial (Ω ⊕ ToricPairAlgebra.Index (ι := L.NonidentityColor) o) k) ≃ₐ[k]
      L.NormalizedSourceField (k := k) o :=
  IteratedRationalField.combinedEquiv

end Sunlet.NormalizedLatinSystem
end
end Stage_NormalizedGenericParameters

#check "SUNLET_NormalizedGenericParameters_READY"

section Stage_GenericConclusions




/-! Generic identifiability, normalized degree, and the actual Galois action.

The checkpoint source map records the original component files; this module
is the maintained implementation, including the explicit interchange result.
Compilation, mathematical coverage, and axiom auditing are separate gates. -/

noncomputable section

section ConclusionSource_LatinGenericConclusions

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω) (hm : 5 ≤ Fintype.card Ω)

def genericWitness : SparseWitness (k := k) o L.nonidentityPerm :=
  Classical.choice (L.exists_sparseWitness (k := k) o hm)

theorem nonidentity_moves_base (a : L.NonidentityColor) : L.nonidentityPerm a o ≠ o :=
  L.derangement a.val a.property o

include hm in
theorem normalized_tangent_card_gt_two :
    2 < Fintype.card (NormalizedVariations.Index L.NonidentityColor Ω o) := by
  have hcard : Fintype.card {x : Ω // x ≠ o} = Fintype.card Ω - 1 := by
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun x : Ω => x = o)
  simp only [NormalizedVariations.Index, Fintype.card_sum, hcard]
  omega

theorem loop_colors_compatible (a : L.NonidentityColor) :
    L.nonidentityPerm a = (L.loopAt o).left ((L.loopColorEquiv o).symm a).val := by
  ext x
  simpa only [Equiv.apply_symm_apply] using
    (L.loopColorEquiv_permutation o ((L.loopColorEquiv o).symm a) x).symm

include hm in
/-- Exact degree of the actual off-diagonal sum-coordinate field. -/
theorem offDiagonal_generic_degree [IsAlgClosed k] :
    Module.finrank
      (JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm))
      (FunctionField (k := k) (ι := L.NonidentityColor) o) =
        2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 := by
  exact (L.loopAt o).coordinateField_finrank (k := k) (L.loopColorEquiv o).symm
    L.nonidentityPerm (L.loop_colors_compatible o) (L.genericWitness (k := k) o hm)
    (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm)

include hm in
/-- The field extension of the actual sum coordinates is Galois. -/
theorem offDiagonal_isGalois [IsAlgClosed k] :
    IsGalois
      (JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm))
      (FunctionField (k := k) (ι := L.NonidentityColor) o) := by
  exact (L.loopAt o).coordinateField_isGalois (k := k) (L.loopColorEquiv o).symm
    L.nonidentityPerm (L.loop_colors_compatible o) (L.genericWitness (k := k) o hm)
    (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm)

/-- The semidirect product consists of actual characters of the universal
loop abelianization and acts by the displayed rescalings and interchange. -/
def offDiagonal_galoisEquiv [IsAlgClosed k] :
    (L.loopAt o).CharacterWreath (k := k) ≃*
      (FunctionField (k := k) (ι := L.NonidentityColor) o ≃ₐ[
        JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm)]
          FunctionField (k := k) (ι := L.NonidentityColor) o) :=
  (L.loopAt o).coordinateField_galoisEquiv (k := k) (L.loopColorEquiv o).symm
    L.nonidentityPerm (L.loop_colors_compatible o) (L.genericWitness (k := k) o hm)
    (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm)

include hm in
/-- Literal generic uniqueness, including existence and all boundary
points of the toric closure. The principal open is nonempty and dense. -/
theorem generic_unique_unordered_decomposition [IsAlgClosed k] :
    ∃ P : MvPolynomial (L.NonidentityColor × Ω) k,
      MvPolynomial.aeval (genericCoordinates (k := k) o L.nonidentityPerm) P ≠ 0 ∧
      (principalOpen (k := k) o L.nonidentityPerm P).Nonempty ∧
      PolynomialClosureProduct.closure (principalOpen (k := k) o L.nonidentityPerm P) =
        secantClosure (k := k) o L.nonidentityPerm ∧
      ∀ z ∈ principalOpen (k := k) o L.nonidentityPerm P,
        ∃ x ∈ toricClosure (k := k) o L.nonidentityPerm,
          ∃ y ∈ toricClosure (k := k) o L.nonidentityPerm,
            x + y = z ∧
            ∀ x' ∈ toricClosure (k := k) o L.nonidentityPerm,
              ∀ y' ∈ toricClosure (k := k) o L.nonidentityPerm,
                x' + y' = z → (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  let W := L.genericWitness (k := k) o hm
  obtain ⟨a, _, _, _, _⟩ := W.Atwo
  let p : L.NonidentityColor × Ω := (a, o)
  obtain ⟨D⟩ := exists_pivotRecovery_of_witness (k := k) o L.nonidentityPerm W
    (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm) p
  refine ⟨D.openPolynomial, D.openPolynomial_generic_ne, ?_,
    closure_principalOpen o L.nonidentityPerm D.openPolynomial D.openPolynomial_generic_ne, ?_⟩
  · obtain ⟨U, h, hb, hP⟩ := D.nonempty_open_parameter_sums
    let x := toricPoint L.nonidentityPerm (U false) (h false)
    let y := toricPoint L.nonidentityPerm (U true) (h true)
    have hx : x ∈ toricClosure (k := k) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm ⟨U false, h false, hb false, rfl⟩
    have hy : y ∈ toricClosure (k := k) o L.nonidentityPerm :=
      parameterImage_subset_toricClosure o L.nonidentityPerm ⟨U true, h true, hb true, rfl⟩
    refine ⟨x + y, ?_, hP⟩
    intro Q hQ
    exact hQ (x + y) ⟨x, hx, y, hy, rfl⟩
  · intro z hz
    have hnot : genericDifference (k := k) o L.nonidentityPerm p ∉
        JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm) :=
      (L.loopAt o).difference_not_mem_coordinateField (k := k)
        (L.loopColorEquiv o).symm L.nonidentityPerm (L.loop_colors_compatible o) p
    obtain ⟨x, hx, y, hy, hs⟩ := D.exists_pair_on_open hnot z hz.1 hz.2
    refine ⟨x, hx, y, hy, hs, ?_⟩
    intro x' hx' y' hy' hs'
    exact D.unique_unordered_on_open z x y x' y' hz.2 hx hy hx' hy' hs hs'

end Sunlet.NormalizedLatinSystem

namespace Sunlet.LoopData

variable {Ω : Type*} (L : LoopData Ω)

def asLatin : NormalizedLatinSystem Ω Ω where
  perm := L.left
  identity := L.identity
  normalized := L.left_identity
  column_bijective := L.column_bijective

theorem ext_data {A B : LoopData Ω} (hi : A.identity = B.identity)
    (hl : A.left = B.left) : A = B := by
  cases A
  cases B
  cases hi
  cases hl
  rfl

@[simp] theorem loopAt_asLatin : L.asLatin.loopAt L.identity = L := by
  apply LoopData.ext_data
  · rfl
  · funext x
    have he : (Equiv.ofBijective (fun a => L.left a L.identity)
        (L.column_bijective L.identity)).symm x = x := by
      apply (Equiv.ofBijective (fun a => L.left a L.identity)
        (L.column_bijective L.identity)).injective
      rw [Equiv.apply_symm_apply]
      exact (L.right_identity x).symm
    change L.left ((Equiv.ofBijective (fun a => L.left a L.identity)
      (L.column_bijective L.identity)).symm x) = L.left x
    rw [he]

end Sunlet.LoopData

end ConclusionSource_LatinGenericConclusions


section ConclusionSource_NormalizedFunctionField

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Exact equality of the actual displayed coordinate maps. -/
theorem generic_normalized_coordinates :
    Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) ∘
        L.normalizedCoordinateIndex =
      RationalBaseChange.coordinates (genericCoordinates (k := k) o L.nonidentityPerm)
        (fun ax : L.NonidentityColor × Ω => L.nonidentityPerm ax.1 ax.2) := by
  funext j
  rcases j with x | ⟨a, x⟩
  · simp [Function.comp_apply, normalizedCoordinateIndex, Normalization.parameterMap,
      Normalization.coordinate, genericNormalizedParameters, RationalBaseChange.coordinates]
  · have he := congrFun (embedded_sum o
      (L.normalizedSourceEmbedding (k := k) o) L.nonidentityPerm) (a, x)
    simp only [normalizedCoordinateIndex, Function.comp_apply, Equiv.coe_fn_mk,
      Normalization.parameterMap, Normalization.coordinate, dite_eq_right a.property,
      genericNormalizedParameters, RationalBaseChange.coordinates]
    change RationalBaseChange.diagonal (L.perm a.val x) * _ =
      RationalBaseChange.diagonal (L.nonidentityPerm a x) * _
    congr 1
    simpa only [toricPoint, ToricDifferential.coordinate, ToricDifferential.ratio,
      Pi.add_apply, div_eq_mul_inv, mul_assoc, Units.val_inv_eq_inv_val,
      normalizedSourceEmbedding, IsScalarTower.toAlgHom_apply, nonidentityPerm] using he

theorem normalizedImageField_eq :
    L.NormalizedImageField (k := k) o =
      RationalBaseChange.ImageField (k := k)
        (genericCoordinates (k := k) o L.nonidentityPerm)
        (fun ax : L.NonidentityColor × Ω => L.nonidentityPerm ax.1 ax.2) := by
  unfold NormalizedImageField RationalBaseChange.ImageField
  congr 1
  rw [← L.generic_normalized_coordinates (k := k) o]
  exact (L.normalizedCoordinateIndex.surjective.range_comp _).symm

/-- The generic degree is computed for the literal normalized map (3). -/
theorem normalized_generic_degree [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    Module.finrank (L.NormalizedImageField (k := k) o)
      (L.NormalizedSourceField (k := k) o) =
        2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 := by
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm)
  let E := L.OffDiagonalField (k := k) o
  letI : Module.Finite F E :=
    ((L.loopAt o).coordinateField_finite_separable L.nonidentityPerm
      (L.genericWitness (k := k) o hm) (L.nonidentity_moves_base o)).1
  rw [L.normalizedImageField_eq (k := k) o, RationalBaseChange.finrank_eq]
  exact L.offDiagonal_generic_degree (k := k) o hm

end Sunlet.NormalizedLatinSystem

end ConclusionSource_NormalizedFunctionField

section ConclusionSource_NormalizedGalois

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

def normalizedWreathAutomorphism (d : (L.loopAt o).CharacterWreath (k := k)) :
    L.NormalizedSourceField (k := k) o ≃ₐ[k] L.NormalizedSourceField (k := k) o :=
  RationalBaseChange.extendAutomorphism (E := L.OffDiagonalField (k := k) o) (J := Ω)
    ((L.loopAt o).wreathAutomorphism (L.loopColorEquiv o).symm d)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem normalizedWreathAutomorphism_coordinates
    (d : (L.loopAt o).CharacterWreath (k := k)) (i : ι × Ω) :
    L.normalizedWreathAutomorphism o d
      (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) i) =
      Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o) i := by
  let j := L.normalizedCoordinateIndex.symm i
  have hcoord := congrFun (L.generic_normalized_coordinates (k := k) o) j
  have he := RationalBaseChange.extendAutomorphism_coordinates
    (genericCoordinates (k := k) o L.nonidentityPerm)
    (fun ax : L.NonidentityColor × Ω => L.nonidentityPerm ax.1 ax.2)
    ((L.loopAt o).wreathAutomorphism (L.loopColorEquiv o).symm d)
    ((L.loopAt o).wreathAutomorphism_coordinates (L.loopColorEquiv o).symm
      L.nonidentityPerm (L.loop_colors_compatible o) d) j
  simp only [j, Function.comp_apply, Equiv.apply_symm_apply] at hcoord
  exact (congrArg (L.normalizedWreathAutomorphism o d) hcoord).trans
    (he.trans hcoord.symm)

def normalizedWreathHom : (L.loopAt o).CharacterWreath (k := k) →*
    (L.NormalizedSourceField (k := k) o ≃ₐ[L.NormalizedImageField (k := k) o]
      L.NormalizedSourceField (k := k) o) where
  toFun d := GeneratedFieldActions.overGenerated
    (Normalization.parameterMap L.perm (L.genericNormalizedParameters (k := k) o))
    (L.normalizedWreathAutomorphism o d)
    (L.normalizedWreathAutomorphism_coordinates o d)
  map_one' := by
    ext x
    change RationalBaseChange.extendAutomorphism (J := Ω)
      ((L.loopAt o).wreathAutomorphism (L.loopColorEquiv o).symm 1) x = x
    rw [(L.loopAt o).wreathAutomorphism_one]
    exact congrArg (fun σ : L.NormalizedSourceField (k := k) o ≃ₐ[k]
      L.NormalizedSourceField (k := k) o => σ x)
      (RationalBaseChange.extendHom (k := k) (E := L.OffDiagonalField (k := k) o)
        (J := Ω)).map_one
  map_mul' d d' := by
    ext x
    change RationalBaseChange.extendAutomorphism (J := Ω)
      ((L.loopAt o).wreathAutomorphism (L.loopColorEquiv o).symm (d * d')) x = _
    rw [(L.loopAt o).wreathAutomorphism_mul]
    exact congrArg (fun σ : L.NormalizedSourceField (k := k) o ≃ₐ[k]
      L.NormalizedSourceField (k := k) o => σ x)
      ((RationalBaseChange.extendHom (k := k) (E := L.OffDiagonalField (k := k) o)
        (J := Ω)).map_mul _ _)

@[simp] theorem normalizedWreathHom_apply
    (d : (L.loopAt o).CharacterWreath (k := k))
    (x : L.NormalizedSourceField (k := k) o) :
    L.normalizedWreathHom o d x = L.normalizedWreathAutomorphism o d x := rfl

theorem normalizedWreathHom_injective (hm : 5 ≤ Fintype.card Ω) :
    Function.Injective (L.normalizedWreathHom (k := k) o) := by
  intro d d' he
  obtain ⟨a, _, _, _, _⟩ := (L.genericWitness (k := k) o hm).Atwo
  apply (L.loopAt o).wreathAutomorphism_injective (L.loopColorEquiv o).symm
    L.nonidentityPerm (L.loop_colors_compatible o) a
  apply RationalBaseChange.extendAutomorphism_injective (J := Ω)
  ext x
  exact congrArg (fun σ : L.NormalizedSourceField (k := k) o ≃ₐ[
      L.NormalizedImageField (k := k) o] L.NormalizedSourceField (k := k) o => σ x) he

/-- Interchange is the actual automorphism swapping the two coefficient
and normalized torus families and retaining every diagonal variable. -/
def normalizedInterchange :
    L.NormalizedSourceField (k := k) o ≃ₐ[L.NormalizedImageField (k := k) o]
      L.NormalizedSourceField (k := k) o :=
  L.normalizedWreathHom o (SemidirectProduct.inr (Equiv.swap false true))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
@[simp] theorem normalizedInterchange_diagonal (x : Ω) :
    L.normalizedInterchange (k := k) o
      (RationalBaseChange.diagonal (E := L.OffDiagonalField (k := k) o) x) =
      RationalBaseChange.diagonal (E := L.OffDiagonalField (k := k) o) x := by
  rw [normalizedInterchange, normalizedWreathHom_apply]
  exact RationalBaseChange.extendAutomorphism_diagonal
    (E := L.OffDiagonalField (k := k) o)
    ((L.loopAt o).wreathAutomorphism (L.loopColorEquiv o).symm
      (SemidirectProduct.inr (Equiv.swap false true))) x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
@[simp] theorem normalizedInterchange_variable (b : Bool)
    (j : NormalizedVariations.Index L.NonidentityColor Ω o) :
    L.normalizedInterchange (k := k) o
      (algebraMap (L.OffDiagonalField (k := k) o) (L.NormalizedSourceField (k := k) o)
        (genericVariable o (b, j))) =
      algebraMap (L.OffDiagonalField (k := k) o) (L.NormalizedSourceField (k := k) o)
        (genericVariable o (!b, j)) := by
  rw [normalizedInterchange, normalizedWreathHom_apply, normalizedWreathAutomorphism]
  erw [RationalBaseChange.extendAutomorphism_constant, LoopData.wreathAutomorphism_variable]
  cases b <;> cases j <;> simp [LoopData.characterWeight] <;> rfl

theorem normalizedInterchange_ne_one (hm : 5 ≤ Fintype.card Ω) :
    L.normalizedInterchange (k := k) o ≠ 1 := by
  intro he
  have hd : (SemidirectProduct.inr (Equiv.swap false true) :
      (L.loopAt o).CharacterWreath (k := k)) = 1 :=
    L.normalizedWreathHom_injective o hm (he.trans (L.normalizedWreathHom o).map_one.symm)
  have hp := congrArg (fun d : (L.loopAt o).CharacterWreath (k := k) => d.right) hd
  have hb := congrArg (fun p : Equiv.Perm Bool => p false) hp
  simpa using hb

theorem normalizedSource_finite [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    Module.Finite (L.NormalizedImageField (k := k) o) (L.NormalizedSourceField (k := k) o) := by
  apply Module.finite_of_finrank_pos
  rw [L.normalized_generic_degree o hm]
  have hc : 0 < Nat.card (L.loopAt o).AbelianGroup := Nat.card_pos
  exact Nat.mul_pos (by decide) (pow_pos hc 2)

/-- Galoisness is derived from the explicit independent automorphisms
and the previously proved degree, not supplied as an assumption. -/
theorem normalized_isGalois [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    IsGalois (L.NormalizedImageField (k := k) o) (L.NormalizedSourceField (k := k) o) := by
  let E := L.NormalizedSourceField (k := k) o
  let F := L.NormalizedImageField (k := k) o
  letI : Module.Finite F E := L.normalizedSource_finite o hm
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [L.normalized_generic_degree o hm, ← (L.loopAt o).characterWreath_card (k := k)]
    exact Nat.card_le_card_of_injective (L.normalizedWreathHom o)
      (L.normalizedWreathHom_injective o hm)

theorem normalizedWreathHom_bijective [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    Function.Bijective (L.normalizedWreathHom (k := k) o) := by
  let E := L.NormalizedSourceField (k := k) o
  let F := L.NormalizedImageField (k := k) o
  letI : Module.Finite F E := L.normalizedSource_finite o hm
  letI : IsGalois F E := L.normalized_isGalois o hm
  letI : Fintype ((L.loopAt o).CharacterWreath (k := k)) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨L.normalizedWreathHom_injective o hm, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank, L.normalized_generic_degree o hm,
    (L.loopAt o).characterWreath_card]

/-- The exact character-wreath-product group in Theorem 4.2 for the
literal normalized map with all diagonal coordinates included. -/
def normalizedGaloisEquiv [IsAlgClosed k] (hm : 5 ≤ Fintype.card Ω) :
    (L.loopAt o).CharacterWreath (k := k) ≃*
      (L.NormalizedSourceField (k := k) o ≃ₐ[L.NormalizedImageField (k := k) o]
        L.NormalizedSourceField (k := k) o) :=
  MulEquiv.ofBijective (L.normalizedWreathHom o) (L.normalizedWreathHom_bijective o hm)

end Sunlet.NormalizedLatinSystem

end ConclusionSource_NormalizedGalois

section ConclusionSource_PrimeNonassociativeDegree

namespace Sunlet.LoopData

variable {k Ω : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype Ω] [DecidableEq Ω] (L : LoopData Ω)

/-- Exact generic degree two. The only field automorphisms over the
actual image field are the identity and interchange of the summands. -/
theorem paper_corollary_5_1_degree (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    Module.finrank (L.asLatin.NormalizedImageField (k := k) L.identity)
      (L.asLatin.NormalizedSourceField (k := k) L.identity) = 2 := by
  rw [L.asLatin.normalized_generic_degree L.identity hm,L.loopAt_asLatin]
  have hc : Nat.card L.AbelianGroup = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact L.abelianGroup_card_eq_one_of_prime_nonassociative hprime hnonassoc
  simp only [hc, one_pow, mul_one]

theorem paper_corollary_5_1_galois (hm : 5 ≤ Fintype.card Ω) :
    IsGalois (L.asLatin.NormalizedImageField (k := k) L.identity)
      (L.asLatin.NormalizedSourceField (k := k) L.identity) :=
  L.asLatin.normalized_isGalois L.identity hm

theorem paper_corollary_5_1_two_automorphisms (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    Nat.card (L.asLatin.NormalizedSourceField (k := k) L.identity ≃ₐ[
      L.asLatin.NormalizedImageField (k := k) L.identity]
        L.asLatin.NormalizedSourceField (k := k) L.identity) = 2 := by
  letI := L.asLatin.normalizedSource_finite (k := k) L.identity hm
  letI := L.paper_corollary_5_1_galois (k := k) hm
  rw [IsGalois.card_aut_eq_finrank]
  exact L.paper_corollary_5_1_degree hm hprime hnonassoc

/-- The two automorphisms are identified explicitly: every ambiguity of
the function field is either the identity or the literal interchange of
the two normalized parameter families. -/
theorem paper_corollary_5_1_automorphisms (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative)
    (σ : L.asLatin.NormalizedSourceField (k := k) L.identity ≃ₐ[
      L.asLatin.NormalizedImageField (k := k) L.identity]
        L.asLatin.NormalizedSourceField (k := k) L.identity) :
    σ = 1 ∨ σ = L.asLatin.normalizedInterchange L.identity := by
  classical
  let E := L.asLatin.NormalizedSourceField (k := k) L.identity
  let F := L.asLatin.NormalizedImageField (k := k) L.identity
  letI := L.asLatin.normalizedSource_finite (k := k) L.identity hm
  letI : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      L.paper_corollary_5_1_two_automorphisms (k := k) hm hprime hnonassoc
  have hne : (1 : E ≃ₐ[F] E) ≠ L.asLatin.normalizedInterchange L.identity :=
    (L.asLatin.normalizedInterchange_ne_one (k := k) L.identity hm).symm
  have hu : ({1, L.asLatin.normalizedInterchange L.identity} : Finset (E ≃ₐ[F] E)) =
      Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [Finset.card_pair_eq_two_iff.mpr hne, hcard]
  have hmem : σ ∈ ({1, L.asLatin.normalizedInterchange L.identity} : Finset (E ≃ₐ[F] E)) := by
    rw [hu]
    exact Finset.mem_univ σ
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

end Sunlet.LoopData

end ConclusionSource_PrimeNonassociativeDegree

section ConclusionSource_SecantFixedField

namespace Sunlet.ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (o : Ω) (π : ι → Equiv.Perm Ω)

abbrev pairPointField : IntermediateField k (FunctionField (k := k) (ι := ι) o) :=
  IntermediateField.adjoin k (Set.range (fun bi : Bool × (ι × Ω) =>
    genericPoint (k := k) o π bi.1 bi.2))

theorem sumField_le_pairPointField :
    JacobianFinite.generatedField (genericCoordinates (k := k) o π) ≤ pairPointField o π := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (pairPointField (k := k) o π).add_mem
    (IntermediateField.subset_adjoin k _ ⟨(false, i), rfl⟩)
    (IntermediateField.subset_adjoin k _ ⟨(true, i), rfl⟩)

theorem algHom_eq_on_pairPointField {A : Type*} [Field A] [Algebra k A]
    (f g : FunctionField (k := k) (ι := ι) o →ₐ[k] A)
    (h : ∀ b i, f (genericPoint (k := k) o π b i) = g (genericPoint o π b i))
    (x : FunctionField (k := k) (ι := ι) o) (hx : x ∈ pairPointField (k := k) o π) :
    f x = g x := by
  refine IntermediateField.adjoin_induction k (motive := fun x _ => f x = g x)
    ?_ ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨b, i⟩, rfl⟩
    exact h b i
  · intro c
    rw [f.commutes, g.commutes]
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro x _ hx
    rw [map_inv₀, map_inv₀, hx]
  · intro x y _ _ hx hy
    rw [map_mul, map_mul, hx, hy]

end Sunlet.ToricPairAlgebra

namespace Sunlet.NormalizedLatinSystem

open ToricPairAlgebra

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

def swapParameterField : FunctionField (k := k) (ι := L.NonidentityColor) o ≃ₐ[k]
    FunctionField (k := k) (ι := L.NonidentityColor) o :=
  (L.loopAt o).permutationAutomorphism (Equiv.swap false true)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem swapParameterField_point (b : Bool) (i : L.NonidentityColor × Ω) :
    L.swapParameterField (k := k) o (genericPoint (k := k) o L.nonidentityPerm b i) =
      genericPoint (k := k) o L.nonidentityPerm (!b) i := by
  have h := congrFun ((L.loopAt o).permutationAutomorphism_point (k := k)
    L.nonidentityPerm (Equiv.swap false true) b) i
  cases b <;> simpa only [swapParameterField, loopAt, Bool.not_false, Bool.not_true,
    Equiv.swap_apply_left, Equiv.swap_apply_right] using h

/-- This is the fixed-field identification needed for rationality over
ℚ. Neither algebraic closedness nor a descent assertion is a hypothesis. -/
theorem pairField_fixed_iff (hm : 5 ≤ Fintype.card Ω)
    (x : FunctionField (k := k) (ι := L.NonidentityColor) o)
    (hx : x ∈ pairPointField (k := k) o L.nonidentityPerm) :
    L.swapParameterField o x = x ↔
      x ∈ JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm) := by
  let E := FunctionField (k := k) (ι := L.NonidentityColor) o
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o L.nonidentityPerm)
  let A := AlgebraicClosure E
  let W := L.genericWitness (k := k) o hm
  letI : Module.Finite F E :=
    ((L.loopAt o).coordinateField_finite_separable L.nonidentityPerm W
      (L.nonidentity_moves_base o)).1
  constructor
  · intro hfix
    have hfixed : ∀ ψ : E →ₐ[F] A, ψ x = algebraMap E A x := by
      intro ψ
      let φ : E →ₐ[k] A := IsScalarTower.toAlgHom k E A
      have hc : ∀ i, algebraMap E A (genericCoordinates (k := k) o L.nonidentityPerm i) =
          (ψ.restrictScalars k) (genericCoordinates (k := k) o L.nonidentityPerm i) := by
        intro i
        let q : F := ⟨genericCoordinates (k := k) o L.nonidentityPerm i,
          JacobianFinite.coordinate_mem_generatedField _ i⟩
        exact (ψ.commutes q).symm
      have hu := unordered_under_embedding o L.nonidentityPerm W
        (L.nonidentity_moves_base o) (L.normalized_tangent_card_gt_two o hm)
        (ψ.restrictScalars k) hc
      rcases hu with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact algHom_eq_on_pairPointField o L.nonidentityPerm (ψ.restrictScalars k) φ
          (fun b i => by cases b; exact congrFun h0 i; exact congrFun h1 i) x hx
      · have hh := algHom_eq_on_pairPointField o L.nonidentityPerm (ψ.restrictScalars k)
          (φ.comp (L.swapParameterField o).toAlgHom) (fun b i => by
            change _ = φ (L.swapParameterField o (genericPoint (k := k) o L.nonidentityPerm b i))
            rw [L.swapParameterField_point]
            cases b
            · exact congrFun h0 i
            · exact congrFun h1 i) x hx
        change ψ x = algebraMap E A (L.swapParameterField o x) at hh
        rw [hfix] at hh
        exact hh
    obtain ⟨a, ha⟩ := EmbeddingFixedField.mem_range_of_embeddings x hfixed
    exact ha ▸ a.property
  · intro hxF
    exact GeneratedFieldActions.fixes_adjoin
      (genericCoordinates (k := k) o L.nonidentityPerm) (L.swapParameterField o)
      ((L.loopAt o).permutationAutomorphism_coordinates L.nonidentityPerm (Equiv.swap false true))
      ⟨x, hxF⟩

end Sunlet.NormalizedLatinSystem

end ConclusionSource_SecantFixedField

end
end Stage_GenericConclusions

#check "SUNLET_GenericConclusions_READY"

section Stage_LoopWreathPresentation



/-!
# The character group in the paper's stated presentation

The main construction acts by functions on loop elements satisfying the
character equations. The proved universal property identifies these
functions with homomorphisms from the literal abelianization. This module
transports the interchange action as well, giving the exact semidirect
product written in Theorem 4.2.
-/

noncomputable section

namespace Sunlet.LoopData

variable {Ω M k : Type*} (L : LoopData Ω) [CommGroup M]

/-- Interchange acts on two actual homomorphisms from the universal
abelian group by inverse precomposition on the two-element index. -/
def abelianCharacterSwap : Equiv.Perm Bool →*
    MulAut (Bool → (Multiplicative L.AbelianGroup →* M)) where
  toFun p := MulEquiv.arrowCongr p (MulEquiv.refl _)
  map_one' := by ext χ b; rfl
  map_mul' p q := by ext χ b; rfl

abbrev AbelianCharacterWreath :=
  (Bool → (Multiplicative L.AbelianGroup →* M)) ⋊[L.abelianCharacterSwap (M := M)]
    Equiv.Perm Bool

/-- The universal character equivalence respects the permutation action,
so it identifies the complete semidirect products, not only their factors. -/
def abelianCharacterWreathEquiv [Field k] :
    L.AbelianCharacterWreath (M := kˣ) ≃* L.CharacterWreath (k := k) :=
  SemidirectProduct.congr
    (MulEquiv.arrowCongr (Equiv.refl Bool) (L.characterEquiv (M := kˣ)))
    (MulEquiv.refl (Equiv.Perm Bool)) (by
      intro p
      ext χ b
      rfl)

end Sunlet.LoopData

namespace Sunlet.NormalizedLatinSystem

variable {k ι Ω : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- The normalized function-field Galois group, with the character factors
written literally as homomorphisms from the constructed abelianization. -/
def normalizedGaloisUniversalEquiv (hm : 5 ≤ Fintype.card Ω) :
    (L.loopAt o).AbelianCharacterWreath (M := kˣ) ≃*
      (L.NormalizedSourceField (k := k) o ≃ₐ[L.NormalizedImageField (k := k) o]
        L.NormalizedSourceField (k := k) o) :=
  ((L.loopAt o).abelianCharacterWreathEquiv (k := k)).trans
    (L.normalizedGaloisEquiv o hm)

end Sunlet.NormalizedLatinSystem
end
end Stage_LoopWreathPresentation

#check "SUNLET_LoopWreathPresentation_READY"

#check @Sunlet.NormalizedLatinSystem.generic_unique_unordered_decomposition
#print axioms Sunlet.NormalizedLatinSystem.generic_unique_unordered_decomposition
#check @Sunlet.NormalizedLatinSystem.normalized_generic_degree
#print axioms Sunlet.NormalizedLatinSystem.normalized_generic_degree
#check @Sunlet.NormalizedLatinSystem.normalized_isGalois
#print axioms Sunlet.NormalizedLatinSystem.normalized_isGalois
#check @Sunlet.NormalizedLatinSystem.normalizedGaloisUniversalEquiv
#print axioms Sunlet.NormalizedLatinSystem.normalizedGaloisUniversalEquiv
#check @Sunlet.LoopData.paper_corollary_5_1_degree
#print axioms Sunlet.LoopData.paper_corollary_5_1_degree
#check @Sunlet.LoopData.paper_corollary_5_1_automorphisms
#print axioms Sunlet.LoopData.paper_corollary_5_1_automorphisms
#check @Sunlet.NormalizedLatinSystem.pairField_fixed_iff
#print axioms Sunlet.NormalizedLatinSystem.pairField_fixed_iff
