module
public import sunlet.all_loop_contact_supports
public import sunlet.loop_field_actions
public import Mathlib.Data.Fintype.Perm
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_GENERIC_FIELD_CORE_IMPORTS_READY"

section GenericSource_LoopEmbeddingClassification

namespace Sunlet.LoopData

open ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

abbrev coordinateField : IntermediateField k (L.PairField (k := k) (ι := ι)) :=
  JacobianFinite.generatedField (genericCoordinates (k := k) L.identity π)

abbrev EmbeddingData (A : Type*) [Field A] :=
  Equiv.Perm Bool × (Bool → L.characterSubgroup (M := Aˣ))

section Description

variable {A : Type*} [Field A] [CharZero A] [Algebra k A]

def Parametrizes
    (φ ψ : L.PairField (k := k) (ι := ι) →ₐ[k] A)
    (d : L.EmbeddingData A) : Prop :=
  (∀ b a, embeddedCoefficient L.identity ψ b a =
    embeddedCoefficient L.identity φ (d.1 b) a * ((d.2 b).val (e a)).val) ∧
  (∀ b x, embeddedTorus L.identity ψ b x =
    embeddedTorus L.identity φ (d.1 b) x * (d.2 b).val x)

theorem parametrizes_unique
    (φ ψ ρ : L.PairField (k := k) (ι := ι) →ₐ[k] A)
    (d : L.EmbeddingData A)
    (hψ : L.Parametrizes e φ ψ d) (hρ : L.Parametrizes e φ ρ d) : ψ = ρ := by
  apply RationalDiagonalActions.algHom_ext_variables
  rintro ⟨b, a | x⟩
  · exact (hψ.1 b a).trans (hρ.1 b a).symm
  · change ψ (genericVariable L.identity (b, Sum.inr x)) =
      ρ (genericVariable L.identity (b, Sum.inr x))
    have ht := congrArg Units.val ((hψ.2 b x).trans (hρ.2 b x).symm)
    change ψ ((genericTorus (k := k) (ι := ι) L.identity b x).val) =
      ρ ((genericTorus (k := k) (ι := ι) L.identity b x).val) at ht
    simpa only [genericTorus, dif_neg x.property, Units.val_mk0] using ht

include hπ in
theorem exists_parametrizes_of_point_permutation
    (φ ψ : L.PairField (k := k) (ι := ι) →ₐ[k] A)
    (p : Equiv.Perm Bool)
    (hp : ∀ b, (fun ax => ψ (genericPoint L.identity π b ax)) =
      fun ax => φ (genericPoint L.identity π (p b) ax)) :
    ∃ d : L.EmbeddingData A, L.Parametrizes e φ ψ d := by
  have hb : ∀ b,
      toricPoint π (embeddedCoefficient L.identity φ (p b))
          (embeddedTorus L.identity φ (p b)) =
        toricPoint π (embeddedCoefficient L.identity ψ b)
          (embeddedTorus L.identity ψ b) := by
    intro b
    rw [embedded_point, embedded_point]
    exact (hp b).symm
  let χ : Bool → L.characterSubgroup (M := Aˣ) := fun b =>
    L.characterOfPointEquality e π hπ
      (embeddedCoefficient L.identity φ (p b)) (embeddedCoefficient L.identity ψ b)
      (embeddedTorus L.identity φ (p b)) (embeddedTorus L.identity ψ b)
      (embeddedCoefficient_ne_zero L.identity φ (p b))
      (embeddedCoefficient_ne_zero L.identity ψ b)
      (embeddedTorus_base L.identity φ (p b)) (embeddedTorus_base L.identity ψ b) (hb b)
  refine ⟨(p, χ), ?_, ?_⟩
  · intro b a
    exact L.coefficient_of_point_equality e π hπ _ _ _ _ _ _ _ _ (hb b) a
  · intro b x
    exact L.torus_of_point_equality e π hπ _ _ _ _ _ _ _ _ (hb b) x

end Description

theorem coordinateField_finite_separable
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity) :
    Module.Finite (L.coordinateField (k := k) π) (L.PairField (k := k) (ι := ι)) ∧
      Algebra.IsSeparable (L.coordinateField (k := k) π)
        (L.PairField (k := k) (ι := ι)) :=
  generic_finite_separable L.identity π (W.A : Set ι) (W.B : Set ι)
    W.disjoint hmoves W.Atwo W.Btwo W.Atrans W.Btrans

section UpperBound

variable {A : Type*} [Field A] [CharZero A] [Algebra k A]
  [Algebra (L.PairField (k := k) (ι := ι)) A]
  [IsScalarTower k (L.PairField (k := k) (ι := ι)) A]
  [Algebra.IsSeparable (L.PairField (k := k) (ι := ι)) A]

include hπ in
theorem exists_parametrizes_of_sum
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity))
    (ψ : L.PairField (k := k) (ι := ι) →ₐ[k] A)
    (hcoord : ∀ ax,
      algebraMap (L.PairField (k := k) (ι := ι)) A
        (genericCoordinates L.identity π ax) = ψ (genericCoordinates L.identity π ax)) :
    ∃ d : L.EmbeddingData A,
      L.Parametrizes e (canonical (k := k) (F := A) (ι := ι) L.identity) ψ d := by
  have hu := unordered_under_embedding L.identity π W hmoves hdim ψ hcoord
  obtain ⟨p, hp⟩ : ∃ p : Equiv.Perm Bool, ∀ b,
      (fun ax => ψ (genericPoint L.identity π b ax)) =
        fun ax => algebraMap (L.PairField (k := k) (ι := ι)) A
          (genericPoint L.identity π (p b) ax) := by
    rcases hu with ⟨hf, ht⟩ | ⟨hf, ht⟩
    · refine ⟨Equiv.refl _, ?_⟩
      intro b
      cases b
      · exact hf
      · exact ht
    · refine ⟨Equiv.swap false true, ?_⟩
      intro b
      cases b
      · simpa using hf
      · simpa using ht
  exact L.exists_parametrizes_of_point_permutation e π hπ _ ψ p hp

end UpperBound

theorem embeddingData_card {A : Type*} [Field A] [IsAlgClosed A] [CharZero A] :
    Nat.card (L.EmbeddingData A) = 2 * Nat.card L.AbelianGroup ^ 2 := by
  rw [Nat.card_prod, Nat.card_fun, L.character_card (K := A)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_bool]
  norm_num

include hπ in
/-- The upper bound counts actual embeddings of the actual coordinate
field extension, rather than solutions of an assumed fiber equation. -/
theorem coordinateField_finrank_le
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity)) :
    Module.finrank (L.coordinateField (k := k) π) (L.PairField (k := k) (ι := ι)) ≤
      2 * Nat.card L.AbelianGroup ^ 2 := by
  let E := L.PairField (k := k) (ι := ι)
  let F := L.coordinateField (k := k) π
  let A := AlgebraicClosure E
  have hfin := L.coordinateField_finite_separable π W hmoves
  letI : Module.Finite F E := hfin.1
  letI : Algebra.IsSeparable F E := hfin.2
  have hdata : ∀ ψ : E →ₐ[F] A, ∃ d : L.EmbeddingData A,
      L.Parametrizes e (canonical (k := k) (F := A) (ι := ι) L.identity)
        (ψ.restrictScalars k) d := by
    intro ψ
    apply L.exists_parametrizes_of_sum e π hπ W hmoves hdim
    intro ax
    let x : F := ⟨genericCoordinates L.identity π ax,
      JacobianFinite.coordinate_mem_generatedField _ ax⟩
    exact (ψ.commutes x).symm
  choose f hf using hdata
  have hi : Function.Injective f := by
    intro ψ ρ he
    have hh := L.parametrizes_unique e _ (ψ.restrictScalars k) (ρ.restrictScalars k)
      (f ψ) (hf ψ) (he.symm ▸ hf ρ)
    ext x
    exact congrArg (fun q : E →ₐ[k] A => q x) hh
  calc
    Module.finrank F E = Nat.card (E →ₐ[F] A) :=
      (AlgHom.natCard_of_splits F E A (fun _ => IsAlgClosed.splits _)).symm
    _ ≤ Nat.card (L.EmbeddingData A) := Nat.card_le_card_of_injective f hi
    _ = 2 * Nat.card L.AbelianGroup ^ 2 := L.embeddingData_card

section Automorphisms

theorem genericPoint_injective_bool (a : ι) :
    Function.Injective (genericPoint (k := k) L.identity π) := by
  have hne : genericPoint (k := k) L.identity π false ≠
      genericPoint L.identity π true := by
    intro he
    have hd := congrArg
      (DerivativeChords.vectorDerivative (euler (k := k) (ι := ι) L.identity)) he
    rw [euler_genericPoint, euler_genericPoint] at hd
    change genericPoint (k := k) L.identity π false = 0 at hd
    have hv := congrFun hd (a, L.identity)
    have hn : genericPoint (k := k) L.identity π false (a, L.identity) ≠ 0 := by
      change genericCoefficient L.identity false a *
        ((genericTorus (k := k) (ι := ι) L.identity false L.identity).val /
          (genericTorus (k := k) (ι := ι) L.identity false (π a L.identity)).val) ≠ 0
      exact mul_ne_zero (genericVariable_ne_zero L.identity (false, Sum.inl a))
        (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    exact hn hv
  intro b c he
  cases b <;> cases c
  · rfl
  · exact False.elim (hne he)
  · exact False.elim (hne he.symm)
  · rfl

def dataAutomorphism (d : L.EmbeddingData k) :
    L.PairField (k := k) (ι := ι) ≃ₐ[k] L.PairField (k := k) (ι := ι) :=
  L.permutationAutomorphism d.1 * L.characterAutomorphism e d.2

include hπ in
theorem dataAutomorphism_point (d : L.EmbeddingData k) (b : Bool) :
    (fun ax => L.dataAutomorphism e d (genericPoint L.identity π b ax)) =
      genericPoint L.identity π (d.1 b) := by
  funext ax
  change L.permutationAutomorphism d.1
      (L.characterAutomorphism e d.2 (genericPoint L.identity π b ax)) = _
  rw [congrFun (L.characterAutomorphism_point e π hπ d.2 b) ax,
    congrFun (L.permutationAutomorphism_point π d.1 b) ax]

include hπ in
theorem dataAutomorphism_coordinates (d : L.EmbeddingData k) (ax : ι × Ω) :
    L.dataAutomorphism e d (genericCoordinates L.identity π ax) =
      genericCoordinates L.identity π ax := by
  change L.permutationAutomorphism d.1
      (L.characterAutomorphism e d.2 (genericCoordinates L.identity π ax)) = _
  rw [L.characterAutomorphism_coordinates e π hπ,
    L.permutationAutomorphism_coordinates π]

include hπ in
theorem dataAutomorphism_injective (a : ι) :
    Function.Injective (L.dataAutomorphism (k := k) e) := by
  rintro ⟨p, χ⟩ ⟨q, η⟩ he
  have hp : p = q := by
    ext b
    apply L.genericPoint_injective_bool (k := k) π a
    have hb := congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[k]
        L.PairField (k := k) (ι := ι) =>
      fun ax => σ (genericPoint L.identity π b ax)) he
    rw [L.dataAutomorphism_point e π hπ, L.dataAutomorphism_point e π hπ] at hb
    exact hb
  subst q
  have hc : L.characterAutomorphism e χ = L.characterAutomorphism e η :=
    mul_left_cancel he
  exact Prod.ext rfl (L.characterAutomorphism_injective e hc)

def dataAutomorphismOverCoordinate (d : L.EmbeddingData k) :
    L.PairField (k := k) (ι := ι) ≃ₐ[L.coordinateField (k := k) π]
      L.PairField (k := k) (ι := ι) :=
  GeneratedFieldActions.overGenerated (genericCoordinates L.identity π)
    (L.dataAutomorphism e d) (L.dataAutomorphism_coordinates e π hπ d)

include hπ in
theorem dataAutomorphismOverCoordinate_injective (a : ι) :
    Function.Injective (L.dataAutomorphismOverCoordinate (k := k) e π hπ) := by
  intro d d' he
  apply L.dataAutomorphism_injective e π hπ a
  ext x
  exact congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[L.coordinateField (k := k) π]
      L.PairField (k := k) (ι := ι) => σ x) he

end Automorphisms

include hπ in
/-- Exact degree for the literal two-component ratio map, obtained from
the proved upper bound on embeddings and explicit distinct automorphisms. -/
theorem coordinateField_finrank [IsAlgClosed k]
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity)) :
    Module.finrank (L.coordinateField (k := k) π) (L.PairField (k := k) (ι := ι)) =
      2 * Nat.card L.AbelianGroup ^ 2 := by
  let E := L.PairField (k := k) (ι := ι)
  let F := L.coordinateField (k := k) π
  have hfin := L.coordinateField_finite_separable π W hmoves
  letI : Module.Finite F E := hfin.1
  obtain ⟨a, -, _, -, -⟩ := W.Atwo
  have hlo : 2 * Nat.card L.AbelianGroup ^ 2 ≤ Nat.card (E ≃ₐ[F] E) := by
    rw [← L.embeddingData_card (A := k)]
    exact Nat.card_le_card_of_injective (L.dataAutomorphismOverCoordinate e π hπ)
      (L.dataAutomorphismOverCoordinate_injective e π hπ a)
  have haut : Nat.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  exact le_antisymm (L.coordinateField_finrank_le e π hπ W hmoves hdim) (hlo.trans haut)

include hπ in
theorem coordinateField_isGalois [IsAlgClosed k]
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity)) :
    IsGalois (L.coordinateField (k := k) π) (L.PairField (k := k) (ι := ι)) := by
  let E := L.PairField (k := k) (ι := ι)
  let F := L.coordinateField (k := k) π
  have hfin := L.coordinateField_finite_separable π W hmoves
  letI : Module.Finite F E := hfin.1
  obtain ⟨a, -, _, -, -⟩ := W.Atwo
  apply IsGalois.of_card_aut_eq_finrank
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [L.coordinateField_finrank e π hπ W hmoves hdim,
      ← L.embeddingData_card (A := k)]
    exact Nat.card_le_card_of_injective (L.dataAutomorphismOverCoordinate e π hπ)
      (L.dataAutomorphismOverCoordinate_injective e π hπ a)

end Sunlet.LoopData

end GenericSource_LoopEmbeddingClassification

#check "SUNLET_LOOP_FIELD_CLASSIFICATION_READY"

section GenericSource_LoopGaloisGroup

namespace Sunlet.LoopData

open ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

/-- The ordinary action of the permutation group on the two character
factors, with inverse precomposition. -/
def swapCharacters : Equiv.Perm Bool →* MulAut (Bool → L.characterSubgroup (M := kˣ)) where
  toFun p := MulEquiv.arrowCongr p (MulEquiv.refl _)
  map_one' := by ext χ b; rfl
  map_mul' p q := by ext χ b; rfl

@[simp] theorem swapCharacters_apply (p : Equiv.Perm Bool)
    (χ : Bool → L.characterSubgroup (M := kˣ)) (b : Bool) :
    L.swapCharacters p χ b = χ (p.symm b) := rfl

abbrev CharacterWreath :=
  (Bool → L.characterSubgroup (M := kˣ)) ⋊[L.swapCharacters (k := k)] Equiv.Perm Bool

def wreathAutomorphism (d : L.CharacterWreath (k := k)) :
    L.PairField (k := k) (ι := ι) ≃ₐ[k] L.PairField (k := k) (ι := ι) :=
  L.characterAutomorphism e d.left * L.permutationAutomorphism d.right

@[simp] theorem wreathAutomorphism_variable (d : L.CharacterWreath (k := k))
    (b : Bool) (j : NormalizedVariations.Index ι Ω L.identity) :
    L.wreathAutomorphism e d (genericVariable L.identity (b, j)) =
      algebraMap k (L.PairField (k := k) (ι := ι))
        (L.characterWeight e d.left (d.right b, j)).val *
        genericVariable L.identity (d.right b, j) := by
  simp [wreathAutomorphism]

theorem wreathAutomorphism_one :
    L.wreathAutomorphism (k := k) e 1 = 1 := by
  apply RationalDiagonalActions.algEquiv_ext_variables
  rintro ⟨b, j⟩
  change L.wreathAutomorphism (k := k) e 1 (genericVariable L.identity (b, j)) =
    genericVariable L.identity (b, j)
  cases j <;> simp [characterWeight]

theorem wreathAutomorphism_mul (d d' : L.CharacterWreath (k := k)) :
    L.wreathAutomorphism e (d * d') =
      L.wreathAutomorphism e d * L.wreathAutomorphism e d' := by
  apply RationalDiagonalActions.algEquiv_ext_variables
  rintro ⟨b, j⟩
  change L.wreathAutomorphism e (d * d') (genericVariable L.identity (b, j)) =
    L.wreathAutomorphism e d (L.wreathAutomorphism e d'
      (genericVariable L.identity (b, j)))
  simp only [wreathAutomorphism_variable, map_mul, AlgEquiv.commutes,
    SemidirectProduct.mul_left, SemidirectProduct.mul_right, Equiv.Perm.mul_apply]
  cases j <;> simp only [characterWeight, Pi.mul_apply, Subgroup.coe_mul,
    swapCharacters_apply, Equiv.symm_apply_apply, Units.val_mul, map_mul]
  all_goals ring

include hπ in
theorem wreathAutomorphism_coordinates (d : L.CharacterWreath (k := k)) (ax : ι × Ω) :
    L.wreathAutomorphism e d (genericCoordinates L.identity π ax) =
      genericCoordinates L.identity π ax := by
  change L.characterAutomorphism e d.left
      (L.permutationAutomorphism d.right (genericCoordinates L.identity π ax)) = _
  rw [L.permutationAutomorphism_coordinates π,
    L.characterAutomorphism_coordinates e π hπ]

theorem wreathAutomorphism_eq_data (d : L.CharacterWreath (k := k)) :
    L.wreathAutomorphism e d =
      L.dataAutomorphism e (d.right, fun b => d.left (d.right b)) := by
  apply RationalDiagonalActions.algEquiv_ext_variables
  rintro ⟨b, j⟩
  change L.wreathAutomorphism e d (genericVariable L.identity (b, j)) =
    L.permutationAutomorphism d.right
      (L.characterAutomorphism e (fun b => d.left (d.right b))
        (genericVariable L.identity (b, j)))
  cases j <;> simp [characterWeight]

include hπ in
theorem wreathAutomorphism_point (d : L.CharacterWreath (k := k)) (b : Bool) :
    (fun ax => L.wreathAutomorphism e d (genericPoint L.identity π b ax)) =
      genericPoint L.identity π (d.right b) := by
  rw [L.wreathAutomorphism_eq_data e]
  exact L.dataAutomorphism_point e π hπ _ b

include hπ in
theorem wreathAutomorphism_injective (a : ι) :
    Function.Injective (L.wreathAutomorphism (k := k) e) := by
  intro d d' he
  rw [L.wreathAutomorphism_eq_data e, L.wreathAutomorphism_eq_data e] at he
  have hh := L.dataAutomorphism_injective e π hπ a he
  have hp : d.right = d'.right := congrArg Prod.fst hh
  have hc : (fun b => d.left (d.right b)) = fun b => d'.left (d'.right b) :=
    congrArg Prod.snd hh
  apply SemidirectProduct.ext
  · funext b
    have hv := congrFun hc (d.right.symm b)
    simpa [← hp] using hv
  · exact hp

/-- The literal group homomorphism from the semidirect product into the
automorphisms of the actual coordinate-field extension. -/
def wreathHom : L.CharacterWreath (k := k) →*
    (L.PairField (k := k) (ι := ι) ≃ₐ[L.coordinateField (k := k) π]
      L.PairField (k := k) (ι := ι)) where
  toFun d := GeneratedFieldActions.overGenerated (genericCoordinates L.identity π)
    (L.wreathAutomorphism e d) (L.wreathAutomorphism_coordinates e π hπ d)
  map_one' := by
    ext x
    exact congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[k]
      L.PairField (k := k) (ι := ι) => σ x) (L.wreathAutomorphism_one e)
  map_mul' d d' := by
    ext x
    exact congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[k]
      L.PairField (k := k) (ι := ι) => σ x) (L.wreathAutomorphism_mul e d d')

include hπ in
theorem wreathHom_injective (a : ι) :
    Function.Injective (L.wreathHom (k := k) e π hπ) := by
  intro d d' he
  apply L.wreathAutomorphism_injective e π hπ a
  ext x
  exact congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[L.coordinateField (k := k) π]
    L.PairField (k := k) (ι := ι) => σ x) he

theorem characterWreath_card [IsAlgClosed k] :
    Nat.card (L.CharacterWreath (k := k)) = 2 * Nat.card L.AbelianGroup ^ 2 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd), Nat.card_prod,
    Nat.card_fun, L.character_card (K := k)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_perm]
  norm_num [mul_comm]

instance characterWreath_finite [IsAlgClosed k] : Finite (L.CharacterWreath (k := k)) :=
  Finite.of_equiv ((Bool → L.characterSubgroup (M := kˣ)) × Equiv.Perm Bool)
    SemidirectProduct.equivProd.symm

include hπ in
theorem wreathHom_bijective [IsAlgClosed k]
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity)) :
    Function.Bijective (L.wreathHom (k := k) e π hπ) := by
  let E := L.PairField (k := k) (ι := ι)
  let F := L.coordinateField (k := k) π
  letI : Module.Finite F E := (L.coordinateField_finite_separable π W hmoves).1
  letI : IsGalois F E := L.coordinateField_isGalois e π hπ W hmoves hdim
  letI : Fintype (L.CharacterWreath (k := k)) := Fintype.ofFinite _
  obtain ⟨a, -, _, -, -⟩ := W.Atwo
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨L.wreathHom_injective e π hπ a, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank,
    L.coordinateField_finrank e π hπ W hmoves hdim, L.characterWreath_card]

def coordinateField_galoisEquiv [IsAlgClosed k]
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity)) :
    L.CharacterWreath (k := k) ≃*
      (L.PairField (k := k) (ι := ι) ≃ₐ[L.coordinateField (k := k) π]
        L.PairField (k := k) (ι := ι)) :=
  MulEquiv.ofBijective (L.wreathHom e π hπ)
    (L.wreathHom_bijective e π hπ W hmoves hdim)

include hπ in
/-- The outer product of the difference vector is an actual rational
function of the sum coordinates.  This is the algebraic input for the
generic-open reconstruction, including the toric boundary. -/
theorem differenceProduct_mem_coordinateField [IsAlgClosed k]
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity))
    (i j : ι × Ω) :
    (genericPoint (k := k) L.identity π false i - genericPoint L.identity π true i) *
        (genericPoint L.identity π false j - genericPoint L.identity π true j) ∈
      L.coordinateField (k := k) π := by
  let E := L.PairField (k := k) (ι := ι)
  let F := L.coordinateField (k := k) π
  letI : Module.Finite F E := (L.coordinateField_finite_separable π W hmoves).1
  letI : IsGalois F E := L.coordinateField_isGalois e π hπ W hmoves hdim
  have hfix : ∀ σ : E ≃ₐ[F] E,
      σ ((genericPoint L.identity π false i - genericPoint L.identity π true i) *
        (genericPoint L.identity π false j - genericPoint L.identity π true j)) =
        (genericPoint L.identity π false i - genericPoint L.identity π true i) *
          (genericPoint L.identity π false j - genericPoint L.identity π true j) := by
    intro σ
    obtain ⟨d, rfl⟩ := (L.wreathHom_bijective e π hπ W hmoves hdim).surjective σ
    change L.wreathAutomorphism e d (_ * _) = _
    rw [map_mul, map_sub, map_sub,
      congrFun (L.wreathAutomorphism_point e π hπ d false) i,
      congrFun (L.wreathAutomorphism_point e π hπ d true) i,
      congrFun (L.wreathAutomorphism_point e π hπ d false) j,
      congrFun (L.wreathAutomorphism_point e π hπ d true) j]
    have hne : d.right false ≠ d.right true := d.right.injective.ne (by decide)
    cases hp : d.right false <;> cases hq : d.right true
    · exact False.elim (hne (hp.trans hq.symm))
    · rfl
    · ring
    · exact False.elim (hne (hp.trans hq.symm))
  obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact hx ▸ x.property

include hπ in
/-- A nonzero component difference cannot lie in the sum-coordinate
field, because the literal interchange automorphism fixes that field. -/
theorem difference_not_mem_coordinateField (i : ι × Ω) :
    genericPoint (k := k) L.identity π false i - genericPoint L.identity π true i ∉
      L.coordinateField (k := k) π := by
  intro hm
  let p : Equiv.Perm Bool := Equiv.swap false true
  have hh := GeneratedFieldActions.fixes_adjoin (genericCoordinates (k := k) L.identity π)
    (L.permutationAutomorphism (k := k) (ι := ι) p)
    (L.permutationAutomorphism_coordinates π p) ⟨_, hm⟩
  rw [map_sub, congrFun (L.permutationAutomorphism_point π p false) i,
    congrFun (L.permutationAutomorphism_point π p true) i] at hh
  simp only [p, Equiv.swap_apply_left, Equiv.swap_apply_right] at hh
  have he : genericPoint (k := k) L.identity π false i =
      genericPoint L.identity π true i := by
    have hn : -(genericPoint (k := k) L.identity π false i -
        genericPoint L.identity π true i) =
        genericPoint L.identity π false i - genericPoint L.identity π true i := by
      simpa only [neg_sub] using hh
    exact sub_eq_zero.mp (CharZero.neg_eq_self_iff.mp hn)
  have hd := congrArg (euler (k := k) (ι := ι) L.identity) he
  have hf := congrFun (euler_genericPoint (k := k) L.identity π false) i
  have ht := congrFun (euler_genericPoint (k := k) L.identity π true) i
  change euler L.identity (genericPoint L.identity π false i) =
    genericPoint L.identity π false i at hf
  change euler L.identity (genericPoint L.identity π true i) = 0 at ht
  rw [hf, ht] at hd
  have hn : genericPoint (k := k) L.identity π false i ≠ 0 := by
    change genericCoefficient L.identity false i.1 *
      ((genericTorus (k := k) (ι := ι) L.identity false i.2).val /
        (genericTorus (k := k) (ι := ι) L.identity false (π i.1 i.2)).val) ≠ 0
    exact mul_ne_zero (genericVariable_ne_zero L.identity (false, Sum.inl i.1))
      (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))
  exact hn hd

end Sunlet.LoopData

end GenericSource_LoopGaloisGroup

#check "SUNLET_LOOP_GALOIS_GROUP_READY"
#check @Sunlet.LoopData.coordinateField_finrank
#print axioms Sunlet.LoopData.coordinateField_finrank
#check @Sunlet.LoopData.coordinateField_isGalois
#print axioms Sunlet.LoopData.coordinateField_isGalois
#check @Sunlet.LoopData.coordinateField_galoisEquiv
#print axioms Sunlet.LoopData.coordinateField_galoisEquiv
#check @Sunlet.LoopData.differenceProduct_mem_coordinateField
#print axioms Sunlet.LoopData.differenceProduct_mem_coordinateField
