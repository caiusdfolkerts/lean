module

public import sunlet.generic_toric_embeddings
public import sunlet.loop_point_fibers
public import sunlet.rational_diagonal_actions
public import Mathlib.GroupTheory.SemidirectProduct

/-! The two character actions and permutation of the two summands as
actual automorphisms of the parameter function field. -/

@[expose] public section
noncomputable section

namespace Sunlet.LoopData

open ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})

abbrev PairField := ToricPairAlgebra.FunctionField (k := k) (ι := ι) L.identity

def characterWeight (χ : Bool → L.characterSubgroup (M := kˣ)) :
    ToricPairAlgebra.Index (ι := ι) L.identity → kˣ
  | (b, .inl a) => (χ b).val (e a)
  | (b, .inr x) => (χ b).val x

def characterAutomorphism (χ : Bool → L.characterSubgroup (M := kˣ)) :
    L.PairField (k := k) (ι := ι) ≃ₐ[k] L.PairField (k := k) (ι := ι) :=
  RationalDiagonalActions.fieldEquiv (Equiv.refl _) (L.characterWeight e χ)

@[simp] theorem characterAutomorphism_variable
    (χ : Bool → L.characterSubgroup (M := kˣ))
    (j : ToricPairAlgebra.Index (ι := ι) L.identity) :
    L.characterAutomorphism e χ (genericVariable L.identity j) =
      algebraMap k (L.PairField (k := k) (ι := ι)) (L.characterWeight e χ j).val *
        genericVariable L.identity j :=
  RationalDiagonalActions.fieldEquiv_variable (Equiv.refl _) (L.characterWeight e χ) j

def mapCharacter {K : Type*} [Field K] [Algebra k K]
    (χ : L.characterSubgroup (M := kˣ)) : L.characterSubgroup (M := Kˣ) :=
  ⟨fun x => Units.map (algebraMap k K).toMonoidHom (χ.val x), by
    constructor
    · simp [χ.property.1]
    · intro x y
      simp [χ.property.2]⟩

theorem characterAutomorphism_coefficient
    (χ : Bool → L.characterSubgroup (M := kˣ)) (b : Bool) (a : ι) :
    embeddedCoefficient L.identity (L.characterAutomorphism e χ).toAlgHom b a =
      genericCoefficient L.identity b a *
        ((L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).val (e a)).val := by
  change L.characterAutomorphism e χ (genericVariable L.identity (b, Sum.inl a)) = _
  rw [characterAutomorphism_variable]
  exact mul_comm _ _

theorem characterAutomorphism_torus
    (χ : Bool → L.characterSubgroup (M := kˣ)) (b : Bool) (x : Ω) :
    embeddedTorus L.identity (L.characterAutomorphism e χ).toAlgHom b x =
      genericTorus (k := k) (ι := ι) L.identity b x *
        (L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).val x := by
  apply Units.ext
  by_cases hx : x = L.identity
  · subst x
    simp [embeddedTorus, mapCharacter, (χ b).property.1]
  · change L.characterAutomorphism e χ
        ((genericTorus (k := k) (ι := ι) L.identity b x).val) = _
    simp only [genericTorus, dif_neg hx, Units.val_mk0, characterAutomorphism_variable,
      Units.val_mul, mapCharacter, characterWeight, Units.coe_map]
    exact mul_comm _ _

theorem characterAutomorphism_point (π : ι → Equiv.Perm Ω)
    (hπ : ∀ a, π a = L.left (e a))
    (χ : Bool → L.characterSubgroup (M := kˣ)) (b : Bool) :
    (fun ax => L.characterAutomorphism e χ (genericPoint L.identity π b ax)) =
      genericPoint L.identity π b := by
  change (fun ax => (L.characterAutomorphism e χ).toAlgHom
    (genericPoint L.identity π b ax)) = _
  rw [← embedded_point]
  have hc := funext (L.characterAutomorphism_coefficient e χ b)
  have ht := funext (L.characterAutomorphism_torus e χ b)
  rw [hc, ht]
  funext ax
  rcases ax with ⟨a, x⟩
  have hχ : (L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).val (π a x) =
      (L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).val (e a) *
        (L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).val x := by
    rw [hπ]
    exact (L.mapCharacter (K := L.PairField (k := k) (ι := ι)) (χ b)).property.2 (e a) x
  simp only [toricPoint, ToricPairAlgebra.genericPoint, ToricDifferential.coordinate,
    ToricDifferential.ratio, Units.val_mul, hχ]
  field_simp
  <;> ring

theorem characterAutomorphism_coordinates (π : ι → Equiv.Perm Ω)
    (hπ : ∀ a, π a = L.left (e a))
    (χ : Bool → L.characterSubgroup (M := kˣ)) (ax : ι × Ω) :
    L.characterAutomorphism e χ (genericCoordinates L.identity π ax) =
      genericCoordinates L.identity π ax := by
  change L.characterAutomorphism e χ
      (genericPoint L.identity π false ax + genericPoint L.identity π true ax) = _
  rw [map_add, congrFun (L.characterAutomorphism_point e π hπ χ false) ax,
    congrFun (L.characterAutomorphism_point e π hπ χ true) ax]
  rfl

theorem characterAutomorphism_injective :
    Function.Injective (L.characterAutomorphism (k := k) e) := by
  intro χ η he
  funext b
  apply Subtype.ext
  funext x
  by_cases hx : x = L.identity
  · subst x
    exact (χ b).property.1.trans (η b).property.1.symm
  · apply Units.ext
    have hv := congrArg (fun σ : L.PairField (k := k) (ι := ι) ≃ₐ[k]
        L.PairField (k := k) (ι := ι) =>
          σ (genericVariable L.identity (b, Sum.inr ⟨x, hx⟩))) he
    rw [characterAutomorphism_variable, characterAutomorphism_variable] at hv
    have hc := mul_right_cancel₀ (genericVariable_ne_zero (k := k) L.identity
      (b, Sum.inr ⟨x, hx⟩)) hv
    exact (algebraMap k (L.PairField (k := k) (ι := ι))).injective hc

def permutationIndex (p : Equiv.Perm Bool) :
    ToricPairAlgebra.Index (ι := ι) L.identity ≃
      ToricPairAlgebra.Index (ι := ι) L.identity :=
  Equiv.prodCongr p (Equiv.refl _)

def permutationAutomorphism (p : Equiv.Perm Bool) :
    L.PairField (k := k) (ι := ι) ≃ₐ[k] L.PairField (k := k) (ι := ι) :=
  RationalDiagonalActions.fieldEquiv (L.permutationIndex p) (fun _ => 1)

@[simp] theorem permutationAutomorphism_variable (p : Equiv.Perm Bool)
    (b : Bool) (j : NormalizedVariations.Index ι Ω L.identity) :
    L.permutationAutomorphism (k := k) (ι := ι) p (genericVariable L.identity (b, j)) =
      genericVariable L.identity (p b, j) := by
  change RationalDiagonalActions.fieldEquiv (L.permutationIndex p) (fun _ => (1 : kˣ))
    (RationalPartials.coordinateVariable (b, j)) = _
  rw [RationalDiagonalActions.fieldEquiv_variable]
  simp [permutationIndex]
  rfl

theorem permutationAutomorphism_coefficient (p : Equiv.Perm Bool) (b : Bool) (a : ι) :
    embeddedCoefficient L.identity (L.permutationAutomorphism (k := k) (ι := ι) p).toAlgHom b a =
      genericCoefficient (k := k) L.identity (p b) a :=
  L.permutationAutomorphism_variable p b (Sum.inl a)

theorem permutationAutomorphism_torus (p : Equiv.Perm Bool) (b : Bool) (x : Ω) :
    embeddedTorus L.identity (L.permutationAutomorphism (k := k) (ι := ι) p).toAlgHom b x =
      genericTorus (k := k) (ι := ι) L.identity (p b) x := by
  apply Units.ext
  by_cases hx : x = L.identity
  · subst x
    simp
  · simp [embeddedTorus, genericTorus, hx, permutationAutomorphism_variable]

theorem permutationAutomorphism_point (π : ι → Equiv.Perm Ω)
    (p : Equiv.Perm Bool) (b : Bool) :
    (fun ax => L.permutationAutomorphism (k := k) (ι := ι) p (genericPoint L.identity π b ax)) =
      genericPoint L.identity π (p b) := by
  change (fun ax => (L.permutationAutomorphism (k := k) (ι := ι) p).toAlgHom
    (genericPoint L.identity π b ax)) = _
  rw [← embedded_point]
  rw [funext (L.permutationAutomorphism_coefficient p b),
    funext (L.permutationAutomorphism_torus p b)]
  rfl

theorem permutationAutomorphism_coordinates (π : ι → Equiv.Perm Ω)
    (p : Equiv.Perm Bool) (ax : ι × Ω) :
    L.permutationAutomorphism (k := k) (ι := ι) p (genericCoordinates L.identity π ax) =
      genericCoordinates L.identity π ax := by
  change L.permutationAutomorphism (k := k) (ι := ι) p
      (genericPoint L.identity π false ax + genericPoint L.identity π true ax) = _
  rw [map_add, congrFun (L.permutationAutomorphism_point π p false) ax,
    congrFun (L.permutationAutomorphism_point π p true) ax]
  have hne : p false ≠ p true := p.injective.ne Bool.false_ne_true
  cases hp : p false <;> cases hq : p true
  · exact False.elim (hne (hp.trans hq.symm))
  · rfl
  · exact add_comm _ _
  · exact False.elim (hne (hp.trans hq.symm))

end Sunlet.LoopData
