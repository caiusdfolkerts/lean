module

public import sunlet.generic_pair_geometry
public import sunlet.extended_rational_derivations

/-!
# Unordered uniqueness under actual parameter-field embeddings

All evaluations and derivations here are constructed from the rational
parameter field. No tangent-range or derivation-existence hypothesis is
assumed in the final embedding theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace Sunlet.ToricPairAlgebra

open NormalizedVariations ToricDifferential

variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (o : Ω)

section EmbeddedParameters

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]

def embeddedCoefficient (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (b : Bool) (a : ι) : F := φ (genericCoefficient o b a)

def embeddedTorus (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (b : Bool) (x : Ω) : Fˣ := Units.map φ.toMonoidHom (genericTorus o b x)

@[simp] theorem embeddedTorus_base (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (b : Bool) : embeddedTorus o φ b o = 1 := by
  simp [embeddedTorus]

theorem embeddedCoefficient_ne_zero (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (b : Bool) (a : ι) : embeddedCoefficient o φ b a ≠ 0 := by
  exact (map_ne_zero φ).2 (genericVariable_ne_zero (k := k) o (b, Sum.inl a))

theorem evaluate_embedded (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F) :
    evaluate (k := k) o (embeddedCoefficient o φ) (embeddedTorus o φ) =
      φ.comp (generic o) :=
  evaluate_comp o φ (genericCoefficient o) (genericTorus o)

theorem embedded_faithful (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F) :
    Function.Injective (evaluate (k := k) o (embeddedCoefficient o φ) (embeddedTorus o φ)) := by
  rw [evaluate_embedded]
  exact φ.injective.comp (generic_injective o)

theorem embedded_point (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (π : ι → Equiv.Perm Ω) (b : Bool) :
    toricPoint π (embeddedCoefficient o φ b) (embeddedTorus o φ b) =
      fun ax => φ (genericPoint o π b ax) := by
  funext ax
  simp [toricPoint, genericPoint, embeddedCoefficient, embeddedTorus, coordinate, ratio]

theorem embedded_sum (φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (π : ι → Equiv.Perm Ω) :
    toricPoint π (embeddedCoefficient o φ false) (embeddedTorus o φ false) +
      toricPoint π (embeddedCoefficient o φ true) (embeddedTorus o φ true) =
      fun ax => φ (genericCoordinates o π ax) := by
  rw [embedded_point, embedded_point]
  funext ax
  exact (map_add φ _ _).symm

end EmbeddedParameters

section CanonicalDerivations

variable {F : Type*} [Field F] [CharZero F] [Algebra k F]
  [Algebra (FunctionField (k := k) (ι := ι) o) F]
  [IsScalarTower k (FunctionField (k := k) (ι := ι) o) F]
  [Algebra.IsSeparable (FunctionField (k := k) (ι := ι) o) F]

abbrev canonical : FunctionField (k := k) (ι := ι) o →ₐ[k] F :=
  IsScalarTower.toAlgHom k (FunctionField (k := k) (ι := ι) o) F

def logarithmicWeight (b : Bool) : NormalizedVariations.Index ι Ω o → F
  | .inl _ => 1
  | .inr x => algebraMap (FunctionField (k := k) (ι := ι) o) F
      (genericVariable o (b, Sum.inr x))

def logarithmicPartial (b : Bool) (j : NormalizedVariations.Index ι Ω o) :
    Derivation k F F :=
  logarithmicWeight (k := k) (F := F) (ι := ι) o b j •
    ExtendedRationalDerivations.coordinatePartial (k := k) (A := F) (b, j)

theorem logarithmicPartial_variable (b : Bool) (j : NormalizedVariations.Index ι Ω o)
    (q : Index (ι := ι) o) :
    logarithmicPartial (k := k) (F := F) (ι := ι) o b j
      (algebraMap (FunctionField (k := k) (ι := ι) o) F (genericVariable o q)) =
      if q = (b, j) then logarithmicWeight (k := k) (F := F) (ι := ι) o b j else 0 := by
  change (logarithmicWeight (k := k) (F := F) (ι := ι) o b j •
    ExtendedRationalDerivations.coordinatePartial (k := k) (A := F) (b, j))
      (algebraMap (FunctionField (k := k) (ι := ι) o) F
        (RationalPartials.coordinateVariable q)) = _
  simp only [Derivation.smul_apply, ExtendedRationalDerivations.partial_algebraMap_variable,
    smul_eq_mul]
  split_ifs <;> simp

theorem canonical_logarithmicVelocity (b c : Bool)
    (j : NormalizedVariations.Index ι Ω o) :
    logarithmicVelocity (logarithmicPartial (k := k) (F := F) (ι := ι) o b j)
      (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o) c)
      (fun x => (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o) c x).val) =
      if c = b then asVariation o (Pi.single j 1) else 0 := by
  apply Prod.ext
  · funext a
    change logarithmicPartial (k := k) (F := F) (ι := ι) o b j
      (algebraMap (FunctionField (k := k) (ι := ι) o) F
        (genericVariable o (c, Sum.inl a))) = _
    rw [logarithmicPartial_variable]
    cases j with
    | inl a' =>
      by_cases hcb : c = b <;> by_cases haa : a = a' <;>
        simp [hcb, haa, logarithmicWeight, asVariation, Pi.single_apply]
    | inr x =>
      by_cases hcb : c = b <;> simp [hcb, logarithmicWeight, asVariation, Pi.single_apply]
  · funext x
    by_cases hx : x = o
    · subst x
      by_cases hcb : c = b <;>
        simp [hcb, logarithmicVelocity, embeddedTorus, genericTorus, asVariation]
    · simp only [logarithmicVelocity, embeddedTorus, genericTorus, dif_neg hx,
        Units.coe_map, Units.val_mk0]
      change logarithmicPartial (k := k) (F := F) (ι := ι) o b j
        (algebraMap (FunctionField (k := k) (ι := ι) o) F
          (genericVariable o (c, Sum.inr ⟨x, hx⟩))) /
        algebraMap (FunctionField (k := k) (ι := ι) o) F
          (genericVariable o (c, Sum.inr ⟨x, hx⟩)) = _
      rw [logarithmicPartial_variable]
      have hne : algebraMap (FunctionField (k := k) (ι := ι) o) F
          (genericVariable o (c, Sum.inr ⟨x, hx⟩)) ≠ 0 :=
        (map_ne_zero (algebraMap (FunctionField (k := k) (ι := ι) o) F)).2
          (genericVariable_ne_zero (k := k) o _)
      cases j with
      | inl a =>
        by_cases hcb : c = b <;> simp [hcb, asVariation, hx, Pi.single_apply]
      | inr y =>
        by_cases hcb : c = b
        · subst c
          by_cases hxy : x = y.val
          · subst x
            simp [logarithmicWeight, asVariation, y.property, Pi.single_apply, hne]
          · have hsub : (⟨x, hx⟩ : {x : Ω // x ≠ o}) ≠ y := by
              intro he
              exact hxy (congrArg Subtype.val he)
            simp [hsub, logarithmicWeight, asVariation, hx, Pi.single_apply]
        · simp [hcb, logarithmicWeight, asVariation, hx, Pi.single_apply]

theorem logarithmicPartial_point (π : ι → Equiv.Perm Ω) (b : Bool)
    (j : NormalizedVariations.Index ι Ω o) (c : Bool) :
    DerivativeChords.vectorDerivative (logarithmicPartial (k := k) (F := F) (ι := ι) o b j)
      (toricPoint π (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o) c)
        (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o) c)) =
      if c = b then componentDifferential o π
        (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o))
        (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o)) c (Pi.single j 1) else 0 := by
  funext ax
  rw [show DerivativeChords.vectorDerivative (logarithmicPartial (k := k) (F := F) (ι := ι) o b j)
      (toricPoint π (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o) c)
        (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o) c)) ax =
      differential π (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o) c)
        (fun x => (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o) c x).val)
        (logarithmicVelocity (logarithmicPartial (k := k) (F := F) (ι := ι) o b j)
          (embeddedCoefficient o (canonical (k := k) (F := F) (ι := ι) o) c)
          (fun x => (embeddedTorus o (canonical (k := k) (F := F) (ι := ι) o) c x).val)) ax from
      derivation_coordinate _ _ _ _ (fun x => Units.ne_zero _) ax.1 ax.2,
    canonical_logarithmicVelocity]
  by_cases hcb : c = b <;> simp [hcb, componentDifferential]

/-- Every embedding preserving the actual sum-coordinate field preserves
the two actual toric points as an unordered pair. -/
theorem unordered_under_embedding
    (π : ι → Equiv.Perm Ω) (W : SparseWitness (k := k) o π)
    (hmoves : ∀ a, π a o ≠ o)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω o))
    (ψ : FunctionField (k := k) (ι := ι) o →ₐ[k] F)
    (hcoord : ∀ ax,
      algebraMap (FunctionField (k := k) (ι := ι) o) F (genericCoordinates o π ax) =
        ψ (genericCoordinates o π ax)) :
    ((fun ax => ψ (genericPoint o π false ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) F (genericPoint o π false ax)) ∧
      (fun ax => ψ (genericPoint o π true ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) F (genericPoint o π true ax))) ∨
    ((fun ax => ψ (genericPoint o π false ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) F (genericPoint o π true ax)) ∧
      (fun ax => ψ (genericPoint o π true ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) F (genericPoint o π false ax))) := by
  let φ : FunctionField (k := k) (ι := ι) o →ₐ[k] F := canonical (k := k) (F := F) (ι := ι) o
  have hs : toricPoint π (embeddedCoefficient o φ false) (embeddedTorus o φ false) +
      toricPoint π (embeddedCoefficient o φ true) (embeddedTorus o φ true) =
      toricPoint π (embeddedCoefficient o ψ false) (embeddedTorus o ψ false) +
      toricPoint π (embeddedCoefficient o ψ true) (embeddedTorus o ψ true) := by
    rw [embedded_sum, embedded_sum]
    exact funext hcoord
  have hu := unordered_of_actual_derivations o π W hmoves
    (embeddedCoefficient o φ) (embeddedCoefficient o ψ)
    (embeddedTorus o φ) (embeddedTorus o ψ)
    (embeddedTorus_base o φ) (embeddedTorus_base o ψ)
    (embedded_faithful o φ) (embedded_faithful o ψ)
    (embeddedCoefficient_ne_zero o φ) hdim
    (logarithmicPartial (k := k) (F := F) (ι := ι) o) (logarithmicPartial_point o π)
    (ExtendedRationalDerivations.toricEuler (k := k) (A := F) (ι := ι) o)
    (ExtendedRationalDerivations.toricEuler_coefficient (k := k) (A := F) o)
    (ExtendedRationalDerivations.toricEuler_torus (k := k) (A := F) o) hs
  simpa [embedded_point, φ, canonical] using hu

end CanonicalDerivations

end Sunlet.ToricPairAlgebra
