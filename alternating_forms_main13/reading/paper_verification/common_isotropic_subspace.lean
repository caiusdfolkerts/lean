module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic

/-!
# Common isotropic subspaces for two alternating forms

Any two alternating bilinear forms on an `n`-dimensional vector space over a field
of characteristic different from two have a common isotropic subspace of dimension
at least `ceil(n/2)`. The argument does not assume that the pencil is generic.

In odd dimension an alternating form has a nonzero radical vector. In even
dimension any nonzero vector suffices. Intersect its common orthogonal space with
a transverse hyperplane, apply dimension induction there, and add the chosen line.
-/

@[expose] public section
noncomputable section

universe u v
open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace PaperVerification.CommonIsotropicSubspace

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The usual total isotropy condition, including both arguments in the subspace. -/
def Isotropic (B : BilinForm K V) (U : Submodule K V) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, B x y = 0

/-- An alternating form on an odd-dimensional space has a nonzero radical vector. -/
theorem exists_radical_of_odd [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B : BilinForm K V) (hB : B.IsAlt) (hodd : Odd (finrank K V)) :
    ∃ v : V, v ≠ 0 ∧ ∀ w : V, B v w = 0 := by
  classical
  let b := Module.finBasis K V
  let A := BilinForm.toMatrix b B
  have hskew : A.transpose = -A := by
    ext i j
    simpa only [A, Matrix.transpose_apply, Matrix.neg_apply,
      BilinForm.toMatrix_apply] using (hB.neg_eq (b i) (b j)).symm
  have hdet : A.det = -A.det := by
    calc
      A.det = A.transpose.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det hskew
      _ = -A.det := by rw [Matrix.det_neg]; simp [hodd.neg_one_pow]
  have hz : A.det = 0 := by
    have h : (2 : K) * A.det = 0 := by linear_combination hdet
    exact (mul_eq_zero.mp h).resolve_left h₂
  by_contra h
  have hsep : B.SeparatingLeft := by
    intro v hv
    by_contra hv₀
    exact h ⟨v, hv₀, hv⟩
  exact (Matrix.separatingLeft_iff_det_ne_zero.mp
    (BilinForm.SeparatingLeft.toMatrix hsep b)) hz

/-- A line orthogonal to an isotropic space extends that space isotropically. -/
theorem isotropic_sup_span (B : BilinForm K V) (hB : B.IsAlt)
    {U : Submodule K V} (hU : Isotropic B U) {v : V}
    (hv : ∀ x ∈ U, B v x = 0) : Isotropic B (U ⊔ K ∙ v) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hd
  have hav : B a v = 0 := by rw [← hB.neg_eq v a, hv a ha, neg_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hU a ha c hc, hav, hv c hc, hB.self_eq_zero v, smul_zero, zero_add, add_zero]

/-- The full dimension bound for every pair of alternating forms. -/
theorem exists_common_isotropic [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B C : BilinForm K V) (hB : B.IsAlt) (hC : C.IsAlt) :
    ∃ U : Submodule K V, (finrank K V + 1) / 2 ≤ finrank K U ∧
      Isotropic B U ∧ Isotropic C U := by
  classical
  suffices h : ∀ n : ℕ, ∀ (W : Type v) [AddCommGroup W] [Module K W]
      [FiniteDimensional K W], finrank K W = n →
      ∀ (B C : BilinForm K W), B.IsAlt → C.IsAlt →
      ∃ U : Submodule K W, (n + 1) / 2 ≤ finrank K U ∧
        Isotropic B U ∧ Isotropic C U by
    exact h (finrank K V) V rfl B C hB hC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ hn B C hB hC
    by_cases hn₀ : n = 0
    · subst n
      refine ⟨⊥, by simp [hn₀], ?_, ?_⟩ <;>
        intro x hx y hy <;> simp only [Submodule.mem_bot] at hx hy <;>
        subst x <;> subst y <;> simp
    have step (v : W) (T : Submodule K W) (hv : v ∉ T)
        (hBT : ∀ w : T, B v w = 0) (hCT : ∀ w : T, C v w = 0)
        (hbound : (n + 1) / 2 ≤ (finrank K T + 1) / 2 + 1) :
        ∃ U : Submodule K W, (n + 1) / 2 ≤ finrank K U ∧
          Isotropic B U ∧ Isotropic C U := by
      have hsmall : finrank K T < n := by
        rw [← hn]
        exact Submodule.finrank_lt (by
          intro h
          apply hv
          rw [h]
          exact Submodule.mem_top)
      obtain ⟨U, hdim, hBU, hCU⟩ := ih (finrank K T) hsmall T rfl
        (B.restrict T) (C.restrict T) (fun w ↦ hB w) (fun w ↦ hC w)
      let U' := U.map T.subtype
      have hle : U' ≤ T := by
        rintro _ ⟨x, hx, rfl⟩
        exact x.property
      have hv' : v ∉ U' := fun h ↦ hv (hle h)
      have hB' : Isotropic B U' := by
        rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
        exact hBU x' hx' y' hy'
      have hC' : Isotropic C U' := by
        rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
        exact hCU x' hx' y' hy'
      refine ⟨U' ⊔ K ∙ v, ?_, isotropic_sup_span B hB hB' ?_,
        isotropic_sup_span C hC hC' ?_⟩
      · rw [Submodule.finrank_sup_span_singleton hv']
        have hdim' : finrank K U' = finrank K U := Submodule.finrank_map_subtype_eq T U
        omega
      · exact fun x hx ↦ hBT ⟨x, hle hx⟩
      · exact fun x hx ↦ hCT ⟨x, hle hx⟩
    by_cases hodd : Odd n
    · obtain ⟨v, hv₀, hvB⟩ := exists_radical_of_odd h₂ B hB (by simpa only [hn] using hodd)
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv₀
      let F : W →ₗ[K] K × K := φ.prod (C v)
      let T := LinearMap.ker F
      have hv : v ∉ T := by
        intro hv
        have h := congrArg Prod.fst (show F v = 0 from hv)
        simpa [F, hφ] using h
      have hdim : n ≤ finrank K T + 2 := by
        have hnull := F.finrank_range_add_finrank_ker
        have hle := Submodule.finrank_le (LinearMap.range F)
        simp only [Module.finrank_prod, Module.finrank_self] at hle
        change finrank K (LinearMap.range F) + finrank K T = finrank K W at hnull
        omega
      apply step v T hv (fun w ↦ hvB w) (fun w ↦ ?_) (by omega)
      exact congrArg Prod.snd (show F w = 0 from w.property)
    · obtain ⟨v, hv₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < finrank K W by omega)
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv₀
      let F : W →ₗ[K] K × (K × K) := φ.prod ((B v).prod (C v))
      let T := LinearMap.ker F
      have hv : v ∉ T := by
        intro hv
        have h := congrArg Prod.fst (show F v = 0 from hv)
        simpa [F, hφ] using h
      have hdim : n ≤ finrank K T + 3 := by
        have hnull := F.finrank_range_add_finrank_ker
        have hle := Submodule.finrank_le (LinearMap.range F)
        simp only [Module.finrank_prod, Module.finrank_self] at hle
        change finrank K (LinearMap.range F) + finrank K T = finrank K W at hnull
        omega
      have heven : n % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hodd)
      apply step v T hv (fun w ↦ ?_) (fun w ↦ ?_) (by omega)
      · exact congrArg (fun z : K × (K × K) ↦ z.2.1) (show F w = 0 from w.property)
      · exact congrArg (fun z : K × (K × K) ↦ z.2.2) (show F w = 0 from w.property)

/-- Every allowed number of vectors can be chosen independently and simultaneously
isotropic for the two original forms. -/
theorem exists_common_isotropic_vectors [FiniteDimensional K V] (h₂ : (2 : K) ≠ 0)
    (B C : BilinForm K V) (hB : B.IsAlt) (hC : C.IsAlt)
    (s : ℕ) (hs : s ≤ (finrank K V + 1) / 2) :
    ∃ v : Fin s → V, LinearIndependent K v ∧
      (∀ i j, B (v i) (v j) = 0) ∧ (∀ i j, C (v i) (v j) = 0) := by
  obtain ⟨U, hdim, hBU, hCU⟩ := exists_common_isotropic h₂ B C hB hC
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (hs.trans hdim)
  refine ⟨fun i ↦ (v i : U), hv.map' U.subtype (LinearMap.ker_eq_bot.mpr U.injective_subtype), ?_, ?_⟩
  · exact fun i j ↦ hBU _ (v i).property _ (v j).property
  · exact fun i j ↦ hCU _ (v i).property _ (v j).property

end PaperVerification.CommonIsotropicSubspace
