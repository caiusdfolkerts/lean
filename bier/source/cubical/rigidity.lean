import cubical.pinning
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Infinitesimal rigidity, gluing, and coning

These definitions use actual infinitesimal Euclidean motions, rather than a
nullity bound which can become misleading for degenerate placements.
The graph may have any vertex type; finiteness is needed only for later rank
arguments and is not needed by the elementary rigidity lemmas here.
-/

namespace Cubical.Rigidity

open Module
open scoped InnerProductSpace

variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The defining skew-adjoint identity for an infinitesimal rotation. -/
def IsSkew (A : E →ₗ[ℝ] E) : Prop :=
  ∀ x y : E, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ

/-- Infinitesimal preservation of the length of every edge. -/
def IsMotion (G : SimpleGraph V) (p u : V → E) : Prop :=
  ∀ a b, G.Adj a b → ⟪p a - p b, u a - u b⟫_ℝ = 0

/-- Restriction of an ambient Euclidean infinitesimal motion. -/
def IsTrivialMotion (p u : V → E) : Prop :=
  ∃ t : E, ∃ A : E →ₗ[ℝ] E, IsSkew A ∧ ∀ v, u v = t + A (p v)

/-- All infinitesimal motions are Euclidean motions. -/
def IsRigid (G : SimpleGraph V) (p : V → E) : Prop :=
  ∀ u : V → E, IsMotion G p u → IsTrivialMotion p u

theorem IsSkew.inner_self {A : E →ₗ[ℝ] E} (hA : IsSkew A) (x : E) :
    ⟪x, A x⟫_ℝ = 0 := by
  have h := hA x x
  have hc := real_inner_comm x (A x)
  linarith

theorem IsSkew.sub {A B : E →ₗ[ℝ] E} (hA : IsSkew A) (hB : IsSkew B) :
    IsSkew (A - B) := by
  intro x y
  simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right, hA x y, hB x y]
  ring

theorem IsTrivialMotion.isMotion {G : SimpleGraph V} {p u : V → E}
    (hu : IsTrivialMotion p u) : IsMotion G p u := by
  obtain ⟨t, A, hA, hu⟩ := hu
  intro a b _
  rw [hu a, hu b]
  have hsub : t + A (p a) - (t + A (p b)) = A (p a - p b) := by
    rw [map_sub]
    abel
  rw [hsub]
  exact hA.inner_self _

theorem IsMotion.sub_const {G : SimpleGraph V} {p u : V → E}
    (hu : IsMotion G p u) (t : E) : IsMotion G p (fun v => u v - t) := by
  intro a b hab
  have h : (u a - t) - (u b - t) = u a - u b := by abel
  rw [h]
  exact hu a b hab

theorem IsRigid.mono {G H : SimpleGraph V} (hGH : G ≤ H) {p : V → E}
    (hG : IsRigid G p) : IsRigid H p := by
  intro u hu
  exact hG u (fun a b hab => hu a b (hGH hab))

/-- An ambient rigid motion is uniquely determined by `dim E` affinely
independent point values. This includes a facet's vertices. -/
theorem trivial_motion_agreement
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t s : E) (A B : E →ₗ[ℝ] E)
    (hA : IsSkew A) (hB : IsSkew B) (q : ι → E)
    (hq : AffineIndependent ℝ q) (hcard : finrank ℝ E ≤ Fintype.card ι)
    (hagree : ∀ i, t + A (q i) = s + B (q i)) :
    ∀ x, t + A x = s + B x := by
  have hpin : ∀ i, (t - s) + (A - B) (q i) = 0 := by
    intro i
    simp only [LinearMap.sub_apply]
    calc
      (t - s) + (A (q i) - B (q i)) = (t + A (q i)) - (s + B (q i)) := by abel
      _ = 0 := sub_eq_zero.mpr (hagree i)
  have hzero := Pinning.rigid_motion_pinned_on_affine_independent
    (A - B) (t - s) q (hA.sub hB) hq hcard hpin
  intro x
  have h := hzero.2.2 x
  simp only [LinearMap.sub_apply] at h
  apply sub_eq_zero.mp
  convert h using 1
  abel

/-- Gluing two rigid restrictions with an affinely independent overlap of
at least the ambient dimension. All edges are edges of the ambient graph. -/
theorem IsRigid.union
    [FiniteDimensional ℝ E] {G : SimpleGraph V} {p : V → E}
    (S T : Set V)
    (hS : IsRigid (G.induce S) (fun v : S => p v))
    (hT : IsRigid (G.induce T) (fun v : T => p v))
    {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → V)
    (hqS : ∀ i, q i ∈ S) (hqT : ∀ i, q i ∈ T)
    (hq : AffineIndependent ℝ (p ∘ q))
    (hcard : finrank ℝ E ≤ Fintype.card ι) :
    IsRigid (G.induce (S ∪ T)) (fun v : ↥(S ∪ T) => p v) := by
  intro u hu
  let uS : S → E := fun v => u ⟨v, Or.inl v.property⟩
  let uT : T → E := fun v => u ⟨v, Or.inr v.property⟩
  have huS : IsMotion (G.induce S) (fun v : S => p v) uS := by
    intro a b hab
    exact hu ⟨a, Or.inl a.property⟩ ⟨b, Or.inl b.property⟩ hab
  have huT : IsMotion (G.induce T) (fun v : T => p v) uT := by
    intro a b hab
    exact hu ⟨a, Or.inr a.property⟩ ⟨b, Or.inr b.property⟩ hab
  obtain ⟨s, A, hA, huA⟩ := hS uS huS
  obtain ⟨t, B, hB, huB⟩ := hT uT huT
  have hagree : ∀ i, s + A (p (q i)) = t + B (p (q i)) := by
    intro i
    rw [← huA ⟨q i, hqS i⟩, ← huB ⟨q i, hqT i⟩]
  have hall := trivial_motion_agreement s t A B hA hB (p ∘ q) hq hcard hagree
  refine ⟨s, A, hA, ?_⟩
  intro v
  rcases v.property with hv | hv
  · exact huA ⟨v, hv⟩
  · exact (huB ⟨v, hv⟩).trans (hall (p v)).symm

/-- The graph cone with a fresh apex `none`. -/
def coneGraph (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some a, some b => G.Adj a b
  symm := ⟨by
    intro a b hab
    cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

/-- The usual cone placement: the apex is zero and the old placement lies
in the affine hyperplane with last coordinate one. -/
noncomputable def conePlacement (p : V → E) : Option V → WithLp 2 (E × ℝ)
  | none => 0
  | some v => WithLp.toLp 2 (p v, 1)

/-- The skew block matrix associated with a base translation and rotation. -/
noncomputable def coneSkew (A : E →ₗ[ℝ] E) (t : E) :
    WithLp 2 (E × ℝ) →ₗ[ℝ] WithLp 2 (E × ℝ) where
  toFun x := WithLp.toLp 2 (A (WithLp.ofLp x).1 + (WithLp.ofLp x).2 • t,
    -⟪t, (WithLp.ofLp x).1⟫_ℝ)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add,
      map_add, add_smul, inner_add_right]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    simp [map_smul, smul_add, smul_smul, inner_smul_right]

theorem coneSkew_isSkew {A : E →ₗ[ℝ] E} (hA : IsSkew A) (t : E) :
    IsSkew (coneSkew A t) := by
  intro x y
  simp only [coneSkew, LinearMap.coe_mk, AddHom.coe_mk, WithLp.prod_inner_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hA (WithLp.ofLp x).1 (WithLp.ofLp y).1,
    real_inner_comm (WithLp.ofLp x).1 t]
  simp only [RCLike.conj_to_real, inner_neg_left, inner_neg_right, Real.inner_apply]
  ring

/-- Coning an infinitesimally rigid framework preserves rigidity, in one
higher Euclidean dimension. The proof is an explicit block-matrix argument. -/
theorem IsRigid.cone {G : SimpleGraph V} {p : V → E}
    (hp : IsRigid G p) : IsRigid (coneGraph G) (conePlacement p) := by
  intro u hu
  let v : Option V → WithLp 2 (E × ℝ) := fun a => u a - u none
  have hv : IsMotion (coneGraph G) (conePlacement p) v := hu.sub_const (u none)
  have hv0 : v none = 0 := sub_self _
  let w : V → E := fun a => (WithLp.ofLp (v (some a))).1
  have hw : IsMotion G p w := by
    intro a b hab
    have h := hv (some a) (some b) hab
    simpa [conePlacement, WithLp.prod_inner_apply, w] using h
  obtain ⟨t, A, hA, hwA⟩ := hp w hw
  have hlast : ∀ a, (WithLp.ofLp (v (some a))).2 = -⟪t, p a⟫_ℝ := by
    intro a
    have h := hv (some a) none trivial
    simp [conePlacement, hv0, WithLp.prod_inner_apply] at h
    have hwval : (v (some a)).fst = t + A (p a) := hwA a
    rw [hwval, inner_add_right, hA.inner_self] at h
    rw [real_inner_comm t (p a)] at h
    change (v (some a)).snd = -⟪t, p a⟫_ℝ
    linarith
  refine ⟨u none, coneSkew A t, coneSkew_isSkew hA t, ?_⟩
  intro a
  cases a with
  | none => simp [conePlacement]
  | some a =>
    have hvval : v (some a) = coneSkew A t (conePlacement p (some a)) := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [coneSkew, conePlacement, w, add_comm] using hwA a
      · simpa [coneSkew, conePlacement] using hlast a
    change u (some a) = u none + coneSkew A t (conePlacement p (some a))
    rw [← hvval]
    dsimp [v]
    abel

end Cubical.Rigidity
