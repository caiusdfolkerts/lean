module
public import PaperVerification.ToricPrimitiveRelations
public import Mathlib.Tactic.Linarith
@[expose] public section
/-!
# Convex support data on actual smooth complete fans

Nefness is stated as feasibility of genuine linear supporting functions on
every actual cone. Strict support records strict inequalities on precisely
the rays outside that cone. Neither definition includes a primitive-relation
criterion; its forward implication is proved below, and its converse requires
a separate terminating reduction argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Convex support coefficients: each cone admits a real linear function
agreeing on that cone's primitive rays and bounded above on all fan rays. -/
def IsNef (a : Lattice n → ℝ) : Prop :=
  ∀ s ∈ «Σ».cones, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
    (∀ v ∈ s, ℓ (embed n v) = a v) ∧
    (∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v)

/-- Strict convex support on every actual cone. Rays outside that cone have
strict supporting slack. This is independent of primitive relations. -/
def IsStrictSupport (a : Lattice n → ℝ) : Prop :=
  ∀ s ∈ «Σ».cones, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
    (∀ v ∈ s, ℓ (embed n v) = a v) ∧
    (∀ v ∈ «Σ».rays, v ∉ s → ℓ (embed n v) < a v)

theorem ray_mem_of_mem_cone {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    {v : Lattice n} (hv : v ∈ s) : v ∈ «Σ».rays :=
  («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩

theorem IsStrictSupport.isNef {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) : «Σ».IsNef a := by
  intro s hs
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  refine ⟨ℓ, he, ?_⟩
  intro v hv
  by_cases hvs : v ∈ s
  · exact (he v hvs).le
  · exact (hlt v hv hvs).le

theorem IsStrictSupport.smul {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) {t : ℝ} (ht : 0 < t) :
    «Σ».IsStrictSupport (t • a) := by
  intro s hs
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  refine ⟨t • ℓ, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, Pi.smul_apply, he v hv]
  · intro v hv hvs
    exact mul_lt_mul_of_pos_left (hlt v hv hvs) ht

theorem isNef_zero : «Σ».IsNef (0 : Lattice n → ℝ) := by
  intro s hs
  exact ⟨0, by simp, by simp⟩

theorem IsNef.add {a b : Lattice n → ℝ}
    (ha : «Σ».IsNef a) (hb : «Σ».IsNef b) : «Σ».IsNef (a + b) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  obtain ⟨k, ke, kle⟩ := hb s hs
  refine ⟨ℓ + k, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.add_apply, Pi.add_apply, he v hv, ke v hv]
  · intro v hv
    exact add_le_add (hle v hv) (kle v hv)

theorem IsNef.smul {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    {t : ℝ} (ht : 0 ≤ t) : «Σ».IsNef (t • a) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  refine ⟨t • ℓ, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, Pi.smul_apply, he v hv]
  · intro v hv
    exact mul_le_mul_of_nonneg_left (hle v hv) ht

theorem isNef_linear (ℓ : Ambient n →ₗ[ℝ] ℝ) :
    «Σ».IsNef (fun v => ℓ (embed n v)) := by
  intro s hs
  exact ⟨ℓ, fun _ _ => rfl, fun _ _ => le_rfl⟩

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A genuine balanced primitive relation annihilates every global linear
function, by applying that function to its lattice equation. -/
theorem degree_linear (ℓ : Ambient n →ₗ[ℝ] ℝ) :
    R.degree (fun v => ℓ (embed n v)) = 0 := by
  have he := congrArg ℓ (congrArg (embed n) R.equation)
  have hsum : (∑ v ∈ R.positive, ℓ (embed n v)) =
      ∑ v ∈ R.negative, (R.coefficient v : ℝ) * ℓ (embed n v) := by
    simpa only [map_sum, embed_int_smul, Int.cast_natCast, map_smul,
      smul_eq_mul] using he
  exact sub_eq_zero.mpr hsum

/-- Once a linear support is chosen on the focus cone, the primitive degree
is the sum of its actual supporting slacks on the positive collection. -/
theorem degree_eq_sum_slack (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ v ∈ R.negative, ℓ (embed n v) = a v) :
    R.degree a = ∑ v ∈ R.positive, (a v - ℓ (embed n v)) := by
  have hz := R.degree_linear ℓ
  have hn : (∑ v ∈ R.negative,
      (R.coefficient v : ℝ) * ℓ (embed n v)) =
      ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [he v hv]
  simp only [degree] at hz ⊢
  rw [Finset.sum_sub_distrib]
  rw [hn] at hz
  linarith

/-- Convex support is nonnegative on every primitive relation. -/
theorem degree_nonneg_of_nef {a : Lattice n → ℝ} (ha : «Σ».IsNef a) :
    0 ≤ R.degree a := by
  obtain ⟨ℓ, he, hle⟩ := ha R.negative R.negative_cone
  rw [R.degree_eq_sum_slack a ℓ he]
  apply Finset.sum_nonneg
  intro v hv
  exact sub_nonneg.mpr (hle v (R.primitive.1 hv))

/-- Strict support has strictly positive degree on every primitive relation.
Disjointness of the two ray sets is used as a proved theorem. -/
theorem degree_pos_of_strictSupport {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) : 0 < R.degree a := by
  obtain ⟨ℓ, he, hlt⟩ := ha R.negative R.negative_cone
  rw [R.degree_eq_sum_slack a ℓ he]
  apply Finset.sum_pos
  · intro v hv
    apply sub_pos.mpr
    exact hlt v (R.primitive.1 hv)
      (fun hneg => Finset.disjoint_left.mp R.disjoint hv hneg)
  · exact «Σ».primitiveCollection_nonempty R.primitive

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
