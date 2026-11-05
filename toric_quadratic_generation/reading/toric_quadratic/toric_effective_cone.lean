module
public import PaperVerification.ToricNefCone
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Lemmas
@[expose] public section

/-!
# The actual dual effective cone and extremal primitive relations

The effective cone is the cone of balanced ray coefficients nonnegative on
all genuinely convex support functions. Extremality means that the ordinary
nonnegative ray is a face of this cone, using Mathlib's face definition.

The replacement theorem is proved directly: a hypothetical missing cone
contains a primitive collection Q; both its relation and the difference from
the original relation are effective. Extremality forces proportionality,
which contradicts the omitted positive coefficient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Sum an indicator over a larger finite set without changing its value. -/
theorem sum_indicator_of_subset {α E : Type*} [DecidableEq α] [AddCommMonoid E]
    {s t : Finset α} (hst : s ⊆ t) (f : α → E) :
    (∑ v ∈ t, if v ∈ s then f v else 0) = ∑ v ∈ s, f v := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hst h, h⟩⟩
  · intro v hv
    rfl

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Real coefficients on precisely the finite set of actual primitive rays. -/
abbrev RaySpace := {v : Lattice n // v ∈ «Σ».rays} → ℝ

/-- The genuine vector represented by finite real ray coefficients. -/
def rayCombination : «Σ».RaySpace →ₗ[ℝ] Ambient n where
  toFun c := ∑ v : «Σ».rays, c v • embed n (v : Lattice n)
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

/-- The ordinary finite divisor-relation pairing. -/
def rayPairing (a : Lattice n → ℝ) : «Σ».RaySpace →ₗ[ℝ] ℝ where
  toFun c := ∑ v : «Σ».rays, c v * a v
  map_add' c d := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

/-- The dual cone to genuine nef support data, inside the space of balanced
relations. No primitive-generation assertion is built into this definition. -/
def effectiveCone : PointedCone ℝ «Σ».RaySpace :=
  PointedCone.ofConeComb
    {c | «Σ».rayCombination c = 0 ∧ ∀ a, «Σ».IsNef a → 0 ≤ «Σ».rayPairing a c}
    ⟨0, by simp, by simp⟩ (by
      rintro c ⟨hc, hcp⟩ d ⟨hd, hdp⟩ t ht u hu
      refine ⟨by simp only [map_add, map_smul, hc, hd, smul_zero, add_zero], ?_⟩
      intro a ha
      simp only [map_add, map_smul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ht (hcp a ha)) (mul_nonneg hu (hdp a ha)))

theorem mem_effectiveCone_iff (c : «Σ».RaySpace) :
    c ∈ «Σ».effectiveCone ↔
      «Σ».rayCombination c = 0 ∧ ∀ a, «Σ».IsNef a → 0 ≤ «Σ».rayPairing a c := Iff.rfl

/-- A balanced relation whose negative coefficients are confined to a single
actual cone is effective. This is the convex-support proof of Casagrande 1.4. -/
theorem effective_of_negative_support_in_cone (c : «Σ».RaySpace)
    (hbalance : «Σ».rayCombination c = 0) (s : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hpositive : ∀ v : «Σ».rays, (v : Lattice n) ∉ s → 0 ≤ c v) :
    c ∈ «Σ».effectiveCone := by
  refine ⟨hbalance, ?_⟩
  intro a ha
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  have hz : (∑ v : «Σ».rays, c v * ℓ (embed n v)) = 0 := by
    have h := congrArg ℓ hbalance
    simpa only [rayCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
      map_smul, smul_eq_mul, map_zero] using h
  have hp : «Σ».rayPairing a c =
      ∑ v : «Σ».rays, c v * (a v - ℓ (embed n v)) := by
    simp only [rayPairing, LinearMap.coe_mk, AddHom.coe_mk,
      mul_sub, Finset.sum_sub_distrib, hz, sub_zero]
  rw [hp]
  apply Finset.sum_nonneg
  intro v hv
  by_cases hvs : (v : Lattice n) ∈ s
  · rw [he v hvs, sub_self, mul_zero]
  · exact mul_nonneg (hpositive v hvs) (sub_nonneg.mpr (hle v v.property))

/-- Every noncone finite ray set contains a genuine primitive collection. -/
theorem exists_primitiveCollection_subset {s : Finset (Lattice n)}
    (hsrays : s ⊆ «Σ».rays) (hs : s ∉ «Σ».cones) :
    ∃ Q, Q ⊆ s ∧ «Σ».IsPrimitiveCollection Q := by
  let T := s.powerset.filter (fun Q => Q ∉ «Σ».cones)
  have hsT : s ∈ T := by simp [T, hs]
  obtain ⟨Q, hQT, hmin⟩ := Set.exists_min_image (T : Set (Finset (Lattice n)))
    Finset.card T.finite_toSet ⟨s, hsT⟩
  obtain ⟨hQs, hQnot⟩ := Finset.mem_filter.mp hQT
  have hQsub : Q ⊆ s := Finset.mem_powerset.mp hQs
  refine ⟨Q, hQsub, hQsub.trans hsrays, hQnot, ?_⟩
  intro U hU
  by_contra hUnot
  have hUT : U ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp hU).1 hQsub),
      hUnot⟩
  exact (not_le_of_gt (Finset.card_lt_card hU)) (hmin U hUT)

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- The actual coefficient vector of the displayed primitive relation. -/
def vector : «Σ».RaySpace := fun v =>
  (if (v : Lattice n) ∈ R.positive then 1 else 0) -
  if (v : Lattice n) ∈ R.negative then (R.coefficient v : ℝ) else 0

theorem vector_eq_one {v : «Σ».rays} (hv : (v : Lattice n) ∈ R.positive) :
    R.vector v = 1 := by
  have hn : (v : Lattice n) ∉ R.negative :=
    fun h => Finset.disjoint_left.mp R.disjoint hv h
  simp only [vector, if_pos hv, if_neg hn, sub_zero]

theorem vector_le_one (v : «Σ».rays) : R.vector v ≤ 1 := by
  simp only [vector]
  split_ifs <;> have h := Nat.cast_nonneg (α := ℝ) (R.coefficient v) <;> linarith

theorem vector_nonpos_of_not_positive {v : «Σ».rays}
    (hv : (v : Lattice n) ∉ R.positive) : R.vector v ≤ 0 := by
  simp only [vector, if_neg hv, zero_sub]
  split_ifs <;> simp

theorem vector_ne_zero : R.vector ≠ 0 := by
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty R.primitive
  let j : «Σ».rays := ⟨v, R.primitive.1 hv⟩
  intro he
  have h := congrFun he j
  rw [R.vector_eq_one hv] at h
  norm_num at h

/-- The coefficient-vector pairing equals the displayed primitive degree. -/
theorem vector_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Lattice n → E) :
    (∑ v : «Σ».rays, R.vector v • f v) =
      (∑ v ∈ R.positive, f v) -
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) • f v := by
  simp only [vector, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib]
  have hsum (g : Lattice n → E) :
      (∑ v : «Σ».rays, g v) = ∑ v ∈ «Σ».rays, g v :=
    (Finset.sum_subtype «Σ».rays (fun _ => Iff.rfl) g).symm
  rw [hsum (fun v => if v ∈ R.positive then f v else 0),
    hsum (fun v => if v ∈ R.negative then (R.coefficient v : ℝ) • f v else 0),
    sum_indicator_of_subset R.primitive.1]
  congr 1
  exact sum_indicator_of_subset
    (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)
    (fun v => (R.coefficient v : ℝ) • f v)

theorem vector_balanced : «Σ».rayCombination R.vector = 0 := by
  change (∑ v : «Σ».rays, R.vector v • embed n v) = 0
  rw [R.vector_sum]
  apply sub_eq_zero.mpr
  have h := congrArg (embed n) R.equation
  simpa only [map_sum, embed_int_smul, Int.cast_natCast] using h

theorem vector_pairing (a : Lattice n → ℝ) :
    «Σ».rayPairing a R.vector = R.degree a := by
  exact R.vector_sum a

theorem vector_effective : R.vector ∈ «Σ».effectiveCone := by
  refine ⟨R.vector_balanced, ?_⟩
  intro a ha
  rw [R.vector_pairing]
  exact R.degree_nonneg_of_nef ha

/-- Extremality is the literal Mathlib face property of the genuine
nonnegative ray in the dual effective cone. -/
def IsExtremal : Prop :=
  (PointedCone.hull ℝ ({R.vector} : Set «Σ».RaySpace)).IsFaceOf «Σ».effectiveCone

/-- Every extremal primitive relation satisfies the full Casagrande cone
replacement condition. No contraction geometry is assumed in this proof. -/
theorem combinatoriallyContractible_of_extremal (hR : R.IsExtremal) :
    R.IsCombinatoriallyContractible := by
  intro ν hν hdis hfocus x hx
  let s := R.positive.erase x ∪ R.negative ∪ ν
  by_contra hs
  have hsrays : s ⊆ «Σ».rays := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact R.primitive.1 (Finset.mem_of_mem_erase hv)
      · exact «Σ».ray_mem_of_mem_cone R.negative_cone hv
    · exact «Σ».ray_mem_of_mem_cone hν hv
  obtain ⟨Q, hQs, hQ⟩ := «Σ».exists_primitiveCollection_subset hsrays hs
  obtain ⟨S, hSQ⟩ := «Σ».exists_primitiveRelation hQ
  have hSsub : S.positive ⊆ s := by simpa only [hSQ] using hQs
  have hbalance : «Σ».rayCombination (R.vector - S.vector) = 0 := by
    rw [map_sub, R.vector_balanced, S.vector_balanced, sub_self]
  have heff : R.vector - S.vector ∈ «Σ».effectiveCone := by
    apply «Σ».effective_of_negative_support_in_cone _ hbalance (R.negative ∪ ν) hfocus
    intro v hv
    have hvneg : (v : Lattice n) ∉ R.negative :=
      fun h => hv (Finset.mem_union_left _ h)
    by_cases hvpos : (v : Lattice n) ∈ R.positive
    · change 0 ≤ R.vector v - S.vector v
      rw [R.vector_eq_one hvpos]
      exact sub_nonneg.mpr (S.vector_le_one v)
    · have hvS : (v : Lattice n) ∉ S.positive := by
        intro h
        rcases Finset.mem_union.mp (hSsub h) with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact hvpos (Finset.mem_of_mem_erase h)
          · exact hvneg h
        · exact hv (Finset.mem_union_right _ h)
      have hz : R.vector v = 0 := by simp only [vector, if_neg hvpos, if_neg hvneg, sub_self]
      change 0 ≤ R.vector v - S.vector v
      rw [hz]
      linarith [S.vector_nonpos_of_not_positive hvS]
  have hsum : S.vector + (R.vector - S.vector) ∈
      PointedCone.hull ℝ ({R.vector} : Set «Σ».RaySpace) := by
    have heq : S.vector + (R.vector - S.vector) = R.vector := by abel
    rw [heq]
    exact PointedCone.subset_hull (Set.mem_singleton R.vector)
  have hSin := hR.mem_of_add_mem_left S.vector_effective heff hsum
  obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hSin
  have hxneg : x ∉ R.negative := fun h => Finset.disjoint_left.mp R.disjoint hx h
  have hxν : x ∉ ν := by
    intro h
    exact Finset.disjoint_left.mp hdis h (Finset.mem_union_left _ hx)
  have hxS : x ∉ S.positive := by
    intro h
    have hsx := hSsub h
    simp only [s, Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, hxneg, hxν, or_self] at hsx
  let j : «Σ».rays := ⟨x, R.primitive.1 hx⟩
  have hcoord := congrFun he j
  have hnonpos := S.vector_nonpos_of_not_positive (v := j) hxS
  simp only [Pi.smul_apply, smul_eq_mul, R.vector_eq_one (v := j) hx, mul_one] at hcoord
  have ht0 : t = 0 := by linarith
  rw [ht0, zero_smul] at he
  exact S.vector_ne_zero he.symm

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
