module

public import Recovery.Unimodular.WeakFano.EffectiveConeDecision
public import TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import TauCeti.Geometry.Convex.Cone.Face.Basic
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set

namespace Unimodular.EffectiveFaces

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- Adjoin the negatives of the proposed face generators. -/
def augmented (u : E → Lattice n) (t : Finset E) :
    E ⊕ {e // e ∈ t} → Lattice n :=
  Sum.elim u (fun e => -u e.val)

/-- An arithmetic face test, with no real-cone membership oracle. -/
def test (u : E → Lattice n) (t : Finset E) : Prop :=
  ∀ e, e ∉ t → EffectiveConeDecision.contains (augmented u t) (-u e) = false

instance (u : E → Lattice n) (t : Finset E) : Decidable (test u t) := by
  unfold test
  infer_instance

def zeroLabels (u : E → Lattice n) : Finset E :=
  Finset.univ.filter (fun e => u e = 0)

/-- Salience is decided by the exact face test for the zero cone. -/
def salientTest (u : E → Lattice n) : Prop := test u (zeroLabels u)

instance (u : E → Lattice n) : Decidable (salientTest u) :=
  inferInstanceAs (Decidable (test u (zeroLabels u)))

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev cone (u : E → Lattice n) : PointedCone ℝ (Ambient n) :=
  PointedCone.hull ℝ (Set.range (fun e => embed (u e)))

def faceCone (u : E → Lattice n) (t : Finset E) : PointedCone ℝ (Ambient n) :=
  PointedCone.hull ℝ ((fun e => embed (u e)) '' (t : Set E))

private def castHom : Lattice n →+ Ambient n where
  toFun := embed
  map_zero' := by ext i; simp [embed]
  map_add' x y := by ext i; simp [embed]

/-- A positive coefficient in a nonnegative integer dependence puts the
negative of that generator in the actual real cone. -/
theorem neg_mem_of_relation (u : E → Lattice n) (c : E → ℕ)
    (h : ∑ e, c e • u e = 0) (e : E) (he : 0 < c e) :
    -embed (u e) ∈ cone u := by
  have hR : ∑ j, (c j : ℝ) • embed (u j) = 0 := by
    simpa only [map_sum, map_nsmul, map_zero, Nat.cast_smul_eq_nsmul,
      castHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
      congrArg (castHom (n := n)) h
  have hs : (∑ j ∈ Finset.univ.erase e, (c j : ℝ) • embed (u j)) +
      (c e : ℝ) • embed (u e) = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ e)]
    exact hR
  have heq : (∑ j ∈ Finset.univ.erase e, (c j : ℝ) • embed (u j)) =
      (c e : ℝ) • (-embed (u e)) := by
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left hs
  have hm : (c e : ℝ) • (-embed (u e)) ∈ cone u := by
    rw [← heq]
    exact (cone u).sum_mem fun j _ => (cone u).smul_mem (Nat.cast_nonneg _)
      (PointedCone.subset_hull ⟨j, rfl⟩)
  have hp : (0 : ℝ) < c e := by exact_mod_cast he
  have hh := (cone u).smul_mem (inv_nonneg.2 hp.le) hm
  simpa only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul] using hh

def realDual (f : Lattice n →+ ℤ) : Ambient n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (f (Pi.single i 1) : ℝ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem realDual_embed (f : Lattice n →+ ℤ) (x : Lattice n) :
    realDual f (embed x) = (f x : ℝ) := by
  rw [EffectiveConeDecision.additive_eq_intPair f x]
  simp [realDual, EffectiveConeDecision.intPair, embed]

/-- Integer Tucker produces a single functional exposing exactly the tested
subset; its existence is derived from the arithmetic decisions. -/
theorem exposing_of_test (u : E → Lattice n) (t : Finset E) (ht : test u t) :
    ∃ f : Lattice n →+ ℤ, (∀ e, 0 ≤ f (u e)) ∧
      (∀ e ∈ t, f (u e) = 0) ∧ (∀ e, e ∉ t → 0 < f (u e)) := by
  obtain ⟨c, f, hc, hf, hp⟩ :=
    TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos (augmented u t)
  have hc0 : ∀ e, e ∉ t → c (Sum.inl e) = 0 := by
    intro e he
    by_contra hn
    have hm := neg_mem_of_relation (augmented u t) c hc (Sum.inl e) (Nat.pos_of_ne_zero hn)
    have hemb : embed (-u e) = -embed (u e) := by ext i; simp [embed]
    have hm' : embed (-u e) ∈ cone (augmented u t) := by
      simpa only [augmented, Sum.elim_inl, hemb] using hm
    have hc' := (EffectiveConeDecision.contains_iff (augmented u t) (-u e)).2 hm'
    rw [ht e he] at hc'
    exact Bool.false_ne_true hc'
  refine ⟨f, fun e => hf (Sum.inl e), ?_, ?_⟩
  · intro e he
    have h₁ := hf (Sum.inl e)
    have h₂ := hf (Sum.inr ⟨e, he⟩)
    change 0 ≤ f (u e) at h₁
    change 0 ≤ f (-u e) at h₂
    rw [map_neg] at h₂
    omega
  · intro e he
    have hh := hp (Sum.inl e)
    simpa only [hc0 e he, Nat.cast_zero, zero_add, augmented, Sum.elim_inl] using hh

/-- Soundness includes exact saturation among the input generators. -/
theorem test_sound (u : E → Lattice n) (t : Finset E) (ht : test u t) :
    (faceCone u t).IsFaceOf (cone u) ∧
      (∀ e, embed (u e) ∈ faceCone u t ↔ e ∈ t) := by
  obtain ⟨f, hf, hz, hp⟩ := exposing_of_test u t ht
  let φ := realDual f
  have hφ : ∀ x ∈ cone u, 0 ≤ φ x :=
    EffectiveConeDecision.nonneg_on_hull u φ
      (fun e => by dsimp [φ]; rw [realDual_embed]; exact_mod_cast hf e)
  have hz' : ∀ e, φ (embed (u e)) = 0 ↔ e ∈ t := by
    intro e
    dsimp [φ]
    rw [realDual_embed, Int.cast_eq_zero]
    constructor
    · intro he
      by_contra ht'
      have := hp e ht'
      omega
    · exact hz e
  let G := cone u ⊓ PointedCone.ofSubmodule (LinearMap.ker φ)
  have hG : G.IsFaceOf (cone u) := PointedCone.isFaceOf_inf_ker hφ
  have hm : ∀ e, embed (u e) ∈ G ↔ e ∈ t := by
    intro e
    constructor
    · intro he
      exact (hz' e).1 he.2
    · intro he
      exact ⟨PointedCone.subset_hull ⟨e, rfl⟩, (hz' e).2 he⟩
  have heq : G = faceCone u t := by
    have hgen : G = PointedCone.hull ℝ
        ((fun e => embed (u e)) '' {e | embed (u e) ∈ G}) :=
      (show (cone u).Face from ⟨G, hG⟩).eq_hull_image rfl
    rw [hgen]
    unfold faceCone
    congr 1
    congr 1
    exact Set.ext hm
  exact ⟨heq ▸ hG, fun e => by rw [← heq]; exact hm e⟩

/-- The augmented cone is the set of differences of an original-cone point
and a proposed-face point. -/
theorem augmented_decomposition (u : E → Lattice n) (t : Finset E)
    {x : Ambient n} (hx : x ∈ cone (augmented u t)) :
    ∃ a ∈ cone u, ∃ b ∈ faceCone u t, x = a - b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    cases j with
    | inl e =>
      exact ⟨embed (u e), PointedCone.subset_hull ⟨e, rfl⟩,
        0, (faceCone u t).zero_mem, by simp [augmented]⟩
    | inr e =>
      exact ⟨0, (cone u).zero_mem, embed (u e.val),
        PointedCone.subset_hull ⟨e.val, e.property, rfl⟩, by ext i; simp [augmented, embed]⟩
  | zero => exact ⟨0, (cone u).zero_mem, 0, (faceCone u t).zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, hx⟩ := hx
    obtain ⟨c, hc, d, hd, hy⟩ := hy
    exact ⟨a + c, (cone u).add_mem ha hc, b + d, (faceCone u t).add_mem hb hd,
      by rw [hx, hy]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, b, hb, hx⟩ := hx
    refine ⟨(c : ℝ) • a, (cone u).smul_mem c.property ha,
      (c : ℝ) • b, (faceCone u t).smul_mem c.property hb, ?_⟩
    change (c : ℝ) • x = (c : ℝ) • a - (c : ℝ) • b
    rw [hx, smul_sub]

/-- Completeness of the same finite-input arithmetic test. -/
theorem test_complete (u : E → Lattice n) (t : Finset E)
    (hF : (faceCone u t).IsFaceOf (cone u))
    (hsat : ∀ e, embed (u e) ∈ faceCone u t ↔ e ∈ t) : test u t := by
  intro e he
  cases hh : EffectiveConeDecision.contains (augmented u t) (-u e) with
  | false => rfl
  | true =>
    exfalso
    have hm := (EffectiveConeDecision.contains_iff (augmented u t) (-u e)).1 hh
    obtain ⟨a, ha, b, hb, hab⟩ := augmented_decomposition u t hm
    have hneg : embed (-u e) = -embed (u e) := by ext i; simp [embed]
    rw [hneg] at hab
    have heq : embed (u e) + a = b := by
      apply eq_of_sub_eq_zero
      calc
        embed (u e) + a - b = embed (u e) + (a - b) := by abel
        _ = embed (u e) + -embed (u e) := by rw [← hab]
        _ = 0 := add_neg_cancel _
    exact he ((hsat e).1 (hF.mem_of_add_mem_left
      (PointedCone.subset_hull ⟨e, rfl⟩) ha (by rw [heq]; exact hb)))

/-- Exact equivalence to a literal geometric face and its complete set of
input generators, in every dimension and without simpliciality assumptions. -/
theorem test_iff (u : E → Lattice n) (t : Finset E) :
    test u t ↔ (faceCone u t).IsFaceOf (cone u) ∧
      (∀ e, embed (u e) ∈ faceCone u t ↔ e ∈ t) :=
  ⟨test_sound u t, fun h => test_complete u t h.1 h.2⟩

theorem faceCone_zeroLabels (u : E → Lattice n) :
    faceCone u (zeroLabels u) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.2
  rintro x ⟨e, he, rfl⟩
  have hz : u e = 0 := (Finset.mem_filter.1 he).2
  change embed (u e) = 0
  rw [hz]
  funext i
  change ((0 : ℤ) : ℝ) = 0
  exact Int.cast_zero

/-- The salience decision is exact even when the integer input contains zero
vectors, repetitions, lines, or does not span the ambient space. -/
theorem salientTest_iff (u : E → Lattice n) :
    salientTest u ↔ (cone u : ConvexCone ℝ (Ambient n)).Salient := by
  have hzero : ∀ e, embed (u e) ∈ faceCone u (zeroLabels u) ↔ e ∈ zeroLabels u := by
    intro e
    rw [faceCone_zeroLabels]
    simp only [Submodule.mem_bot, zeroLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      ext i
      have hi := congrFun h i
      change (u e i : ℝ) = 0 at hi
      exact_mod_cast hi
    · intro h
      rw [h]
      funext i
      change ((0 : ℤ) : ℝ) = 0
      exact Int.cast_zero
  rw [salientTest, test_iff]
  constructor
  · rintro ⟨hF, _⟩ x hx hn hnx
    rw [faceCone_zeroLabels] at hF
    have h := hF.mem_of_add_mem_left hx hnx (by simp)
    change x = 0 at h
    exact hn h
  · intro hs
    refine ⟨?_, hzero⟩
    rw [faceCone_zeroLabels]
    exact ConvexCone.Salient.bot_isFaceOf (C := cone u) hs

end
end Unimodular.EffectiveFaces

#print axioms Unimodular.EffectiveFaces.test
#print axioms Unimodular.EffectiveFaces.test_iff
#print axioms Unimodular.EffectiveFaces.salientTest_iff
#check Unimodular.EffectiveFaces.test_iff
