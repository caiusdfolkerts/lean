import CommAlg.Polymatroid.Minkowski
import CommAlg.Polymatroid.RankGreedy

/-! # Products and powers of actual polymatroidal polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem monomialIdeal_mul (k : Type*) [CommSemiring k] (B C : Family V) :
    monomialIdeal k B * monomialIdeal k C =
      monomialIdeal k ((B.product C).image (fun bc => bc.1 + bc.2)) := by
  unfold monomialIdeal
  rw [Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨b + c, Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    refine Set.mem_mul.mpr ⟨MvPolynomial.monomial b 1, ⟨b, hb, rfl⟩,
      MvPolynomial.monomial c 1, ⟨c, hc, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]

theorem rankIdeal_add (k : Type*) [CommSemiring k] (g h : RankFunction V) :
    rankIdeal k (g.add h) = rankIdeal k g * rankIdeal k h := by
  rw [rankIdeal, rankBases_add, ← monomialIdeal_mul]
  rfl

theorem RankFunction.ext_fun {g h : RankFunction V} (he : ∀ U, g U = h U) : g = h := by
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      exact funext he

theorem rankIdeal_scale_zero (k : Type*) [CommSemiring k] (g : RankFunction V) :
    rankIdeal k (g.scale 0) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hb : (0 : Exponent V) ∈ rankBases (g.scale 0) := by
    rw [mem_rankBases]
    constructor
    · simp [RankFunction.scale]
    · intro U; simp [subsetSum, RankFunction.scale]
  have hm : MvPolynomial.monomial (0 : Exponent V) (1 : k) ∈ rankIdeal k (g.scale 0) :=
    Ideal.subset_span ⟨0, hb, rfl⟩
  simpa using hm

theorem rankIdeal_scale (k : Type*) [CommSemiring k] (g : RankFunction V) (s : ℕ) :
    rankIdeal k (g.scale s) = (rankIdeal k g) ^ s := by
  induction s with
  | zero => simpa using rankIdeal_scale_zero k g
  | succ s ih =>
    have hs : g.scale (s + 1) = (g.scale s).add g := by
      apply RankFunction.ext_fun
      intro U
      simp [RankFunction.scale, RankFunction.add, Nat.add_mul]
    rw [hs, rankIdeal_add, ih, pow_succ]

theorem family_eq_of_contains_iff {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (he : ∀ a, Contains B a ↔ Contains C a) : B = C := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mp ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mpr ⟨b, hb, le_rfl⟩
    have hca := hB c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mpr ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mp ⟨b, hb, le_rfl⟩
    have hca := hC c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]

theorem rankIdeal_injective (k : Type*) [CommSemiring k] [Nontrivial k] :
    Function.Injective (rankIdeal (V := V) k) := by
  intro g h he
  apply rankBases_injective
  apply family_eq_of_contains_iff (rankBases_equigenerated g).antichain
    (rankBases_equigenerated h).antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k)]
  change (MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g) ↔ _
  rw [he]
  rfl

end CommAlg.Polymatroid
