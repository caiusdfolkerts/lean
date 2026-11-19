module
public import graph_foundation.part005

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteBlocks -/
section
set_option autoImplicit false

/-!
# Crossing blocks in the exact finite row ring

The block families below consist of the actual exponent vectors of predecessor
ratios. Their divisibility predicates decompose the genuine coefficient ideal,
and their supports are the disjoint first-crossing sets of the paper.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def finiteChainToNat (w : FiniteMultichain n E m) : Fin m → Fin d → ℕ :=
  fun s => finiteTupleToNat (w.val s).val

lemma finiteChainToNat_mem (w : FiniteMultichain n E m) (s : Fin m) :
    finiteChainToNat w s ∈ finiteTupleImage E :=
  mem_map.mpr ⟨(w.val s).val,(w.val s).property,rfl⟩

lemma finiteChainToNat_monotone (w : FiniteMultichain n E m) : Monotone (finiteChainToNat w) :=
  w.property

def finiteCrosses (w : FiniteMultichain n E m) (s : Fin m) (x : FiniteVariable.{u} n) : Prop :=
  Crosses (finiteChainToNat w) s (finiteVariableEmbedding x)

lemma finiteCrosses_unique {w : FiniteMultichain n E m} {s t : Fin m}
    {x : FiniteVariable.{u} n} (hs : finiteCrosses w s x) (ht : finiteCrosses w t x) : s = t :=
  crosses_unique hs ht

lemma finiteCrosses_below {w : FiniteMultichain n E m} {s : Fin m}
    {x : FiniteVariable.{u} n} (hx : finiteCrosses w s x) :
    x.2.down < (w.val s).val x.1 := hx.1

lemma finiteRatioExponent_embedding {b a : FiniteTuple n} (hba : b ≤ a) :
    (finiteRowExponent n b - finiteRowExponent n a).embDomain finiteVariableEmbedding =
      squareExponent (ratio (finiteTupleToNat b) (finiteTupleToNat a)) := by
  rw [Finsupp.embDomain_tsub,finiteRowExponent_embedding,finiteRowExponent_embedding,
    ← generalRatio_exponent]
  exact congrArg squareExponent (generalRatio_eq_ratio hba)

lemma squareExponent_mono {V : Type*} [DecidableEq V] {g h : Finset V} (hgh : g ⊆ h) :
    squareExponent g ≤ squareExponent h := by
  intro x
  by_cases hx : x ∈ g
  · simp [squareExponent_apply,hx,hgh hx]
  · simp [squareExponent_apply,hx]

def finiteChainCoordinateFamily (w : FiniteMultichain n E m) : Family (FiniteVariable.{u} n) :=
  univ.biUnion fun s => finiteCoordinatePredecessorFamily E (w.val s).val

lemma finiteChainCoordinate_contains_iff (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoordinateFamily w) v ↔ Contains (finiteChainCoefficientFamily n w) v := by
  constructor
  · rintro ⟨b,hb,hbv⟩
    obtain ⟨s,_,hbs⟩ := mem_biUnion.mp hb
    obtain ⟨c,hc,hcv⟩ := (finiteCoordinatePredecessor_contains_iff hE (w.val s).property v).mp
      ⟨b,hbs,hbv⟩
    exact ⟨c,mem_biUnion.mpr ⟨s,mem_univ s,hc⟩,hcv⟩
  · rintro ⟨b,hb,hbv⟩
    obtain ⟨s,_,hbs⟩ := mem_biUnion.mp hb
    obtain ⟨c,hc,hcv⟩ := (finiteCoordinatePredecessor_contains_iff hE (w.val s).property v).mpr
      ⟨b,hbs,hbv⟩
    exact ⟨c,mem_biUnion.mpr ⟨s,mem_univ s,hc⟩,hcv⟩

/-- The ratio family assigned to the indicated crossing step. -/
def finiteBlockFamily (w : FiniteMultichain n E m) (s : Fin m) : Family (FiniteVariable.{u} n) :=
  (E.filter fun b => b ≤ (w.val s).val ∧ b ≠ (w.val s).val ∧
    BlockRatio (finiteTupleImage E) (finiteChainToNat w) s
      (ratio (finiteTupleToNat b) (finiteChainToNat w s))).image
    (fun b => finiteRowExponent n b - finiteRowExponent n (w.val s).val)

lemma finiteBlockFamily_subset_predecessor (w : FiniteMultichain n E m) (s : Fin m) :
    finiteBlockFamily.{u} w s ⊆ finiteCoordinatePredecessorFamily E (w.val s).val := by
  intro v hv
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  obtain ⟨hbE,hba,hne,_⟩ := mem_filter.mp hb
  exact mem_image.mpr ⟨b,mem_filter.mpr ⟨hbE,hba,hne⟩,rfl⟩

lemma finiteBlockFamily_subset_chain (w : FiniteMultichain n E m) (s : Fin m) :
    finiteBlockFamily.{u} w s ⊆ finiteChainCoordinateFamily w := by
  intro v hv
  exact mem_biUnion.mpr ⟨s,mem_univ s,finiteBlockFamily_subset_predecessor w s hv⟩

lemma finiteBlockFamily_variables (w : FiniteMultichain n E m) (s : Fin m)
    {v : Exponent (FiniteVariable.{u} n)} (hv : v ∈ finiteBlockFamily w s)
    (x : FiniteVariable.{u} n) (hx : v x ≠ 0) : finiteCrosses w s x := by
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  obtain ⟨_,hba,_,hblock⟩ := mem_filter.mp hb
  have he := congrArg (fun c : (Fin d × ℕ) →₀ ℕ => c (finiteVariableEmbedding x))
    (finiteRatioExponent_embedding.{u} hba)
  rw [Finsupp.embDomain_apply_self] at he
  have hmem : finiteVariableEmbedding x ∈ ratio (finiteTupleToNat b) (finiteChainToNat w s) := by
    by_contra hn
    apply hx
    change finiteVariableEmbedding x ∉ ratio (finiteTupleToNat b)
      (finiteTupleToNat (w.val s).val) at hn
    simpa only [squareExponent_apply,if_neg hn] using he
  exact hblock.2.2 _ hmem

lemma finiteBlockFamily_nonzero (w : FiniteMultichain n E m) (s : Fin m)
    {v : Exponent (FiniteVariable.{u} n)} (hv : v ∈ finiteBlockFamily w s) : v ≠ 0 := by
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  obtain ⟨_,hba,hne,_⟩ := mem_filter.mp hb
  obtain ⟨x,hx⟩ := ratio_nonempty (show finiteTupleToNat b ≤ finiteChainToNat w s from hba)
    (fun h => hne (finiteTupleToNat_injective h))
  intro heq
  have hh := finiteRatioExponent_embedding.{u} hba
  rw [heq,Finsupp.embDomain_zero] at hh
  have hhx := congrArg (fun c : (Fin d × ℕ) →₀ ℕ => c x) hh
  change x ∈ ratio (finiteTupleToNat b) (finiteTupleToNat (w.val s).val) at hx
  simpa [squareExponent_apply,hx] using hhx

/-- Every coefficient divisor contains a divisor in precisely one crossing block. -/
theorem finiteChainCoordinate_contains_blocks (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoordinateFamily w) v ↔ ∃ s, Contains (finiteBlockFamily w s) v := by
  constructor
  · rintro ⟨g,hg,hgv⟩
    obtain ⟨s,_,hgs⟩ := mem_biUnion.mp hg
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hgs
    obtain ⟨hbE,hba,hne⟩ := mem_filter.mp hb
    let G := ratio (finiteTupleToNat b) (finiteChainToNat w s)
    have hG : Occurs (finiteTupleImage E) (finiteChainToNat w) G :=
      ⟨s,finiteTupleToNat b,mem_map.mpr ⟨b,hbE,rfl⟩,hba,
        fun h => hne (finiteTupleToNat_injective h),rfl⟩
    obtain ⟨H,hHG,hH⟩ := exists_minimal_le_of_wellFoundedLT
      (Occurs (finiteTupleImage E) (finiteChainToNat w)) G hG
    obtain ⟨p,c,hcE,hcp,hcne,hHc,hcross⟩ := minimalRatio_single_crossing
      (finiteTupleImage_closed hE).1 (finiteChainToNat_mem w) (finiteChainToNat_monotone w) hH
    obtain ⟨c,hcE0,rfl⟩ := mem_map.mp hcE
    change H=ratio (finiteTupleToNat c) (finiteChainToNat w p) at hHc
    have hcp' : c ≤ (w.val p).val := hcp
    have hcne' : c ≠ (w.val p).val := fun h => hcne (congrArg finiteTupleToNat h)
    refine ⟨p,finiteRowExponent n c - finiteRowExponent n (w.val p).val,?_,?_⟩
    · apply mem_image.mpr
      refine ⟨c,mem_filter.mpr ⟨hcE0,hcp',hcne',?_⟩,rfl⟩
      rw [← hHc]
      exact ⟨hH,⟨finiteTupleToNat c,mem_map.mpr ⟨c,hcE0,rfl⟩,hcp,hcne,hHc⟩,hcross⟩
    · apply le_trans _ hgv
      apply (Finsupp.embDomain_le_embDomain_iff_le finiteVariableEmbedding _ _).mp
      rw [finiteRatioExponent_embedding hcp',finiteRatioExponent_embedding hba]
      change squareExponent (ratio (finiteTupleToNat c) (finiteChainToNat w p)) ≤ squareExponent G
      rw [← hHc]
      exact squareExponent_mono hHG
  · rintro ⟨s,g,hg,hgv⟩
    exact ⟨g,finiteBlockFamily_subset_chain w s hg,hgv⟩

/-- The finite block ideals sum to the paper's actual coefficient ideal. -/
theorem finiteChainCoefficient_contains_blocks (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily n w) v ↔ ∃ s, Contains (finiteBlockFamily w s) v := by
  rw [← finiteChainCoordinate_contains_iff hE,finiteChainCoordinate_contains_blocks hE]

/-- No generator in a different crossing block can divide an exponent supported
on this block. This gives the exact restriction equality needed for the block map. -/
theorem finiteBlock_restriction (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (p : Fin m) (v : Exponent (FiniteVariable.{u} n))
    (hv : ∀ x, v x ≠ 0 → finiteCrosses w p x) :
    Contains (finiteChainCoefficientFamily n w) v ↔ Contains (finiteBlockFamily w p) v := by
  rw [finiteChainCoefficient_contains_blocks hE]
  constructor
  · rintro ⟨s,g,hg,hgv⟩
    have hgne := finiteBlockFamily_nonzero w s hg
    obtain ⟨x,hx⟩ := Finsupp.support_nonempty_iff.mpr hgne
    have hgx : g x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hvx : v x ≠ 0 := ne_of_gt ((Nat.pos_of_ne_zero hgx).trans_le (hgv x))
    have hsp : s = p := finiteCrosses_unique (finiteBlockFamily_variables w s hg x hgx) (hv x hvx)
    subst s
    exact ⟨g,hg,hgv⟩
  · exact fun h => ⟨p,h⟩

/-- On a single crossing block, the block ideal and the predecessor at that step
have exactly the same monomials. -/
theorem finitePredecessor_block_restriction (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (p : Fin m) (v : Exponent (FiniteVariable.{u} n))
    (hv : ∀ x, v x ≠ 0 → finiteCrosses w p x) :
    Contains (finitePredecessorFamily n E (w.val p).val) v ↔
      Contains (finiteBlockFamily w p) v := by
  constructor
  · rintro ⟨g,hg,hgv⟩
    apply (finiteBlock_restriction hE w p v hv).mp
    exact ⟨g,mem_biUnion.mpr ⟨p,mem_univ p,hg⟩,hgv⟩
  · rintro ⟨g,hg,hgv⟩
    apply (finiteCoordinatePredecessor_contains_iff hE (w.val p).property v).mp
    exact ⟨g,finiteBlockFamily_subset_predecessor w p hg,hgv⟩

/-- Residual exponent assigned to one of the disjoint crossing blocks. -/
def finiteBlockDegree (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) : Exponent (FiniteVariable.{u} n) :=
  v.filter (finiteCrosses w p)

@[simp] lemma finiteBlockDegree_apply (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) (x : FiniteVariable.{u} n) :
    finiteBlockDegree w p v x = if finiteCrosses w p x then v x else 0 := by
  simp [finiteBlockDegree,Finsupp.filter_apply]

lemma finiteBlockDegree_supported (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) (x : FiniteVariable.{u} n)
    (hx : finiteBlockDegree w p v x ≠ 0) : finiteCrosses w p x := by
  by_contra hn
  simp [hn] at hx

lemma finiteBlockDegree_sum (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n))
    (hv : ∀ x, v x ≠ 0 → ∃ p, finiteCrosses w p x) :
    ∑ p, finiteBlockDegree w p v = v := by
  ext x
  rw [Finsupp.finset_sum_apply]
  by_cases hx : v x = 0
  · simp [hx]
  · obtain ⟨p,hp⟩ := hv x hx
    rw [Finset.sum_eq_single p]
    · simp [hp]
    · intro q _ hqp
      have hq : ¬ finiteCrosses w q x := fun h => hqp (finiteCrosses_unique h hp)
      simp [hq]
    · simp

/-- The factor degree used in the whole-complex lift has precisely the intended
rowwise maximum: its added residual variables are strictly below that factor. -/
lemma finiteBlockDegree_row_bound (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) (x : FiniteVariable.{u} n)
    (hx : (finiteBlockDegree w p v + finiteRowExponent n (w.val p).val) x ≠ 0) :
    x.2.down ≤ (w.val p).val x.1 := by
  rcases x with ⟨r,⟨j⟩⟩
  by_cases hja : j = (w.val p).val r
  · exact hja.le
  · have hgen : finiteRowExponent.{u} n (w.val p).val ⟨r,ULift.up j⟩ = 0 := by
      simp only [finiteRowExponent_apply,if_neg (Ne.symm hja)]
    have hblock : finiteBlockDegree w p v ⟨r,ULift.up j⟩ ≠ 0 := by
      simpa only [Finsupp.add_apply,hgen,add_zero] using hx
    exact (finiteCrosses_below (finiteBlockDegree_supported w p v _ hblock)).le

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MultiplicityOrder -/
section
set_option autoImplicit false

/-! # Sorted multiplicities in any partially ordered set -/

noncomputable section
namespace FourPapers.Sublattice

open Classical
variable {A : Type*} [PartialOrder A]

def orderedMultiplicity (t : A →₀ ℕ) : List A :=
  ((t.toMultiset.map (toLinearExtension : A → LinearExtension A)).sort (· ≤ ·)).map
    (fun a : LinearExtension A => (show A from a))

lemma orderedMultiplicity_multiset (t : A →₀ ℕ) :
    (orderedMultiplicity t : Multiset A) = t.toMultiset := by
  unfold orderedMultiplicity
  rw [← Multiset.map_coe,Multiset.sort_eq,Multiset.map_map]
  exact Multiset.map_id _

lemma orderedMultiplicity_mem (t : A →₀ ℕ) (a : A) :
    a ∈ orderedMultiplicity t ↔ t a ≠ 0 := by
  rw [← Multiset.mem_coe,orderedMultiplicity_multiset,Finsupp.mem_toMultiset,
    Finsupp.mem_support_iff]

lemma orderedMultiplicity_length (t : A →₀ ℕ) :
    (orderedMultiplicity t).length = t.toMultiset.card := by
  rw [← Multiset.coe_card,orderedMultiplicity_multiset]

lemma orderedMultiplicity_pairwise (t : A →₀ ℕ)
    (hcomp : ∀ a b, t a ≠ 0 → t b ≠ 0 → a ≤ b ∨ b ≤ a) :
    (orderedMultiplicity t).Pairwise (· ≤ ·) := by
  let l := (t.toMultiset.map (toLinearExtension : A → LinearExtension A)).sort (· ≤ ·)
  have hsort : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  have hmem (a : LinearExtension A) (ha : a ∈ l) : t (show A from a) ≠ 0 := by
    have hh : (show A from a) ∈ orderedMultiplicity t := List.mem_map.mpr ⟨a,ha,rfl⟩
    exact (orderedMultiplicity_mem t _).mp hh
  have hpair : l.Pairwise (fun a b : LinearExtension A => (show A from a) ≤ (show A from b)) := by
    apply hsort.imp_of_mem
    intro a b ha hb hab
    rcases hcomp (show A from a) (show A from b) (hmem a ha) (hmem b hb) with h | h
    · exact h
    · have hba : b ≤ a := (toLinearExtension (α := A)).monotone h
      exact (le_antisymm hab hba) ▸ le_rfl
  unfold orderedMultiplicity
  rw [List.pairwise_map]
  exact hpair

lemma orderedMultiplicity_injective : Function.Injective (orderedMultiplicity (A := A)) := by
  intro s t h
  have he := congrArg (fun w : List A => (w : Multiset A)) h
  rw [orderedMultiplicity_multiset,orderedMultiplicity_multiset] at he
  exact (Finsupp.toMultiset_eq_iff.mp he).trans (Finsupp.toMultiset_toFinsupp t)

lemma orderedMultiplicity_perm (t : A →₀ ℕ) :
    (orderedMultiplicity t).Perm t.toMultiset.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [orderedMultiplicity_multiset,Multiset.coe_toList]

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteStandard -/
section
set_option autoImplicit false

/-!
# Standard monomials in the exact finite presentation

A presentation monomial is standard precisely when its factors form a chain and
its coefficient is outside every genuine predecessor colon occurring in that
chain. The equivalence below compares literal exponent vectors and divisibility;
it does not define standardness by the desired Betti formula.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma finiteFactorPart_embedding_apply (c : FiniteReesVariable.{u} E →₀ ℕ) (a : E) :
    factorPart (c.embDomain (finiteReesVariableEmbedding E)) (finiteTupleImageEquiv E a) =
      finiteFactorPart c a := by
  change (c.embDomain (finiteReesVariableEmbedding E))
    (finiteReesVariableEmbedding E (Sum.inr a)) = c (Sum.inr a)
  exact Finsupp.embDomain_apply_self _ _ _

lemma finiteCoefficientPart_embedding (c : FiniteReesVariable.{u} E →₀ ℕ) :
    coefficientPart (c.embDomain (finiteReesVariableEmbedding E)) =
      (finiteCoefficientPart c).embDomain finiteVariableEmbedding := by
  ext x
  by_cases hx : x ∈ Set.range (finiteVariableEmbedding.{u} (n := n))
  · obtain ⟨y,rfl⟩ := hx
    change (c.embDomain (finiteReesVariableEmbedding E))
      (finiteReesVariableEmbedding E (Sum.inl y)) =
        ((finiteCoefficientPart c).embDomain finiteVariableEmbedding) (finiteVariableEmbedding y)
    exact (Finsupp.embDomain_apply_self (finiteReesVariableEmbedding E) c (Sum.inl y)).trans
      (Finsupp.embDomain_apply_self finiteVariableEmbedding (finiteCoefficientPart c) y).symm
  · have hxl : Sum.inl x ∉ Set.range (finiteReesVariableEmbedding E) := by
      rintro ⟨y,hy⟩
      cases y with
      | inl y => exact hx ⟨y,Sum.inl.inj hy⟩
      | inr a => cases hy
    change (c.embDomain (finiteReesVariableEmbedding E)) (Sum.inl x) = _
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hxl,
      Finsupp.embDomain_of_notMem_range _ _ _ hx]

lemma squareExponent_le_iff {V : Type*} [DecidableEq V]
    (g : Finset V) (v : V →₀ ℕ) :
    squareExponent g ≤ v ↔ ∀ x ∈ g, 0 < v x := by
  constructor
  · intro h x hx
    have hh := h x
    simpa only [squareExponent_apply,if_pos hx,Nat.succ_le_iff] using hh
  · intro h x
    by_cases hx : x ∈ g
    · simpa only [squareExponent_apply,if_pos hx,Nat.succ_le_iff] using h x hx
    · simp only [squareExponent_apply,if_neg hx]
      exact Nat.zero_le _

lemma finiteRatio_divides_iff {b a : FiniteTuple n} (hba : b ≤ a)
    (v : Exponent (FiniteVariable.{u} n)) :
    finiteRowExponent n b - finiteRowExponent n a ≤ v ↔
      ∀ x ∈ ratio (finiteTupleToNat b) (finiteTupleToNat a),
        0 < v.embDomain finiteVariableEmbedding x := by
  rw [← Finsupp.embDomain_le_embDomain_iff_le finiteVariableEmbedding,
    finiteRatioExponent_embedding hba,squareExponent_le_iff]

/-- Exact finite standardness, using the literal coordinate predecessor ratios. -/
theorem finiteReesStandard_iff (c : FiniteReesVariable.{u} E →₀ ℕ) :
    FiniteReesStandard c ↔
      (∀ a b : E, finiteFactorPart c a ≠ 0 → finiteFactorPart c b ≠ 0 →
        a.val ≤ b.val ∨ b.val ≤ a.val) ∧
      (∀ a : E, finiteFactorPart c a ≠ 0 →
        ¬ Contains (finiteCoordinatePredecessorFamily E a.val) (finiteCoefficientPart c)) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro a b ha hb
      exact h.1 (finiteTupleImageEquiv E a) (finiteTupleImageEquiv E b)
        (by simpa only [finiteFactorPart_embedding_apply] using ha)
        (by simpa only [finiteFactorPart_embedding_apply] using hb)
    · intro a ha hdiv
      obtain ⟨g,hg,hgv⟩ := hdiv
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hg
      obtain ⟨hbE,hba,hne⟩ := mem_filter.mp hb
      apply h.2 (finiteTupleImageEquiv E a)
        (by simpa only [finiteFactorPart_embedding_apply] using ha)
        (finiteTupleToNat b) (mem_map.mpr ⟨b,hbE,rfl⟩) hba
        (fun he => hne (finiteTupleToNat_injective he))
      rw [finiteCoefficientPart_embedding]
      exact (finiteRatio_divides_iff hba _).mp hgv
  · rintro ⟨hcomp,hcoeff⟩
    refine ⟨?_,?_⟩
    · intro a b ha hb
      obtain ⟨a,rfl⟩ := (finiteTupleImageEquiv E).surjective a
      obtain ⟨b,rfl⟩ := (finiteTupleImageEquiv E).surjective b
      exact hcomp a b
        (by simpa only [finiteFactorPart_embedding_apply] using ha)
        (by simpa only [finiteFactorPart_embedding_apply] using hb)
    · intro a ha b hb hba hne hdiv
      obtain ⟨a,rfl⟩ := (finiteTupleImageEquiv E).surjective a
      obtain ⟨b,hb0,rfl⟩ := mem_map.mp hb
      have hba' : b ≤ a.val := hba
      have hne' : b ≠ a.val := fun he => hne (congrArg finiteTupleToNat he)
      apply hcoeff a (by simpa only [finiteFactorPart_embedding_apply] using ha)
      refine ⟨finiteRowExponent n b - finiteRowExponent n a.val,
        mem_image.mpr ⟨b,mem_filter.mpr ⟨hb0,hba',hne'⟩,rfl⟩,?_⟩
      apply (finiteRatio_divides_iff hba' _).mpr
      rw [finiteCoefficientPart_embedding] at hdiv
      exact hdiv

lemma finiteReesStandard_iff_colons (hE : finiteLatticeClosed n E)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    FiniteReesStandard c ↔
      (∀ a b : E, finiteFactorPart c a ≠ 0 → finiteFactorPart c b ≠ 0 →
        a.val ≤ b.val ∨ b.val ≤ a.val) ∧
      (∀ a : E, finiteFactorPart c a ≠ 0 →
        ¬ Contains (finitePredecessorFamily n E a.val) (finiteCoefficientPart c)) := by
  rw [finiteReesStandard_iff]
  simp_rw [finiteCoordinatePredecessor_contains_iff hE (Subtype.mem _)]

def finiteOrderedFactors (c : FiniteReesVariable.{u} E →₀ ℕ) : List E :=
  orderedMultiplicity (finiteFactorPart c)

lemma finiteOrderedFactors_perm (c : FiniteReesVariable.{u} E →₀ ℕ) :
    (finiteOrderedFactors c).Perm (finiteFactorList c) :=
  orderedMultiplicity_perm _

lemma finiteOrderedFactors_pairwise {c : FiniteReesVariable.{u} E →₀ ℕ}
    (hc : FiniteReesStandard c) : (finiteOrderedFactors c).Pairwise (· ≤ ·) :=
  orderedMultiplicity_pairwise _ (finiteReesStandard_iff c |>.mp hc).1

lemma finiteOrderedFactors_mem (c : FiniteReesVariable.{u} E →₀ ℕ) (a : E) :
    a ∈ finiteOrderedFactors c ↔ finiteFactorPart c a ≠ 0 :=
  orderedMultiplicity_mem _ _

lemma finiteReesExponentMap_ordered (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteReesExponentMap E c = finiteTargetExponent
      (finiteCoefficientPart c + generatorListExponent (fun a : E => finiteRowExponent n a.val)
        (finiteOrderedFactors c)) (finiteOrderedFactors c).length := by
  rw [finiteReesExponentMap_coordinates]
  have hp := finiteOrderedFactors_perm c
  have hs := (hp.map (fun a : E => finiteRowExponent.{u} n a.val)).sum_eq
  change generatorListExponent (fun a : E => finiteRowExponent.{u} n a.val)
    (finiteOrderedFactors c)=generatorListExponent (fun a : E => finiteRowExponent.{u} n a.val)
    (finiteFactorList c) at hs
  rw [hp.length_eq,hs]

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainCoordinates -/
section
set_option autoImplicit false

/-!
# The exact chain normal-form parametrization of ordinary powers

The parameters are the multichains and standard coefficient monomials of the
paper. They are proved to be in bijection with the actual monomials of `I_E ^ m`.
This retains both the whole exponent vector and every multiplicity.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

lemma listMultiplicity_eq_sum {A : Type*} [DecidableEq A] (l : List A) :
    (l : Multiset A).toFinsupp = (l.map fun a => Finsupp.single a 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change (Multiset.cons a (l : Multiset A)).toFinsupp=
        ((a::l).map fun a => Finsupp.single a 1).sum
      rw [List.map_cons,List.sum_cons,
        ← Multiset.singleton_add,Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton,ih]


def finiteChainMultiplicity (w : FiniteMultichain n E m) : E →₀ ℕ :=
  (List.ofFn w.val : Multiset E).toFinsupp

lemma finiteChainMultiplicity_sum (w : FiniteMultichain n E m) :
    finiteChainMultiplicity w = ∑ s, Finsupp.single (w.val s) 1 := by
  rw [finiteChainMultiplicity,listMultiplicity_eq_sum,List.map_ofFn,List.sum_ofFn]
  rfl

lemma finiteChainMultiplicity_ne_zero (w : FiniteMultichain n E m) (a : E) :
    finiteChainMultiplicity w a ≠ 0 ↔ ∃ s, w.val s = a := by
  rw [← Finsupp.mem_support_iff,finiteChainMultiplicity,Multiset.toFinsupp_support]
  simp only [Multiset.mem_toFinset,Multiset.mem_coe,List.mem_ofFn]

def finiteChainPresentation (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) : FiniteReesVariable.{u} E →₀ ℕ :=
  v.embDomain Function.Embedding.inl +
    (finiteChainMultiplicity w).embDomain Function.Embedding.inr

@[simp] lemma finiteChainPresentation_coefficient (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) :
    finiteCoefficientPart (finiteChainPresentation w v) = v := by
  ext x
  simp [finiteCoefficientPart,finiteChainPresentation,Finsupp.embDomain_inl,
    Finsupp.embDomain_inr,Finsupp.sumElim_apply]

@[simp] lemma finiteChainPresentation_factor (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) :
    finiteFactorPart (finiteChainPresentation w v) = finiteChainMultiplicity w := by
  ext a
  simp [finiteFactorPart,finiteChainPresentation,Finsupp.embDomain_inl,
    Finsupp.embDomain_inr,Finsupp.sumElim_apply]

lemma finiteChainPresentation_eq_list (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) :
    finiteChainPresentation w v = finiteListPresentation v (List.ofFn w.val) := by
  unfold finiteChainPresentation finiteListPresentation
  rw [finiteChainMultiplicity_sum,List.map_ofFn,List.sum_ofFn]
  congr 1
  simp only [Finsupp.embDomain_eq_mapDomain,Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single]
  rfl

lemma finiteChainShift_eq_list (w : FiniteMultichain n E m) :
    finiteChainShift n w = generatorListExponent
      (fun a : E => finiteRowExponent.{u} n a.val) (List.ofFn w.val) := by
  simp [finiteChainShift,generatorListExponent,List.map_ofFn,List.sum_ofFn]

lemma finiteChainPresentation_image (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) :
    finiteReesExponentMap E (finiteChainPresentation w v) =
      finiteTargetExponent (v + finiteChainShift n w) m := by
  rw [finiteChainPresentation_eq_list,finiteListPresentation_image,
    ← finiteChainShift_eq_list,List.length_ofFn]

/-- Standardness is exactly nonmembership in the actual sum of the colons. -/
theorem finiteChainPresentation_standard_iff (hE : finiteLatticeClosed n E)
    (w : FiniteMultichain n E m) (v : Exponent (FiniteVariable.{u} n)) :
    FiniteReesStandard (finiteChainPresentation w v) ↔
      ¬ Contains (finiteChainCoefficientFamily n w) v := by
  rw [finiteReesStandard_iff_colons hE,finiteChainPresentation_coefficient,
    finiteChainPresentation_factor]
  have hcomp : ∀ a b : E, finiteChainMultiplicity w a ≠ 0 →
      finiteChainMultiplicity w b ≠ 0 → a.val ≤ b.val ∨ b.val ≤ a.val := by
    intro a b ha hb
    obtain ⟨i,rfl⟩ := (finiteChainMultiplicity_ne_zero w a).mp ha
    obtain ⟨j,rfl⟩ := (finiteChainMultiplicity_ne_zero w b).mp hb
    rcases le_total i j with hij | hji
    · exact Or.inl (w.property hij)
    · exact Or.inr (w.property hji)
  constructor
  · rintro ⟨_,hcoeff⟩ ⟨g,hg,hgv⟩
    obtain ⟨s,_,hgs⟩ := mem_biUnion.mp hg
    exact hcoeff (w.val s) ((finiteChainMultiplicity_ne_zero w _).mpr ⟨s,rfl⟩)
      ⟨g,hgs,hgv⟩
  · intro hcoeff
    refine ⟨hcomp,?_⟩
    intro a ha hdiv
    obtain ⟨s,rfl⟩ := (finiteChainMultiplicity_ne_zero w a).mp ha
    obtain ⟨g,hg,hgv⟩ := hdiv
    exact hcoeff ⟨g,mem_biUnion.mpr ⟨s,mem_univ s,hg⟩,hgv⟩

lemma finiteChain_ofFn_pairwise (w : FiniteMultichain n E m) :
    (List.ofFn w.val).Pairwise (· ≤ ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact w.property hij.le

lemma finiteChainMultiplicity_injective :
    Function.Injective (finiteChainMultiplicity (n := n) (E := E) (m := m)) := by
  intro w z h
  have hmult : (List.ofFn w.val : Multiset E) = (List.ofFn z.val : Multiset E) :=
    Multiset.toFinsupp.injective h
  have hp : (List.ofFn w.val).Perm (List.ofFn z.val) := Multiset.coe_eq_coe.mp hmult
  have he := hp.eq_of_pairwise' (finiteChain_ofFn_pairwise w) (finiteChain_ofFn_pairwise z)
  apply Subtype.ext
  funext s
  have hh := congrArg (fun l : List E => l[s.val]?) he
  simpa using hh

/-- A sorted finite list, with its actual length, defines a multichain. -/
def multichainOfList (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    FiniteMultichain n E l.length :=
  ⟨l.get,fun _ _ hij => hl.rel_get_of_le hij⟩

@[simp] lemma multichainOfList_ofFn (l : List E) (hl : l.Pairwise (· ≤ ·)) :
    List.ofFn (multichainOfList l hl).val = l := List.ofFn_get l

/-- Every standard exponent is exactly the presentation exponent of its ordered
multichain and its literal coefficient part. -/
lemma standard_eq_chainPresentation {c : FiniteReesVariable.{u} E →₀ ℕ}
    (hc : FiniteReesStandard c) :
    finiteChainPresentation
      (multichainOfList (finiteOrderedFactors c) (finiteOrderedFactors_pairwise hc))
      (finiteCoefficientPart c) = c := by
  rw [finiteChainPresentation,finiteChainMultiplicity,multichainOfList_ofFn]
  have hm : (finiteOrderedFactors c : Multiset E).toFinsupp = finiteFactorPart c := by
    rw [finiteOrderedFactors,orderedMultiplicity_multiset,Finsupp.toMultiset_toFinsupp]
  rw [hm]
  exact finite_exponent_parts c

abbrev FiniteChainStandardIndex (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ) :=
  Σ w : FiniteMultichain n E m,
    {v : Exponent (FiniteVariable.{u} n) // ¬ Contains (finiteChainCoefficientFamily n w) v}

def finiteChainIndexExponent (a : FiniteChainStandardIndex.{u} n E m) :
    Exponent (FiniteVariable.{u} n) := a.2.val + finiteChainShift n a.1

lemma finiteChainIndexExponent_mem (a : FiniteChainStandardIndex.{u} n E m) :
    Contains (exponentPowerFamily (finiteRowFamily n E) m) (finiteChainIndexExponent a) := by
  apply (finiteTarget_mem_rees_iff _ _).mp
  exact ⟨finiteChainPresentation a.1 a.2.val,finiteChainPresentation_image a.1 a.2.val⟩

lemma finiteChainIndexExponent_injective (hE : finiteLatticeClosed n E) :
    Function.Injective (finiteChainIndexExponent (n := n) (E := E) (m := m)) := by
  rintro ⟨w,v,hv⟩ ⟨z,t,ht⟩ he
  have hs := finiteReesStandard_image_injective hE
    ((finiteChainPresentation_standard_iff hE w v).mpr hv)
    ((finiteChainPresentation_standard_iff hE z t).mpr ht)
    (by rw [finiteChainPresentation_image,finiteChainPresentation_image];
        exact congrArg (fun a => finiteTargetExponent a m) he)
  have hcoeff : v = t := by
    simpa only [finiteChainPresentation_coefficient] using congrArg finiteCoefficientPart hs
  have hchain : w = z := finiteChainMultiplicity_injective (by
    simpa only [finiteChainPresentation_factor] using congrArg finiteFactorPart hs)
  subst z
  subst t
  rfl

lemma finiteChainIndexExponent_surjective (hE : finiteLatticeClosed n E)
    (a : Exponent (FiniteVariable.{u} n))
    (ha : Contains (exponentPowerFamily (finiteRowFamily n E) m) a) :
    ∃ b : FiniteChainStandardIndex.{u} n E m, finiteChainIndexExponent b = a := by
  obtain ⟨c,hc⟩ := (finiteTarget_mem_rees_iff a m).mpr ha
  let c' := finiteReesNormalForm hE c
  have hstd : FiniteReesStandard c' := finiteReesNormalForm_standard hE c
  have him : finiteReesExponentMap E c' = finiteTargetExponent a m :=
    (finiteReesNormalForm_image hE c).trans hc
  rw [finiteReesExponentMap_ordered] at him
  obtain ⟨hexp,hlen⟩ := finiteTargetExponent_injective him
  let w := multichainOfList (finiteOrderedFactors c') (finiteOrderedFactors_pairwise hstd)
  have hp : finiteChainPresentation w (finiteCoefficientPart c') = c' :=
    standard_eq_chainPresentation hstd
  have hv : ¬ Contains (finiteChainCoefficientFamily n w) (finiteCoefficientPart c') :=
    (finiteChainPresentation_standard_iff hE w _).mp (by rw [hp]; exact hstd)
  subst m
  refine ⟨⟨w,finiteCoefficientPart c',hv⟩,?_⟩
  change finiteCoefficientPart c' + finiteChainShift n w = a
  rw [finiteChainShift_eq_list,multichainOfList_ofFn]
  exact hexp

/-- The full, unbounded chain normal form is a genuine equivalence with the
monomial indices of the actual ordinary power. -/
def finiteChainPowerIndexEquiv (hE : finiteLatticeClosed n E) (m : ℕ) :
    FiniteChainStandardIndex.{u} n E m ≃
      {a : Exponent (FiniteVariable.{u} n) //
        Contains (exponentPowerFamily (finiteRowFamily n E) m) a} :=
  Equiv.ofBijective (fun a => ⟨finiteChainIndexExponent a,finiteChainIndexExponent_mem a⟩)
    ⟨fun a b h => finiteChainIndexExponent_injective hE (congrArg Subtype.val h),by
      intro a
      obtain ⟨b,hb⟩ := finiteChainIndexExponent_surjective hE a.val a.property
      exact ⟨b,Subtype.ext hb⟩⟩

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainMultiplication -/
section
set_option autoImplicit false

/-!
# Multiplication by a row variable and the exact leading differential

A coefficient variable acts on the genuine ordinary power. In chain normal-form
coordinates it either stays in the same quotient block or strictly lowers the
explicit presentation weight. No dimension comparison is assumed here.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

def finitePresentationWeight (c : FiniteReesVariable.{u} E →₀ ℕ) : ℕ :=
  reesWeight (finiteTupleImage E) (c.embDomain (finiteReesVariableEmbedding E))

lemma finitePresentationWeight_add_row (c : FiniteReesVariable.{u} E →₀ ℕ)
    (x : FiniteVariable.{u} n) :
    finitePresentationWeight (c + Finsupp.single (Sum.inl x) 1) =
      finitePresentationWeight c + 1 := by
  simp only [finitePresentationWeight,Finsupp.embDomain_add,Finsupp.embDomain_single,
    map_add,Finsupp.weight_single,one_nsmul,finiteReesVariableEmbedding,
    Function.Embedding.sumMap,Sum.map_inl,presentationWeight]
  rfl

lemma finiteReesNormalForm_weight_le (hE : finiteLatticeClosed n E)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finitePresentationWeight (finiteReesNormalForm hE c) ≤ finitePresentationWeight c := by
  unfold finitePresentationWeight
  rw [finiteReesNormalForm_embedding]
  exact reesNormalForm_weight_le _ _

lemma finiteReesNormalForm_weight_lt (hE : finiteLatticeClosed n E)
    {c : FiniteReesVariable.{u} E →₀ ℕ} (hc : ¬ FiniteReesStandard c) :
    finitePresentationWeight (finiteReesNormalForm hE c) < finitePresentationWeight c := by
  unfold finitePresentationWeight
  rw [finiteReesNormalForm_embedding]
  exact reesNormalForm_weight_lt _ hc

lemma finiteChainPresentation_add_row (w : FiniteMultichain n E m)
    (v : Exponent (FiniteVariable.{u} n)) (x : FiniteVariable.{u} n) :
    finiteChainPresentation w (v + Finsupp.single x 1) =
      finiteChainPresentation w v + Finsupp.single (Sum.inl x) 1 := by
  simp only [finiteChainPresentation,Finsupp.embDomain_add,Finsupp.embDomain_single]
  exact add_right_comm _ _ _

lemma finiteTargetExponent_add_row (a : Exponent (FiniteVariable.{u} n))
    (m : ℕ) (x : FiniteVariable.{u} n) :
    finiteTargetExponent (a + Finsupp.single x 1) m =
      finiteTargetExponent a m + Finsupp.single (some x) 1 := by
  simp only [finiteTargetExponent,Finsupp.embDomain_add,Finsupp.embDomain_single]
  exact add_right_comm _ _ _

/-- Variable multiplication transported from the actual monomial ideal. -/
def chainIndexMultiply (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    FiniteChainStandardIndex.{u} n E m :=
  (finiteChainPowerIndexEquiv hE m).symm
    ⟨finiteChainIndexExponent a + Finsupp.single x 1,by
      obtain ⟨b,hb,hba⟩ := finiteChainIndexExponent_mem a
      exact ⟨b,hb,hba.trans (le_add_of_nonneg_right zero_le)⟩⟩

lemma chainIndexMultiply_image (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    finiteChainIndexExponent (chainIndexMultiply hE a x) =
      finiteChainIndexExponent a + Finsupp.single x 1 := by
  exact congrArg Subtype.val ((finiteChainPowerIndexEquiv hE m).apply_symm_apply _)

/-- If the quotient coefficient survives multiplication, the multichain does not change. -/
lemma chainIndexMultiply_of_allowed (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n)
    (ha : ¬ Contains (finiteChainCoefficientFamily n a.1) (a.2.val + Finsupp.single x 1)) :
    chainIndexMultiply hE a x = ⟨a.1,a.2.val + Finsupp.single x 1,ha⟩ := by
  apply finiteChainIndexExponent_injective hE
  rw [chainIndexMultiply_image]
  unfold finiteChainIndexExponent
  exact add_right_comm _ _ _

lemma chainIndexMultiply_presentation (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    finiteChainPresentation (chainIndexMultiply hE a x).1 (chainIndexMultiply hE a x).2.val =
      finiteReesNormalForm hE (finiteChainPresentation a.1 a.2.val +
        Finsupp.single (Sum.inl x) 1) := by
  apply finiteReesStandard_image_injective hE
    ((finiteChainPresentation_standard_iff hE _ _).mpr (chainIndexMultiply hE a x).2.property)
    (finiteReesNormalForm_standard hE _)
  rw [finiteReesNormalForm_image,finiteChainPresentation_image,map_add,
    finiteChainPresentation_image]
  change finiteTargetExponent (finiteChainIndexExponent (chainIndexMultiply hE a x)) m =
    finiteTargetExponent (finiteChainIndexExponent a) m + _
  rw [chainIndexMultiply_image,finiteTargetExponent_add_row]
  congr 1
  change Finsupp.single (some x) 1=Finsupp.weight (finiteReesVariableExponent E)
    (Finsupp.single (Sum.inl x) 1)
  rw [Finsupp.weight_single]
  simp only [one_smul]
  rfl

def chainIndexWeight (a : FiniteChainStandardIndex.{u} n E m) : ℕ :=
  finitePresentationWeight (finiteChainPresentation a.1 a.2.val)

lemma chainIndexMultiply_weight_le (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    chainIndexWeight (chainIndexMultiply hE a x) ≤ chainIndexWeight a + 1 := by
  unfold chainIndexWeight
  rw [chainIndexMultiply_presentation]
  exact (finiteReesNormalForm_weight_le hE _).trans_eq (finitePresentationWeight_add_row _ x)

/-- Precisely the terms absent from the quotient differential strictly lower
weight in the genuine ideal differential. -/
lemma chainIndexMultiply_weight_lt (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n)
    (ha : Contains (finiteChainCoefficientFamily n a.1) (a.2.val + Finsupp.single x 1)) :
    chainIndexWeight (chainIndexMultiply hE a x) < chainIndexWeight a + 1 := by
  unfold chainIndexWeight
  rw [chainIndexMultiply_presentation]
  apply (finiteReesNormalForm_weight_lt hE ?_).trans_eq (finitePresentationWeight_add_row _ x)
  rw [← finiteChainPresentation_add_row,finiteChainPresentation_standard_iff hE]
  exact fun h => h ha

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainWeight -/
section
set_option autoImplicit false

/-!
# The finite multichain filtration of the actual Koszul differential

After fixing the fine degree and the power, the coefficient degree plus exterior
degree is constant. The effective filtration therefore depends only on the
multichain. This makes all homotopies inside one coefficient quotient preserve
weight, without an additional assumption about their individual matrices.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

lemma finiteRowExponent_degree (a : FiniteTuple n) : (finiteRowExponent.{u} n a).degree = d := by
  simp [finiteRowExponent,map_sum,Finsupp.degree_single]

lemma finiteChainShift_degree (w : FiniteMultichain n E m) :
    (finiteChainShift.{u} n w).degree = m * d := by
  simp [finiteChainShift,map_sum,finiteRowExponent_degree]

lemma finitePresentationWeight_row (v : Exponent (FiniteVariable.{u} n)) :
    finitePresentationWeight (E := E) (v.embDomain Function.Embedding.inl) = v.degree := by
  refine v.induction ?_ ?_
  · simp [finitePresentationWeight]
  · intro x r v _ _ ih
    simp only [Finsupp.embDomain_add,Finsupp.embDomain_single,
      finitePresentationWeight,Finsupp.embDomain_add,Finsupp.embDomain_single,
      map_add,Finsupp.weight_single,Finsupp.degree_single,finiteReesVariableEmbedding,
      Function.Embedding.sumMap,Sum.map_inl,presentationWeight,smul_eq_mul,mul_one] at ih ⊢
    rw [ih]
    change r * 1 + v.degree=r+v.degree
    rw [Nat.mul_one]

/-- The weight of the product of Rees variables alone. -/
def finiteChainFactorWeight (w : FiniteMultichain n E m) : ℕ :=
  finitePresentationWeight (E := E)
    ((finiteChainMultiplicity w).embDomain (Function.Embedding.inr : E ↪ FiniteReesVariable.{u} E))

lemma finiteChainFactorWeight_sum (w : FiniteMultichain n E m) :
    finiteChainFactorWeight.{u} w =
      ∑ s, reesVariableWeight (finiteTupleImage E) (finiteTupleToNat (w.val s).val) := by
  unfold finiteChainFactorWeight finitePresentationWeight
  rw [finiteChainMultiplicity_sum]
  simp only [Finsupp.embDomain_eq_mapDomain,Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single,map_sum,Finsupp.weight_single,one_nsmul,
    finiteReesVariableEmbedding,Function.Embedding.sumMap,Sum.map_inr,
    presentationWeight,finiteTupleImageEquiv_val]
  rfl

lemma chainIndexWeight_eq (a : FiniteChainStandardIndex.{u} n E m) :
    chainIndexWeight a = a.2.val.degree + finiteChainFactorWeight.{u} a.1 := by
  unfold chainIndexWeight finiteChainPresentation finitePresentationWeight
  rw [Finsupp.embDomain_add,map_add]
  change finitePresentationWeight (a.2.val.embDomain Function.Embedding.inl) + _ = _
  rw [finitePresentationWeight_row]
  rfl

lemma finiteChainIndexExponent_degree (a : FiniteChainStandardIndex.{u} n E m) :
    (finiteChainIndexExponent a).degree = a.2.val.degree + m * d := by
  rw [finiteChainIndexExponent,map_add,finiteChainShift_degree]

lemma chainIndexMultiply_coefficient_degree (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    (chainIndexMultiply hE a x).2.val.degree = a.2.val.degree + 1 := by
  have he := congrArg Finsupp.degree (chainIndexMultiply_image hE a x)
  simp only [map_add,Finsupp.degree_single,finiteChainIndexExponent_degree] at he
  omega

/-- Every ordinary Koszul boundary weakly lowers the multichain filtration. -/
lemma chainIndexMultiply_factorWeight_le (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n) :
    finiteChainFactorWeight.{u} (chainIndexMultiply hE a x).1 ≤ finiteChainFactorWeight.{u} a.1 := by
  have hw := chainIndexMultiply_weight_le hE a x
  rw [chainIndexWeight_eq,chainIndexWeight_eq,chainIndexMultiply_coefficient_degree] at hw
  omega

/-- Exactly the extra terms of the ordinary differential strictly lower the
multichain filtration. -/
lemma chainIndexMultiply_factorWeight_lt (hE : finiteLatticeClosed n E)
    (a : FiniteChainStandardIndex.{u} n E m) (x : FiniteVariable.{u} n)
    (ha : Contains (finiteChainCoefficientFamily n a.1) (a.2.val + Finsupp.single x 1)) :
    finiteChainFactorWeight.{u} (chainIndexMultiply hE a x).1 < finiteChainFactorWeight.{u} a.1 := by
  have hw := chainIndexMultiply_weight_lt hE a x ha
  rw [chainIndexWeight_eq,chainIndexWeight_eq,chainIndexMultiply_coefficient_degree] at hw
  omega

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainFaces -/
section

set_option autoImplicit false

/-!
# The exact partition of the upper Koszul faces by standard multichains

For a fixed power and fine exponent, the actual upper Koszul faces partition
into the quotient face sets of the coefficient colons, shifted by the actual
chain generator. In particular this is an equality of whole chain-module bases,
not merely a numerical identity of alternating sums.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

abbrev AdmissibleChain (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) :=
  {w : FiniteMultichain n E m // finiteChainShift n w ≤ α}

abbrev ChainFaceIndex (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) :=
  Σ w : AdmissibleChain n E m α,
    {s : Finset (FiniteVariable.{u} n) //
      quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (α - finiteChainShift n w.val) s}

lemma residual_add_shift {V : Type*} [DecidableEq V]
    (α b f : V →₀ ℕ) (hb : b ≤ α) (hf : f ≤ α - b) :
    (α - b - f) + b = α - f := by
  ext x
  have hb' := hb x
  have hf' := hf x
  simp only [Finsupp.tsub_apply] at hf'
  simp only [Finsupp.add_apply,Finsupp.tsub_apply]
  omega

lemma chainFaceIndex_face_le {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) : faceExponent a.2.val ≤ α :=
  a.2.property.1.trans (tsub_le_self)

/-- The standard coefficient recovered from a quotient face. -/
def chainFaceStandardIndex {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) : FiniteChainStandardIndex.{u} n E m :=
  ⟨a.1.val,α - finiteChainShift n a.1.val - faceExponent a.2.val,a.2.property.2⟩

lemma chainFaceStandardIndex_exponent {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) :
    finiteChainIndexExponent (chainFaceStandardIndex a) = α - faceExponent a.2.val :=
  residual_add_shift _ _ _ a.1.property a.2.property.1

def chainFaceToActual {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) :
    {s : Finset (FiniteVariable.{u} n) //
      koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α s} :=
  ⟨a.2.val,chainFaceIndex_face_le a,by
    rw [← chainFaceStandardIndex_exponent a]
    exact finiteChainIndexExponent_mem (chainFaceStandardIndex a)⟩

lemma chainFaceToActual_injective (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n)) :
    Function.Injective (chainFaceToActual (n := n) (E := E) (m := m) (α := α)) := by
  rintro ⟨⟨w,hw⟩,⟨s,hs⟩⟩ ⟨⟨z,hz⟩,⟨t,ht⟩⟩ he
  have hst : s = t := congrArg Subtype.val he
  subst t
  have hidx : chainFaceStandardIndex (⟨⟨w,hw⟩,s,hs⟩ : ChainFaceIndex n E m α) =
      chainFaceStandardIndex (⟨⟨z,hz⟩,s,ht⟩ : ChainFaceIndex n E m α) := by
    apply finiteChainIndexExponent_injective hE
    rw [chainFaceStandardIndex_exponent,chainFaceStandardIndex_exponent]
  have hwz : w = z := congrArg Sigma.fst hidx
  subst z
  rfl

lemma chainFaceToActual_surjective (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n)) :
    Function.Surjective (chainFaceToActual (n := n) (E := E) (m := m) (α := α)) := by
  rintro ⟨s,hs,hsI⟩
  let c := (finiteChainPowerIndexEquiv hE m).symm ⟨α - faceExponent s,hsI⟩
  have hc : finiteChainIndexExponent c = α - faceExponent s :=
    congrArg Subtype.val ((finiteChainPowerIndexEquiv hE m).apply_symm_apply _)
  have hb : finiteChainShift n c.1 ≤ α := by
    have hh : finiteChainShift n c.1 ≤ finiteChainIndexExponent c :=
      le_add_of_nonneg_left zero_le
    exact (hh.trans_eq hc).trans tsub_le_self
  have hface : faceExponent s ≤ α - finiteChainShift n c.1 := by
    intro x
    have hc' := congrArg (fun a : Exponent (FiniteVariable.{u} n) => a x) hc
    have hs' := hs x
    simp only [finiteChainIndexExponent,Finsupp.add_apply,Finsupp.tsub_apply] at hc' ⊢
    omega
  have hcoeff : α - finiteChainShift n c.1 - faceExponent s = c.2.val := by
    ext x
    have hc' := congrArg (fun a : Exponent (FiniteVariable.{u} n) => a x) hc
    have hs' := hs x
    simp only [finiteChainIndexExponent,Finsupp.add_apply,Finsupp.tsub_apply] at hc' ⊢
    omega
  refine ⟨⟨⟨c.1,hb⟩,s,hface,?_⟩,rfl⟩
  change ¬ Contains (finiteChainCoefficientFamily n c.1)
    (α - finiteChainShift n c.1 - faceExponent s)
  rw [hcoeff]
  exact c.2.property

/-- The complete face partition, valid over the integers before any coefficient
ring is chosen. It preserves the literal exterior face. -/
def chainFaceEquiv (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n)) :
    ChainFaceIndex n E m α ≃
      {s : Finset (FiniteVariable.{u} n) //
        koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α s} :=
  Equiv.ofBijective chainFaceToActual
    ⟨chainFaceToActual_injective hE α,chainFaceToActual_surjective hE α⟩

@[simp] lemma chainFaceEquiv_val (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n)) (a : ChainFaceIndex n E m α) :
    (chainFaceEquiv hE α a).val = a.2.val := rfl

@[simp] lemma chainFaceEquiv_card (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n)) (a : ChainFaceIndex n E m α) :
    (chainFaceEquiv hE α a).val.card = a.2.val.card := rfl

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainFaceBoundary -/
section

set_option autoImplicit false
set_option maxHeartbeats 10000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}

lemma residual_erase_anyDecidable {V : Type u} [Fintype V] [LinearOrder V] [DecidableEq V]
    (α : Exponent V) {F : Finset V} {x : V}
    (hF : faceExponent F ≤ α) (hx : x ∈ F) :
    α - faceExponent (F.erase x) = (α-faceExponent F)+Finsupp.single x 1 := by
  ext y
  by_cases hy : y=x
  · subst y
    have hle : 1 ≤ α x := by simpa [faceExponent_apply,hx] using hF x
    simpa [faceExponent_apply,hx] using (Nat.sub_add_cancel hle).symm
  · by_cases hm : y ∈ F <;> simp [faceExponent_apply,Finsupp.single_apply,hy,Ne.symm hy,hm]

def chainFaceErase (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) :
    ChainFaceIndex n E m α :=
  (chainFaceEquiv hE α).symm
    ⟨a.2.val.erase x,
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)
        (Finset.erase_subset x a.2.val) (chainFaceToActual a).property⟩

@[simp] lemma chainFaceErase_val (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) :
    (chainFaceErase hE a x).2.val = a.2.val.erase x := by
  have h := congrArg Subtype.val ((chainFaceEquiv hE α).apply_symm_apply
    (⟨a.2.val.erase x,
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)
        (Finset.erase_subset x a.2.val) (chainFaceToActual a).property⟩ :
      {s // koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α s}))
  exact h

lemma chainFaceErase_standard (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) (hx : x ∈ a.2.val) :
    chainFaceStandardIndex (chainFaceErase hE a x) =
      chainIndexMultiply hE (chainFaceStandardIndex a) x := by
  apply finiteChainIndexExponent_injective hE
  calc
    _ = α - faceExponent (chainFaceErase hE a x).2.val :=
      chainFaceStandardIndex_exponent (chainFaceErase hE a x)
    _ = α - faceExponent (a.2.val.erase x) :=
      congrArg (fun F => α - faceExponent F) (chainFaceErase_val hE a x)
    _ = (α-faceExponent a.2.val)+Finsupp.single x 1 :=
      residual_erase_anyDecidable α (F := a.2.val) (x := x) (chainFaceIndex_face_le a) hx
    _ = finiteChainIndexExponent (chainFaceStandardIndex a)+Finsupp.single x 1 :=
      congrArg (fun v => v+Finsupp.single x 1) (chainFaceStandardIndex_exponent a).symm
    _ = _ := (chainIndexMultiply_image hE (chainFaceStandardIndex a) x).symm

lemma chainFaceErase_weight_le (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) (hx : x ∈ a.2.val) :
    finiteChainFactorWeight.{u} (chainFaceErase hE a x).1.val ≤
      finiteChainFactorWeight.{u} a.1.val := by
  have h := chainIndexMultiply_factorWeight_le hE (chainFaceStandardIndex a) x
  rw [← chainFaceErase_standard hE a x hx] at h
  exact h

lemma chainFaceErase_of_allowed (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n)
    (hq : quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
      (α-finiteChainShift n a.1.val) (a.2.val.erase x)) :
    chainFaceErase hE a x = ⟨a.1,a.2.val.erase x,hq⟩ := by
  apply (chainFaceEquiv hE α).injective
  apply Subtype.ext
  simp only [chainFaceEquiv_val,chainFaceErase_val]

lemma chainFaceErase_weight_lt (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) (hx : x ∈ a.2.val)
    (hq : ¬ quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
      (α-finiteChainShift n a.1.val) (a.2.val.erase x)) :
    finiteChainFactorWeight.{u} (chainFaceErase hE a x).1.val <
      finiteChainFactorWeight.{u} a.1.val := by
  have hf : fullKoszulFaces (α-finiteChainShift n a.1.val) (a.2.val.erase x) :=
    (faceExponent_mono (Finset.erase_subset x a.2.val)).trans a.2.property.1
  have hb : Contains (finiteChainCoefficientFamily n a.1.val)
      ((α-finiteChainShift n a.1.val)-faceExponent (a.2.val.erase x)) := by
    by_contra hn
    exact hq ⟨hf,hn⟩
  have hr : ((α-finiteChainShift n a.1.val)-faceExponent (a.2.val.erase x)) =
      (α-finiteChainShift n a.1.val-faceExponent a.2.val)+Finsupp.single x 1 :=
    residual_erase_anyDecidable (α-finiteChainShift n a.1.val)
      (F := a.2.val) (x := x) a.2.property.1 hx
  have hb' : Contains (finiteChainCoefficientFamily n a.1.val)
      ((chainFaceStandardIndex a).2.val+Finsupp.single x 1) :=
    (congrArg (Contains (finiteChainCoefficientFamily n a.1.val)) hr).mp hb
  have h := chainIndexMultiply_factorWeight_lt hE (chainFaceStandardIndex a) x hb'
  rw [← chainFaceErase_standard hE a x hx] at h
  exact h

@[simp] lemma chainFaceErase_card (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) (x : FiniteVariable.{u} n) (hx : x ∈ a.2.val) :
    (chainFaceErase hE a x).2.val.card + 1 = a.2.val.card := by
  rw [chainFaceErase_val,Finset.card_erase_add_one hx]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainBoundaryMatrix -/
section

set_option autoImplicit false
set_option maxHeartbeats 10000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid CommAlg.Koszul CommAlg
universe u v
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)} {m : ℕ}
variable {k : Type v} {M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

lemma chainDifferential_strictLower
    (hE : finiteLatticeClosed n E) (α : Exponent (FiniteVariable.{u} n))
    (b : Module.Basis (ChainFaceIndex n E m α) k M)
    (d₁ d₀ : Module.End k M)
    (ε : ∀ a : ChainFaceIndex n E m α, {x // x ∈ a.2.val} → ℤˣ)
    (h₁ : ∀ a, d₁ (b a) =
      ∑ x : {x // x ∈ a.2.val}, ε a x • b (chainFaceErase hE a x.val))
    (h₀ : ∀ a, d₀ (b a) =
      ∑ x : {x // x ∈ a.2.val},
        if hq : quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
          (α-finiteChainShift n a.1.val) (a.2.val.erase x.val)
        then ε a x • b ⟨a.1,a.2.val.erase x.val,hq⟩ else 0)
    (a c : ChainFaceIndex n E m α)
    (hc : finiteChainFactorWeight.{u} a.1.val ≤ finiteChainFactorWeight.{u} c.1.val) :
    b.repr ((d₁-d₀) (b a)) c = 0 := by
  rw [LinearMap.sub_apply,h₁,h₀,← Finset.sum_sub_distrib,map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hq : quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
      (α-finiteChainShift n a.1.val) (a.2.val.erase x.val)
  · rw [dif_pos hq,chainFaceErase_of_allowed hE a x.val hq,sub_self,map_zero]
    rfl
  · rw [dif_neg hq,sub_zero,map_zsmul_unit,Module.Basis.repr_self]
    have hne : chainFaceErase hE a x.val ≠ c := by
      intro he
      have hh := chainFaceErase_weight_lt hE a x.val x.property hq
      rw [he] at hh
      exact (not_lt_of_ge hc) hh
    simp [Finsupp.single_apply,hne]

lemma chainDifferential_degreeSupport
    (hE : finiteLatticeClosed n E) (α : Exponent (FiniteVariable.{u} n))
    (b : Module.Basis (ChainFaceIndex n E m α) k M)
    (D : Module.End k M)
    (ε : ∀ a : ChainFaceIndex n E m α, {x // x ∈ a.2.val} → ℤˣ)
    (hD : ∀ a, D (b a) =
      ∑ x : {x // x ∈ a.2.val}, ε a x • b (chainFaceErase hE a x.val))
    (a c : ChainFaceIndex n E m α)
    (hc : c.2.val.card + 1 ≠ a.2.val.card) :
    b.repr (D (b a)) c=0 := by
  rw [hD,map_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [map_zsmul_unit,Module.Basis.repr_self]
  have hne : chainFaceErase hE a x.val ≠ c := by
    intro he
    have hh := chainFaceErase_card hE a x.val x.property
    rw [he] at hh
    exact hc hh
  simp [Finsupp.single_apply,hne]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PartialBlockContraction -/
section
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K B : Type*} [CommRing K] {M : B → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
def blockSpecialDifferential (d : ∀ i, Module.End K (M i)) : Module.End K (Π₀ i, M i) := DFinsupp.mapRange.linearMap d
def blockPartialHomotopy (a : B) (h : ∀ i, i≠a → Module.End K (M i)) : Module.End K (Π₀ i, M i) := DFinsupp.mapRange.linearMap (fun i => if hi : i=a then 0 else h i hi)
lemma blockProjection_section (a : B) :
    (DFinsupp.lapply a : (Π₀ i, M i) →ₗ[K] M a).comp (DFinsupp.lsingle a) = LinearMap.id := by
  ext x
  simp
lemma blockPartialHomotopy_projection (a : B) (h : ∀ i, i≠a → Module.End K (M i)) (x : Π₀ i, M i) : (blockPartialHomotopy a h x) a = 0 := by
  simp [blockPartialHomotopy]
lemma blockPartialHomotopy_contracts (d : ∀ i, Module.End K (M i))
    (a : B) (h : ∀ i, i≠a → Module.End K (M i))
    (hc : ∀ i (hi : i≠a), d i * h i hi + h i hi * d i = 1)
    (x : Π₀ i, M i) (hx : x a=0) :
    blockSpecialDifferential d (blockPartialHomotopy a h x) +
      blockPartialHomotopy a h (blockSpecialDifferential d x) = x := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [blockSpecialDifferential,blockPartialHomotopy,hx]
  · have hh := LinearMap.congr_fun (hc i hi) (x i)
    simpa [blockSpecialDifferential,blockPartialHomotopy,hi] using hh
variable {J : B → Type*}
lemma dfinsuppBasis_repr_apply (b : ∀ i, Module.Basis (J i) K (M i)) (x : Π₀ i, M i) (i : B) (j : J i) :
    (DFinsupp.basis b).repr x ⟨i,j⟩ = (b i).repr (x i) j := rfl
lemma dfinsuppBasis_apply (b : ∀ i, Module.Basis (J i) K (M i)) (i : B) (j : J i) :
    (DFinsupp.basis b) ⟨i,j⟩ = DFinsupp.single i (b i j) := by
  apply (DFinsupp.basis b).repr.injective
  ext a
  rcases a with ⟨r,t⟩
  rw [Module.Basis.repr_self,dfinsuppBasis_repr_apply]
  by_cases h : i=r
  · subst r
    simp [Finsupp.single_apply,Sigma.mk.inj_iff]
  · have hh : (⟨i,j⟩ : Sigma J) ≠ ⟨r,t⟩ := fun e => h (congrArg Sigma.fst e)
    simp [h,hh]
lemma blockMap_basis_weight (b : ∀ i, Module.Basis (J i) K (M i)) (rank : B → ℕ) (h : ∀ i, Module.End K (M i))
    (a c : Sigma J) (hac : rank a.1 < rank c.1) :
    (DFinsupp.basis b).repr (DFinsupp.mapRange.linearMap h ((DFinsupp.basis b) a)) c=0 := by
  rcases a with ⟨i,j⟩
  rcases c with ⟨r,t⟩
  change rank i < rank r at hac
  have hir : i ≠ r := fun he => by subst r; omega
  rw [dfinsuppBasis_repr_apply,dfinsuppBasis_apply]
  simp [hir]
end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainTotalComparison -/
section

set_option autoImplicit false
set_option maxHeartbeats 10000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

abbrev ChainTotalModule (n : Fin d → ℕ) (E : Finset (FiniteTuple n))
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :=
  Π₀ w : AdmissibleChain n E m α,
    TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))

def chainTotalBasis (n : Fin d → ℕ) (E : Finset (FiniteTuple n))
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    Module.Basis (ChainFaceIndex n E m α) k (ChainTotalModule n E m α k) :=
  DFinsupp.basis (fun w => totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)))

def chainTotalEquiv (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    ChainTotalModule n E m α k ≃ₗ[k]
      TotalFaceModule (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) :=
  (chainTotalBasis n E m α k).equiv
    (totalFaceBasis (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α))
    (chainFaceEquiv hE α)

lemma chainTotalEquiv_basis (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a : ChainFaceIndex n E m α) :
    chainTotalEquiv hE m α k (chainTotalBasis n E m α k a) =
      totalFaceBasis (k := k)
        (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)
        (chainFaceEquiv hE α a) :=
  Module.Basis.equiv_apply _ _ _ _

lemma chainTotalEquiv_symm_basis (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (s : {s // koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α s}) :
    (chainTotalEquiv hE m α k).symm
      (totalFaceBasis (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) s) =
      chainTotalBasis n E m α k ((chainFaceEquiv hE α).symm s) := by
  apply (chainTotalEquiv hE m α k).injective
  rw [LinearEquiv.apply_symm_apply,chainTotalEquiv_basis,Equiv.apply_symm_apply]

def chainTotalOrdinaryDifferential (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    Module.End k (ChainTotalModule n E m α k) :=
  (chainTotalEquiv hE m α k).symm.toLinearMap.comp
    ((idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)).comp
      (chainTotalEquiv hE m α k).toLinearMap)

def chainTotalSpecialDifferential (n : Fin d → ℕ) (E : Finset (FiniteTuple n))
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    Module.End k (ChainTotalModule n E m α k) :=
  DFinsupp.mapRange.linearMap (fun w =>
    quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))

lemma chainTotalBasis_apply (n : Fin d → ℕ) (E : Finset (FiniteTuple n))
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (w : AdmissibleChain n E m α)
    (s : {s // quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) s}) :
    chainTotalBasis n E m α k ⟨w,s⟩ =
      DFinsupp.single w (totalFaceBasis
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) s) := by
  change (DFinsupp.basis (fun z : AdmissibleChain n E m α =>
    totalFaceBasis (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
      (α-finiteChainShift n z.val)))) ⟨w,s⟩ = _
  rw [dfinsuppBasis_apply]
  apply DFinsupp.ext
  intro z
  by_cases h : w=z
  · subst z
    simp
  · simp [h]

lemma chainTotalOrdinaryDifferential_basis
    (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a : ChainFaceIndex n E m α) :
    chainTotalOrdinaryDifferential hE m α k (chainTotalBasis n E m α k a) =
      ∑ x : {x // x ∈ a.2.val},
        TauCeti.ExteriorAlgebra.basisEraseSign x.val a.2.val •
          chainTotalBasis n E m α k (chainFaceErase hE a x.val) := by
  simp only [chainTotalOrdinaryDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    chainTotalEquiv_basis,idealTotalDifferential_basis,map_sum,map_zsmul_unit,
    chainTotalEquiv_symm_basis]
  rfl

lemma dfinsuppBlockMap_lsingle {K B : Type*} [CommRing K] {M : B → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [DecidableEq B]
    (D : ∀ i, Module.End K (M i)) (i : B) (x : M i) :
    DFinsupp.mapRange.linearMap D ((DFinsupp.lsingle (R := K) (M := M) i) x) =
      (DFinsupp.lsingle (R := K) (M := M) i) (D i x) := by
  ext j
  by_cases h : i=j
  · subst j
    simp
  · simp [h]

set_option maxHeartbeats 100000 in
lemma chainTotalSpecialDifferential_basis
    (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a : ChainFaceIndex n E m α) :
    chainTotalSpecialDifferential n E m α k (chainTotalBasis n E m α k a) =
      ∑ x : {x // x ∈ a.2.val},
        if hq : quotientKoszulFaces (finiteChainCoefficientFamily n a.1.val)
          (α-finiteChainShift n a.1.val) (a.2.val.erase x.val)
        then TauCeti.ExteriorAlgebra.basisEraseSign x.val a.2.val •
          chainTotalBasis n E m α k ⟨a.1,a.2.val.erase x.val,hq⟩ else 0 := by
  rcases a with ⟨w,s⟩
  rw [chainTotalBasis_apply]
  change DFinsupp.mapRange.linearMap
    (fun z : AdmissibleChain n E m α => quotientTotalDifferential (k := k)
      (finiteChainCoefficientFamily n z.val) (α-finiteChainShift n z.val))
    ((DFinsupp.lsingle (R := k) (M := fun z : AdmissibleChain n E m α =>
      TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
        (α-finiteChainShift n z.val))) w) (totalFaceBasis _ s)) = _
  rw [dfinsuppBlockMap_lsingle,quotientTotalDifferential_basis,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hq
  · rw [map_zsmul_unit]
    exact congrArg (fun v : ChainTotalModule n E m α k =>
      TauCeti.ExteriorAlgebra.basisEraseSign x.val s.val • v)
      (chainTotalBasis_apply n E m α k w ⟨s.val.erase x.val,hq⟩).symm
  · exact (DFinsupp.lsingle (R := k) (M := fun z : AdmissibleChain n E m α =>
      TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n z.val)
        (α-finiteChainShift n z.val))) w).map_zero

lemma chainConjugate_square_zero {K A B : Type*}
    [CommRing K] [AddCommGroup A] [AddCommGroup B] [Module K A] [Module K B]
    (e : A ≃ₗ[K] B) (D : Module.End K B) (hD : ∀ y, D (D y)=0) :
    let d := e.symm.toLinearMap.comp (D.comp e.toLinearMap)
    d*d=0 := by
  apply LinearMap.ext
  intro x
  change e.symm (D (e (e.symm (D (e x)))))=0
  rw [e.apply_symm_apply,hD,map_zero]

lemma chainTotalOrdinaryDifferential_square_zero
    (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    chainTotalOrdinaryDifferential hE m α k *
      chainTotalOrdinaryDifferential hE m α k = 0 := by
  apply chainConjugate_square_zero (chainTotalEquiv hE m α k)
    (idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α))
  intro y
  apply Subtype.ext
  exact Simplicial.boundary_boundary y.val

lemma chainTotalSpecialDifferential_square_zero
    (n : Fin d → ℕ) (E : Finset (FiniteTuple n)) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k] :
    chainTotalSpecialDifferential n E m α k *
      chainTotalSpecialDifferential n E m α k = 0 := by
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro w
  change quotientTotalDifferential _ _ (quotientTotalDifferential _ _ (x w)) = 0
  exact LinearMap.congr_fun (quotientTotalDifferential_comp _ _) (x w)

theorem chainTotalDifferential_strictLower
    (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a c : ChainFaceIndex n E m α)
    (hc : finiteChainFactorWeight.{u} a.1.val ≤ finiteChainFactorWeight.{u} c.1.val) :
    (chainTotalBasis n E m α k).repr
      ((chainTotalOrdinaryDifferential hE m α k -
        chainTotalSpecialDifferential n E m α k)
        (chainTotalBasis n E m α k a)) c = 0 :=
  chainDifferential_strictLower hE α (chainTotalBasis n E m α k)
    (chainTotalOrdinaryDifferential hE m α k)
    (chainTotalSpecialDifferential n E m α k)
    (fun a x => TauCeti.ExteriorAlgebra.basisEraseSign x.val a.2.val)
    (chainTotalOrdinaryDifferential_basis hE m α k)
    (chainTotalSpecialDifferential_basis n E m α k) a c hc

theorem chainTotalOrdinaryDifferential_degreeSupport
    (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (k : Type u) [CommRing k]
    (a c : ChainFaceIndex n E m α)
    (hc : c.2.val.card+1 ≠ a.2.val.card) :
    (chainTotalBasis n E m α k).repr
      (chainTotalOrdinaryDifferential hE m α k
        (chainTotalBasis n E m α k a)) c = 0 :=
  chainDifferential_degreeSupport hE α (chainTotalBasis n E m α k)
    (chainTotalOrdinaryDifferential hE m α k)
    (fun a x => TauCeti.ExteriorAlgebra.basisEraseSign x.val a.2.val)
    (chainTotalOrdinaryDifferential_basis hE m α k) a c hc

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TotalFaceCoreExtras -/
section
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u v
variable {k : Type u} {V : Type v} [Fintype V] [LinearOrder V] [CommRing k]
variable {B C : Family V}
lemma quotientKoszulFaces_eq_of_contains (h : ∀ v, Contains B v ↔ Contains C v)
    (a : Exponent V) : quotientKoszulFaces B a = quotientKoszulFaces C a := by
  funext s
  apply propext
  exact and_congr Iff.rfl (not_congr (h _))

lemma quotientFaceProjection_eq_of_contains (h : ∀ v, Contains B v ↔ Contains C v)
    (a : Exponent V) :
    quotientFaceProjection (k := k) B a = quotientFaceProjection C a := by
  have he : forbiddenKoszulFaces B a = forbiddenKoszulFaces C a := by
    funext s
    exact propext (h _)
  simp only [quotientFaceProjection,he]


/-- Exterior creation on a quotient depends on its ideal-membership predicate,
so a redundant generating family need not literally omit the variable. -/
lemma quotientTotalCreation_contracts_of_contains
    {B C : Family V} {α : Exponent V} {e : V}
    (h : ∀ v, Contains C v ↔ Contains B v)
    (he : UnusedVariable C e) (hα : 0<α e) :
    quotientTotalDifferential (k := k) B α ∘ₗ quotientTotalCreation B α e +
      quotientTotalCreation B α e ∘ₗ quotientTotalDifferential B α = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.creation e x.val))) +
    quotientFaceProjection B α (Simplicial.creation e
      (quotientFaceProjection B α (Simplicial.boundary x.val))) = x.val
  rw [← quotientFaceProjection_eq_of_contains h α]
  apply quotientFace_contraction he hα
  simpa only [quotientKoszulFaces_eq_of_contains h α] using x.property

lemma quotientTotalCreation_raises_of_contains
    {B C : Family V} {α : Exponent V} {e : V}
    (h : ∀ v, Contains C v ↔ Contains B v)
    (he : UnusedVariable C e) (hα : 0<α e) (i : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x∈totalFacePiece (quotientKoszulFaces B α) i) :
    quotientTotalCreation B α e x∈totalFacePiece (quotientKoszulFaces B α) (i+1) := by
  have hxC : x.val∈Simplicial.Chains (quotientKoszulFaces C α) i := by
    simpa only [quotientKoszulFaces_eq_of_contains h α] using
      (show x.val∈Simplicial.Chains (quotientKoszulFaces B α) i from hx)
  have hy := creation_mem_chains e (fun _ hs => quotientKoszulFaces_insert he hα hs) hxC
  change quotientFaceProjection B α (Simplicial.creation e x.val)∈
    Simplicial.Chains (quotientKoszulFaces B α) (i+1)
  rw [← quotientFaceProjection_eq_of_contains h α,quotientFaceProjection,
    relativeProjection_eq_self (chains_mem_basisSpan hy)]
  simpa only [quotientKoszulFaces_eq_of_contains h α] using hy


lemma totalFacePiece_eq_basis_span (P : Finset V → Prop) (i : ℕ) :
    totalFacePiece (k := k) P i =
      Submodule.span k ((totalFaceBasis (k := k) P) '' {s | s.val.card=i}) := by
  apply Submodule.map_injective_of_injective
    (Submodule.subtype_injective (TotalFaceModule (k := k) P))
  have hle : Simplicial.Chains (k := k) P i ≤ TotalFaceModule (k := k) P :=
    fun _ hx => chains_mem_basisSpan hx
  rw [totalFacePiece,Submodule.map_comap_eq,Submodule.range_subtype,
    inf_eq_right.mpr hle,Submodule.map_span]
  change Submodule.span k _ = Submodule.span k _
  apply congrArg (Submodule.span k)
  ext x
  constructor
  · rintro ⟨s,⟨hs,hcard⟩,rfl⟩
    refine ⟨totalFaceBasis (k := k) P ⟨s,hs⟩,?_,totalFaceBasis_val P ⟨s,hs⟩⟩
    exact ⟨⟨s,hs⟩,hcard,rfl⟩
  · rintro ⟨y,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨s.val,⟨s.property,hs⟩,(totalFaceBasis_val P s).symm⟩

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerGeometry -/
section
set_option autoImplicit false

/-!
# Row maxima and the strictly lower first-power components

A fine exponent with row maximum `a` can involve only generators `b ≤ a`.
Every other first-power coefficient quotient has a positive degree in a variable
absent from its coordinate predecessor ideal. These are the exact hypotheses
needed for the integral kernel contraction; they are proved from the row data.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def singletonChain (a : E) : FiniteMultichain n E 1 :=
  ⟨fun _ => a,fun _ _ _ => le_rfl⟩

lemma singletonChain_eq (w : FiniteMultichain n E 1) : singletonChain (w.val 0) = w := by
  apply Subtype.ext
  funext s
  have hs : s = 0 := Subsingleton.elim _ _
  subst s
  rfl

def singletonChainEquiv : E ≃ FiniteMultichain n E 1 where
  toFun := singletonChain
  invFun w := w.val 0
  left_inv _ := rfl
  right_inv := singletonChain_eq

@[simp] lemma singletonChain_shift (a : E) :
    finiteChainShift.{u} n (singletonChain a) = finiteRowExponent n a.val := by
  simp [finiteChainShift,singletonChain]

@[simp] lemma singletonChain_coefficient (a : E) :
    finiteChainCoefficientFamily.{u} n (singletonChain a) = finitePredecessorFamily n E a.val := by
  ext v
  simp [finiteChainCoefficientFamily,singletonChain]

@[simp] lemma singletonChain_factorWeight (a : E) :
    finiteChainFactorWeight.{u} (singletonChain a) =
      reesVariableWeight (finiteTupleImage E) (finiteTupleToNat a.val) := by
  rw [finiteChainFactorWeight_sum]
  simp [singletonChain]

/-- Every variable in the exponent is at or below the stated coordinate. -/
def RowBound (β : Exponent (FiniteVariable.{u} n)) (a : FiniteTuple n) : Prop :=
  ∀ x, β x ≠ 0 → x.2.down ≤ a x.1

/-- The exponent contains the stated generator and has exactly its row maxima. -/
def RowMaximum (β : Exponent (FiniteVariable.{u} n)) (a : FiniteTuple n) : Prop :=
  finiteRowExponent n a ≤ β ∧ RowBound β a

lemma rowBound_of_block (w : FiniteMultichain n E 1) (p : Fin 1)
    (v : Exponent (FiniteVariable.{u} n)) :
    RowBound (finiteBlockDegree w p v + finiteRowExponent n (w.val p).val) (w.val p).val :=
  finiteBlockDegree_row_bound w p v

lemma rowMaximum_block {m : ℕ} (w : FiniteMultichain n E m) (p : Fin m)
    (v : Exponent (FiniteVariable.{u} n)) :
    RowMaximum (finiteBlockDegree w p v + finiteRowExponent n (w.val p).val) (w.val p).val :=
  ⟨le_add_of_nonneg_left zero_le,finiteBlockDegree_row_bound w p v⟩

lemma generator_le_of_rowBound {β : Exponent (FiniteVariable.{u} n)} {a b : FiniteTuple n}
    (hβ : RowBound β a) (hb : finiteRowExponent n b ≤ β) : b ≤ a := by
  intro r
  apply hβ ⟨r,ULift.up (b r)⟩
  have hh := hb ⟨r,ULift.up (b r)⟩
  simpa [finiteRowExponent_apply,Nat.one_le_iff_ne_zero] using hh

lemma proper_generator_weight_lt {β : Exponent (FiniteVariable.{u} n)} {a b : E}
    (hβ : RowMaximum β a.val) (hb : finiteRowExponent n b.val ≤ β) (hne : b ≠ a) :
    reesVariableWeight (finiteTupleImage E) (finiteTupleToNat b.val) <
      reesVariableWeight (finiteTupleImage E) (finiteTupleToNat a.val) := by
  apply predecessor_weight_strict
    (mem_map.mpr ⟨a.val,a.property,rfl⟩) (generator_le_of_rowBound hβ.2 hb)
  intro he
  exact hne (Subtype.ext (finiteTupleToNat_injective he))

/-- A concrete higher column in every proper lower generator. -/
lemma exists_higher_row {a b : FiniteTuple n} (hba : b ≤ a) (hne : b ≠ a) :
    ∃ r, b r < a r := by
  by_contra hn
  push_neg at hn
  apply hne
  funext r
  exact le_antisymm (hba r) (hn r)

/-- The unused coordinate is positive in the actual residual fine exponent. -/
lemma lower_generator_positive_unused {β : Exponent (FiniteVariable.{u} n)} {a b : FiniteTuple n}
    (hβ : RowMaximum β a) (hb : finiteRowExponent n b ≤ β) (hne : b ≠ a) :
    ∃ r, b r < a r ∧ 0 < (β - finiteRowExponent n b) ⟨r,ULift.up (a r)⟩ := by
  obtain ⟨r,hr⟩ := exists_higher_row (generator_le_of_rowBound hβ.2 hb) hne
  refine ⟨r,hr,?_⟩
  have hh : 0 < β ⟨r,ULift.up (a r)⟩ := by
    simpa [finiteRowExponent_apply,Nat.succ_le_iff] using hβ.1 ⟨r,ULift.up (a r)⟩
  simpa only [Finsupp.tsub_apply,finiteRowExponent_apply,if_neg (ne_of_lt hr),Nat.sub_zero]
    using hh

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerBlockContractions -/
section
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma coordinatePredecessor_isUnused (E : Finset (FiniteTuple n))
    (a : FiniteTuple n) (r : Fin d) (j : Fin (n r)) (haj : a r≤j) :
    UnusedVariable (finiteCoordinatePredecessorFamily E a) ⟨r,ULift.up j⟩ := by
  intro v hv
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  obtain ⟨_,hba,_⟩ := mem_filter.mp hb
  simp only [Finsupp.tsub_apply,finiteRowExponent_apply]
  by_cases ha : a r=j
  · simp only [ha,ite_true]
    split_ifs <;> omega
  · have hb : b r≠j := ne_of_lt ((hba r).trans_lt (lt_of_le_of_ne haj ha))
    simp [ha,hb]

/-- A concrete, integral contraction of each proper lower first-power block.
All hypotheses concern the original finite sublattice and the literal exponent. -/
theorem lowerFirstPowerBlock_contractible
    (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a b : E}
    (hβ : RowMaximum β a.val) (hb : finiteRowExponent n b.val≤β) (hne : b≠a) :
    ∃ H : Module.End k
      (TotalFaceModule (k := k) (quotientKoszulFaces (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val))),
      quotientTotalDifferential (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val) * H +
      H * quotientTotalDifferential (finitePredecessorFamily n E b.val)
        (β-finiteRowExponent n b.val) = 1 ∧
      ∀ i x, x∈totalFacePiece
        (quotientKoszulFaces (finitePredecessorFamily n E b.val)
          (β-finiteRowExponent n b.val)) i →
        H x∈totalFacePiece
        (quotientKoszulFaces (finitePredecessorFamily n E b.val)
          (β-finiteRowExponent n b.val)) (i+1) := by
  obtain ⟨r,hr,hpos⟩ := lower_generator_positive_unused hβ hb
    (fun h => hne (Subtype.ext h))
  refine ⟨quotientTotalCreation (finitePredecessorFamily n E b.val)
    (β-finiteRowExponent n b.val) ⟨r,ULift.up (a.val r)⟩, ?_, ?_⟩
  · exact quotientTotalCreation_contracts_of_contains
      (finiteCoordinatePredecessor_contains_iff hE b.property)
      (coordinatePredecessor_isUnused E b.val r (a.val r) hr.le) hpos
  · exact quotientTotalCreation_raises_of_contains
      (finiteCoordinatePredecessor_contains_iff hE b.property)
      (coordinatePredecessor_isUnused E b.val r (a.val r) hr.le) hpos
/-- The distinguished coefficient block in the literal first-power normal form. -/
def firstPowerTarget {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) : AdmissibleChain n E 1 β :=
  ⟨singletonChain a,by simpa using hβ.1⟩

theorem properFirstPowerChainBlock_contractible
    (hE : finiteLatticeClosed n E)
    {β : Exponent (FiniteVariable.{u} n)} {a : E}
    (hβ : RowMaximum β a.val) (w : AdmissibleChain n E 1 β)
    (hw : w≠firstPowerTarget hβ) :
    ∃ H : Module.End k
      (TotalFaceModule (k := k) (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val))),
      quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val) * H +
      H * quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
        (β-finiteChainShift n w.val) = 1 ∧
      ∀ i x, x∈totalFacePiece
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (β-finiteChainShift n w.val)) i →
        H x∈totalFacePiece
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (β-finiteChainShift n w.val)) (i+1) := by
  let b : E := w.val.val 0
  have he : singletonChain b=w.val := singletonChain_eq w.val
  have hb : finiteRowExponent n b.val≤β := by
    simpa only [← he,singletonChain_shift] using w.property
  have hba : b≠a := by
    intro h
    apply hw
    apply Subtype.ext
    change w.val=singletonChain a
    rw [←he,h]
  have hcoef : finiteChainCoefficientFamily.{u} n w.val=finitePredecessorFamily n E b.val := by
    rw [←he,singletonChain_coefficient]
  have hshift : finiteChainShift.{u} n w.val=finiteRowExponent n b.val := by
    rw [←he,singletonChain_shift]
  rw [hcoef,hshift]
  exact lowerFirstPowerBlock_contractible (k := k) hE hβ hb hba

end FourPapers.Sublattice

end

end

/- BEGIN EXACT BODY: FourPapers.Universal.TriangularBasis -/
section

section
/-! # Unitriangular changes of basis with a natural-valued rank

The index set may be infinite and the coefficient ring is arbitrary. Each
individual vector has finite support because it is represented in a genuine
module basis. The strict decrease of a natural-valued rank supplies the entire
termination argument.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset Submodule

variable {I K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

theorem linearIndependent_of_rank_triangular
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_contra hn
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
  have hsim : (l.support.image rank).Nonempty := hs.image rank
  let r := (l.support.image rank).max' hsim
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp (Finset.max'_mem _ hsim)
  have himax : ∀ j ∈ l.support, rank j ≤ rank i := by
    intro j hj
    rw [hir]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hc : (b.repr (Finsupp.linearCombination K v l)) i = l i := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hdiag, mul_one]
    · intro j hj hji
      rw [htri j i hji (himax j hj), mul_zero]
    · intro hni
      exact (hni hi).elim
  rw [hl, map_zero, Finsupp.zero_apply] at hc
  exact (Finsupp.mem_support_iff.mp hi) hc.symm

theorem span_eq_top_of_rank_triangular
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    Submodule.span K (Set.range v) = ⊤ := by
  classical
  let S := Submodule.span K (Set.range v)
  have hb : ∀ n : ℕ, ∀ i, rank i = n → b i ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hir
      have hw : v i - b i ∈ S := by
        rw [← b.linearCombination_repr (v i - b i), Finsupp.linearCombination_apply,
          Finsupp.sum]
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.smul_mem
        have hji : j ≠ i := by
          intro he
          subst j
          have hnz := Finsupp.mem_support_iff.mp hj
          exact hnz (by simp [hdiag])
        have hjlt : rank j < n := by
          by_contra hnlt
          have hrij : rank i ≤ rank j := by omega
          have hnz := Finsupp.mem_support_iff.mp hj
          apply hnz
          simp [htri i j (Ne.symm hji) hrij, hji]
        exact ih (rank j) hjlt j rfl
      have hv : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
      have hh := S.sub_mem hv hw
      simpa only [sub_sub_cancel] using hh
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hb (rank i) i rfl

/-- A genuine module basis obtained from a unitriangular family, without a
field assumption or any finite-dimensionality assumption. -/
def rankTriangularBasis
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) :
    Module.Basis I K M :=
  Module.Basis.mk (linearIndependent_of_rank_triangular b v rank hdiag htri)
    (by rw [span_eq_top_of_rank_triangular b v rank hdiag htri])

@[simp] theorem rankTriangularBasis_apply
    (b : Module.Basis I K M) (v : I → M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (v i) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (v i) j = 0) (i : I) :
    rankTriangularBasis b v rank hdiag htri i = v i :=
  Module.Basis.mk_apply _ _ _

end FourPapers.Universal
end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Perturbation -/
section

set_option autoImplicit false

/-!
# Integral contractions under strictly lower weight perturbations

The operator `1 + (d-d₀)h` intertwines the two differentials whenever `h`
contracts `d₀`.  If the perturbation lowers a natural-valued basis weight, this
operator is an actual module automorphism by the checked triangular basis
construction. Thus the perturbed complex is contractible without dividing by
coefficients or imposing a field hypothesis.
-/

noncomputable section

namespace FourPapers.Sublattice

open FourPapers.Universal

variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def triangularLinearEquiv
    (b : Module.Basis I K M) (f : M →ₗ[K] M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (f (b i)) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (f (b i)) j = 0) : M ≃ₗ[K] M :=
  b.equiv (rankTriangularBasis b (fun i => f (b i)) rank hdiag htri) (Equiv.refl I)

@[simp] lemma triangularLinearEquiv_toLinearMap
    (b : Module.Basis I K M) (f : M →ₗ[K] M) (rank : I → ℕ)
    (hdiag : ∀ i, b.repr (f (b i)) i = 1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (f (b i)) j = 0) :
    (triangularLinearEquiv b f rank hdiag htri).toLinearMap = f := by
  apply b.ext
  intro i
  simp [triangularLinearEquiv,Module.Basis.equiv_apply]

def perturbationMap (d d₀ h : Module.End K M) : Module.End K M := 1 + (d - d₀) * h

lemma perturbationMap_intertwines (d d₀ h : Module.End K M)
    (hd : d * d = 0) (hd₀ : d₀ * d₀ = 0) (hh : d₀ * h + h * d₀ = 1) :
    d * perturbationMap d d₀ h = perturbationMap d d₀ h * d₀ := by
  apply sub_eq_zero.mp
  calc
    d * perturbationMap d d₀ h - perturbationMap d d₀ h * d₀ =
        (d - d₀) - (d - d₀) * (d₀ * h + h * d₀) +
          (d * d) * h - (d₀ * d₀) * h := by
      unfold perturbationMap
      noncomm_ring
    _ = 0 := by rw [hh,hd,hd₀]; simp

lemma perturbationMap_eq (d d₀ h : Module.End K M) (hh : d₀ * h + h * d₀ = 1) :
    perturbationMap d d₀ h = d * h + h * d₀ := by
  calc
    perturbationMap d d₀ h = (d₀ * h + h * d₀) + (d - d₀) * h := by
      rw [hh]
      rfl
    _ = _ := by noncomm_ring

def perturbationEquiv
    (b : Module.Basis I K M) (rank : I → ℕ) (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d - d₀) (h (b i))) j = 0) : M ≃ₗ[K] M :=
  triangularLinearEquiv b (perturbationMap d d₀ h) rank
    (by
      intro i
      have hh := hlower i i le_rfl
      simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
      simp [perturbationMap,hh])
    (by
      intro i j hij hr
      have hh := hlower i j hr
      simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
      simp [perturbationMap,hh,hij])

@[simp] lemma perturbationEquiv_toLinearMap
    (b : Module.Basis I K M) (rank : I → ℕ) (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d - d₀) (h (b i))) j = 0) :
    (perturbationEquiv b rank d d₀ h hlower).toLinearMap = perturbationMap d d₀ h := by
  apply triangularLinearEquiv_toLinearMap

lemma inverse_intertwines (f : M ≃ₗ[K] M) (d d₀ : Module.End K M)
    (hf : d * f.toLinearMap = f.toLinearMap * d₀) :
    f.symm.toLinearMap * d = d₀ * f.symm.toLinearMap := by
  have hfg : f.toLinearMap * f.symm.toLinearMap = 1 := by ext x; simp
  have hgf : f.symm.toLinearMap * f.toLinearMap = 1 := by ext x; simp
  calc
    f.symm.toLinearMap * d =
        (f.symm.toLinearMap * d) * (f.toLinearMap * f.symm.toLinearMap) := by rw [hfg,mul_one]
    _ = f.symm.toLinearMap * (d * f.toLinearMap) * f.symm.toLinearMap := by noncomm_ring
    _ = f.symm.toLinearMap * (f.toLinearMap * d₀) * f.symm.toLinearMap := by rw [hf]
    _ = (f.symm.toLinearMap * f.toLinearMap) * d₀ * f.symm.toLinearMap := by noncomm_ring
    _ = d₀ * f.symm.toLinearMap := by rw [hgf,one_mul]

/-- Explicit contraction after an arbitrary strictly lower weight perturbation. -/
theorem lowerPerturbation_contracts
    (b : Module.Basis I K M) (rank : I → ℕ) (d d₀ h : Module.End K M)
    (hd : d * d = 0) (hd₀ : d₀ * d₀ = 0) (hh : d₀ * h + h * d₀ = 1)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d - d₀) (h (b i))) j = 0) :
    let H := h * (perturbationEquiv b rank d d₀ h hlower).symm.toLinearMap
    d * H + H * d = 1 := by
  let f := perturbationEquiv b rank d d₀ h hlower
  have hf : f.toLinearMap = perturbationMap d d₀ h := perturbationEquiv_toLinearMap ..
  have hi := inverse_intertwines f d d₀ (by
    rw [hf]
    exact perturbationMap_intertwines d d₀ h hd hd₀ hh)
  change d * (h * f.symm.toLinearMap) + (h * f.symm.toLinearMap) * d = 1
  calc
    d * (h * f.symm.toLinearMap) + (h * f.symm.toLinearMap) * d =
        (d * h) * f.symm.toLinearMap + h * (f.symm.toLinearMap * d) := by noncomm_ring
    _ = (d * h) * f.symm.toLinearMap + h * (d₀ * f.symm.toLinearMap) := by rw [hi]
    _ = (d * h + h * d₀) * f.symm.toLinearMap := by noncomm_ring
    _ = f.toLinearMap * f.symm.toLinearMap := by rw [← perturbationMap_eq d d₀ h hh,← hf]
    _ = 1 := by ext x; simp

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ChainSection -/
section

set_option autoImplicit false

/-!
# Correcting a degreewise section into a chain section

This is the explicit integral correction used in Theorem 7.1.  It requires no
field and does not choose homology representatives: the entire source complex
lifts.  The kernel contraction will be obtained from the bounded weight strand.
-/

namespace FourPapers.Sublattice

variable {K X Y : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def sectionDefect (dX : X →ₗ[K] X) (dY : Y →ₗ[K] Y) (s : Y →ₗ[K] X) : Y →ₗ[K] X :=
  dX.comp s - s.comp dY

lemma sectionDefect_anticommute
    (dX : X →ₗ[K] X) (dY : Y →ₗ[K] Y) (s : Y →ₗ[K] X)
    (hX : dX.comp dX = 0) (hY : dY.comp dY = 0) (y : Y) :
    dX (sectionDefect dX dY s y) + sectionDefect dX dY s (dY y) = 0 := by
  have hx : dX (dX (s y)) = 0 := LinearMap.congr_fun hX (s y)
  have hy : dY (dY y) = 0 := LinearMap.congr_fun hY y
  simp [sectionDefect,hx,hy]

lemma sectionDefect_mem_kernel
    (f : X →ₗ[K] Y) (dX : X →ₗ[K] X) (dY : Y →ₗ[K] Y) (s : Y →ₗ[K] X)
    (hcomm : dY.comp f = f.comp dX) (hsection : f.comp s = LinearMap.id)
    (y : Y) : f (sectionDefect dX dY s y) = 0 := by
  have hc : dY (f (s y)) = f (dX (s y)) := LinearMap.congr_fun hcomm (s y)
  have hs : ∀ z, f (s z) = z := fun z => LinearMap.congr_fun hsection z
  simp only [sectionDefect,LinearMap.sub_apply,LinearMap.comp_apply,map_sub,← hc,hs,sub_self]

def correctedSection
    (dX : X →ₗ[K] X) (dY : Y →ₗ[K] Y) (s : Y →ₗ[K] X) (h : X →ₗ[K] X) :
    Y →ₗ[K] X := s - h.comp (sectionDefect dX dY s)

/-- A degreewise section of a surjective chain map becomes a chain section after
subtracting the contraction applied to its differential defect. -/
theorem correctedSection_is_chain_section
    (f : X →ₗ[K] Y) (dX : X →ₗ[K] X) (dY : Y →ₗ[K] Y)
    (s : Y →ₗ[K] X) (h : X →ₗ[K] X)
    (hX : dX.comp dX = 0) (hY : dY.comp dY = 0)
    (hcomm : dY.comp f = f.comp dX) (hsection : f.comp s = LinearMap.id)
    (hkernel : ∀ x, f x = 0 → f (h x) = 0)
    (hcontract : ∀ x, f x = 0 → dX (h x) + h (dX x) = x) :
    f.comp (correctedSection dX dY s h) = LinearMap.id ∧
      dX.comp (correctedSection dX dY s h) =
        (correctedSection dX dY s h).comp dY := by
  have he : ∀ y, f (sectionDefect dX dY s y) = 0 :=
    sectionDefect_mem_kernel f dX dY s hcomm hsection
  constructor
  · ext y
    have hs : f (s y) = y := LinearMap.congr_fun hsection y
    simp only [LinearMap.comp_apply,correctedSection,LinearMap.sub_apply,map_sub,
      hkernel _ (he y),sub_zero,LinearMap.id_apply,hs]
  · ext y
    have hh := hcontract _ (he y)
    have ha := congrArg h (sectionDefect_anticommute dX dY s hX hY y)
    simp only [map_add,map_zero] at ha
    have hd : sectionDefect dX dY s y = dX (s y) - s (dY y) := rfl
    simp only [LinearMap.comp_apply,correctedSection,LinearMap.sub_apply,map_sub]
    have hn := eq_neg_of_add_eq_zero_left ha
    rw [hn] at hh
    have hh' : dX (h (sectionDefect dX dY s y)) - h (sectionDefect dX dY s (dY y)) =
        dX (s y) - s (dY y) :=
      (show dX (h (sectionDefect dX dY s y)) - h (sectionDefect dX dY s (dY y)) =
          sectionDefect dX dY s y from by simpa only [sub_eq_add_neg] using hh).trans hd
    apply sub_eq_zero.mp
    calc
      (dX (s y) - dX (h (sectionDefect dX dY s y))) -
          (s (dY y) - h (sectionDefect dX dY s (dY y))) =
        (dX (s y) - s (dY y)) -
          (dX (h (sectionDefect dX dY s y)) -
            h (sectionDefect dX dY s (dY y))) := by abel
      _ = 0 := by rw [← hh']; simp

end FourPapers.Sublattice

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerPerturbation -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
variable {K M N I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

lemma perturbation_commutator (d d₀ h : Module.End K M)
    (hd : d*d=0) (hd₀ : d₀*d₀=0) :
    d * perturbationMap d d₀ h - perturbationMap d d₀ h * d₀ =
      (d-d₀) * (1-(d₀*h+h*d₀)) := by
  calc
    _ = (d-d₀) - (d-d₀)*(d₀*h+h*d₀) + (d*d)*h - (d₀*d₀)*h := by
      unfold perturbationMap
      noncomm_ring
    _ = _ := by rw [hd,hd₀]; noncomm_ring

theorem partialPerturbation_contracts
    (b : Module.Basis I K M) (rank : I → ℕ)
    (q : M →ₗ[K] N) (d d₀ h : Module.End K M)
    (hd : d*d=0) (hd₀ : d₀*d₀=0)
    (hqδ : ∀ x, q ((d-d₀) x)=0)
    (hqh : ∀ x, q (h x)=0)
    (hh : ∀ x, q x=0 → d₀ (h x)+h (d₀ x)=x)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d-d₀) (h (b i))) j=0) :
    let H := h * (perturbationEquiv b rank d d₀ h hlower).symm.toLinearMap
    (∀ x, q (H x)=0) ∧ ∀ x, q x=0 → d (H x)+H (d x)=x := by
  let e := perturbationEquiv b rank d d₀ h hlower
  have he (x : M) : e x = x + (d-d₀) (h x) := by
    change e.toLinearMap x = _
    rw [show e.toLinearMap = perturbationMap d d₀ h from perturbationEquiv_toLinearMap ..]
    rfl
  have hqe (x : M) : q (e x)=q x := by rw [he,map_add,hqδ,add_zero]
  have hqinv (x : M) : q (e.symm x)=q x := by
    calc
      _ = q (e (e.symm x)) := (hqe _).symm
      _ = _ := by rw [e.apply_symm_apply]
  have hinter (x : M) (hx : q x=0) : d (e x)=e (d₀ x) := by
    have hc := LinearMap.congr_fun (perturbation_commutator d d₀ h hd hd₀) x
    change d (perturbationMap d d₀ h x) - perturbationMap d d₀ h (d₀ x) =
      (d-d₀) (x-(d₀ (h x)+h (d₀ x))) at hc
    rw [hh x hx,sub_self,map_zero] at hc
    have hp : ∀ y, perturbationMap d d₀ h y=e y := fun y => (he y).symm
    simpa only [hp] using sub_eq_zero.mp hc
  constructor
  · intro x
    exact hqh _
  · intro x hx
    let y := e.symm x
    have hy : q y=0 := (hqinv x).trans hx
    have hid : e.symm (d x)=d₀ y := by
      apply e.injective
      rw [e.apply_symm_apply]
      simpa only [y,e.apply_symm_apply] using hinter y hy
    change d (h y)+h (e.symm (d x))=x
    rw [hid]
    calc
      d (h y)+h (d₀ y) = (d₀ (h y)+h (d₀ y))+(d (h y)-d₀ (h y)) := by abel
      _ = y+(d-d₀) (h y) := by rw [hh y hy]; rfl
      _ = e y := (he y).symm
      _ = x := e.apply_symm_apply x

theorem partialPerturbation_chain_section
    (b : Module.Basis I K M) (rank : I → ℕ)
    (q : M →ₗ[K] N) (d d₀ h : Module.End K M)
    (dN : Module.End K N) (s : N →ₗ[K] M)
    (hd : d*d=0) (hd₀ : d₀*d₀=0) (hdN : dN*dN=0)
    (hqδ : ∀ x, q ((d-d₀) x)=0)
    (hqh : ∀ x, q (h x)=0)
    (hh : ∀ x, q x=0 → d₀ (h x)+h (d₀ x)=x)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d-d₀) (h (b i))) j=0)
    (hcomm : dN.comp q=q.comp d) (hs : q.comp s=LinearMap.id) :
    let H := h * (perturbationEquiv b rank d d₀ h hlower).symm.toLinearMap
    q.comp (correctedSection d dN s H)=LinearMap.id ∧
      d.comp (correctedSection d dN s H)=(correctedSection d dN s H).comp dN := by
  have hH := partialPerturbation_contracts b rank q d d₀ h hd hd₀ hqδ hqh hh hlower
  exact correctedSection_is_chain_section q d dN s _
    hd hdN hcomm hs (fun x _ => hH.1 x) hH.2

lemma lower_after_weight_preserving
    (b : Module.Basis I K M) (rank : I → ℕ) (δ h : Module.End K M)
    (hδ : ∀ i j, rank i ≤ rank j → b.repr (δ (b i)) j = 0)
    (hh : ∀ i j, rank i < rank j → b.repr (h (b i)) j = 0) :
    ∀ i j, rank i ≤ rank j → b.repr (δ (h (b i))) j = 0 := by
  classical
  intro i j hij
  rw [← b.linearCombination_repr (h (b i))]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a ha
  have hai : rank a ≤ rank i := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ha) (hh i a (lt_of_not_ge hn))
  rw [hδ a j (hai.trans hij), mul_zero]

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MaximalBlockSection -/
section

noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K B : Type*} [CommRing K] {M : B → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] {J : B → Type*}

lemma blockSpecialDifferential_square_zero (dB : ∀ i, Module.End K (M i))
    (hdB : ∀ i, dB i * dB i = 0) :
    blockSpecialDifferential dB * blockSpecialDifferential dB = 0 := by
  apply LinearMap.ext
  intro x
  ext i
  exact LinearMap.congr_fun (hdB i) (x i)

lemma maximalBlock_projection_lower (b : ∀ i, Module.Basis (J i) K (M i))
    (rank : B → ℕ) (a : B) (hmax : ∀ i, rank i ≤ rank a)
    (δ : Module.End K (Π₀ i, M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr (δ ((DFinsupp.basis b) i)) j = 0) :
    (DFinsupp.lapply a).comp δ = 0 := by
  apply (DFinsupp.basis b).ext
  intro i
  apply (b a).repr.injective
  ext j
  change (b a).repr ((δ ((DFinsupp.basis b) i)) a) j = (b a).repr 0 j
  rw [map_zero, Finsupp.zero_apply]
  exact hlower i ⟨a,j⟩ (hmax i.1)

lemma blockPerturbationLower (b : ∀ i, Module.Basis (J i) K (M i))
    (rank : B → ℕ) (a : B)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d - blockSpecialDifferential dB)
        ((DFinsupp.basis b) i)) j = 0) :
    ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d - blockSpecialDifferential dB)
        (blockPartialHomotopy a h ((DFinsupp.basis b) i))) j = 0 := by
  apply lower_after_weight_preserving (DFinsupp.basis b) (fun i => rank i.1)
    (d - blockSpecialDifferential dB) (blockPartialHomotopy a h) hlower
  exact blockMap_basis_weight b rank (fun i => if hi : i = a then 0 else h i hi)

def blockKernelHomotopy (b : ∀ i, Module.Basis (J i) K (M i))
    (rank : B → ℕ) (a : B)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d - blockSpecialDifferential dB)
        ((DFinsupp.basis b) i)) j = 0) : Module.End K (Π₀ i, M i) :=
  blockPartialHomotopy a h *
    (perturbationEquiv (DFinsupp.basis b) (fun i => rank i.1) d
      (blockSpecialDifferential dB) (blockPartialHomotopy a h)
      (blockPerturbationLower b rank a d dB h hlower)).symm.toLinearMap

def blockCorrectedSection (b : ∀ i, Module.Basis (J i) K (M i))
    (rank : B → ℕ) (a : B)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d - blockSpecialDifferential dB)
        ((DFinsupp.basis b) i)) j = 0) : M a →ₗ[K] Π₀ i, M i :=
  correctedSection d (dB a) (DFinsupp.lsingle a)
    (blockKernelHomotopy b rank a d dB h hlower)

theorem blockCorrectedSection_is_chain (b : ∀ i, Module.Basis (J i) K (M i))
    (rank : B → ℕ) (a : B) (hmax : ∀ i, rank i ≤ rank a)
    (d : Module.End K (Π₀ i, M i)) (dB : ∀ i, Module.End K (M i))
    (h : ∀ i, i ≠ a → Module.End K (M i))
    (hd : d * d = 0) (hdB : ∀ i, dB i * dB i = 0)
    (hh : ∀ i (hi : i ≠ a), dB i * h i hi + h i hi * dB i = 1)
    (hlower : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((d - blockSpecialDifferential dB)
        ((DFinsupp.basis b) i)) j = 0) :
    (DFinsupp.lapply a).comp (blockCorrectedSection b rank a d dB h hlower) = LinearMap.id ∧
      d.comp (blockCorrectedSection b rank a d dB h hlower) =
        (blockCorrectedSection b rank a d dB h hlower).comp (dB a) := by
  have hqδ : ∀ x, ((d - blockSpecialDifferential dB) x) a = 0 := by
    intro x
    exact LinearMap.congr_fun (maximalBlock_projection_lower b rank a hmax
      (d - blockSpecialDifferential dB) hlower) x
  have hcomm : (dB a).comp (DFinsupp.lapply a) =
      (DFinsupp.lapply a).comp d := by
    apply LinearMap.ext
    intro x
    have ht := hqδ x
    change (d x) a - (blockSpecialDifferential dB x) a = 0 at ht
    exact (sub_eq_zero.mp ht).symm
  exact partialPerturbation_chain_section (DFinsupp.basis b) (fun i => rank i.1)
    (DFinsupp.lapply a) d (blockSpecialDifferential dB) (blockPartialHomotopy a h)
    (dB a) (DFinsupp.lsingle a) hd (blockSpecialDifferential_square_zero dB hdB)
    (hdB a) hqδ (blockPartialHomotopy_projection a h)
    (blockPartialHomotopy_contracts dB a h hh)
    (blockPerturbationLower b rank a d dB h hlower) hcomm (blockProjection_section a)
end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TriangularInverseSubspace -/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
lemma repr_zero_of_mem_basis_span (b : Module.Basis I K M) (S : Set I)
    {x : M} (hx : x ∈ Submodule.span K (b '' S)) {i : I} (hi : i ∉ S) : b.repr x i=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,hj,rfl⟩ := hx
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [hji,Ne.symm hji]
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx,ihy]
  | smul c x hx ih => simp [ih]
theorem triangularInverse_preserves_span (b : Module.Basis I K M) (rank : I → ℕ)
    (f : M ≃ₗ[K] M)
    (hdiag : ∀ i, b.repr (f (b i)) i=1)
    (htri : ∀ i j, i ≠ j → rank i ≤ rank j → b.repr (f (b i)) j=0)
    (S : Set I)
    (hpres : ∀ x, x ∈ Submodule.span K (b '' S) → f x ∈ Submodule.span K (b '' S))
    {x : M} (hx : x ∈ Submodule.span K (b '' S)) : f.symm x ∈ Submodule.span K (b '' S) := by
  let P := Submodule.span K (b '' S)
  have hb : ∀ r : ℕ, ∀ i, rank i=r → i∈S → f.symm (b i)∈P := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hir hi
      let w := f (b i)-b i
      have hbi : b i ∈ P := Submodule.subset_span ⟨i,hi,rfl⟩
      have hwP : w ∈ P := P.sub_mem (hpres _ hbi) hbi
      have hfw : f.symm w ∈ P := by
        rw [← b.linearCombination_repr w,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
        apply Submodule.sum_mem
        intro j hj
        rw [map_smul]
        apply Submodule.smul_mem
        have hne := Finsupp.mem_support_iff.mp hj
        have hji : j ≠ i := by
          intro h
          subst j
          exact hne (by simp [w,hdiag])
        have hjr : rank j < r := by
          by_contra hn
          have hrij : rank i ≤ rank j := by omega
          apply hne
          simp [w,htri i j (Ne.symm hji) hrij,hji,Ne.symm hji]
        have hjS : j ∈ S := by
          by_contra hn
          exact hne (repr_zero_of_mem_basis_span b S hwP hn)
        exact ih (rank j) hjr j rfl hjS
      simpa [w] using P.sub_mem hbi hfw
  rw [← b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  apply hb (rank i) i rfl
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hi) (repr_zero_of_mem_basis_span b S hx hn)
theorem perturbationInverse_preserves_span (b : Module.Basis I K M) (rank : I → ℕ)
    (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d-d₀) (h (b i))) j=0)
    (S : Set I)
    (hpres : ∀ x, x ∈ Submodule.span K (b '' S) → perturbationMap d d₀ h x ∈ Submodule.span K (b '' S))
    {x : M} (hx : x ∈ Submodule.span K (b '' S)) :
    (perturbationEquiv b rank d d₀ h hlower).symm x ∈ Submodule.span K (b '' S) := by
  apply triangularInverse_preserves_span b rank
  · intro i
    change b.repr ((perturbationEquiv b rank d d₀ h hlower).toLinearMap (b i)) i=1
    rw [perturbationEquiv_toLinearMap]
    have hh := hlower i i le_rfl
    simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
    simp [perturbationMap,hh]
  · intro i j hij hr
    change b.repr ((perturbationEquiv b rank d d₀ h hlower).toLinearMap (b i)) j=0
    rw [perturbationEquiv_toLinearMap]
    have hh := hlower i j hr
    simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply] at hh
    simp [perturbationMap,hh,hij]
  · intro y hy
    change (perturbationEquiv b rank d d₀ h hlower).toLinearMap y ∈ _
    rw [perturbationEquiv_toLinearMap]
    exact hpres y hy
  · exact hx
end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PerturbationDegrees -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def basisDegreePiece (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) : Submodule K M :=
  Submodule.span K (b '' {i | degree i = n})

lemma perturbationMap_preserves_degree (b : Module.Basis I K M) (degree : I → ℕ)
    (d d₀ h : Module.End K M)
    (hd : ∀ n x, x ∈ basisDegreePiece b degree (n+1) → d x ∈ basisDegreePiece b degree n)
    (hd₀ : ∀ n x, x ∈ basisDegreePiece b degree (n+1) → d₀ x ∈ basisDegreePiece b degree n)
    (hh : ∀ n x, x ∈ basisDegreePiece b degree n → h x ∈ basisDegreePiece b degree (n+1))
    (n : ℕ) {x : M} (hx : x ∈ basisDegreePiece b degree n) :
    perturbationMap d d₀ h x ∈ basisDegreePiece b degree n := by
  exact (basisDegreePiece b degree n).add_mem hx
    ((basisDegreePiece b degree n).sub_mem (hd n _ (hh n x hx)) (hd₀ n _ (hh n x hx)))

lemma partialPerturbation_raises (b : Module.Basis I K M) (rank degree : I → ℕ)
    (d d₀ h : Module.End K M)
    (hlower : ∀ i j, rank i ≤ rank j → b.repr ((d-d₀) (h (b i))) j = 0)
    (hd : ∀ n x, x ∈ basisDegreePiece b degree (n+1) → d x ∈ basisDegreePiece b degree n)
    (hd₀ : ∀ n x, x ∈ basisDegreePiece b degree (n+1) → d₀ x ∈ basisDegreePiece b degree n)
    (hh : ∀ n x, x ∈ basisDegreePiece b degree n → h x ∈ basisDegreePiece b degree (n+1))
    (n : ℕ) {x : M} (hx : x ∈ basisDegreePiece b degree n) :
    (h * (perturbationEquiv b rank d d₀ h hlower).symm.toLinearMap) x ∈
      basisDegreePiece b degree (n+1) := by
  apply hh n
  exact perturbationInverse_preserves_span b rank d d₀ h hlower {i | degree i = n}
    (fun y hy => perturbationMap_preserves_degree b degree d d₀ h hd hd₀ hh n hy) hx

variable {N : Type*} [AddCommGroup N] [Module K N]

lemma correctedSection_preserves_degree
    (P : ℕ → Submodule K M) (Q : ℕ → Submodule K N)
    (d : Module.End K M) (dN : Module.End K N) (s : N →ₗ[K] M) (H : Module.End K M)
    (hd : ∀ n x, x ∈ P (n+1) → d x ∈ P n)
    (hdN : ∀ n x, x ∈ Q (n+1) → dN x ∈ Q n)
    (hdzero : ∀ x, x ∈ P 0 → d x = 0)
    (hdNzero : ∀ x, x ∈ Q 0 → dN x = 0)
    (hs : ∀ n x, x ∈ Q n → s x ∈ P n)
    (hH : ∀ n x, x ∈ P n → H x ∈ P (n+1))
    (n : ℕ) {x : N} (hx : x ∈ Q n) :
    correctedSection d dN s H x ∈ P n := by
  cases n with
  | zero =>
    simpa [correctedSection, sectionDefect, hdzero _ (hs 0 x hx), hdNzero x hx] using
      hs 0 x hx
  | succ n =>
    apply (P (n+1)).sub_mem (hs (n+1) x hx)
    apply hH n
    exact (P n).sub_mem (hd n _ (hs (n+1) x hx)) (hs n _ (hdN n x hx))

end FourPapers.Sublattice

end
end


end
