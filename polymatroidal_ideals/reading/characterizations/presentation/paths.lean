import Characterizations.Presentation.Edges

/-! # Exchange paths span the actual polynomial syzygies -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

def pairAt (B : Family V) (C : Exponent V) (a b : Generators B) : Free (k := k) B :=
  Pi.single a (monomial (C - a.val) 1) - Pi.single b (monomial (C - b.val) 1)

@[simp] lemma pairAt_self (B : Family V) (C : Exponent V) (a : Generators B) :
    pairAt (k := k) B C a a = 0 := sub_self _

lemma pairAt_add (B : Family V) (C : Exponent V) (a b c : Generators B) :
    pairAt (k := k) B C a b + pairAt B C b c = pairAt B C a c := by
  exact sub_add_sub_cancel _ _ _

lemma pairAt_mem_of_step (B : Family V) (C : Exponent V) (a b : Generators B)
    (ha : a.val ≤ C) (hb : b.val ≤ C) (h : UnitStep a.val b.val) :
    pairAt (k := k) B C a b ∈ edgeSpan B := by
  rw [pairAt, ← scaled_pairSyzygy B C a b ha hb]
  exact (edgeSpan B).smul_mem _ (pairSyzygy_mem_edgeSpan B a b h)

lemma pairAt_mem_of_path (B : Family V) (C : Exponent V) {a b : Exponent V}
    (hp : Relation.ReflTransGen (BoxStep B C) a b) (ha : a ∈ B) (hb : b ∈ B) :
    pairAt (k := k) B C ⟨a, ha⟩ ⟨b, hb⟩ ∈ edgeSpan B := by
  induction hp with
  | refl => simp
  | @tail b c hp hbc ih =>
    have h₁ := ih hbc.1
    have h₂ := pairAt_mem_of_step (k := k) B C ⟨b, hbc.1⟩ ⟨c, hb⟩ hbc.2.2.1 hbc.2.2.2.1 hbc.2.2.2.2
    simpa only [pairAt_add] using (edgeSpan B).add_mem h₁ h₂

lemma strand_eq_sum_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B)) (a : Generators B) :
    (∑ b, (MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) • pairAt B C b a) = strand B C x := by
  have hs : (∑ b, MvPolynomial.C (strandCoefficient B C x b) : MvPolynomial V k) = 0 := by
    rw [← map_sum, strandCoefficient_sum_zero hx, map_zero]
  simp only [pairAt, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [hs, zero_smul, sub_zero]
  funext c
  simp [Pi.single_apply, strand, C_mul_monomial]

lemma strand_mem_of_pairs {B : Family V} (C : Exponent V) (x : Free (k := k) B)
    (hx : x ∈ LinearMap.ker (augmentation B))
    (hp : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → pairAt (k := k) B C a b ∈ edgeSpan B) :
    strand B C x ∈ edgeSpan B := by
  by_cases hne : ∃ a : Generators B, a.val ≤ C
  · obtain ⟨a, ha⟩ := hne
    rw [← strand_eq_sum_pairs C x hx a]
    apply (edgeSpan B).sum_mem
    intro b hb
    by_cases hbc : b.val ≤ C
    · exact (edgeSpan B).smul_mem _ (hp b a hbc ha)
    · simp [strandCoefficient, hbc]
  · have he : strand B C x = 0 := by
      funext b
      have hb : ¬ b.val ≤ C := fun h => hne ⟨b, h⟩
      simp [strand, strandCoefficient, hb]
    rw [he]
    exact (edgeSpan B).zero_mem

lemma ker_le_edgeSpan_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B := by
  intro x hx
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  exact pairAt_mem_of_path B C (hB C a.val a.property ha b.val b.property hb) a.property b.property

/-- Every actual homogeneous linear syzygy is spanned by the binomial
unit-exchange syzygies, without any connectivity assumption. -/
lemma linear_relation_mem_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (x : Free (k := k) B) (hx : x ∈ LinearMap.ker (augmentation B))
    (hlin : Resolution.IsHomogeneousVector x 1) : x ∈ edgeSpan B := by
  rw [← sum_strand B x]
  apply (edgeSpan B).sum_mem
  intro C hC
  have hdeg : C.degree = d + 1 := by
    obtain ⟨b, hb, hC⟩ := mem_biUnion.mp hC
    obtain ⟨e, he, rfl⟩ := mem_image.mp hC
    have he' : e.degree = 1 := by
      by_contra hn
      exact (mem_support_iff.mp he) ((hlin b).coeff_eq_zero hn)
    rw [map_add, he', hB b.val b.property, Nat.add_comm]
  apply strand_mem_of_pairs C x hx
  intro a b ha hb
  by_cases hab : a = b
  · subst b; simp
  · exact pairAt_mem_of_step B C a b ha hb (step_of_common_degree_one hB C hdeg a b ha hb hab)

lemma linearSpan_eq_edgeSpan {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    Submodule.span (MvPolynomial V k)
      {x : Free (k := k) B | x ∈ LinearMap.ker (augmentation B) ∧ Resolution.IsHomogeneousVector x 1} =
      edgeSpan B := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    exact linear_relation_mem_edgeSpan hB x hx.1 hx.2
  · exact edgeSpan_le_linearSpan B

lemma linearPresentation_of_boxConnected {B : Family V} (hB : BoxConnected B) :
    HasLinearPresentation (k := k) B :=
  (ker_le_edgeSpan_of_boxConnected hB).trans (edgeSpan_le_linearSpan B)

end Characterizations.Presentation
