import Characterizations.Presentation.Paths

/-! # A disconnected box detects a genuine nonlinear first syzygy -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Presentation
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

/-- Restrict the actual canonical augmentation to a specified generator subset. -/
def selectedAugmentation (B : Family V) (U : Finset (Generators B)) :
    Free (k := k) B →ₗ[MvPolynomial V k] MvPolynomial V k :=
  Fintype.linearCombination _ (fun b => if b ∈ U then monomial b.val 1 else 0)

lemma selectedAugmentation_single (B : Family V) (U : Finset (Generators B))
    (b : Generators B) (p : MvPolynomial V k) :
    selectedAugmentation B U (Pi.single b p) = if b ∈ U then p * monomial b.val 1 else 0 := by
  simp [selectedAugmentation, Fintype.linearCombination_apply, Pi.single_apply, smul_eq_mul,
    mul_ite]

lemma selectedAugmentation_pair (B : Family V) (U : Finset (Generators B))
    (a b : Generators B) :
    selectedAugmentation (k := k) B U (pairSyzygy B a b) =
      (if a ∈ U then monomial (a.val ⊔ b.val) 1 else 0) -
        (if b ∈ U then monomial (a.val ⊔ b.val) 1 else 0) := by
  rw [pairSyzygy, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le le_sup_left,
    tsub_add_cancel_of_le le_sup_right]

lemma selectedAugmentation_pairAt (B : Family V) (U : Finset (Generators B))
    (C : Exponent V) (a b : Generators B) (ha : a.val ≤ C) (hb : b.val ≤ C) :
    selectedAugmentation (k := k) B U (pairAt B C a b) =
      (if a ∈ U then monomial C 1 else 0) - (if b ∈ U then monomial C 1 else 0) := by
  rw [pairAt, map_sub, selectedAugmentation_single, selectedAugmentation_single]
  simp only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le ha,
    tsub_add_cancel_of_le hb]

lemma selectedAugmentation_edge_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (a b : Generators B) (hab : UnitStep a.val b.val) (p : MvPolynomial V k) :
    (selectedAugmentation (k := k) B U (p • pairSyzygy (k := k) B a b)).coeff C = 0 := by
  rw [map_smul, selectedAugmentation_pair]
  by_cases hsup : a.val ⊔ b.val ≤ C
  · have he := hU a b (le_sup_left.trans hsup) (le_sup_right.trans hsup) hab
    by_cases ha : a ∈ U
    · simp [ha, he.mp ha]
    · have hb : b ∉ U := fun hb => ha (he.mpr hb)
      simp [ha, hb]
  · simp only [smul_eq_mul, mul_sub]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
      simp [ha, hb, coeff_mul_monomial', hsup]

lemma selectedAugmentation_edgeSpan_coeff_zero (B : Family V) (U : Finset (Generators B))
    (C : Exponent V)
    (hU : ∀ a b : Generators B, a.val ≤ C → b.val ≤ C → UnitStep a.val b.val → (a ∈ U ↔ b ∈ U))
    (x : Free (k := k) B) (hx : x ∈ edgeSpan B) :
    (selectedAugmentation B U x).coeff C = 0 := by
  suffices hh : ∀ p : MvPolynomial V k, (selectedAugmentation B U (p • x)).coeff C = 0 by
    simpa using hh 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact selectedAugmentation_edge_coeff_zero B U C hU a b hab
  | zero => intro p; simp
  | add x y hx hy ihx ihy =>
    intro p
    simp only [smul_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihx, ihy, add_zero]
  | smul r x hx ih =>
    intro p
    rw [smul_smul]
    exact ih (p * r)

/-- A disconnected box produces an actual syzygy outside the submodule generated
by all linear binomial relations. This holds in every nontrivial coefficient ring. -/
lemma boxConnected_of_ker_le_edgeSpan [Nontrivial k] {B : Family V}
    (hker : LinearMap.ker (augmentation (k := k) B) ≤ edgeSpan B) : BoxConnected B := by
  intro C a ha haC b hb hbC
  by_contra hpath
  let U : Finset (Generators B) := univ.filter (fun c => Relation.ReflTransGen (BoxStep B C) a c.val)
  have hU : ∀ x y : Generators B, x.val ≤ C → y.val ≤ C → UnitStep x.val y.val → (x ∈ U ↔ y ∈ U) := by
    intro x y hx hy hxy
    simp only [U, mem_filter, mem_univ, true_and]
    constructor
    · intro hp
      exact hp.tail ⟨x.property, y.property, hx, hy, hxy⟩
    · intro hp
      exact hp.tail ⟨y.property, x.property, hy, hx, hxy.symm⟩
  let a' : Generators B := ⟨a, ha⟩
  let b' : Generators B := ⟨b, hb⟩
  have haU : a' ∈ U := by simp [U, a', Relation.ReflTransGen.refl]
  have hbU : b' ∉ U := by simpa [U, b'] using hpath
  have hz : pairAt (k := k) B C a' b' ∈ LinearMap.ker (augmentation B) := by
    rw [pairAt, ← scaled_pairSyzygy B C a' b' haC hbC]
    exact (LinearMap.ker (augmentation B)).smul_mem _ (pairSyzygy_mem_ker B a' b')
  have hh := selectedAugmentation_edgeSpan_coeff_zero B U C hU _ (hker hz)
  rw [selectedAugmentation_pairAt B U C a' b' haC hbC] at hh
  simpa [haU, hbU] using hh

/-- Lemma 3.1: the conventional linear first-syzygy condition is equivalent to
connectivity of every nonempty coordinate box, over every field (indeed, ring). -/
theorem linearPresentation_iff_boxConnected [Nontrivial k] {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) : HasLinearPresentation (k := k) B ↔ BoxConnected B := by
  constructor
  · intro h
    apply boxConnected_of_ker_le_edgeSpan (k := k)
    simpa only [HasLinearPresentation, linearSpan_eq_edgeSpan hB] using h
  · exact linearPresentation_of_boxConnected

end Characterizations.Presentation
