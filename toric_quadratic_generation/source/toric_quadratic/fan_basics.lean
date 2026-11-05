module

public import paper_verification.toric027
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Purity and an integral projectivity witness

Two usual consequences of the fan hypotheses are proved here. Every
finite smooth complete fan is pure. If such a fan has a real strictly
convex support, it also has an integral strictly convex support: strict
support is determined by finitely many open inequalities, rational
coefficients are dense, and a positive common denominator clears the
finitely many ray coefficients.

These lemmas remove redundant purity and projectivity-witness arguments
from the public real-support theorems. The real support itself is never
replaced or restricted in those theorems.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every cone of a finite smooth complete fan lies in a full cone.
Maximize the number of rays in a cone containing the given cone. If its
smooth basis presentation omits a direction, the existing small-perturbation
lemma contradicts maximality. -/
theorem isPure_of_complete : «Σ».IsPure := by
  intro s hs
  let above := «Σ».cones.filter (fun u => s ⊆ u)
  have habove : above.Nonempty :=
    ⟨s, Finset.mem_filter.mpr ⟨hs, Finset.Subset.refl s⟩⟩
  obtain ⟨u, hu, hmax⟩ := above.exists_max_image Finset.card habove
  have hucone : u ∈ «Σ».cones := (Finset.mem_filter.mp hu).1
  have hsu : s ⊆ u := (Finset.mem_filter.mp hu).2
  obtain ⟨b, I, huI⟩ := «Σ».smooth u hucone
  have hI : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    obtain ⟨ε, hε, t, ht, hut, hx⟩ :=
      «Σ».exists_small_perturbation_in_containing_cone hucone (embed n (b j))
    have htu : t = u :=
      (Finset.eq_of_subset_of_card_le hut
        (hmax t (Finset.mem_filter.mpr ⟨ht, hsu.trans hut⟩))).symm
    rw [htu] at hx
    have hxI : (∑ v ∈ u, embed n v) + ε • embed n (b j) ∈
        latticeRayCone (I.image b) := by
      rw [← huI]
      exact hx
    have hzero := ((mem_latticeRayCone_basis_iff b I _).mp hxI).2 j hj
    have hsum : (integralBasisReal b).repr (∑ v ∈ u, embed n v) j = 0 := by
      rw [map_sum, Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (huI ▸ hv)
      have hij : i ≠ j := by
        rintro rfl
        exact hj hi
      simp [integralBasisReal_repr, Module.Basis.repr_self_apply, hij, Ne.symm hij]
    have hεzero : ε = 0 := by
      simpa only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        hsum, integralBasisReal_repr, Module.Basis.repr_self_apply, if_true,
        Int.cast_one, smul_eq_mul, zero_add, mul_one] using hzero
    exact (ne_of_gt hε) hεzero
  refine ⟨u, hucone, hsu, ?_⟩
  rw [huI, hI, Finset.card_image_of_injective _ b.injective]
  simp

/-- Strict support depends only on coefficients at actual fan rays. -/
theorem IsStrictSupport.congr_on_rays {a b : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) (hab : ∀ u ∈ «Σ».rays, a u = b u) :
    «Σ».IsStrictSupport b := by
  intro s hs
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  refine ⟨ℓ, ?_, ?_⟩
  · intro u hu
    exact (he u hu).trans (hab u («Σ».ray_mem_of_mem_cone hs hu))
  · intro u hu hus
    rw [← hab u hu]
    exact hlt u hu hus

theorem continuous_cartierPoint (s : «Σ».fullCones) :
    Continuous (fun a : Lattice n → ℝ => «Σ».cartierPoint a s) := by
  unfold cartierPoint
  fun_prop

theorem continuous_wallSlack (s : «Σ».fullCones) (u : Lattice n) :
    Continuous (fun a : Lattice n → ℝ => «Σ».wallSlack a s u) := by
  exact (continuous_apply u).add
    ((dotProductEquiv ℝ (Fin n) (embed n u)).continuous_of_finiteDimensional.comp
      («Σ».continuous_cartierPoint s))

/-- Rational coefficients can be chosen inside the finite open system of
strict Cartier-point inequalities. -/
theorem exists_rational_strictSupport (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) :
    ∃ q : Lattice n → ℚ, «Σ».IsStrictSupport (fun u => (q u : ℝ)) := by
  let J := {p : «Σ».fullCones × «Σ».rays // p.2.val ∉ p.1.val}
  let U : Set (Lattice n → ℝ) :=
    {b | ∀ j : J, 0 < «Σ».wallSlack b j.val.1 j.val.2.val}
  have hUopen : IsOpen U := by
    dsimp only [U]
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j =>
      isOpen_lt continuous_const («Σ».continuous_wallSlack j.val.1 j.val.2.val))
  have hUa : a ∈ U := by
    intro j
    have hh := «Σ».cartierPoint_support_lt_of_not_mem ha j.val.1 j.val.2.property j.property
    dsimp only [wallSlack]
    linarith
  have hdense : DenseRange (fun q : Lattice n → ℚ => fun u => (q u : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q, hq⟩ := hdense.exists_mem_open hUopen ⟨a, hUa⟩
  refine ⟨q, ?_⟩
  apply «Σ».strictSupport_of_full_cartier_inequalities «Σ».isPure_of_complete
  intro s u hu hus
  have hh := hq ⟨(s, ⟨u, hu⟩), hus⟩
  change 0 < (q u : ℝ) +
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint (fun v => (q v : ℝ)) s) at hh
  linarith

/-- A real strictly convex support supplies an integral projectivity
witness. Only finitely many ray denominators are cleared; the original
real support remains arbitrary. -/
theorem exists_integral_strictSupport_of_real (a : Lattice n → ℝ)
    (ha : «Σ».IsStrictSupport a) :
    ∃ A : Lattice n → ℤ, «Σ».IsStrictSupport (fun u => (A u : ℝ)) := by
  obtain ⟨q, hq⟩ := «Σ».exists_rational_strictSupport a ha
  let N : ℕ := ∏ u ∈ «Σ».rays, (q u).den
  have hN : 0 < N := Finset.prod_pos (fun u _ => (q u).den_pos)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let A : Lattice n → ℤ := fun u => ((N / (q u).den : ℕ) : ℤ) * (q u).num
  have hcoeff (u : Lattice n) (hu : u ∈ «Σ».rays) :
      (A u : ℝ) = (N : ℝ) * (q u : ℝ) := by
    have hdvd : (q u).den ∣ N := Finset.dvd_prod_of_mem (fun v => (q v).den) hu
    have hdiv : ((N / (q u).den : ℕ) : ℝ) * ((q u).den : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    simp only [A, Int.cast_mul, Int.cast_natCast, Rat.cast_def]
    rw [← mul_div_assoc]
    apply (eq_div_iff hden).mpr
    rw [← hdiv]
    ring
  refine ⟨A, IsStrictSupport.congr_on_rays «Σ» (IsStrictSupport.smul «Σ» hq hNR) ?_⟩
  intro u hu
  exact (hcoeff u hu).symm

end PaperVerification.ToricGeometry.SmoothCompleteFan

end
