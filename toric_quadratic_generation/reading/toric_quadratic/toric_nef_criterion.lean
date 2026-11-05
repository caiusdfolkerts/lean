module

public import PaperVerification.ToricPrimitiveReduction

@[expose] public section

/-!
# The primitive-relation criterion for genuine nef support

The converse uses the terminating reductions, not a definition of nefness by
primitive inequalities. For a full smooth cone and an arbitrary ray v, add
enough copies of every basis ray that the sum remains in the full cone after
adding v. Reduce this nonnegative integral representation. Fan intersection
forces the terminal support back into that same cone, so cost monotonicity
gives the required Cartier inequality at v.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem countVector_add (c d : Lattice n → ℕ) :
    «Σ».countVector (c + d) = «Σ».countVector c + «Σ».countVector d := by
  simp only [countVector, Pi.add_apply, Nat.cast_add, add_smul, Finset.sum_add_distrib]

theorem countCost_add (a : Lattice n → ℝ) (c d : Lattice n → ℕ) :
    «Σ».countCost a (c + d) = «Σ».countCost a c + «Σ».countCost a d := by
  simp only [countCost, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem countVector_single {v : Lattice n} (hv : v ∈ «Σ».rays) :
    «Σ».countVector (Pi.single v 1) = v := by
  simp [countVector, Pi.single_apply, Nat.cast_ite, ite_smul, hv]

theorem countCost_single (a : Lattice n → ℝ) {v : Lattice n} (hv : v ∈ «Σ».rays) :
    «Σ».countCost a (Pi.single v 1) = a v := by
  simp [countCost, Pi.single_apply, Nat.cast_ite, ite_mul, hv]

theorem countVector_indicator (t : Finset (Lattice n)) (ht : t ⊆ «Σ».rays) (N : ℕ) :
    «Σ».countVector (fun v => if v ∈ t then N else 0) = (N : ℤ) • ∑ v ∈ t, v := by
  simp only [countVector, Nat.cast_ite, Nat.cast_zero, ite_smul, zero_smul]
  rw [sum_indicator_of_subset ht]
  exact (Finset.smul_sum).symm

/-- Terms outside the genuine positive support contribute zero. -/
theorem embed_countVector_eq_sum_support (c : Lattice n → ℕ) :
    embed n («Σ».countVector c) =
      ∑ v ∈ «Σ».countSupport c, (c v : ℝ) • embed n v := by
  simp only [countVector, map_sum, embed_int_smul, Int.cast_natCast,
    countSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hcv : 0 < c v
  · simp only [if_pos hcv]
  · have hzero : c v = 0 := Nat.eq_zero_of_not_pos hcv
    simp only [if_neg hcv, hzero, Nat.cast_zero, zero_smul, ite_self]

/-- If coefficients are positive on a cone and their actual sum lies in
another fan cone, every support ray belongs to the latter cone. -/
theorem countSupport_subset_of_vector_mem (c : Lattice n → ℕ)
    (hc : «Σ».countSupport c ∈ «Σ».cones) {t : Finset (Lattice n)} (ht : t ∈ «Σ».cones)
    (hvec : embed n («Σ».countVector c) ∈ latticeRayCone t) :
    «Σ».countSupport c ⊆ t := by
  apply «Σ».positive_sum_mem_cone_implies_subset hc ht (fun v => (c v : ℝ))
  · intro v hv
    exact_mod_cast (Finset.mem_filter.mp hv).2
  · rwa [← «Σ».embed_countVector_eq_sum_support c]

/-- If a linear function agrees with all active coefficients, pairing the
actual vector computes the cost exactly. -/
theorem countCost_eq_linear (a : Lattice n → ℝ) (c : Lattice n → ℕ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ v ∈ «Σ».countSupport c, ℓ (embed n v) = a v) :
    «Σ».countCost a c = ℓ (embed n («Σ».countVector c)) := by
  simp only [countCost, countVector, map_sum, embed_int_smul, Int.cast_natCast,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : 0 < c v
  · rw [he v (Finset.mem_filter.mpr ⟨hv, hc⟩)]
  · rw [Nat.eq_zero_of_not_pos hc]
    simp

/-- Large integral translations along all rays of a full smooth cone keep
the translated arbitrary lattice vector in that actual cone. -/
theorem exists_positive_basis_translation
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (v : Lattice n) :
    ∃ N : ℕ, 0 < N ∧
      embed n ((N : ℤ) • (∑ i, b i) + v) ∈
        latticeRayCone (Finset.univ.image b) := by
  let N : ℕ := 1 + ∑ i, (b.repr v i).natAbs
  refine ⟨N, by omega, ?_⟩
  rw [mem_latticeRayCone_basis_iff]
  refine ⟨?_, by simp⟩
  intro i
  rw [integralBasisReal_repr]
  have hsum : b.repr (∑ j, b j) i = 1 := by
    simp [map_sum, Finsupp.finsetSum_apply, Module.Basis.repr_self_apply,
      Finsupp.single_apply]
  have hcoord : b.repr ((N : ℤ) • (∑ j, b j) + v) i = (N : ℤ) + b.repr v i := by
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, hsum, mul_one]
  rw [hcoord]
  have hbound : (b.repr v i).natAbs ≤ ∑ j, (b.repr v j).natAbs :=
    Finset.single_le_sum (f := fun j : Fin n => (b.repr v j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hboundZ : ((b.repr v i).natAbs : ℤ) ≤
      ((∑ j, (b.repr v j).natAbs : ℕ) : ℤ) := by exact_mod_cast hbound
  have hneg : -(b.repr v i) ≤ ((b.repr v i).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(b.repr v i)))
  have hcoord0 : (0 : ℤ) ≤ (N : ℤ) + b.repr v i := by
    dsimp [N]
    omega
  exact_mod_cast hcoord0

/-- Primitive nonnegativity forces the actual supporting inequalities of
the Cartier functional at a full smooth cone. -/
theorem full_cone_linear_support_of_primitive_nonneg
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (ha : ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (htb : t = Finset.univ.image b)
    (ℓ : Ambient n →ₗ[ℝ] ℝ) (hℓ : ∀ v ∈ t, ℓ (embed n v) = a v) :
    ∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v := by
  intro v hv
  obtain ⟨N, hN, htranslate⟩ := exists_positive_basis_translation b v
  let cbase : Lattice n → ℕ := fun u => if u ∈ t then N else 0
  let c : Lattice n → ℕ := cbase + Pi.single v 1
  have htrays : t ⊆ «Σ».rays := fun u hu => «Σ».ray_mem_of_mem_cone ht hu
  have hsumt : (∑ u ∈ t, u) = ∑ i, b i := by
    rw [htb, Finset.sum_image]
    exact fun i _ j _ hij => b.injective hij
  have hbase : «Σ».countVector cbase = (N : ℤ) • ∑ i, b i := by
    rw [«Σ».countVector_indicator t htrays N, hsumt]
  have hcvec : «Σ».countVector c = «Σ».countVector cbase + v := by
    rw [countVector_add, «Σ».countVector_single hv]
  have hccost : «Σ».countCost a c = «Σ».countCost a cbase + a v := by
    rw [countCost_add, «Σ».countCost_single a hv]
  obtain ⟨d, hdvec, hdcone, hdcost⟩ := «Σ».exists_cone_reduction H hH a ha c
  have hdmem : embed n («Σ».countVector d) ∈ latticeRayCone t := by
    rw [hdvec, hcvec, hbase, htb]
    exact htranslate
  have hdsub := «Σ».countSupport_subset_of_vector_mem d hdcone ht hdmem
  have hdlinear := «Σ».countCost_eq_linear a d ℓ (fun u hu => hℓ u (hdsub hu))
  have hbaselinear : «Σ».countCost a cbase = ℓ (embed n («Σ».countVector cbase)) := by
    apply «Σ».countCost_eq_linear a cbase ℓ
    intro u hu
    have hpos := (Finset.mem_filter.mp hu).2
    have hut : u ∈ t := by
      by_contra h
      simp only [cbase, if_neg h, lt_self_iff_false] at hpos
    exact hℓ u hut
  rw [hdlinear, hdvec, hcvec, map_add, map_add, hccost, hbaselinear] at hdcost
  linarith

/-- The full primitive-relation criterion, derived from actual support data
and terminating reductions. Purity is independently supplied by the literal
normal fan construction and is preserved by the proved star subdivision. -/
theorem isNef_iff_primitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a := by
  constructor
  · intro ha R
    exact R.degree_nonneg_of_nef ha
  · intro ha s hs
    obtain ⟨t, ht, hst, hdim⟩ := hpure s hs
    obtain ⟨b, htb⟩ := «Σ».full_cone_basis ht hdim
    let ℓ : Ambient n →ₗ[ℝ] ℝ :=
      (integralBasisReal b).constr ℝ (fun i => a (b i))
    have hℓ : ∀ v ∈ t, ℓ (embed n v) = a v := by
      intro v hv
      rw [htb] at hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [← integralBasisReal_apply]
      exact (integralBasisReal b).constr_basis ℝ _ i
    refine ⟨ℓ, fun v hv => hℓ v (hst hv), ?_⟩
    exact «Σ».full_cone_linear_support_of_primitive_nonneg H hH a ha t ht b htb ℓ hℓ

end SmoothCompleteFan

end PaperVerification.ToricGeometry
