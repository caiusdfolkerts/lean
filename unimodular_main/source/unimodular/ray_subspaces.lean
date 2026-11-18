module

public import Unimodular.ConeBases
public import Unimodular

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.RaySubspaces

attribute [local instance] Classical.propDecidable

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

noncomputable def basisFace {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    (A : Finset (Fin n)) : PointedCone ℝ V :=
  PointedCone.hull ℝ (ι '' (b '' (A : Set (Fin n))))

theorem basisFace_isFaceOf (hι : IsIntegralLattice ι) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n)) :
    (basisFace (ι := ι) b A).IsFaceOf (ConeBases.cone (ι := ι) b) := by
  have he : ι '' (b '' (A : Set (Fin n))) = (fun i => ι (b i)) '' (A : Set (Fin n)) :=
    Set.image_image _ _ _
  rw [basisFace, he]
  exact PointedCone.isFaceOf_hull_image (hι.linearIndependent_basis b) rfl _

theorem finrank_span_basisFace (hι : IsIntegralLattice ι) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n)) :
    Module.finrank ℝ (Submodule.span ℝ (basisFace (ι := ι) b A : Set V)) = A.card := by
  have he : ι '' (b '' (A : Set (Fin n))) =
      Set.range (fun i : {i : Fin n // i ∈ A} => ι (b i.1)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨b i.1, ⟨i.1, i.2, rfl⟩, rfl⟩
  rw [basisFace, RayHyperplanes.span_hull_eq, he]
  simpa [Function.comp_def] using finrank_span_eq_card
    ((hι.linearIndependent_basis b).comp (fun i : {i : Fin n // i ∈ A} => i.1)
      Subtype.val_injective)

variable (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
  (hcrit : ConeBases.PositiveCriterion Φ)

include hcrit in
theorem positive_coordinate_unique {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    (hb : ConeBases.cone (ι := ι) b ∈ Φ.cones) {u : N} (hu : ConeBases.IsRay Φ u)
    {i j : Fin n} (hi : 0 < b.repr u i) (hj : 0 < b.repr u j) : i = j := by
  by_contra hij
  have hsum : max (b.repr u i) 0 + max (b.repr u j) 0 ≤ ∑ k, max (b.repr u k) 0 := by
    calc
      _ = ∑ k ∈ ({i, j} : Finset (Fin n)), max (b.repr u k) 0 := by simp [hij]
      _ ≤ ∑ k, max (b.repr u k) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => le_max_right _ _)
  rw [max_eq_left hi.le, max_eq_left hj.le] at hsum
  have hbnd := hcrit n b hb u hu
  omega

include hΦ hreg hcrit

/-- The span of any independent family of primitive fan rays is the span of an actual
fan cone, in the full ambient vector space and with its exact dimension. -/
theorem independent_ray_span_is_cone_span {k : ℕ} (a : Fin k → N)
    (haRay : ∀ j, ConeBases.IsRay Φ (a j))
    (ha : LinearIndependent ℝ (fun j => ι (a j))) :
    ∃ C ∈ Φ.cones, Module.finrank ℝ (Submodule.span ℝ (C : Set V)) = k ∧
      Submodule.span ℝ (Set.range (fun j => ι (a j))) = Submodule.span ℝ (C : Set V) := by
  classical
  let T := {C : Φ.cones // Submodule.span ℝ (C.1 : Set V) = ⊤}
  letI : Fintype T := Fintype.ofFinite T
  have hex : ∀ C : T, ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N),
      C.1.1 = ConeBases.cone (ι := ι) b := fun C =>
    ConeBases.exists_basis_of_full_regular Φ.lattice
      (Fan.isRegular_iff.1 hreg C.1.1 C.1.2) C.2
  choose n b hb using hex
  let row := fun p : (C : T) × Fin (n C) => fun j : Fin k => (b p.1).repr (a j) p.2
  let J := {p : (C : T) × Fin (n C) // ∃ j, row p j ≠ 0}
  obtain ⟨t, ht, hgeneric⟩ := GenericWeights.exists_geometric_progression
    (fun p : J => row p.1) (fun p => p.2)
  let x : N := ∑ j : Fin k, t ^ j.1 • a j
  obtain ⟨C₀, hC₀, hfull, hxC₀⟩ := FanMaximalCones.full_cones_cover Φ hΦ (ι x)
  let C : T := ⟨⟨C₀, hC₀⟩, hfull⟩
  have hbmem : ConeBases.cone (ι := ι) (b C) ∈ Φ.cones := by
    rw [← hb C]
    exact C.1.2
  have hxcone : ι x ∈ ConeBases.cone (ι := ι) (b C) := by
    rw [← hb C]
    exact hxC₀
  have hxcoord : ∀ i, 0 ≤ (b C).repr x i :=
    (ConeBases.lattice_mem_cone_iff Φ.lattice (b C) x).1 hxcone
  have hformula (i : Fin (n C)) : (b C).repr x i =
      ∑ j : Fin k, (b C).repr (a j) i * t ^ j.1 := by
    simp only [x, map_sum, map_smulₛₗ, RingHom.id_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_comm]
  let A : Finset (Fin (n C)) := Finset.univ.filter (fun i => ∃ j, (b C).repr (a j) i ≠ 0)
  have hA (i : Fin (n C)) : i ∈ A ↔ ∃ j, (b C).repr (a j) i ≠ 0 := by simp [A]
  have hstrict (i : Fin (n C)) (hi : i ∈ A) : 0 < (b C).repr x i := by
    have hn : (b C).repr x i ≠ 0 := by
      rw [hformula]
      exact hgeneric ⟨⟨C, i⟩, (hA i).1 hi⟩
    exact lt_of_le_of_ne (hxcoord i) (Ne.symm hn)
  have hpos (i : {i : Fin (n C) // i ∈ A}) : ∃ j, 0 < (b C).repr (a j) i.1 := by
    by_contra h
    push_neg at h
    have hnonpos : (b C).repr x i.1 ≤ 0 := by
      rw [hformula]
      exact Finset.sum_nonpos (fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (h j) (pow_nonneg ht.le _))
    exact (not_lt_of_ge hnonpos) (hstrict i.1 i.2)
  choose f hf using hpos
  have hfi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply positive_coordinate_unique Φ hcrit (b C) hbmem (haRay (f i)) (hf i)
    simpa only [he] using hf j
  have hcardle : A.card ≤ k := by
    simpa using Fintype.card_le_of_injective f hfi
  let S := Submodule.span ℝ (basisFace (ι := ι) (b C) A : Set V)
  let L := Submodule.span ℝ (Set.range (fun j => ι (a j)))
  have hLS : L ≤ S := by
    apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    change ι (a j) ∈ S
    change ι (a j) ∈ Submodule.span ℝ (basisFace (ι := ι) (b C) A : Set V)
    rw [basisFace, RayHyperplanes.span_hull_eq]
    apply (RegularQuotients.mem_integer_span_iff Φ.lattice (b C) A (a j)).1
    apply (b C).mem_span_image.2
    intro i hi
    exact (hA i).2 ⟨j, Finsupp.mem_support_iff.1 hi⟩
  have hdimL : Module.finrank ℝ L = k := by
    simpa [L] using finrank_span_eq_card ha
  have hdimS : Module.finrank ℝ S = A.card := finrank_span_basisFace Φ.lattice (b C) A
  have hcardge : k ≤ A.card := by
    rw [← hdimL, ← hdimS]
    exact Submodule.finrank_mono hLS
  have hcard : A.card = k := le_antisymm hcardle hcardge
  refine ⟨basisFace (ι := ι) (b C) A,
    Φ.mem_of_isFaceOf hbmem (basisFace_isFaceOf Φ.lattice (b C) A),
    hdimS.trans hcard, ?_⟩
  exact Submodule.eq_of_le_of_finrank_eq hLS (by rw [hdimL, hdimS, hcard])

/-- The first assertion of Lemma 6.4 for an arbitrary collection of rays, with no
independence or dimension restriction added to the statement. -/
theorem ray_generated_subspace_is_cone_span (U : Set N) (hU : U ⊆ {u | ConeBases.IsRay Φ u}) :
    ∃ C ∈ Φ.cones, Submodule.span ℝ (ι '' U) = Submodule.span ℝ (C : Set V) := by
  classical
  obtain ⟨f, hf, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (ι '' U)
  choose u hu he using hf
  have hembed : (fun i => ι (u i)) = f := funext he
  have ha : LinearIndependent ℝ (fun i => ι (u i)) := by
    rw [hembed]
    exact hli
  obtain ⟨C, hC, _, hL⟩ := independent_ray_span_is_cone_span Φ hΦ hreg hcrit u
    (fun i => hU (hu i)) ha
  refine ⟨C, hC, ?_⟩
  rw [hembed] at hL
  exact hspan.symm.trans hL

end Unimodular.RaySubspaces
