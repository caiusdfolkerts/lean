module

public import Unimodular.RankThree
public import Unimodular.PolytopeFans
public import Unimodular.SeriesParallelK4

@[expose] public section

/-!
# The rank-three smooth Fano obstruction without the corner condition

This module proves Lemma 6.5 with its full hypotheses. Uniform unimodularity
and a smooth reflexive polytope suffice; no deep monotonicity or positive
coordinate condition is assumed. The final statement excludes an ordinary
restriction isomorphic to the genuine six-edge cycle matroid of K4.
-/

open Set
open scoped BigOperators Matroid

noncomputable section

namespace Unimodular.SmoothReflexivePresentation

/-- A supporting hyperplane of the primitive-normal hull contains at most n
normals. Maximize the sum of these normals over the original smooth polytope:
equality forces every selected normal into one actual vertex's integral basis.
This uses smoothness and the facet inequalities, with no corner hypothesis. -/
theorem support_normals_card_le {n : ℕ} (P : SmoothReflexivePresentation n)
    {J : Type*} [Fintype J] (a : J → Lattice n)
    (ha : ∀ j, a j ∈ P.normals) (hinj : Function.Injective a)
    (h : Ambient n) (hbound : ∀ u ∈ P.normals, pairing h u ≤ 1)
    (heq : ∀ j, pairing h (a j) = 1) : Fintype.card J ≤ n := by
  classical
  let x : Ambient n := ∑ j, embed (a j)
  obtain ⟨v, hv⟩ := P.exists_max_vertex x
  have hsum (p : Ambient n) : realPairing p x = ∑ j, pairing p (a j) := by
    simp only [x, realPairing, Finset.sum_apply, Finset.mul_sum, embed, pairing]
    exact Finset.sum_comm
  have hxval : realPairing h x = Fintype.card J := by
    rw [hsum]
    simp [heq]
  have hupper (j : J) : pairing (embed v.val) (a j) ≤ 1 :=
    (P.mem_carrier_iff _).1 (P.vertex_mem v) (a j) (ha j)
  have hsumle : (∑ j, pairing (embed v.val) (a j)) ≤ Fintype.card J := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hupper j)
  have hsumeq : (∑ j, pairing (embed v.val) (a j)) = Fintype.card J := by
    apply le_antisymm hsumle
    have hmax := hv h ((P.mem_carrier_iff h).2 hbound)
    simpa only [hxval, hsum] using hmax
  have hmone (j : J) : pairing (embed v.val) (a j) = 1 := by
    by_contra hnot
    have hjlt : pairing (embed v.val) (a j) < 1 := lt_of_le_of_ne (hupper j) hnot
    have hslt : (∑ j, pairing (embed v.val) (a j)) < (∑ _ : J, (1 : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro k _
        exact hupper k
      · exact ⟨j, Finset.mem_univ _, hjlt⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hslt
    exact (ne_of_lt hslt) hsumeq
  have hex (j : J) : ∃ i, P.basis v i = a j :=
    P.active_subset v (a j) (ha j) (hmone j)
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro j k hjk
    apply hinj
    rw [← hf j, ← hf k, hjk]
  simpa using Fintype.card_le_of_injective f hf_inj

end Unimodular.SmoothReflexivePresentation

namespace Unimodular.RankThree

/-- The determinant condition is preserved under an actual integral lattice
isomorphism. This permits basis normalization without changing the configuration. -/
theorem uniform_image_of_latticeEquiv {n : ℕ} (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (φ : Lattice n ≃ₗ[ℤ] Lattice n) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : φ '' U => u.val) := by
  intro a
  choose x hx he using fun i => (a i).property
  let labels : Fin n → U := fun i => ⟨x i, hx i⟩
  have h := hU labels
  rw [BasisCover.basis_determinant_abs (Pi.basisFun ℤ (Fin n))
    ((Pi.basisFun ℤ (Fin n)).map φ)]
  rw [Module.Basis.det_map]
  convert h using 1
  congr 2
  funext i
  change φ.symm (a i).val = x i
  rw [← he i, φ.symm_apply_apply]


/-- The minor bound used by the rank-three root calculation, with uniformity
itself as hypothesis rather than any geometric sufficient condition. -/
theorem det_bound_of_uniform (S : Set (Lattice 3))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) (fun u : S => u.val))
    (u v w : Lattice 3) (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) :
    |(Matrix.of ![u, v, w]).det| ≤ 1 := by
  have h := hS ![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩]
  have hvec : (fun i : Fin 3 =>
      (![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩] i : S).val) = ![u, v, w] := by
    funext i
    fin_cases i <;> rfl
  change |(Pi.basisFun ℤ (Fin 3)).det
    (fun i => (![⟨u, hu⟩, ⟨v, hv⟩, ⟨w, hw⟩] i : S).val)| ≤ 1 at h
  rw [hvec, det_eq_coordinate_rows] at h
  simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] using h

/-- Allow either actual sign on the two selected lines. -/
theorem signed_det_bound_of_uniform (S : Set (Lattice 3))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) (fun u : S => u.val))
    (u v w : Lattice 3) (hu : u ∈ S) (hv : v ∈ S ∨ -v ∈ S)
    (hw : w ∈ S ∨ -w ∈ S) : |(Matrix.of ![u, v, w]).det| ≤ 1 := by
  have hn₂ : (Matrix.of ![u, -v, w]).det = -(Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  have hn₃ : (Matrix.of ![u, v, -w]).det = -(Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  have hn₂₃ : (Matrix.of ![u, -v, -w]).det = (Matrix.of ![u, v, w]).det := by
    simp [Matrix.det_fin_three] <;> ring
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact det_bound_of_uniform S hS u v w hu hv hw
  · simpa only [hn₃, abs_neg] using det_bound_of_uniform S hS u v (-w) hu hv hw
  · simpa only [hn₂, abs_neg] using det_bound_of_uniform S hS u (-v) w hu hv hw
  · simpa only [hn₂₃] using det_bound_of_uniform S hS u (-v) (-w) hu hv hw

set_option maxHeartbeats 1000000 in
/-- Every nonzero vector in a uniformly unimodular system containing all six
K4 lines is one of the twelve signed A3 roots. Extra vectors are unrestricted. -/
theorem every_vector_is_root_of_uniform (S : Set (Lattice 3))
    (hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) (fun u : S => u.val))
    (hlines : ∀ i, baseRoot i ∈ S ∨ -baseRoot i ∈ S)
    (u : Lattice 3) (hu : u ∈ S) (hne : u ≠ 0) : ∃ r, root r = u := by
  have minor (i j : Fin 6) := signed_det_bound_of_uniform S hS u
    (baseRoot i) (baseRoot j) hu (hlines i) (hlines j)
  have h₀ : |u 0| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three] using minor 1 2
  have h₁ : |u 1| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three, abs_neg] using minor 0 2
  have h₂ : |u 2| ≤ 1 := by simpa [baseRoot, Matrix.det_fin_three] using minor 0 1
  have h₀₁ : |u 0 + u 1| ≤ 1 := by
    have h : |-u 0 - u 1| ≤ 1 := by
      simpa [baseRoot, Matrix.det_fin_three] using minor 3 2
    have hh := abs_le.mp h
    exact abs_le.mpr (by constructor <;> omega)
  have h₀₂ : |u 0 + u 2| ≤ 1 := by
    simpa [baseRoot, Matrix.det_fin_three] using minor 4 1
  have h₁₂ : |u 1 + u 2| ≤ 1 := by
    have h : |-u 1 - u 2| ≤ 1 := by
      simpa [baseRoot, Matrix.det_fin_three] using minor 5 0
    have hh := abs_le.mp h
    exact abs_le.mpr (by constructor <;> omega)
  have hcoords : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra! hzero
    apply hne
    ext i
    fin_cases i <;> simp_all
  have bounds := abs_le.1 h₀
  have bounds' := abs_le.1 h₁
  have bounds'' := abs_le.1 h₂
  have sums := abs_le.1 h₀₁
  have sums' := abs_le.1 h₀₂
  have sums'' := abs_le.1 h₁₂
  have hc :
      (u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 1 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 1) ∨
      (u 0 = 1 ∧ u 1 = -1 ∧ u 2 = 0) ∨
      (u 0 = 1 ∧ u 1 = 0 ∧ u 2 = -1) ∨
      (u 0 = 0 ∧ u 1 = 1 ∧ u 2 = -1) ∨
      (u 0 = -1 ∧ u 1 = 0 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = -1 ∧ u 2 = 0) ∨
      (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = -1) ∨
      (u 0 = -1 ∧ u 1 = 1 ∧ u 2 = 0) ∨
      (u 0 = -1 ∧ u 1 = 0 ∧ u 2 = 1) ∨
      (u 0 = 0 ∧ u 1 = -1 ∧ u 2 = 1) := by
    rcases bounds with ⟨h0lo, h0hi⟩
    rcases bounds' with ⟨h1lo, h1hi⟩
    rcases bounds'' with ⟨h2lo, h2hi⟩
    generalize hu0 : u 0 = x0 at *
    generalize hu1 : u 1 = x1 at *
    generalize hu2 : u 2 = x2 at *
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · refine ⟨(0, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(1, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(2, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(3, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(4, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(5, false), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(0, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(1, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(2, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(3, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(4, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]
  · refine ⟨(5, true), ?_⟩; ext i; fin_cases i <;> simp_all [root, baseRoot]

/-- Pulling back a covector through the actual integral basis. -/
theorem pairing_coordinate_pullback (b : Module.Basis (Fin 3) ℤ (Lattice 3))
    (h : Ambient 3) (u : Lattice 3) :
    pairing (dualCorner b h) u = pairing h (b.equivFun u) := by
  rw [pairing_dualCorner]
  simp only [pairing, Module.Basis.equivFun_apply]

/-- The normalized six-line obstruction for a uniformly unimodular smooth Fano
normal configuration, in every integral basis. The proof uses the exact 729-case
root certificate, genuine positive spanning, and the preceding smooth support
bound. It does not impose the positive-coordinate criterion. -/
theorem no_K4_lines_fano (P : SmoothReflexivePresentation 3)
    (hP : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3))
      (fun u : (P.normals : Set (Lattice 3)) => u.val))
    (b : Module.Basis (Fin 3) ℤ (Lattice 3))
    (hlines : ∀ i, b.equivFun.symm (baseRoot i) ∈ P.normals ∨
      -b.equivFun.symm (baseRoot i) ∈ P.normals) : False := by
  classical
  let S : Set (Lattice 3) := b.equivFun '' (P.normals : Set (Lattice 3))
  have hS : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) (fun u : S => u.val) :=
    uniform_image_of_latticeEquiv (P.normals : Set (Lattice 3)) hP b.equivFun
  have hmem (u : Lattice 3) : u ∈ S ↔ b.equivFun.symm u ∈ P.normals := by
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [b.equivFun.symm_apply_apply, Finset.mem_coe] using hv
    · intro hu
      exact ⟨b.equivFun.symm u, hu, b.equivFun.apply_symm_apply u⟩
  have hlinesS (i : Fin 6) : baseRoot i ∈ S ∨ -baseRoot i ∈ S := by
    rcases hlines i with hi | hi
    · exact Or.inl ((hmem _).2 hi)
    · exact Or.inr ((hmem _).2 (by simpa only [map_neg] using hi))
  have hne (u : Lattice 3) (hu : u ∈ S) : u ≠ 0 := by
    intro hz
    have hu' := (hmem u).1 hu
    rw [hz, map_zero] at hu'
    obtain ⟨v, i, hi⟩ := P.normals_occur 0 hu'
    exact (P.basis v).ne_zero i hi
  have hroots (u : Lattice 3) (hu : u ∈ S) : ∃ r, root r = u :=
    every_vector_is_root_of_uniform S hS hlinesS u hu (hne u hu)
  let s : Fin 6 → Fin 3 := fun i =>
    if baseRoot i ∈ S then (if -baseRoot i ∈ S then 2 else 0) else 1
  have hs (r : RootTag) : selected s r ↔ root r ∈ S := by
    obtain ⟨i, e⟩ := r
    have hi := hlinesS i
    cases e <;> by_cases hp : baseRoot i ∈ S <;>
      by_cases hn : -baseRoot i ∈ S <;> simp_all [s, selected, root]
  rcases oriented_roots_obstruction s with hsep | hface
  · obtain ⟨i, hi⟩ := hsep
    apply P.coordinateFan.no_separating_functional (dualCorner b (embed (separator i)))
    · intro u hu
      have hu' : u ∈ P.normals := (P.coordinateFan_ray_iff u).1 hu
      have hsu : b.equivFun u ∈ S := ⟨u, hu', rfl⟩
      obtain ⟨r, hr⟩ := hroots _ hsu
      rw [pairing_coordinate_pullback, ← hr, pairing_embed]
      exact_mod_cast hi r ((hs r).2 (hr.symm ▸ hsu))
    · intro hz
      apply embed_ne_zero (separator_ne_zero i)
      have hh := congrArg (dualCoordinates b) hz
      simpa only [dualCoordinates_dualCorner, map_zero] using hh
  · obtain ⟨i, hi, hselected⟩ := hface
    have hc := P.support_normals_card_le
      (fun j => b.equivFun.symm (root (faceRoot i j)))
      (fun j => (hmem _).1 ((hs _).1 (hselected j)))
      (b.equivFun.symm.injective.comp (faceRoot_injective i))
      (dualCorner b (embed (faceNormal i)))
      (by
        intro u hu
        have hsu : b.equivFun u ∈ S := ⟨u, hu, rfl⟩
        obtain ⟨r, hr⟩ := hroots _ hsu
        rw [pairing_coordinate_pullback, ← hr, pairing_embed]
        exact_mod_cast hi r ((hs r).2 (hr.symm ▸ hsu)))
      (by
        intro j
        rw [pairing_coordinate_pullback, b.equivFun.apply_symm_apply,
          pairing_embed, faceRoot_pairing]
        norm_num)
    norm_num at hc

/-- The complete determinant-pattern version of the Fano-only obstruction.
The six vectors are normalized integrally by the proved rank-three rigidity
lemma; neither their signs nor any other normals are omitted. -/
theorem no_K4_dependence_pattern_fano (P : SmoothReflexivePresentation 3)
    (hP : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3))
      (fun u : (P.normals : Set (Lattice 3)) => u.val))
    (U : Fin 6 → Lattice 3) (hU : ∀ i, U i ∈ P.normals)
    (hpattern : ∀ a : Fin 3 → Fin 6,
      (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) = 0 ↔
        (Pi.basisFun ℤ (Fin 3)).det (baseRoot ∘ a) = 0) : False := by
  have hUniform : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3)) U :=
    fun a => hP (fun i => ⟨U (a i), hU (a i)⟩)
  obtain ⟨b, hb⟩ := integral_K4_normal_form U hUniform hpattern
  apply no_K4_lines_fano P hP b
  intro i
  rcases hb i with hi | hi
  · exact Or.inl (hi.symm ▸ hU i)
  · exact Or.inr (hi.symm ▸ hU i)

/-- Equality of ordinary represented matroids entails equality of every maximal
minor's vanishing pattern, including selections with repeated labels. -/
theorem determinant_pattern_of_matroid_eq (U V : Fin 6 → Lattice 3)
    (hM : VectorMatroid.ofFamily (K := ℝ) (fun i => embed (U i)) =
      VectorMatroid.ofFamily (K := ℝ) (fun i => embed (V i)))
    (a : Fin 3 → Fin 6) :
    (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) = 0 ↔
      (Pi.basisFun ℤ (Fin 3)).det (V ∘ a) = 0 := by
  have hsets := (VectorMatroid.ofFamily_eq_iff (K := ℝ) _ _).1 hM
  have hreal : LinearIndependent ℝ (fun i => embed (U (a i))) ↔
      LinearIndependent ℝ (fun i => embed (V (a i))) := by
    constructor
    · intro h
      have ha : Function.Injective a := fun i j hij =>
        h.injective (congrArg (fun k => embed (U k)) hij)
      exact (linearIndepOn_range_iff ha (fun i => embed (V i))).1
        ((hsets (Set.range a)).1
          ((linearIndepOn_range_iff ha (fun i => embed (U i))).2 h))
    · intro h
      have ha : Function.Injective a := fun i j hij =>
        h.injective (congrArg (fun k => embed (V k)) hij)
      exact (linearIndepOn_range_iff ha (fun i => embed (U i))).1
        ((hsets (Set.range a)).2
          ((linearIndepOn_range_iff ha (fun i => embed (V i))).2 h))
  have hint : LinearIndependent ℤ (U ∘ a) ↔ LinearIndependent ℤ (V ∘ a) :=
    (real_independent_iff_integer_independent (U ∘ a)).symm.trans
      (hreal.trans (real_independent_iff_integer_independent (V ∘ a)))
  have hdet : (Pi.basisFun ℤ (Fin 3)).det (U ∘ a) ≠ 0 ↔
      (Pi.basisFun ℤ (Fin 3)).det (V ∘ a) ≠ 0 :=
    (IntegralRigidity.independent_iff_det_ne_zero _ _).symm.trans
      (hint.trans (IntegralRigidity.independent_iff_det_ne_zero _ _))
  simpa only [not_not] using not_congr hdet

/-- Lemma 6.5, with exactly its Fano and uniform-unimodularity hypotheses.
No injective labeling of the six edges of K4 can be an ordinary matroid
restriction of the actual primitive facet-normal configuration. Deep monotonicity
and the corner criterion do not occur among the assumptions. -/
theorem no_K4_restriction_fano (P : SmoothReflexivePresentation 3)
    (hP : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 3))
      (fun u : (P.normals : Set (Lattice 3)) => u.val))
    (f : Fin 6 ↪ Lattice 3) :
    ¬ SeriesParallel.K4Matroid.mapEmbedding f ≤r
      VectorMatroid.onSet (K := ℝ) (embed : Lattice 3 → Ambient 3)
        (P.normals : Set (Lattice 3)) := by
  intro hres
  have hg : (SeriesParallel.K4Matroid.mapEmbedding f).E = Set.range f := by simp
  have hsubset : Set.range f ⊆ (P.normals : Set (Lattice 3)) := by
    simpa only [hg, VectorMatroid.onSet_ground] using hres.subset
  have hfamily : VectorMatroid.ofFamily (K := ℝ) (fun i => embed (f i)) =
      SeriesParallel.K4Matroid := by
    apply SeriesParallel.EmbeddingTransport.map_injective f
    calc
      (VectorMatroid.ofFamily (K := ℝ) (fun i => embed (f i))).mapEmbedding f =
          VectorMatroid.onSet (K := ℝ) embed (Set.range f) :=
        VectorMatroid.ofFamily_mapEmbedding_eq_onSet _ _ f (fun _ => rfl)
      _ = (VectorMatroid.onSet (K := ℝ) embed (P.normals : Set (Lattice 3))) ↾
          Set.range f := (VectorMatroid.restrict_onSet _ hsubset).symm
      _ = SeriesParallel.K4Matroid.mapEmbedding f := by
        simpa only [hg] using hres.eq_restrict
  apply no_K4_dependence_pattern_fano P hP f
  · intro i
    exact hsubset ⟨i, rfl⟩
  · exact determinant_pattern_of_matroid_eq f baseRoot hfamily

#print axioms Unimodular.SmoothReflexivePresentation.support_normals_card_le
#print axioms Unimodular.RankThree.no_K4_restriction_fano

end Unimodular.RankThree
end
