module

public import Continuation.Divisor.WallSupportGeneric
public import Continuation.Divisor.WallCurves
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity

/-!
# Nonnegative wall slacks imply global Cartier support

The support function is glued on the actual finite cones. It is continuous
by the finite closed cover. Across each wall it is the minimum of the two
Cartier linear forms. Local concavity away from the finite union of
codimension-two faces therefore gives global concavity. No projectivity
assumption is used.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Module Filter
open scoped Classical BigOperators Topology

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

theorem coveringFullCone (x : Ambient n) :
    ∃ s : F.fullCones, x ∈ latticeRayCone s.val := by
  obtain ⟨s, hs, hx⟩ := F.complete x
  obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
  exact ⟨⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩, latticeRayCone_mono hst hx⟩

/-- The genuine Cartier linear form, with value `-a` on each cone ray. -/
def wallSupportForm (a : Lattice n → ℝ) (s : F.fullCones) : Ambient n →ₗ[ℝ] ℝ :=
  dotProductEquiv ℝ (Fin n) (F.cartierPoint a s)

lemma wallSupportForm_ray (a : Lattice n → ℝ) (s : F.fullCones)
    {u : Lattice n} (hu : u ∈ s.val) :
    F.wallSupportForm a s (embed n u) = -a u := by
  change F.cartierPoint a s ⬝ᵥ embed n u = -a u
  rw [dotProduct_comm]
  exact F.cartierPoint_support_eq_of_mem a s hu

lemma wallSupportForm_agree (a : Lattice n → ℝ) (s t : F.fullCones)
    {x : Ambient n} (hs : x ∈ latticeRayCone s.val) (ht : x ∈ latticeRayCone t.val) :
    F.wallSupportForm a s x = F.wallSupportForm a t x := by
  have hi : x ∈ latticeRayCone (s.val ∩ t.val) := by
    rw [← F.intersection s.val (F.fullCones_mem s) t.val (F.fullCones_mem t)]
    exact ⟨hs, ht⟩
  obtain ⟨c, hc, he⟩ := hi
  rw [← he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  rw [map_smul, map_smul,
    F.wallSupportForm_ray a s (Finset.mem_inter.mp hu).1,
    F.wallSupportForm_ray a t (Finset.mem_inter.mp hu).2]

/-- The piecewise linear function on the actual complete fan. -/
def wallSupportFunction (a : Lattice n → ℝ) (x : Ambient n) : ℝ :=
  F.wallSupportForm a (F.coveringFullCone x).choose x

lemma wallSupportFunction_on_cone (a : Lattice n → ℝ) (s : F.fullCones)
    (x : Ambient n) (hx : x ∈ latticeRayCone s.val) :
    F.wallSupportFunction a x = F.wallSupportForm a s x :=
  F.wallSupportForm_agree a _ s (F.coveringFullCone x).choose_spec hx

lemma wallSupportFunction_ray (a : Lattice n → ℝ) {u : Lattice n} (hu : u ∈ F.rays) :
    F.wallSupportFunction a (embed n u) = -a u := by
  obtain ⟨s, hs, hus⟩ := (F.mem_rays_iff u).mp hu
  obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
  let t' : F.fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
  rw [F.wallSupportFunction_on_cone a t' _ (latticeRayCone_generator t (hst hus))]
  exact F.wallSupportForm_ray a t' (hst hus)

lemma wallSupportFunction_continuous (a : Lattice n → ℝ) :
    Continuous (F.wallSupportFunction a) := by
  let cones : F.fullCones → Set (Ambient n) := fun s => latticeRayCone s.val
  apply (locallyFinite_of_finite cones).continuous
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact F.coveringFullCone x
  · intro s
    exact F.isClosed_latticeRayCone (F.fullCones_mem s)
  · intro s
    apply (F.wallSupportForm a s).continuous_of_finiteDimensional.continuousOn.congr
    intro x hx
    exact F.wallSupportFunction_on_cone a s x hx

lemma wallSupportFunction_smul (a : Lattice n → ℝ) (r : ℝ) (hr : 0 ≤ r) (x : Ambient n) :
    F.wallSupportFunction a (r • x) = r * F.wallSupportFunction a x := by
  obtain ⟨s, hs⟩ := F.coveringFullCone x
  rw [F.wallSupportFunction_on_cone a s _ (PointedCone.smul_mem _ hr hs),
    F.wallSupportFunction_on_cone a s x hs, map_smul, smul_eq_mul]

lemma wallSupport_cone_eq (s : F.fullCones) :
    latticeRayCone s.val = PointedCone.hull ℝ (Set.range (integralBasisReal (F.fullConeBasis s))) := by
  rw [F.fullConeBasis_ray_set s, latticeRayCone_basis, finiteRayCone_eq_hull]
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]

private lemma basis_of_range {V : Type*} [AddCommGroup V] [Module ℤ V]
    (b : Basis (Fin n) ℤ V) (v : Fin n → V) (hv : Function.Injective v)
    (hr : Set.range v = Set.range b) :
    ∃ c : Basis (Fin n) ℤ V, ∀ i, c i = v i := by
  have hex (i : Fin n) : ∃ j, b j = v i := by
    have hi : v i ∈ Set.range b := hr ▸ Set.mem_range_self i
    exact hi
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← hf i, ← hf j, hij]
  let e : Fin n ≃ Fin n := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  refine ⟨b.reindex e.symm, ?_⟩
  intro i
  rw [Basis.reindex_apply, Equiv.symm_symm]
  simpa only [e, Equiv.ofBijective_apply] using hf i

lemma aligned_wall_basis (s t : F.fullCones) (j : Fin n) (w : Lattice n)
    (ht : t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)))
    (hw : (F.fullConeBasis s).repr w j = -1) :
    ∃ c : Basis (Fin n) ℤ (Lattice n),
      t.val = Finset.univ.image c ∧ c j = w ∧
      ∀ i, i ≠ j → c i = F.fullConeBasis s i := by
  let b := F.fullConeBasis s
  let v : Fin n → Lattice n := fun i => if i = j then w else b i
  have hwne (i : Fin n) (hij : i ≠ j) : w ≠ b i := by
    intro he
    have hh := congrArg (fun u => b.repr u j) he
    dsimp only [b] at hh
    simp only [hw, Basis.repr_self_apply, if_neg hij] at hh
    omega
  have hvi : Function.Injective v := by
    intro i k hik
    by_cases hi : i = j
    · subst i
      by_cases hk : k = j
      · exact hk.symm
      · exact ((hwne k hk) (by simpa [v, hk] using hik)).elim
    · by_cases hk : k = j
      · subst k
        exact ((hwne i hi) (by simpa [v, hi] using hik.symm)).elim
      · exact b.injective (by simpa [v, hi, hk] using hik)
  have hvset : Finset.univ.image v = t.val := by
    rw [ht]
    ext u
    constructor
    · rintro hu
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      by_cases hij : i = j
      · simp [v, hij]
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_image.mpr ⟨i, by simp [wallIndices, hij], by simp [v, hij, b]⟩
    · intro hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simp [v]⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simp [v, hij, b]⟩
  have hr : Set.range v = Set.range (F.fullConeBasis t) := by
    have he := congrArg (fun z : Finset (Lattice n) => (z : Set (Lattice n)))
      (hvset.trans (F.fullConeBasis_ray_set t))
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using he
  obtain ⟨c, hc⟩ := basis_of_range (F.fullConeBasis t) v hvi hr
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [← hvset]
    congr 1
    exact funext (fun i => (hc i).symm)
  · simpa [v] using hc j
  · intro i hij
    simpa [v, hij] using hc i

/-- Nonnegative slacks for all genuine adjacent full cones. -/
def HasNonnegativeWallSlacks (a : Lattice n → ℝ) : Prop :=
  ∀ (s t : F.fullCones) (j : Fin n) (w : Lattice n),
    t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)) →
    (F.fullConeBasis s).repr w j = -1 →
    0 ≤ a w + F.wallSupportForm a s (embed n w)

lemma wallSupportFunction_locally_concave_at_wall (a : Lattice n → ℝ)
    (ha : F.HasNonnegativeWallSlacks a) (s : F.fullCones) (j : Fin n) (x : Ambient n)
    (hz : (integralBasisReal (F.fullConeBasis s)).repr x j = 0)
    (hp : ∀ i, i ≠ j → 0 < (integralBasisReal (F.fullConeBasis s)).repr x i) :
    ∃ r : ℝ, 0 < r ∧ ConcaveOn ℝ (Metric.ball x r) (F.wallSupportFunction a) := by
  let b := F.fullConeBasis s
  let br := integralBasisReal b
  obtain ⟨t, w, ht, hw, _, _, _⟩ := F.exists_full_opposite_wall F.isPure s j
  obtain ⟨c, hc, hcj, hci⟩ := F.aligned_wall_basis s t j w ht hw
  let cr := integralBasisReal c
  have hshared : ∀ i, i ≠ j → cr i = br i := by
    intro i hij
    simpa only [cr, br, b, integralBasisReal_apply] using congrArg (embed n) (hci i hij)
  have hopp : br.repr (cr j) j = -1 := by
    rw [show cr j = embed n w by simp [cr, hcj], integralBasisReal_repr, hw]
    norm_num
  have htcone : latticeRayCone t.val = PointedCone.hull ℝ (Set.range cr) := by
    rw [hc, latticeRayCone_basis, finiteRayCone_eq_hull]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, cr]
  have hscone : latticeRayCone s.val = PointedCone.hull ℝ (Set.range br) :=
    F.wallSupport_cone_eq s
  have hn := Unimodular.WallSupportGeometry.adjacentBasis_union_mem_nhds_of_positive_facet
    br cr j hshared hopp x hz hp
  rw [← hscone, ← htcone] at hn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let h : ℝ := a w + F.wallSupportForm a s (embed n w)
  have hnonneg : 0 ≤ h := ha s t j w ht hw
  have hd : F.wallSupportForm a t - F.wallSupportForm a s = h • br.coord j := by
    apply cr.ext
    intro i
    by_cases hij : i = j
    · subst i
      have hwt : w ∈ t.val := ht ▸ Finset.mem_insert_self _ _
      have hcjreal : cr j = embed n w := by simp [cr, hcj]
      have hjcoord : br.repr (embed n w) j = -1 := by
        rw [← hcjreal]
        exact hopp
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Basis.coord_apply,
        smul_eq_mul, hcjreal, F.wallSupportForm_ray a t hwt, hjcoord]
      dsimp only [h]
      ring
    · have his : b i ∈ s.val := by
        rw [F.fullConeBasis_ray_set s]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hit : b i ∈ t.val := by
        rw [ht]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨i, by simp [wallIndices, hij], rfl⟩))
      rw [LinearMap.sub_apply, LinearMap.smul_apply, hshared i hij,
        integralBasisReal_apply, F.wallSupportForm_ray a t hit,
        F.wallSupportForm_ray a s his]
      simp [Basis.coord_apply, br, hij]
  have heq : ∀ y ∈ Metric.ball x r,
      F.wallSupportFunction a y = min (F.wallSupportForm a s y) (F.wallSupportForm a t y) := by
    intro y hy
    have hdy := LinearMap.congr_fun hd y
    change F.wallSupportForm a t y - F.wallSupportForm a s y = h * br.repr y j at hdy
    rcases hball hy with hys | hyt
    · rw [F.wallSupportFunction_on_cone a s y hys]
      have hyj := (Unimodular.WallSupportGeometry.mem_basisCone_iff br y).mp
        (hscone ▸ hys) j
      apply (min_eq_left _).symm
      have hm := mul_nonneg hnonneg hyj
      linarith
    · rw [F.wallSupportFunction_on_cone a t y hyt]
      have hyj := (Unimodular.WallSupportGeometry.mem_basisCone_iff cr y).mp
        (htcone ▸ hyt) j
      have hneg := Unimodular.WallSupportGeometry.adjacentBasis_omitted_coordinate_neg
        br cr j hshared hopp y
      apply (min_eq_right _).symm
      have hm := mul_nonpos_of_nonneg_of_nonpos hnonneg
        (show br.repr y j ≤ 0 by linarith)
      linarith
  refine ⟨r, hr, ?_⟩
  apply (((F.wallSupportForm a s).concaveOn (convex_ball x r)).inf
    ((F.wallSupportForm a t).concaveOn (convex_ball x r))).congr
  intro y hy
  exact (heq y hy).symm

lemma wallSupportFunction_concave_of_nonnegative_walls (a : Lattice n → ℝ)
    (ha : F.HasNonnegativeWallSlacks a) : ConcaveOn ℝ Set.univ (F.wallSupportFunction a) := by
  let labels := Σ s : F.fullCones, {p : Fin n × Fin n // p.1 ≠ p.2}
  let subspaces : labels → Submodule ℝ (Ambient n) := fun q =>
    ((integralBasisReal (F.fullConeBasis q.1)).coord q.2.val.1).ker ⊓
    ((integralBasisReal (F.fullConeBasis q.1)).coord q.2.val.2).ker
  refine Unimodular.WallSupportGeometry.concaveOn_univ_of_continuous_locally_concave_off_finite_subspaces
    subspaces ?_ (F.wallSupportFunction a) (F.wallSupportFunction_continuous a) ?_
  · intro q x
    exact Unimodular.WallSupportGeometry.basis_pair_ker_sup_span_singleton_ne_top
      (integralBasisReal (F.fullConeBasis q.1)) q.2.val.1 q.2.val.2 q.2.property x
  · intro x hx
    obtain ⟨s, hs⟩ := F.coveringFullCone x
    let b := integralBasisReal (F.fullConeBasis s)
    have hnonneg : ∀ i, 0 ≤ b.repr x i := by
      apply (Unimodular.WallSupportGeometry.mem_basisCone_iff b x).mp
      rwa [← F.wallSupport_cone_eq s]
    by_cases hpos : ∀ i, 0 < b.repr x i
    · have hinter := Unimodular.WallSupportGeometry.mem_interior_basisCone_of_positive b x hpos
      rw [← F.wallSupport_cone_eq s] at hinter
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinter)
      refine ⟨r, hr, ?_⟩
      apply ((F.wallSupportForm a s).concaveOn (convex_ball x r)).congr
      intro y hy
      exact (F.wallSupportFunction_on_cone a s y (hball hy)).symm
    · push_neg at hpos
      obtain ⟨j, hj⟩ := hpos
      have hz : b.repr x j = 0 := le_antisymm hj (hnonneg j)
      apply F.wallSupportFunction_locally_concave_at_wall a ha s j x hz
      intro i hij
      have hne : b.repr x i ≠ 0 := by
        intro hi
        exact hx (⟨s, ⟨(i,j), hij⟩⟩ : labels) ⟨hi,hz⟩
      exact lt_of_le_of_ne (hnonneg i) hne.symm

lemma wallSupportFunction_superadditive (a : Lattice n → ℝ)
    (hc : ConcaveOn ℝ Set.univ (F.wallSupportFunction a)) (x y : Ambient n) :
    F.wallSupportFunction a x + F.wallSupportFunction a y ≤ F.wallSupportFunction a (x+y) := by
  have hm := hc.2 (Set.mem_univ x) (Set.mem_univ y)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  rw [← smul_add, ← smul_add, F.wallSupportFunction_smul a (1/2) (by norm_num)] at hm
  simp only [smul_eq_mul] at hm
  linarith

/-- Global support follows from local walls on every complete smooth fan. -/
theorem isNef_of_nonnegative_wall_slacks (a : Lattice n → ℝ)
    (ha : F.HasNonnegativeWallSlacks a) : F.IsNef a := by
  have hc := F.wallSupportFunction_concave_of_nonnegative_walls a ha
  intro r hr
  obtain ⟨s, hs, hrs, hcard⟩ := F.isPure r hr
  let s' : F.fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs,hcard⟩⟩
  refine ⟨-F.wallSupportForm a s', ?_, ?_⟩
  · intro u hu
    rw [LinearMap.neg_apply, F.wallSupportForm_ray a s' (hrs hu), neg_neg]
  · intro u hu
    let b := integralBasisReal (F.fullConeBasis s')
    let upper : Ambient n := b.equivFun.symm (fun i => max (b.repr (embed n u) i) 0)
    have hupper (i : Fin n) : b.repr upper i = max (b.repr (embed n u) i) 0 := by
      change b.equivFun upper i = _
      simp only [upper, LinearEquiv.apply_symm_apply]
    have hup : upper ∈ latticeRayCone s := by
      rw [F.wallSupport_cone_eq s']
      apply (Unimodular.WallSupportGeometry.mem_basisCone_iff b upper).mpr
      intro i
      rw [hupper]
      exact le_max_right _ _
    have hlo : upper - embed n u ∈ latticeRayCone s := by
      rw [F.wallSupport_cone_eq s']
      apply (Unimodular.WallSupportGeometry.mem_basisCone_iff b _).mpr
      intro i
      rw [map_sub, Finsupp.sub_apply, hupper]
      exact sub_nonneg.mpr (le_max_left _ _)
    have hh := F.wallSupportFunction_superadditive a hc (upper - embed n u) (embed n u)
    rw [sub_add_cancel, F.wallSupportFunction_on_cone a s' upper hup,
      F.wallSupportFunction_on_cone a s' _ hlo, F.wallSupportFunction_ray a hu,
      map_sub] at hh
    change -F.wallSupportForm a s' (embed n u) ≤ a u
    linarith

/-- Exact integer-wall interface used by the ordinary sheaf-degree theorem. -/
theorem isNef_of_integerWallSlack_nonneg (a : Lattice n → ℤ)
    (ha : ∀ (s t : F.fullCones) (j : Fin n) (w : Lattice n),
      t.val = insert w ((F.wallIndices s j).image (F.fullConeBasis s)) →
      (F.fullConeBasis s).repr w j = -1 →
      0 ≤ F.integerWallSlack a s w) :
    F.IsNef (fun u => (a u : ℝ)) := by
  apply F.isNef_of_nonnegative_wall_slacks
  intro s t j w ht hw
  have h := ha s t j w ht hw
  have he : F.wallSupportForm (fun u => (a u : ℝ)) s (embed n w) =
      (integerPairing w (F.cartierLatticePoint a s) : ℝ) := by
    change F.cartierPoint (fun u => (a u : ℝ)) s ⬝ᵥ embed n w = _
    rw [← F.embed_cartierLatticePoint a s, dotProduct_comm]
    exact normalRay_pairing_lattice w (F.cartierLatticePoint a s)
  rw [he]
  change 0 ≤ a w + integerPairing w (F.cartierLatticePoint a s) at h
  change (0 : ℝ) ≤ (a w : ℝ) + (integerPairing w (F.cartierLatticePoint a s) : ℝ)
  rw [← Int.cast_add]
  exact Int.cast_nonneg h

#print axioms isNef_of_integerWallSlack_nonneg

end PaperVerification.ToricGeometry.SmoothCompleteFan
