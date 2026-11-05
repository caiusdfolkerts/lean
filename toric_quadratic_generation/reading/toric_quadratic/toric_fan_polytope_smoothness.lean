module

public import PaperVerification.ToricFanPolytopeConstruction
public import PaperVerification.ToricFanConstruction

@[expose] public section

/-!
# Smoothness and the exact normal fan of the support polytope

An arbitrary actual incident edge is forced onto one dual coordinate ray
by the minimal face of its endpoints. This rules out omitted incident
edges. All normal cones, including the zero cone and proper face cones,
are then identified with the original finite fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def supportInequalities (a : Lattice n → ℝ) :
    AffineInequalities «Σ».rays (Ambient n) :=
  AffineInequalities.ofSlack (fun u =>
    (dotProductEquiv ℝ (Fin n) (embed n u)).toAffineMap +
      AffineMap.const ℝ (Ambient n) (a u))

theorem supportInequalities_slack (a : Lattice n → ℝ) (u : «Σ».rays)
    (x : Ambient n) :
    («Σ».supportInequalities a).slack u x =
      (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u := rfl

theorem supportInequalities_region (a : Lattice n → ℝ) :
    («Σ».supportInequalities a).region = «Σ».fanPolytope a := by
  ext x
  change (∀ u : «Σ».rays, 0 ≤
    (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) ↔ _
  constructor
  · intro h u hu
    have hh := h ⟨u, hu⟩
    change -a u ≤ _
    linarith
  · intro h u
    have hh := h u u.property
    change -a u ≤ _ at hh
    linarith

/-- Any actual edge incident to a Cartier vertex lies on exactly one of
the primitive dual coordinate rays. This conclusion is derived from the
actual finite halfspace face, not assumed as fan combinatorics. -/
theorem support_polytope_edge_has_coordinate_direction
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones)
    (w : Ambient n)
    (hedge : («Σ».supportLatticePolytope hpure a ha).IsEdge
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) w) :
    ∃ i : Fin n, w ∈ («Σ».supportLatticePolytope hpure a ha).coordinateRayFace
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  let v := «Σ».cartierPoint aR s
  let b := «Σ».cartierBasis s
  let H := «Σ».supportInequalities aR
  have hPH : P.carrier = H.region := by
    rw [«Σ».supportInequalities_region, «Σ».supportLatticePolytope_carrier]
  obtain ⟨hvP, hwP⟩ := P.edge_endpoints_extreme hedge
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ b.repr (x - v) j := by
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have hpositive : ∃ i : Fin n, 0 < b.repr (w - v) i := by
    by_contra hn
    push_neg at hn
    have heq : w = v := by
      apply b.ext_elem
      intro i
      have hz := le_antisymm (hn i) (horthant w hwP.1 i)
      simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz
    exact hedge.1 heq.symm
  obtain ⟨i, hi⟩ := hpositive
  obtain ⟨ε, hε, hpoint⟩ := «Σ».exists_positive_axis_point ha s i
  let z := v + ε • b i
  have hzH : z ∈ H.region := by
    rw [«Σ».supportInequalities_region]
    exact hpoint
  have hzface : z ∈ H.face (H.jointZeros v w) := by
    refine ⟨hzH, ?_⟩
    intro u hu
    have huv := hu.1
    have huw := hu.2
    have hucone : (u : Lattice n) ∈ (s : Finset (Lattice n)) := by
      by_contra hus
      have hh := «Σ».cartierPoint_support_lt_of_not_mem ha s u.property hus
      rw [«Σ».supportInequalities_slack] at huv
      change (dotProductEquiv ℝ (Fin n) (embed n u)) v + aR u = 0 at huv
      linarith
    obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hucone)
    have hjne : j ≠ i := by
      intro hji
      subst j
      have he : b.repr (w - v) i = 0 := by
        rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
        change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i))) w -
          -aR («Σ».fullConeBasis s i) = 0
        rw [hju]
        simpa only [H, «Σ».supportInequalities_slack, sub_neg_eq_add] using huw
      linarith
    rw [«Σ».supportInequalities_slack]
    have hp : (dotProductEquiv ℝ (Fin n) (embed n u)) (b i) = 0 := by
      rw [← hju]
      change (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s j))) (b i) = 0
      rw [«Σ».activeRay_dual]
      simp [b, Module.Basis.repr_self_apply, hjne, Ne.symm hjne]
    change (dotProductEquiv ℝ (Fin n) (embed n u)) (v + ε • b i) + aR u = 0
    rw [map_add, map_smul, hp, smul_zero, add_zero]
    exact huv
  have hmin := H.jointFace_minimal (hPH ▸ hvP.1) (hPH ▸ hwP.1)
    (convex_segment v w) (by simpa only [← hPH] using hedge.2)
    (left_mem_segment ℝ v w) (right_mem_segment ℝ v w)
  have hzseg : z ∈ segment ℝ v w := hmin hzface
  obtain ⟨r, t, hr, ht, hrt, hline⟩ := hzseg
  have hcoords (j : Fin n) :
      ε * (if i = j then 1 else 0) = t * b.repr (w - v) j := by
    have he := congrArg (fun x => b.repr x j) hline
    change b.repr (r • v + t • w) j = b.repr (v + ε • b i) j at he
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, smul_eq_mul] at he
    simp only [map_sub, Finsupp.sub_apply]
    have hbase : (r + t) * b.repr v j = b.repr v j := by rw [hrt, one_mul]
    nlinarith only [he, hbase]
  have htne : t ≠ 0 := by
    intro he
    have hh := hcoords i
    simp [he] at hh
    linarith
  refine ⟨i, hwP.1, ?_⟩
  intro j hji
  have he := hcoords j
  rw [if_neg (Ne.symm hji), mul_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left htne

/-- All coordinate-ray faces have actual positive integral endpoints. -/
theorem support_polytope_coordinate_edges
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    ∃ lengths : Fin n → ℕ, ∀ i,
      0 < lengths i ∧
      («Σ».supportLatticePolytope hpure a ha).IsEdge
        («Σ».cartierPoint (fun u => (a u : ℝ)) s)
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) ∧
      («Σ».supportLatticePolytope hpure a ha).coordinateRayFace
        («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i =
        segment ℝ («Σ».cartierPoint (fun u => (a u : ℝ)) s)
          (embed n («Σ».cartierLatticePoint a s +
            (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  have hvgen : «Σ».cartierLatticePoint a s ∈ P.generators :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have hex (i : Fin n) := P.coordinateRayFace_eq_integral_edge
    («Σ».cartierLatticePoint a s) hvgen (integralDualBasis («Σ».fullConeBasis s)) horthant i
    (by simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint,
      «Σ».supportLatticePolytope_carrier] using «Σ».exists_positive_axis_point ha s i)
  choose lengths hlengths using hex
  refine ⟨lengths, ?_⟩
  intro i
  simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint] using hlengths i

/-- The resulting lattice polytope is smooth in the literal all-edges
definition. Both existence and completeness of the incident basis edges
have been proved independently. -/
theorem supportLatticePolytope_smooth
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).Smooth := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  intro v hv
  have hP : P.carrier = convexHull ℝ (Set.range («Σ».cartierPoint aR)) := by
    rw [«Σ».supportLatticePolytope_carrier,
      «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
  have hv' : v ∈ (convexHull ℝ (Set.range («Σ».cartierPoint aR))).extremePoints ℝ :=
    hP ▸ hv
  obtain ⟨s, rfl⟩ := extremePoints_convexHull_subset hv'
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  refine ⟨«Σ».cartierLatticePoint a s, integralDualBasis («Σ».fullConeBasis s), lengths,
    «Σ».embed_cartierLatticePoint a s, ?_, ?_⟩
  · intro i
    exact ⟨(hlengths i).1, (hlengths i).2.1⟩
  · intro w hw
    obtain ⟨i, hi⟩ := «Σ».support_polytope_edge_has_coordinate_direction hpure a ha s w hw
    have hwseg := (hlengths i).2.2 ▸ hi
    have hverts := P.edge_endpoints_extreme hw
    have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
    rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
      _ hverts.1.1 _ hend hwseg with hvw | hew
    · exact (hw.1 hvw).elim
    · exact ⟨i, hew.symm⟩

/-- The actual normal cone at each integral Cartier vertex is its full
original fan cone, with no rescaling or missing primitive ray. -/
theorem supportLatticePolytope_cartier_normalCone
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    («Σ».supportLatticePolytope hpure a ha).normalCone
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) =
      (latticeRayCone (s : Finset (Lattice n)) : Set (Ambient n)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  have hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n («Σ».cartierLatticePoint a s))
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    intro i
    simpa only [«Σ».embed_cartierLatticePoint] using
      ⟨(hlengths i).1, (hlengths i).2.1⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have heq := P.normalCone_eq_latticeRayCone («Σ».cartierLatticePoint a s)
    (integralDualBasis («Σ».fullConeBasis s)) lengths hedges horthant
  simpa only [«Σ».embed_cartierLatticePoint, integralDualBasis_involutive,
    ← «Σ».fullConeBasis_ray_set] using heq

/-- Equality of the entire actual normal fan, including all proper cones. -/
theorem supportLatticePolytope_normalFan
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).normalFan = «Σ».realCones := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  have hnormal := «Σ».supportLatticePolytope_cartier_normalCone hpure a ha
  have hv (s : «Σ».fullCones) : «Σ».cartierPoint aR s ∈ P.carrier := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hhull : x ∈ convexHull ℝ (Set.range («Σ».cartierPoint aR)) := by
      rw [← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha),
        ← «Σ».supportLatticePolytope_carrier hpure a ha]
      exact hx
    obtain ⟨p, hp, hpsum, hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        («Σ».cartierPoint aR) hhull
    let K := Finset.univ.filter (fun s : «Σ».fullCones => 0 < p s)
    have hK : K.Nonempty := by
      have hpos : 0 < ∑ s, p s := by rw [hpsum]; norm_num
      obtain ⟨s, hs, hps⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => hp s)).mp hpos
      exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hps⟩⟩
    obtain ⟨t, ht, hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun s : «Σ».fullCones => (s : Finset (Lattice n))) hK
      (fun s _ => «Σ».fullCones_mem s)
    refine ⟨t, ht, ?_⟩
    ext u
    rw [← hpm, P.mem_normalCone_convex_average («Σ».cartierPoint aR) p hv hp hpsum u]
    change (∀ s : «Σ».fullCones, 0 < p s → u ∈ P.normalCone («Σ».cartierPoint aR s)) ↔
      u ∈ latticeRayCone t
    rw [hspec u]
    simp only [P, aR, hnormal, K, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    let d := «Σ».fullConeBasis s'
    let I := basisRayIndices d t
    have htfull : t ⊆ Finset.univ.image d := by
      rw [← «Σ».fullConeBasis_ray_set s']
      exact hts
    have hI : I.image d = t := image_basisRayIndices d t htfull
    obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s'
    have hedges : ∀ i, 0 < lengths i ∧
        P.IsEdge (embed n («Σ».cartierLatticePoint a s'))
          (embed n («Σ».cartierLatticePoint a s' + (lengths i : ℤ) • integralDualBasis d i)) := by
      intro i
      simpa only [«Σ».embed_cartierLatticePoint] using
        ⟨(hlengths i).1, (hlengths i).2.1⟩
    have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
        0 ≤ (integralBasisReal (integralDualBasis d)).repr
          (x - embed n («Σ».cartierLatticePoint a s')) j := by
      rw [«Σ».embed_cartierLatticePoint]
      exact «Σ».cartierPoint_orthant s' ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
    have hsub := P.subbasis_mem_normalFan («Σ».cartierLatticePoint a s')
      (by simpa only [«Σ».embed_cartierLatticePoint] using hv s')
      (integralDualBasis d) lengths hedges horthant I
    simpa only [integralDualBasis_involutive, hI] using hsub

/-- The complete reverse dictionary required by dimension induction. -/
theorem exists_smooth_latticePolytope_of_integral_strictSupport
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    ∃ P : LatticePolytope n,
      P.carrier = «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      P.Smooth ∧ P.normalFan = «Σ».realCones := by
  exact ⟨«Σ».supportLatticePolytope hpure a ha,
    «Σ».supportLatticePolytope_carrier hpure a ha,
    «Σ».supportLatticePolytope_smooth hpure a ha,
    «Σ».supportLatticePolytope_normalFan hpure a ha⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
