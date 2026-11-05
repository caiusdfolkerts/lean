module

public import PaperVerification.ToricCanonicalCenters
public import PaperVerification.ToricCenterCovering
public import PaperVerification.ToricAdjointSupport

@[expose] public section

/-!
# Literal ray inequalities for the covered targets

The center-polytope tests are derived on the actual common subdivision.
Singleton selected foci remain old rays and are included in the same
calculation. The integral slacks are the genuine primitive pairings with
the lattice target, before any cast to the reals.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

def latticeSlack {n : ℕ} (a : Lattice n → ℤ) (m u : Lattice n) : ℤ :=
  (∑ j, u j * m j) + a u

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem latticeSlack_cast («Σ» : SmoothCompleteFan n)
    (a : Lattice n → ℤ) (m u : Lattice n) :
    (latticeSlack a m u : ℝ) =
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n m) + a u := by
  rw [normalRay_pairing_lattice]
  simp only [latticeSlack, Int.cast_add]

theorem latticeSlack_pos_of_interior (a : Lattice n → ℤ) (m : Lattice n)
    (hm : embed n m ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))))
    (u : Lattice n) (hu : u ∈ «Σ».rays) : 0 < latticeSlack a m u := by
  rw [«Σ».interior_fanPolytope_eq] at hm
  have h := hm u hu
  have hc := «Σ».latticeSlack_cast a m u
  have hr : (0 : ℝ) < (latticeSlack a m u : ℝ) := by linarith
  exact_mod_cast hr

theorem normalRay_sum_pairing («Σ» : SmoothCompleteFan n)
    (T : Finset (Lattice n)) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n (∑ u ∈ T, u))) x =
      ∑ u ∈ T, (dotProductEquiv ℝ (Fin n) (embed n u)) x := by
  simp only [map_sum, LinearMap.sum_apply]

variable {ι : Type*} [Fintype ι] (R : ι → «Σ».PrimitiveRelation)
variable (hne : ∀ i, (R i).negative.Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci (fun i => (R i).negative))

theorem selectedFan_isPure (hpure : «Σ».IsPure) :
    («Σ».selectedFan R hne hdisj).IsPure :=
  «Σ».isPure_simultaneousSubdivision («Σ».selectedStarFocus R) hpure
    (fun i => (R i).negative_cone) (fun i => hne i)
    («Σ».selectedStarFocus_disjoint R hdisj)

theorem selectedPullback_old (a : Lattice n → ℝ)
    (u : Lattice n) (hu : u ∈ «Σ».rays) : «Σ».selectedPullback R a u = a u :=
  «Σ».simultaneousSupport_old («Σ».selectedStarFocus R)
    (fun i => (R i).negative_cone) (fun i => i.property) a 0 u hu

theorem selectedPullback_add (a b : Lattice n → ℝ) :
    «Σ».selectedPullback R (a + b) = «Σ».selectedPullback R a + «Σ».selectedPullback R b := by
  funext v
  simp only [selectedPullback, simultaneousSupport, Pi.add_apply, Pi.zero_apply,
    sub_zero, Finset.sum_add_distrib]
  have h : (∑ i : «Σ».BlowupIndices R,
      if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
        ((∑ w ∈ «Σ».selectedStarFocus R i, a w) + ∑ w ∈ «Σ».selectedStarFocus R i, b w) -
          (a v + b v) else 0) =
      (∑ i : «Σ».BlowupIndices R,
        if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
          (∑ w ∈ «Σ».selectedStarFocus R i, a w) - a v else 0) +
      ∑ i : «Σ».BlowupIndices R,
        if v = ∑ w ∈ «Σ».selectedStarFocus R i, w then
          (∑ w ∈ «Σ».selectedStarFocus R i, b w) - b v else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [h]
  ring

def selectedCenterSupport (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) : Lattice n → ℝ :=
  fun v => «Σ».selectedPullback R a v - c -
    ∑ i, if v = «Σ».selectedRay R i then t i else 0

theorem selectedCenterSupport_add (a b : Lattice n → ℝ)
    (c d : ℝ) (t s : ι → ℝ) :
    «Σ».selectedCenterSupport R a c t + «Σ».selectedCenterSupport R b d s =
      «Σ».selectedCenterSupport R (a + b) (c + d) (t + s) := by
  funext v
  simp only [selectedCenterSupport, «Σ».selectedPullback_add R, Pi.add_apply]
  have h : (∑ i, if v = «Σ».selectedRay R i then t i + s i else 0) =
      (∑ i, if v = «Σ».selectedRay R i then t i else 0) +
      ∑ i, if v = «Σ».selectedRay R i then s i else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [h]
  ring

include hne hdisj in
theorem selectedCenterSupport_at_selected_ray
    (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) (i : ι) :
    «Σ».selectedCenterSupport R a c t («Σ».selectedRay R i) =
      (∑ u ∈ (R i).negative, a u) - c - t i := by
  rw [selectedCenterSupport, «Σ».selectedPullback_at_selected_ray R hne hdisj]
  have h : (∑ j, if «Σ».selectedRay R i = «Σ».selectedRay R j then t j else 0) = t i := by
    simp only [(«Σ».selectedRay_injective R hdisj).eq_iff]
    simp
  rw [h]

/-- The old inequalities and the total-height inequality at every
selected locus imply membership in the literal center polytope. -/
theorem mem_selectedCenterSupport_of_slacks
    (a : Lattice n → ℝ) (c : ℝ) (t : ι → ℝ) (x : Ambient n)
    (hold : ∀ u ∈ «Σ».rays,
      c ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u)
    (hselected : ∀ i, c + t i ≤ ∑ u ∈ (R i).negative,
      ((dotProductEquiv ℝ (Fin n) (embed n u)) x + a u)) :
    x ∈ («Σ».selectedFan R hne hdisj).fanPolytope
      («Σ».selectedCenterSupport R a c t) := by
  intro u hu
  by_cases hex : ∃ i, u = «Σ».selectedRay R i
  · obtain ⟨i, rfl⟩ := hex
    rw [«Σ».selectedCenterSupport_at_selected_ray R hne hdisj]
    have hd := «Σ».normalRay_sum_pairing (R i).negative x
    have hh := hselected i
    rw [Finset.sum_add_distrib] at hh
    change (dotProductEquiv ℝ (Fin n)
      (embed n («Σ».selectedRay R i))) x = _ at hd
    linarith
  · have hn : ∀ i, u ≠ «Σ».selectedRay R i := by simpa only [not_exists] using hex
    have holdray : u ∈ «Σ».rays := by
      rw [selectedFan, «Σ».simultaneous_rays_eq («Σ».selectedStarFocus R)
        (fun i => (R i).negative_cone) (fun i => hne i)
        («Σ».selectedStarFocus_disjoint R hdisj) (fun i => i.property)] at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hu
      · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hu
        exact False.elim (hn i he.symm)
    rw [selectedCenterSupport, «Σ».selectedPullback_old R a u holdray]
    simp only [hn, if_false, Finset.sum_const_zero, sub_zero]
    linarith [hold u holdray]

end SmoothCompleteFan

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Exact sufficient height test from Section 6.3, including a selected
old ray when its focus has cardinality one. -/
theorem parity_centers_cover_of_slacks (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (hne : ∀ i, («Σ».parityFamily P Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i,
      «Σ».parityDisplacements P Q P hne i + «Σ».parityDisplacements P Q Q hne i + 2 ≤
        ∑ u ∈ («Σ».parityFamily P Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) :
    let Γ := «Σ».selectedFan («Σ».parityFamily P Q) hne
      («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
    embed n m ∈ Γ.fanPolytope
      («Σ».parityCenter P Q P hne + «Σ».parityCenter P Q Q hne) := by
  let R := «Σ».parityFamily P Q
  let t : «Σ».parityIndices P Q → ℝ := fun i => «Σ».parityDisplacements P Q P hne i
  let s : «Σ».parityIndices P Q → ℝ := fun i => «Σ».parityDisplacements P Q Q hne i
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let b : Lattice n → ℝ := fun u => (Q.integralSupport u : ℝ)
  change embed n m ∈ («Σ».selectedFan R hne
    («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)).fanPolytope
    («Σ».selectedCenterSupport R a 1 t + «Σ».selectedCenterSupport R b 1 s)
  rw [«Σ».selectedCenterSupport_add]
  apply «Σ».mem_selectedCenterSupport_of_slacks R hne
    («Σ».parityFamily_disjoint hpure P Q hP hQ hfanP hfanQ hboundP hboundQ)
  · intro u hu
    have hh : (2 : ℝ) ≤ (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hold u hu
    rw [«Σ».latticeSlack_cast] at hh
    simpa only [a, b, Pi.add_apply, Int.cast_add, show (1 : ℝ) + 1 = 2 by norm_num]
      using hh
  · intro i
    have hh : («Σ».parityDisplacements P Q P hne i : ℝ) +
        («Σ».parityDisplacements P Q Q hne i : ℝ) + 2 ≤
        ∑ u ∈ (R i).negative,
          (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hselected i
    simp only [«Σ».latticeSlack_cast, Pi.add_apply, Int.cast_add] at hh
    dsimp [a, b, t, s]
    linarith

/-- Exact sufficient height test from Section 7.5. The two different
canonical shifts add to two on old rays, and to q+t+1 at a selected locus. -/
theorem adjoint_centers_cover_of_slacks (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n) (hP : P.Smooth) (hQ : Q.Smooth)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1))
    (hne : ∀ i, («Σ».adjointFamily Q i).negative.Nonempty)
    (m : Lattice n)
    (hold : ∀ u ∈ «Σ».rays, 2 ≤ latticeSlack (P.integralSupport + Q.integralSupport) m u)
    (hselected : ∀ i, ((«Σ».adjointFamily Q i).negative.card : ℤ) +
      «Σ».adjointDisplacements Q hne i + 1 ≤
        ∑ u ∈ («Σ».adjointFamily Q i).negative,
          latticeSlack (P.integralSupport + Q.integralSupport) m u) :
    let Γ := «Σ».selectedFan («Σ».adjointFamily Q) hne
      («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
    embed n m ∈ Γ.fanPolytope
      («Σ».firstAdjointCenter P Q + «Σ».secondAdjointCenter Q hne) := by
  let R := «Σ».adjointFamily Q
  let t : «Σ».adjointIndices Q → ℝ := fun i => (R i).negative.card - 1
  let s : «Σ».adjointIndices Q → ℝ := fun i => «Σ».adjointDisplacements Q hne i
  let a : Lattice n → ℝ := fun u => (P.integralSupport u : ℝ)
  let b : Lattice n → ℝ := fun u => (Q.integralSupport u : ℝ)
  change embed n m ∈ («Σ».selectedFan R hne
    («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)).fanPolytope
    («Σ».selectedCenterSupport R a (1 / 2) t +
      «Σ».selectedCenterSupport R b (3 / 2) s)
  rw [«Σ».selectedCenterSupport_add]
  apply «Σ».mem_selectedCenterSupport_of_slacks R hne
    («Σ».adjointFamily_disjoint hpure Q hQ hfanQ hboundQ)
  · intro u hu
    have hh : (2 : ℝ) ≤ (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hold u hu
    rw [«Σ».latticeSlack_cast] at hh
    simpa only [a, b, Pi.add_apply, Int.cast_add,
      show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num] using hh
  · intro i
    have hh : ((R i).negative.card : ℝ) + («Σ».adjointDisplacements Q hne i : ℝ) + 1 ≤
        ∑ u ∈ (R i).negative,
          (latticeSlack (P.integralSupport + Q.integralSupport) m u : ℝ) := by
      exact_mod_cast hselected i
    simp only [«Σ».latticeSlack_cast, Pi.add_apply, Int.cast_add] at hh
    dsimp [a, b, t, s]
    linarith

/-- The primitive slacks of an actual interior Minkowski target are
positive integers. No interior condition has been replaced by a weaker
set of inequalities in the final induction. -/
theorem latticeSlack_pos_of_interior_minkowski (hpure : «Σ».IsPure)
    (P Q : LatticePolytope n)
    (hfanP : «Σ».realCones = P.normalFan) (hfanQ : «Σ».realCones = Q.normalFan)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∀ u ∈ «Σ».rays, 0 < latticeSlack (P.integralSupport + Q.integralSupport) m u := by
  have ha := P.integralSupport_isStrictSupport «Σ» hfanP
  have hb := Q.integralSupport_isStrictSupport «Σ» hfanQ
  have he : (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) =
      (fun u => (P.integralSupport u : ℝ)) +
        (fun u => (Q.integralSupport u : ℝ)) := by
    funext u
    simp
  have hset : «Σ».fanPolytope
      (fun u => ((P.integralSupport + Q.integralSupport) u : ℝ)) = P.minkowskiSum Q := by
    rw [he, «Σ».fanPolytope_add hpure _ _
      (IsStrictSupport.isNef «Σ» ha) (IsStrictSupport.isNef «Σ» hb),
      P.fanPolytope_integralSupport_eq «Σ» hfanP,
      Q.fanPolytope_integralSupport_eq «Σ» hfanQ]
    rfl
  intro u hu
  exact «Σ».latticeSlack_pos_of_interior _ m (hset.symm ▸ hm) u hu

end SmoothCompleteFan

end PaperVerification.ToricGeometry
