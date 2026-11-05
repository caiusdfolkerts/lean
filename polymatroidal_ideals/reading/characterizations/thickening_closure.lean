import Characterizations.Thickening

/-! # Exact closure and sharp power threshold for minimal local obstructions -/
noncomputable section
namespace Characterizations
universe u
open Classical CommAlg CommAlg.Polymatroid Finset
open scoped Pointwise
variable {V : Type u} [Fintype V] [DecidableEq V]

@[simp] theorem realExponent_add (a b : Exponent V) :
    realExponent (a+b) = realExponent a + realExponent b := by
  ext i
  simp [realExponent]

theorem realImage_thickening (B : Family V) (q : ℕ) :
    realExponent '' (thickening B q : Set (Exponent V)) =
      (realExponent '' (B : Set (Exponent V))) +
        (realExponent '' (degreeFamily (V := V) q : Set (Exponent V))) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    exact Set.mem_add.mpr ⟨realExponent b,Set.mem_image_of_mem _ hb,
      realExponent c,Set.mem_image_of_mem _ hc,(realExponent_add b c).symm⟩
  · intro hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Set.mem_add.mp hx
    obtain ⟨b,hb,rfl⟩ := hy
    obtain ⟨c,hc,rfl⟩ := hz
    exact ⟨b+c,mem_image.mpr ⟨(b,c),mem_product.mpr ⟨hb,hc⟩,rfl⟩,realExponent_add b c⟩

theorem closed_thickening_generator_mem_convexHull {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (q : ℕ) {a : Exponent V} (ha : a ∈ thickening (lowerBaseFamily (lowerRank B) d) q) :
    realExponent a ∈ convexHull ℝ (realExponent '' (thickening B q : Set (Exponent V))) := by
  obtain ⟨⟨b,c⟩,hbc,rfl⟩ := mem_image.mp ha
  obtain ⟨hb,hc⟩ := mem_product.mp hbc
  rw [realExponent_add, realImage_thickening, convexHull_add]
  exact Set.add_mem_add (canonicalLowerBase_mem_convexHull hB hanti hl hd hb)
    (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hc))

theorem thickening_polymatroidal_iff_closed [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔
      thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q := by
  constructor
  · intro hp
    apply Finset.Subset.antisymm (thickening_mono (subset_lowerBaseFamily hd) q)
    intro a ha
    have hi := monomial_integral_of_convexHull ℚ (thickening B q) a
      (closed_thickening_generator_mem_convexHull hB hanti hl hd q ha)
    have hm := polymatroidal_integrallyClosed (thickening_nonempty hB q) hp _ hi
    have hcontains := (monomial_mem_iff (k := ℚ) _ _).mp hm
    have hdeg := thickening_equigenerated (lowerBaseFamily_equigenerated (lowerRank B) d) q a ha
    exact ((thickening_equigenerated hd q).mem_iff_contains hdeg).mpr hcontains
  · intro he
    rw [he]
    exact thickening_polymatroidal (hB.mono (subset_lowerBaseFamily hd))
      (canonicalLowerBases_polymatroidal hB hl hd) q

theorem thickening_eq_closed_iff_hole_bound {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (q : ℕ) :
    thickening B q = thickening (lowerBaseFamily (lowerRank B) d) q ↔
      ∀ a ∈ holeSet B, a.degree < d+q := by
  constructor
  · intro he a ha
    by_contra hn
    have hc : Contains (thickening (lowerBaseFamily (lowerRank B) d) q) a :=
      (contains_thickening_iff (lowerBaseFamily_equigenerated _ _) q a).mpr
        ⟨(contains_canonicalLowerBases_iff hB hl hd a).mpr ha.1,by omega⟩
    rw [← he] at hc
    exact ha.2 ((contains_thickening_iff hd q a).mp hc).1
  · intro h
    apply family_eq_of_contains_iff (thickening_equigenerated hd q).antichain
      (thickening_equigenerated (lowerBaseFamily_equigenerated _ _) q).antichain
    intro a
    rw [contains_thickening_iff hd, contains_thickening_iff (lowerBaseFamily_equigenerated _ _),
      contains_canonicalLowerBases_iff hB hl hd]
    constructor
    · rintro ⟨⟨b,hb,hba⟩,hdeg⟩
      exact ⟨fun U => (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i)),hdeg⟩
    · rintro ⟨ha,hdeg⟩
      refine ⟨?_,hdeg⟩
      by_contra hout
      exact (not_lt_of_ge hdeg) (h a ⟨ha,hout⟩)

theorem thickening_polymatroidal_iff_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree) (q : ℕ) :
    IsPolymatroidal (thickening B q) ↔ a.degree < d+q := by
  rw [thickening_polymatroidal_iff_closed hB hanti hl hd,
    thickening_eq_closed_iff_hole_bound hB hl hd]
  exact ⟨fun h => h a ha,fun h b hb => (hmax b hb).trans_lt h⟩

theorem least_polymatroidal_thickening [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hda : d ≤ a.degree) :
    IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (a.degree+1-d) := by
  constructor
  · exact (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax _).mpr (by omega)
  · intro q hq
    have h := (thickening_polymatroidal_iff_top_hole hB hanti hl hd ha hmax q).mp hq
    omega

end Characterizations
