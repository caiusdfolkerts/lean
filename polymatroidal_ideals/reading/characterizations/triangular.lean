import Characterizations.TriangleCore
import Characterizations.MinimalMixedObstruction

/-! # The degree-bounded and triangular localization characterizations

Theorems 4.2, 4.5 (sufficiency), and 4.9, with the exact polynomial rings on
the retained variables and genuine derived-Tor Betti components.
-/

noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

def RetainedLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent U, ∀ i : ℕ, i ≤ t →
    a.degree ≠ e+i → bettiNumber (k := k) (localFamily B U) a i = 0

theorem localLinearThrough_iff_retained (B : Family V) (U : Finset V) (e t : ℕ) :
    LocalLinearThrough (k := k) B U e t ↔ RetainedLinearThrough (k := k) B U e t := by
  constructor
  · intro h a i hi hoff
    have hs := Strands.extend_support_subset U a
    have hh := h (extendExponent U a) hs i hi (by simpa only [extendExponent_degree] using hoff)
    rw [betti_localize_supported B U _ hs i,restrict_extend] at hh
    exact hh
  · intro h a ha i hi hoff
    rw [betti_localize_supported B U a ha i]
    exact h (restrictExponent U a) i hi (by rwa [restrictExponent_degree_supported U a ha])

/-- The literal local-ring statement of the triangular tests. -/
def RetainedTriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localFamily B U) e ∧
      (0 < e → RetainedLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

theorem triangularTests_iff_retained (B : Family V) (d : ℕ) :
    TriangularTests (k := k) B d ↔ RetainedTriangularTests (k := k) B d := by
  simp only [TriangularTests,RetainedTriangularTests,
    localFamily_equigenerated_iff,localLinearThrough_iff_retained]

/-- Theorem 4.9 in the ambient supported-degree description. -/
theorem polymatroidal_iff_triangular_ambient {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ TriangularTests (k := k) B d := by
  refine ⟨fun hp => triangularTests_of_polymatroidal hp d,?_⟩
  intro ht
  by_contra hn
  have hl := locallyEquigenerated_of_triangularTests hB hd ht
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact triangularTests_exclude_low_nonlinear hB hd ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.9, with every Betti component computed over `k[U]`. -/
theorem polymatroidal_iff_triangular {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔ RetainedTriangularTests (k := k) B d :=
  (polymatroidal_iff_triangular_ambient hB hd hd2).trans (triangularTests_iff_retained B d)

/-- Theorem 4.5 with prior local equigeneration: codimension at most d−2
suffices, and the conclusion is the full exchange axiom. -/
theorem polymatroidal_iff_pure_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) (hl : LocallyEquigenerated B) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-2 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hd.antichain hl hn
  exact linearBand_excludes_low_nonlinear hB hd hl ht U e i a he hr hc hi hie hic ha hdeg hbetti

/-- Theorem 4.5 without prior local equigeneration: codimension at most d−1
forces both purity and the complete polymatroid exchange property. -/
theorem polymatroidal_iff_localization_band {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hd2 : 2 ≤ d) :
    IsPolymatroidal B ↔
      ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
        HasLinearResolution (monomialLocalization k (monomialIdeal k B) U) := by
  refine ⟨fun hp U _ _ => polymatroidal_local_linearResolutions hp U,?_⟩
  intro ht
  have hl := locallyEquigenerated_of_linearBand hB hd ht
  exact (polymatroidal_iff_pure_localization_band hB hd hd2 hl).mpr
    (fun U hc hk => ht U hc (by omega))

def DegreeBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (e-1))

def DegreeDimensionBoundedTests (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ e, Equigenerated (localFamily B U) e ∧
    (0 < e → RetainedLinearThrough (k := k) B U e (min (e-1) (U.card-1)))

theorem degreeBoundedTests_of_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hp : IsPolymatroidal B) : DegreeBoundedTests (k := k) B := by
  intro U
  have he := localFamily_equigenerated hp U
  refine ⟨lowerRank B U,he,?_⟩
  intro _
  apply (localLinearThrough_iff_retained B U _ _).mp
  exact localLinearThrough_of_linearResolution hB U
    (localFamily_equigenerated_iff.mp he) (polymatroidal_local_linearResolutions hp U) _

theorem degreeDimensionBoundedTests_of_degreeBoundedTests {B : Family V}
    (ht : DegreeBoundedTests (k := k) B) : DegreeDimensionBoundedTests (k := k) B := by
  intro U
  obtain ⟨e,he,hlinear⟩ := ht U
  exact ⟨e,he,fun hp a i hi hoff => hlinear hp a i (hi.trans (min_le_left _ _)) hoff⟩

/-- Theorem 4.2, including the smaller equivalent depth
`min {e_U−1, |U|−1}`. No original equigeneration hypothesis is added. -/
theorem polymatroidal_iff_degree_dimension_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeDimensionBoundedTests (k := k) B := by
  refine ⟨fun hp => degreeDimensionBoundedTests_of_degreeBoundedTests
    (degreeBoundedTests_of_polymatroidal hB hp),?_⟩
  intro ht
  have hl : LocallyEquigenerated B := by
    intro U
    obtain ⟨e,he,_⟩ := ht U
    exact ⟨e,localFamily_equigenerated_iff.mp he⟩
  by_contra hn
  obtain ⟨U,e,i,a,he,hr,hc,hi,hie,hic,ha,hdeg,hbetti⟩ :=
    exists_low_nonlinear_localization (k := k) hB hanti hl hn
  obtain ⟨f,hf,hlinear⟩ := ht U
  have hf' := localFamily_equigenerated_iff.mp hf
  obtain ⟨b,hb⟩ := localize_nonempty hB U
  have hef : e = f := (he b hb).symm.trans (hf' b hb)
  subst f
  have hvan := (localLinearThrough_iff_retained B U e _).mpr (hlinear (by omega))
  exact hbetti (hvan a ha i (le_min hie hic) (by omega))

/-- Theorem 4.2 with exactly the displayed degree cutoff `e_U−1`. -/
theorem polymatroidal_iff_degree_tests {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) : IsPolymatroidal B ↔ DegreeBoundedTests (k := k) B :=
  ⟨degreeBoundedTests_of_polymatroidal hB,fun ht =>
    (polymatroidal_iff_degree_dimension_tests hB hanti).mpr
      (degreeDimensionBoundedTests_of_degreeBoundedTests ht)⟩

end Characterizations
