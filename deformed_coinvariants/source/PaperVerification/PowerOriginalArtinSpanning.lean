module

public import PaperVerification.PowerUniversalSlope
public import PaperVerification.PowerHilbertSeries
public import PaperVerification.PowerTheoremOneOneSufficiency

/-!
# What literal Artin spanning forces at an arbitrary original slope

Homogeneous projection of the actual image span makes every degree a quotient
of the corresponding Artin degree space. Thus global Artin spanning bounds
each degree by the exact Artin degree-fiber cardinality. The unconditional
original-family Hom lower bound then forces equality and an actual degreewise
representation equivalence, even at a resonant slope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Module

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

abbrev ArtinDegreeIndex (n m d : ℕ) := {a : ArtinIndex n m // a.val.degree=d}

def artinDegreeSpace (K : Type*) [Field K] (n m d : ℕ) :
    Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun a : ArtinDegreeIndex n m d => monomial a.val.val (1 : K))

def artinDegreeBasis (K : Type*) [Field K] (n m d : ℕ) :
    Basis (ArtinDegreeIndex n m d) K (artinDegreeSpace K n m d) :=
  Basis.span ((artinMonomials_linearIndependent (K := K) (n := n) m).comp
    (fun a : ArtinDegreeIndex n m d => a.val) Subtype.val_injective)

instance artinDegreeSpace_finite (m d : ℕ) : Module.Finite K (artinDegreeSpace K n m d) :=
  Module.Finite.of_basis (artinDegreeBasis K n m d)

theorem artinDegreeSpace_finrank (m d : ℕ) :
    Module.finrank K (artinDegreeSpace K n m d) = Fintype.card (ArtinDegreeIndex n m d) :=
  Module.finrank_eq_card_basis (artinDegreeBasis K n m d)

theorem artinDegreeSpace_le_homogeneous (m d : ℕ) :
    artinDegreeSpace K n m d ≤ homogeneousSubmodule (Fin n) K d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact isHomogeneous_monomial (1 : K) a.property

theorem homogeneousComponent_artinSpan_mem (m d : ℕ)
    {p : MvPolynomial (Fin n) K} (hp : p ∈ artinSpan K n m) :
    homogeneousComponent d p ∈ artinDegreeSpace K n m d := by
  rw [artinSpan_eq_span_range] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,rfl⟩ := hp
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial (1 : K) rfl)]
    split_ifs with ha
    · exact Submodule.subset_span ⟨⟨a,ha.symm⟩,rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (artinDegreeSpace K n m d).zero_mem
  | add p q hp hq ihp ihq =>
    simpa only [map_add] using (artinDegreeSpace K n m d).add_mem ihp ihq
  | smul a p hp ih =>
    simpa only [map_smul] using (artinDegreeSpace K n m d).smul_mem a ih

theorem homogeneousComponent_mem_originalTailHit
    (c : Fin n → K) (lam : K) (m d : ℕ)
    {p : MvPolynomial (Fin n) K} (hp : p ∈ originalTailHit c lam m) :
    homogeneousComponent d p ∈ originalTailHit c lam m := by
  obtain ⟨u,hu⟩ := original_projection_mem_degree_range c lam m d hp
  have h := originalDegreePolynomialMap_mem_hit c lam m d u
  rw [hu] at h
  simpa only [shiftedProjection,Nat.zero_le,ite_true,Nat.sub_zero] using h

theorem original_mkQ_homogeneousComponent_eq_of_mkQ_eq
    (c : Fin n → K) (lam : K) (m d : ℕ) (p q : MvPolynomial (Fin n) K)
    (he : (originalTailHit c lam m).mkQ p = (originalTailHit c lam m).mkQ q) :
    (originalTailHit c lam m).mkQ (homogeneousComponent d p) =
      (originalTailHit c lam m).mkQ (homogeneousComponent d q) := by
  have hdiff : p-q ∈ originalTailHit c lam m := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (originalTailHit c lam m).mkQ (p-q) = 0
    rw [map_sub,he,sub_self]
  have hproj := homogeneousComponent_mem_originalTailHit c lam m d hdiff
  have hz := (Submodule.Quotient.mk_eq_zero _).mpr hproj
  change (originalTailHit c lam m).mkQ (homogeneousComponent d (p-q)) = 0 at hz
  rw [map_sub,map_sub] at hz
  exact sub_eq_zero.mp hz

def originalArtinDegreeMap (c : Fin n → K) (lam : K) (m d : ℕ) :
    artinDegreeSpace K n m d →ₗ[K] originalTailQuotientDegree c lam m d :=
  (((originalTailHit c lam m).mkQ).comp (artinDegreeSpace K n m d).subtype).codRestrict _
    (fun p => ⟨p,artinDegreeSpace_le_homogeneous m d p.property,rfl⟩)

theorem originalArtinDegreeMap_surjective_of_span
    (c : Fin n → K) (lam : K) (m d : ℕ)
    (hspan : (artinSpan K n m).map (originalTailHit c lam m).mkQ = ⊤) :
    Function.Surjective (originalArtinDegreeMap c lam m d) := by
  intro z
  obtain ⟨p,hp,hpz⟩ := z.property
  have hz : (z : MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) ∈
      (artinSpan K n m).map (originalTailHit c lam m).mkQ := by
    rw [hspan]
    trivial
  obtain ⟨q,hq,hqz⟩ := hz
  refine ⟨⟨homogeneousComponent d q,homogeneousComponent_artinSpan_mem m d hq⟩,?_⟩
  apply Subtype.ext
  change (originalTailHit c lam m).mkQ (homogeneousComponent d q) = z.val
  have he := original_mkQ_homogeneousComponent_eq_of_mkQ_eq c lam m d q p (hqz.trans hpz.symm)
  rw [homogeneousComponent_eq_self hp] at he
  exact he.trans hpz

theorem original_degree_finrank_le_artin_card_of_span
    (c : Fin n → K) (lam : K) (m d : ℕ)
    (hspan : (artinSpan K n m).map (originalTailHit c lam m).mkQ = ⊤) :
    Module.finrank K (originalTailQuotientDegree c lam m d) ≤
      Fintype.card (ArtinDegreeIndex n m d) := by
  rw [← artinDegreeSpace_finrank (K := K) (n := n) m d]
  exact LinearMap.finrank_le_finrank_of_surjective
    (originalArtinDegreeMap_surjective_of_span c lam m d hspan)

theorem complete_degree_finrank_eq_artin_card [CharZero K]
    (m d : ℕ) (hm : 0 < m) (G : Subgroup (Equiv.Perm (Fin n))) :
    Module.finrank K (ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) =
      Fintype.card (ArtinDegreeIndex n m d) := by
  rw [complete_degree_finrank_eq_tail (fun _ : Fin n => (1 : K)) 0 m d hm
    (constant_nonresonant_zero m) G (fun _ _ => rfl)]
  exact tailQuotientDegree_finrank_eq_artin_card (fun _ => 1) 0 m hm
    (constant_nonresonant_zero m) d

theorem original_degree_complete_equiv_of_artin_span [CharZero K]
    (lam : K) (m d : ℕ) (hm : 0 < m)
    (hspan : (artinSpan K n m).map
      (originalTailHit (fun _ : Fin n => (1 : K)) lam m).mkQ = ⊤)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Nonempty ((originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
      lam m (fun _ _ => rfl) d).Equiv (completeHomogeneousDegreeRepresentation G m d)) := by
  let ρ := completeHomogeneousDegreeRepresentation (K := K) G m d
  let σ := originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
    lam m (fun _ _ => rfl) d
  have hhom : ∀ r : ℕ, ∀ τ : Representation K G (Fin r → K),
      Module.finrank K (IntertwiningMap τ ρ) ≤ Module.finrank K (IntertwiningMap τ σ) :=
    fun r τ => constant_complete_intertwiner_finrank_le_original lam m d hm G τ
  have hlo := RepresentationHomComparison.finrank_le_of_coordinate_hom_tests ρ σ hhom
  have hhi := original_degree_finrank_le_artin_card_of_span (fun _ => (1 : K)) lam m d hspan
  rw [← complete_degree_finrank_eq_artin_card (K := K) m d hm G] at hhi
  letI : NeZero (Nat.card G : K) :=
    ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩
  obtain ⟨e⟩ := RepresentationHomComparison.nonempty_equiv_of_coordinate_hom_le_of_finrank_eq
    ρ σ hhom (le_antisymm hlo hhi)
  exact ⟨e.symm⟩

/-- Literal degreewise complete-to-elementary coinvariant identification. -/
def completeToCoinvariantDegreeRepresentation
    (G : Subgroup (Equiv.Perm (Fin n))) (d : ℕ) :
    (completeHomogeneousDegreeRepresentation (K := K) G 1 d).Equiv
      (ordinaryQuotientDegreeRepresentation G (elementaryCoinvariantFamily K n)
        (elementaryCoinvariantFamily_invariant G) d) := by
  let e := completeToCoinvariantRepresentation (K := K) G
  have he_apply (x : MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n 1) :
      e x = completeToCoinvariant (K := K) (n := n) x := rfl
  let ed : ordinaryQuotientDegree (completeHomogeneousFamily K n 1) d ≃ₗ[K]
      ordinaryCoinvariantDegree K n d :=
    { toFun x := ⟨e x,by
        rw [he_apply]
        exact (completeToCoinvariant_degree_iff (K := K) (n := n) d x.val).mp x.property⟩
      invFun y := ⟨e.symm y,(completeToCoinvariant_degree_iff (K := K) (n := n) d (e.symm y)).mpr (by
        rw [← he_apply, e.apply_symm_apply]
        exact y.property)⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x)
      right_inv y := Subtype.ext (e.apply_symm_apply y)
      map_add' x y := Subtype.ext (e.map_add x y)
      map_smul' a x := Subtype.ext (e.map_smul a x) }
  refine Representation.Equiv.mk ed ?_
  intro g
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change e (completeHomogeneousAction G 1 g x.val) =
    ordinaryCoinvariantAction G g (e x.val)
  simpa only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply,
    Representation.Equiv.coe_toIntertwiningMap] using
    LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x

/-- This is the consequence needed for the contradiction in Theorem 1.1:
Artin spanning alone forces the ordinary coinvariant representation in every
degree, for every parameter. No nonresonance premise is present. -/
theorem original_degree_coinvariant_equiv_of_artin_span [CharZero K]
    (lam : K) (d : ℕ)
    (hspan : (artinSpan K n 1).map
      (originalTailHit (fun _ : Fin n => (1 : K)) lam 1).mkQ = ⊤)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Nonempty ((originalTailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K))
      lam 1 (fun _ _ => rfl) d).Equiv
      (ordinaryQuotientDegreeRepresentation G (elementaryCoinvariantFamily K n)
        (elementaryCoinvariantFamily_invariant G) d)) := by
  obtain ⟨e⟩ := original_degree_complete_equiv_of_artin_span lam 1 d Nat.zero_lt_one hspan G
  exact ⟨e.trans (completeToCoinvariantDegreeRepresentation G d)⟩

end PaperVerification.PowerOperators
