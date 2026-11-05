module

public import Unimodular.Extensions

@[expose] public section

noncomputable section

namespace Unimodular

open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem pairing_sub_left {n : ℕ} (x y : Ambient n) (u : Lattice n) :
    pairing (x - y) u = pairing x u - pairing y u := by
  simp [pairing, sub_mul, Finset.sum_sub_distrib]

namespace SmoothReflexivePresentation

variable {n : ℕ} (P : SmoothReflexivePresentation n)

/-- Actual convex extreme subsets, including the empty face and the whole polytope.
The order is literal set inclusion inherited by the subtype. -/
abbrev GeometricFace := {E : Set (Ambient n) // Convex ℝ E ∧ IsExtreme ℝ P.carrier E}

instance : PartialOrder P.GeometricFace := inferInstanceAs
  (PartialOrder {E : Set (Ambient n) // Convex ℝ E ∧ IsExtreme ℝ P.carrier E})

/-- The intersection with the supporting hyperplanes indexed by `S`. -/
def normalIntersection (S : Set (Lattice n)) : Set (Ambient n) :=
  {x | x ∈ P.carrier ∧ ∀ u ∈ S, pairing x u = 1}

theorem normalIntersection_convex (S : Set (Lattice n)) :
    Convex ℝ (P.normalIntersection S) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  intro u hu
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hx.2 u hu, hy.2 u hu]
  simpa using hab

theorem normalIntersection_extreme (S : Set (Lattice n))
    (hS : S ⊆ (P.normals : Set (Lattice n))) :
    IsExtreme ℝ P.carrier (P.normalIntersection S) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hx, ?_⟩
  intro u hu
  have hxle := (P.mem_carrier_iff x).1 hx u (hS hu)
  have hyle := (P.mem_carrier_iff y).1 hy u (hS hu)
  have hh := congrArg (fun p => pairing p u) he
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hz.2 u hu] at hh
  nlinarith

/-- Normals whose hyperplanes contain the whole set. -/
def commonNormals (E : Set (Ambient n)) : Set (Lattice n) :=
  {u | u ∈ P.normals ∧ ∀ x ∈ E, pairing x u = 1}

/-- A convex subset of a polytope has a point with exactly its universally active
normal inequalities. Finiteness and midpoint averaging suffice; no relative-interior
or closed-face theorem is assumed. -/
theorem exists_common_active_point {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : E ⊆ P.carrier) (hne : E.Nonempty) :
    ∃ p ∈ E, ∀ u ∈ P.normals, pairing p u = 1 → ∀ x ∈ E, pairing x u = 1 := by
  have aux : ∀ s : Finset (Lattice n), s ⊆ P.normals →
      ∃ p ∈ E, ∀ u ∈ s, pairing p u = 1 → ∀ x ∈ E, pairing x u = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, hp, by simp⟩
    | @insert a s ha ih =>
      intro hs
      obtain ⟨p, hp, hpa⟩ := ih (fun u hu => hs (Finset.mem_insert_of_mem hu))
      have haN : a ∈ P.normals := hs (Finset.mem_insert_self _ _)
      by_cases hall : ∀ x ∈ E, pairing x a = 1
      · refine ⟨p, hp, ?_⟩
        intro u hu he
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact hall
        · exact hpa u hu he
      · push_neg at hall
        obtain ⟨q, hq, hqa⟩ := hall
        let r : Ambient n := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q
        have hr : r ∈ E := hE hp hq (by norm_num) (by norm_num) (by norm_num)
        refine ⟨r, hr, ?_⟩
        intro u hu he
        have huN := hs hu
        have hpu := (P.mem_carrier_iff p).1 (hEP hp) u huN
        have hqu := (P.mem_carrier_iff q).1 (hEP hq) u huN
        have he' : (1 / 2 : ℝ) * pairing p u + (1 / 2 : ℝ) * pairing q u = 1 := by
          simpa only [r, pairing_add_left, pairing_smul_left] using he
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exfalso
          apply hqa
          linarith
        · apply hpa u hu
          linarith
  exact aux P.normals (by intro u hu; exact hu)

/-- Every nonempty actual convex face is exactly the intersection of the facets
that contain it. The reverse inclusion is proved by extending a segment through
a common active point and applying the defining extreme-set property. -/
theorem face_eq_normalIntersection {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : IsExtreme ℝ P.carrier E) (hne : E.Nonempty) :
    E = P.normalIntersection (P.commonNormals E) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hEP.subset hx, fun u hu => hu.2 x hx⟩
  · rintro x ⟨hx, hxa⟩
    obtain ⟨p, hp, hpa⟩ := P.exists_common_active_point hE hEP.subset hne
    obtain ⟨t, ht, hstep⟩ := exists_pos_feasible_step P.normals
      (fun u => 1 - pairing p u) (fun u => pairing (p - x) u)
      (by
        intro u hu
        exact sub_nonneg.2 ((P.mem_carrier_iff p).1 (hEP.subset hp) u hu))
      (by
        intro u hu hzero
        have hpu : pairing p u = 1 := by linarith
        have hxu : pairing x u = 1 := hxa u ⟨hu, hpa u hu hpu⟩
        rw [pairing_sub_left, hpu, hxu]
        norm_num)
    let y : Ambient n := p + t • (p - x)
    have hy : y ∈ P.carrier := by
      apply (P.mem_carrier_iff y).2
      intro u hu
      dsimp [y]
      rw [pairing_add_left, pairing_smul_left]
      linarith [hstep u hu]
    apply hEP.left_mem_of_mem_openSegment hx hy hp
    have hden : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht hden, div_pos zero_lt_one hden,
      ?_, ?_⟩
    · field_simp <;> ring
    · ext i
      simp only [y, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp <;> ring

/-- An actual convex face is the convex hull of precisely the listed vertices it
contains. This proof uses the extreme-set endpoint condition, not an assumption
that the presentation has already enumerated a face lattice. -/
theorem face_eq_convexHull_vertices {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : IsExtreme ℝ P.carrier E) :
    E = convexHull ℝ (embed '' {v : Lattice n | v ∈ P.vertices ∧ embed v ∈ E}) := by
  let V : Set (Ambient n) := embed '' {v : Lattice n | v ∈ P.vertices ∧ embed v ∈ E}
  let F : Set (Ambient n) := convexHull ℝ V
  have hFE : F ⊆ E := convexHull_min (by rintro x ⟨v, hv, rfl⟩; exact hv.2) hE
  let T : Set (Ambient n) := {x | x ∈ P.carrier ∧ (x ∈ E → x ∈ F)}
  have hTc : Convex ℝ T := by
    rintro x ⟨hx, hxf⟩ y ⟨hy, hyf⟩ a b ha hb hab
    refine ⟨(convex_convexHull ℝ _) hx hy ha hb hab, ?_⟩
    intro hz
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hyf (by simpa [ha0, hb1] using hz)
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hxf (by simpa [hb0, ha1] using hz)
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hseg : a • x + b • y ∈ openSegment ℝ x y :=
      ⟨a, b, hapos, hbpos, hab, rfl⟩
    exact (convex_convexHull ℝ V)
      (hxf (hEP.left_mem_of_mem_openSegment hx hy hz hseg))
      (hyf (hEP.right_mem_of_mem_openSegment hx hy hz hseg)) ha hb hab
  have hPT : P.carrier ⊆ T := by
    apply convexHull_min _ hTc
    rintro x ⟨v, hv, rfl⟩
    refine ⟨P.vertex_mem ⟨v, hv⟩, ?_⟩
    intro he
    exact subset_convexHull ℝ V ⟨v, ⟨hv, he⟩, rfl⟩
  exact Set.Subset.antisymm (fun x hx => (hPT (hEP.subset hx)).2 hx) hFE

/-- Inclusion of actual faces is determined by their listed vertices. -/
theorem face_subset_iff_vertices (E F : P.GeometricFace) :
    E.val ⊆ F.val ↔ ∀ v ∈ P.vertices, embed v ∈ E.val → embed v ∈ F.val := by
  constructor
  · exact fun h v hv hx => h hx
  · intro h
    rw [P.face_eq_convexHull_vertices E.property.1 E.property.2]
    apply convexHull_min _ F.property.1
    rintro x ⟨v, hv, rfl⟩
    exact h v hv.1 hv.2

end SmoothReflexivePresentation

end Unimodular

end
