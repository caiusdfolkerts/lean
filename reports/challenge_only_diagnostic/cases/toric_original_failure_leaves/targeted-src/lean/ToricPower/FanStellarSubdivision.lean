module

public import ToricPower.ConeBoundary

/-!
# Stellar subdivision of a finite rational fan

This constructs the actual fan obtained by adding an integral ray. It
retains precisely the old cones not containing the new point and cones
off their appropriate faces. Intersections and support are proved from
the original geometric fan axioms. The construction does not assume
that the old fan is simplicial.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) {p : V}
  {σ τ υ σ' τ' : PointedCone ℝ V}

theorem rayJoin_inter_old (hσ : σ ∈ fan.cones) (hτ : τ ∈ fan.cones)
    (hυ : υ ∈ fan.cones) (hτσ : τ ≤ σ) (hpσ : p ∈ σ) :
    rayJoin p τ ⊓ υ =
      if p ∈ υ then rayJoin p (τ ⊓ υ) else τ ⊓ υ := by
  have restrict : rayJoin p τ ⊓ υ = rayJoin p τ ⊓ (σ ⊓ υ) := by
    apply le_antisymm
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans (rayJoin_le hpσ hτσ)) inf_le_right)
    · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have base : τ ⊓ (σ ⊓ υ) = τ ⊓ υ := by
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hτσ) inf_le_right)
  rw [restrict]
  split_ifs with hpυ
  · rw [rayJoin_inf_face_of_mem hτσ (fan.inf_isFaceOf_left hσ hυ) ⟨hpσ, hpυ⟩, base]
  · rw [rayJoin_inf_face hpσ hτσ (fan.inf_isFaceOf_left hσ hυ)
      (fun h => hpυ h.2), base]

theorem rayJoin_inter_rayJoin (hσ : σ ∈ fan.cones) (hτ : τ ∈ fan.cones)
    (hσ' : σ' ∈ fan.cones) (hτ' : τ' ∈ fan.cones)
    (hτσ : τ ≤ σ) (hτ'σ' : τ' ≤ σ')
    (hpσ : p ∈ σ) (hpσ' : p ∈ σ') (hpτ : p ∉ τ) (hpτ' : p ∉ τ') :
    rayJoin p τ ⊓ rayJoin p τ' = rayJoin p (τ ⊓ τ') := by
  have restrict : rayJoin p τ ⊓ rayJoin p τ' =
      (rayJoin p τ ⊓ σ') ⊓ (rayJoin p τ' ⊓ σ) := by
    apply le_antisymm
    · exact le_inf
        (le_inf inf_le_left (inf_le_right.trans (rayJoin_le hpσ' hτ'σ')))
        (le_inf inf_le_right (inf_le_left.trans (rayJoin_le hpσ hτσ)))
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  rw [restrict, rayJoin_inter_old fan hσ hτ hσ' hτσ hpσ,
    rayJoin_inter_old fan hσ' hτ' hσ hτ'σ' hpσ', if_pos hpσ', if_pos hpσ]
  have faceLeft : (τ ⊓ σ').IsFaceOf (σ ⊓ σ') :=
    (fan.isFaceOf_of_le hσ hτ hτσ).inf (PointedCone.IsFaceOf.refl σ')
  have faceRight : (τ' ⊓ σ).IsFaceOf (σ ⊓ σ') := by
    simpa only [inf_comm σ' σ] using
      (fan.isFaceOf_of_le hσ' hτ' hτ'σ').inf (PointedCone.IsFaceOf.refl σ)
  rw [rayJoin_inf (C := σ ⊓ σ') ⟨hpσ, hpσ'⟩ faceLeft faceRight
    (fun h => hpτ h.1) (fun h => hpτ' h.1) le_rfl le_rfl]
  congr 1
  apply le_antisymm
  · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  · exact le_inf (le_inf inf_le_left (inf_le_right.trans hτ'σ'))
      (le_inf inf_le_right (inf_le_left.trans hτσ))

/-- Old cones avoiding the point, and cones on their boundary faces. -/
def stellarGenerators (p : V) : Set (PointedCone ℝ V) :=
  {σ ∈ fan.cones | p ∉ σ} ∪
    rayJoin p '' {τ ∈ fan.cones | p ∉ τ ∧ ∃ σ ∈ fan.cones, p ∈ σ ∧ τ ≤ σ}

theorem stellarGenerators_finite (p : V) : (stellarGenerators fan p).Finite := by
  exact (fan.finite_cones.subset fun _ h => h.1).union
    ((fan.finite_cones.subset fun _ h => h.1).image (rayJoin p))

theorem stellarGenerators_refines {S : PointedCone ℝ V}
    (member : S ∈ stellarGenerators fan p) : ∃ σ ∈ fan.cones, S ≤ σ := by
  rcases member with h | ⟨τ, ⟨hτ, _, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · exact ⟨S, h.1, le_rfl⟩
  · exact ⟨σ, hσ, rayJoin_le hpσ hτσ⟩

theorem stellarGenerators_toric (q : N) {S : PointedCone ℝ V}
    (member : S ∈ stellarGenerators fan (i q)) : IsToricCone i S := by
  rcases member with h | ⟨τ, ⟨hτ, _, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · exact fan.isToricCone h.1
  · exact rayJoin_isToricCone (fan.isToricCone hσ) q hpσ (fan.isToricCone hτ) hτσ

theorem stellarGenerators_pairwise {S T : PointedCone ℝ V}
    (hS : S ∈ stellarGenerators fan p) (hT : T ∈ stellarGenerators fan p) :
    (S ⊓ T).IsFaceOf S := by
  rcases hS with ⟨hS, hpS⟩ | ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · rcases hT with ⟨hT, hpT⟩ | ⟨υ, ⟨hυ, hpυ, σ, hσ, hpσ, hυσ⟩, rfl⟩
    · exact fan.inf_isFaceOf_left hS hT
    · rw [inf_comm S, rayJoin_inter_old fan hσ hυ hS hυσ hpσ, if_neg hpS]
      exact fan.inf_isFaceOf_right hυ hS
  · rcases hT with ⟨hT, hpT⟩ | ⟨τ', ⟨hτ', hpτ', σ', hσ', hpσ', hτ'σ'⟩, rfl⟩
    · rw [rayJoin_inter_old fan hσ hτ hT hτσ hpσ, if_neg hpT]
      exact (fan.inf_isFaceOf_left hτ hT).trans
        (base_isFaceOf_rayJoin hpσ (fan.isFaceOf_of_le hσ hτ hτσ))
    · rw [rayJoin_inter_rayJoin fan hσ hτ hσ' hτ' hτσ hτ'σ' hpσ hpσ' hpτ hpτ']
      exact rayJoin_isFaceOf hpσ (fan.isFaceOf_of_le hσ hτ hτσ) hpτ le_rfl
        (fan.inf_isFaceOf_left hτ hτ')

/-- The actual finite rational stellar subdivision. -/
def stellarFan (q : N) : Fan i :=
  Fan.ofCones fan.lattice (stellarGenerators fan (i q))
    (stellarGenerators_finite fan (i q)) (fun {_} h => stellarGenerators_toric fan q h)
    (fun {_ _} hS hT => stellarGenerators_pairwise fan hS hT)

theorem stellarFan_mem_faces (q : N) {S : PointedCone ℝ V} :
    S ∈ (stellarFan fan q).cones ↔
      ∃ T ∈ stellarGenerators fan (i q), S.IsFaceOf T := by
  rw [stellarFan, Fan.mem_ofCones_cones]

theorem stellarFan_old_mem (q : N) (hσ : σ ∈ fan.cones) (hpσ : i q ∉ σ) :
    σ ∈ (stellarFan fan q).cones :=
  (stellarFan_mem_faces fan q).mpr ⟨σ, Or.inl ⟨hσ, hpσ⟩, PointedCone.IsFaceOf.refl σ⟩

theorem stellarFan_rayJoin_mem (q : N) (hτ : τ ∈ fan.cones) (hpτ : i q ∉ τ)
    (hσ : σ ∈ fan.cones) (hpσ : i q ∈ σ) (hτσ : τ ≤ σ) :
    rayJoin (i q) τ ∈ (stellarFan fan q).cones :=
  (stellarFan_mem_faces fan q).mpr
    ⟨rayJoin (i q) τ, Or.inr ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩,
      PointedCone.IsFaceOf.refl _⟩

/-- Every new cone still lies in an original cone. -/
theorem stellarFan_refines (q : N) {S : PointedCone ℝ V}
    (member : S ∈ (stellarFan fan q).cones) : ∃ σ ∈ fan.cones, S ≤ σ := by
  obtain ⟨T, hT, face⟩ := (stellarFan_mem_faces fan q).mp member
  obtain ⟨σ, hσ, hTσ⟩ := stellarGenerators_refines fan hT
  exact ⟨σ, hσ, face.le.trans hTσ⟩

/-- The new fan has exactly the old support. -/
theorem stellarFan_support (q : N) (nonzero : i q ≠ 0) :
    (stellarFan fan q).support = fan.support := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨S, member, hx⟩ := (Fan.mem_support _).mp hx
    obtain ⟨σ, hσ, hSσ⟩ := stellarFan_refines fan q member
    exact (Fan.mem_support _).mpr ⟨σ, hσ, hSσ hx⟩
  · intro x hx
    obtain ⟨σ, hσ, hx⟩ := (Fan.mem_support _).mp hx
    by_cases hpσ : i q ∈ σ
    · obtain ⟨F, face, hpF, hxF⟩ := rationalCone_boundary_decomposition
        fan.lattice (fan.isToricCone hσ) hpσ nonzero hx
      exact (Fan.mem_support _).mpr ⟨rayJoin (i q) F,
        stellarFan_rayJoin_mem fan q (fan.mem_of_isFaceOf hσ face) hpF hσ hpσ face.le, hxF⟩
    · exact (Fan.mem_support _).mpr ⟨σ, stellarFan_old_mem fan q hσ hpσ, hx⟩

/-- No extra cones are hidden by the face closure in `Fan.ofCones`:
every cone is an unchanged old cone or a cone on an actual old face. -/
theorem stellarFan_mem_iff (q : N) {S : PointedCone ℝ V} :
    S ∈ (stellarFan fan q).cones ↔ S ∈ stellarGenerators fan (i q) := by
  rw [stellarFan_mem_faces]
  constructor
  · rintro ⟨T, hT, face⟩
    rcases hT with ⟨hT, hpT⟩ | ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩
    · exact Or.inl ⟨fan.mem_of_isFaceOf hT face, fun hpS => hpT (face.le hpS)⟩
    · obtain ⟨baseFace, old | new⟩ := rayJoin_face_classification face
      · exact Or.inl ⟨old ▸ fan.mem_of_isFaceOf hτ baseFace,
          fun hpS => hpτ ((congrArg (fun K : PointedCone ℝ V => i q ∈ K) old).mp hpS).2⟩
      · exact Or.inr ⟨S ⊓ τ,
          ⟨fan.mem_of_isFaceOf hτ baseFace, fun h => hpτ h.2,
            σ, hσ, hpσ, inf_le_right.trans hτσ⟩, new.symm⟩
  · intro member
    exact ⟨S, member, PointedCone.IsFaceOf.refl S⟩

end ToricPower.FanSubdivision
end
