import Gluck.Forward.Discrete.CyclicComponents

/-!
# Finite circle contact sets

Generic finite bookkeeping for the vertices lying on a metric sphere.  The
results here are independent of Dahlberg's Euclidean comparison geometry and
can be reused by both the containing-circle and interior-missing-circle
arguments.
-/

namespace Gluck.Forward

universe u v

/-- The finite set of indices whose vertices lie on the sphere of centre `O`
and radius `R`. -/
noncomputable def circleContactSet {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    (vertices : ι → X) (O : X) (R : ℝ) : Finset ι :=
  Finset.univ.filter fun i => dist O (vertices i) = R

@[simp]
theorem mem_circleContactSet {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {i : ι} :
    i ∈ circleContactSet vertices O R ↔ dist O (vertices i) = R := by
  classical
  simp [circleContactSet]

/-- A named contact makes the finite contact set nonempty. -/
theorem circleContactSet_nonempty_of_contact {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {i : ι}
    (hi : dist O (vertices i) = R) :
    (circleContactSet vertices O R).Nonempty := by
  exact ⟨i, mem_circleContactSet.mpr hi⟩

@[simp]
theorem circleContactSet_nonempty_iff {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} :
    (circleContactSet vertices O R).Nonempty ↔
      ∃ i, dist O (vertices i) = R := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, mem_circleContactSet.mp hi⟩
  · rintro ⟨i, hi⟩
    exact circleContactSet_nonempty_of_contact hi

/-- Contact-set inclusion is pointwise implication of boundary incidence. -/
theorem circleContactSet_subset_iff
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ} :
    circleContactSet vertices O₁ R₁ ⊆ circleContactSet vertices O₂ R₂ ↔
      ∀ i, dist O₁ (vertices i) = R₁ → dist O₂ (vertices i) = R₂ := by
  constructor
  · intro hsubset i hi
    exact mem_circleContactSet.mp (hsubset (mem_circleContactSet.mpr hi))
  · intro himp i hi
    exact mem_circleContactSet.mpr (himp i (mem_circleContactSet.mp hi))

/-- A contact-set inclusion is strict as soon as one contact of the larger
circle is not a contact of the smaller circle. -/
theorem circleContactSet_ssubset_of_subset_of_contact_of_not_contact
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {Osmall Olarge : X} {Rsmall Rlarge : ℝ} {i : ι}
    (hsubset : circleContactSet vertices Osmall Rsmall ⊆
      circleContactSet vertices Olarge Rlarge)
    (hilarge : dist Olarge (vertices i) = Rlarge)
    (hismall : dist Osmall (vertices i) ≠ Rsmall) :
    circleContactSet vertices Osmall Rsmall ⊂
      circleContactSet vertices Olarge Rlarge := by
  rw [Finset.ssubset_iff_of_subset hsubset]
  exact ⟨i, mem_circleContactSet.mpr hilarge,
    fun hi => hismall (mem_circleContactSet.mp hi)⟩

/-- A contained contact set strictly shrinks when one old contact becomes a
strictly interior vertex of the new circle. -/
theorem circleContactSet_ssubset_of_subset_of_contact_of_strictInterior
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {Onew Oold : X} {Rnew Rold : ℝ} {i : ι}
    (hsubset : circleContactSet vertices Onew Rnew ⊆
      circleContactSet vertices Oold Rold)
    (hiold : dist Oold (vertices i) = Rold)
    (hinew : dist Onew (vertices i) < Rnew) :
    circleContactSet vertices Onew Rnew ⊂
      circleContactSet vertices Oold Rold := by
  exact circleContactSet_ssubset_of_subset_of_contact_of_not_contact
    hsubset hiold (ne_of_lt hinew)

/-- The strict contact-set shrink above strictly decreases cardinality. -/
theorem circleContactSet_card_lt_of_subset_of_contact_of_strictInterior
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {Onew Oold : X} {Rnew Rold : ℝ} {i : ι}
    (hsubset : circleContactSet vertices Onew Rnew ⊆
      circleContactSet vertices Oold Rold)
    (hiold : dist Oold (vertices i) = Rold)
    (hinew : dist Onew (vertices i) < Rnew) :
    (circleContactSet vertices Onew Rnew).card <
      (circleContactSet vertices Oold Rold).card := by
  exact Gluck.strictSubset_card_lt
    (circleContactSet_ssubset_of_subset_of_contact_of_strictInterior
      hsubset hiold hinew)

/-- A strictly interior vertex witnesses that not every index is a contact. -/
theorem circleContactSet_ssubset_univ_of_strictInterior
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {i : ι}
    (hi : dist O (vertices i) < R) :
    circleContactSet vertices O R ⊂ (Finset.univ : Finset ι) := by
  rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
  exact ⟨i, Finset.mem_univ _,
    fun himem => (ne_of_lt hi) (mem_circleContactSet.mp himem)⟩

/-- A contact set with a strictly interior vertex has fewer elements than the
whole finite index type. -/
theorem card_circleContactSet_lt_card_univ_of_strictInterior
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {i : ι}
    (hi : dist O (vertices i) < R) :
    (circleContactSet vertices O R).card <
      (Finset.univ : Finset ι).card := by
  exact Gluck.strictSubset_card_lt
    (circleContactSet_ssubset_univ_of_strictInterior hi)

/-- Two finite contact sets are equal exactly when their boundary predicates
agree at every vertex. -/
theorem circleContactSet_eq_iff {ι : Type u} [Fintype ι]
    {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ} :
    circleContactSet vertices O₁ R₁ = circleContactSet vertices O₂ R₂ ↔
      ∀ i, dist O₁ (vertices i) = R₁ ↔ dist O₂ (vertices i) = R₂ := by
  constructor
  · intro hsets i
    rw [← mem_circleContactSet, ← mem_circleContactSet, hsets]
  · intro hpred
    ext i
    simpa only [mem_circleContactSet] using hpred i

/-- Equal centre-radius data have equal finite contact sets. -/
theorem circleContactSet_eq_of_circleData_eq
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ}
    (hdata : (O₁, R₁) = (O₂, R₂)) :
    circleContactSet vertices O₁ R₁ = circleContactSet vertices O₂ R₂ := by
  cases hdata
  rfl

/-- Distinct finite contact sets force distinct centre-radius data. -/
theorem circleData_ne_of_circleContactSet_ne
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ}
    (hsets : circleContactSet vertices O₁ R₁ ≠
      circleContactSet vertices O₂ R₂) :
    (O₁, R₁) ≠ (O₂, R₂) := by
  intro hdata
  exact hsets (circleContactSet_eq_of_circleData_eq hdata)

/-- A vertex contacting one circle but not the other distinguishes their
finite contact sets. -/
theorem circleContactSet_ne_of_contact_of_not_contact
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O₁ O₂ : X} {R₁ R₂ : ℝ} {i : ι}
    (hi₁ : dist O₁ (vertices i) = R₁)
    (hi₂ : dist O₂ (vertices i) ≠ R₂) :
    circleContactSet vertices O₁ R₁ ≠ circleContactSet vertices O₂ R₂ := by
  intro hsets
  apply hi₂
  exact mem_circleContactSet.mp
    (hsets ▸ mem_circleContactSet.mpr hi₁)

/-- A contact of one circle that is strictly inside another distinguishes the
two contact sets. -/
theorem circleContactSet_ne_of_contact_of_strictInterior
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {Ocontact Ointerior : X}
    {Rcontact Rinterior : ℝ} {i : ι}
    (hicontact : dist Ocontact (vertices i) = Rcontact)
    (hiinterior : dist Ointerior (vertices i) < Rinterior) :
    circleContactSet vertices Ocontact Rcontact ≠
      circleContactSet vertices Ointerior Rinterior := by
  exact circleContactSet_ne_of_contact_of_not_contact
    hicontact (ne_of_lt hiinterior)

/-- A contact of one circle that is strictly inside another also distinguishes
the centre-radius pairs themselves. -/
theorem circleData_ne_of_contact_of_strictInterior
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {Ocontact Ointerior : X}
    {Rcontact Rinterior : ℝ} {i : ι}
    (hicontact : dist Ocontact (vertices i) = Rcontact)
    (hiinterior : dist Ointerior (vertices i) < Rinterior) :
    (Ocontact, Rcontact) ≠ (Ointerior, Rinterior) := by
  intro hdata
  cases hdata
  exact (ne_of_lt hiinterior) hicontact

/-- Three pairwise-distinct named contacts give a contact set of cardinality at
least three. -/
theorem three_le_card_circleContactSet
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : dist O (vertices a) = R)
    (hb : dist O (vertices b) = R)
    (hc : dist O (vertices c) = R) :
    3 ≤ (circleContactSet vertices O R).card := by
  classical
  have hsub : ({a, b, c} : Finset ι) ⊆ circleContactSet vertices O R := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨mem_circleContactSet.mpr ha, mem_circleContactSet.mpr hb,
      mem_circleContactSet.mpr hc⟩
  have hcard : ({a, b, c} : Finset ι).card = 3 := by
    simp [hab, hac, hbc]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- A contact set of cardinality at least three contains a contact distinct
from any two prescribed indices. -/
theorem exists_circleContact_ne_two_of_three_le_card
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    {vertices : ι → X} {O : X} {R : ℝ} {a b : ι}
    (hthree : 3 ≤ (circleContactSet vertices O R).card) :
    ∃ c : ι, c ∈ circleContactSet vertices O R ∧ c ≠ a ∧ c ≠ b := by
  classical
  by_contra hnone
  push Not at hnone
  have hsub : circleContactSet vertices O R ⊆ {a, b} := by
    intro c hc
    by_cases hca : c = a
    · simp [hca]
    · simp [hnone c hc hca]
  have hcard := Finset.card_le_card hsub
  have hpairs : ({a, b} : Finset ι).card ≤ 2 := by
    have hle := Finset.card_insert_le a ({b} : Finset ι)
    simpa only [Finset.card_singleton, Nat.reduceAdd] using hle
  omega

/-- A strict-shrink process on finite index sets, started at a circle contact
set, reaches a terminal set within the initial number of contacts. -/
theorem exists_terminal_iterate_from_circleContactSet_of_strict_shrink
    {ι : Type u} [Fintype ι] {X : Type v} [PseudoMetricSpace X]
    (vertices : ι → X) (O : X) (R : ℝ)
    (step : Finset ι → Finset ι) (terminal : Finset ι → Prop)
    (hstep : ∀ A, ¬ terminal A → step A ⊂ A) :
    ∃ k : ℕ,
      k ≤ (circleContactSet vertices O R).card ∧
        terminal ((step^[k]) (circleContactSet vertices O R)) := by
  exact Gluck.exists_terminal_iterate_of_strict_shrink
    step terminal hstep (circleContactSet vertices O R)

end Gluck.Forward
