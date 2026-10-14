import Gluck.Discrete.Converse

/-!
# Four-vertex windows under monotone periodic collapse

Adjacent equal readings may share a collapsed index. Alternating strict
level signs prevent any two successive witnesses of a four-vertex window
from sharing one, including across the periodic seam.
-/

namespace Gluck.Discrete

/-- A monotone map of lifted indices that respects periods and readings
preserves the same strict four-vertex level. -/
theorem DFV.of_monotone_periodic_collapse
    {n m : ℕ} {κ : ZMod n → ℝ} {μ : ZMod m → ℝ} {c : ℝ}
    {r : ℕ → ℕ} (hr : Monotone r)
    (hperiod : ∀ i, r (i + n) = r i + m)
    (hreading : ∀ i, μ (r i : ZMod m) = κ (i : ZMod n))
    (hdfv : DFV κ c) : DFV μ c := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, h1, h2, h3, h4⟩ := hdfv
  have hm1 : c < μ (r i₁ : ZMod m) := by rwa [hreading]
  have hm2 : μ (r i₂ : ZMod m) < c := by rwa [hreading]
  have hm3 : c < μ (r i₃ : ZMod m) := by rwa [hreading]
  have hm4 : μ (r i₄ : ZMod m) < c := by rwa [hreading]
  have hr12 : r i₁ < r i₂ := by
    have hle := hr h12.le
    by_contra hnot
    have he : r i₁ = r i₂ := by omega
    rw [he] at hm1
    linarith
  have hr23 : r i₂ < r i₃ := by
    have hle := hr h23.le
    by_contra hnot
    have he : r i₂ = r i₃ := by omega
    rw [he] at hm2
    linarith
  have hr34 : r i₃ < r i₄ := by
    have hle := hr h34.le
    by_contra hnot
    have he : r i₃ = r i₄ := by omega
    rw [he] at hm3
    linarith
  have hr41 : r i₄ < r i₁ + m := by
    have hle : r i₄ ≤ r i₁ + m := by
      simpa [hperiod] using hr h41.le
    by_contra hnot
    have he : r i₄ = r i₁ + m := by omega
    rw [he] at hm4
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hm4
    linarith
  exact ⟨r i₁, r i₂, r i₃, r i₄, hr12, hr23, hr34, hr41, hm1, hm2, hm3, hm4⟩

/-- Four strict cyclically ordered witnesses require at least four entries. -/
theorem DFV.four_le_period {n : ℕ} {κ : ZMod n → ℝ} {c : ℝ}
    (hdfv : DFV κ c) : 4 ≤ n := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, _⟩ := hdfv
  omega

/-- The collapsed period remains large enough for the coherent converse. -/
theorem DFV.four_le_of_monotone_periodic_collapse
    {n m : ℕ} {κ : ZMod n → ℝ} {μ : ZMod m → ℝ} {c : ℝ}
    {r : ℕ → ℕ} (hr : Monotone r)
    (hperiod : ∀ i, r (i + n) = r i + m)
    (hreading : ∀ i, μ (r i : ZMod m) = κ (i : ZMod n))
    (hdfv : DFV κ c) : 4 ≤ m :=
  (hdfv.of_monotone_periodic_collapse hr hperiod hreading).four_le_period

end Gluck.Discrete
