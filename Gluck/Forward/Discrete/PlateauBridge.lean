module

public import Gluck.Forward.Kernel
public import Gluck.Discrete.TabachnikovReduction

/-! # The two formal plateau-extremum vocabularies

Alternating plateau-aware extrema in Dahlberg's forward theorem yield the
strict level window and distinct plateau runs used in the converse theorem.
-/

@[expose] public section

namespace Gluck.Forward

variable {n : ℕ}

/-- A plateau minimum cannot occur inside the right half of a maximal plateau. -/
lemma not_localMin_on_right_max_plateau {κ : ZMod n → ℝ} {i : ZMod n} {r d : ℕ}
    (hd : d < r) (heq : ∀ m < r, κ (i + (m : ZMod n)) = κ i)
    (hdrop : κ (i + (r : ZMod n)) < κ i) :
    ¬ DiscreteLocalMin κ (i + (d : ZMod n)) := by
  rintro ⟨l, s, hl, hs, hn, hleft, hright, hlrise, hrise⟩
  have hdval := heq d hd
  by_cases hds : d + s < r
  · have he := heq (d + s) hds
    rw [Nat.cast_add, ← add_assoc] at he
    rw [he, hdval] at hrise
    exact (lt_irrefl _ hrise)
  · have hrs : r - d ≤ s := by omega
    rcases lt_or_eq_of_le hrs with hrs | hrs
    · have he := hright (r - d) hrs
      have hidx : i + (d : ZMod n) + ((r - d : ℕ) : ZMod n) = i + (r : ZMod n) := by
        rw [Nat.cast_sub hd.le]
        ring
      rw [hidx, hdval] at he
      exact (ne_of_lt hdrop) he
    · have hidx : i + (d : ZMod n) + (s : ZMod n) = i + (r : ZMod n) := by
        rw [← hrs, Nat.cast_sub hd.le]
        ring
      rw [hidx, hdval] at hrise
      exact (not_lt_of_gt hdrop) hrise

/-- A plateau minimum cannot occur inside the left half of a maximal plateau. -/
lemma not_localMin_on_left_max_plateau {κ : ZMod n → ℝ} {i : ZMod n} {l d : ℕ}
    (hd : d < l) (heq : ∀ m < l, κ (i - (m : ZMod n)) = κ i)
    (hdrop : κ (i - (l : ZMod n)) < κ i) :
    ¬ DiscreteLocalMin κ (i - (d : ZMod n)) := by
  intro hmin
  apply not_localMin_on_right_max_plateau (κ := fun j ↦ κ (-j)) (i := -i) hd
  · intro m hm
    simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using heq m hm
  · simpa only [neg_add_rev, neg_neg, sub_eq_add_neg, add_comm] using hdrop
  · convert discreteLocalMin_negIndex hmin using 1
    abel

/-- The lower of two separated plateau maxima and its own two exits give a strict level. -/
lemma alternatesAcrossLevel_of_lower_localMax {κ : ZMod n → ℝ} {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + n)
    (hmax : DiscreteLocalMax κ (a : ZMod n))
    (hminb : DiscreteLocalMin κ (b : ZMod n))
    (hmind : DiscreteLocalMin κ (d : ZMod n)) (hac : κ (a : ZMod n) ≤ κ (c : ZMod n)) :
    ∃ z, AlternatesAcrossLevel κ z := by
  obtain ⟨l, r, hl, hr, hlr, hleft, hright, hldrop, hrdrop⟩ := hmax
  have hrb : r ≤ b - a := by
    by_contra h
    have hidx : (a : ZMod n) + ((b - a : ℕ) : ZMod n) = (b : ZMod n) := by
      rw [Nat.cast_sub hab.le]
      ring
    exact not_localMin_on_right_max_plateau (d := b - a) (by omega) hright hrdrop
      (by simpa only [hidx] using hminb)
  have hld : l ≤ a + n - d := by
    by_contra h
    have hidx : (a : ZMod n) - ((a + n - d : ℕ) : ZMod n) = (d : ZMod n) := by
      rw [Nat.cast_sub hda.le, Nat.cast_add, ZMod.natCast_self]
      ring
    exact not_localMin_on_left_max_plateau (d := a + n - d) (by omega) hleft hldrop
      (by simpa only [hidx] using hmind)
  let m := max (κ ((a : ZMod n) - (l : ZMod n))) (κ ((a : ZMod n) + (r : ZMod n)))
  have hm : m < κ (a : ZMod n) := max_lt hldrop hrdrop
  refine ⟨(m + κ (a : ZMod n)) / 2, a, a + r, c, a + (n - l),
    by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · have hh := le_max_right (κ ((a : ZMod n) - (l : ZMod n)))
      (κ ((a : ZMod n) + (r : ZMod n)))
    rw [Nat.cast_add]
    change κ ((a : ZMod n) + (r : ZMod n)) ≤ m at hh
    linarith
  · have hh := le_max_left (κ ((a : ZMod n) - (l : ZMod n)))
      (κ ((a : ZMod n) + (r : ZMod n)))
    rw [Nat.cast_add, Nat.cast_sub (show l ≤ n by omega), ZMod.natCast_self, zero_sub]
    change κ ((a : ZMod n) - (l : ZMod n)) ≤ m at hh
    rw [← sub_eq_add_neg]
    linarith
  · linarith
  · linarith

/-- Dahlberg's alternating plateau extrema have a common strict separating level. -/
theorem DahlbergFourVertex.exists_alternatesAcrossLevel {κ : ZMod n → ℝ}
    (h : DahlbergFourVertex κ) : ∃ z, AlternatesAcrossLevel κ z := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hma, hmb, hmc, hmd⟩ := h
  rcases le_total (κ (a : ZMod n)) (κ (c : ZMod n)) with hac | hca
  · exact alternatesAcrossLevel_of_lower_localMax hab hbc hcd hda hma hmb hmd hac
  · apply alternatesAcrossLevel_of_lower_localMax hcd hda (Nat.add_lt_add_right hab n)
      (by omega) hmc hmd
    · simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using hmb
    · simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using hca

/-- The forward plateau conclusion gives the exact strict window used by the converse. -/
theorem DahlbergFourVertex.exists_dfv {κ : ZMod n → ℝ} (h : DahlbergFourVertex κ) :
    ∃ z, Gluck.Discrete.DFV κ z := by
  obtain ⟨z, a, b, c, d, hab, hbc, hcd, hda, hb, hd, ha, hc⟩ :=
    h.exists_alternatesAcrossLevel
  exact ⟨z, a, b, c, d, hab, hbc, hcd, hda, ha, hb, hc, hd⟩

/-- Both plateau encodings count distinct maximal runs, including repeated entries. -/
theorem DahlbergFourVertex.hasTwoPlateauMaxRuns_and_min [NeZero n] {κ : ZMod n → ℝ}
    (h : DahlbergFourVertex κ) :
    Gluck.Discrete.HasTwoPlateauMaxRuns κ ∧ Gluck.Discrete.HasTwoPlateauMinRuns κ := by
  obtain ⟨z, hz⟩ := h.exists_dfv
  exact hz.plateau_extrema

end Gluck.Forward
