/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck.Discrete.N6MonotoneResidue
public import Gluck.Discrete.N6PlateauPerturbation
public import Gluck.Statements

/-!
# Tabachnikov's Problem 2 as one named proposition

This file states the general positive discrete converse four-vertex theorem —
Tabachnikov's Problem 2 (arXiv:0710.5902) — as a single named `Prop`,
`TabachnikovProblem2 n`, and proves that it follows from three named stratum
hypotheses via an exhaustive plateau / zigzag / runs trichotomy.

This file realizes only `n = 4` (`tabachnikovProblem2_four`, which
eta-expands `discreteGluckConverse_R2_pos_four`). The stratum hypotheses
`ZigzagRealizes`, `RunsRealizes` and `PlateauRealizes` belong to an earlier
route and are not discharged here. The general theorem is proved by a
different argument, the four-active-edge anchor, in
`Gluck.Discrete.TabachnikovFourActive` (`tabachnikovProblem2_all`, every
`n ≥ 4`). `Gluck.Discrete.TabachnikovConverse` (`tabachnikov_converse`)
restates it with radii, convexity and coherence.

The final section identifies the hypothesis class with Dahlberg's: the
level form `DiscreteFourVertexPos` and the extremum form
`DiscreteFourVertexExtrema` (two distinct plateau maxima and two distinct
plateau minima) define the *same* class
(`discreteFourVertexPos_iff_extrema`), so `TabachnikovProblem2 n` is the
literature's problem and not a value-separated proxy for it.  Two distinct
plateau maxima already suffice: they produce a window level on their own
(`exists_dfv_of_two_plateauMaxRun`), which makes the minima half of
Dahlberg's conclusion a formal consequence of the maxima half
(`hasTwoPlateauMaxRuns_iff_hasTwoPlateauMinRuns`).  This closes a *statement*
gap only; the three stratum hypotheses themselves are not used by the proof.

-/

@[expose] public section

namespace Gluck.Discrete

variable {n : ℕ}

/-! ## The problem -/

/-- **Tabachnikov's Problem 2 at length `n`** (arXiv:0710.5902, Problem 2):
every positive cyclic curvature word of length `n` which is constant or admits
a strict four-vertex window at a positive level is realized by a simple
moderate-arc Euclidean `n`-gon with those signed curvatures.  Every `n ≥ 4` is
proved in `Gluck.Discrete.TabachnikovFourActive` (`tabachnikovProblem2_all`);
this file itself proves only `n = 4` (`tabachnikovProblem2_four`). -/
def TabachnikovProblem2 (n : ℕ) [NeZero n] : Prop :=
  ∀ κ : ZMod n → ℝ, DiscreteFourVertexPos κ → RealizesR2 κ

/-- **The problem is settled at `n = 4`**: exactly
`discreteGluckConverse_R2_pos_four`, eta-expanded.  This is what keeps the
reduction `tabachnikovProblem2_of_strata` non-vacuous. -/
theorem tabachnikovProblem2_four : TabachnikovProblem2 4 :=
  fun _ h => discreteGluckConverse_R2_pos_four h

/-! ## The strata -/

/-- **The runs stratum** (whole-run granularity): every positive word with no
adjacent equality, a positive-level four-vertex window, and at least one
non-extremal vertex — i.e. at least one strictly monotone run of length ≥ 2
(`exists_monotone_run_of_not_strictZigzag`) — is realizable.

**NOT discharged anywhere in this development; open research, owned
externally.**  The two live external routes are (a) the relative
two-dimensional trace degree `FC(4)` for the two-quadrilateral fibre product
with outgoing-socket propagation, and (b) a multi-edge (whole-run) carrier
certificate extending the four-gap carrier across a run.  The one-cut
selection route is **refuted**: the all-outer-heavy residue has outer sum
`O = a² + d²` increasing in every cut ratio, so componentwise minimal cuts
already give `O ≥ 1`, and the sharp witness is a monotone run of uniform ratio
`9/10` whose achievable cut menu is a singleton.  No cut-selection lemma is a
Lean target of this project. -/
def RunsRealizes (n : ℕ) [NeZero n] : Prop :=
  ∀ κ : ZMod n → ℝ, (∀ i, 0 < κ i) → (∀ i, κ i ≠ κ (i + 1)) →
    (∃ c > 0, DFV κ c) → ¬ StrictZigzag κ → RealizesR2 κ

/-- **The plateau stratum**: every positive word with a positive-level
four-vertex window and two adjacent equal prescribed curvatures is realizable.

**NOT discharged; open research, owned by nobody.**  The minimal witness is
`(1,1,2,1,1,2)` at level `3/2`: positive with a strict four-vertex window, yet
every adjacent-pair deletion leaves a four-word with two adjacent equal
entries, so it is outside the reach of literal zigzag deletion.  At `n = 6`,
`mem_closure_positive_dfv_ne_succ` puts every such profile in the closure of
the positive adjacent-unequal stratum with the same window.  The remaining
issue is analytic: realizability has not been shown closed when realizing
edge lengths can tend to zero. -/
def PlateauRealizes (n : ℕ) [NeZero n] : Prop :=
  ∀ κ : ZMod n → ℝ, (∀ i, 0 < κ i) → (∃ c > 0, DFV κ c) →
    (∃ i, κ i = κ (i + 1)) → RealizesR2 κ

/-! ## The trichotomy and the reduction -/

/-- **A non-extremal vertex is the interior of a monotone run**: in a cyclic
word with no adjacent equality which is not strictly zigzag, some vertex is
strictly between its two neighbours. -/
theorem exists_monotone_run_of_not_strictZigzag {κ : ZMod n → ℝ}
    (hne : ∀ i, κ i ≠ κ (i + 1)) (hnz : ¬ StrictZigzag κ) :
    ∃ i, (κ (i - 1) < κ i ∧ κ i < κ (i + 1)) ∨
      (κ (i + 1) < κ i ∧ κ i < κ (i - 1)) := by
  rw [strictZigzag_iff_forall_extremum, not_forall] at hnz
  obtain ⟨i, hi⟩ := hnz
  rw [IsStrictExtremum, not_or, IsStrictLocalMax, IsStrictLocalMin] at hi
  obtain ⟨hmax, hmin⟩ := hi
  have hprev : κ (i - 1) ≠ κ i := by
    have := hne (i - 1)
    rwa [sub_add_cancel] at this
  have hnext : κ i ≠ κ (i + 1) := hne i
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hprev with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hnext with h₂ | h₂
  · exact Or.inl ⟨h₁, h₂⟩
  · exact absurd ⟨h₁, h₂⟩ hmax
  · exact absurd ⟨h₁, h₂⟩ hmin
  · exact Or.inr ⟨h₂, h₁⟩

/-- **The three strata are exhaustive**: every cyclic word has an adjacent
equality, or is strictly zigzag, or has all adjacent values distinct and a
non-extremal vertex.  (The strata are also mutually exclusive, which is not
needed downstream.) -/
theorem strata_exhaustive (κ : ZMod n → ℝ) :
    (∃ i, κ i = κ (i + 1)) ∨ StrictZigzag κ ∨
      ((∀ i, κ i ≠ κ (i + 1)) ∧ ¬ StrictZigzag κ) := by
  by_cases heq : ∃ i, κ i = κ (i + 1)
  · exact Or.inl heq
  · rw [not_exists] at heq
    by_cases hz : StrictZigzag κ
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr ⟨heq, hz⟩)

/-- **The reduction**: for `4 ≤ n`, the three stratum hypotheses together
imply Tabachnikov's Problem 2 at length `n`.

Status of each hypothesis (`rem:tab_status`):
* `ZigzagRealizes n` — **not discharged**; target of the four-gap programme,
  whose remaining external input is the endpoint-defect certificate.  It is
  vacuously true for odd `n`, since a strictly zigzag word has even length
  (`strictZigzag_even_length`).
* `RunsRealizes n` — **not discharged**; open research, owned externally.
* `PlateauRealizes n` — **not discharged**; open research, owned by nobody.
* `TabachnikovProblem2 4` — proved unconditionally (`tabachnikovProblem2_four`),
  so the reduction is not vacuous at every length. -/
theorem tabachnikovProblem2_of_strata [NeZero n] (hn : 4 ≤ n)
    (hz : ZigzagRealizes n) (hr : RunsRealizes n) (hp : PlateauRealizes n) :
    TabachnikovProblem2 n := by
  intro κ hκ
  obtain ⟨hpos, hconst | hdfv⟩ := hκ
  · obtain ⟨c, hc⟩ := hconst
    have hcpos : 0 < c := (hc 0) ▸ hpos 0
    exact realizesR2_of_const (by omega) hcpos hc
  · rcases strata_exhaustive κ with hplateau | hzig | ⟨hne, hnz⟩
    · exact hp κ hpos hdfv hplateau
    · exact hz κ hpos hzig
    · exact hr κ hpos hne hdfv hnz

/-- **Menger form of the reduction**: under the same three stratum hypotheses,
every positive four-vertex word of length `n` is realized with the prescribed
signed Menger curvatures.  Composition of `tabachnikovProblem2_of_strata` with
the bridge `realizesR2_realizesMenger`. -/
theorem realizesMenger_of_strata [NeZero n] (hn : 4 ≤ n)
    (hz : ZigzagRealizes n) (hr : RunsRealizes n) (hp : PlateauRealizes n)
    {κ : ZMod n → ℝ} (hκ : DiscreteFourVertexPos κ) : RealizesMenger κ :=
  realizesR2_realizesMenger (tabachnikovProblem2_of_strata hn hz hr hp κ hκ)

/-! ## The extrema form of the hypothesis class

Everything above hypothesizes a *level*: `DFV κ c` asks for a real number `c`
and four cyclically ordered indices whose values alternate across it.
Dahlberg and Tabachnikov hypothesize instead an *extremum count*: at least two
local maxima and at least two local minima of the curvature, in the
plateau-aware sense (`PlateauMaxRun` / `PlateauMinRun`).  This section proves
the two hypothesis classes coincide, so `TabachnikovProblem2 n` really is the
literature's problem and not a value-separated proxy for it.

Blueprint: `chap:discrete_tabachnikov_reduction`, section *The extrema form of
the hypothesis class*. -/

/-- **The extremum-form hypothesis class**: all values positive, and the
profile is constant or has two distinct plateau maxima *and* two distinct
plateau minima.  This is the positive-curvature form of the conclusion class
of Dahlberg's Theorem 1, used as a hypothesis. -/
def DiscreteFourVertexExtrema (κ : ZMod n → ℝ) : Prop :=
  (∀ i, 0 < κ i) ∧
    ((∃ c, ∀ i, κ i = c) ∨ (HasTwoPlateauMaxRuns κ ∧ HasTwoPlateauMinRuns κ))

/-- A window level of a positive profile is itself positive: the window
supplies an index whose value is `< c` and which is positive. -/
theorem DFV.pos_of_pos {κ : ZMod n → ℝ} {c : ℝ} (h : DFV κ c)
    (hpos : ∀ i, 0 < κ i) : 0 < c := by
  obtain ⟨_, i₂, _, _, _, _, _, _, _, h2, _, _⟩ := h
  exact lt_trans (hpos ((i₂ : ℕ) : ZMod n)) h2

/-- The `ℕ`-lift `a + (n - 1)` is the predecessor residue of `a`. -/
private lemma natCast_add_sub_one [NeZero n] (a : ℕ) :
    ((a + (n - 1) : ℕ) : ZMod n) = (a : ZMod n) - 1 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hpred : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
      have e : ((n - 1 + 1 : ℕ) : ZMod n) = 0 := by
        rw [Nat.sub_add_cancel hn, ZMod.natCast_self]
      rw [← e]; push_cast; ring
    exact add_eq_zero_iff_eq_neg.mp h
  rw [Nat.cast_add, hpred]
  ring

/-- Auxiliary form of `exists_dfv_of_two_plateauMaxRun` carrying the extra
hypothesis that the first run is the *lower* of the two maxima.  Note the
second run's `PlateauMaxRun` data is never used: only its base value, through
`hle`, and its residue, through the disjointness clause. -/
private theorem exists_dfv_of_two_plateauMaxRun_aux [NeZero n] {κ : ZMod n → ℝ}
    {a₁ k₁ a₂ k₂ : ℕ}
    (h₁ : PlateauMaxRun κ a₁ k₁)
    (hdisj : ∀ m₁, m₁ ≤ k₁ → ∀ m₂, m₂ ≤ k₂ →
      ((a₁ + m₁ : ℕ) : ZMod n) ≠ ((a₂ + m₂ : ℕ) : ZMod n))
    (hle : κ (a₁ : ZMod n) ≤ κ (a₂ : ZMod n)) :
    ∃ c, DFV κ c := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨-, hlow, hhigh⟩ := h₁
  -- the unique lift `d < n` of `a₂ - a₁`
  set d : ℕ := ((a₂ : ZMod n) - (a₁ : ZMod n)).val with hd_def
  have hd_lt : d < n := ZMod.val_lt _
  have hd_cast : ((a₁ + d : ℕ) : ZMod n) = (a₂ : ZMod n) := by
    have : ((d : ℕ) : ZMod n) = (a₂ : ZMod n) - (a₁ : ZMod n) := by
      rw [hd_def]; exact ZMod.natCast_zmod_val _
    rw [Nat.cast_add, this]; ring
  -- Step 1: locate the second run
  have hd_gt : k₁ < d := by
    by_contra hcon
    exact hdisj d (Nat.not_lt.mp hcon) 0 (Nat.zero_le _)
      (by rw [hd_cast, Nat.add_zero])
  have hd_ne_succ : d ≠ k₁ + 1 := by
    intro hcon
    have : ((a₁ + k₁ + 1 : ℕ) : ZMod n) = (a₂ : ZMod n) := by
      rw [← hd_cast, hcon, Nat.add_assoc]
    rw [this] at hhigh
    linarith
  have hd_ne_pred : d ≠ n - 1 := by
    intro hcon
    have : (a₂ : ZMod n) = (a₁ : ZMod n) - 1 := by
      rw [← hd_cast, hcon, natCast_add_sub_one]
    rw [← this] at hlow
    linarith
  have hd_up : d < n - 1 := by omega
  -- Step 2: the level
  set M : ℝ := max (κ ((a₁ : ZMod n) - 1)) (κ ((a₁ + k₁ + 1 : ℕ) : ZMod n)) with hM
  have hM_lt : M < κ (a₁ : ZMod n) := max_lt hlow hhigh
  refine ⟨(M + κ (a₁ : ZMod n)) / 2, a₁, a₁ + k₁ + 1, a₁ + d, a₁ + (n - 1),
    by omega, by omega, by omega, by omega, by linarith, ?_, ?_, ?_⟩
  · have : κ ((a₁ + k₁ + 1 : ℕ) : ZMod n) ≤ M := le_max_right _ _
    linarith
  · rw [hd_cast]; linarith
  · rw [natCast_add_sub_one]
    have : κ ((a₁ : ZMod n) - 1) ≤ M := le_max_left _ _
    linarith

/-- **Two distinct plateau maxima produce a window level.**  Slightly stronger
than "two maxima and two minima give a level": two maxima *alone* already do,
and the level is read off from the *smaller* of the two maxima together with
its own two immediate neighbours — no minimum is ever inspected, and no
adjacent-inequality hypothesis is used. -/
theorem exists_dfv_of_two_plateauMaxRun [NeZero n] {κ : ZMod n → ℝ}
    (h : HasTwoPlateauMaxRuns κ) : ∃ c, DFV κ c := by
  obtain ⟨a₁, k₁, a₂, k₂, -, -, h₁, h₂, hdisj⟩ := h
  rcases le_total (κ (a₁ : ZMod n)) (κ (a₂ : ZMod n)) with hle | hle
  · exact exists_dfv_of_two_plateauMaxRun_aux h₁ hdisj hle
  · exact exists_dfv_of_two_plateauMaxRun_aux h₂
      (fun m₂ hm₂ m₁ hm₁ => (hdisj m₁ hm₁ m₂ hm₂).symm) hle

/-- **Two distinct strict local maxima produce a window level** — the
plateau-free specialization of `exists_dfv_of_two_plateauMaxRun`, obtained by
feeding it two singleton runs. -/
theorem exists_dfv_of_two_strictLocalMax [NeZero n] {κ : ZMod n → ℝ}
    {p q : ZMod n} (hpq : p ≠ q) (hp : IsStrictLocalMax κ p)
    (hq : IsStrictLocalMax κ q) : ∃ c, DFV κ c := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hcp : ((p.val : ℕ) : ZMod n) = p := ZMod.natCast_zmod_val p
  have hcq : ((q.val : ℕ) : ZMod n) = q := ZMod.natCast_zmod_val q
  refine exists_dfv_of_two_plateauMaxRun ⟨p.val, 0, q.val, 0, hn, hn, ?_, ?_, ?_⟩
  · refine ⟨fun m hm => by rw [Nat.le_zero.mp hm, Nat.add_zero], ?_, ?_⟩
    · rw [hcp]; exact hp.1
    · rw [Nat.add_zero, hcp, Nat.cast_add, hcp, Nat.cast_one]; exact hp.2
  · refine ⟨fun m hm => by rw [Nat.le_zero.mp hm, Nat.add_zero], ?_, ?_⟩
    · rw [hcq]; exact hq.1
    · rw [Nat.add_zero, hcq, Nat.cast_add, hcq, Nat.cast_one]; exact hq.2
  · intro m₁ hm₁ m₂ hm₂
    rw [Nat.le_zero.mp hm₁, Nat.le_zero.mp hm₂, Nat.add_zero, Nat.add_zero, hcp, hcq]
    exact hpq

/-! ### The minima are redundant

`rem:tab_minima_redundant`: since two plateau maxima alone already produce a
window level, and a window level produces both kinds of run, the "at least two
local minima" half of Dahlberg's conclusion is a formal consequence of the "at
least two local maxima" half — for any real cyclic word, with no positivity and
no adjacent-inequality hypothesis. -/

/-- Negating the profile exchanges plateau minimum and plateau maximum runs. -/
theorem PlateauMinRun.neg {κ : ZMod n → ℝ} {a k : ℕ} (h : PlateauMinRun κ a k) :
    PlateauMaxRun (fun i => -κ i) a k :=
  ⟨fun m hm => by simpa using h.1 m hm, by simpa using h.2.1, by simpa using h.2.2⟩

/-- Negating the profile exchanges the two distinct-extrema hypotheses. -/
theorem HasTwoPlateauMinRuns.neg {κ : ZMod n → ℝ} (h : HasTwoPlateauMinRuns κ) :
    HasTwoPlateauMaxRuns (fun i => -κ i) := by
  obtain ⟨a₁, k₁, a₂, k₂, hk₁, hk₂, h₁, h₂, hdisj⟩ := h
  exact ⟨a₁, k₁, a₂, k₂, hk₁, hk₂, h₁.neg, h₂.neg, hdisj⟩

/-- A window for the negated profile is a window for the profile at the
negated level, after rotating the four indices by one place: the negation
swaps which pair is high, and `i₄ < i₁ + n` makes `i₁ + n` the fourth index of
the rotated window. -/
theorem DFV.of_neg {κ : ZMod n → ℝ} {c : ℝ} (h : DFV (fun i => -κ i) c) :
    DFV κ (-c) := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, hκ1, hκ2, hκ3, hκ4⟩ := h
  simp only at hκ1 hκ2 hκ3 hκ4
  refine ⟨i₂, i₃, i₄, i₁ + n, h23, h34, h41, by omega, by linarith, by linarith,
    by linarith, ?_⟩
  have hcast : ((i₁ + n : ℕ) : ZMod n) = ((i₁ : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_self]; ring
  rw [hcast]; linarith

/-- **Two distinct plateau minima produce a window level** — the mirror of
`exists_dfv_of_two_plateauMaxRun`, via negation. -/
theorem exists_dfv_of_two_plateauMinRun [NeZero n] {κ : ZMod n → ℝ}
    (h : HasTwoPlateauMinRuns κ) : ∃ c, DFV κ c :=
  let ⟨c, hc⟩ := exists_dfv_of_two_plateauMaxRun h.neg
  ⟨-c, hc.of_neg⟩

/-- **Two distinct local maxima force two distinct local minima.** -/
theorem HasTwoPlateauMaxRuns.hasTwoPlateauMinRuns [NeZero n] {κ : ZMod n → ℝ}
    (h : HasTwoPlateauMaxRuns κ) : HasTwoPlateauMinRuns κ :=
  let ⟨_, hc⟩ := exists_dfv_of_two_plateauMaxRun h
  hc.plateau_extrema.2

/-- **Two distinct local minima force two distinct local maxima.** -/
theorem HasTwoPlateauMinRuns.hasTwoPlateauMaxRuns [NeZero n] {κ : ZMod n → ℝ}
    (h : HasTwoPlateauMinRuns κ) : HasTwoPlateauMaxRuns κ :=
  let ⟨_, hc⟩ := exists_dfv_of_two_plateauMinRun h
  hc.plateau_extrema.1

/-- **The two halves of Dahlberg's conclusion are equivalent.**  In
particular the second conjunct of `DiscreteFourVertexExtrema` is redundant. -/
theorem hasTwoPlateauMaxRuns_iff_hasTwoPlateauMinRuns [NeZero n] {κ : ZMod n → ℝ} :
    HasTwoPlateauMaxRuns κ ↔ HasTwoPlateauMinRuns κ :=
  ⟨HasTwoPlateauMaxRuns.hasTwoPlateauMinRuns,
    HasTwoPlateauMinRuns.hasTwoPlateauMaxRuns⟩

/-- **The level form and the extremum form define the same class.**  Forward
is `DFV.plateau_extrema`; backward is `exists_dfv_of_two_plateauMaxRun`
followed by `DFV.pos_of_pos`, which supplies the positivity of the level for
free. -/
theorem discreteFourVertexPos_iff_extrema [NeZero n] {κ : ZMod n → ℝ} :
    DiscreteFourVertexPos κ ↔ DiscreteFourVertexExtrema κ := by
  constructor
  · rintro ⟨hpos, hconst | ⟨c, -, hdfv⟩⟩
    · exact ⟨hpos, Or.inl hconst⟩
    · exact ⟨hpos, Or.inr ⟨hdfv.plateau_extrema.1, hdfv.plateau_extrema.2⟩⟩
  · rintro ⟨hpos, hconst | ⟨hmax, -⟩⟩
    · exact ⟨hpos, Or.inl hconst⟩
    · obtain ⟨c, hdfv⟩ := exists_dfv_of_two_plateauMaxRun hmax
      exact ⟨hpos, Or.inr ⟨c, hdfv.pos_of_pos hpos, hdfv⟩⟩

/-- **Two distinct plateau maxima suffice**: the minimum runs demanded by
`DiscreteFourVertexExtrema` never have to be exhibited. -/
theorem discreteFourVertexExtrema_of_two_plateauMaxRuns [NeZero n] {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) (hmax : HasTwoPlateauMaxRuns κ) :
    DiscreteFourVertexExtrema κ :=
  ⟨hpos, Or.inr ⟨hmax, hmax.hasTwoPlateauMinRuns⟩⟩

/-- **Problem 2 in Dahlberg's extremum form**: the named proposition of this
file is the literature's problem, not a value-separated approximation to it. -/
theorem tabachnikovProblem2_iff_extrema_form [NeZero n] :
    TabachnikovProblem2 n ↔
      ∀ κ : ZMod n → ℝ, DiscreteFourVertexExtrema κ → RealizesR2 κ := by
  constructor
  · exact fun h κ hκ => h κ (discreteFourVertexPos_iff_extrema.mpr hκ)
  · exact fun h κ hκ => h κ (discreteFourVertexPos_iff_extrema.mp hκ)

/-- **The extremum form is settled at `n = 4`** — `tabachnikovProblem2_four`
transported across `tabachnikovProblem2_iff_extrema_form`, so the extremum
form is non-vacuous too. -/
theorem discreteFourVertexExtrema_realizesR2_four {κ : ZMod 4 → ℝ}
    (hκ : DiscreteFourVertexExtrema κ) : RealizesR2 κ :=
  tabachnikovProblem2_iff_extrema_form.mp tabachnikovProblem2_four κ hκ

/-- **Menger form of the reduction, in Dahlberg's extremum form**: under the
three stratum hypotheses, every positive profile with two distinct plateau
maxima and two distinct plateau minima is realized with the prescribed signed
Menger curvatures. -/
theorem realizesMenger_of_strata_extrema [NeZero n] (hn : 4 ≤ n)
    (hz : ZigzagRealizes n) (hr : RunsRealizes n) (hp : PlateauRealizes n)
    {κ : ZMod n → ℝ} (hκ : DiscreteFourVertexExtrema κ) : RealizesMenger κ :=
  realizesMenger_of_strata hn hz hr hp (discreteFourVertexPos_iff_extrema.mpr hκ)

/-! ## Deleting the plateau stratum

`PlateauRealizes n` — the stratum this file's own docstring calls "open
research, owned by nobody" — is *subsumed* by a uniform-margin strengthening
of the other two strata.  The composition is two facts:

* **density** — a profile with adjacent equal values is a limit of profiles
  with the same four-vertex window and no adjacent equal values
  (`mem_closure_positive_dfv_ne_succ_of_nhds`, the general-`n` form of
  `mem_closure_positive_dfv_ne_succ`);
* **closedness** — realizability passes to such limits provided the realizing
  lengths lie in one box `[a,b]` with `a > 0` and satisfy one wall margin
  `η > 0` (`realizesR2_of_mem_closure_uniform_margin`).

**This section realizes nothing beyond `n = 4`.**
`AdjacentUnequalUniformRealizes n` is proved only at `n = 4`
(`adjacentUnequalUniformRealizes_four`, from the explicit orthogonal-diagonal
lengths) and is open at every `n ≥ 5`; it is STRICTLY STRONGER than the
conjunction of the zigzag and runs hypotheses it replaces, since those two
need only produce *a* realization, whereas this one must produce a length box
and a wall margin, locally uniformly in the profile.  The plateau stratum is
therefore SUBSUMED, never solved — the price of deleting it is charged to the
other two.

Blueprint: `chap:discrete_tabachnikov_reduction`, section *Deleting the
plateau stratum*. -/

section PlateauDeletion

open Filter Set
open scoped Topology

/-- **The index perturbation at general `n`**: add `ε` times each residue's
canonical representative.  Project-local — it is the density vehicle of
`mem_closure_positive_dfv_ne_succ_of_nhds`, and the general-`n` copy of
`n6IndexPerturbation`, which stays where it is as the `n = 6` special case. -/
def indexPerturbation (w : ZMod n → ℝ) (ε : ℝ) (i : ZMod n) : ℝ :=
  w i + ε * i.val

/-- The index perturbation is continuous in its scalar parameter.  Each
coordinate is affine in `ε`, and the profile space carries the product
topology on a finite index type. -/
theorem continuous_indexPerturbation (w : ZMod n → ℝ) :
    Continuous (indexPerturbation w) := by
  unfold indexPerturbation
  fun_prop

/-- The index perturbation tends to its original profile as the parameter
tends to zero, since `indexPerturbation w 0 = w`. -/
theorem tendsto_indexPerturbation_zero (w : ZMod n → ℝ) :
    Tendsto (indexPerturbation w) (𝓝 0) (𝓝 w) := by
  have hcont : ContinuousAt (indexPerturbation w) 0 :=
    (continuous_indexPerturbation w).continuousAt
  change Tendsto (indexPerturbation w) (𝓝 0)
    (𝓝 (indexPerturbation w 0)) at hcont
  convert hcont using 1
  congr 1
  funext i
  simp only [indexPerturbation, zero_mul, add_zero]

/-- **Consecutive residues have different canonical representatives**, as real
numbers, as soon as `2 ≤ n`.  This is what makes the index perturbation move
adjacent entries by different amounts. -/
theorem val_ne_val_add_one (hn : 2 ≤ n) (i : ZMod n) :
    (i.val : ℝ) ≠ ((i + 1).val : ℝ) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro h
  have hval : i.val = (i + 1).val := by exact_mod_cast h
  have hi : i = i + 1 := ZMod.val_injective n hval
  exact one_ne_zero (add_eq_left.mp hi.symm)

/-- **An affine pair with different slopes separates**: for `p ≠ q` the
equation `a + εp = b + εq` has the single solution `ε = (b-a)/(p-q)`, so it
fails on a punctured neighbourhood of `0` — when `a = b` that solution *is*
`0`, which the puncture already removes. -/
theorem eventually_add_mul_ne_add_mul {a b p q : ℝ} (hpq : p ≠ q) :
    ∀ᶠ ε in 𝓝[≠] 0, a + ε * p ≠ b + ε * q := by
  by_cases hab : a = b
  · subst b
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [mem_compl_iff, mem_singleton_iff] at hε
    intro heq
    exact hpq (mul_left_cancel₀ hε (by linarith))
  · have hcont : ContinuousAt (fun ε : ℝ ↦ (a + ε * p) - (b + ε * q)) 0 := by
      fun_prop
    have hzero : (a + 0 * p) - (b + 0 * q) ≠ 0 := by
      simpa only [zero_mul, add_zero, sub_ne_zero] using hab
    have hne := hcont.eventually_ne hzero
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with ε hε
    exact sub_ne_zero.mp hε

/-- **The perturbation is eventually adjacent-unequal**: finitely many
punctured neighbourhoods, one per index, intersect in one. -/
theorem eventually_indexPerturbation_ne_succ [NeZero n] (hn : 2 ≤ n)
    (w : ZMod n → ℝ) :
    ∀ᶠ ε in 𝓝[≠] 0, ∀ i, indexPerturbation w ε i ≠
      indexPerturbation w ε (i + 1) := by
  rw [Filter.eventually_all]
  intro i
  simpa only [indexPerturbation] using eventually_add_mul_ne_add_mul
    (a := w i) (b := w (i + 1)) (val_ne_val_add_one hn i)

/-- **Local density of the adjacent-unequal stratum** — the theorem of this
section.  A positive profile with a four-vertex window at level `c` lies in
the closure of the *adjacent-unequal* profiles with the same window
intersected with any prescribed neighbourhood `U` of it.

The puncture in `𝓝[≠] 0` is essential: at `ε = 0` the curve is `w` itself,
which is exactly the profile whose adjacent equalities are being removed. -/
theorem mem_closure_positive_dfv_ne_succ_of_nhds [NeZero n] (hn : 2 ≤ n)
    {w : ZMod n → ℝ} {c : ℝ} (hpos : ∀ i, 0 < w i) (hdfv : DFV w c)
    {U : Set (ZMod n → ℝ)} (hU : U ∈ 𝓝 w) :
    w ∈ closure ({w' : ZMod n → ℝ |
      (∀ i, 0 < w' i) ∧ DFV w' c ∧ ∀ i, w' i ≠ w' (i + 1)} ∩ U) := by
  have hprofile : ∀ᶠ w' in 𝓝 w, ((∀ i, 0 < w' i) ∧ DFV w' c) ∧ w' ∈ U := by
    filter_upwards [isOpen_positiveProfile.eventually_mem hpos, hdfv.eventually, hU]
      with w' hw'pos hw'dfv hw'U
    exact ⟨⟨hw'pos, hw'dfv⟩, hw'U⟩
  have hpull := (tendsto_indexPerturbation_zero w).eventually hprofile
  have hpull' : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      ((∀ i, 0 < indexPerturbation w ε i) ∧ DFV (indexPerturbation w ε) c) ∧
        indexPerturbation w ε ∈ U :=
    hpull.filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ ε in 𝓝[≠] 0, indexPerturbation w ε ∈
      ({w' : ZMod n → ℝ |
        (∀ i, 0 < w' i) ∧ DFV w' c ∧ ∀ i, w' i ≠ w' (i + 1)} ∩ U) := by
    filter_upwards [hpull', eventually_indexPerturbation_ne_succ hn w]
      with ε hstable hne
    exact ⟨⟨hstable.1.1, hstable.1.2, hne⟩, hstable.2⟩
  have hlimNE : Tendsto (indexPerturbation w) (𝓝[≠] (0 : ℝ)) (𝓝 w) :=
    (tendsto_indexPerturbation_zero w).mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlimNE hall

/-- **Local uniform-margin realization off the diagonal.**  For every positive
`w` and every level `c` with `DFV w c` there are a neighbourhood `U` of `w`
and constants `a, b, η` with `0 < a`, `0 < η` such that every `w' ∈ U` which
is positive, has the window at the *same* level `c`, and has all adjacent
values distinct, is realized by lengths in `[a,b]` with wall margin `η`.

Three features of the quantifier order are deliberate.  The constants are
chosen *after* `(w, c)`, so no uniformity across profile space is demanded —
that would be false, since the arcsine walls force `ℓ → 0` as `κ → ∞`.  The
neighbourhood `U` makes the requirement local, so a construction only has to
behave on one chart.  And `w'` ranges only over adjacent-unequal profiles,
i.e. over the union of the zigzag and runs strata of `strata_exhaustive`.

**Proved only at `n = 4`** (`adjacentUnequalUniformRealizes_four`); open at
every `n ≥ 5`.  It is strictly stronger than the conjunction of
`ZigzagRealizes n` and `RunsRealizes n`: a realization obtained from a bare
degree or compactness argument need not come with a length box or a wall
margin.  What makes `n = 4` work is precisely that its realization is an
explicit formula (`orthogonalEdges`), hence continuous in the profile. -/
def AdjacentUnequalUniformRealizes (n : ℕ) [NeZero n] : Prop :=
  ∀ (w : ZMod n → ℝ) (c : ℝ), (∀ i, 0 < w i) → DFV w c →
    ∃ U ∈ 𝓝 w, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w' ∈ U, (∀ i, 0 < w' i) → DFV w' c → (∀ i, w' i ≠ w' (i + 1)) →
        ∃ ell : ZMod n → ℝ,
          (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
          (∀ i, |w' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
            |w' i| * (ell i / 2) ≤ 1 - eta) ∧
          closureGap w' ell = 0 ∧ turningSum w' ell = 2 * Real.pi

/-- **A single realization always carries a certificate.**  `RealizesR2 κ`
alone yields lengths in a box `[a,b]` with `a > 0` and a wall margin `η > 0`:
`ModerateArc 0` gives the strict inequalities pointwise, and the index type is
finite, so their finitely many witnesses have a positive infimum and a
supremum below the wall.

So the content of `AdjacentUnequalUniformRealizes n` *beyond* realizability of
the adjacent-unequal profiles is exactly that the constants `a, b, η` can be
chosen locally uniformly in the profile.  That, and nothing else, is the price
of deleting the plateau stratum — the hypothesis is not "realizability plus an
unrelated extra", it is "realizability, with the constants not degenerating as
the profile moves in a chart". -/
theorem exists_uniform_margin_certificate_of_realizesR2 [NeZero n]
    {κ : ZMod n → ℝ} (h : RealizesR2 κ) :
    ∃ (ell : ZMod n → ℝ) (a b eta : ℝ), 0 < a ∧ 0 < eta ∧
      (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
      (∀ i, |κ i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
        |κ i| * (ell i / 2) ≤ 1 - eta) ∧
      closureGap κ ell = 0 ∧ turningSum κ ell = 2 * Real.pi := by
  obtain ⟨ell, hmod, hclose, hturn, -⟩ := h
  rw [moderateArc_zero_iff] at hmod
  have hne : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  have hsup : ∀ j : ZMod n,
      max (|κ j| * (ell (j - 1) / 2)) (|κ j| * (ell j / 2)) ≤
        Finset.univ.sup' hne
          (fun i => max (|κ i| * (ell (i - 1) / 2)) (|κ i| * (ell i / 2))) :=
    fun j => Finset.le_sup'
      (fun i => max (|κ i| * (ell (i - 1) / 2)) (|κ i| * (ell i / 2)))
      (Finset.mem_univ j)
  set M := Finset.univ.sup' hne
    (fun i => max (|κ i| * (ell (i - 1) / 2)) (|κ i| * (ell i / 2))) with hM
  have hMlt : M < 1 := by
    rw [hM, Finset.sup'_lt_iff]
    exact fun i _ => max_lt (hmod i).2.1 (hmod i).2.2
  refine ⟨ell, Finset.univ.inf' hne ell, Finset.univ.sup' hne ell, 1 - M,
    ?_, by linarith, ?_, ?_, hclose, hturn⟩
  · rw [Finset.lt_inf'_iff]
    exact fun i _ => (hmod i).1
  · exact fun i => ⟨Finset.inf'_le _ (Finset.mem_univ i),
      Finset.le_sup' _ (Finset.mem_univ i)⟩
  · intro i
    have h1 : |κ i| * (ell (i - 1) / 2) ≤ M := le_trans (le_max_left _ _) (hsup i)
    have h2 : |κ i| * (ell i / 2) ≤ M := le_trans (le_max_right _ _) (hsup i)
    exact ⟨by linarith, by linarith⟩

/-- **The workhorse of this section.**  Under the hypothesis, *every* positive
profile with a four-vertex window at some level is realizable — the window is
all that is asked, no stratum condition at all.  Density puts the profile in
the closure of the adjacent-unequal stratum inside the chart `U` supplied by
the hypothesis, and the uniform-margin closure theorem carries realizability
across.

This is why the hypothesis subsumes every stratum: the three stratum
conditions are used nowhere in the proof. -/
theorem realizesR2_of_adjacentUnequalUniform [NeZero n] (hn : 3 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) {κ : ZMod n → ℝ} {c : ℝ}
    (hpos : ∀ i, 0 < κ i) (hdfv : DFV κ c) : RealizesR2 κ := by
  obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ := h κ c hpos hdfv
  exact realizesR2_of_mem_closure_uniform_margin hn hpos ha heta
    (mem_closure_positive_dfv_ne_succ_of_nhds (by omega) hpos hdfv hU)
    fun w' hw' => hreal w' hw'.2 hw'.1.1 hw'.1.2.1 hw'.1.2.2

/-- **The plateau stratum is a consequence.**  Density puts the plateau
profile in the closure of the adjacent-unequal stratum inside the chart `U`
supplied by the hypothesis, and the uniform-margin closure theorem carries
realizability across.

The adjacent-equality hypothesis of `PlateauRealizes` is never used — that is
deliberate, and is what `tabachnikovProblem2_of_adjacentUnequalUniform`
exploits.  Nothing here realizes anything: the plateau stratum is subsumed by
a strictly stronger hypothesis on the other two, not solved. -/
theorem plateauRealizes_of_adjacentUnequalUniform [NeZero n] (hn : 3 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) : PlateauRealizes n := by
  rintro κ hpos ⟨c, -, hdfv⟩ -
  exact realizesR2_of_adjacentUnequalUniform hn h hpos hdfv

/-- **Problem 2 from one hypothesis on the adjacent-unequal words.**  The
constant disjunct is `realizesR2_of_const`, as in `tabachnikovProblem2_of_strata`;
the window disjunct is the argument of `plateauRealizes_of_adjacentUnequalUniform`
verbatim, which never used the adjacent-equality hypothesis.

The three stratum hypotheses of `tabachnikovProblem2_of_strata` become one —
but that one is strictly stronger than the two it replaces, so this is a
reframing of the remaining obligation, not a step toward discharging it. -/
theorem tabachnikovProblem2_of_adjacentUnequalUniform [NeZero n] (hn : 4 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) : TabachnikovProblem2 n := by
  intro κ hκ
  obtain ⟨hpos, hconst | ⟨c, -, hdfv⟩⟩ := hκ
  · obtain ⟨c, hc⟩ := hconst
    have hcpos : 0 < c := (hc 0) ▸ hpos 0
    exact realizesR2_of_const (by omega) hcpos hc
  · exact realizesR2_of_adjacentUnequalUniform (by omega) h hpos hdfv

/-- **Menger form.**  `tabachnikovProblem2_of_adjacentUnequalUniform` composed
with the bridge `realizesR2_realizesMenger`, exactly as
`realizesMenger_of_strata` composes the three-hypothesis reduction.  Still
conditional at every `n ≥ 5`. -/
theorem realizesMenger_of_adjacentUnequalUniform [NeZero n] (hn : 4 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) {κ : ZMod n → ℝ}
    (hκ : DiscreteFourVertexPos κ) : RealizesMenger κ :=
  realizesR2_realizesMenger (tabachnikovProblem2_of_adjacentUnequalUniform hn h κ hκ)

/-! ### The surviving hypothesis subsumes all three strata

`AdjacentUnequalUniformRealizes n` implies each of `ZigzagRealizes n`,
`RunsRealizes n` and `PlateauRealizes n`, so it is at least as strong as the
conjunction it replaces.  Together with the fact that a realization from a
bare degree or compactness argument carries no length box and no wall margin,
this is the precise sense in which the plateau stratum is *subsumed* rather
than solved: the whole obligation has been moved onto the other two, in a
strengthened form.

The only non-formal step of the argument is the zigzag one, which needs the
window `RunsRealizes` and `PlateauRealizes` already hypothesize but
`ZigzagRealizes` does not: a strict zigzag has two distinct strict local
maxima (`hasTwoPlateauMaxRuns_of_strictZigzag`), which produce a level. -/

/-- In a strict zigzag, a strict local maximum at `i` propagates to `i + 2`:
extrema alternate around the cycle. -/
private lemma isStrictLocalMax_add_two_aux {κ : ZMod n → ℝ}
    (hz : StrictZigzag κ) {i : ZMod n} (hi : IsStrictLocalMax κ i) :
    IsStrictLocalMax κ (i + 2) := by
  have e1 : i + 1 + 1 = i + 2 := by ring
  have e2 : i + 1 + 2 = i + 2 + 1 := by ring
  have e3 : i + 2 - 1 = i + 1 := by ring
  have h1 := hz i
  have h2 := hz (i + 1)
  rw [e1, e2] at h2
  have hup : 0 < κ (i + 2) - κ (i + 1) := by
    rcases mul_neg_iff.mp h1 with ⟨hp, -⟩ | ⟨-, hq⟩
    · linarith [hi.2]
    · exact hq
  refine ⟨?_, ?_⟩
  · rw [e3]; linarith
  · rcases mul_neg_iff.mp h2 with ⟨-, hq⟩ | ⟨hp, -⟩
    · linarith
    · linarith

/-- In a strict zigzag, a strict local minimum at `i` is followed by a strict
local maximum at `i + 1`. -/
private lemma isStrictLocalMax_succ_of_min_aux {κ : ZMod n → ℝ}
    (hz : StrictZigzag κ) {i : ZMod n} (hi : IsStrictLocalMin κ i) :
    IsStrictLocalMax κ (i + 1) := by
  have e1 : i + 1 - 1 = i := by ring
  have e2 : i + 1 + 1 = i + 2 := by ring
  have h1 := hz i
  refine ⟨?_, ?_⟩
  · rw [e1]; exact hi.2
  · rw [e2]
    rcases mul_neg_iff.mp h1 with ⟨-, hq⟩ | ⟨hp, -⟩
    · linarith
    · linarith [hi.2]

/-- A strict local maximum, viewed as a plateau maximum run of length `0`. -/
private lemma plateauMaxRun_zero_aux [NeZero n] {κ : ZMod n → ℝ} {i : ZMod n}
    (hi : IsStrictLocalMax κ i) : PlateauMaxRun κ i.val 0 := by
  have hcast : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_rightInverse i
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    interval_cases m
    simp
  · rw [hcast]; exact hi.1
  · have : ((i.val + 0 + 1 : ℕ) : ZMod n) = i + 1 := by push_cast [hcast]; ring
    rw [this, hcast]; exact hi.2

/-- **A strict zigzag has two distinct plateau maxima** as soon as `3 ≤ n`:
extrema alternate, so `i` and `i + 2` are both strict local maxima, and
`3 ≤ n` keeps them distinct. -/
theorem hasTwoPlateauMaxRuns_of_strictZigzag [NeZero n] (hn : 3 ≤ n)
    {κ : ZMod n → ℝ} (hz : StrictZigzag κ) : HasTwoPlateauMaxRuns κ := by
  have hmax : ∃ i : ZMod n, IsStrictLocalMax κ i := by
    rcases (strictZigzag_iff_forall_extremum κ).mp hz 0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨0 + 1, isStrictLocalMax_succ_of_min_aux hz h⟩
  obtain ⟨i, hi⟩ := hmax
  have hi2 := isStrictLocalMax_add_two_aux hz hi
  have hne : i ≠ i + 2 := by
    intro heq
    have h2 : (2 : ZMod n) = 0 := by
      have := congrArg (fun z : ZMod n => z - i) heq
      simpa using this.symm
    have hdvd : n ∣ 2 := by
      have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h2
      exact (ZMod.natCast_eq_zero_iff 2 n).mp this
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  refine ⟨i.val, 0, (i + 2).val, 0, by omega, by omega,
    plateauMaxRun_zero_aux hi, plateauMaxRun_zero_aux hi2, ?_⟩
  intro m₁ hm₁ m₂ hm₂
  interval_cases m₁
  interval_cases m₂
  simpa [ZMod.natCast_rightInverse i, ZMod.natCast_rightInverse (i + 2)] using hne

/-- **A positive strict zigzag has a four-vertex window at a positive level.**
This is what lets the window-based hypothesis of this section cover
`ZigzagRealizes`, which hypothesizes no window of its own. -/
theorem exists_dfv_pos_of_strictZigzag [NeZero n] (hn : 3 ≤ n) {κ : ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) (hz : StrictZigzag κ) : ∃ c > 0, DFV κ c := by
  obtain ⟨c, hc⟩ := exists_dfv_of_two_plateauMaxRun
    (hasTwoPlateauMaxRuns_of_strictZigzag hn hz)
  exact ⟨c, hc.pos_of_pos hpos, hc⟩

/-- **The zigzag stratum is subsumed too.** -/
theorem zigzagRealizes_of_adjacentUnequalUniform [NeZero n] (hn : 3 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) : ZigzagRealizes n := by
  intro κ hpos hz
  obtain ⟨c, -, hdfv⟩ := exists_dfv_pos_of_strictZigzag hn hpos hz
  exact realizesR2_of_adjacentUnequalUniform hn h hpos hdfv

/-- **The runs stratum is subsumed too.**  Neither the adjacent-inequality
hypothesis nor the non-zigzag hypothesis of `RunsRealizes` is used. -/
theorem runsRealizes_of_adjacentUnequalUniform [NeZero n] (hn : 3 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) : RunsRealizes n := by
  rintro κ hpos - ⟨c, -, hdfv⟩ -
  exact realizesR2_of_adjacentUnequalUniform hn h hpos hdfv

/-- **The surviving hypothesis is at least as strong as the conjunction it
replaces**: it implies all three stratum hypotheses of
`tabachnikovProblem2_of_strata`, not merely the plateau one.

So `tabachnikovProblem2_of_adjacentUnequalUniform` is not a smaller
hypothesis — it is one hypothesis in place of three, and a strictly stronger
one, because a realization produced by a degree or compactness argument need
not come with a length box and a wall margin.  The plateau stratum is
SUBSUMED, never solved. -/
theorem strata_of_adjacentUnequalUniform [NeZero n] (hn : 3 ≤ n)
    (h : AdjacentUnequalUniformRealizes n) :
    ZigzagRealizes n ∧ RunsRealizes n ∧ PlateauRealizes n :=
  ⟨zigzagRealizes_of_adjacentUnequalUniform hn h,
    runsRealizes_of_adjacentUnequalUniform hn h,
    plateauRealizes_of_adjacentUnequalUniform hn h⟩

/-! ### Toward the first instance: explicit lengths at `n = 4`

`AdjacentUnequalUniformRealizes n` is proved for no `n`, and the cheapest
first instance is `n = 4`, where the realization is an explicit
orthogonal-diagonal quadrilateral.  What the hypothesis needs beyond the
existing `n = 4` converse is a *formula*: `exists_orthogonal_realization_of_strict_alternation`
hides its lengths behind an existential, so nothing can be said about how they
vary with the profile.  The definition below names them, and
`orthogonalEdges_certificate` re-derives the certificate for the named
lengths — the same construction, with the existential opened.

This is the ingredient a proof of the instance needs; it is not the instance.
-/

/-- **The orthogonal-diagonal edge lengths at `n = 4`, named.**  These are
exactly the lengths that `exists_orthogonal_realization_of_strict_alternation`
produces, written as an explicit formula in the profile so that their
dependence on it can be used.  Project-local: Mathlib has no discrete
realization theory. -/
noncomputable def orthogonalEdges (k₀ k₁ k₂ k₃ : ℝ) : ZMod 4 → ℝ :=
  fourProfile (Real.sqrt (orthogonalA2 k₀ k₁ k₂ k₃))
    (Real.sqrt (orthogonalB2 k₀ k₁ k₂ k₃))
    (Real.sqrt (orthogonalC2 k₀ k₁ k₂ k₃))
    (Real.sqrt (orthogonalD2 k₀ k₁ k₂ k₃))

/-- **The named lengths realize the profile.**  Everything but the choice of
lengths is `orthogonal_realization_data`; the four Pythagoras relations are
the `orthogonalA2`–`orthogonalD2` identities, and the four curvature
relations are `field_simp`. -/
theorem orthogonalEdges_certificate {k₀ k₁ k₂ k₃ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (h₁₀ : k₁ < k₀) (h₁₂ : k₁ < k₂) (h₃₀ : k₃ < k₀) (h₃₂ : k₃ < k₂) :
    ModerateArc 0 (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdges k₀ k₁ k₂ k₃) ∧
      closureGap (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdges k₀ k₁ k₂ k₃) = 0 ∧
      turningSum (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdges k₀ k₁ k₂ k₃) =
        2 * Real.pi := by
  unfold orthogonalEdges
  have hprod : k₁ * k₃ < k₀ * k₂ := by
    calc
      k₁ * k₃ < k₀ * k₃ := mul_lt_mul_of_pos_right h₁₀ hk₃
      _ < k₀ * k₂ := mul_lt_mul_of_pos_left h₃₂ hk₀
  have hΔ : 0 < orthogonalDelta k₀ k₁ k₂ k₃ := by
    have hfac : orthogonalDelta k₀ k₁ k₂ k₃ =
        (k₀ * k₂ - k₁ * k₃) * (k₀ * k₂ + k₁ * k₃) := by
      unfold orthogonalDelta; ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr hprod) (add_pos (mul_pos hk₀ hk₂) (mul_pos hk₁ hk₃))
  have hs₂₃ : 0 < k₂ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₂) (add_pos hk₂ hk₃)]
  have hs₀₃ : 0 < k₀ ^ 2 - k₃ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₃₀) (add_pos hk₀ hk₃)]
  have hs₀₁ : 0 < k₀ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₀) (add_pos hk₀ hk₁)]
  have hs₂₁ : 0 < k₂ ^ 2 - k₁ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₁₂) (add_pos hk₂ hk₁)]
  have hA2 : 0 < orthogonalA2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalA2
    exact div_pos (mul_pos (by norm_num) hs₂₃) hΔ
  have hB2 : 0 < orthogonalB2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalB2
    exact div_pos (mul_pos (by norm_num) hs₀₃) hΔ
  have hC2 : 0 < orthogonalC2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalC2
    exact div_pos (mul_pos (by norm_num) hs₀₁) hΔ
  have hD2 : 0 < orthogonalD2 k₀ k₁ k₂ k₃ := by
    unfold orthogonalD2
    exact div_pos (mul_pos (by norm_num) hs₂₁) hΔ
  set A := Real.sqrt (orthogonalA2 k₀ k₁ k₂ k₃) with hAdef
  set B := Real.sqrt (orthogonalB2 k₀ k₁ k₂ k₃) with hBdef
  set C := Real.sqrt (orthogonalC2 k₀ k₁ k₂ k₃) with hCdef
  set D := Real.sqrt (orthogonalD2 k₀ k₁ k₂ k₃) with hDdef
  have hA : 0 < A := Real.sqrt_pos.2 hA2
  have hB : 0 < B := Real.sqrt_pos.2 hB2
  have hC : 0 < C := Real.sqrt_pos.2 hC2
  have hD : 0 < D := Real.sqrt_pos.2 hD2
  have hAroot : A ^ 2 = orthogonalA2 k₀ k₁ k₂ k₃ := Real.sq_sqrt hA2.le
  have hBroot : B ^ 2 = orthogonalB2 k₀ k₁ k₂ k₃ := Real.sq_sqrt hB2.le
  have hCroot : C ^ 2 = orthogonalC2 k₀ k₁ k₂ k₃ := Real.sq_sqrt hC2.le
  have hDroot : D ^ 2 = orthogonalD2 k₀ k₁ k₂ k₃ := Real.sq_sqrt hD2.le
  have hasq : (k₀ * A * D / 2) ^ 2 = k₀ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hAroot, hDroot]; norm_num
  have hbsq : (k₁ * A * B / 2) ^ 2 = k₁ ^ 2 * orthogonalA2 k₀ k₁ k₂ k₃ *
      orthogonalB2 k₀ k₁ k₂ k₃ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hAroot, hBroot]; norm_num
  have hcsq : (k₂ * B * C / 2) ^ 2 = k₂ ^ 2 * orthogonalB2 k₀ k₁ k₂ k₃ *
      orthogonalC2 k₀ k₁ k₂ k₃ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hBroot, hCroot]; norm_num
  have hdsq : (k₃ * C * D / 2) ^ 2 = k₃ ^ 2 * orthogonalC2 k₀ k₁ k₂ k₃ *
      orthogonalD2 k₀ k₁ k₂ k₃ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hCroot, hDroot]; norm_num
  have hk₀eq : 2 * (k₀ * A * D / 2) / (A * D) = k₀ := by
    field_simp [hA.ne', hD.ne']
  have hk₁eq : 2 * (k₁ * A * B / 2) / (A * B) = k₁ := by
    field_simp [hA.ne', hB.ne']
  have hk₂eq : 2 * (k₂ * B * C / 2) / (B * C) = k₂ := by
    field_simp [hB.ne', hC.ne']
  have hk₃eq : 2 * (k₃ * C * D / 2) / (C * D) = k₃ := by
    field_simp [hC.ne', hD.ne']
  have hdata := orthogonal_realization_data
    (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)
    (a := k₀ * A * D / 2) (b := k₁ * A * B / 2) (c := k₂ * B * C / 2)
    (d := k₃ * C * D / 2)
    (div_pos (mul_pos (mul_pos hk₀ hA) hD) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₁ hA) hB) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₂ hB) hC) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₃ hC) hD) (by norm_num))
    hA hB hC hD
    (by rw [hAroot, hasq, hbsq]; exact orthogonalA2_identity hΔ.ne')
    (by rw [hBroot, hbsq, hcsq]; exact orthogonalB2_identity hΔ.ne')
    (by rw [hCroot, hcsq, hdsq]; exact orthogonalC2_identity hΔ.ne')
    (by rw [hDroot, hdsq, hasq]; exact orthogonalD2_identity hΔ.ne')
    hk₀eq hk₁eq hk₂eq hk₃eq
  exact ⟨hdata.1, hdata.2.1, hdata.2.2.1⟩

private lemma zmod4_cases_aux (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

/-- **The named lengths depend continuously on the profile.**  Away from the
vanishing of `orthogonalDelta` the four squared lengths are rational functions
of the profile, and `Real.sqrt` is continuous.  This is the second ingredient
an instance of `AdjacentUnequalUniformRealizes 4` needs: it is what forbids
the length box and the wall margin from degenerating as the profile moves. -/
theorem continuousAt_orthogonalEdges {κ : ZMod 4 → ℝ}
    (hΔ : orthogonalDelta (κ 0) (κ 1) (κ 2) (κ 3) ≠ 0) :
    ContinuousAt
      (fun w : ZMod 4 → ℝ => orthogonalEdges (w 0) (w 1) (w 2) (w 3)) κ := by
  have hden : ContinuousAt
      (fun w : ZMod 4 → ℝ => orthogonalDelta (w 0) (w 1) (w 2) (w 3)) κ := by
    unfold orthogonalDelta
    fun_prop
  have key : ∀ f : ℝ → ℝ → ℝ → ℝ → ℝ,
      ContinuousAt (fun w : ZMod 4 → ℝ => f (w 0) (w 1) (w 2) (w 3)) κ →
      ContinuousAt (fun w : ZMod 4 → ℝ =>
        Real.sqrt (4 * f (w 0) (w 1) (w 2) (w 3) /
          orthogonalDelta (w 0) (w 1) (w 2) (w 3))) κ := by
    intro f hf
    exact Real.continuous_sqrt.continuousAt.comp
      (((continuousAt_const.mul hf).div hden hΔ))
  rw [continuousAt_pi]
  intro i
  have hA := key (fun k₀ k₁ k₂ k₃ => k₂ ^ 2 - k₃ ^ 2) (by fun_prop)
  have hB := key (fun k₀ k₁ k₂ k₃ => k₀ ^ 2 - k₃ ^ 2) (by fun_prop)
  have hC := key (fun k₀ k₁ k₂ k₃ => k₀ ^ 2 - k₁ ^ 2) (by fun_prop)
  have hD := key (fun k₀ k₁ k₂ k₃ => k₂ ^ 2 - k₁ ^ 2) (by fun_prop)
  rcases zmod4_cases_aux i with rfl | rfl | rfl | rfl
  · simpa [orthogonalEdges, orthogonalA2] using hA
  · simpa [orthogonalEdges, orthogonalB2] using hB
  · simpa [orthogonalEdges, orthogonalC2] using hC
  · simpa [orthogonalEdges, orthogonalD2] using hD

/-- **Uniform constants from a continuous certificate.**  If a length map `E`
is continuous at `κ`, and every positive profile satisfying an
eventually-true side condition `P` is realized by `E`, then one neighbourhood
of `κ` and one triple `(a, b, η)` serve every profile in it.

Project-local: this is the mechanism that turns a *pointwise* realization
formula into the *locally uniform* certificate that
`AdjacentUnequalUniformRealizes` demands.  The whole content is that the
finitely many strict inequalities of the base moderate-arc certificate stay
strict on a neighbourhood — which is exactly what a bare degree or
compactness realization, having no formula, cannot supply. -/
theorem exists_uniform_margin_nhds_of_continuousAt [NeZero n] {κ : ZMod n → ℝ}
    {P : (ZMod n → ℝ) → Prop} {E : (ZMod n → ℝ) → ZMod n → ℝ}
    (hpos : ∀ i, 0 < κ i) (hP : ∀ᶠ w in 𝓝 κ, P w) (hEcont : ContinuousAt E κ)
    (hcert : ∀ w : ZMod n → ℝ, (∀ i, 0 < w i) → P w →
      ModerateArc 0 w (E w) ∧ closureGap w (E w) = 0 ∧
        turningSum w (E w) = 2 * Real.pi) :
    ∃ U ∈ 𝓝 κ, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, ∃ ell : ZMod n → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  have hbase := hcert κ hpos hP.self_of_nhds
  have hmodκ : ∀ i, 0 < E κ i ∧ |κ i| * (E κ (i - 1) / 2) < 1 ∧
      |κ i| * (E κ i / 2) < 1 := moderateArc_zero_iff.mp hbase.1
  have hEi : ∀ i : ZMod n, ContinuousAt (fun w : ZMod n → ℝ => E w i) κ :=
    continuousAt_pi.mp hEcont
  have hne : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  have hwallsup : ∀ j : ZMod n,
      max (|κ j| * (E κ (j - 1) / 2)) (|κ j| * (E κ j / 2)) ≤
        Finset.univ.sup' hne
          (fun i => max (|κ i| * (E κ (i - 1) / 2)) (|κ i| * (E κ i / 2))) :=
    fun j => Finset.le_sup'
      (fun i => max (|κ i| * (E κ (i - 1) / 2)) (|κ i| * (E κ i / 2)))
      (Finset.mem_univ j)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Finset.univ.sup' hne
      (fun i => max (|κ i| * (E κ (i - 1) / 2)) (|κ i| * (E κ i / 2))) := ⟨_, rfl⟩
  have hM : M < 1 := by
    rw [hMdef, Finset.sup'_lt_iff]
    exact fun i _ => max_lt (hmodκ i).2.1 (hmodκ i).2.2
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Finset.univ.inf' hne (E κ) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Finset.univ.sup' hne (E κ) := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff]
    exact fun i _ => (hmodκ i).1
  have hminf : ∀ i, m ≤ E κ i := by
    intro i; rw [hmdef]; exact Finset.inf'_le _ (Finset.mem_univ i)
  have hSsup : ∀ i, E κ i ≤ S := by
    intro i; rw [hSdef]; exact Finset.le_sup' _ (Finset.mem_univ i)
  have hbox : ∀ᶠ w in 𝓝 κ, ∀ i, m / 2 ≤ E w i ∧ E w i ≤ S + 1 := by
    rw [Filter.eventually_all]
    intro i
    have h1 := (hEi i).eventually (eventually_gt_nhds
      (show m / 2 < E κ i by have := hminf i; linarith))
    have h2 := (hEi i).eventually (eventually_lt_nhds
      (show E κ i < S + 1 by have := hSsup i; linarith))
    filter_upwards [h1, h2] with w hw1 hw2
    exact ⟨hw1.le, hw2.le⟩
  have hwall : ∀ᶠ w in 𝓝 κ, ∀ i,
      |w i| * (E w (i - 1) / 2) ≤ 1 - (1 - M) / 2 ∧
        |w i| * (E w i / 2) ≤ 1 - (1 - M) / 2 := by
    rw [Filter.eventually_all]
    intro i
    have hc1 : ContinuousAt
        (fun w : ZMod n → ℝ => |w i| * (E w (i - 1) / 2)) κ :=
      ((continuous_apply i).continuousAt.abs).mul ((hEi (i - 1)).div_const 2)
    have hc2 : ContinuousAt (fun w : ZMod n → ℝ => |w i| * (E w i / 2)) κ :=
      ((continuous_apply i).continuousAt.abs).mul ((hEi i).div_const 2)
    have hbnd := hwallsup i
    rw [← hMdef] at hbnd
    have hv1 : |κ i| * (E κ (i - 1) / 2) < 1 - (1 - M) / 2 := by
      have := le_trans (le_max_left (|κ i| * (E κ (i - 1) / 2))
        (|κ i| * (E κ i / 2))) hbnd
      linarith
    have hv2 : |κ i| * (E κ i / 2) < 1 - (1 - M) / 2 := by
      have := le_trans (le_max_right (|κ i| * (E κ (i - 1) / 2))
        (|κ i| * (E κ i / 2))) hbnd
      linarith
    filter_upwards [hc1.eventually (eventually_lt_nhds hv1),
      hc2.eventually (eventually_lt_nhds hv2)] with w hw1 hw2
    exact ⟨hw1.le, hw2.le⟩
  have hev : ∀ᶠ w in 𝓝 κ, ((∀ i, 0 < w i) ∧ P w) ∧
      (∀ i, m / 2 ≤ E w i ∧ E w i ≤ S + 1) ∧
      (∀ i, |w i| * (E w (i - 1) / 2) ≤ 1 - (1 - M) / 2 ∧
        |w i| * (E w i / 2) ≤ 1 - (1 - M) / 2) := by
    filter_upwards [isOpen_positiveProfile.eventually_mem hpos, hP, hbox, hwall]
      with w hw1 hw2 hw3 hw4
    exact ⟨⟨hw1, hw2⟩, hw3, hw4⟩
  obtain ⟨U, hU, hUprop⟩ := Filter.eventually_iff_exists_mem.mp hev
  refine ⟨U, hU, m / 2, S + 1, (1 - M) / 2, by linarith, by linarith, ?_⟩
  intro w hw
  obtain ⟨⟨hwpos, hwP⟩, hwbox, hwwall⟩ := hUprop w hw
  obtain ⟨-, hclose, hturn⟩ := hcert w hwpos hwP
  exact ⟨E w, hwbox, hwwall, hclose, hturn⟩

private lemma fourProfile_eval_aux (w : ZMod 4 → ℝ) :
    fourProfile (w 0) (w 1) (w 2) (w 3) = w := by
  funext i
  rcases zmod4_cases_aux i with rfl | rfl | rfl | rfl <;> simp

private lemma eventually_lt_apply_aux {κ : ZMod 4 → ℝ} (p q : ZMod 4)
    (hpq : κ p < κ q) : ∀ᶠ w in 𝓝 κ, w p < w q := by
  have hc : ContinuousAt (fun w : ZMod 4 → ℝ => w q - w p) κ := by fun_prop
  filter_upwards [hc.eventually
    (eventually_gt_nhds (show (0 : ℝ) < κ q - κ p by linarith))] with w hw
  linarith

/-- **The uniform-margin requirement holds on the even chart at `n = 4`.**  If
the two larger values of `κ` sit at the even indices, there are a
neighbourhood `U` of `κ` and constants `a, b, η` with `0 < a`, `0 < η` such
that *every* profile in `U` — no positivity, window or adjacency hypothesis
needed, `U` already forces what is used — is realized by lengths in `[a,b]`
with wall margin `η`, closing at total turning `2π`.

This is exactly the requirement `AdjacentUnequalUniformRealizes 4` makes,
restricted to the chart where the window sits at even indices.  It is the
first place in this development where a realization is produced with
*uniform* constants, which is what deleting the plateau stratum costs. -/
theorem exists_uniform_margin_nhds_four_even {κ : ZMod 4 → ℝ} {c : ℝ}
    (hpos : ∀ i, 0 < κ i) (h₀ : c < κ 0) (h₁ : κ 1 < c) (h₂ : c < κ 2)
    (h₃ : κ 3 < c) :
    ∃ U ∈ 𝓝 κ, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, ∃ ell : ZMod 4 → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  have hΔ : orthogonalDelta (κ 0) (κ 1) (κ 2) (κ 3) ≠ 0 := by
    have hfac : orthogonalDelta (κ 0) (κ 1) (κ 2) (κ 3) =
        (κ 0 * κ 2 - κ 1 * κ 3) * (κ 0 * κ 2 + κ 1 * κ 3) := by
      unfold orthogonalDelta; ring
    have hprod : κ 1 * κ 3 < κ 0 * κ 2 := by
      nlinarith [hpos 0, hpos 1, hpos 2, hpos 3]
    rw [hfac]
    exact ne_of_gt (mul_pos (sub_pos.mpr hprod)
      (add_pos (mul_pos (hpos 0) (hpos 2)) (mul_pos (hpos 1) (hpos 3))))
  refine exists_uniform_margin_nhds_of_continuousAt
    (P := fun w => w 1 < w 0 ∧ w 1 < w 2 ∧ w 3 < w 0 ∧ w 3 < w 2)
    (E := fun w => orthogonalEdges (w 0) (w 1) (w 2) (w 3)) hpos ?_
    (continuousAt_orthogonalEdges hΔ) ?_
  · filter_upwards [eventually_lt_apply_aux 1 0 (by linarith : κ 1 < κ 0),
      eventually_lt_apply_aux 1 2 (by linarith : κ 1 < κ 2),
      eventually_lt_apply_aux 3 0 (by linarith : κ 3 < κ 0),
      eventually_lt_apply_aux 3 2 (by linarith : κ 3 < κ 2)]
      with w e₁ e₂ e₃ e₄
    exact ⟨e₁, e₂, e₃, e₄⟩
  · intro w hw hPw
    have hd := orthogonalEdges_certificate (hw 0) (hw 1) (hw 2) (hw 3)
      hPw.1 hPw.2.1 hPw.2.2.1 hPw.2.2.2
    rwa [fourProfile_eval_aux w] at hd

/-- **The orthogonal-diagonal edge lengths at `n = 4`, odd chart.**  The
defining system of `orthogonal_realization_data` is invariant under the
simultaneous cyclic shift of the profile and of the lengths, so a profile
whose two larger values sit at the *odd* indices is realized by the data of
the once-shifted profile, read back one place.  No rotation lemma for
`closureGap` or `turningSum` is needed: the shift happens in the *inputs*. -/
noncomputable def orthogonalEdgesOdd (k₀ k₁ k₂ k₃ : ℝ) : ZMod 4 → ℝ :=
  fourProfile (Real.sqrt (orthogonalD2 k₁ k₂ k₃ k₀))
    (Real.sqrt (orthogonalA2 k₁ k₂ k₃ k₀))
    (Real.sqrt (orthogonalB2 k₁ k₂ k₃ k₀))
    (Real.sqrt (orthogonalC2 k₁ k₂ k₃ k₀))

/-- **The odd-chart lengths realize the profile.**  `orthogonalEdges_certificate`
with the inputs of `orthogonal_realization_data` relabelled by one cyclic
step; the four Pythagoras relations are the same four identities, read in the
shifted order. -/
theorem orthogonalEdgesOdd_certificate {k₀ k₁ k₂ k₃ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (h₀₁ : k₀ < k₁) (h₀₃ : k₀ < k₃) (h₂₁ : k₂ < k₁) (h₂₃ : k₂ < k₃) :
    ModerateArc 0 (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdgesOdd k₀ k₁ k₂ k₃) ∧
      closureGap (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdgesOdd k₀ k₁ k₂ k₃) = 0 ∧
      turningSum (fourProfile k₀ k₁ k₂ k₃) (orthogonalEdgesOdd k₀ k₁ k₂ k₃) =
        2 * Real.pi := by
  unfold orthogonalEdgesOdd
  have hprod : k₂ * k₀ < k₁ * k₃ := by
    calc
      k₂ * k₀ < k₁ * k₀ := mul_lt_mul_of_pos_right h₂₁ hk₀
      _ < k₁ * k₃ := mul_lt_mul_of_pos_left h₀₃ hk₁
  have hΔ : 0 < orthogonalDelta k₁ k₂ k₃ k₀ := by
    have hfac : orthogonalDelta k₁ k₂ k₃ k₀ =
        (k₁ * k₃ - k₂ * k₀) * (k₁ * k₃ + k₂ * k₀) := by
      unfold orthogonalDelta; ring
    rw [hfac]
    exact mul_pos (sub_pos.mpr hprod) (add_pos (mul_pos hk₁ hk₃) (mul_pos hk₂ hk₀))
  have hs₃₀ : 0 < k₃ ^ 2 - k₀ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₀₃) (add_pos hk₃ hk₀)]
  have hs₁₀ : 0 < k₁ ^ 2 - k₀ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₀₁) (add_pos hk₁ hk₀)]
  have hs₁₂ : 0 < k₁ ^ 2 - k₂ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₂₁) (add_pos hk₁ hk₂)]
  have hs₃₂ : 0 < k₃ ^ 2 - k₂ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h₂₃) (add_pos hk₃ hk₂)]
  have hA2 : 0 < orthogonalA2 k₁ k₂ k₃ k₀ := by
    unfold orthogonalA2
    exact div_pos (mul_pos (by norm_num) hs₃₀) hΔ
  have hB2 : 0 < orthogonalB2 k₁ k₂ k₃ k₀ := by
    unfold orthogonalB2
    exact div_pos (mul_pos (by norm_num) hs₁₀) hΔ
  have hC2 : 0 < orthogonalC2 k₁ k₂ k₃ k₀ := by
    unfold orthogonalC2
    exact div_pos (mul_pos (by norm_num) hs₁₂) hΔ
  have hD2 : 0 < orthogonalD2 k₁ k₂ k₃ k₀ := by
    unfold orthogonalD2
    exact div_pos (mul_pos (by norm_num) hs₃₂) hΔ
  set A := Real.sqrt (orthogonalD2 k₁ k₂ k₃ k₀) with hAdef
  set B := Real.sqrt (orthogonalA2 k₁ k₂ k₃ k₀) with hBdef
  set C := Real.sqrt (orthogonalB2 k₁ k₂ k₃ k₀) with hCdef
  set D := Real.sqrt (orthogonalC2 k₁ k₂ k₃ k₀) with hDdef
  have hA : 0 < A := Real.sqrt_pos.2 hD2
  have hB : 0 < B := Real.sqrt_pos.2 hA2
  have hC : 0 < C := Real.sqrt_pos.2 hB2
  have hD : 0 < D := Real.sqrt_pos.2 hC2
  have hAroot : A ^ 2 = orthogonalD2 k₁ k₂ k₃ k₀ := Real.sq_sqrt hD2.le
  have hBroot : B ^ 2 = orthogonalA2 k₁ k₂ k₃ k₀ := Real.sq_sqrt hA2.le
  have hCroot : C ^ 2 = orthogonalB2 k₁ k₂ k₃ k₀ := Real.sq_sqrt hB2.le
  have hDroot : D ^ 2 = orthogonalC2 k₁ k₂ k₃ k₀ := Real.sq_sqrt hC2.le
  have hasq : (k₀ * A * D / 2) ^ 2 = k₀ ^ 2 * orthogonalC2 k₁ k₂ k₃ k₀ *
      orthogonalD2 k₁ k₂ k₃ k₀ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hAroot, hDroot]; ring
  have hbsq : (k₁ * A * B / 2) ^ 2 = k₁ ^ 2 * orthogonalA2 k₁ k₂ k₃ k₀ *
      orthogonalD2 k₁ k₂ k₃ k₀ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hAroot, hBroot]; ring
  have hcsq : (k₂ * B * C / 2) ^ 2 = k₂ ^ 2 * orthogonalA2 k₁ k₂ k₃ k₀ *
      orthogonalB2 k₁ k₂ k₃ k₀ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hBroot, hCroot]; ring
  have hdsq : (k₃ * C * D / 2) ^ 2 = k₃ ^ 2 * orthogonalB2 k₁ k₂ k₃ k₀ *
      orthogonalC2 k₁ k₂ k₃ k₀ / 4 := by
    rw [div_pow, mul_pow, mul_pow, hCroot, hDroot]; ring
  have hk₀eq : 2 * (k₀ * A * D / 2) / (A * D) = k₀ := by
    field_simp [hA.ne', hD.ne']
  have hk₁eq : 2 * (k₁ * A * B / 2) / (A * B) = k₁ := by
    field_simp [hA.ne', hB.ne']
  have hk₂eq : 2 * (k₂ * B * C / 2) / (B * C) = k₂ := by
    field_simp [hB.ne', hC.ne']
  have hk₃eq : 2 * (k₃ * C * D / 2) / (C * D) = k₃ := by
    field_simp [hC.ne', hD.ne']
  have hdata := orthogonal_realization_data
    (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)
    (a := k₀ * A * D / 2) (b := k₁ * A * B / 2) (c := k₂ * B * C / 2)
    (d := k₃ * C * D / 2)
    (div_pos (mul_pos (mul_pos hk₀ hA) hD) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₁ hA) hB) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₂ hB) hC) (by norm_num))
    (div_pos (mul_pos (mul_pos hk₃ hC) hD) (by norm_num))
    hA hB hC hD
    (by rw [hAroot, hasq, hbsq]; exact orthogonalD2_identity hΔ.ne')
    (by rw [hBroot, hbsq, hcsq]; exact orthogonalA2_identity hΔ.ne')
    (by rw [hCroot, hcsq, hdsq]; exact orthogonalB2_identity hΔ.ne')
    (by rw [hDroot, hdsq, hasq]; exact orthogonalC2_identity hΔ.ne')
    hk₀eq hk₁eq hk₂eq hk₃eq
  exact ⟨hdata.1, hdata.2.1, hdata.2.2.1⟩

/-- The odd-chart lengths are continuous where the shifted discriminant does
not vanish. -/
theorem continuousAt_orthogonalEdgesOdd {κ : ZMod 4 → ℝ}
    (hΔ : orthogonalDelta (κ 1) (κ 2) (κ 3) (κ 0) ≠ 0) :
    ContinuousAt
      (fun w : ZMod 4 → ℝ => orthogonalEdgesOdd (w 0) (w 1) (w 2) (w 3)) κ := by
  have hden : ContinuousAt
      (fun w : ZMod 4 → ℝ => orthogonalDelta (w 1) (w 2) (w 3) (w 0)) κ := by
    unfold orthogonalDelta
    fun_prop
  have key : ∀ f : ℝ → ℝ → ℝ → ℝ → ℝ,
      ContinuousAt (fun w : ZMod 4 → ℝ => f (w 0) (w 1) (w 2) (w 3)) κ →
      ContinuousAt (fun w : ZMod 4 → ℝ =>
        Real.sqrt (4 * f (w 0) (w 1) (w 2) (w 3) /
          orthogonalDelta (w 1) (w 2) (w 3) (w 0))) κ := by
    intro f hf
    exact Real.continuous_sqrt.continuousAt.comp
      ((continuousAt_const.mul hf).div hden hΔ)
  rw [continuousAt_pi]
  intro i
  have hA := key (fun k₀ k₁ k₂ k₃ => k₃ ^ 2 - k₀ ^ 2) (by fun_prop)
  have hB := key (fun k₀ k₁ k₂ k₃ => k₁ ^ 2 - k₀ ^ 2) (by fun_prop)
  have hC := key (fun k₀ k₁ k₂ k₃ => k₁ ^ 2 - k₂ ^ 2) (by fun_prop)
  have hD := key (fun k₀ k₁ k₂ k₃ => k₃ ^ 2 - k₂ ^ 2) (by fun_prop)
  rcases zmod4_cases_aux i with rfl | rfl | rfl | rfl
  · simpa [orthogonalEdgesOdd, orthogonalD2] using hD
  · simpa [orthogonalEdgesOdd, orthogonalA2] using hA
  · simpa [orthogonalEdgesOdd, orthogonalB2] using hB
  · simpa [orthogonalEdgesOdd, orthogonalC2] using hC

/-- **The uniform-margin requirement holds on the odd chart at `n = 4`.**  The
mirror of `exists_uniform_margin_nhds_four_even` with the two larger values at
the odd indices. -/
theorem exists_uniform_margin_nhds_four_odd {κ : ZMod 4 → ℝ} {c : ℝ}
    (hpos : ∀ i, 0 < κ i) (h₀ : κ 0 < c) (h₁ : c < κ 1) (h₂ : κ 2 < c)
    (h₃ : c < κ 3) :
    ∃ U ∈ 𝓝 κ, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, ∃ ell : ZMod 4 → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  have hΔ : orthogonalDelta (κ 1) (κ 2) (κ 3) (κ 0) ≠ 0 := by
    have hfac : orthogonalDelta (κ 1) (κ 2) (κ 3) (κ 0) =
        (κ 1 * κ 3 - κ 2 * κ 0) * (κ 1 * κ 3 + κ 2 * κ 0) := by
      unfold orthogonalDelta; ring
    have hprod : κ 2 * κ 0 < κ 1 * κ 3 := by
      nlinarith [hpos 0, hpos 1, hpos 2, hpos 3]
    rw [hfac]
    exact ne_of_gt (mul_pos (sub_pos.mpr hprod)
      (add_pos (mul_pos (hpos 1) (hpos 3)) (mul_pos (hpos 2) (hpos 0))))
  refine exists_uniform_margin_nhds_of_continuousAt
    (P := fun w => w 0 < w 1 ∧ w 0 < w 3 ∧ w 2 < w 1 ∧ w 2 < w 3)
    (E := fun w => orthogonalEdgesOdd (w 0) (w 1) (w 2) (w 3)) hpos ?_
    (continuousAt_orthogonalEdgesOdd hΔ) ?_
  · filter_upwards [eventually_lt_apply_aux 0 1 (by linarith : κ 0 < κ 1),
      eventually_lt_apply_aux 0 3 (by linarith : κ 0 < κ 3),
      eventually_lt_apply_aux 2 1 (by linarith : κ 2 < κ 1),
      eventually_lt_apply_aux 2 3 (by linarith : κ 2 < κ 3)]
      with w e₁ e₂ e₃ e₄
    exact ⟨e₁, e₂, e₃, e₄⟩
  · intro w hw hPw
    have hd := orthogonalEdgesOdd_certificate (hw 0) (hw 1) (hw 2) (hw 3)
      hPw.1 hPw.2.1 hPw.2.2.1 hPw.2.2.2
    rwa [fourProfile_eval_aux w] at hd

/-- **The hypothesis is non-vacuous: it holds at `n = 4`.**  At length four a
`DFV` window forces its four indices to be consecutive, so the two larger
values sit either at the even indices or at the odd ones, and the two chart
lemmas cover both cases.  Neither the adjacent-inequality hypothesis nor the
window hypothesis on the *nearby* profiles is used: the chart neighbourhood
already supplies everything.

This is the first instance of `AdjacentUnequalUniformRealizes`, so the
plateau-deletion reduction is not vacuous, and — via
`strata_of_adjacentUnequalUniform` — the three stratum hypotheses hold at
`n = 4` with uniform constants. -/
theorem adjacentUnequalUniformRealizes_four : AdjacentUnequalUniformRealizes 4 := by
  intro w c hpos hdfv
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h41, hc1, hc2, hc3, hc4⟩ := hdfv
  have e2 : i₂ = i₁ + 1 := by omega
  have e3 : i₃ = i₁ + 2 := by omega
  have e4 : i₄ = i₁ + 3 := by omega
  subst e2; subst e3; subst e4
  push_cast at hc2 hc3 hc4
  obtain ⟨A, hA⟩ : ∃ A : ZMod 4, A = ((i₁ : ℕ) : ZMod 4) := ⟨_, rfl⟩
  rw [← hA] at hc1 hc2 hc3 hc4
  have hweak : ∀ U ∈ 𝓝 w, ∀ a b eta : ℝ, 0 < a → 0 < eta →
      (∀ w' ∈ U, ∃ ell : ZMod 4 → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w' i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w' ell = 0 ∧ turningSum w' ell = 2 * Real.pi) →
      ∃ U ∈ 𝓝 w, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
        ∀ w' ∈ U, (∀ i, 0 < w' i) → DFV w' c → (∀ i, w' i ≠ w' (i + 1)) →
          ∃ ell : ZMod 4 → ℝ,
            (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
            (∀ i, |w' i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
              |w' i| * (ell i / 2) ≤ 1 - eta) ∧
            closureGap w' ell = 0 ∧ turningSum w' ell = 2 * Real.pi :=
    fun U hU a b eta ha heta hreal =>
      ⟨U, hU, a, b, eta, ha, heta, fun w' hw' _ _ _ => hreal w' hw'⟩
  rcases zmod4_cases_aux A with rfl | rfl | rfl | rfl
  · norm_num at hc2 hc3 hc4
    obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
      exists_uniform_margin_nhds_four_even (c := c) hpos hc1 hc2 hc3 hc4
    exact hweak U hU a b eta ha heta hreal
  · norm_num at hc2 hc3 hc4
    obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
      exists_uniform_margin_nhds_four_odd (c := c) hpos hc4 hc1 hc2 hc3
    exact hweak U hU a b eta ha heta hreal
  · norm_num at hc2 hc3 hc4
    obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
      exists_uniform_margin_nhds_four_even (c := c) hpos hc3 hc4 hc1 hc2
    exact hweak U hU a b eta ha heta hreal
  · norm_num at hc2 hc3 hc4
    obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
      exists_uniform_margin_nhds_four_odd (c := c) hpos hc2 hc3 hc4 hc1
    exact hweak U hU a b eta ha heta hreal

/-- **All three strata hold at `n = 4` with uniform constants.**  The zigzag
and runs strata were already known there (`tabachnikovProblem2_four`); what is
new is that a *single* local chart, with one length box and one wall margin,
covers every profile near a given one.  That uniformity — not the realization
— is the content that `n ≥ 5` still lacks. -/
theorem strata_four : ZigzagRealizes 4 ∧ RunsRealizes 4 ∧ PlateauRealizes 4 :=
  strata_of_adjacentUnequalUniform (by norm_num) adjacentUnequalUniformRealizes_four

end PlateauDeletion

/-! ## Uniformity is free at a regular point

`rem:tab_plateau_deleted` records the price of the plateau deletion: a
construction must now deliver a length box and a wall margin, *locally
uniformly* in the profile, and at `n = 4` that price was paid by having an
explicit continuous formula.  It is natural to read that as "any `n ≥ 5`
construction must also produce a formula".  This section measures the price
and finds it **zero wherever the closure map is a submersion**.

The observation is that `projImage_mem_nhds_of_jointSubmersion`
(`CollaredConverse.lean`) accepts an *arbitrary* neighbourhood `V` of the
solution point; `profileImage_mem_nhds_of_collarRegular`
(`CollarOpenness.lean`) calls it with `V` the whole moment-rank open set.
Calling it instead with that open set intersected with a small ball costs
nothing and buys everything: every nearby profile is then realized by lengths
within `ε` of the ONE fixed reference length vector, which is a length box and
a wall margin at once.  No continuity of any length map is used, and no
formula.

**Honest scope.**  This section realizes nothing new and proves
`AdjacentUnequalUniformRealizes n` at no `n ≥ 5`: it replaces one open
hypothesis by another.  What is genuinely new is the SIZE of the price charged
by the plateau deletion — zero at regular points — so a future `n ≥ 5`
construction does not have to produce a continuous formula the way the `n = 4`
route did; it has to produce a *regular* realization.  Whether
`RegularCollarCoverage n` is strictly weaker than `TabachnikovProblem2 n`
itself turns on whether the constant-curvature stratum is the whole
moment-rank-drop locus, which is numerically true in every sample taken and
has neither proof nor counterexample.

**Not a violation of the Lorentzian Closure Obstruction.**  That obstruction
forbids a lower bound on `|det|` uniform over profile space.  The argument
here uses the submersion at ONE point and transports it by an open-mapping
argument, which is exactly the local statement the obstruction leaves
standing; no uniform determinant bound is asserted anywhere. -/

section RegularUniformity

open Filter Set
open scoped Topology

/-- **`thm:tab_local_profile_image`.**  The localized form of
`profileImage_mem_nhds_of_collarRegular`: at a point `p` of the regular collar
interior over the chamber `univ`, the profile image of the regular collar
interior *intersected with a ball of radius `ε` around `p`* is still a
neighbourhood of `p.1`.

Project-local because `projImage_mem_nhds_of_jointSubmersion` places no
constraint on its neighbourhood `V` beyond being a neighbourhood, so the whole
proof of `profileImage_mem_nhds_of_collarRegular` goes through verbatim with
`V` shrunk to the moment-rank open set intersected with `Metric.ball p ε`.
This is the single step that makes the D24 uniformity free. -/
theorem profileImage_ball_mem_nhds_of_collarRegular [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    Prod.fst '' (collarRegularInterior (Set.univ : Set (ZMod n → ℝ)) ∩
      Metric.ball p ε) ∈ 𝓝 p.1 := by
  obtain ⟨hpI, hpR⟩ := hp
  obtain ⟨G', hG⟩ := closureMapR3_hasStrictFDerivAt hpI.2.1
  have hfd : fderiv ℝ closureMapR3 p = G' := hG.hasFDerivAt.fderiv
  have hsurj : (G'.prod
      (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))).range = ⊤ := by
    rw [← hfd]
    exact (range_prod_fst_eq_top_iff _).mpr
      ((lengthRank_iff_momentRank hpI).mpr hpR)
  have h0 : Prod.fst ''
      ({y : (ZMod n → ℝ) × (ZMod n → ℝ) | closureMapR3 y = 0} ∩
        ({q : (ZMod n → ℝ) × (ZMod n → ℝ) |
          ModerateArc 0 q.1 q.2 ∧ MomentRank q.1 q.2} ∩ Metric.ball p ε))
      ∈ 𝓝 p.1 :=
    projImage_mem_nhds_of_jointSubmersion hpI.2.2 hG hasStrictFDerivAt_fst
      hsurj (Filter.inter_mem (isOpen_momentRank.mem_nhds ⟨hpI.2.1, hpR⟩)
        (Metric.ball_mem_nhds p hε)) Set.Subset.rfl
  refine Filter.mem_of_superset h0 ?_
  rintro κ' ⟨y, ⟨hy0, ⟨hyMA, hyMR⟩, hyB⟩, rfl⟩
  exact ⟨y, ⟨⟨⟨Set.mem_univ _, hyMA, hy0⟩, hyMR⟩, hyB⟩, rfl⟩

/-- **`thm:tab_uniform_of_collarRegular` — the theorem of this section.**  A
single point `p` of the regular collar interior over `univ` produces a
neighbourhood `U` of its profile and ONE triple `(a, b, η)`, `a > 0`, `η > 0`,
serving *every* profile in `U`: each is realized by lengths in `[a, b]` whose
two wall products are at most `1 - η`, with vanishing closure gap and total
turning `2π`.

The conclusion is character-identical to that of
`exists_uniform_margin_nhds_of_continuousAt`, so the two are interchangeable
at the consumption site — but the hypothesis here is a *rank condition at one
point*, not a continuous length formula.  That is the whole content: the
uniformity that `AdjacentUnequalUniformRealizes` demands, and that the `n = 4`
route paid for with an explicit formula, is free at a regular point.  The
mechanism is `profileImage_ball_mem_nhds_of_collarRegular`, which confines the
realizing lengths of every nearby profile to one fixed ball around the single
reference length vector `p.2`; a ball is a length box and a wall margin at
once.

Neither `3 ≤ n` nor positivity of `p.1` is needed: the wall products are taken
in absolute value and the argument never leaves the moderate-arc domain.

**Not a uniform determinant bound.**  The submersion is used at the single
point `p`, and transported by the open-mapping step of
`projImage_mem_nhds_of_jointSubmersion`; nothing here asserts a lower bound on
`|det|` uniform over profile space, which the Lorentzian Closure Obstruction
refutes. -/
theorem exists_uniform_margin_nhds_of_collarRegular [NeZero n]
    {p : (ZMod n → ℝ) × (ZMod n → ℝ)}
    (hp : p ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ))) :
    ∃ U ∈ 𝓝 p.1, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, ∃ ell : ZMod n → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  obtain ⟨hpI, hpR⟩ := hp
  have hmod : ∀ i, 0 < p.2 i ∧ |p.1 i| * (p.2 (i - 1) / 2) < 1 ∧
      |p.1 i| * (p.2 i / 2) < 1 := moderateArc_zero_iff.mp hpI.2.1
  have hne : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  -- the four finite readouts at the reference point `p`
  have hwallsup : ∀ j : ZMod n,
      max (|p.1 j| * (p.2 (j - 1) / 2)) (|p.1 j| * (p.2 j / 2)) ≤
        Finset.univ.sup' hne
          (fun i => max (|p.1 i| * (p.2 (i - 1) / 2)) (|p.1 i| * (p.2 i / 2))) :=
    fun j => Finset.le_sup'
      (fun i => max (|p.1 i| * (p.2 (i - 1) / 2)) (|p.1 i| * (p.2 i / 2)))
      (Finset.mem_univ j)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Finset.univ.sup' hne
      (fun i => max (|p.1 i| * (p.2 (i - 1) / 2)) (|p.1 i| * (p.2 i / 2))) := ⟨_, rfl⟩
  have hM : M < 1 := by
    rw [hMdef, Finset.sup'_lt_iff]
    exact fun i _ => max_lt (hmod i).2.1 (hmod i).2.2
  have hwM : ∀ i : ZMod n, |p.1 i| * (p.2 (i - 1) / 2) ≤ M ∧
      |p.1 i| * (p.2 i / 2) ≤ M := by
    intro i
    have h := hwallsup i
    rw [← hMdef] at h
    exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = Finset.univ.inf' hne p.2 := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = Finset.univ.sup' hne p.2 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Finset.univ.sup' hne (fun i => |p.1 i|) := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef, Finset.lt_inf'_iff]
    exact fun i _ => (hmod i).1
  have hminf : ∀ i, m ≤ p.2 i := by
    intro i; rw [hmdef]; exact Finset.inf'_le _ (Finset.mem_univ i)
  have hSsup : ∀ i, p.2 i ≤ S := by
    intro i; rw [hSdef]; exact Finset.le_sup' _ (Finset.mem_univ i)
  have hPsup : ∀ i, |p.1 i| ≤ P := by
    intro i; rw [hPdef]
    exact Finset.le_sup' (fun i => |p.1 i|) (Finset.mem_univ i)
  have hP0 : 0 ≤ P := le_trans (abs_nonneg _) (hPsup 0)
  have hS0 : 0 < S := lt_of_lt_of_le hmpos (le_trans (hminf 0) (hSsup 0))
  -- the radius: small enough to keep the box positive and the walls inside `M + (1-M)/2`
  have hden : 0 < P + S + 1 := by linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
      ε = min (min 1 (m / 2)) ((1 - M) / (P + S + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min one_pos (by linarith)) (div_pos (by linarith) hden)
  have hε1 : ε ≤ 1 := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεm : ε ≤ m / 2 := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεM : ε * (P + S + 1) ≤ 1 - M := by
    have hle : ε ≤ (1 - M) / (P + S + 1) := by rw [hεdef]; exact min_le_right _ _
    have := mul_le_mul_of_nonneg_right hle hden.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at this
  refine ⟨Prod.fst '' (collarRegularInterior (Set.univ : Set (ZMod n → ℝ)) ∩
      Metric.ball p ε),
    profileImage_ball_mem_nhds_of_collarRegular ⟨hpI, hpR⟩ hε,
    m / 2, S + 1, (1 - M) / 2, by linarith, by linarith, ?_⟩
  rintro w ⟨q, ⟨hqI, hqB⟩, rfl⟩
  -- the product norm is a max of two sup norms, so both components move by `< ε`
  have hd : dist q p < ε := Metric.mem_ball.mp hqB
  rw [Prod.dist_eq] at hd
  have hd1 : ∀ i, |q.1 i - p.1 i| < ε := by
    intro i
    have h := (dist_pi_lt_iff hε).mp (lt_of_le_of_lt (le_max_left _ _) hd) i
    rwa [Real.dist_eq] at h
  have hd2 : ∀ i, |q.2 i - p.2 i| < ε := by
    intro i
    have h := (dist_pi_lt_iff hε).mp (lt_of_le_of_lt (le_max_right _ _) hd) i
    rwa [Real.dist_eq] at h
  have hbox : ∀ i, m / 2 ≤ q.2 i ∧ q.2 i ≤ S + 1 := by
    intro i
    have h := hd2 i
    rw [abs_lt] at h
    have h1 := hminf i
    have h2 := hSsup i
    exact ⟨by linarith, by linarith⟩
  have hwall : ∀ i j : ZMod n, |p.1 i| * (p.2 j / 2) ≤ M →
      |q.1 i| * (q.2 j / 2) ≤ 1 - (1 - M) / 2 := by
    intro i j hij
    have habs : |q.1 i| ≤ |p.1 i| + ε := by
      have h := hd1 i
      have hsub := abs_sub_abs_le_abs_sub (q.1 i) (p.1 i)
      linarith
    have hlen : q.2 j ≤ p.2 j + ε := by
      have h := hd2 j
      rw [abs_lt] at h
      linarith
    have hq2pos : 0 < q.2 j := lt_of_lt_of_le (by linarith) (hbox j).1
    have key : |q.1 i| * (q.2 j / 2) ≤ (|p.1 i| + ε) * ((p.2 j + ε) / 2) :=
      mul_le_mul habs (by linarith) (by linarith)
        (by have := abs_nonneg (p.1 i); linarith)
    have expand : (|p.1 i| + ε) * ((p.2 j + ε) / 2)
        = |p.1 i| * (p.2 j / 2) + ε * (p.2 j / 2) + ε * (|p.1 i| / 2)
          + ε * ε / 2 := by ring
    have t1 : ε * (p.2 j / 2) ≤ ε * (S / 2) :=
      mul_le_mul_of_nonneg_left (by have := hSsup j; linarith) hε.le
    have t2 : ε * (|p.1 i| / 2) ≤ ε * (P / 2) :=
      mul_le_mul_of_nonneg_left (by have := hPsup i; linarith) hε.le
    have t3 : ε * ε / 2 ≤ ε * (1 / 2) := by
      have := mul_le_mul_of_nonneg_left hε1 hε.le
      linarith
    have t4 : ε * (S / 2) + ε * (P / 2) + ε * (1 / 2) ≤ (1 - M) / 2 := by
      nlinarith [hεM]
    rw [expand] at key
    linarith
  refine ⟨q.2, hbox, fun i => ⟨hwall i (i - 1) (hwM i).1, hwall i i (hwM i).2⟩, ?_⟩
  exact (closureMapR3_eq_zero_iff q.1 q.2).mp hqI.1.2.2

/-- **The reusable singleton-chamber bridge**, the D25 counterpart of
`realizesR2_eventually_of_collarRegularInterior_nonempty`: the chamber enters
`collarRegularInterior` only through the profile-membership condition, so a
member over `{κ}` has first component `κ` and is a member over `univ`.  Hence
a nonempty regular collar interior over the singleton chamber already yields
the locally uniform certificate around `κ`. -/
theorem exists_uniform_margin_nhds_of_collarRegularInterior_nonempty [NeZero n]
    {κ : ZMod n → ℝ} (hne : (collarRegularInterior {κ}).Nonempty) :
    ∃ U ∈ 𝓝 κ, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, ∃ ell : ZMod n → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  obtain ⟨q, ⟨hqS, hqMA, hq0⟩, hqR⟩ := hne
  have hq1 : q.1 = κ := Set.mem_singleton_iff.mp hqS
  obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
    exists_uniform_margin_nhds_of_collarRegular
      (⟨⟨Set.mem_univ _, hqMA, hq0⟩, hqR⟩ :
        q ∈ collarRegularInterior (Set.univ : Set (ZMod n → ℝ)))
  rw [hq1] at hU
  exact ⟨U, hU, a, b, eta, ha, heta, hreal⟩

/-- **`def:tab_regular_coverage`.**  Every strictly positive profile with a
four-vertex window at some level is realized by lengths at which the closure
map is a submersion — that is, it is the first coordinate of a point of the
regular collar interior over `univ`.

**No uniformity, no length box and no wall margin appear in this statement.**
That is the whole point: it is a pointwise, purely geometric requirement, and
`adjacentUnequalUniformRealizes_of_regularCollarCoverage` shows it already
implies the locally uniform hypothesis `AdjacentUnequalUniformRealizes n` that
the plateau deletion charges.  It is stronger than plain realizability only in
asking the realization to be *regular*; the moment-rank criterion fails on the
constant-curvature stratum (`not_momentRank_of_const_curvature`), which a
four-vertex window already excludes, but whether that stratum is the *whole*
rank-drop locus is unknown — so whether this is genuinely weaker than
`TabachnikovProblem2 n` is open. -/
def RegularCollarCoverage (n : ℕ) [NeZero n] : Prop :=
  ∀ (w : ZMod n → ℝ) (c : ℝ), (∀ i, 0 < w i) → DFV w c →
    ∃ ell : ZMod n → ℝ,
      ((w, ell) : (ZMod n → ℝ) × (ZMod n → ℝ)) ∈
        collarRegularInterior (Set.univ : Set (ZMod n → ℝ))

/-- **`thm:tab_uniform_of_coverage` — the price of the plateau deletion is
zero on the regular locus.**  `RegularCollarCoverage n`, which mentions no
constants at all, implies `AdjacentUnequalUniformRealizes n`, which demands a
length box and a wall margin locally uniformly in the profile.

`exists_uniform_margin_nhds_of_collarRegular` supplies a conclusion strictly
stronger than the definition asks — it serves *every* profile of the
neighbourhood, not only the positive adjacent-unequal ones with the same
window — so the three side hypotheses on the nearby profiles are discarded,
exactly as `adjacentUnequalUniformRealizes_four` discards them through its
`hweak` helper.

Nothing here realizes anything: one open hypothesis is replaced by another.
What is measured is the *size* of the surplus charged by the plateau
deletion. -/
theorem adjacentUnequalUniformRealizes_of_regularCollarCoverage [NeZero n]
    (h : RegularCollarCoverage n) : AdjacentUnequalUniformRealizes n := by
  intro w c hpos hdfv
  obtain ⟨ell, hmem⟩ := h w c hpos hdfv
  obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
    exists_uniform_margin_nhds_of_collarRegular hmem
  exact ⟨U, hU, a, b, eta, ha, heta, fun w' hw' _ _ _ => hreal w' hw'⟩

/-- **`cor:tab_problem2_of_coverage`.**  Problem 2 from a hypothesis with no
uniformity in it: compose `adjacentUnequalUniformRealizes_of_regularCollarCoverage`
with `tabachnikovProblem2_of_adjacentUnequalUniform`.

Still conditional at every `n ≥ 5`; `RegularCollarCoverage n` is proved
nowhere in this development. -/
theorem tabachnikovProblem2_of_regularCollarCoverage [NeZero n] (hn : 4 ≤ n)
    (h : RegularCollarCoverage n) : TabachnikovProblem2 n :=
  tabachnikovProblem2_of_adjacentUnequalUniform hn
    (adjacentUnequalUniformRealizes_of_regularCollarCoverage h)

/-- **Menger form of `tabachnikovProblem2_of_regularCollarCoverage`**, through
the bridge `realizesR2_realizesMenger`. -/
theorem realizesMenger_of_regularCollarCoverage [NeZero n] (hn : 4 ≤ n)
    (h : RegularCollarCoverage n) {κ : ZMod n → ℝ}
    (hκ : DiscreteFourVertexPos κ) : RealizesMenger κ :=
  realizesR2_realizesMenger (tabachnikovProblem2_of_regularCollarCoverage hn h κ hκ)

/-- **`thm:tab_uniform_family_notPrime`, factored form.**  At every
`n = m·p` with `m ≥ 3`, `p ≥ 2` the certificate demanded by
`AdjacentUnequalUniformRealizes` exists on an explicit open family: around the
block spike profile there is a neighbourhood, one length box `[a, b]` with
`a > 0` and one wall margin `η > 0`, such that every profile in it is
positive with a four-vertex window and is realized within those constants.

This is the D25 counterpart of `exists_nhds_dfv_realizesR2`: the rotational
witness gives a regular collar point over the singleton chamber, hence over
`univ` with first coordinate the spike, and
`exists_uniform_margin_nhds_of_collarRegular` upgrades the bare realizability
of that family to a uniform certificate.  It does **not** give
`AdjacentUnequalUniformRealizes n`, which quantifies over every positive
four-vertex profile. -/
theorem exists_nhds_dfv_uniform_margin [NeZero n] {m p : ℕ}
    (hn : n = m * p) (hm : 3 ≤ m) (hp : 2 ≤ p) :
    ∃ κ₀ : ZMod n → ℝ, ∃ U ∈ 𝓝 κ₀, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, DiscreteFourVertexPos w ∧ ∃ ell : ZMod n → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  obtain ⟨hpos, hper, hnc⟩ := blockSpikeProfile_spec hn (by omega) hp
  obtain ⟨U, hU, a, b, eta, ha, heta, hreal⟩ :=
    exists_uniform_margin_nhds_of_collarRegularInterior_nonempty
      (collarRegularInterior_nonempty_of_periodic hn hm hp hpos hper hnc)
  obtain ⟨V, hV, hVprop⟩ := Filter.eventually_iff_exists_mem.mp
    (DiscreteFourVertexPos.eventually_of_window hpos
      (by norm_num : (0 : ℝ) < 3 / 2) (blockSpikeProfile_dfv hn hm hp))
  exact ⟨blockSpikeProfile p, U ∩ V, Filter.inter_mem hU hV, a, b, eta, ha, heta,
    fun w hw => ⟨hVprop w hw.2, hreal w hw.1⟩⟩

/-- Project-local arithmetic readout, re-derived here because the
`CollarOpenness.lean` helper of the same content is `private`: every composite
`n ≥ 6` admits a factorization `n = m·p` with `m ≥ 3` and `p ≥ 2`. -/
private lemma exists_factorization_of_composite' {n : ℕ} (hn6 : 6 ≤ n)
    (hnp : ¬ n.Prime) : ∃ m p : ℕ, n = m * p ∧ 3 ≤ m ∧ 2 ≤ p := by
  have hq := Nat.minFac_prime (show n ≠ 1 by omega)
  obtain ⟨d, hd⟩ := Nat.minFac_dvd n
  rcases eq_or_lt_of_le hq.two_le with heq | hlt
  · rw [← heq] at hd
    exact ⟨d, 2, by omega, by omega, le_rfl⟩
  · refine ⟨n.minFac, d, hd, by omega, ?_⟩
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · exfalso
      have hcase : d = 0 ∨ d = 1 := by omega
      rcases hcase with h0 | h1
      · rw [h0, Nat.mul_zero] at hd
        omega
      · rw [h1, Nat.mul_one] at hd
        exact hnp (by rw [hd]; exact hq)
    · exact hd2

/-- **`thm:tab_uniform_family_notPrime`.**  At every composite `n ≥ 6` there
is a profile `κ₀` and a neighbourhood of it on which one length box and one
wall margin serve every profile, each of which is positive with a four-vertex
window.  The composite readout of `exists_nhds_dfv_uniform_margin`. -/
theorem exists_nhds_dfv_uniform_margin_of_notPrime [NeZero n]
    (hn6 : 6 ≤ n) (hnp : ¬ n.Prime) :
    ∃ κ₀ : ZMod n → ℝ, ∃ U ∈ 𝓝 κ₀, ∃ a b eta : ℝ, 0 < a ∧ 0 < eta ∧
      ∀ w ∈ U, DiscreteFourVertexPos w ∧ ∃ ell : ZMod n → ℝ,
        (∀ i, a ≤ ell i ∧ ell i ≤ b) ∧
        (∀ i, |w i| * (ell (i - 1) / 2) ≤ 1 - eta ∧
          |w i| * (ell i / 2) ≤ 1 - eta) ∧
        closureGap w ell = 0 ∧ turningSum w ell = 2 * Real.pi := by
  obtain ⟨m, p, hn, hm, hp⟩ := exists_factorization_of_composite' hn6 hnp
  exact exists_nhds_dfv_uniform_margin hn hm hp

/-- **The coverage condition is satisfied at at least one profile at every
composite `n ≥ 6`.**  The block spike is positive, has a four-vertex window at
the level `3/2`, and *is* the profile of a point of the regular collar
interior over `univ` — that is, it meets the requirement
`RegularCollarCoverage n` imposes, at that one profile.

This is non-vacuity of the requirement, not of the hypothesis: nothing here
gives `RegularCollarCoverage n`, which quantifies over *every* positive
four-vertex profile. -/
theorem exists_dfv_collarRegularInterior_of_notPrime [NeZero n]
    (hn6 : 6 ≤ n) (hnp : ¬ n.Prime) :
    ∃ κ ell : ZMod n → ℝ, (∀ i, 0 < κ i) ∧ DFV κ (3 / 2 : ℝ) ∧
      ((κ, ell) : (ZMod n → ℝ) × (ZMod n → ℝ)) ∈
        collarRegularInterior (Set.univ : Set (ZMod n → ℝ)) := by
  obtain ⟨m, p, hn, hm, hp⟩ := exists_factorization_of_composite' hn6 hnp
  obtain ⟨hpos, hper, hnc⟩ := blockSpikeProfile_spec hn (by omega) hp
  obtain ⟨q, ⟨hqS, hqMA, hq0⟩, hqR⟩ :=
    collarRegularInterior_nonempty_of_periodic hn hm hp hpos hper hnc
  have hq1 : q.1 = blockSpikeProfile (n := n) p := Set.mem_singleton_iff.mp hqS
  refine ⟨blockSpikeProfile p, q.2, hpos, blockSpikeProfile_dfv hn hm hp, ?_⟩
  rw [← hq1]
  exact ⟨⟨Set.mem_univ _, hqMA, hq0⟩, hqR⟩

/-- **All three strata from regular collar coverage.**  The D25 counterpart of
`strata_four`: `RegularCollarCoverage n` — a pointwise regularity requirement
with no constants in it — already implies each of `ZigzagRealizes n`,
`RunsRealizes n` and `PlateauRealizes n`, through
`strata_of_adjacentUnequalUniform`.  Conditional at every `n ≥ 5`. -/
theorem strata_of_regularCollarCoverage [NeZero n] (hn : 3 ≤ n)
    (h : RegularCollarCoverage n) :
    ZigzagRealizes n ∧ RunsRealizes n ∧ PlateauRealizes n :=
  strata_of_adjacentUnequalUniform hn
    (adjacentUnequalUniformRealizes_of_regularCollarCoverage h)

end RegularUniformity

end Gluck.Discrete
