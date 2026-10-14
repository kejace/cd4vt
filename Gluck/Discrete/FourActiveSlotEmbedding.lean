import Gluck.Discrete.GapCoords
import Gluck.Discrete.BlockResultant
import Gluck.Discrete.CurvatureLinkage
import Gluck.Discrete.NativeOppositePureNativeRank
import Gluck.Discrete.RegularDormantOpening

/-!
# Embedding four literal active edges in an arbitrary cyclic profile

The selected edges are actual edges of the original word, ordered by their
natural representatives. All unselected lengths vanish on the active slice;
no curvature reading is changed. Identities in this file hold on the entire
active slice, including signed lengths, so they can later be differentiated.
-/

namespace Gluck.Discrete.FourActiveSlots

open scoped BigOperators

/-- Four distinct actual edges, in the ambient natural order. -/
structure Frame (n : ℕ) where
  edge : Fin 4 → ℕ
  strictMono : StrictMono edge
  lt_n : ∀ j, edge j < n

namespace Frame

variable {n : ℕ} (F : Frame n)

/-- The original cyclic edge index. -/
def residue (j : Fin 4) : ZMod n := (F.edge j : ZMod n)

def natEmbedding : Fin 4 ↪ ℕ := ⟨F.edge, F.strictMono.injective⟩

lemma residue_injective : Function.Injective F.residue := by
  intro i j hij
  apply F.strictMono.injective
  have := congrArg ZMod.val hij
  simpa only [residue, ZMod.val_natCast_of_lt (F.lt_n i),
    ZMod.val_natCast_of_lt (F.lt_n j)] using this

/-- Full ambient lengths obtained from the four half-lengths. -/
noncomputable def lengths (L : Fin 4 → ℝ) (i : ZMod n) : ℝ :=
  ∑ j : Fin 4, if i = F.residue j then 2 * L j else 0

@[simp] lemma lengths_selected (L : Fin 4 → ℝ) (j : Fin 4) :
    F.lengths L (F.residue j) = 2 * L j := by
  unfold lengths
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right (fun he => hij (F.residue_injective he.symm))]
  · simp

lemma lengths_unselected (L : Fin 4 → ℝ) {i : ZMod n}
    (hi : ∀ j, i ≠ F.residue j) : F.lengths L i = 0 := by
  simp only [lengths, ite_eq_right (hi _), Finset.sum_const_zero]

/-- The literal reading at the start of a selected edge. -/
def start (κ : ZMod n → ℝ) (j : Fin 4) : ℝ := κ (F.residue j)

/-- The literal reading at the end of a selected edge. -/
def finish (κ : ZMod n → ℝ) (j : Fin 4) : ℝ := κ (F.residue j + 1)

noncomputable def startArc (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  Real.arcsin (F.start κ j * L j)

noncomputable def finishArc (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  Real.arcsin (F.finish κ j * L j)

@[simp] lemma gap_selected (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) (j : Fin 4) :
    gapAngle κ (F.lengths L) (F.residue j) =
      F.startArc κ L j + F.finishArc κ L j := by
  simp [gapAngle, gapAngleAt, startArc, finishArc, start, finish]

/-- Sparse summation over an arbitrary collection of selected actual edges. -/
lemma sum_range_selected {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hoff : ∀ k < n, (∀ j, k ≠ F.edge j) → f k = 0) :
    ∑ k ∈ Finset.range n, f k = ∑ j : Fin 4, f (F.edge j) := by
  let s := Finset.univ.map F.natEmbedding
  have hs : s ⊆ Finset.range n := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hk
    exact Finset.mem_range.2 (F.lt_n j)
  have hsum := Finset.sum_subset hs (f := f) (by
    intro k hk hks
    apply hoff k (Finset.mem_range.1 hk)
    intro j hkj
    apply hks
    exact Finset.mem_map.2 ⟨j, Finset.mem_univ _, hkj.symm⟩)
  simpa only [s, Finset.sum_map, natEmbedding, Function.Embedding.coeFn_mk] using hsum.symm

lemma residue_ne_of_nat_ne {k : ℕ} (hk : k < n) (hne : ∀ j, k ≠ F.edge j) :
    ∀ j, (k : ZMod n) ≠ F.residue j := by
  intro j he
  apply hne j
  have := congrArg ZMod.val he
  simpa only [residue, ZMod.val_natCast_of_lt hk,
    ZMod.val_natCast_of_lt (F.lt_n j)] using this

/-- Exact total-turn regrouping; all hidden curvature readings are retained. -/
theorem turningSum_lengths [NeZero n] (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    turningSum κ (F.lengths L) =
      ∑ j : Fin 4, (F.startArc κ L j + F.finishArc κ L j) := by
  rw [← sum_gapAngle, ← sum_range_natCast_add (gapAngle κ (F.lengths L)) 0]
  simp only [zero_add]
  rw [F.sum_range_selected]
  · exact Finset.sum_congr rfl (fun j _ => F.gap_selected κ L j)
  · intro k hk hne
    simp [gapAngle, gapAngleAt, F.lengths_unselected L (F.residue_ne_of_nat_ne hk hne)]

/-- A prefix of the edge-gap sum is the corresponding prefix of the four
selected edges. -/
lemma sum_gap_prefix (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) {r : ℕ} (hr : r ≤ n) :
    (∑ k ∈ Finset.range r, gapAngle κ (F.lengths L) (k : ZMod n)) =
      ∑ j : Fin 4, if F.edge j < r then F.startArc κ L j + F.finishArc κ L j else 0 := by
  let f : ℕ → ℝ := fun k => if k < r then gapAngle κ (F.lengths L) (k : ZMod n) else 0
  have hsmall : (∑ k ∈ Finset.range r, gapAngle κ (F.lengths L) (k : ZMod n)) =
      ∑ k ∈ Finset.range r, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [f, Finset.mem_range.1 hk]
  rw [hsmall, Finset.sum_subset (Finset.range_mono hr)]
  · rw [F.sum_range_selected]
    · apply Finset.sum_congr rfl
      intro j _
      change (if F.edge j < r then gapAngle κ (F.lengths L) (F.residue j) else 0) = _
      rw [F.gap_selected]
    · intro k hk hne
      simp [f, gapAngle, gapAngleAt,
        F.lengths_unselected L (F.residue_ne_of_nat_ne hk hne)]
  · intro k _ hkr
    simp only [Finset.mem_range, not_lt] at hkr
    simp [f, not_lt.mpr hkr]

end Frame

/-- The inclusive native heading is an incoming wrap half-angle plus a
prefix of edge gaps and the outgoing half-angle of the current edge. -/
lemma heading_eq_edge_gap_prefix {n : ℕ} (κ ℓ : ZMod n → ℝ) (j : ℕ) :
    heading κ ℓ j = Real.arcsin (κ 0 * (ℓ (-1) / 2)) +
      (∑ k ∈ Finset.range j, gapAngle κ ℓ (k : ZMod n)) +
      Real.arcsin (κ (j : ZMod n) * (ℓ (j : ZMod n) / 2)) := by
  induction j with
  | zero => simp [heading, turningAngle]
  | succ j ih =>
    rw [heading, Finset.sum_range_succ]
    change heading κ ℓ j + turningAngle 0 κ ℓ ((j + 1 : ℕ) : ZMod n) = _
    rw [ih, Finset.sum_range_succ]
    simp only [turningAngle, tK_zero, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      gapAngle, gapAngleAt]
    ring

namespace Frame

variable {n : ℕ} (F : Frame n)

/-- Heading relative to the first selected edge, using only original endpoint arcs. -/
noncomputable def relativeHeading (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  (∑ k : Fin 4, if k < j then F.startArc κ L k + F.finishArc κ L k else 0) +
    F.startArc κ L j - F.startArc κ L 0

/-- The actual collapsed-block turns. A block's interior readings disappear
only because the intervening edge lengths are zero. -/
noncomputable def turns (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![F.finishArc κ L 3 + F.startArc κ L 0,
    F.finishArc κ L 0 + F.startArc κ L 1,
    F.finishArc κ L 1 + F.startArc κ L 2,
    F.finishArc κ L 2 + F.startArc κ L 3]

@[simp] lemma relativeHeading_zero (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    F.relativeHeading κ L 0 = 0 := by
  simp [relativeHeading]

@[simp] lemma relativeHeading_one (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    F.relativeHeading κ L 1 = F.turns κ L 1 := by
  norm_num [relativeHeading, turns, Fin.sum_univ_four]
  ring

@[simp] lemma relativeHeading_two (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    F.relativeHeading κ L 2 = F.turns κ L 1 + F.turns κ L 2 := by
  norm_num [relativeHeading, turns, Fin.sum_univ_four]
  ring

@[simp] lemma relativeHeading_three (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    F.relativeHeading κ L 3 = F.turns κ L 1 + F.turns κ L 2 + F.turns κ L 3 := by
  norm_num [relativeHeading, turns, Fin.sum_univ_four]
  ring

/-- The native inclusive heading and the grouped slot heading differ by the
single heading of the first selected edge, with no full-turn hypothesis. -/
theorem heading_selected (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) (j : Fin 4) :
    heading κ (F.lengths L) (F.edge j) =
      heading κ (F.lengths L) (F.edge 0) + F.relativeHeading κ L j := by
  rw [heading_eq_edge_gap_prefix, heading_eq_edge_gap_prefix,
    F.sum_gap_prefix κ L (F.lt_n j).le,
    F.sum_gap_prefix κ L (F.lt_n 0).le]
  simp only [F.strictMono.lt_iff_lt, not_lt_zero, ite_false,
    Finset.sum_const_zero, add_zero]
  change _ + _ + Real.arcsin (F.start κ j * (F.lengths L (F.residue j) / 2)) =
    _ + Real.arcsin (F.start κ 0 * (F.lengths L (F.residue 0) / 2)) + _
  rw [F.lengths_selected, F.lengths_selected]
  simp only [mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)]
  unfold relativeHeading startArc
  ring

/-- The finite native slot controller, before embedding into the ambient word. -/
noncomputable def controller (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) : ℂ × ℝ :=
  let θ := F.turns κ L
  ((L 0 : ℂ) + (L 1 : ℂ) * unitPhase (θ 1) +
    (L 2 : ℂ) * unitPhase (θ 1 + θ 2) +
    (L 3 : ℂ) * unitPhase (θ 1 + θ 2 + θ 3),
    θ 0 + θ 1 + θ 2 + θ 3 - 2 * Real.pi)

theorem turningSum_eq_controller [NeZero n] (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    turningSum κ (F.lengths L) - 2 * Real.pi = (F.controller κ L).2 := by
  rw [F.turningSum_lengths, Fin.sum_univ_four]
  simp only [controller, turns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  ring

/-- Exact ambient closure, including both the full/half-length factor and
the heading gauge. This identity holds for every vector of four lengths. -/
theorem closureGap_eq_controller (κ : ZMod n → ℝ) (L : Fin 4 → ℝ) :
    closureGap κ (F.lengths L) =
      2 * unitPhase (heading κ (F.lengths L) (F.edge 0)) * (F.controller κ L).1 := by
  have hsum : closureGap κ (F.lengths L) =
      ∑ j : Fin 4, ((2 * L j : ℝ) : ℂ) *
        unitPhase (heading κ (F.lengths L) (F.edge j)) := by
    unfold closureGap vertexR2
    rw [F.sum_range_selected]
    · apply Finset.sum_congr rfl
      intro j _
      change (F.lengths L (F.residue j) : ℂ) * _ = _
      rw [F.lengths_selected]
      rfl
    · intro k hk hne
      rw [F.lengths_unselected L (F.residue_ne_of_nat_ne hk hne)]
      simp
  rw [hsum]
  calc
    _ = ∑ j : Fin 4, ((2 * L j : ℝ) : ℂ) *
        (unitPhase (heading κ (F.lengths L) (F.edge 0)) *
          unitPhase (F.relativeHeading κ L j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [F.heading_selected κ L j, unitPhase_add]
    _ = _ := by
      rw [Fin.sum_univ_four]
      have hzero : unitPhase 0 = 1 := by simp [unitPhase]
      simp only [F.relativeHeading_zero, F.relativeHeading_one, F.relativeHeading_two,
        F.relativeHeading_three, hzero, mul_one, controller,
        Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring

/-- Positivity and the eight actual selected-edge walls imply all ambient
nonnegative strict-cap bounds, including the dormant coordinates. -/
theorem lengths_nonneg_lt_edgeCap (κ : ZMod n → ℝ) (L : Fin 4 → ℝ)
    (hκ : ∀ i, 0 < κ i) (hL : ∀ j, 0 < L j)
    (hstart : ∀ j, F.start κ j * L j < 1)
    (hfinish : ∀ j, F.finish κ j * L j < 1) :
    ∀ i, 0 ≤ F.lengths L i ∧ F.lengths L i < edgeCap κ i := by
  intro i
  by_cases hi : ∃ j, i = F.residue j
  · obtain ⟨j, rfl⟩ := hi
    rw [F.lengths_selected]
    refine ⟨(mul_pos (by norm_num) (hL j)).le, ?_⟩
    have hm : 0 < max (κ (F.residue j)) (κ (F.residue j + 1)) :=
      lt_of_lt_of_le (hκ _) (le_max_left _ _)
    rw [edgeCap, lt_div_iff₀ hm]
    have hs := hstart j
    have hf := hfinish j
    change κ (F.residue j) * L j < 1 at hs
    change κ (F.residue j + 1) * L j < 1 at hf
    rcases le_total (κ (F.residue j)) (κ (F.residue j + 1)) with hh | hh
    · rw [max_eq_right hh]
      nlinarith
    · rw [max_eq_left hh]
      nlinarith
  · have hoff : ∀ j, i ≠ F.residue j := fun j he => hi ⟨j, he⟩
    rw [F.lengths_unselected L hoff]
    exact ⟨le_rfl, (edgeCap_pos (hκ _) (hκ _)).1⟩

/-- Linear insertion of the four active half-length coordinates. -/
noncomputable def lengthsLinearMap : (Fin 4 → ℝ) →ₗ[ℝ] (ZMod n → ℝ) where
  toFun := F.lengths
  map_add' L M := by
    funext i
    change (∑ j : Fin 4, if i = F.residue j then 2 * (L j + M j) else 0) =
      (∑ j : Fin 4, if i = F.residue j then 2 * L j else 0) +
      (∑ j : Fin 4, if i = F.residue j then 2 * M j else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  map_smul' c L := by
    funext i
    change (∑ j : Fin 4, if i = F.residue j then 2 * (c * L j) else 0) =
      c * (∑ j : Fin 4, if i = F.residue j then 2 * L j else 0)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring

/-- The active slice as a continuous linear map, ready for the chain rule. -/
noncomputable def lengthsCLM [NeZero n] : (Fin 4 → ℝ) →L[ℝ] (ZMod n → ℝ) :=
  F.lengthsLinearMap.toContinuousLinearMap

@[simp] lemma lengthsCLM_apply [NeZero n] (L : Fin 4 → ℝ) :
    F.lengthsCLM L = F.lengths L := rfl

/-- Every slice direction is supported on the positive active coordinates of
the anchor. Dormant edges cannot contribute to the transported rank. -/
theorem lengths_direction_supported (L v : Fin 4 → ℝ) (hL : ∀ j, 0 < L j)
    (i : ZMod n) (hi : F.lengths L i = 0) : F.lengths v i = 0 := by
  apply F.lengths_unselected
  intro j he
  rw [he, F.lengths_selected] at hi
  have := mul_pos (show (0 : ℝ) < 2 by norm_num) (hL j)
  linarith

/-- The concrete opposite-pure slot model agrees literally with the generic
controller when the selected actual edges have the stated endpoint readings. -/
theorem controller_eq_nativeLengthController
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1]) (L : Fin 4 → ℝ) :
    F.controller κ L = NativeOppositePure.nativeLengthController p t q h l L := by
  have hturn : F.turns κ L = NativeOppositePure.lengthTurns p t q h l L := by
    funext j
    fin_cases j <;>
      simp [turns, startArc, finishArc, hstart, hfinish, NativeOppositePure.lengthTurns]
  simp only [controller, NativeOppositePure.nativeLengthController, hturn]

/-- The ambient native controller on the active slice, in the exact opposite-pure
half-length convention. No closure or turning assumption is used. -/
theorem native_controller_embedding [NeZero n]
    {κ : ZMod n → ℝ} {p t q h l : ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1]) (L : Fin 4 → ℝ) :
    (closureGap κ (F.lengths L), turningSum κ (F.lengths L) - 2 * Real.pi) =
      (2 * unitPhase (heading κ (F.lengths L) (F.edge 0)) *
        (NativeOppositePure.nativeLengthController p t q h l L).1,
        (NativeOppositePure.nativeLengthController p t q h l L).2) := by
  rw [F.closureGap_eq_controller, F.turningSum_eq_controller,
    F.controller_eq_nativeLengthController hstart hfinish]

/-- At a zero of the grouped controller, differentiating its variable heading
rotation contributes no extra term. The active half-length columns map to the
actual ambient derivative with the displayed invertible output scaling. -/
theorem fderiv_lengths_at_controller_zero [NeZero n]
    {κ : ZMod n → ℝ} {L : Fin 4 → ℝ}
    (hκ : ∀ i, 0 < κ i)
    (hbounds : ∀ i, 0 ≤ F.lengths L i ∧ F.lengths L i < edgeCap κ i)
    (hd : DifferentiableAt ℝ (F.controller κ) L)
    (hzero : F.controller κ L = 0) (v : Fin 4 → ℝ) :
    fderiv ℝ (fun ell => closureMapR3 (κ, ell)) (F.lengths L) (F.lengths v) =
      (2 * unitPhase (heading κ (F.lengths L) (F.edge 0)) *
        (fderiv ℝ (F.controller κ) L v).1,
        (fderiv ℝ (F.controller κ) L v).2) := by
  let g : (Fin 4 → ℝ) → ℂ := fun X =>
    2 * unitPhase (heading κ (F.lengths X) (F.edge 0))
  have hw := strict_arc_walls_of_nonneg_lt_edgeCap hκ hbounds
  have hheading := contDiffAt_heading_lengths (F.edge 0)
    (fun j _ => hw (j : ZMod n))
  have hheading' : DifferentiableAt ℝ
      (fun X : Fin 4 → ℝ => heading κ (F.lengths X) (F.edge 0)) L := by
    exact (hheading.differentiableAt one_ne_zero).comp L F.lengthsCLM.differentiableAt
  have hg : DifferentiableAt ℝ g L := by
    dsimp [g, unitPhase]
    fun_prop
  have hprod := (hg.hasFDerivAt.mul hd.hasFDerivAt.fst).prodMk hd.hasFDerivAt.snd
  have hfun : (fun X : Fin 4 → ℝ => (g X * (F.controller κ X).1,
      (F.controller κ X).2)) = (fun X => closureMapR3 (κ, F.lengths X)) := by
    funext X
    apply Prod.ext
    · exact (F.closureGap_eq_controller κ X).symm
    · exact (F.turningSum_eq_controller κ X).symm
  change HasFDerivAt (fun X : Fin 4 → ℝ =>
    (g X * (F.controller κ X).1, (F.controller κ X).2)) _ L at hprod
  rw [hfun] at hprod
  have hamb := (lengthClosureMap_hasStrictFDerivAt_of_nonneg_lt_edgeCap hκ hbounds).hasFDerivAt
  have hcomp := hamb.comp L F.lengthsCLM.hasFDerivAt
  have heq := hcomp.unique hprod
  have hv := congrArg (fun A : (Fin 4 → ℝ) →L[ℝ] (ℂ × ℝ) => A v) heq
  simpa [g, ContinuousLinearMap.comp_apply, hzero, smul_eq_mul] using hv

/-- Surjectivity of the four-slot derivative is supported entirely on the
original nonzero edges; no dormant direction is used to supply rank. -/
theorem active_surj_of_controller_regular [NeZero n]
    {κ : ZMod n → ℝ} {L : Fin 4 → ℝ}
    (hκ : ∀ i, 0 < κ i) (hL : ∀ j, 0 < L j)
    (hbounds : ∀ i, 0 ≤ F.lengths L i ∧ F.lengths L i < edgeCap κ i)
    (hzero : F.controller κ L = 0)
    (hsurj : Function.Surjective (fderiv ℝ (F.controller κ) L)) :
    ∀ y : ℂ × ℝ, ∃ b : ZMod n → ℝ,
      fderiv ℝ (fun ell => closureMapR3 (κ, ell)) (F.lengths L) b = y ∧
        ∀ i, F.lengths L i = 0 → b i = 0 := by
  have hd : DifferentiableAt ℝ (F.controller κ) L := by
    by_contra hn
    rw [fderiv_zero_of_not_differentiableAt hn] at hsurj
    obtain ⟨v, hv⟩ := hsurj (0, 1)
    have := congrArg Prod.snd hv
    norm_num at this
  let g : ℂ := 2 * unitPhase (heading κ (F.lengths L) (F.edge 0))
  have hg : g ≠ 0 := mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  intro y
  obtain ⟨v, hv⟩ := hsurj (y.1 / g, y.2)
  refine ⟨F.lengths v, ?_, F.lengths_direction_supported L v hL⟩
  rw [F.fderiv_lengths_at_controller_zero hκ hbounds hd hzero, hv]
  change (g * (y.1 / g), y.2) = y
  rw [mul_div_cancel₀ _ hg]

/-- A regular strict four-slot anchor realizes the entire original cyclic
profile, including every arbitrarily long hidden block. -/
theorem realizesR2_of_controller_regular [NeZero n]
    {κ : ZMod n → ℝ} {L : Fin 4 → ℝ}
    (hκ : ∀ i, 0 < κ i) (hL : ∀ j, 0 < L j)
    (hstart : ∀ j, F.start κ j * L j < 1)
    (hfinish : ∀ j, F.finish κ j * L j < 1)
    (hzero : F.controller κ L = 0)
    (hsurj : Function.Surjective (fderiv ℝ (F.controller κ) L)) :
    RealizesR2 κ := by
  have hbounds := F.lengths_nonneg_lt_edgeCap κ L hκ hL hstart hfinish
  have h01 := F.strictMono (show (0 : Fin 4) < 1 by decide)
  have h12 := F.strictMono (show (1 : Fin 4) < 2 by decide)
  have h23 := F.strictMono (show (2 : Fin 4) < 3 by decide)
  have h3n := F.lt_n 3
  have hn : 3 ≤ n := by omega
  have hambzero : closureMapR3 (κ, F.lengths L) = 0 := by
    unfold closureMapR3
    rw [F.closureGap_eq_controller, F.turningSum_eq_controller, hzero]
    simp
  exact realizesR2_of_regular_dormant_anchor_of_active_surj hn hκ hbounds hambzero
    (F.active_surj_of_controller_regular hκ hL hbounds hzero hsurj)

/-- Concrete normalized opposite-pure consumer: a strict regular zero of
the native length controller opens four actual selected edges in any word. -/
theorem realizesR2_of_nativeLengthController_regular [NeZero n]
    {κ : ZMod n → ℝ} {p t q h l : ℝ} {L : Fin 4 → ℝ}
    (hstart : F.start κ = ![1, t, q, l])
    (hfinish : F.finish κ = ![p, q, h, 1])
    (hκ : ∀ i, 0 < κ i) (hL : ∀ j, 0 < L j)
    (hwstart : ∀ j, F.start κ j * L j < 1)
    (hwfinish : ∀ j, F.finish κ j * L j < 1)
    (hzero : NativeOppositePure.nativeLengthController p t q h l L = 0)
    (hsurj : Function.Surjective
      (fderiv ℝ (NativeOppositePure.nativeLengthController p t q h l) L)) :
    RealizesR2 κ := by
  have hfun : F.controller κ = NativeOppositePure.nativeLengthController p t q h l :=
    funext (F.controller_eq_nativeLengthController hstart hfinish)
  apply F.realizesR2_of_controller_regular hκ hL hwstart hwfinish
  · rwa [hfun]
  · rwa [hfun]

end Frame

end Gluck.Discrete.FourActiveSlots
