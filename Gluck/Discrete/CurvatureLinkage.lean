import Gluck.Discrete.ClosingCell

/-!
# Curvature-circle linkage transfers

This file records the local algebra behind the fixed-bar linkage associated to a
discrete curvature profile.  If consecutive curvature radii are `r` and `s`, an
edge of length `ell` has half-angles

`p = arcsin (ell / (2 * r))`, `q = arcsin (ell / (2 * s))`

and lifted cell angle `delta = p + q`.  With `y = exp (delta * I)`, the center-
and vertex-frame transfers are the affine maps

`z ↦ y*z + (r^2-s^2)*y/(s+r*y)` and
`z ↦ y*z + r*s*(y^2-1)/(s+r*y)`.

## Admissibility and the angle lift

The affine formulas alone are algebraic.  A geometric moderate cell must still
carry a *strictly positive* length in the chart domain

`ell ∈ Set.Ioo 0 (2 / max r⁻¹ s⁻¹)`.

Equivalently, its lifted angle lies in the corresponding strict `chartMap`
image.  In particular, a zero-length cell is only a compactification point and
is not an admissible polygon edge.  Moreover, `unitPhase` forgets multiples of
`2 * Real.pi`: cyclic polygon closure therefore requires the separate real-lift
condition that the sum of the cell angles is exactly `2 * Real.pi`; an affine
product equal to the identity does not by itself prove that condition.

## Reversal caveat

The reversal lemmas below are identities of affine maps.  They replace `y` by
`y⁻¹`; for `y = unitPhase delta` this represents the negative lift `-delta`.
Since an admissible moderate cell has `0 < delta < Real.pi`, algebraic reversal
does **not** construct another positive chart cell and cannot be used as a
positive geometric insertion without an additional argument.
-/

namespace Gluck.Discrete

/-- The common denominator `s + r*y` in both local linkage transfers. -/
def linkageDen (r s : ℝ) (y : ℂ) : ℂ := (s : ℂ) + (r : ℂ) * y

/-- Translation coefficient of the local center-frame transfer. -/
noncomputable def centerCoeff (r s : ℝ) (y : ℂ) : ℂ :=
  ((r ^ 2 - s ^ 2 : ℝ) : ℂ) * y / linkageDen r s y

/-- Translation coefficient of the local vertex-frame transfer. -/
noncomputable def vertexCoeff (r s : ℝ) (y : ℂ) : ℂ :=
  ((r * s : ℝ) : ℂ) * (y ^ 2 - 1) / linkageDen r s y

/-- The unit complex phase `exp (delta * I)` of a real lifted angle. -/
noncomputable def unitPhase (delta : ℝ) : ℂ :=
  Complex.exp ((delta : ℂ) * Complex.I)

/-- The half-angle subtended by a chord of length `ell` in a circle of radius `r`. -/
noncomputable def radiusHalfAngle (r ell : ℝ) : ℝ :=
  Real.arcsin (ell / (2 * r))

/-- The lifted rotation angle of one linkage cell. -/
noncomputable def linkageAngle (r s ell : ℝ) : ℝ :=
  radiusHalfAngle r ell + radiusHalfAngle s ell

/-- The unit phase of the lifted rotation angle of one linkage cell. -/
noncomputable def linkagePhase (r s ell : ℝ) : ℂ :=
  unitPhase (linkageAngle r s ell)

/-- A complex affine map `z ↦ linear * z + shift`. -/
@[ext] structure LinkageAffine where
  linear : ℂ
  shift : ℂ

def LinkageAffine.one : LinkageAffine := ⟨1, 0⟩

/-- Composition of affine maps: `comp g h` applies `h` first and then `g`. -/
def LinkageAffine.comp (g h : LinkageAffine) : LinkageAffine :=
  ⟨g.linear * h.linear, g.shift + g.linear * h.shift⟩

noncomputable def LinkageAffine.inv (g : LinkageAffine) : LinkageAffine :=
  ⟨g.linear⁻¹, -g.linear⁻¹ * g.shift⟩

/-- The local center-frame affine transfer. -/
noncomputable def centerTransfer (r s : ℝ) (y : ℂ) : LinkageAffine :=
  ⟨y, centerCoeff r s y⟩

/-- The local vertex-frame affine transfer. -/
noncomputable def vertexTransfer (r s : ℝ) (y : ℂ) : LinkageAffine :=
  ⟨y, vertexCoeff r s y⟩

/-- Translation by a real radius, used to change between center and vertex gauges. -/
def radiusGauge (r : ℝ) : LinkageAffine := ⟨1, r⟩

lemma LinkageAffine.comp_assoc (f g h : LinkageAffine) :
    LinkageAffine.comp (LinkageAffine.comp f g) h
      = LinkageAffine.comp f (LinkageAffine.comp g h) := by
  ext <;> simp [LinkageAffine.comp] <;> ring

@[simp] lemma LinkageAffine.one_comp (g : LinkageAffine) :
    LinkageAffine.comp LinkageAffine.one g = g := by
  ext <;> simp [LinkageAffine.comp, LinkageAffine.one]

@[simp] lemma LinkageAffine.comp_one (g : LinkageAffine) :
    LinkageAffine.comp g LinkageAffine.one = g := by
  ext <;> simp [LinkageAffine.comp, LinkageAffine.one]

lemma LinkageAffine.pose_comp_eq_self_iff {p g : LinkageAffine}
    (hp : p.linear ≠ 0) : LinkageAffine.comp p g = p ↔ g = LinkageAffine.one := by
  constructor
  · intro h
    have hlinear : p.linear * g.linear = p.linear := by
      exact congrArg LinkageAffine.linear h
    have hglinear : g.linear = 1 := by
      apply (mul_left_cancel₀ hp)
      simpa using hlinear
    have hshift : p.shift + p.linear * g.shift = p.shift := by
      exact congrArg LinkageAffine.shift h
    have hgshift : g.shift = 0 := by
      have hzero : p.shift + p.linear * g.shift - p.shift = 0 := sub_eq_zero.mpr hshift
      have : p.linear * g.shift = 0 := by simpa [add_sub_cancel_left] using hzero
      exact (mul_eq_zero.mp this).resolve_left hp
    ext
    · simpa [LinkageAffine.one] using hglinear
    · simpa [LinkageAffine.one] using hgshift
  · rintro rfl
    exact LinkageAffine.comp_one p

lemma LinkageAffine.right_radiusGauge_eq_iff (p q : LinkageAffine) (r : ℝ) :
    LinkageAffine.comp p (radiusGauge r) = LinkageAffine.comp q (radiusGauge r)
      ↔ p = q := by
  constructor
  · intro h
    have hlinear : p.linear = q.linear := by
      simpa [LinkageAffine.comp, radiusGauge] using congrArg LinkageAffine.linear h
    have hshift := congrArg LinkageAffine.shift h
    ext
    · exact hlinear
    · simpa [LinkageAffine.comp, radiusGauge, hlinear] using hshift
  · rintro rfl
    rfl

/-- Ordered composition of a list of transfers. -/
def LinkageAffine.product : List LinkageAffine → LinkageAffine
  | [] => LinkageAffine.one
  | g :: gs => LinkageAffine.comp g (LinkageAffine.product gs)

/-- The expanded translation part of an ordered affine product. -/
def LinkageAffine.weightedShift : List LinkageAffine → ℂ
  | [] => 0
  | g :: gs => g.shift + g.linear * LinkageAffine.weightedShift gs

/-- Concatenating two transfer chains composes their affine products. -/
lemma LinkageAffine.product_append (gs hs : List LinkageAffine) :
    LinkageAffine.product (gs ++ hs) =
      LinkageAffine.comp (LinkageAffine.product gs) (LinkageAffine.product hs) := by
  induction gs with
  | nil => simp [LinkageAffine.product]
  | cons g gs ih => simp [LinkageAffine.product, ih, LinkageAffine.comp_assoc]

@[simp] lemma LinkageAffine.product_linear (gs : List LinkageAffine) :
    (LinkageAffine.product gs).linear = (gs.map LinkageAffine.linear).prod := by
  induction gs with
  | nil => simp [LinkageAffine.product, LinkageAffine.one]
  | cons g gs ih => simp [LinkageAffine.product, LinkageAffine.comp, ih]

@[simp] lemma LinkageAffine.product_shift (gs : List LinkageAffine) :
    (LinkageAffine.product gs).shift = LinkageAffine.weightedShift gs := by
  induction gs with
  | nil => simp [LinkageAffine.product, LinkageAffine.one, LinkageAffine.weightedShift]
  | cons g gs ih => simp [LinkageAffine.product, LinkageAffine.comp,
      LinkageAffine.weightedShift, ih]

/-- The translation of a concatenated chain is the first translation plus its
linear part times the second translation. -/
lemma LinkageAffine.weightedShift_append (gs hs : List LinkageAffine) :
    LinkageAffine.weightedShift (gs ++ hs) =
      LinkageAffine.weightedShift gs +
        (gs.map LinkageAffine.linear).prod * LinkageAffine.weightedShift hs := by
  have h := congrArg LinkageAffine.shift (LinkageAffine.product_append gs hs)
  simpa [LinkageAffine.comp] using h

lemma LinkageAffine.product_eq_one_iff (gs : List LinkageAffine) :
    LinkageAffine.product gs = LinkageAffine.one ↔
      (gs.map LinkageAffine.linear).prod = 1 ∧
        LinkageAffine.weightedShift gs = 0 := by
  constructor
  · intro h
    constructor
    · simpa [LinkageAffine.one] using congrArg LinkageAffine.linear h
    · simpa [LinkageAffine.one] using congrArg LinkageAffine.shift h
  · rintro ⟨hlinear, hshift⟩
    ext
    · simpa [LinkageAffine.one] using hlinear
    · simpa [LinkageAffine.one] using hshift

lemma LinkageAffine.center_vertex_endpoint_closure_iff
    (p g : LinkageAffine) (r : ℝ) :
    LinkageAffine.comp (LinkageAffine.comp p g) (radiusGauge r)
        = LinkageAffine.comp p (radiusGauge r)
      ↔ LinkageAffine.comp p g = p := by
  exact LinkageAffine.right_radiusGauge_eq_iff (LinkageAffine.comp p g) p r

lemma LinkageAffine.cyclic_frame_closure_iff {p : LinkageAffine}
    (hp : p.linear ≠ 0) (g : LinkageAffine) (r : ℝ) :
    LinkageAffine.comp (LinkageAffine.comp p g) (radiusGauge r)
        = LinkageAffine.comp p (radiusGauge r)
      ↔ g = LinkageAffine.one := by
  rw [LinkageAffine.center_vertex_endpoint_closure_iff,
    LinkageAffine.pose_comp_eq_self_iff hp]

lemma radiusHalfAngle_pos {r ell : ℝ} (hr : 0 < r) (hell : 0 < ell) :
    0 < radiusHalfAngle r ell := by
  exact Real.arcsin_pos.2 (div_pos hell (mul_pos two_pos hr))

lemma radiusHalfAngle_lt_pi_div_two {r ell : ℝ} (hr : 0 < r)
    (hell : ell < 2 * r) : radiusHalfAngle r ell < Real.pi / 2 := by
  apply Real.arcsin_lt_pi_div_two.2
  exact (div_lt_one (mul_pos two_pos hr)).2 hell

lemma radius_sin_halfAngle {r ell : ℝ} (hr : 0 < r) (hell0 : 0 ≤ ell)
    (hell : ell ≤ 2 * r) : r * Real.sin (radiusHalfAngle r ell) = ell / 2 := by
  have harg0 : 0 ≤ ell / (2 * r) := div_nonneg hell0 (mul_pos two_pos hr).le
  have harg1 : ell / (2 * r) ≤ 1 := (div_le_one (mul_pos two_pos hr)).2 hell
  rw [radiusHalfAngle, Real.sin_arcsin (by linarith) harg1]
  field_simp [hr.ne']

lemma radius_halfAngle_chord {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 ≤ ell) (hellr : ell ≤ 2 * r) (hells : ell ≤ 2 * s) :
    r * Real.sin (radiusHalfAngle r ell)
      = s * Real.sin (radiusHalfAngle s ell) := by
  rw [radius_sin_halfAngle hr hell0 hellr, radius_sin_halfAngle hs hell0 hells]

lemma linkageAngle_eq_chartMap {r s ell : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    linkageAngle r s ell = chartMap r⁻¹ s⁻¹ ell := by
  unfold linkageAngle radiusHalfAngle chartMap
  apply congrArg₂ (· + ·)
  · congr 1
    field_simp [hr]
  · congr 1
    field_simp [hs]

/-- A strictly positive, strictly sub-wall edge has its lifted linkage angle in
the strict single-edge chart image.  This statement deliberately retains the
length witness instead of passing only to its phase. -/
lemma linkageAngle_mem_chartImage {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hwall : ell < 2 / max r⁻¹ s⁻¹) :
    linkageAngle r s ell ∈
      chartMap r⁻¹ s⁻¹ '' Set.Ioo (0 : ℝ) (2 / max r⁻¹ s⁻¹) := by
  refine ⟨ell, ⟨hell0, hwall⟩, ?_⟩
  exact (linkageAngle_eq_chartMap hr.ne' hs.ne').symm

lemma linkageAngle_pos {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell : 0 < ell) : 0 < linkageAngle r s ell := by
  exact add_pos (radiusHalfAngle_pos hr hell) (radiusHalfAngle_pos hs hell)

lemma linkageAngle_lt_pi {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hellr : ell < 2 * r) (hells : ell < 2 * s) : linkageAngle r s ell < Real.pi := by
  have hp := radiusHalfAngle_lt_pi_div_two hr hellr
  have hq := radiusHalfAngle_lt_pi_div_two hs hells
  unfold linkageAngle
  linarith

@[simp] lemma norm_unitPhase (delta : ℝ) : ‖unitPhase delta‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

@[simp] lemma linkagePhase_norm (r s ell : ℝ) : ‖linkagePhase r s ell‖ = 1 := by
  simp [linkagePhase]

lemma unitPhase_eq_cos_add_sin_mul_I (delta : ℝ) :
    unitPhase delta = (Real.cos delta : ℂ) + (Real.sin delta : ℂ) * Complex.I := by
  exact Complex.exp_ofReal_mul_I delta

lemma unitPhase_add (a b : ℝ) : unitPhase (a + b) = unitPhase a * unitPhase b := by
  rw [unitPhase, unitPhase, unitPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The complex phase forgets one full turn.  Geometric closure must therefore
carry the real angle-sum lift separately. -/
lemma unitPhase_add_two_pi (delta : ℝ) :
    unitPhase (delta + 2 * Real.pi) = unitPhase delta := by
  simpa [unitPhase] using Complex.exp_mul_I_periodic (delta : ℂ)

lemma unitPhase_sub (a b : ℝ) : unitPhase (a - b) = unitPhase a * unitPhase (-b) := by
  rw [show a - b = a + -b by ring, unitPhase_add]

lemma unitPhase_sub_neg (a : ℝ) :
    unitPhase a - unitPhase (-a) = 2 * Complex.I * (Real.sin a : ℂ) := by
  rw [unitPhase_eq_cos_add_sin_mul_I, unitPhase_eq_cos_add_sin_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

lemma unitPhase_add_sub (p q : ℝ) :
    unitPhase (p + q) - unitPhase (p - q)
      = 2 * Complex.I * (Real.sin q : ℂ) * unitPhase p := by
  rw [unitPhase_add, unitPhase_sub]
  rw [← mul_sub]
  rw [unitPhase_sub_neg]
  ring

lemma one_sub_unitPhase_two (p : ℝ) :
    1 - unitPhase (2 * p) = -2 * Complex.I * (Real.sin p : ℂ) * unitPhase p := by
  have h := unitPhase_sub_neg p
  rw [show unitPhase (2 * p) = unitPhase p * unitPhase p by
    rw [← unitPhase_add]
    congr 1
    ring]
  have hmul := congrArg (fun z : ℂ => z * unitPhase p) h
  rw [sub_mul] at hmul
  have hnorm : unitPhase (-p) * unitPhase p = 1 := by
    rw [← unitPhase_add]
    simp [unitPhase]
  rw [hnorm] at hmul
  linear_combination -hmul

@[simp] lemma unitPhase_re (delta : ℝ) : (unitPhase delta).re = Real.cos delta := by
  simp [unitPhase, Complex.exp_ofReal_mul_I_re]

@[simp] lemma unitPhase_im (delta : ℝ) : (unitPhase delta).im = Real.sin delta := by
  simp [unitPhase, Complex.exp_ofReal_mul_I_im]

lemma linkageDen_im (r s delta : ℝ) :
    (linkageDen r s (unitPhase delta)).im = r * Real.sin delta := by
  simp [linkageDen, Complex.mul_im]

lemma linkageDen_ne_zero_of_angle {r s delta : ℝ} (hr : 0 < r)
    (hd0 : 0 < delta) (hdpi : delta < Real.pi) :
    linkageDen r s (unitPhase delta) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  rw [linkageDen_im, Complex.zero_im] at him
  exact (mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hd0 hdpi)).ne' him

lemma linkageDen_ne_zero_of_length {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hellr : ell < 2 * r) (hells : ell < 2 * s) :
    linkageDen r s (linkagePhase r s ell) ≠ 0 := by
  exact linkageDen_ne_zero_of_angle hr (linkageAngle_pos hr hs hell0)
    (linkageAngle_lt_pi hr hs hellr hells)

lemma linkagePhase_im_pos {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hellr : ell < 2 * r) (hells : ell < 2 * s) :
    0 < (linkagePhase r s ell).im := by
  rw [linkagePhase, unitPhase_im]
  exact Real.sin_pos_of_pos_of_lt_pi (linkageAngle_pos hr hs hell0)
    (linkageAngle_lt_pi hr hs hellr hells)

lemma unitPhase_ne_one_of_angle {delta : ℝ} (hd0 : 0 < delta)
    (hdpi : delta < Real.pi) : unitPhase delta ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  rw [unitPhase_im, Complex.one_im] at him
  exact (Real.sin_pos_of_pos_of_lt_pi hd0 hdpi).ne' him

lemma unitPhase_ne_neg_one_of_angle {delta : ℝ} (hd0 : 0 < delta)
    (hdpi : delta < Real.pi) : unitPhase delta ≠ -1 := by
  intro h
  have him := congrArg Complex.im h
  rw [unitPhase_im] at him
  norm_num at him
  exact (Real.sin_pos_of_pos_of_lt_pi hd0 hdpi).ne' him

lemma unitPhase_sq_ne_one_of_angle {delta : ℝ} (hd0 : 0 < delta)
    (hdpi : delta < Real.pi) : unitPhase delta ^ 2 ≠ 1 := by
  intro h
  have hfac : (unitPhase delta - 1) * (unitPhase delta + 1) = 0 := by
    calc
      (unitPhase delta - 1) * (unitPhase delta + 1)
          = unitPhase delta ^ 2 - 1 := by ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact unitPhase_ne_one_of_angle hd0 hdpi (sub_eq_zero.mp h1)
  · exact unitPhase_ne_neg_one_of_angle hd0 hdpi (add_eq_zero_iff_eq_neg.mp h1)

lemma vertexCoeff_ne_zero_of_angle {r s delta : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hd0 : 0 < delta) (hdpi : delta < Real.pi) :
    vertexCoeff r s (unitPhase delta) ≠ 0 := by
  rw [vertexCoeff]
  exact div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero hr.ne' hs.ne'))
      (sub_ne_zero.mpr (unitPhase_sq_ne_one_of_angle hd0 hdpi)))
    (linkageDen_ne_zero_of_angle hr hd0 hdpi)

lemma vertexCoeff_eq_centerCoeff_add (r s : ℝ) (y : ℂ)
    (hden : linkageDen r s y ≠ 0) :
    vertexCoeff r s y = centerCoeff r s y + (s : ℂ) * y - r := by
  rw [vertexCoeff, centerCoeff]
  apply (div_eq_iff hden).2
  rw [sub_mul, add_mul, div_mul_cancel₀ _ hden]
  simp only [linkageDen]
  push_cast
  ring

/-- A collapsed (zero-angle) cell does not move its vertex frame.  This is an
algebraic compactification identity; it does not make a zero edge admissible. -/
@[simp] lemma vertexCoeff_one (r s : ℝ) : vertexCoeff r s 1 = 0 := by
  simp [vertexCoeff]

/-- At phase one the center-frame displacement is `r-s`, provided the two
positive-radius terms do not cancel in the denominator. -/
lemma centerCoeff_one_of_add_ne_zero (r s : ℝ) (hrs : r + s ≠ 0) :
    centerCoeff r s 1 = (r : ℂ) - s := by
  unfold centerCoeff linkageDen
  have hden : (s : ℂ) + (r : ℂ) ≠ 0 := by
    exact_mod_cast (show s + r ≠ 0 by simpa [add_comm] using hrs)
  field_simp [hden]
  push_cast
  ring

@[simp] lemma centerCoeff_self (r : ℝ) (y : ℂ) : centerCoeff r r y = 0 := by
  simp [centerCoeff]

lemma vertexCoeff_self {r : ℝ} (hr : r ≠ 0) {y : ℂ} (hy : y ≠ -1) :
    vertexCoeff r r y = (r : ℂ) * (y - 1) := by
  have hden : linkageDen r r y ≠ 0 := by
    have hy' : (1 : ℂ) + y ≠ 0 := by
      intro h
      apply hy
      linear_combination h
    rw [show linkageDen r r y = (r : ℂ) * (1 + y) by
      simp only [linkageDen]
      ring]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hy'
  rw [vertexCoeff_eq_centerCoeff_add r r y hden, centerCoeff_self]
  ring

lemma linkageAngle_self (r ell : ℝ) :
    linkageAngle r r ell = 2 * radiusHalfAngle r ell := by
  simp [linkageAngle, two_mul]

/-- The vertex and center transfers differ by their endpoint radius gauges. -/
lemma vertexTransfer_eq_gauge_center_gauge (r s : ℝ) (y : ℂ)
    (hden : linkageDen r s y ≠ 0) :
    LinkageAffine.comp
        (LinkageAffine.comp (radiusGauge (-r)) (centerTransfer r s y))
        (radiusGauge s)
      = vertexTransfer r s y := by
  ext
  · simp [LinkageAffine.comp, radiusGauge, centerTransfer, vertexTransfer]
  · simp only [LinkageAffine.comp, radiusGauge, centerTransfer, vertexTransfer]
    rw [vertexCoeff_eq_centerCoeff_add r s y hden]
    push_cast
    ring

lemma centerCoeff_reverse (r s : ℝ) (y : ℂ) (hy : y ≠ 0)
    (hden : linkageDen r s y ≠ 0) :
    centerCoeff s r y⁻¹ = -y⁻¹ * centerCoeff r s y := by
  unfold centerCoeff linkageDen
  have hden' : (r : ℂ) + (s : ℂ) * y⁻¹ ≠ 0 := by
    intro h
    apply hden
    have h' : y * ((r : ℂ) + (s : ℂ) * y⁻¹) = 0 := by rw [h, mul_zero]
    calc
      (s : ℂ) + (r : ℂ) * y = y * ((r : ℂ) + (s : ℂ) * y⁻¹) := by
        field_simp [hy]
        ring
      _ = 0 := h'
  field_simp [hy, hden, hden']
  push_cast
  ring

lemma vertexCoeff_reverse (r s : ℝ) (y : ℂ) (hy : y ≠ 0)
    (hden : linkageDen r s y ≠ 0) :
    vertexCoeff s r y⁻¹ = -y⁻¹ * vertexCoeff r s y := by
  unfold vertexCoeff linkageDen
  have hden' : (r : ℂ) + (s : ℂ) * y⁻¹ ≠ 0 := by
    intro h
    apply hden
    have h' : y * ((r : ℂ) + (s : ℂ) * y⁻¹) = 0 := by rw [h, mul_zero]
    calc
      (s : ℂ) + (r : ℂ) * y = y * ((r : ℂ) + (s : ℂ) * y⁻¹) := by
        field_simp [hy]
        ring
      _ = 0 := h'
  field_simp [hy, hden, hden']
  ring

/-- Algebraic reversal for the center transfer.  See the module-level warning:
`y⁻¹` normally has a negative angle lift and is not a positive chart cell. -/
lemma centerTransfer_reverse_eq_inv (r s : ℝ) (y : ℂ) (hy : y ≠ 0)
    (hden : linkageDen r s y ≠ 0) :
    centerTransfer s r y⁻¹ = LinkageAffine.inv (centerTransfer r s y) := by
  ext
  · rfl
  · exact centerCoeff_reverse r s y hy hden

/-- Algebraic reversal for the vertex transfer.  This is not, by itself, an
admissible positive-edge reversal theorem. -/
lemma vertexTransfer_reverse_eq_inv (r s : ℝ) (y : ℂ) (hy : y ≠ 0)
    (hden : linkageDen r s y ≠ 0) :
    vertexTransfer s r y⁻¹ = LinkageAffine.inv (vertexTransfer r s y) := by
  ext
  · rfl
  · exact vertexCoeff_reverse r s y hy hden

lemma centerCoeff_eq_direct {r s p q : ℝ}
    (hchord : r * Real.sin p = s * Real.sin q)
    (hden : linkageDen r s (unitPhase (p + q)) ≠ 0) :
    centerCoeff r s (unitPhase (p + q))
      = (r : ℂ) - (s : ℂ) * unitPhase (p - q) := by
  have hxy : unitPhase (p - q) * unitPhase (p + q) = unitPhase (2 * p) := by
    rw [← unitPhase_add]
    congr 1
    ring
  have hyx := unitPhase_add_sub p q
  have hp2 := one_sub_unitPhase_two p
  have hchordC : (r : ℂ) * (Real.sin p : ℂ) = (s : ℂ) * (Real.sin q : ℂ) := by
    exact_mod_cast hchord
  have hzero : (s : ℂ) * ((s : ℂ) * (unitPhase (p - q) - unitPhase (p + q))
      + (r : ℂ) * (unitPhase (p - q) * unitPhase (p + q) - 1)) = 0 := by
    rw [hxy, show unitPhase (p - q) - unitPhase (p + q)
        = -(unitPhase (p + q) - unitPhase (p - q)) by ring, hyx,
      show unitPhase (2 * p) - 1 = -(1 - unitPhase (2 * p)) by ring, hp2]
    linear_combination (2 * Complex.I * unitPhase p * (s : ℂ)) * hchordC
  rw [centerCoeff]
  apply (div_eq_iff hden).2
  simp only [linkageDen]
  calc
    ((r ^ 2 - s ^ 2 : ℝ) : ℂ) * unitPhase (p + q)
        = ((r : ℂ) - (s : ℂ) * unitPhase (p - q)) *
            ((s : ℂ) + (r : ℂ) * unitPhase (p + q)) +
          (s : ℂ) * ((s : ℂ) * (unitPhase (p - q) - unitPhase (p + q))
            + (r : ℂ) * (unitPhase (p - q) * unitPhase (p + q) - 1)) := by
              push_cast
              ring
    _ = _ := by rw [hzero, add_zero]

lemma vertexCoeff_eq_chord {r s p q ell : ℝ}
    (hchord : r * Real.sin p = s * Real.sin q)
    (hell : ell = 2 * r * Real.sin p)
    (hden : linkageDen r s (unitPhase (p + q)) ≠ 0) :
    vertexCoeff r s (unitPhase (p + q))
      = Complex.I * (ell : ℂ) * unitPhase p := by
  have hyx := unitPhase_add_sub p q
  have hchordC : (r : ℂ) * (Real.sin p : ℂ) = (s : ℂ) * (Real.sin q : ℂ) := by
    exact_mod_cast hchord
  rw [vertexCoeff_eq_centerCoeff_add _ _ _ hden,
    centerCoeff_eq_direct hchord hden, hell]
  rw [show (r : ℂ) - (s : ℂ) * unitPhase (p - q) +
      (s : ℂ) * unitPhase (p + q) - r
        = (s : ℂ) * (unitPhase (p + q) - unitPhase (p - q)) by ring, hyx]
  rw [show ((2 * r * Real.sin p : ℝ) : ℂ)
      = 2 * (r : ℂ) * (Real.sin p : ℂ) by push_cast; ring]
  calc
    (s : ℂ) * (2 * Complex.I * (Real.sin q : ℂ) * unitPhase p)
        = 2 * Complex.I * ((s : ℂ) * (Real.sin q : ℂ)) * unitPhase p := by ring
    _ = 2 * Complex.I * ((r : ℂ) * (Real.sin p : ℂ)) * unitPhase p := by
      rw [hchordC]
    _ = Complex.I * (2 * (r : ℂ) * (Real.sin p : ℂ)) * unitPhase p := by ring

lemma vertexCoeff_eq_length_frame {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hellr : ell < 2 * r) (hells : ell < 2 * s) :
    vertexCoeff r s (linkagePhase r s ell)
      = Complex.I * (ell : ℂ) * unitPhase (radiusHalfAngle r ell) := by
  have hchord := radius_halfAngle_chord hr hs hell0.le hellr.le hells.le
  have hsin := radius_sin_halfAngle hr hell0.le hellr.le
  have hell : ell = 2 * r * Real.sin (radiusHalfAngle r ell) := by linarith
  simpa only [linkagePhase, linkageAngle] using
    (vertexCoeff_eq_chord hchord hell
      (linkageDen_ne_zero_of_length hr hs hell0 hellr hells))

lemma norm_vertexCoeff_eq_length {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hellr : ell < 2 * r) (hells : ell < 2 * s) :
    ‖vertexCoeff r s (linkagePhase r s ell)‖ = ell := by
  rw [vertexCoeff_eq_length_frame hr hs hell0 hellr hells]
  simp [abs_of_pos hell0]

lemma vertexCoeff_ne_zero_of_length {r s ell : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hell0 : 0 < ell) (hellr : ell < 2 * r) (hells : ell < 2 * s) :
    vertexCoeff r s (linkagePhase r s ell) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_vertexCoeff_eq_length hr hs hell0 hellr hells]
  exact hell0.ne'

end Gluck.Discrete
