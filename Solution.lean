/-
Copyright (c) 2026 kejace. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kejace
-/
module

public import Gluck

/-!
# Comparator solution

The library `Gluck` proves the six theorems stated in `Challenge.lean` under the
same names. Comparator (`comparator.json`) checks that their statements, and
every definition they depend on, are identical to the challenge, that the
proofs use only `propext`, `Classical.choice` and `Quot.sound`, and that the
kernels accept them.
-/
