/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import algebra.periodic
import data.nat.interval

/-!
# Periodic Functions on ℕ

This file identifies a few functions which are periodic, and also proves a lemma about periodic predicates which helps determine their cardinality when filtering intervals over them.
-/

open finset nat function

lemma periodic_gcd (a : ℕ) : periodic (gcd a) a := by simp

lemma periodic_coprime (a : ℕ) : periodic (coprime a) a := by simp

-- TODO? Generalize from ℕ
-- Note that this does not hold for locally finitely ordered add_monoids in general,
-- as we could have a (horizontally) periodic function on ℤ² which is different over different
-- y-coordinates. It should hold over ℤ though.
/-- An interval of length `a` filtered over a periodic predicate of period `a` has the
same cardinality as `range a` filtered over that predicate. -/
@[simp] lemma filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [decidable_pred p]
 (pp : function.periodic p a) :
  (filter p (Ico n (n+a))).card = a.count p :=
begin
  by_cases a = 0,
  { simp [h], },
  induction n,
  { simp [count_eq_card_filter_range], },
  { rw ←n_ih,
    clear n_ih,
    simp only [succ_add],
    rw Ico_succ_right_eq_insert_Ico,
    { rw [Ico_succ_left_eq_erase_Ico, filter_insert, filter_erase],
      split_ifs,
      { rw [card_insert_eq_ite, card_erase_eq_ite],
        split_ifs,
        { simp [*] at *, },
        { simp [*] at *, },
        { rw [add_one, succ_pred_eq_of_pos],
          rw [card_pos, finset.nonempty],
          use n_n,
          assumption, },
        { simp [mem_filter] at *,
          rw pp at h_1,
          exact h_3 (pos_iff_ne_zero.mpr h) h_1, }, },
      { rw card_erase_eq_ite,
        split_ifs,
        simp [*] at *, }, },
    { rwa [succ_eq_add_one, add_le_add_iff_left, one_le_iff_ne_zero], }, },
end
