/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/

import data.nat.prime
import data.finset.interval
import data.nat.multiplicity
import data.nat.choose.sum
import number_theory.padics.padic_norm
import data.complex.exponential_bounds
import ring_theory.multiplicity
import algebra.module
import number_theory.primorial
import analysis.special_functions.pow
import analysis.special_functions.sqrt
import analysis.calculus.local_extr
import data.real.basic
import data.real.sqrt
import data.real.nnreal

/-!
# Bertrand's Postulate

This file contains a proof of Bertrand's postulate: That between any positive number and its
double there is a prime

-- TODO File Docstring
-- TODO Cite "Proofs From THE BOOK"
-/

open_locale big_operators



/-- The multiplicity of p in the nth central binomial coefficient-/
private def α (n p : nat) [hp : fact p.prime] : nat :=
padic_val_nat p ((2 * n).choose n)

lemma nat.self_le_mul {m : ℕ} : ∀ {n : ℕ} (n0 : 0 < n), m ≤ n * m
| 0     h := (lt_irrefl _ h).elim
| 1     h := (one_mul m).symm.le
| (n+2) h := trans (nat.self_le_mul n.succ_pos) $ mul_le_mul_right' n.succ.le_succ _

lemma nat.le_two_mul_self (n : ℕ) : n ≤ 2 * n :=
nat.self_le_mul zero_lt_two

lemma central_binom_nonzero (n : ℕ) : (2 * n).choose n ≠ 0 :=
(nat.choose_pos n.le_two_mul_self).ne'

lemma claim_1
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  : p ^ (α n p) ≤ 2 * n
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1)
                        (hp.out) n.le_two_mul_self (lt_add_one (p.log (2 * n)))],
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n: congr_arg (flip (has_sub.sub) n) (two_mul n)
    ... = n: nat.add_sub_cancel n n,
  simp [r, ←two_mul],
  apply trans (pow_le_pow (trans one_le_two hp.out.two_le) _) (_ : p ^ p.log (2 * n) ≤ 2 * n),
  { calc _  ≤ (finset.Ico 1 (nat.log p (2 * n) + 1)).card : finset.card_filter_le _ _
        ... = (p.log (2 * n) + 1) - 1                     : nat.card_Ico _ _ },
  { apply nat.pow_log_le_self,
    exact hp.out.one_lt,
    linarith, }
end

lemma claim_2
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 3 ≤ n)
  (smallish : (2 * n) < p ^ 2)
  : (α n p) ≤ 1
  :=
nat.le_of_lt_succ $ (pow_lt_pow_iff hp.out.one_lt).1 $
  calc p ^ α n p ≤ 2 * n : claim_1 p n n_big
             ... < p ^ 2 : smallish

lemma twice_nat_small (n : nat) (h : 2 * n < 2) : n = 0 :=
nat.le_zero_iff.mp $ nat.le_of_lt_succ $
  lt_of_mul_lt_mul_left (h.trans_le (mul_one _).symm.le) (nat.zero_le _)

lemma claim_3
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 6 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : α n p = 0
  :=
begin
  unfold α,
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n),
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1)
                        (hp.out) n.le_two_mul_self (lt_add_one (p.log (2 * n)))],
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
               ... = n         : nat.add_sub_cancel n n,
  simp only [r, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable],
  clear r,

  let p_pos : 0 < p := trans zero_lt_one hp.out.one_lt,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.mem_Ico at i_in_interval,
  have three_lt_p : 3 ≤ p ,
  { rcases le_or_lt 3 p with H|H,
    { exact H, },
    { refine (lt_irrefl 12 _).elim,
      calc 12 = 2 * 6 : rfl
        ... < 2 * n   : (mul_lt_mul_left zero_lt_two).2 n_big
        ... < 3 * p   : big
        ... < 3 * 3   : (mul_lt_mul_left zero_lt_three).2 H
        ... = 9       : rfl
        ... < 12      : nat.lt_of_sub_eq_succ rfl } },

  refine not_le.mpr _,

  rcases lt_trichotomy 1 i with H|rfl|H,
  { have two_le_i : 2 ≤ i := nat.succ_le_of_lt H,
    have two_n_lt_pow_p_i : 2 * n < p ^ i,
    { calc 2 * n < 3 * p : big
             ... ≤ p * p : (mul_le_mul_right p_pos).2 three_lt_p
             ... = p ^ 2 : (sq _).symm
             ... ≤ p ^ i : nat.pow_le_pow_of_le_right p_pos two_le_i, },
    have n_mod : n % p ^ i = n,
    { apply nat.mod_eq_of_lt,
      calc n ≤ n + n : nat.le.intro rfl
         ... = 2 * n : (two_mul n).symm
         ... < p ^ i : two_n_lt_pow_p_i, },
    rw n_mod,
    exact two_n_lt_pow_p_i, },

    { rw [pow_one],
      suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
      { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },
      have n_big : 1 ≤ (n / p) := (nat.le_div_iff_mul_le' p_pos).2 (trans (one_mul _).le small),
      rw [←mul_add, nat.div_add_mod],
      calc  2 * n < 3 * p : big
              ... = 2 * p + p : nat.succ_mul _ _
              ... ≤ 2 * (p * (n / p)) + p : add_le_add_right ((mul_le_mul_left zero_lt_two).mpr
              $ ((le_mul_iff_one_le_right p_pos).mpr n_big)) _ },
    { have : i = 0 := nat.le_zero_iff.mp (nat.le_of_lt_succ H),
      rw [this, pow_zero, nat.mod_one, mul_zero],
      exact zero_lt_one }
end


lemma claim_4
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (multiplicity_pos : 0 < α n p)
  : p ≤ 2 * n
  :=
begin
  unfold α at multiplicity_pos,
  rw @padic_val_nat_def p hp ((2 * n).choose n) (central_binom_nonzero n) at multiplicity_pos,
  simp only [@nat.prime.multiplicity_choose p (2 * n) n (p.log (2 * n) + 1) hp.out
    n.le_two_mul_self (lt_add_one (p.log (2 * n)))] at multiplicity_pos,
  have r : 2 * n - n = n,
    calc 2 * n - n = n + n - n : congr_arg (flip (has_sub.sub) n) (two_mul n)
               ... = n         : nat.add_sub_cancel n n,
  simp only [r, ←two_mul, gt_iff_lt, enat.get_coe', finset.filter_congr_decidable]
    at multiplicity_pos,
  clear r,
  rw finset.card_pos at multiplicity_pos,
  cases multiplicity_pos with m hm,
  simp only [finset.mem_Ico, finset.mem_filter] at hm,
  calc p = p ^ 1 : (pow_one _).symm
  ...    ≤ p ^ m : nat.pow_le_pow_of_le_right
                    (show 0 < p, from trans zero_lt_one hp.out.one_lt) hm.left.left
  ...    ≤ 2 * (n % p ^ m) : hm.right
  ...    ≤ 2 * n : nat.mul_le_mul_left _ (nat.mod_le n _),
end

/-
Then:
4^n ≤ 2nCn * (2 * n + 1) (by choose_halfway_is_big)
= prod (primes ≤ 2n) p^(α n p) * (2n+1)
= prod (primes ≤ n) p^(α n p) * prod (primes n < p <= 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ 2n/3) p^α * prod (primes 2n/3 to n) 1 * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 3)
= prod (primes ≤ 2n/3) p^α * prod (primes n < p ≤ 2n) p^α * (2n+1)
= prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p^α
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ prod (primes ≤ sqrt(2n)) p^α * prod(primes sqrt(2n)..2n/3) p
  * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 2)
≤ prod (primes ≤ sqrt(2n)) p^α * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by a general bound on the primorial)
≤ prod (primes ≤ sqrt(2n)) (2n) * 4 ^ (2n / 3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by claim 1)
= (2n)^π (sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
≤ (2n)^(sqrt 2n) * 4 ^ (2n/3) * prod (primes n < p ≤ 2n) p^α * (2n+1)
  (by "prime count of x is less than x")

For sufficiently large n, that last product term is > 1.
Indeed, suppose for contradiction it's equal to 1.
Then 4^n ≤ (2n)^(sqrt 2n) * 4^(2n/3) * (2n+1)
so 4^(n/3) ≤ (2n)^(sqrt 2n) (2n+1)
and this is Clearly False for sufficiently large n.
-/

lemma two_n_div_3_le_two_mul_n_choose_n (n : ℕ) : 2 * n / 3 < (2 * n).choose n :=
begin
  cases n,
  { simp only [nat.succ_pos', nat.choose_self, nat.zero_div, mul_zero], },
  calc 2 * (n + 1) / 3 < 2 * (n + 1): nat.div_lt_self (by norm_num) (by norm_num)
  ... = (2 * (n + 1)).choose(1): by norm_num
  ... ≤ (2 * (n + 1)).choose(2 * (n + 1) / 2): nat.choose_le_middle 1 (2 * (n + 1))
  ... = (2 * (n + 1)).choose(n + 1): by simp only [nat.succ_pos', nat.mul_div_right]
end

lemma not_pos_iff_zero (n : ℕ) : ¬ 0 < n ↔ n = 0 := trans not_lt le_zero_iff

lemma alskjhads_no_two (n x : ℕ) (h : n / 3 + 1 ≤ x) : n < 3 * x :=
lt_of_lt_of_le
  ((nat.div_lt_iff_lt_mul' zero_lt_three).mp (nat.succ_le_iff.mp h))
  (mul_comm _ _).le

lemma alskjhads (n x : ℕ): 2 * n / 3 + 1 ≤ x -> 2 * n < 3 * x :=
alskjhads_no_two (2 * n) x

lemma central_binom_factorization (n : ℕ) :
      ∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      = (2 * n).choose n :=
  prod_pow_prime_padic_val_nat _ (central_binom_nonzero n) _ (lt_add_one _)




lemma interchange_filters {α: _} {S: finset α} {f g: α → Prop}
[decidable_pred f] [decidable_pred g]
  : (S.filter g).filter f = S.filter (λ i, g i ∧ f i) :=
by { ext1, simp only [finset.mem_filter, and_assoc] }

lemma interchange_and_in_filter {α: _} {S: finset α} {f g: α → Prop}
[decidable_pred f] [decidable_pred g]
  : S.filter (λ i, g i ∧ f i) = S.filter (λ i, f i ∧ g i) :=
by { ext1, simp only [finset.mem_filter, and.comm, iff_self] }

lemma intervening_sqrt {a n : ℕ} (small : (nat.sqrt n) ^ 2 ≤ a ^ 2) (big : a ^ 2 ≤ n)
  : a = nat.sqrt n :=
begin
  rcases lt_trichotomy a (nat.sqrt n) with H|rfl|H,
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc  _ = a * a             : sq _
         ... < n.sqrt * n.sqrt  : nat.mul_self_lt_mul_self H
         ... = (nat.sqrt n) ^ 2 : (sq _).symm
         ... ≤ a ^ 2            : small, },
  { refl, },
  { refine (lt_irrefl (a ^ 2) _).elim,
    calc  _ ≤ n     : big
        ... < a * a : nat.sqrt_lt.1 H
        ... = a ^ 2 : (sq _).symm, },
end

lemma filter_filter_card_le_filter_card {α: _} {S: finset α} {f g: α → Prop}
[_inst : decidable_pred f][_inst : decidable_pred g]
: ((S.filter g).filter f).card ≤ (S.filter f).card :=
begin
  calc ((S.filter g).filter f).card = (S.filter (λ i, g i ∧ f i)).card
            : congr_arg finset.card interchange_filters
  ... = (S.filter (λ i, f i ∧ g i)).card: congr_arg finset.card interchange_and_in_filter
  ... = ((S.filter f).filter g).card: congr_arg finset.card interchange_filters.symm
  ... ≤ (S.filter f).card: (finset.filter f S).card_filter_le g,
end

lemma filter_size {S : finset ℕ} {a : ℕ} : (finset.filter (λ p, p < a) S).card ≤ a :=
have t : ∀ i, i ∈ (S.filter (λ p, p < a)) → i ∈ finset.range(a), by simp,
have r: S.filter (λ p, p < a) ⊆ finset.range(a) := finset.subset_iff.mpr t,
have s: (S.filter (λ p, p < a)).card ≤ (finset.range(a)).card := finset.card_le_of_subset r,
by simpa only [finset.card_range] using s

lemma even_prime_is_two {p : ℕ} (pr: nat.prime p) (div: 2 ∣ p) : p = 2 :=
((nat.prime_dvd_prime_iff_eq nat.prime_two pr).mp div).symm

lemma even_prime_is_small {a n : ℕ} (a_prime : nat.prime a) (n_big : 2 < n)
(small : a ^ 2 ≤ 2 * n)
: a ^ 2 < 2 * n :=
begin
  cases lt_or_ge (a ^ 2) (2 * n),
  { exact h, },
  { have t : a * a = 2 * n := (sq _).symm.trans (small.antisymm h),
    have a_even : 2 ∣ a := (or_self _).mp ((nat.prime.dvd_mul nat.prime_two).mp ⟨n, t⟩),
    have a_two : a = 2 := even_prime_is_two a_prime a_even,
    rw [a_two, sq],
    exact (mul_lt_mul_left zero_lt_two).mpr n_big },
end

lemma pow_beats_mul (n : ℕ) (big : 3 < n) : 32 * n ≤ 4 ^ n :=
begin
  induction n with n hyp,
  { exact zero_le_one, },
  { cases le_or_gt n 3,
    { have s : n = 3 := h.antisymm (nat.lt_succ_iff.mp big),
      rw s,
      norm_num, },
  { specialize hyp h,
    have r : 32 ≤ 4 ^ n := trans
        (trans (nat.self_le_mul (trans zero_lt_three h)) (mul_comm _ _ ).le) hyp,
    calc 32 * (n + 1) = 32 * n + 32 : mul_add _ _ _
    ... ≤ 4 ^ n + 32 : add_le_add_right hyp _
    ... ≤ 4 ^ n + 4 ^ n : add_le_add_left r _
    ... = (4 ^ n) * 2 : (mul_two _).symm
    ... ≤ (4 ^ n) * 4 : (mul_le_mul_left (pow_pos zero_lt_four _)).mpr (nat.le_of_sub_eq_zero rfl)
    ... = 4 ^ (n + 1) : (pow_succ' _ _).symm, }, },
end

lemma six_le_three_mul_four_pow_succ : ∀ (k : ℕ), 6 ≤ 3 * 4 ^ (k + 1)
| 0       := by norm_num
| (k + 1) := calc  6 ≤ 3 * 4 ^ (k + 1) : six_le_three_mul_four_pow_succ k
                 ... ≤ 3 * 4 ^ (k + 2) : (mul_le_mul_left zero_lt_three).mpr $
                   pow_le_pow (nat.succ_pos 3) (nat.le_succ _)

lemma thirty_mul_succ_le_four_pow {n : ℕ} (n4 : 4 ≤ n) :
  30 * (n + 1) ≤ 4 ^ n :=
begin
  rcases le_iff_exists_add.mp n4 with ⟨k, rfl⟩,
  -- Case k = 0: easy
  cases k, { norm_num },
  -- Case k = 1: easy
  cases k, { norm_num },
  rw pow_add,
  refine mul_le_mul _ _ (zero_le _) (zero_le _),
  { norm_num },
  { obtain F : k + 1 < 4 ^ (k + 1) := (k + 1).lt_pow_self (nat.succ_lt_succ (2 : ℕ).succ_pos),
    calc  _ = k + 1 + 6 : (congr_arg nat.succ (add_comm 4 _) : _)
        ... ≤ 4 ^ (k + 1) + 6                : add_le_add_right F.le _
        ... ≤ 4 ^ (k + 1) +  3 * 4 ^ (k + 1) : add_le_add_left (six_le_three_mul_four_pow_succ k) _
        ... = 3 * 4 ^ (k + 1) + 4 ^ (k + 1)  : add_comm _ _
        ... = 4 * 4 ^ (k + 1)                : (nat.succ_mul _ _).symm }
end

lemma succ_two_mul_le_four_pow_div_fifteen {n : ℕ} (n_large : 60 ≤ n) :
  2 * n + 1 ≤ 4 ^ (n / 15) :=
begin
  obtain F : 30 * (n / 15 + 1) ≤ 4 ^ (n / 15) := thirty_mul_succ_le_four_pow
    ((nat.le_div_iff_mul_le _ _ (nat.succ_pos 14)).mpr n_large : 4 ≤ n / 15),
  refine trans (nat.succ_le_of_lt _ : 2 * n < 2 * 15 * (n / 15 + 1)) F,
  rw mul_assoc,
  exact (mul_lt_mul_left zero_lt_two).mpr (nat.lt_mul_div_succ _ (nat.succ_pos 14)),
end

lemma power_conversion_1 (n : ℕ) (n_large : 480 < n) : 2 * n + 1 ≤ 4 ^ (n / 15) :=
succ_two_mul_le_four_pow_div_fifteen (trans (nat.le_of_sub_eq_zero rfl : 60 ≤ 481) n_large)

open real
open_locale nnreal

lemma pow_coe (a b : ℕ) : (↑(a ^ b) : ℝ) = (↑a) ^ (↑b : ℝ) :=
by simp only [rpow_nat_cast, nat.cast_pow]

lemma nat_sqrt_le_real_sqrt (a : ℕ) : (nat.sqrt a : ℝ) ≤ real.sqrt a :=
le_sqrt_of_sq_le (by simpa using (nat.cast_le.mpr a.sqrt_le' : ((id nat.sqrt a ^ 2 : ℕ) : ℝ) ≤ a))

open set

lemma one_lt_four : (1 : ℝ) < 4 := by linarith

lemma log_four_pos : 0 < log 4 := log_pos one_lt_four

lemma log_1024_div_log_4 : log 1024 / log 4 = 5 :=
begin
  rw div_eq_iff,
  have h : (1024 : ℝ) = 4 ^ (5 : ℝ), norm_num,
  rw h,
  rw log_rpow,
  linarith,
  linarith [log_four_pos],
end

lemma inequality1 {x : ℝ} (n_large : 1024 < x) : log (2 * x + 1) / (x * log 4) ≤ 1/30 :=
begin
  suffices : log (4 * x) / (x * log 4) ≤ 1 / 30,
  apply trans _ this,
  rw div_le_div_right,
  rw log_le_log,
  repeat {linarith,},
  apply mul_pos,
  linarith,
  apply log_pos,
  exact one_lt_four,
  rw log_mul,
  rw add_div,
  have h4 : 0 < x,
    linarith only [n_large],
  have x_ne_zero : x ≠ 0, exact ne_of_gt h4,
  have h1: log 4 ≠ 0 := real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num),
  have h2: log 4 * sqrt x ≠ 0, apply mul_ne_zero h1, exact sqrt_ne_zero'.mpr h4,

  have h3 : log 4 / (x * log 4) + log x / (x * log 4) = 1 / x + (log x / x) / log 4,
    field_simp,
  ring,
  rw h3,
  calc 1 / x + log x / x / log 4 ≤ 1 / 1024 + log x / x / log 4 :
          begin
            simp,
            rw inv_le,
            simp,
            apply le_of_lt,
            assumption,
            exact h4,
            norm_num,
          end
  ... ≤ 1 / 1024 + log 1024 / 1024 / log 4 :
          begin
            simp,
            rw div_le_div_right,
            apply log_div_self_antitone_on,
            simp,
            linarith only [exp_one_lt_d9],
            simp,
            linarith only [exp_one_lt_d9, n_large],
            exact le_of_lt n_large,
            exact log_four_pos,
          end
  ... ≤ 1 / 30 :
          begin
            rw div_div_eq_div_mul,
            rw mul_comm,
            rw <-div_div_eq_div_mul,
            rw log_1024_div_log_4,
            norm_num,
          end,
  norm_num1,
  linarith,
end

lemma four_eq_two_rpow_two : (4 : ℝ) = 2 ^ (2 : ℝ) :=
calc (4 : ℝ) = 2 ^ (2 : ℕ) : by {norm_num,}
... = 2 ^ (2 : ℝ) : by {rw <-real.rpow_nat_cast, congr, exact nat.cast_two,}


lemma inequality2 {x : ℝ} (n_large : 1024 < x) : sqrt 2 * sqrt x * log 2 / (x * log 4) ≤ 0.04 :=
begin
  rw div_le_iff,
  rw <-mul_assoc,
  rw four_eq_two_rpow_two,
  rw log_rpow,
  rw <-mul_assoc,
  rw mul_le_mul_right,
  rw <-le_div_iff,
  rw mul_comm _ x,
  rw mul_assoc,
  rw mul_comm x,
  rw mul_div_assoc,
  rw div_sqrt,
  rw mul_comm,
  rw <-div_le_iff,
  rw le_sqrt,
  rw div_pow,
  -- simp only [one_div, div_pow],
  rw real.sq_sqrt,
  field_simp,
  -- repeat {apply ne_of_gt},
  repeat {apply mul_pos},
  repeat {apply log_pos},
  repeat {apply div_nonneg},
  -- repeat {apply rpow_pos_of_pos},
  repeat {norm_num,},
  repeat {linarith,},
  apply sqrt_nonneg,

  -- suffices : sqrt 2 ≤  sqrt x * (1 / 25) * 2,
  -- {
  --   rw mul_comm,
  -- },

end

lemma inequality3' {x : ℝ} (n_large : 1024 < x) : sqrt 2 * sqrt x * log x / (x * log 4) = (sqrt 2 / log 4) * log x / sqrt x :=
begin
  have h : x ≠ 0,
  { apply ne_of_gt,
    linarith, },
  have h4 : 0 < x,
    linarith,
  have h1: log 4 ≠ 0 := real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num),
  have h2: log 4 * sqrt x ≠ 0, apply mul_ne_zero h1, exact sqrt_ne_zero'.mpr h4,
  field_simp,
  ring_nf,
  apply eq.symm,
  rw @sq_sqrt x,
  ring,
  linarith,
end

-- example (a b c : ℝ) (hc : 0 < c) : (exp a) ^ b = exp (a * b) := by library_search

lemma log_div_sqrt_decreasing {x y : ℝ} (hex : real.exp 2 ≤ x) (hxy : x ≤ y) : log y / sqrt y ≤ log x / sqrt x :=
begin
  have hltx : 0 < x, exact lt_of_lt_of_le ( (exp_pos 2)) hex,
  have hlty : 0 < y, linarith,
  have hx : 0 ≤ x, exact le_trans (le_of_lt (exp_pos 2)) hex,
  have hy : 0 ≤ y, linarith,
  conv_lhs
  begin
    congr,
    rw <-sq_sqrt hy,
  end,
  conv_rhs
  begin
    congr,
    rw <-sq_sqrt hx,
  end,
  rw <-real.rpow_nat_cast,
  rw <-real.rpow_nat_cast,
  rw log_rpow,
  rw log_rpow,
  rw mul_div_assoc,
  rw mul_div_assoc,
  rw mul_le_mul_left,
  apply log_div_self_antitone_on,
  simp,
  rw le_sqrt,
  rw <-exp_nat_mul,
  simp [hex],
  swap 3,
  simp,
  rw le_sqrt,
  rw <-exp_nat_mul,
  simp,
  exact le_trans hex hxy,
  exact le_of_lt (exp_pos 1),
  exact hy,
  exact le_of_lt (exp_pos 1),
  exact hx,
  exact sqrt_le_sqrt hxy,
  norm_num,

  exact sqrt_pos.mpr hltx,
  rw sqrt_pos,
  exact hlty,
end

-- example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b^2 -> a ≤ b := by library_search

lemma inequality3 {x : ℝ} (n_large : 1024 < x) : sqrt 2 * sqrt x * log x / (x * log 4) ≤ 1/4 :=
begin
  rw [inequality3' n_large],
  -- Get the log x in the second term to be 2 log sqrt x. and split the 1/x i n that term to
  calc sqrt 2 / log 4 * log x / sqrt x
       = sqrt 2 / log 4 * (log x / sqrt x) : by rw mul_div_assoc
  ...  ≤ sqrt 2 / log 4 * (log 1024 / sqrt 1024) :
          begin
            rw mul_le_mul_left,
            have n_larger := le_of_lt n_large,
            apply log_div_sqrt_decreasing,
            calc exp 2 = (exp 1) ^ 2 :
              begin
                rw <-exp_nat_mul,
                simp,
              end
            ... ≤ 2.7182818286 ^ 2 :
              begin
                apply pow_le_pow_of_le_left,
                apply le_of_lt,
                exact exp_pos 1,
                apply le_of_lt,
                exact exp_one_lt_d9,
              end
            ... ≤ 1024 : by norm_num,
            exact n_larger,
            apply div_pos,
            rw sqrt_pos,
            linarith,
            exact log_four_pos,
          end
  ...  = log 1024 / log 4 * sqrt 2 / sqrt 1024 :
          begin
            ring,
          end
  ...  = 5 * sqrt 2 / sqrt 1024 :
          begin
            congr,
            rw log_1024_div_log_4,
          end
  ... ≤ 1 / 4 :
          begin
            rw mul_div_assoc,
            rw <-sqrt_div,
            rw mul_comm,
            rw <-le_div_iff,
            rw sqrt_le_iff,
            split,
            norm_num,
            norm_num,
            linarith,
            linarith,
          end,

end

lemma equality4 {x : ℝ} (n_large : 1024 < x) : 2 * x / 3 * log 4 / (x * log 4) = 2 / 3 :=
begin
  have h : x ≠ 0,
  { apply ne_of_gt,
    linarith, },
  have : log 4 ≠ 0 := real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num),
  field_simp,
  ring,
end

lemma real_false_inequality_is_false {x : ℝ} (n_large : (1024 : ℝ) < x)
  : (2 * x + 1) * (2 * x) ^ (real.sqrt (2 * x)) * 4 ^ (2 * x / 3) < 4 ^ x :=
begin
  apply (log_lt_log_iff _ _).1,
  rw [log_mul, log_mul, log_rpow, log_rpow, log_rpow, log_mul],
  rw <-div_lt_one,
  simp only [add_div, mul_add, add_mul, add_div, <-add_assoc],
  simp,
  {
    rw [equality4 n_large],
    linarith only [inequality1 n_large, inequality2 n_large, inequality3 n_large],
  },
  repeat {apply ne_of_gt},
  repeat {apply mul_pos},
  repeat {apply rpow_pos_of_pos},
  repeat {norm_num,},
  repeat {linarith,},
  apply log_pos,
  norm_num,

end


-- Take the approach of immediately reifying
lemma false_inequality_is_false {n : ℕ} (n_large : 1024 < n)
  : 4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) → false :=
begin
  rw imp_false,
  rw not_le,
  rw <-@nat.cast_lt ℝ,
  have fact1 : 0 < 2 * (n : ℝ) + 1,
  {

    rw <-nat.cast_zero,
    conv
    begin
      to_rhs,
      congr,
      skip,
      rw <-nat.cast_one,
    end,
    rw <-nat.cast_two,
    rw <-nat.cast_mul,
    rw <-nat.cast_add,
    rw nat.cast_lt,
    linarith,
  },
  have fact2 : 0 < 2 * (n : ℝ),
  {
    rw <-nat.cast_zero,
    rw <-nat.cast_two,
    rw <-nat.cast_mul,
    rw nat.cast_lt,
    linarith,
  },
  simp only [nat.cast_bit0, nat.cast_add, nat.cast_one, nat.cast_mul, nat.cast_pow],
  simp only [<-rpow_nat_cast],
  calc (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ (nat.sqrt (2 * n) : ℝ) * 4 ^ (((2 * n / 3) : ℕ) : ℝ)
        ≤ (2 * (n : ℝ) + 1) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (((2 * n / 3) : ℕ) : ℝ) :
          begin
            rw mul_le_mul_right,
            rw mul_le_mul_left,
            apply rpow_le_rpow_of_exponent_le,
            rw <-@nat.cast_lt ℝ at n_large,
            have h : (1024) < (n : ℝ), convert n_large, simp,
            linarith,
            rw le_sqrt,
            rw <-nat.cast_pow,
            conv
            begin
              to_rhs,
              rw <-nat.cast_two,
            end,
            rw <-nat.cast_mul,
            rw nat.cast_le,
            exact (2 * n).sqrt_le',
            exact (nat.sqrt (2 * n)).cast_nonneg,
            rw <-nat.cast_two,
            rw <-nat.cast_mul,
            exact (2 * n).cast_nonneg,
            exact fact1,
            apply rpow_pos_of_pos,
            norm_num,
          end
     ... ≤ (2 * (n : ℝ) + 1) * (2 * n : ℝ) ^ (real.sqrt (2 * (n : ℝ))) * 4 ^ (2 * (n : ℝ) / 3) :
          begin
            -- sorry
            rw mul_le_mul_left,
            -- rw mul_le_mul_left,
            apply rpow_le_rpow_of_exponent_le,
            linarith,
            -- simp,
            apply trans nat.cast_div_le,
            apply le_of_eq,
            congr,
            simp,
            simp,
            exact is_trans.swap (λ (x y : ℝ), y ≤ x),
            apply mul_pos,
            exact fact1,
            apply rpow_pos_of_pos,
            exact fact2,
          end
    ... < 4 ^ (n : ℝ) :
          begin
            apply real_false_inequality_is_false,
            rw <-@nat.cast_lt ℝ at n_large,
            have h : (1024) < (n : ℝ), convert n_large, simp,
            linarith,
          end,
end

lemma more_restrictive_filter_means_smaller_subset {a : _} {S : finset a} {f : _} {g : _}
[decidable_pred f] [decidable_pred g] (p : ∀ i, f i → g i)
  : finset.filter f S ⊆ finset.filter g S :=
begin
  intros h prop,
  simp only [finset.mem_filter] at prop,
  simp only [finset.mem_filter],
  exact ⟨prop.1, p h prop.2⟩,
end

lemma filter_to_subset {a : _} {S : finset a} {T : finset a} {p : _} [decidable_pred p]
(prop : ∀ i, p i → i ∈ T)
  : finset.filter p S ⊆ T :=
begin
  suffices : ∀ x, x ∈ finset.filter p S → x ∈ T, by exact finset.subset_iff.mpr this,
  intros x hyp,
  simp only [finset.mem_filter] at hyp,
  exact prop x hyp.2
end

lemma foo {n : ℕ} :
(finset.filter (λ (p : ℕ), p ^ 2 < 2 * n)
  (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card ≤ nat.sqrt (2 * n) :=
begin
  have t : ∀ p, p ^ 2 ≤ 2 * n ↔ p ≤ nat.sqrt (2 * n),
  { intro p,
    exact nat.le_sqrt'.symm, },

  have u : ∀ p, (p ^ 2 < 2 * n) → p ^ 2 ≤ 2 * n, by
  { intros p hyp,
    exact le_of_lt hyp, },

  have v : finset.filter (λ p, p ^ 2 < 2 * n)
            (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) ⊆
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) :=
    more_restrictive_filter_means_smaller_subset u,

  have w' : finset.filter (λ p, p ^ 2 ≤ 2 * n)
              (finset.filter nat.prime (finset.range (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) :=
    by {
      apply congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime i)),
      rw finset.range_eq_Ico,
    },

  have w : finset.filter (λ p, p ^ 2 ≤ 2 * n)
            (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1))) =
    finset.filter (λ p, p ^ 2 ≤ 2 * n) (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { refine congr_arg (λ i, finset.filter (λ p, p ^ 2 ≤ 2 * n) i) _,
      ext1,
      split,
      { intros hyp,
        simp only [true_and, finset.mem_Ico, zero_le', finset.mem_filter] at hyp,
        simp only [finset.mem_Ico, finset.mem_filter],
        exact ⟨⟨nat.prime.two_le hyp.2, hyp.1⟩, hyp.2⟩, },
      { intros hyp,
        simp only [finset.mem_Ico, finset.mem_filter] at hyp,
        simp only [true_and, finset.mem_Ico, zero_le', finset.mem_filter],
        exact ⟨hyp.1.2, hyp.2⟩, }, },

  have g : finset.filter (λ p, p ^ 2 ≤ 2 * n)
            (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))) =
           finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n)
            (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))),
    { ext1,
      split,
      { intros hyp,
        simp only [finset.mem_Ico, finset.mem_filter] at hyp,
        simp only [finset.mem_Ico, finset.mem_filter],
        have r : 2 ≤ a ^ 2 :=
          by calc 2 ≤ a : nat.prime.two_le hyp.1.2
          ... ≤ a * a : nat.le_mul_self a
          ... = a ^ 2 : by ring,
        exact ⟨hyp.1, ⟨r, hyp.2⟩⟩, },
      { intros hyp,
        simp only [finset.mem_Ico, finset.mem_filter] at hyp,
        simp only [finset.mem_Ico, finset.mem_filter],
        exact ⟨hyp.1, hyp.2.2⟩, }, },

  have h : (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n)
              (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1))))
            ⊆ finset.Ico 2 (nat.sqrt (2 * n) + 1)
    , by {
      apply filter_to_subset _,
      intros i hyp,
      simp,
      split,
      { cases le_or_gt 2 i,
        { exact h, },
        { cases i,
          { linarith, },
          { cases i,
            { linarith, },
            { exact dec_trivial, }, } }, },
      { have : i ≤ nat.sqrt (2 * n) := nat.le_sqrt'.mpr hyp.2,
        linarith, },
    },

  calc (finset.filter (λ (p : ℕ), p ^ 2 < 2 * n)
          (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card
      ≤ (finset.filter (λ p, p ^ 2 ≤ 2 * n)
        (finset.filter nat.prime (finset.range (2 * n / 3 + 1)))).card: finset.card_le_of_subset v
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 0 (2 * n / 3 + 1)))).card: congr_arg finset.card w'
  ... = (finset.filter (λ p, p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card w
  ... = (finset.filter (λ p, 2 ≤ p ^ 2 ∧ p ^ 2 ≤ 2 * n)
          (finset.filter nat.prime (finset.Ico 2 (2 * n / 3 + 1)))).card: congr_arg finset.card g
  ... ≤ (finset.Ico 2 (nat.sqrt (2 * n) + 1)).card: finset.card_le_of_subset h
  ... = nat.sqrt (2 * n) + 1 - 2: nat.card_Ico 2 (nat.sqrt (2 * n) + 1)
  ... = nat.sqrt (2 * n) - 1: by ring
  ... ≤ nat.sqrt (2 * n): (nat.sqrt (2 * n)).sub_le 1,

end

lemma bertrand_eventually (n : nat) (n_big : 1024 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  by_contradiction no_prime,

  have central_binom_factorization_small :
      ∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
        p ^ (padic_val_nat p ((2 * n).choose n))
      =
      ∏ p in finset.filter nat.prime (finset.range (((2 * n).choose n + 1))),
        p ^ (padic_val_nat p ((2 * n).choose n)) ,
    { apply finset.prod_subset,
      apply finset.subset_iff.2,
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intro hx,
      split,
      { linarith [(hx.left), (two_n_div_3_le_two_mul_n_choose_n n)], },
      { exact hx.right, },
      intro x,
      rw [finset.mem_filter, finset.mem_filter, finset.mem_range, finset.mem_range],
      intros hx h2x,
      simp only [hx.right, and_true, not_lt] at h2x,
      by_contradiction,
      have x_le_two_mul_n : x ≤ 2 * n, by
        { apply (@claim_4 x ⟨hx.right⟩ n),
          unfold α,
          by_contradiction h1,
          rw not_pos_iff_zero at h1,
          rw h1 at h,
          rw pow_zero at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
      apply no_prime,
      use x,
      split,
      { exact hx.right, },
      { split,
        { by_contradiction neg_n_le_x,
          simp only [not_lt] at neg_n_le_x,
          have claim := @claim_3 x ⟨hx.right⟩ n (by linarith) (by linarith) (alskjhads n x h2x),
          unfold α at claim,
          rw [claim, pow_zero] at h,
          simp only [eq_self_iff_true, not_true] at h,
          exact h, },
        exact x_le_two_mul_n, }, },

    have double_pow_pos: ∀ (i : ℕ), 0 < (2 * n) ^ i,
    { intros _, exact pow_pos (by linarith) _ },

    have binom_inequality
      : (2 * n).choose n ≤ (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3), by
      calc (2 * n).choose n
              = (∏ p in finset.filter nat.prime (finset.range ((2 * n).choose n + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : (central_binom_factorization n).symm
      ...     = (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                      : central_binom_factorization_small.symm
      ...     = (∏ p in finset.filter nat.prime
                          (finset.range (2 * n / 3 + 1)),
                   if p ^ 2 ≤ 2 * n
                    then p ^ (padic_val_nat p ((2 * n).choose n))
                    else p ^ (padic_val_nat p ((2 * n).choose n)))
                       : by simp only [if_t_t]
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, ¬p ^ 2 ≤ 2 * n)
                  (finset.filter nat.prime (finset.range (2 * n / 3 + 1))),
                    p ^ (padic_val_nat p ((2 * n).choose n)))
                    : finset.prod_ite _ _
      ...     = (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : by simp only [not_le, finset.filter_congr_decidable]
      ...     ≤ (∏ p in finset.filter (λ p, p ^ 2 ≤ 2 * n)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   2 * n)
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine finset.prod_le_prod'' _,
                       intros i hyp,
                       simp only [finset.mem_filter, finset.mem_range] at hyp,
                       exact @claim_1 i (fact_iff.2 hyp.1.2) n (by linarith),
                     end
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 ≤ 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : by simp only [finset.prod_const]
      ...     = (2 * n) ^ finset.card (finset.filter (λ p, p ^ 2 < 2 * n)
                                        (finset.filter nat.prime (finset.range (2 * n / 3 + 1))))
                *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                   : begin
                    refine (nat.mul_left_inj _).2 _,
                    { refine finset.prod_pos _,
                      intros p hyp,
                      simp only [finset.mem_filter, finset.mem_range] at hyp,
                      exact pow_pos (nat.prime.pos hyp.1.2) (padic_val_nat p ((2 * n).choose n)), },
                    { refine congr_arg (λ i, (2 * n) ^ i) _,
                      refine congr_arg (λ s, finset.card s) _,
                      ext1,
                      split,
                      { intro h, simp at h, simp, split,
                        exact h.1, exact even_prime_is_small h.1.2 (by linarith) h.2, },
                      { intro h, simp at h, simp, split, exact h.1, linarith, }
                     },
                   end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ (padic_val_nat p ((2 * n).choose n)))
                     : begin
                       refine (nat.mul_le_mul_right _ _),
                       refine pow_le_pow (by linarith) _,
                       exact foo,
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter (λ p, (2 * n) < p ^ 2)
                          (finset.filter nat.prime
                            (finset.range (2 * n / 3 + 1))),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                        { refine finset.prod_le_prod'' _,
                          intros i hyp,
                          simp only [finset.mem_filter, finset.mem_range] at hyp,
                          cases hyp with i_facts sqrt_two_n_lt_i,
                          refine pow_le_pow _ _,
                          { cases le_or_gt 1 i,
                            { exact h, },
                            { have i_zero : i = 0, by linarith,
                              rw i_zero at i_facts,
                              exfalso,
                              exact nat.not_prime_zero i_facts.2, }, },
                          { exact @claim_2 i (fact_iff.2 i_facts.2) n (by linarith)
                            sqrt_two_n_lt_i, }, },
                     end
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p ^ 1)
                     : begin
                       refine nat.mul_le_mul_left _ _,
                       refine finset.prod_le_prod_of_subset_of_one_le' (finset.filter_subset _ _) _,
                        { intros i hyp1 hyp2,
                        cases le_or_gt 1 i,
                        { ring_nf, exact h, },
                        { have i_zero : i = 0, by linarith,
                          simp only [i_zero, true_and, nat.succ_pos',
                                     finset.mem_filter, finset.mem_range] at hyp1,
                          exfalso, exact nat.not_prime_zero hyp1, }, }
                     end
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
                 *
                (∏ p in finset.filter nat.prime (finset.range (2 * n / 3 + 1)),
                   p)
                     : by simp only [pow_one]
      ...     = (2 * n) ^ (nat.sqrt (2 * n))
               *
                (primorial (2 * n / 3))
                     : by unfold primorial
      ...     ≤ (2 * n) ^ (nat.sqrt (2 * n))
                 *
                4 ^ (2 * n / 3)
                     : nat.mul_le_mul_left _ (primorial_le_4_pow (2 * n / 3)),

    have false_inequality
      : 4 ^ n ≤ (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3), by
      calc 4 ^ n ≤ (2 * n + 1) * (2 * n).choose n
                    :  nat.four_pow_le_two_mul_add_one_mul_central_binom n
        ...      ≤ (2 * n + 1) * ((2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3))
                    :
                    begin
                      apply mul_le_mul_of_nonneg_left,
                      exact binom_inequality,
                      linarith,
                    end
        ...      = (2 * n + 1) * (2 * n) ^ (nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) : by ring,

    exfalso,
    exact false_inequality_is_false n_big false_inequality,
end

/--
Proves that Bertrand's postulate holds over all positive naturals less than n by identifying a descending list of
primes, each no more than twice the next, such that the list contains a witness for each number ≤ n.
-/
lemma bertrand_initial (n : ℕ) (hn0 : 0 < n) (plist : list ℕ)
  (primeplist : ∀ p ∈ plist, nat.prime p)
  (covering : ∀ a b, (a, b) ∈ list.zip plist (list.tail (plist ++ [2])) →
        a ≤ 2 * b)
   (hn : n < (plist ++ [2]).head) :
  ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  tactic.unfreeze_local_instances,
  induction plist,
  { simp * at *,
    interval_cases n,
    { use 2,
      norm_num, }, },
  { simp * at *,
    by_cases plist_hd ≤ 2 * n,
    { use plist_hd,
      exact ⟨primeplist.left, hn, h⟩, },
    { apply plist_ih,
      { exact primeplist.right, },
      { intros a b hmem,
        apply covering,
        cases plist_tl,
        { simp * at *, },
        { simp at hmem,
          simp,
          right,
          assumption, }, },
      { cases plist_tl,
        { simp * at *,
          have h_hd := covering plist_hd 2 rfl rfl,
          have hn2 : 2 * n < 2 * 2, exact gt_of_ge_of_gt h_hd h,
          exact lt_of_mul_lt_mul_left' hn2, },
        { simp * at *,
          have h_hd := covering plist_hd plist_tl_hd,
          simp at h_hd,
          have hn2 : 2 * n < 2 * plist_tl_hd, exact gt_of_ge_of_gt h_hd h,
          exact lt_of_mul_lt_mul_left' hn2, }, }, }, },
end


/-- Bertrand's Postulate: For any positive natural number, there is a prime which is greater than it, but no more than twice as large. -/
theorem bertrand (n : nat) (n_pos : 0 < n) : ∃ p, nat.prime p ∧ n < p ∧ p ≤ 2 * n :=
begin
  cases lt_or_le 1024 n,
  { exact bertrand_eventually n h },
  have h' := nat.lt_succ_of_le h,
  -- Supply a list of primes to cover the initial cases
  apply bertrand_initial n n_pos [1031, 547, 277, 139, 73, 37, 19, 11, 7, 5, 3],
  -- Prove the list has the properties needed:
  { -- Prove the list consists of primes
    intros p hp,
    simp at hp,
    iterate {cases hp <|> rw hp <|> norm_num}, },
  { -- Prove each element of the list is at least half the previous.
    intros a b hab,
    simp at hab,
    iterate {cases hab <|> rw [hab.left, hab.right] <|> linarith}, },
  { -- Prove the first element of the list is large enough.
    simp,
    linarith, },
end
