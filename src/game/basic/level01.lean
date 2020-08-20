import data.nat.prime
import data.rat.basic
import data.real.basic
import tactic

namespace uwyo -- hide

/-
# Chapter 1 : Basic facts

## Level 1

In this level you need to prove that `sqrt 2` is irrational.
This is adapted from a similar proof from chapter 2 of "logic and Proof"
by J. Avigad, R. Y. Lewis and F. van Doorn, freely available online.
-/


/- Lemma
For any two arbitrary natural numbers $a$ and $b$, it is not true that
$$ a^2 = 2 b^2.$$
-/
theorem sqrt_two_irrational {a b : ℕ} (co : nat.gcd a b = 1) : a^2 ≠ 2 * b^2 :=
begin
    intro h,
    have h1 : 2 ∣ a^2, simp [h],
    have h2 : 2 ∣ a, from nat.prime.dvd_of_dvd_pow nat.prime_two h1,
    cases h2 with c aeq,
    have h3 : 2 * ( 2 * c^2) = 2 * b^2,
        by simp [eq.symm h, aeq]; 
           simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
    have h4 : 2 * c^2 = b^2,
        from nat.eq_of_mul_eq_mul_left dec_trivial h3,
    have h5 : 2 ∣ b^2, by simp [eq.symm h4],
    have hb : 2 ∣ b, from nat.prime.dvd_of_dvd_pow nat.prime_two h5,
    have ha : 2 ∣ a, from nat.prime.dvd_of_dvd_pow nat.prime_two h1,
    have h6 : 2 ∣ nat.gcd a b, from nat.dvd_gcd ha hb,
    have habs : 2 ∣ (1 : ℕ), by 
        {rw co at h6, exact h6},
    have h7 : ¬ 2 ∣ 1, exact dec_trivial,
    exact h7 habs, done
end

end uwyo -- hide
