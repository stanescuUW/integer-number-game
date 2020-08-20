import data.nat.prime
import data.rat.basic
import data.real.basic
import tactic
import game.basic.level01

namespace uwyo -- hide

/-
# Chapter 1 : Basic facts

## Level 2

In this level you need to prove a slightly different statement
of the fact that `sqrt 2` is irrational. This will require you to work more closely
with Lean's tools for handling rationals.
-/

-- begin hide
lemma rat_times_rat (r : ℚ) : r * r * ↑(r.denom) ^ 2 = ↑(r.num) ^ 2 :=
begin
    have h1 := @rat.mul_denom_eq_num r,
    rw pow_two,
    rw mul_assoc, rw ← mul_assoc r r.denom r.denom,
    rw h1, rw ← mul_assoc, rw mul_comm, rw ← mul_assoc,
    rw mul_comm ↑r.denom r, rw h1, rw pow_two, done
end
-- end hide

/- Lemma
There doesn't exist a rational number `r` such that `r ^ 2 = 2`.
-/
theorem rational_not_sqrt_two : ¬ ∃ r : ℚ, r ^ 2 = (2:ℚ)  := 
begin
    intro h,
    cases h with r H,
    let num := r.num, set den := r.denom with hden,
    --explicitly build the hypothetical rational number r
    have hr := @rat.num_denom r,
    rw ← hr at H, -- use it in the main assumption
    -- now we can figure out some properties of r.num and r.denom
    -- first off, the denominator is not zero; this is encoded in r.
    have hdenom := r.pos,  -- the denom is actually positive
    have hdne : r.denom ≠ 0, linarith, -- so it is non zero; linarith can handle that
    set n := int.nat_abs num with hn1, -- give it a new name to type less
    have hn : (n ^2 : ℤ) = num ^ 2,
        norm_cast, rw ← int.nat_abs_pow_two num, rw ← int.coe_nat_pow,
    have G : (2:ℚ) * (r.denom ^2) = (r.num ^ 2),
        rw ← H, norm_cast, simp,
        rw pow_two r, simp * at *,
        exact rat_times_rat r,
    norm_cast at G,
    rw ← hn at G,
    have g1 : nat.gcd n den = 1, 
        have g11 := r.cop, 
        unfold nat.coprime at g11,
        have g12 := nat.coprime.pow_left 2 g11,
        have g13 := nat.coprime.coprime_mul_left g12,
        rw ← hn1 at g13, exact g13,
    have E := sqrt_two_irrational g1,
    have g2 := G.symm, 
    norm_cast at g2,
    done
end


end uwyo -- hide
