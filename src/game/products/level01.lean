import tactic
import data.rat
import data.real.basic
import data.real.irrational
import game.basic.level02

namespace uwyo -- hide
open real -- hide

/-
# Chapter 3 : Products

## Level 1

-/

/- Lemma
The product of a rational and an irrational number may be a rational.
-/
theorem irrat_prod : ¬ (∀ (a : ℝ), ∀ (b : ℚ), irrational a → irrational (a*b)) :=
begin
    intro H,
    have H1 := H (sqrt 2) (0: ℚ),
    have H2 := H1 irrational_sqrt_two,
    apply H2,
    existsi (0 : ℚ), simp, done
end

end uwyo -- hide
