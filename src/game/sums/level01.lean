import tactic
import data.rat
import data.real.basic
import data.real.irrational
import game.basic.level02

namespace uwyo -- hide
open real -- hide


/-
# Chapter 2 : Sums

## Level 1

-/

/- Lemma
There are irrational numbers that sum up to a rational.
-/
theorem irrat_sum : ¬ (∀ (x y : ℝ), irrational x → irrational y → irrational (x+y)) :=
begin
  intro H,
  have H2 := H (sqrt 2) (-sqrt 2),
  have H3 := H2 irrational_sqrt_two (irrational.neg irrational_sqrt_two),
  apply H3,
  existsi (0 : ℚ),
  simp, done
end

end uwyo -- hide
