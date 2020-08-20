import tactic
import data.equiv.ring


namespace uwyo

-- Creating the integers starting from the natural numbers.
-- Peter J. Cameron: "Sets, Logic and Categories"
--                    section 1.8, page 29
-- In this construction, think of an integer x as the solution to the equation:
--    x + natnat.snd = natnat.fst
-- So that x = fst - snd effectively, 
-- but avoiding subtraction, which is not defined everywhere
@[ext] structure natnat := 
( fst : ℕ )
( snd : ℕ ) 

namespace natnat

notation `ℕ2` := natnat

def ℕ2_zero : ℕ2 := ⟨ 0, 0 ⟩ 
instance : has_zero ℕ2 := ⟨ ℕ2_zero ⟩
-- these may be useful later on
@[simp] lemma fst_zero : (0 : ℕ2).1 = 0 := by refl
@[simp] lemma snd_zero : (0 : ℕ2).2 = 0 := by refl

-- let's play a little 
def ℕ2_minus_three : ℕ2 := ⟨ 0, 3 ⟩ 
def ℕ2_another_zero : ℕ2 := ⟨ 3, 3 ⟩ 

-- this is our canonical "one"
def ℕ2_one : ℕ2 := ⟨ 1, 0 ⟩ 
def ℕ2_another_one : ℕ2 := ⟨ 3, 2 ⟩ 
instance : has_one ℕ2 := ⟨ ℕ2_one ⟩
-- these may be useful later on
@[simp] lemma fst_one : (1 : ℕ2).1 = 1 := by refl
@[simp] lemma snd_one : (1 : ℕ2).2 = 0 := by refl

-- OK, let's get to business
-- Here is the equivalence relation that defines our integers as equivalence classes.
def same (a b : ℕ2) : Prop := a.1 + b.2 = a.2 + b.1 
notation a `~` b := same a b  -- we shouldn't really need this
instance : has_equiv ℕ2 := ⟨ same ⟩   -- equivalence relation on ℕ2; should ≃ work as notation???

theorem same_equiv : equivalence same := 
begin
    split,
    { -- reflexive:
        intros x, unfold same, rw add_comm, 
    },
    split,
    { -- symmetric
        intros x y hxy, unfold same at *,
        rw [add_comm, add_comm y.snd _],
        exact hxy.symm,
    },
    { -- transitive
        intros x y z H G, 
        unfold same at *, linarith,
    }
end
-- let's check that both our `one`s are in the same equivalence class
lemma check_same_one : ℕ2_one ~ ℕ2_another_one := 
begin
    unfold same, refl,
end
example : ℕ2_zero ~ ℕ2_another_zero := by {unfold same, refl}

-- time to bundle together the set ℕ × ℕ with the equivalence relation "~"
instance : setoid ℕ2 :=
{ 
    r := same,
    iseqv := same_equiv 
}

end natnat 

-- Define the integers

notation `myℤ` := quotient natnat.setoid 
#check myℤ

-- Let's first check the equivalence classes that we set up.

def zero : myℤ := ⟦0⟧  --what 0 is the one in between the brackets? Should come from ℕ2.
def another_zero : myℤ := ⟦ natnat.ℕ2_another_zero ⟧
example : zero = another_zero :=
begin
  apply quot.sound,
  -- ⊢ setoid.r ℕ2_zero ℕ2_another_zero
  -- simp only [setoid.r] is helpful with a goal like this
  show natnat.same natnat.ℕ2_zero natnat.ℕ2_another_zero,
  show 0 + 3 = 3 + 0,
  norm_num, done
end
example : zero = another_zero := 
begin
    apply quot.sound,
    dsimp [setoid.r],
    unfold natnat.same,
    rw [natnat.ℕ2_another_zero],  -- can't rw natnat.ℕ2_zero here, so...
    simp, 
    done
end
example : ⟦ natnat.ℕ2_zero ⟧ = another_zero := 
begin
    apply quot.sound,
    dsimp [setoid.r],
    unfold natnat.same,
    rw [natnat.ℕ2_zero, natnat.ℕ2_another_zero],  -- now I can rw natnat.ℕ2_zero
    done
end
example : ⟦ natnat.ℕ2_one ⟧ = ⟦ natnat.ℕ2_another_one ⟧ := 
begin
    apply quot.sound,
    exact natnat.check_same_one,
end

-- So now the task is to prove that `myℤ` forms a commutative ring with identity and 
-- has no (non-trivial) divisors of zero.
-- First we have to define its operations, addition and multiplication,
-- together with their identity elements. We'll also define order.
-- The operations should work in the following way:
-- Addition: [a,b] + [c,d] = [a+b,c+d]               (check it)
-- Multiplication: [a,b] * [c,d] = [ac+bd, ad + bc]  (check it)
-- Less or equal: [a,b] ≤ [c,d]  ↔  a + d ≤ b + c    (check it)
def our_zero : myℤ := ⟦ natnat.ℕ2_zero ⟧  
instance : has_zero myℤ := ⟨ our_zero ⟩
@[simp] lemma zero_thing : (0 : myℤ) = ⟦0⟧ := rfl   -- ⟦ 0 ⟧ was defined above

def our_one : myℤ := ⟦ natnat.ℕ2_one ⟧
instance : has_one myℤ := ⟨our_one⟩
@[simp] lemma one_thing : (1 : myℤ) = ⟦1⟧ := rfl  --and this?

open natnat

-- Let us define an additional simplification lemma:
@[simp] lemma same_thing (a b : ℕ2) : a ≈ b ↔ a.fst + b.snd = a.snd + b.fst := iff.rfl

--protected def add (a b : myℤ) : myℤ :=  sorry  -- these will probably need `quotient.lift` 
--protected def mul (a b : myℤ) : myℤ :=  sorry
--protected def le (a b : myℤ) : Prop :=  sorry

-- Lean help us be certain our definitions make sense
-- For example for addition: if a1, a2, b1 and b2 are of type `natnat`
-- And:     a1 ~ b1 and a2 ~ b2
-- Then our definition of addition should be such that:
--          a1 + a2 ~ b1 + b2 
-- This is what `quotient.lift_on₂` is designed to take care of:
@[simp] def add (a b : myℤ) : myℤ := quotient.lift_on₂ a b 
    ( λ z w, ⟦ natnat.mk (z.fst + w.fst) (z.snd + w.snd) ⟧  ) 
begin
    intros a1 a2 b1 b2 hab1 hab2,
    change a1.1 + b1.2 = a1.2 + b1.1 at hab1, 
    change a2.1 + b2.2 = a2.2 + b2.1 at hab2, 
    simp at *, 
    set A1 := a1.fst + a2.fst with hA1,
    set A2 := a1.snd + a2.snd with hA2, 
    set B1 := b1.fst + b2.fst with hB1,
    set B2 := b1.snd + b2.snd with hB2,
    change A1 + B2 = A2 + B1,
    linarith,
end
-- one thing that I'm still not certain of is whether we want "protected" or not
-- for these definitions
-- Now we can declare the addition operation on our integers:
instance : has_add myℤ := ⟨ add ⟩

-- Now that we have addition we can also define the additive inverse;
-- Again, Lean allows us to make sure the inverse is correctly defined:
-- If a1 and b1 are of type `natnat` and a1 ~ b1 
-- Then (- a1) ~ (- b1)
@[simp] def neg (a : myℤ) : myℤ := 
    quotient.lift_on a ( λ b, ⟦ natnat.mk b.snd b.fst ⟧ )
begin
  intros a1 b1 hab1,
  change a1.1 + b1.2 = a1.2 + b1.1 at hab1, 
  simp at *,
  change a1.snd + b1.fst = a1.fst + b1.snd, 
  omega,  -- another tactic that can be used with nat/int
end
-- So now we can also declare the additive inverse (negation)
instance : has_neg myℤ := ⟨ neg ⟩
-- With these two instances we can now use our usual notation for addition and inverse:
@[simp] lemma add_thing (a b : myℤ) : a + b = add a b := rfl
@[simp] lemma neg_thing (a   : myℤ) : - a   = neg a   := rfl

----- an important simp lemma (original idea due to Kenny Lau) that rewrites quotient terms
----- this has been incorporated in `mathlib` now
--@[simp] theorem quotient.lift_on_beta₂ {α : Type} {β : Type} [setoid α] (f : α → α → β) (h)
--  (x y : α) : ⟦x⟧.lift_on₂ ⟦y⟧ f h = f x y := rfl
----- this is my rewriting of it in mathlib style
--@[simp] theorem quotient.lift_on_beta_v2 {α : Type} {β : Type} [setoid α] (f : α → α → β) (h) 
--  (x y : α) : quotient.lift_on₂ (quotient.mk x) (quotient.mk y) f h = f x y := rfl
----- this is the `mathlib` style proof
--@[simp] theorem quotient.lift_on_beta₂ {α : Type} {β : Type} [setoid α] (f : α → α → β) 
--  (h : ∀ (a₁ a₂ b₁ b₂ : α), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) (x y : α) : 
--  quotient.lift_on₂ (quotient.mk x) (quotient.mk y) f h = f x y := rfl

-- Which brings us to the point where we can show that our integers form an additive
-- group under addition as defined above:
instance : add_comm_group myℤ :=
{ add := has_add.add,
  add_assoc := begin
    intros a b c, 
    apply quotient.induction_on₃ a b c,
    intros a b c,
    simp * at *,
    omega, done
  end,
  zero := has_zero.zero,
  zero_add := begin
    intros a,
    apply quotient.induction_on a,
    simp * at *, 
    intros, omega, done
  end,
  add_zero := begin
    intros a,
    apply quotient.induction_on a,
    intros,
    simp * at *,
    omega, done
  end,
  neg := has_neg.neg,
  add_left_neg := begin
    intro z, apply quotient.induction_on z,
    intro a,
    simp * at *, -- uses quotient.lift_on_beta₂ to simplify
    exact add_comm _ _, done
  end,
  add_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b,
    simp * at *,
    intros, 
    omega, done
  end 
}

-- So let's move on to multiplication. First we have to define it
-- This is a little on the long side.
@[simp] def mul (a b : myℤ) : myℤ := quotient.lift_on₂ a b ( λ z w, 
  ⟦ natnat.mk (z.fst * w.fst + z.snd * w.snd ) (z.fst * w.snd + z.snd * w.fst) ⟧  ) 
begin
  intros a1 a2 b1 b2 hab1 hab2,
  simp * at *,
  nlinarith, done
end
instance : has_mul myℤ := ⟨mul⟩
@[simp] lemma mul_thing (a b : myℤ) : a * b = mul a b := rfl 

-- So we're ready to go for the full structure on the integers:
instance : comm_ring myℤ :=
{ mul := has_mul.mul,
  mul_assoc := begin 
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros a1 b1 c1,
    simp only [mul, mul_thing, quotient.lift_on_beta₂, same_thing, quotient.eq],
    ring, done
  end,
  one := has_one.one,
  one_mul := begin 
    intro a,
    apply quotient.induction_on a,
    intros,
    simp only [mul, mul_thing, add_zero, one_mul, fst_one, zero_mul, snd_one, 
               one_thing, quotient.lift_on_beta₂, same_thing, quotient.eq],
    ring,
  end,
  mul_one := begin 
    intro a,
    apply quotient.induction_on a,
    intros,
    simp,
    ring,
  end,
  left_distrib := begin 
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    apply quotient.sound,
    simp,
    ring,
  end,
  right_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    intros,
    apply quotient.sound,
    simp,
    ring,
  end,
  mul_comm := begin 
    intros a b,
    apply quotient.induction_on₂ a b,
    intros,
    simp,
    ring,
  end,
  ..uwyo.add_comm_group }

-------------------------------------------------------------------------------
-- Work in progress below this line:
#check quotient.eq  -- this could be used instead of quotient.sound
#check quotient.sound
#check quotient.lift_on our_one --
#check quotient.lift_beta --
#check quotient.lift_on_beta --
#check quotient.lift_on_beta₂
#check quotient.lift_on₂ --
#check quotient.lift
#check quot.map
-------------------------------------------------------------------------------

end uwyo