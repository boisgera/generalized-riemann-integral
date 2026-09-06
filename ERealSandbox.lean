import Mathlib

#print EReal
-- def EReal : Type := WithBot (WithTop ℝ)

/-!
`WithTop` and `WithBot` are `Option` wrappers.
-/

#print WithTop
-- def WithTop.{u_2} : Type u_2 → Type u_2 :=
-- fun α ↦ Option α

#print WithBot
-- def WithBot.{u_2} : Type u_2 → Type u_2 :=
-- fun α ↦ Option α

/-!
So at the basic level, we can always pattern match like that:
-/

/-!
There is no support for the notation `∞` or `-∞`;
we should use `⊤` (`some none`) and `⊥` (`none`) instead.
-/

#reduce match (⊤ : EReal) with
  | some (some _) => "real"
  | some none => "+∞"
  | none => "-∞"
-- "+∞"


#reduce match (⊤ : EReal) with
  | ⊤ => "+∞"
  | ⊥ => "-∞"
  | some (some _) => "real"
-- "+∞"

/-!
That version is idiomatic (robust wrt a potential change in the implementation
of EReal)
-/

#reduce match (⊤ : EReal) with
  | (_ : ℝ) => "real"
  | ⊤ => "+∞"
  | ⊥ => "-∞"
-- "+∞"


/-
The types `WithTop α` and `WithBot α` inherit a bunch instances when the
corresponding instance exists for `α`, then may have some extra properties.
For example, `EReal`:
- has a linear order (inherited)
- has a *complete* linear order (ℝ is merely *conditionally* complete)
- is densely ordered
- have greatest and least elements (`bot` and `top` are defined as well
  as the notations `⊥` and `⊤` and le_top` and `bot_le` hold)
-/

#synth LinearOrder EReal
-- instLinearOrderEReal

#synth CompleteLinearOrder EReal
-- instCompleteLinearOrderEReal

#synth DenselyOrdered EReal
-- instDenselyOrderedEReal

#synth OrderTop EReal
-- CompletelyDistribLattice.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop

#synth OrderBot EReal
-- CompleteLattice.toCompletePartialOrder.toOrderBot

noncomputable def inf : EReal := ⊤
noncomputable def negInf : EReal := ⊥

/-!
We can define natural numbers, integers, real numbers and non-negative
extended real numbers as extended reals.
Note that `EReal` doesn't support the scientific notation, so we need to
explictly qualify a number in floating-point notation as a real number before
we can cast it an extended real number.
-/

noncomputable def zero : EReal := 0
noncomputable def one : EReal := 1
noncomputable def negOne : EReal := -1


noncomputable def alsoZero : EReal := (0 : ℝ)
noncomputable def alsoOne : EReal := (1 : ℝ)
noncomputable def almostPi : EReal := (3.14 : ℝ)

noncomputable def alsoOne' : EReal := (1 : ENNReal)

/-!
Real numbers have no instance of `ToString`, but the have an instance of`Repr`.
However extended real numbers have neither. We can still `#reduce` them
however.
-/

#eval repr (3.14 : Real)
-- Real.ofCauchy (sorry /- (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50,
-- (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50,
-- (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, ... -/)

-- noncomputable: can't be #eval'd but can be #reduce'd
#reduce one
-- some (some Real.wrapped✝.1)

#reduce inf
-- some none

#reduce negInf
-- none

-- Intermediate coercion needed since extended reals don't support `OfScientific`.
#reduce ((4.5 : Real) : EReal)
-- some
--   (some
--     {
--       cauchy :=
--         Quot.mk (fun f g ↦ (f - g).LimZero) ⟨fun x ↦ { num := Int.ofNat 9, den := 2, den_nz := ⋯, reduced := ⋯ }, ⋯⟩ })


/-!
I should explore the [extended real numbers API doc] thoroughly.

[extended real numbers API doc]: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/EReal/Basic.html>

-/

/-!
Operations
--------------------------------------------------------------------------------
-/

/-!
Let's track for example where/how is defined the division between extended
real numbers.
-/

#synth Div EReal
-- EReal.instDivInvMonoid.toDiv

#print EReal.instDivInvMonoid
-- @[implicit_reducible] def EReal.instDivInvMonoid : DivInvMonoid EReal :=
-- { toMonoid := EReal.instCommMonoidWithZero.toMonoidWithZero.toMonoid,
--   inv := EReal.inv, div := DivInvMonoid.div',
--   zpow := zpowRec, div_eq_mul_inv := EReal.instDivInvMonoid._proof_1, zpow_zero' := EReal.instDivInvMonoid._proof_2,
--   zpow_succ' := EReal.instDivInvMonoid._proof_3, zpow_neg' := EReal.instDivInvMonoid._proof_4 }

#print EReal.inv
-- protected def EReal.inv : EReal → EReal :=
-- fun x ↦
--   match x with
--   | none => 0
--   | some none => 0
--   | some (some x) => ↑x⁻¹

/-!
OK, and then I guess that `x / y` is defined as `x * y⁻¹` in the `DivInvMonoid`???
-/

#print DivInvMonoid.div'
-- def DivInvMonoid.div'.{u} : {G : Type u} → [Monoid G] → [Inv G] → G → G → G :=
-- fun {G} [Monoid G] [Inv G] a b ↦ a * b⁻¹

/-!
OK, all this makes sense! So they don't have to deal with a 3×3 pattern matching
expression when they define this binary operation on extended real numbers,
they just extend the inverse (3 cases) and use it to define /.
-/

#print EReal.mul

#synth HMul EReal EReal EReal
-- instHMul

#print instHMul

#reduce (1 : EReal) / 2

example (x : EReal) (x_lt_top : x < ⊤) : x / 2 < ⊤ := by
  rw [div_eq_mul_inv, lt_top_iff_ne_top]
  match x with
  | (r : Real) =>
    rw [show (2 : EReal)⁻¹ = ((2⁻¹ : ℝ) : EReal) from by norm_cast, ← EReal.coe_mul]
    exact EReal.coe_ne_top _
  | ⊥ =>
    have : (0 < (2⁻¹ : EReal)) := by
      rw [show (2 : EReal)⁻¹ = ((2⁻¹ : ℝ) : EReal) from by norm_cast]
      norm_num
    rw [EReal.bot_mul_of_pos (this)]
    exact bot_ne_top
  | ⊤ =>
    exact absurd x_lt_top (lt_irrefl ⊤)


example (x : EReal) (x_lt_top : x < ⊤) : x / 2 < ⊤ := by
  simp only [lt_top_iff_ne_top] at *
  rw [DivInvMonoid.div_eq_mul_inv]
  rw [show (2⁻¹ : EReal) = (↑(2⁻¹ : Real)) from by norm_cast]
  simp only [HMul.hMul, Mul.mul, EReal.mul]
  -- At this point, the goal is an expression embedding a 3*3 pattern match on
  -- a pair extended real numbers, but most of the cases are absurd.
  split -- 3*3 = 9 goals
  any_goals contradiction -- down to 2 goals!
  · rename_i y h_eq
    have : (↑y : EReal) = (↑2⁻¹ : EReal) := h_eq.symm
    have : y = 2⁻¹ := by
      apply EReal.coe_eq_coe_iff.mp
      exact this
    have : y > 0 := by
      rw [this]
      norm_num
    simp [this]
  · apply EReal.coe_ne_top




/-!
Intervals
--------------------------------------------------------------------------------

I can use Icc, Ioo, etc. as usual since there is a linear order on EReal.

-/

def I : Set EReal := Set.Icc (0 : EReal) (1 : EReal)

#check Set.Icc
-- Set.Icc.{u_1} {α : Type u_1} [Preorder α] (a b : α) : Set α

#reduce I
-- fun x ↦ 0 ≤ x ∧ x ≤ 1

example : Set.Icc (⊥ : EReal) (⊤ : EReal) = Set.univ := by
  rw [← Set.Icc_def, Set.univ]
  ext x
  simp only [Set.mem_setOf]
  rw [iff_true]
  exact And.intro bot_le le_top
