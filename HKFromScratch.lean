import Mathlib
import Paperproof

namespace HK

/-!
Aimed reach:
  - HK style only,
  - 1D only, but possibly unbounded,
  - Integration for/based on every Radon measure
    (locally finite, no way to deal with the counting measure for
    example)

TODO:
  - We work on the space [-∞, +∞],
  - Our "boxes" are exactly the non-empty intervals, inc. non-bounded,
  - Partitions are really partitions,
  - "volumes" associated to intervals live are into [0, +∞]
  - "volumes"
  - Riemann sum cancel by definition every term with and infinite
    volume.
-/


#print EReal
-- def EReal : Type :=
-- WithBot (WithTop ℝ)

/-!
`WithTop` and `WithBot` are mere `Option` wrappers.
-/
#print WithTop
-- def WithTop.{u_2} : Type u_2 → Type u_2 :=
-- fun α ↦ Option α

#print WithBot
-- def WithBot.{u_2} : Type u_2 → Type u_2 :=
-- fun α ↦ Option α

noncomputable def inf : EReal := ⊤
noncomputable def negInf : EReal := ⊥
noncomputable def one : EReal := (1 : Real)

-- We can coerce real numbers as extended reals

-- toString doesn't support real numbers, but repr does

#eval repr (3.14 : Real)
-- Real.ofCauchy (sorry /- (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, (157 : Rat)/50, ... -/)

-- ... but extended real numbers support nothing.

-- noncomputable: can't be #eval'd but can be #reduce'd
#reduce one
-- some (some Real.wrapped✝.1)

#reduce inf
-- some none

#reduce negInf
-- none

-- Intermediate coercion needed since extended reals don't support OfScientific
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
I can use Icc, Ioo, etc. as usual since there is a linear order on EReal.

-/

def I : Set EReal := Set.Icc (0 : EReal) (1 : EReal)

#check Set.Icc

#reduce I
-- fun x ↦ 0 ≤ x ∧ x ≤ 1

example : Set.Icc (⊥ : EReal) (⊤ : EReal) = Set.univ := by
  rw [← Set.Icc_def, Set.univ]
  ext x
  simp only [Set.mem_setOf]
  rw [iff_true]
  exact And.intro bot_le le_top

/-!
Being an interval in EReal is being order-connected:
-/

#print Set.OrdConnected
-- class Set.OrdConnected.{u_1} {α : Type u_1} [Preorder α] (s : Set α) : Prop
-- ...
--   Set.OrdConnected.out' : ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
--   ...

#check Set.OrdConnected.out
-- Set.OrdConnected.out.{u_1} {α : Type u_1} [Preorder α] {s : Set α}
-- (h : s.OrdConnected) ⦃x : α⦄ :
-- x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s

-- TODO: being order-connected means

-- Canonical representation by construction.
-- Note: "inf" and "sup" are the right names because the intervals are nonempty
inductive NonEmptyInterval where
  | ioo (inf : EReal) (sup : EReal) (h : inf < sup) : NonEmptyInterval
  | ioc (inf : EReal) (sup : EReal) (h : inf < sup) : NonEmptyInterval
  | ico (inf : EReal) (sup : EReal) (h : inf < sup) : NonEmptyInterval
  | icc (inf : EReal) (sup : EReal) (h : inf ≤ sup) : NonEmptyInterval

instance : Coe NonEmptyInterval (Set EReal) where
  coe i := match i with
    | .ioo inf sup _ => Set.Ioo inf sup
    | .ioc inf sup _ => Set.Ioc inf sup
    | .ico inf sup _ => Set.Ico inf sup
    | .icc inf sup _ => Set.Icc inf sup

#check Pairwise
-- Pairwise.{u_1} {α : Type u_1} (r : α → α → Prop) : Prop

#print Pairwise
-- def Pairwise.{u_1} : {α : Type u_1} → (α → α → Prop) → Prop :=
-- fun {α} r ↦ ∀ ⦃i j : α⦄, i ≠ j → r i j

structure Partition where
  intervals : Finset NonEmptyInterval

  disjoints: Pairwise (fun A B => Disjoint A B)
