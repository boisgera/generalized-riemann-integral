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

-- Canonical representation: by construction, "=" works as intended.
-- Note: "inf" and "sup" are the right names because the intervals are nonempty.
-- (they are the infimum and the supremeum)
inductive Interval where
  | empty : Interval
  | ioo (inf : EReal) (sup : EReal) (h : inf < sup) : Interval
  | ioc (inf : EReal) (sup : EReal) (h : inf < sup) : Interval
  | ico (inf : EReal) (sup : EReal) (h : inf < sup) : Interval
  | icc (inf : EReal) (sup : EReal) (h : inf ≤ sup) : Interval

def Interval.toSet (I : Interval) : Set EReal :=
  match I with
      | .empty => ∅
      | .ioo inf sup _ => Set.Ioo inf sup
      | .ioc inf sup _ => Set.Ioc inf sup
      | .ico inf sup _ => Set.Ico inf sup
      | .icc inf sup _ => Set.Icc inf sup

instance : Coe Interval (Set EReal) where
  coe := Interval.toSet

def Interval.mem (I : Interval) (x : EReal) : Prop :=
  match I with
      | .empty => False
      | .ioo inf sup _ => inf < x ∧ x < sup
      | .ioc inf sup _ => inf < x ∧ x ≤ sup
      | .ico inf sup _ => inf ≤ x ∧ x < sup
      | .icc inf sup _ => inf ≤ x ∧ x ≤ sup

instance : Membership EReal Interval where
  mem := Interval.mem

theorem Interval_mem_iff_Set_mem (I : Interval) (x : EReal) :
    x ∈ I ↔ x ∈ (↑I : Set EReal) := by
  conv =>
    lhs ; simp only [Membership.mem]
  simp only [Interval.mem.eq_def]
  simp only [Interval.toSet]
  simp only [Set.Ioo, Set.Ioc, Set.Ico, Set.Icc]
  change (match I with
   | Interval.empty => x ∈ (∅ : Set EReal)
   | Interval.ioo inf sup h => x ∈ {y | inf < y ∧ y < sup}
   | Interval.ioc inf sup h => x ∈ {y | inf < y ∧ y ≤ sup}
   | Interval.ico inf sup h => x ∈ {y | inf ≤ y ∧ y < sup}
   | Interval.icc inf sup h => x ∈ {y | inf ≤ y ∧ y ≤ sup})
  grind

#check Pairwise
-- Pairwise.{u_1} {α : Type u_1} (r : α → α → Prop) : Prop

#print Pairwise
-- def Pairwise.{u_1} : {α : Type u_1} → (α → α → Prop) → Prop :=
-- fun {α} r ↦ ∀ ⦃i j : α⦄, i ≠ j → r i j

/-!
TODO: study this `Pairwise` stuff and how it's done in BoxIntegral.
AFAICT the issue I have is that my "collection" is a (fin)set when
`Pairwise` is meant for types.
-/

#print Set.Pairwise
-- protected def Set.Pairwise.{u_1} : {α : Type u_1} → Set α → (α → α → Prop) → Prop :=
-- fun {α} s r ↦ ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y

#print Disjoint
-- def Disjoint.{u_1} : {α : Type u_1} → [inst : PartialOrder α] → [OrderBot α] → α → α → Prop :=
-- fun {α} [PartialOrder α] [OrderBot α] a b ↦ ∀ ⦃x : α⦄, x ≤ a → x ≤ b → x ≤ ⊥

/-!
Either I need a shittone of coercions, or I need to define a partial order
on Interval that has a ⊥. But since we don't allow the empty set,
I am fucked. OK, let's do this again with an empty set maybe?
-/

/-!
`intervals` is not automatically coerce to Set (Set EReal) since there
are two levels of coercion there and Lean does not compose them automatically.
-/


/-!
Actually I have to look at Fintype instead of finset to get a finite indexed
familiy of intervals.
-/

/-!
Finite partition made of intervals. Maybe work out the stuff with sets and
finite sets and coerce/export to intervals afterwards?
-/
structure Partition where
  intervals : Finset Interval
  nonEmpty : ∀ I ∈ intervals, Set.Nonempty (I : Set EReal)
  pairwiseDisjoints : ∀ I ∈ intervals, ∀ J ∈ intervals,
    I ≠ J → (I : Set EReal) ∩ (J : Set EReal) = ∅

-- TODO: declare membership.

def Partition.toSetOfSets (p : Partition) : Set (Set EReal) :=
  (p.intervals : Set Interval) -- first coerce : Finset Interval → Set interval
  |> Set.image (fun (I : Interval) => (I : Set EReal)) -- internal coercion

instance : Coe (Partition) (Set (Set EReal)) where
  coe := Partition.toSetOfSets

def Partition.sUnion (p : Partition) : Set EReal :=
  ⋃₀ p -- coercion works...

-- read as "is a partition of"
def PartitionOf (p : Partition) (s : Set EReal) : Prop := ⋃₀ p = s

end HK
