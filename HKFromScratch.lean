import Mathlib
import Paperproof

namespace HK

/-!
Aimed reach:
  - HK style only,
  - 1D only, but possibly unbounded,
  - ~~Integration for/based on every Radon measure
    (locally finite, no way to deal with the counting measure for
    example)~~ no, scratch that, let's start with Lebesgue only

TODO:
  - We work on the space [-∞, +∞],
  - Our "boxes" are exactly the non-empty intervals, inc. non-bounded,
  - Partitions are really partitions,
  - "volumes" are scrached, we hard-code length of an interval,
  - Riemann sum cancel by definition every term with an unbounded interval.
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

-- ... but extended real numbers support nothing. (That's fine)

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
-- Set.Icc.{u_1} {α : Type u_1} [Preorder α] (a b : α) : Set α

#reduce I
-- fun x ↦ 0 ≤ x ∧ x ≤ 1

example : Set.Icc (⊥ : EReal) (⊤ : EReal) = Set.univ := by
  rw [← Set.Icc_def, Set.univ]
  ext x
  simp only [Set.mem_setOf]
  rw [iff_true]
  exact And.intro bot_le le_top



/-!
Definition of Intervals
--------------------------------------------------------------------------------
-/

-- Canonical representation of intervals: by construction, "=" works as intended.
-- Note: "inf" and "sup" are the right names because the intervals are nonempty.
-- (they are the infimum and the supremum ; see later)
inductive Interval where
  | empty
  | ioo (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | ioc (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | ico (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | icc (inf : EReal) (sup : EReal) (inf_le_sup : inf ≤ sup)

/-!
Intervals as Sets
--------------------------------------------------------------------------------

Declare an automatic coercion of intervals as sets.
-/

def Interval.toSet (I : Interval) : Set EReal :=
  match I with
      | .empty => ∅
      | .ioo inf sup _ => Set.Ioo inf sup
      | .ioc inf sup _ => Set.Ioc inf sup
      | .ico inf sup _ => Set.Ico inf sup
      | .icc inf sup _ => Set.Icc inf sup

instance : Coe Interval (Set EReal) where
  coe := Interval.toSet

/-!
Membership
--------------------------------------------------------------------------------
-/


/-!
Generally,
- I define the operations using only elementary constructs for intervals
- I prove that these definitions match how the operations on intervals-as-sets
  behave afterwards.
-/
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
  cases I
  · simp only
    exact Set.mem_empty_iff_false x
  repeat
    simp only
    rw [Set.mem_setOf]

#print HasSubset

def Interval.Subset (I J : Interval) : Prop :=
  sorry

instance : HasSubset Interval where
  Subset := Interval.Subset

/-! TODO: check that ⊆ for intervals work for intervals-as-sets -/


/-!
Infimum and Supremum
--------------------------------------------------------------------------------
-/


#print CompleteLinearOrder
-- ...
-- SupSet.sSup : Set α → α
-- CompleteSemilatticeSup.isLUB_sSup : ∀ (s : Set α), IsLUB s (sSup s)
-- InfSet.sInf : Set α → α
-- CompleteSemilatticeInf.isGLB_sInf : ∀ (s : Set α), IsGLB s (sInf s)

#synth CompleteLinearOrder EReal
-- instCompleteLinearOrderEReal

noncomputable def Interval.inf : Interval → EReal
  | .empty => ⊤
  | .ioo inf _ _ => inf
  | .ioc inf _ _ => inf
  | .ico inf _ _ => inf
  | .icc inf _ _ => inf

noncomputable def Interval.sup : Interval → EReal
  | .empty => ⊥
  | .ioo _ sup _ => sup
  | .ioc _ sup _ => sup
  | .ico _ sup _ => sup
  | .icc _ sup _ => sup

theorem Interval.inf_eq_sInf_coe (I : Interval) : I.inf = sInf ↑I := by
  sorry

theorem Interval.sup_eq_sSup_coe (I : Interval) : I.sup = sSup ↑I := by
  sorry



/-!
Empty (and non-empty) intervals
--------------------------------------------------------------------------------
-/

/-- Support the `∅` notation for `Interval.empty` -/
instance : EmptyCollection Interval where
  emptyCollection := Interval.empty

/-!
To show that an interval differs from `∅` iff there is an element in it,
we leverage the (ordered) density of the extended real numbers.
-/

#check DenselyOrdered.dense
-- DenselyOrdered.dense.{u_5} {α : Type u_5}
-- {inst✝ : LT α} [self : DenselyOrdered α]
-- (a₁ a₂ : α) : a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

#synth DenselyOrdered EReal
-- instDenselyOrderedEReal

theorem Interval.nonempty_iff_ne_empty (I : Interval) : I ≠ ∅ ↔ ∃ x, x ∈ I := by
  constructor
  · intro neEmpty
    match I with
    | .empty =>
      nomatch neEmpty
    | .ioo inf sup inf_lt_sup
    | .ioc inf sup inf_lt_sup
    | .ico inf sup inf_lt_sup =>
      have ⟨x, inf_lt_x, x_lt_sup⟩ := DenselyOrdered.dense inf sup inf_lt_sup
      use x
      simp only [Membership.mem, Interval.mem]
      grind
    | .icc inf sup inf_le_sup =>
      use inf
      simp only [Membership.mem, Interval.mem]
      exact ⟨le_rfl, inf_le_sup⟩
  · intro ⟨x, x_in_I⟩
    simp only [Membership.mem, Interval.mem] at x_in_I
    simp only [EmptyCollection.emptyCollection]
    intro I_empty
    simp only [I_empty] at x_in_I

/-- The empty interval corresponds to the empty set. -/
theorem Interval.empty_iff_empty_coe (I : Interval) :
    I = ∅ ↔ (↑I : Set EReal) = ∅ := by
  constructor
  · intro I_eq_empty
    simp only [EmptyCollection.emptyCollection] at I_eq_empty
    simp only [Interval.toSet.eq_def, I_eq_empty]
  · intro I_coe_eq_empty
    simp only [Interval.toSet.eq_def] at I_coe_eq_empty
    match I with
    | empty => rfl
    | ioo inf sup h | ioc inf sup h | ico inf sup h | icc inf sup h =>
      simp only [
        Set.Ioo_eq_empty_iff,
        Set.Ioc_eq_empty_iff,
        Set.Ico_eq_empty_iff,
        Set.Icc_eq_empty_iff
      ] at I_coe_eq_empty
      contradiction




/-!
Connectedness
--------------------------------------------------------------------------------

Being an interval in EReal is exactly being order-connected:
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

#check Set.ordConnected_Ioo
-- Set.ordConnected_Ioo.{u_1} {α : Type u_1} [Preorder α] {a b : α} :
-- (Set.Ioo a b).OrdConnected

theorem interval_iff_ordConnected (s : Set EReal) :
  (∃ (I : Interval), s = I.toSet) ↔ s.OrdConnected := by
  constructor
  · intro ⟨I, hI⟩
    rw [Interval.toSet.eq_def] at hI
    rw [hI]; clear hI
    match I with
    | .empty => simp only; exact Set.ordConnected_empty
    | .ioo inf sup _ =>
      dsimp only ; exact Set.ordConnected_Ioo
    | .ioc inf sup _ =>
      dsimp only ; exact Set.ordConnected_Ioc
    | .ico inf sup _ =>
      dsimp only ; exact Set.ordConnected_Ico
    | .icc inf sup _ =>
      dsimp only ; exact Set.ordConnected_Icc
  · -- TODO: distinguish empty or not
    -- if not empty, find inf and sup
    -- show that only 4 cases are possible
    sorry

--- Interval.ofSet when provided with a set and a prove or order connectedness
noncomputable def Interval.ofSet (s : Set EReal) (ordConnected : s.OrdConnected)
    : Interval :=
  s
    |> interval_iff_ordConnected
    |>.mpr ordConnected
    |> Classical.choose



/-!
TODO: Nonempty (when not .empty)
-/



-- instance : HasSubset Interval where
--   Subset :

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
TODO: define "NonOverlapping". Think hard about it before ; if we define it
with references to sets, can we avoid to deal with a huge combinatorial
cases. Idea: define intersection of intervals to begin with (and check the
consistency of the def with the sets), then NonOverlapping becomes easy
(intersection is either empty or Interval.Icc with the same inf and sup)
-/




structure Partition where
  intervals : Finset Interval
  nonEmpty : ∀ I ∈ intervals, Set.Nonempty (I : Set EReal)
  pairwiseDisjoints : ∀ I ∈ intervals, ∀ J ∈ intervals,
    I ≠ J → (I : Set EReal) ∩ (J : Set EReal) = ∅

structure Partition' where
  intervals : Finset Interval
  nonEmpty : ∀ I ∈ intervals, Set.Nonempty (I : Set EReal)
  pairwiseDisjoints : ∀ I ∈ intervals, ∀ J ∈ intervals,
    I ≠ J → Disjoint (↑I : Set EReal) (↑J : Set EReal)


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

/-!
TODO: consider the collection of all finite unions of intervals,
show that we have a ring (stable by ∪ and \) and even an algebra
(contains the full set).

Note that here we won't require `vol` to be a pre-measure
(we don't want to have anything to do with σ-additivity)
-/

end HK
