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
-- (they are the infimum and the supremum. TODO: prove this!)
inductive Interval where
  | empty
  | ioo (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | ioc (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | ico (inf : EReal) (sup : EReal) (inf_lt_sup : inf < sup)
  | icc (inf : EReal) (sup : EReal) (inf_le_sup : inf ≤ sup)

def Interval.toSet (I : Interval) : Set EReal :=
  match I with
      | .empty => ∅
      | .ioo inf sup _ => Set.Ioo inf sup
      | .ioc inf sup _ => Set.Ioc inf sup
      | .ico inf sup _ => Set.Ico inf sup
      | .icc inf sup _ => Set.Icc inf sup

instance : Coe Interval (Set EReal) where
  coe := Interval.toSet

-- TODO: support ∅ notation (and prob more isEmpty stuff and co.)

instance : EmptyCollection Interval where
  emptyCollection := Interval.empty

-- TODO : pick the middle, execept when a bound is ⊥ or ⊤, then be smarter
-- to ensure that whatever the case, the element is in the interval.
def midLike (I : Interval) (nonEmpty : I ≠ ∅) : EReal :=
  match I with
  | .empty => -- impossible
    simp [EmptyCollection.emptyCollection] at nonEmpty
    sorry -- impossible
  | .ioo inf sup inf_lt_sup => sorry
  | .ioc inf sup inf_lt_sup => sorry
  | .ico inf sup inf_lt_sup => sorry
  | .icc inf sup inf_le_sup => sorry

-- Then prove the property (it is in the original interval)



theorem Interval.empty_iff_empty_coe (I : Interval) : I = ∅ ↔ (↑I : Set EReal) = ∅ := by
  constructor
  · intro I_empty
    simp only [EmptyCollection.emptyCollection] at I_empty
    rw [I_empty]
    simp only [Interval.toSet.eq_def]
  · intro h
    rw [Interval.toSet.eq_def] at h
    match I with
    | .empty => rfl
    | .ioo inf sup inf_lt_sup =>
      dsimp at h
      let mid := (inf + sup) / 2 -- Nah we need to special-case ⊥ and ⊤
      have h1 : inf < mid := by grind
      have h2 : mid < sup := by grind
      sorry
    | .ioc inf sup inf_lt_sup => sorry
    | .ico inf sup inf_lt_sup => sorry
    | .icc inf sup inf_le_sup => sorry
-- TODO: instance NonEmpty when appropriate

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
TODO: Show that we capture *exactly* the ordered connected sets of EReal,
but in an explicit way.
-/
#check Set.ordConnected_Ioo

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

/-!
Here I define the operation using the specifics of intervals
and prove with a theorem that it matches how sets behave.
What's the argument for this approach instead of the reverse? And the cons?
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

def Interval.Subset (I J : Interval) : Prop :=
  sorry

instance : HasSubset Interval where
  Subset := Interval.Subset



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
