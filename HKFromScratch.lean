import Mathlib
import Mathlib.Topology.Defs.Filter
import Paperproof

open Topology


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
Definition of Intervals and Boxes
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

structure Box where
  inf : EReal
  sup : EReal
  inf_le_sup : inf ≤ sup

def Box.toInterval (box : Box) : Interval :=
  Interval.icc box.inf box.sup box.inf_le_sup

instance : Coe Box Interval where
  coe := Box.toInterval

/-!
TODO: Have all the set-like operation also work for Box
(just inherit from Interval)
-/

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
Later, we do the opposite, assuming that the set if order-connected.
-/

/-!
Membership
--------------------------------------------------------------------------------
-/

/-!
Generally,
- I define the operations using only elementary constructs for intervals
- I prove that these definitions match how the operations on intervals-as-sets
  behave afterwards.
- Box piggybacks on the Interval def.
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


instance : Membership EReal Box where
  mem (box : Box):= (↑box : Interval).mem


#print HasSubset
-- class HasSubset.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   HasSubset.Subset : α → α → Prop
-- constructor:
--   HasSubset.mk.{u} {α : Type u} (Subset : α → α → Prop) : HasSubset α

/-! TODO

-- def Interval.Subset (I J : Interval) : Prop :=
--   match I, J with
--   | empty, _ => True
--   | .ioo inf sup,

-- instance : HasSubset Interval where
--   Subset := Interval.Subset

-/

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



/-- Give an interval when provided with a set and a proof or its connectedness -/
noncomputable def Interval.ofSet (s : Set EReal) (ordConnected : s.OrdConnected)
    : Interval :=
  s
    |> interval_iff_ordConnected
    |>.mpr ordConnected
    |> Classical.choose

/-!
The associated coercion would be not a `Coe` but a `CoeDep`, I don't want to
get into this, let's keep the explicit `ofSet`.
-/


/-!
Topology
--------------------------------------------------------------------------------
-/

#synth TopologicalSpace EReal
-- EReal.instTopologicalSpace

/-!
The topology on [-∞, +∞] is the (pre-)order topology, which is generated by
the collections of [-∞, x[ and ]x,+∞] when x varies in [-∞, +∞].
As a consequence, we have:
-/

#check isOpen_Ioi
-- isOpen_Ioi.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] {a : α} : IsOpen (Set.Ioi a)

#check isOpen_Iio
-- isOpen_Ioi.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] {a : α} : IsOpen (Set.Ioi a)



/-!
Tagged Stuff
--------------------------------------------------------------------------------
-/


structure TaggedBoxes.{u} (ι : Type u) [Fintype ι] where
  box : ι → Box
  tag : ι → EReal


def TaggedBoxes.IsHenstock {ι} [Fintype ι] (π : TaggedBoxes ι) : Prop :=
  ∀ i, π.tag i ∈ (↑(π.box i) : Interval)

def TaggedBoxes.cover {ι} [Fintype ι] (π : TaggedBoxes ι) : Set EReal := ⋃ i, (π.box i)

def Interval.NonOverlapping (s t : Interval) : Prop :=
  Set.Subsingleton ((s : Set EReal) ∩ (t : Set EReal))

def TaggedBoxes.NonOverlapping {ι} [Fintype ι] (π : TaggedBoxes ι) : Prop :=
  ∀ i j, π.box i ≠ π.box j → Interval.NonOverlapping (π.box i) (π.box j)

structure TaggedDivision.{u} (ι : Type u) [Fintype ι] extends TaggedBoxes ι where
  isHenstock : toTaggedBoxes.IsHenstock
  nonOverlapping : toTaggedBoxes.NonOverlapping

/-!
Gauges
--------------------------------------------------------------------------------

Since we (may) work in [-∞, +∞], there are issue with gauges as real-valued
functions. Instead we use function whose values are neighbourhoods of the
reference point.
-/

#check nhds
-- nhds.{u_3} {X : Type u_3} [TopologicalSpace X] (x : X) : Filter X

#print Filter
-- structure Filter.{u_1} (α : Type u_1) : Type u_1
-- number of parameters: 1
-- fields:
--   Filter.sets : Set (Set α)
--   Filter.univ_sets : Set.univ ∈ self.sets
--   Filter.sets_of_superset : ∀ {x y : Set α}, x ∈ self.sets → x ⊆ y → y ∈ self.sets
--   Filter.inter_sets : ∀ {x y : Set α}, x ∈ self.sets → y ∈ self.sets → x ∩ y ∈ self.sets
-- constructor:
--   Filter.mk.{u_1} {α : Type u_1} (sets : Set (Set α)) (univ_sets : Set.univ ∈ sets)
--     (sets_of_superset : ∀ {x y : Set α}, x ∈ sets → x ⊆ y → y ∈ sets)
--     (inter_sets : ∀ {x y : Set α}, x ∈ sets → y ∈ sets → x ∩ y ∈ sets) : Filter α

#print Set.Icc

structure Gauge where
  toFun : EReal → Set EReal
  mem_nhds : ∀ x : EReal, toFun x ∈ 𝓝 x

instance : CoeFun Gauge (fun _ => EReal → Set EReal) where
  coe g := g.toFun

/-!
TODO:
  - TODO: make a "numerical gauge" where the δ > 0 is interpreted differently
    when x is -∞ or +∞? (via 1/x?)
-/


def TaggedBoxes.subordinateTo {ι} [Fintype ι] (π : TaggedBoxes ι)
    (γ : Gauge) : Prop :=
    ∀ (i : ι), ↑(π.box i) ⊆ γ (π.tag i)

notation:50 π " ≼ " γ => TaggedBoxes.subordinateTo π γ

/-!
Cousin Lemma
--------------------------------------------------------------------------------
-/

#check IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
-- IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed.{u, v} {X : Type u} [TopologicalSpace X] {ι : Type v}
--   [hι : Nonempty ι] (t : ι → Set X) (htd : Directed (fun x1 x2 ↦ x1 ⊇ x2) t) (htn : ∀ (i : ι), (t i).Nonempty)
--   (htc : ∀ (i : ι), IsCompact (t i))
--   (htcl : ∀ (i : ι), IsClosed (t i)) : (⋂ i, t i).Nonempty

/-!
Let's simplify this, since we are in an (easier) specific case.
-/

theorem nonempty_iInter_of_antitone_nonempty_isClosed.{v}
    {ι : Type v} [LinearOrder ι] [hι : Nonempty ι] (t : ι → Set EReal)
    (hta : Antitone t) (htn : ∀ (i : ι), (t i).Nonempty)
    (htcl : ∀ (i : ι), IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have htc (i : ι) : IsCompact (t i) := IsClosed.isCompact (htcl i)
  have htd : Directed (fun x1 x2 ↦ x1 ⊇ x2) t := Antitone.directed_ge hta
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

/-!
TODO: we need TaggedBoxes.cover and concept of taggedBoxes subordinate to a gauge
before we can proceed.
-/

theorem Cousin_lemma.{u} (γ : Gauge) (box : Box) :
    ∃ (ι : Type u) (hf : Fintype ι) (π : TaggedDivision ι),
    π.cover = ↑box ∧ π.toTaggedBoxes ≼ γ
    := by
  sorry

/-!
Small lemma: if we start with a tagged partition with one cell which is
the base box and merelely split on some of the cells, the π.cover = ↑box
is "obvious" at each step.

We need to construct the basic "split this one", aggregrate with the rest
mutation step...
-/

def NoGauge.{u} (γ : Gauge) (box : Box): Prop :=
    ∀ (ι : Type u) (_ : Fintype ι) (π : TaggedDivision ι),
    π.cover = ↑box → ¬ π.toTaggedBoxes ≼ γ

noncomputable def Box.midPoint__deprecated (box : Box) : EReal :=
  match hinf : box.inf, hsup : box.sup with
  | ⊥, ⊥ => ⊥
  | ⊥, ⊤ => 0
  | ⊥, some (some y) => y - 1
  | ⊤, ⊥ =>
    have inf_le_sup := box.inf_le_sup
    have top_le_bot : (⊤ : EReal) ≤ (⊥ : EReal) := by
      simp only [hinf, hsup] at inf_le_sup
      exact inf_le_sup
    have bot_lt_top : (⊥ : EReal) < (⊤ : EReal) := bot_lt_top
    have false : False := by grind
    nomatch false
  | ⊤, ⊤ => ⊤
  | ⊤, some (some y) =>
    have inf_le_sup := box.inf_le_sup
    have top_le_y : (⊤ : EReal) ≤ (↑y : EReal) := by
      rw [hinf, hsup] at inf_le_sup
      exact inf_le_sup
    have y_le_top := le_top (a := (↑y : EReal))
    have top_eq_y := LE.le.antisymm top_le_y y_le_top
    nomatch top_eq_y
  | some (some x), ⊥ =>
    have inf_le_sup := box.inf_le_sup
    have x_le_bot : (↑x : EReal) ≤ ⊥ := by
      rw [hinf, hsup] at inf_le_sup
      exact inf_le_sup
    have x_eq_bot := LE.le.antisymm x_le_bot (bot_le (a := (↑x : EReal)))
    nomatch x_eq_bot
  | some (some x), ⊤ => x + 1
  | some (some x), some (some y) => (x + y) / 2

-- This is a mess, I should factor out the three cases that can't exist

theorem Box.absurd_1 (box : Box)
    (hinf : box.inf = ⊤) (hsup : box.sup = ⊥) : False := by
  have inf_le_sup := box.inf_le_sup
  have top_le_bot : (⊤ : EReal) ≤ (⊥ : EReal) := by
    simp only [hinf, hsup] at inf_le_sup
    exact inf_le_sup
  have bot_lt_top : (⊥ : EReal) < (⊤ : EReal) := bot_lt_top
  exact (by grind)

theorem Box.absurd_2 (box : Box)
    (hinf : box.inf = ⊤) (hsup : ∃ y : ℝ, box.sup = ↑y) : False := by
  have inf_le_sup := box.inf_le_sup
  have ⟨y, hsupy⟩ := hsup
  have top_le_y : (⊤ : EReal) ≤ (↑y : EReal) := by
    rw [hinf, hsupy] at inf_le_sup
    exact inf_le_sup
  have y_le_top := le_top (a := (↑y : EReal))
  have top_eq_y := LE.le.antisymm top_le_y y_le_top
  nomatch top_eq_y

theorem Box.absurd_3 (box : Box)
    (hinf : ∃ x : ℝ, box.inf = ↑x) (hsup : box.sup = ⊥) : False := by
  have inf_le_sup := box.inf_le_sup
  have ⟨x, hinfx⟩ := hinf
  have x_le_bot : (↑x : EReal) ≤ ⊥ := by
    rw [hinfx, hsup] at inf_le_sup
    exact inf_le_sup
  have x_eq_bot := LE.le.antisymm x_le_bot (bot_le (a := (↑x : EReal)))
  nomatch x_eq_bot

noncomputable def Box.midPoint (box : Box) : EReal :=
  match hinf : box.inf, hsup : box.sup with
  | ⊥, ⊥ => ⊥
  | ⊥, ⊤ => 0
  | ⊥, some (some y) => y - 1
  | ⊤, ⊥ => nomatch box.absurd_1 hinf hsup
  | ⊤, ⊤ => ⊤
  | ⊤, some (some y) => nomatch box.absurd_2 hinf ⟨y, hsup⟩
  | some (some x), ⊥ => nomatch box.absurd_3 ⟨x, hinf⟩ hsup
  | some (some x), ⊤ => x + 1
  | some (some x), some (some y) => (x + y) / 2

theorem Box.midPointMem (box : Box) : box.midPoint ∈ box := by
  constructor
  · rw [Box.midPoint]
    split
    · rename_i hinf hsup
      rw [hinf]
      exact le_refl (a := ⊥)
    · rename_i hinf hsup
      rw [hinf]
      exact bot_le
    · rename_i y hinf hsup
      rw [hinf]
      exact bot_le
    · rename_i hinf hsup
      nomatch box.absurd_1 hinf hsup
    · rename_i hinf hsup
      rw [hinf]
      exact le_refl (a := ⊤)
    · rename_i y hinf hsup
      nomatch box.absurd_2 hinf ⟨y, hsup⟩
    · rename_i x hinf hsup
      nomatch box.absurd_3 ⟨x, hinf⟩ hsup
    · rename_i x hinf hsup
      rw [hinf]
      have x_le_succ_x : x ≤ x + 1 := by linarith
      have : (some (some x) : Option (WithTop ℝ)) = (↑x : EReal)  := rfl
      simp only [this]
      exact_mod_cast x_le_succ_x
    · rename_i x y hinf hsup
      rw [hinf]
      have inf_le_sup := box.inf_le_sup
      rw [hinf, hsup] at inf_le_sup
      have inf_le_sup' : (↑x : EReal) ≤ (↑y : EReal) := inf_le_sup
      have : x ≤ y := by exact_mod_cast inf_le_sup'
      have le : x ≤ (x + y) / 2 := by linarith
      have : (some (some x) : Option (WithTop ℝ)) = (↑x : EReal) := rfl
      simp only [this]
      have h2 : (2 : EReal) = (↑(2 : ℝ) : EReal) := by norm_cast
      rw [h2, ← EReal.coe_add, ← EReal.coe_div]
      exact_mod_cast le
  · rw [Box.midPoint]
    split
    · rename_i hinf hsup
      rw [hsup]
      exact le_refl (a := ⊥)
    · rename_i hinf hsup
      rw [hsup]
      exact le_top
    · rename_i y hinf hsup
      rw [hsup]
      have : (some (some y) : Option (WithTop ℝ)) = (↑y : EReal) := rfl
      simp only [this]
      have y_sub_one_le_y : y - 1 ≤ y := by linarith
      exact_mod_cast y_sub_one_le_y
    · rename_i hinf hsup
      nomatch box.absurd_1 hinf hsup
    · rename_i hinf hsup
      rw [hsup]
      exact le_refl (a := ⊤)
    · rename_i y hinf hsup
      nomatch box.absurd_2 hinf ⟨y, hsup⟩
    · rename_i x hinf hsup
      nomatch box.absurd_3 ⟨x, hinf⟩ hsup
    · rename_i x hinf hsup
      rw [hsup]
      exact le_top
    · rename_i x y hinf hsup
      rw [hsup]
      have inf_le_sup := box.inf_le_sup
      rw [hinf, hsup] at inf_le_sup
      have inf_le_sup' : (↑x : EReal) ≤ (↑y : EReal) := inf_le_sup
      have : x ≤ y := by exact_mod_cast inf_le_sup'
      have le : (x + y) / 2 ≤ y := by linarith
      have : (some (some y) : Option (WithTop ℝ)) = (↑y : EReal) := rfl
      simp only [this]
      have h2 : (2 : EReal) = (↑(2 : ℝ) : EReal) := by norm_cast
      rw [h2, ← EReal.coe_add, ← EReal.coe_div]
      exact_mod_cast le

noncomputable def Box.split (box : Box) : Box × Box :=
  let box1 : Box := ⟨box.inf, box.midPoint, box.midPointMem.1⟩
  let box2 : Box := ⟨box.midPoint, box.sup, box.midPointMem.2⟩
  (box1, box2)

-- TODO: show that if we have a sequence of boxes such that the next is one
-- of the split of the current, we end up with a point where the sequence
-- "aggregates" inside any of the neighbourhoods.

-- Prior lemma: "shape" of the neighbourhoods in EReal where we can fit
-- small enough boxes.

/-!
Neighbourhoods and intervals in the extended real numbers set
--------------------------------------------------------------------------------
-/

#check EReal.mem_nhds_bot_iff
-- EReal.mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 ⊥ ↔ ∃ y, Set.Iio ↑y ⊆ s

#check EReal.mem_nhds_top_iff
-- EReal.mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 ⊤ ↔ ∃ y, Set.Ioi ↑y ⊆ s

#check mem_nhds_iff_exists_Ioo_subset'
-- mem_nhds_iff_exists_Ioo_subset'.{u} {α : Type u}
--   [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
--   {a : α} {s : Set α} (hl : ∃ l, l < a) (hu : ∃ u, a < u) :
--   s ∈ 𝓝 a ↔ ∃ l u, a ∈ Set.Ioo l u ∧ Set.Ioo l u ⊆ s

theorem EReal.mem_nhds_real_iff {s : Set EReal} {a : EReal}
    (a_real : ∃ aReal : ℝ, ↑aReal = a) :
    s ∈ 𝓝 a ↔ ∃ l u, a ∈ Set.Ioo l u ∧ Set.Ioo l u ⊆ s := by
  have hl : ∃ l, l < a := by sorry
  have hr : ∃ r, a < r := by sorry
  constructor
  · intro s_in_nhds_a
    apply (mem_nhds_iff_exists_Ioo_subset' hl hr).mp
    grind
  · intro ⟨l, u, a_in_ioo_u_l, ioo_u_l_subset_nhds_a⟩
    apply (mem_nhds_iff_exists_Ioo_subset' hl hr).mpr
    grind

/-!
--------------------------------------------------------------------------------
-/

theorem nested_boxes (boxes : ℕ → Box)
    (h : ∀ n, boxes (n + 1) = (boxes n).split.1 ∨ boxes (n + 1) = (boxes n).split.2) :
    ∃ x : EReal, ∀ s ∈ 𝓝 x, ∃ n0, ∀ n ≥ n0, ↑(boxes n) ⊆ s := by
  sorry

#check nonempty_iInter_of_antitone_nonempty_isClosed
-- HK.nonempty_iInter_of_antitone_nonempty_isClosed.{v}
--   {ι : Type v} [LinearOrder ι] [hι : Nonempty ι] (t : ι → Set EReal)
--   (hta : Antitone t) (htn : ∀ (i : ι), (t i).Nonempty) (htcl : ∀ (i : ι), IsClosed (t i)) :
--   (⋂ i, t i).Nonempty

lemma Box.split_antitone_step (box : Box) :
    (↑box.split.1 : Set EReal) ⊆ (↑box : Set EReal) ∧
    (↑box.split.2 : Set EReal) ⊆ (↑box : Set EReal) := by
  constructor
  · simp only [Box.toInterval, Interval.toSet, Box.split]
    apply Set.Icc_subset_Icc
    · apply le_refl
    · have mem := Box.midPointMem box
      simp only [Membership.mem, Box.toInterval, Interval.mem] at mem
      exact mem.right
  · simp only [Box.toInterval, Interval.toSet, Box.split]
    apply Set.Icc_subset_Icc
    · have mem := Box.midPointMem box
      simp only [Membership.mem, Box.toInterval, Interval.mem] at mem
      exact mem.left
    · apply le_refl

lemma nested_boxes_acc (boxes : ℕ → Box)
    (h : ∀ n, boxes (n + 1) = (boxes n).split.1 ∨ boxes (n + 1) = (boxes n).split.2) :
    (⋂ i, ↑(boxes i) : Set EReal).Nonempty := by
    have antitone : Antitone fun i ↦ (↑(boxes i): Set EReal) := by
      apply antitone_nat_of_succ_le
      intro n
      specialize h n
      cases h with
      | inl h =>
        rw [h]
        exact Box.split_antitone_step (boxes n) |>.1
      | inr h =>
        rw [h]
        exact Box.split_antitone_step (boxes n) |>.2
    apply nonempty_iInter_of_antitone_nonempty_isClosed
    · apply antitone
    · intro i
      rw [Box.toInterval, Interval.toSet]
      exact Set.nonempty_Icc.mpr (boxes i).inf_le_sup
    · intro i
      rw [Box.toInterval, Interval.toSet]
      apply isClosed_Icc

/-!
TODO:
  - Make the assumptions in nested_box theorem
  - Consider the -- nonempty -- intersection of the boxes.
  - If it contains -inf or +inf at each stage, special case (TODO).
  - Otherwise we can pick a x in the intersection.
    after the stage where neither -inf not +inf is in the intersection,
    at each stage the length of the interval is divided by 2.
    Pick a neighbourhood of x, extract a sub interval, push the iteration
    and show that we end up in it.
  - The infinity special case is quite similar.

-/

/-!
TODO: first lemma, assume that at some stage (boxes i) has finite bounds.
Show that the length is / 2 at each stage and that is converges "inside"
any Icc (neighb of...)
-/


-- TODO: theorem noGauge_induction


/-!
Mmm actually our induction needs to mutate the base box? We show that
if the Cousin lemma is contradicted for some box, then it's also
contradicted one one of the "splits" of it?
-/



/-!
We need to pick a gauge on a box, and assume a contradiction, that is that
we cannot find any subdivision of the box which is subordinate to the gauge,
construct by induction a family of nested boxes that ends up being a
fundamental neighbourhood basis of some point, and exhibit the contradiction
there.

This is the stuff we have not captured yet, that our construction will end
up "fitting into" any neighbourhood of the limit point by construction.
-/

/-!
Riemann sums
--------------------------------------------------------------------------------
-/

/-- Nota: do we need a length that returns values in ENNReal instead? -/
noncomputable def Interval.length : Interval → EReal
  | .empty => 0
  | .ioo inf sup _ | .ioc inf sup _ | .ico inf sup _ | icc inf sup _ =>
    sup - inf

/-!
The function that maps infinite lengths to zero already exist:
-/
#print EReal.toReal
-- def EReal.toReal : EReal → ℝ :=
-- fun x ↦
--   match x with
--   | none => 0
--   | some none => 0
--   | some (some x) => x

noncomputable def Interval.lengthReal := EReal.toReal ∘ Interval.length

/-!
TODO: later a version of the sum that accepts integrands with extended real
values, with a pre-cleanup for negligible sets.
-/

/-- The raw Riemann sum function; use `sum` instead, which is a linear map. -/
noncomputable def TaggedBoxes.sum' {ι} [Fintype ι]
(π : TaggedBoxes ι) (f : EReal → ℝ) : ℝ :=
  ∑ i : ι, Interval.lengthReal (π.box i) * f (π.tag i)

theorem TaggedBoxes.sum'_is_linear {ι} [Fintype ι] (π : TaggedBoxes ι) :
    IsLinearMap ℝ π.sum' where
  map_add := by
    intro x y
    simp only [TaggedBoxes.sum']
    simp only [Pi.add_apply]
    simp only [mul_add]
    simp only [Finset.sum_add_distrib]
  map_smul := by
    intro c x
    simp only [TaggedBoxes.sum']
    simp only [Pi.smul_apply]
    simp only [smul_eq_mul]
    conv => enter [1, 2, x_1, 2]; rw [mul_comm]
    conv => enter [1, 2, x_1]; rw [<- mul_assoc]
    conv => enter [2]; rw [mul_comm]
    simp only [Finset.sum_mul]

noncomputable def TaggedBoxes.sum {ι} [Fintype ι] (π : TaggedBoxes ι) :
    (EReal → ℝ) →ₗ[ℝ] ℝ :=
  IsLinearMap.mk' π.sum' (TaggedBoxes.sum'_is_linear π)


end HK
