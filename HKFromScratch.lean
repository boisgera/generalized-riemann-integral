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
  | .ioo inf _ _
  | .ioc inf _ _
  | .ico inf _ _
  | .icc inf _ _ => inf

noncomputable def Interval.sup : Interval → EReal
  | .empty => ⊥
  | .ioo _ sup _
  | .ioc _ sup _
  | .ico _ sup _
  | .icc _ sup _ => sup

#check sInf
-- InfSet.sInf.{u_1} {α : Type u_1} [self : InfSet α] : Set α → α

#print InfSet -- computation/data only, not related to order
-- class InfSet.{u_1} (α : Type u_1) : Type u_1
-- number of parameters: 1
-- fields:
--   InfSet.sInf : Set α → α
-- constructor:
--   InfSet.mk.{u_1} {α : Type u_1} (sInf : Set α → α) : InfSet α

#synth InfSet EReal
-- instInfSetEReal

#print CompleteLattice
-- HUGE stuff. includes stuff such as
--  CompleteSemilatticeInf.isGLB_sInf : ∀ (s : Set α), IsGLB s (sInf s)

#synth CompleteLattice EReal
-- CompleteLinearOrder.toCompletelyDistribLattice.toCompleteLattice

#print IsGLB
-- def IsGLB.{u_1} : {α : Type u_1} → [LE α] → Set α → α → Prop :=
-- fun {α} [LE α] s ↦ IsGreatest (lowerBounds s)

#print IsGreatest
-- def IsGreatest.{u_1} : {α : Type u_1} → [LE α] → Set α → α → Prop :=
-- fun {α} [LE α] s a ↦ a ∈ s ∧ a ∈ upperBounds s

#print upperBounds
-- def upperBounds.{u_1} : {α : Type u_1} → [LE α] → Set α → Set α :=
-- fun {α} [LE α] s ↦ {x | ∀ ⦃a : α⦄, a ∈ s → a ≤ x}

#check isGLB_iff_sInf_eq
-- isGLB_iff_sInf_eq.{u_1} {α : Type u_1} [CompleteSemilatticeInf α] {s : Set α} {a : α} :
-- IsGLB s a ↔ sInf s = a

theorem Interval.inf_eq_sInf_coe (I : Interval) : I.inf = sInf ↑I := by
  -- First step : reduce the goal of being the inf to being the GLB
  apply Eq.symm
  simp only [<- isGLB_iff_sInf_eq (α := EReal)]
  -- ⊢ IsGLB I.toSet I.inf
  simp only [IsGLB, IsGreatest, lowerBounds]
  -- ⊢ I.inf ∈ {x | ∀ ⦃a : EReal⦄, a ∈ I.toSet → x ≤ a} ∧
  -- I.inf ∈ upperBounds {x | ∀ ⦃a : EReal⦄, a ∈ I.toSet → x ≤ a}
  constructor
  · sorry
  · sorry


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
Length
--------------------------------------------------------------------------------
-/

/-!
Notes:
- We need to special-case ∅.length since ∅.sup - ∅.inf = ⊥ - ⊤ = ⊥.
- [⊥, ⊥].length and [⊤, ⊤].length are junk values
  (that keep the definition as simple as possible)
-/

noncomputable def Interval.length : Interval → EReal
  | .empty => 0
  | .ioo inf sup _
  | .ioc inf sup _
  | .ico inf sup _
  | .icc inf sup _ => sup - inf

theorem EReal.sub_eq_top_iff (x y : EReal) :
    (x - y = ⊤) ↔ (x = ⊤ ∧ y ≠ ⊤) ∨ (x ≠ ⊥ ∧ y = ⊥) := by
  constructor
  · intro sub_eq_top
    cases x <;> cases y <;>
      simp only [EReal.bot_sub, EReal.sub_top, EReal.top_sub_bot, EReal.top_sub_coe,
        EReal.coe_sub_bot, ← EReal.coe_sub, EReal.coe_ne_top, bot_ne_top] at sub_eq_top <;>
      simp only [EReal.coe_ne_top, EReal.coe_ne_bot, bot_ne_top, ne_eq, and_true, or_true,
        true_or, not_false_eq_true]
  · intro h
    rcases h with ⟨x_eq_top, y_ne_top⟩ | ⟨x_ne_bot, y_eq_bot⟩
    · rw [x_eq_top]
      exact EReal.top_sub y_ne_top
    · rw [y_eq_bot]
      exact EReal.sub_bot x_ne_bot

theorem EReal.sub_ne_top_iff (x y : EReal) :
    (x - y ≠ ⊤) ↔ (x ≠ ⊤ ∨ y = ⊤) ∧ (x = ⊥ ∨ y ≠ ⊥) := by
  have := (EReal.sub_eq_top_iff x y).not
  push Not at this
  simp only [show (x = ⊤ → y = ⊤) = (x ≠ ⊤ ∨ y = ⊤) from by grind] at this
  simp only [show (x ≠ ⊥ → y ≠ ⊥) = (x = ⊥ ∨ y ≠ ⊥) from by grind] at this
  exact this

#check EReal.sub_nonneg
-- EReal.sub_nonneg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
-- 0 ≤ x - y ↔ y ≤ x

theorem Interval.length_nonneg (i : Interval)
    (hnbb : ¬(i.inf = ⊥ ∧ i.sup = ⊥))
    (hntt : ¬(i.inf = ⊤ ∧ i.sup = ⊤))
    : (i.length ≥ 0) := by
  cases i
  all_goals
    simp only [Interval.inf, Interval.sup, Interval.length] at *
    first
    | rfl
    | apply (EReal.sub_nonneg (by grind) (by grind)).mpr
      first
      | assumption
      | apply le_of_lt ; assumption

theorem Interval.length_finite (i : Interval)
    (inf_ne_bot : i.inf ≠ ⊥) (sup_ne_top : i.sup ≠ ⊤)
    : i.length ≠ ⊤ := by
  cases h : i with
  | empty =>
    rw [Interval.length]
    apply EReal.zero_ne_top
  | ioo inf sup inf_lt_sup
  | ioc inf sup inf_lt_sup
  | ico inf sup inf_lt_sup
  | icc inf sup inf_le_sup =>
    rw [Interval.length]
    apply (EReal.sub_ne_top_iff sup inf).mpr
    simp only [h, Interval.inf, Interval.sup] at *
    grind

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

noncomputable def Box.length (box : Box) : EReal := Interval.length box

noncomputable def Box.lengthReal (box : Box) : EReal := Interval.lengthReal box


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

/-!
Three absurd lemmas, all consequences of ¬ (box.inf > box.sup)
-/

theorem Box.ne_inf_eq_top_and_sup_eq_bot (box : Box)
    (hinf : box.inf = ⊤) (hsup : box.sup = ⊥) : False := by
  have inf_le_sup := box.inf_le_sup
  have top_le_bot : (⊤ : EReal) ≤ (⊥ : EReal) := by
    simp only [hinf, hsup] at inf_le_sup
    exact inf_le_sup
  have bot_lt_top : (⊥ : EReal) < (⊤ : EReal) := bot_lt_top
  exact (by grind)

theorem Box.ne_inf_eq_top_and_sup_real (box : Box)
    (hinf : box.inf = ⊤) {y : ℝ} (hsup : box.sup = ↑y) : False := by
  have inf_le_sup := box.inf_le_sup
  have top_le_y : (⊤ : EReal) ≤ (↑y : EReal) := by
    rw [hinf, hsup] at inf_le_sup
    exact inf_le_sup
  have y_le_top := le_top (a := (↑y : EReal))
  have top_eq_y := LE.le.antisymm top_le_y y_le_top
  nomatch top_eq_y

theorem Box.ne_inf_real_and_sup_eq_bot (box : Box)
    {x : ℝ} (hinf : box.inf = ↑x) (hsup : box.sup = ⊥) : False := by
  have inf_le_sup := box.inf_le_sup
  have x_le_bot : (↑x : EReal) ≤ ⊥ := by
    rw [hinf, hsup] at inf_le_sup
    exact inf_le_sup
  have x_eq_bot := LE.le.antisymm x_le_bot (bot_le (a := (↑x : EReal)))
  nomatch x_eq_bot

macro "box_absurd" : tactic =>
  `(tactic|
      apply False.elim <;>
      first
      | (apply Box.ne_inf_eq_top_and_sup_eq_bot <;> assumption)
      | (apply Box.ne_inf_eq_top_and_sup_real <;>
           first | assumption | exact ⟨_, by assumption⟩)
      | (apply Box.ne_inf_real_and_sup_eq_bot <;>
           first | assumption | exact ⟨_, by assumption⟩))

noncomputable def Box.midPoint (box : Box) : EReal :=
  match box.inf, box.sup with
  | ⊥, ⊥ => ⊥
  | ⊥, ⊤ => 0
  | ⊥, (y : ℝ) => y - 1
  | ⊤, ⊥ => ⊥ -- junk, can't happen
  | ⊤, ⊤ => ⊤
  | ⊤, (_ : ℝ) => ⊥ -- junk, can't happen
  | (_ : ℝ), ⊥ => ⊥ -- junk, can't happen
  | (x : ℝ), ⊤ => x + 1
  | (x : ℝ), (y : ℝ) => (x + y) / 2

lemma Box.midPoint_ne_bot (box : Box) : (box.sup ≠ ⊥) → (box.midPoint ≠ ⊥) := by
  simp only [Box.midPoint]
  intro box_sup_ne_bot
  split
  · contradiction
  · exact EReal.bot_ne_zero.symm
  · norm_cast ; intro h ; cases h
  · box_absurd
  · exact top_ne_bot
  · box_absurd
  · contradiction
  · norm_cast ; intro h ; cases h
  next x y _ _ =>
    norm_cast
    intro h
    have : (2 : EReal) = (↑(2 : Real) : EReal) := by norm_cast
    rw [this] at h
    rw [<- EReal.coe_div] at h
    cases h

lemma Box.midPoint_ne_top (box : Box) : (box.inf ≠ ⊤) → (box.midPoint ≠ ⊤) := by
  simp only [Box.midPoint]
  intro box_inf_ne_top
  split
  · exact bot_ne_top
  · exact EReal.zero_ne_top
  · norm_cast ; intro h ; cases h
  · exact bot_ne_top
  · contradiction
  · exact bot_ne_top
  · exact bot_ne_top
  · norm_cast ; intro h ; cases h
  next x y _ _ =>
    norm_cast
    intro h
    have : (2 : EReal) = (↑(2 : Real) : EReal) := by norm_cast
    rw [this] at h
    rw [<- EReal.coe_div] at h
    cases h

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
    · box_absurd
    · rename_i hinf hsup
      rw [hinf]
      exact le_refl (a := ⊤)
    · box_absurd
    · box_absurd
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
    · box_absurd
    · rename_i hinf hsup
      rw [hsup]
      exact le_refl (a := ⊤)
    · box_absurd
    · box_absurd
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

theorem finite_split (box : Box) (hinf : box.inf ≠ ⊥) (htop : box.sup ≠ ⊤) :
    box.split.1.inf ≠ ⊥ ∧
    box.split.1.sup ≠ ⊤ ∧
    box.split.2.inf ≠ ⊥ ∧
    box.split.2.sup ≠ ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Box.split]
    exact hinf
  · simp only [Box.split]
    have midPointMem := box.midPointMem
    simp only [Membership.mem, Box.toInterval, Interval.mem] at midPointMem
    have : box.midPoint < ⊤ :=
      have midPoint_le_sup : box.midPoint ≤ box.sup := midPointMem.2
      have sup_lt_top: box.sup < ⊤ :=
        lt_of_le_of_ne (OrderTop.le_top box.sup) htop
      lt_of_le_of_lt midPoint_le_sup sup_lt_top
    exact ne_of_lt this
  · simp only [Box.split]
    have midPointMem := box.midPointMem
    simp only [Membership.mem, Box.toInterval, Interval.mem] at midPointMem
    have : ⊥ < box.midPoint :=
      have inf_le_midPoint : box.inf ≤ box.midPoint := midPointMem.1
      have bot_lt_inf : ⊥ < box.inf :=
        lt_of_le_of_ne (OrderBot.bot_le box.inf) (Ne.symm hinf)
      lt_of_lt_of_le bot_lt_inf inf_le_midPoint
    exact ne_of_gt this
  · simp only [Box.split]
    exact htop

theorem half_length_of_split
    (box : Box) (hinf : box.inf ≠ ⊥) (htop : box.sup ≠ ⊤) :
    box.split.1.length = box.length / 2 ∧
    box.split.2.length = box.length / 2 := by
  apply And.intro
  · simp only [Box.length, Interval.length]
    simp only [Box.split, Box.toInterval]
    sorry
  · sorry


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

lemma nested_boxes_finite_aux (boxes : ℕ → Box)
    (hanti : ∀ n,
      boxes (n + 1) = (boxes n).split.1 ∨
      boxes (n + 1) = (boxes n).split.2)
    (j : ℕ) (hfin : (boxes j).inf ≠ ⊥ ∧ (boxes j).sup ≠ ⊤) :
    ∀ i ≥ j,
      (
          (boxes j).inf ≠ ⊥
        ∧ (boxes j).sup ≠ ⊤
        ∧ (boxes (i + 1)).length ≤ (boxes i).length / 2
      ) := by
  intro i i_ge_j
  induction i, i_ge_j using Nat.le_induction with
  | base =>
    constructor
    · exact hfin.1
    · constructor
      · exact hfin.2
      · specialize hanti j
        sorry
  | succ k k_le_j ih =>
    sorry


-- The quantitative/explicit version
lemma nested_boxes_finite (boxes : ℕ → Box)
    (hanti : ∀ n,
      boxes (n + 1) = (boxes n).split.1 ∨
      boxes (n + 1) = (boxes n).split.2)
    (j : ℕ) (hfin : (boxes j).inf ≠ ⊥ ∧ (boxes j).sup ≠ ⊤) :
    ∀ i ≥ j,
      (boxes (i + 1)).length ≤ (boxes i).length / 2
  := by
    intro i i_ge_j
    have ⟨h1, h2, h3⟩ := nested_boxes_finite_aux boxes hanti j hfin i i_ge_j
    exact h3

#check pow_unbounded_of_one_lt
-- pow_unbounded_of_one_lt.{u_3} {R : Type u_3} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]
--  {y : R} [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : ∃ n, x < y ^ n

lemma omg_i_feel_so_much_pain (x : ℕ → ℝ) (j : ℕ)
    (hpos : ∀ i ≥ j, x i > 0)
    (hbound : ∀ i ≥ j, x (i + 1) ≤ (x i) / 2) :
    ∃ c > 0, ∀ i, x i ≤ c / 2 ^ i := by
  have : ∃ c > 0, ∀ i ≥ j, x i ≤ c / 2 ^ i := by
    use (x j) * 2 ^ j
    constructor
    · have := hpos j (show j ≤ j from le_rfl)
      positivity
    · intro i i_ge_j
      induction i, i_ge_j using Nat.le_induction with
      | base =>
        specialize hbound j le_rfl
        field_simp
        apply le_rfl
      | succ n hn ih =>
        field_simp at *
        specialize hbound n hn
        have hbound' : x (n + 1) * 2 * 2 ^ n ≤ (x n) * 2 ^ n := mul_le_mul_of_nonneg_right
          (hbc := hbound)
          (ha := show (0 ≤ 2 ^ n) from by positivity)
        clear hbound
        have := le_trans hbound' ih
        conv at this =>
          left ; rw [mul_assoc]
        conv at this =>
          left ; right; rw [<- pow_succ']
        exact this
  obtain ⟨c, c_pos, hc⟩ := this
  -- Purely finite fact: any function is bounded (in this "c / 2 ^ i" sense)
  -- on any finite initial segment {0, ..., n - 1}, regardless of hypotheses.
  have hfin : ∀ (y : ℕ → ℝ) (n : ℕ), ∃ d > 0, ∀ i < n, y i ≤ d / 2 ^ i := by
    intro y n
    induction n with
    | zero => exact ⟨1, by norm_num, by intro i hi; omega⟩
    | succ n ih =>
      obtain ⟨d, d_pos, hd⟩ := ih
      refine ⟨max d (y n * 2 ^ n + 1), lt_max_of_lt_left d_pos, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact le_trans (hd i h) (by gcongr; exact le_max_left _ _)
      · subst h
        rw [le_div_iff₀ (by positivity)]
        exact le_trans (by linarith) (le_max_right d (y i * 2 ^ i + 1))
  obtain ⟨d, d_pos, hd⟩ := hfin x j
  refine ⟨max c d, lt_max_of_lt_left c_pos, ?_⟩
  intro i
  rcases lt_or_ge i j with hij | hij
  · exact le_trans (hd i hij) (by gcongr; exact le_max_right c d)
  · exact le_trans (hc i hij) (by gcongr; exact le_max_left c d)

lemma quant_to_quali
    (x : ℕ → ℝ) (ε : ℝ) (ε_pos : ε > 0)
    (hb : ∃ j, ∀ i ≥ j, x (i + 1) ≤ (x i) / 2)
    : ∃ k, ∀ i ≥ k, x i < ε := by
  -- TODO:
  -- - split on the property that ∀ j ≥ i, x j > 0 or not.
  -- - the "easy case" if when the property is false. Then show by induction
  --   that x k ≤ 0 after the first value that satisfies this property and
  --   conclude in this case.
  -- - In the "meaty" case, reduce the result to pow_unbounded_of_one_lt
  have ⟨j, hbj⟩ := hb
  by_cases hpos : ∀ i ≥ j, x i > 0
  · have hb' : ∃ c > 0, ∀ i, x i ≤ c / 2 ^ i := by
      apply omg_i_feel_so_much_pain x j hpos hbj
    clear hb
    have ⟨c, c_pos, hb'c⟩ := hb' ; clear hb'
    have hi : ∃ i, c / 2 ^ i < ε := by -- use pow_unbounded_of_one_lt (2^n unbounded)
      have ⟨i, hi'⟩ := pow_unbounded_of_one_lt (c / ε) (y := 2) (show 1 < 2 from by norm_num)
      use i
      rw [div_lt_iff₀ ε_pos] at hi'
      rw [div_lt_iff₀ (by positivity)]
      rw [mul_comm] at hi'
      exact hi'
    have ⟨j', hj'⟩ : ∃ j, ∀ i ≥ j, c / 2 ^ i < ε := by
      -- use hi and that x / 2 ≤ x ; induction
      let ⟨j, hij⟩ := hi
      rename_i i
      use j
      intro i i_ge_j
      induction i, i_ge_j using Nat.le_induction with
      | base => exact hij
      | succ n hn ih =>
        simp only [pow_add]
        simp only [div_mul_eq_div_div]
        norm_num
        have hp : c / 2 ^ n ≥ 0 := by positivity
        have := div_le_self (ha := hp) (hb := show 2 ≥ 1 from by norm_num)
        apply lt_of_le_of_lt this ih
    clear hi
    let k := max j j'
    have k_ge_j : k ≥ j := by grind
    have k_ge_j' : k ≥ j' := by grind
    use k
    intro i i_ge_k
    specialize hb'c i
    specialize hj' i (show i ≥ j' from by linarith)
    apply lt_of_le_of_lt (b := c / 2 ^ i)
    repeat assumption
  · push Not at hpos
    have ⟨k, k_ge_j, x_k_nonpos⟩ := hpos
    clear hpos
    use k
    have : ∀ i ≥ k, x i ≤ 0 := by
      intro i' i'_ge_j
      induction i', i'_ge_j using Nat.le_induction with
      | base => exact x_k_nonpos
      | succ n ih hn =>
        specialize hbj n (show n ≥ j from by linarith)
        have : x n / 2 ≤ 0 := by grind
        exact le_trans hbj this
    intro i i_ge_k
    specialize this i i_ge_k
    linarith

theorem EReal.half_ne_top (x : EReal) (x_lt_top : x ≠ ⊤) : x / 2 ≠ ⊤ := by
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

theorem EReal.half_bot_eq_bot : (⊥ : EReal) / 2 = ⊥ := by
  simp only [HDiv.hDiv, Div.div, DivInvMonoid.div', HMul.hMul, Mul.mul, EReal.mul]
  split
  any_goals contradiction -- only 1/9 goal left!
  rename_i x1 x y _ eq
  have l1: (some (some y) : EReal) = (↑y : EReal) := by rfl
  have l2: EReal.inv 2 = ↑(2: Real)⁻¹ := by
    rw [EReal.coe_inv]
    simp only [Inv.inv]
    rfl
  have : (↑(2 : ℝ)⁻¹ : EReal) = ↑y := by
    simp only [l1, l2] at eq
    exact eq
  have : 2⁻¹ = y := by
    apply EReal.coe_injective this
  have y_pos : 0 < y := by positivity
  simp only [y_pos]
  simp only [if_true]

lemma quant_to_quali_extended
    (x : ℕ → EReal) (ε : EReal) (ε_pos : ε > 0)
    (hb : ∃ j, (∀ i ≥ j, x (i + 1) ≤ (x i) / 2) ∧ (x j ≠ ⊤))
    : ∃ k, ∀ i ≥ k, x i < ε := by
    have ⟨j, hbj, x_j_finite⟩ := hb
    clear hb
    have all_x_ne_top : ∀ i ≥ j, x i ≠ ⊤ := by
      intro i i_ge_j
      induction i, i_ge_j using Nat.le_induction with
      | base => exact x_j_finite
      | succ n ih hn =>
        specialize hbj n ih
        have half_ne_top : (x n) / 2 ≠ ⊤ := EReal.half_ne_top (x n) hn
        have half_lt_top : (x n) / 2 < ⊤ :=
          lt_of_le_of_ne (OrderTop.le_top ((x n) / 2)) half_ne_top
        have : x (n + 1) < ⊤ := by
          exact lt_of_le_of_lt hbj half_lt_top
        exact ne_of_lt this
    -- First we deal with the case where some x i is equal to ⊥
    have exists_eq_bot_ok : (∃ i ≥ j, x i = ⊥) → (∃ k, ∀ i ≥ k, x i < ε) := by
      intro exists_eq_bot
      have ⟨i, i_ge_j, x_i_eq_bot⟩ := exists_eq_bot; clear exists_eq_bot
      have : ∀ k ≥ i, x k = ⊥ := by
        intro k k_ge_i
        induction k, k_ge_i using Nat.le_induction with
        | base => exact x_i_eq_bot
        | succ n ih hn =>
          specialize hbj n (le_trans i_ge_j ih)
          rw [hn] at hbj
          rw [EReal.half_bot_eq_bot] at hbj
          have := OrderBot.bot_le (x (n + 1))
          apply le_antisymm
          repeat assumption
      use i
      intro k k_ge_i
      specialize this k k_ge_i
      rw [this]
      exact lt_trans EReal.bot_lt_zero ε_pos
    cases em (∀ i ≥ j, ⊥ ≠ x i) with
    | inr not_eventually_ne_bot => -- The case we have already singled out
      push Not at not_eventually_ne_bot
      apply exists_eq_bot_ok
      grind
    | inl all_bot_ne_x => -- the "normal case"
      -- At this point, we know that:
      -- all_x_ne_top : ∀ i ≥ j, x i ≠ ⊤
      -- all_bot_ne_x : ∀ i ≥ j, ⊥ < x i
      have ⟨y, hy⟩ : ∃ (y : ℕ → ℝ), ∀ i ≥ j, x i = ↑(y i) := by
        use (fun i => (x i).toReal)
        intro i i_ge_j
        simp only [EReal.toReal]
        split
        · rename_i _ heq
          specialize all_bot_ne_x i i_ge_j
          exact (all_bot_ne_x.symm heq).elim
        · rename_i _ heq
          specialize all_x_ne_top i i_ge_j
          exact (all_x_ne_top heq).elim
        · rename_i yi heq
          exact heq
      have almost_there : ∃ k, ∀ i ≥ k, y i < ε := by
        match ε with
        | ⊥ => contradiction
        | ⊤ =>
          use 0
          intro i _
          apply lt_of_le_of_ne
          · apply OrderTop.le_top
          · intro eq
            nomatch eq
        | (ε' : ℝ) =>
          have ε'_pos : ε' > 0 := by
            apply EReal.coe_lt_coe_iff.mp
            exact ε_pos
          simp only [EReal.coe_lt_coe_iff]
          apply quant_to_quali y ε' ε'_pos
          use j
          intro i i_ge_j
          specialize hbj i i_ge_j
          simp only [hy i i_ge_j] at hbj
          simp only [hy (i + 1) (show i + 1 ≥ j from by linarith)] at hbj
          apply EReal.coe_le_coe_iff.mp
          simp only [EReal.coe_div]
          exact hbj
      have ⟨k, hk⟩ := almost_there
      let k' := max k j
      use k'
      intro i i_ge_k'
      specialize hk i (show i ≥ k from by grind)
      specialize hy i (show i ≥ j from by grind)
      rw [hy]
      exact hk


-- The quantitative version. TODO. We still have a mismatch here in that
-- we have not proved that all the length are finite.
-- lemma nested_boxes_finite_quanti (boxes : ℕ → Box)
--     (hanti : ∀ n,
--       boxes (n + 1) = (boxes n).split.1 ∨
--       boxes (n + 1) = (boxes n).split.2)
--     (j : ℕ)
--     (hfin : (boxes j).inf ≠ ⊥ ∧ (boxes j).sup ≠ ⊤) :
--     (∀ i ≥ j, (boxes (i + 1)).length ≤ ((boxes i).length / 2)) :=
--     by sorry


#check quant_to_quali_extended
-- HK.quant_to_quali_extended (x : ℕ → EReal) (ε : EReal) (ε_pos : ε > 0)
--   (hb : ∃ j, (∀ i ≥ j, x (i + 1) ≤ x i / 2) ∧ x j ≠ ⊤) : ∃ k, ∀ i ≥ k, x i < ε
-- TODO: use quant_to_quali_extended


lemma nested_boxes_finite_quali (boxes : ℕ → Box)
    (hanti : ∀ n,
      boxes (n + 1) = (boxes n).split.1 ∨
      boxes (n + 1) = (boxes n).split.2)
    (j : ℕ)
    (hfin : (boxes j).inf ≠ ⊥ ∧ (boxes j).sup ≠ ⊤) :
    Filter.Tendsto (Box.length ∘ boxes) Filter.atTop (𝓝 0) := by
  -- Let's transform the goal into a classic ε-δ goal.
  rw [tendsto_order]
  simp only [Filter.eventually_atTop, Function.comp_apply]
  constructor
  · intro a' a'_neg
    use 0
    intro i zero_ne_i
    have : 0 ≤ (boxes i).length := by
      apply Interval.length_nonneg
    grind
  · intro ε ε_pos
    -- Grrr this lemma won't do, I it them to work for any i ≥ j.
    have length_div : ∀ i ≥ j, (boxes (i + 1)).length ≤ (boxes i).length / 2
      := by
      intro i i_ge_j
      exact nested_boxes_finite boxes hanti j hfin i i_ge_j
    have length_finite : (boxes j).length ≠ ⊤ := by
      simp only [Box.length, Interval.length, Box.toInterval]
      split
      · rename_i inf_eq_sup
        exact EReal.zero_ne_top
      · have ⟨inf_ne_bot, sup_ne_top⟩ := hfin
        intro h
        have h' := (HK.EReal.sub_eq_top_iff (boxes j).sup (boxes j).inf).mp h
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact sup_ne_top h1
        · exact inf_ne_bot h1
    apply quant_to_quali_extended (ε_pos := ε_pos)
    use j

#check HK.EReal.sub_eq_top_iff

lemma nested_boxes_acc_bot (boxes : ℕ → Box)
    (hanti : ∀ n,
      boxes (n + 1) = (boxes n).split.1 ∨
      boxes (n + 1) = (boxes n).split.2)
    (hbot : ∃ j, ⊥ ∈ ⋂ i ∈ { i | i ≥ j }, (↑(boxes i) : Set EReal)) :
    ∀ u : EReal, u > ⊥ → ∃ k, ∀ i ≥ k, ↑(boxes i) ⊆ Set.Iio u := by
  have ⟨j, hbotj⟩ := hbot

  have bot_in_box: ∀ i ≥ j, ⊥ ∈ boxes i := by
    intro i i_ge_j
    simp only [Set.mem_iInter] at hbotj
    specialize hbotj i i_ge_j
    exact hbotj

  have : ∀ i ≥ j, (boxes i).inf = ⊥ := by
    intro i i_ge_j
    have bot_in_box_i_j := bot_in_box i i_ge_j
    rw [show (boxes i).inf = (Interval.inf (boxes i)) from by rfl]
    have : ⊥ ∈ (boxes i).toInterval.toSet := by
      exact bot_in_box_i_j
    rw [Interval.inf_eq_sInf_coe]
    exact le_bot_iff.mp (sInf_le this)

  -- TODO: this is false, we can also have boxes i = [⊥, ⊥]
  have : ∀ i ≥ j, boxes (i + 1) = (boxes i).split.1 := by
    intro i i_ge_j
    cases hanti i with
    | inl h => exact h
    | inr h =>
      simp only [Box.split] at h
      sorry

  have : ∀ i ≥ j + 1, ∃ a : ℝ, (boxes (i + 1) |>.sup) = ↑a := by sorry

  -- TODO: compute the number of iteration required
  sorry

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
