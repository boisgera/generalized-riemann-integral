import Mathlib
import Paperproof

open BoxIntegral (Box BoxAdditiveMap HasIntegral IntegrationParams)

abbrev n := 1
abbrev ι := Fin n

def lower : ι → ℝ := ![0.0]
def upper : ι → ℝ := ![1.0]

example : upper 0 = 1.0 := by
  simp [upper]


#check Pi.lt_def
-- Pi.lt_def.{u_1, u_4}
--     {ι : Type u_1} {π : ι → Type u_4}
--     [(i : ι) → Preorder (π i)] {x y : (i : ι) → π i} :
--   x < y ↔ x ≤ y ∧ ∃ i, x i < y i

#check Pi.le_def
-- Pi.le_def.{u_1, u_2}
--     {ι : Type u_1} {π : ι → Type u_2}
--     [(i : ι) → LE (π i)] {x y : (i : ι) → π i} :
--   x ≤ y ↔ ∀ (i : ι), x i ≤ y i

-- Nice, but not what we want (we need each box coordinate to
-- satisfy the strict inequality)
theorem lower_lt_upper : lower < upper := by
  apply Pi.lt_def.mpr
  apply And.intro
  · apply Pi.le_def.mpr
    intro i
    rw [Fin.eq_zero i]
    rw [lower, upper]
    norm_num
  · use 0
    rw [lower, upper]
    norm_num

-- This is what we need
theorem lower_lt_upper' : ∀ (i : ι), lower i < upper i := by
  intro i
  rw [Fin.eq_zero i]
  rw [lower, upper]
  norm_num

-- ]0, 1]
def unitBox : Box ι := ⟨lower, upper, lower_lt_upper'⟩

/-!
TODO:

- build ]1, 2], consider the union (as sets),
  "convert back" to ]0, 2] (not sure that's possible...)
  OK, now the question is rather, what kind of set-like
  operations do I have on Boxes.

- show that the integral of the fct equal to 1 over ]0, 1] is 1.
  (For Riemman first, then hk)

-/

def riemann : IntegrationParams := {
  bRiemann := true,
  bHenstock := true,
  bDistortion := false
}

def henstockKurzweil : IntegrationParams := {
  bRiemann := false, -- controlled by a gauge
  bHenstock := true,
  bDistortion := false
}

#check HasIntegral
-- BoxIntegral.HasIntegral.{u, v, w}
--   {ι : Type u} {E : Type v} {F : Type w}
--   [NormedAddCommGroup E] [NormedSpace ℝ E]
--   [NormedAddCommGroup F] [NormedSpace ℝ F]
--   [Fintype ι]
--   (I : Box ι) (l : IntegrationParams) (f : (ι → ℝ) → E)
--   (vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤) (y : F)
--   : Prop

def I := unitBox
def l := riemann
def f : (ι → ℝ) → ℝ := fun _ => 1.0

#print BoxAdditiveMap
-- structure BoxIntegral.BoxAdditiveMap.{u_3, u_4} (ι : Type u_3) (M : Type u_4)
-- [AddCommMonoid M]
--   (I : WithTop (Box ι)) :
--   Type (max u_3 u_4)
-- number of parameters: 4
-- fields:
--   BoxIntegral.BoxAdditiveMap.toFun : Box ι → M
--   BoxIntegral.BoxAdditiveMap.sum_partition_boxes' : ∀ (J : Box ι),
--       ↑J ≤ I
--       → ∀ (π : BoxIntegral.Prepartition J), π.IsPartition
--       → ∑ Ji ∈ π.boxes, self.toFun Ji = self.toFun J
-- ...

/-!
Building a `vol` as a `BoxAdditiveMap` is the by far the hardest piece of work
since this map has values in `ℝ →L[ℝ] → ℝ` (a space of continuous linear maps).

Let's start with this and we'll prove that our function is additive afterwards.
-/

theorem continuousLinearMap_types :
    (ℝ →L[ℝ] ℝ) = ContinuousLinearMap (σ := RingHom.id ℝ) ℝ ℝ := by
  rfl

-- Let's define our "volume as a scalar" from within the cont. lin. map
-- framework and get its properties for free.
def vol (b : Box ι) : ℝ →L[ℝ] ℝ  :=
  (b.upper 0 - b.lower 0) • ContinuousLinearMap.id ℝ ℝ

-- We can still recover the "raw function" and the constant afterwards
-- using the "evaluate on 1" trick.

theorem vol_eq_upper_sub_lower (box : Box ι) :
    vol box 1 = box.upper 0 - box.lower 0 := by
  -- let x := box.upper 0 - box.lower 0
  -- rw [show box.upper 0 - box.lower 0 = x from by rfl]
  rw [vol]
  set x := box.upper 0 - box.lower 0
  simp only [smul_apply]
  simp only [ContinuousLinearMap.id_apply]
  simp only [smul_eq_mul]
  simp only [mul_one]


-- Here I hope that there are some tools to help us ...
-- Maybe some stuff to reorder the components of a partition(?)
-- AAAAAAAH! I guess that it's not **that** hard by induction on the
-- number of boxes in the partition? But still we're gonna need
-- some subpartitions I guess. Mmmmm
theorem vol_additive (I : WithTop (Box ι)) (J : Box ι) :
    ↑J ≤ I
    → ∀ (π : BoxIntegral.Prepartition J), π.IsPartition
    → ∑ Ji ∈ π.boxes, vol Ji = vol J := by
  admit


-- theorem working_title : HasIntegral := by
-- admit
