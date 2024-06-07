

import «Test2».Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

def additive (v : Finset Nat → Int) : Prop :=  ∀ a b : Finset Nat, v (a ∪ b) = v a + v b
def value_empty (v : Finset Nat → Int) : Prop :=  v (∅) = 0
def value_goods (v : Finset Nat → Int) : Prop := ∀ x : Nat, 0 < v {x}

def ef (v: Finset Nat → Int) (a b : Finset Nat): Prop :=
  v a ≥ v b

def ef1 (v : Finset Nat → Int) (a b : Finset Nat): Prop :=
  (v a < v b) → ∃ x ∈ b, v {x} + v a ≥ v b

def ef1_mutual (v : Finset Nat → Int) (a b : Finset Nat): Prop :=
  ef1 v a b ∧ ef1 v b a

@[simp] theorem ef1_mutual_comm (h1 : ef1_mutual v a b) : (ef1_mutual v b a) := by
  rw [ef1_mutual] at h1
  rw [ef1_mutual]
  apply And.intro
  exact h1.right
  exact h1.left

@[simp] theorem ef_implies_ef1_insert_x (h1 : ef v a b) (add: additive v): ef1 v a (insert x b) := by
  rw [ef1]
  rw [ef] at h1
  rw [Finset.insert_eq]
  rw [add]
  intro _
  use x
  apply And.intro
  rw [← Finset.insert_eq]
  exact Finset.mem_insert_self x b
  --
  simp
  exact h1


theorem ef1_impl_ef1_insert_x (add: additive v) (val_goods: value_goods v) (val_empty : value_empty v)(hef1: ef1 v a b) (x : Nat) : ef1 v (insert x a) b:= by
  rw [ef1] at *
  intro h1
  rw [Finset.insert_eq] at h1
  rw [add] at h1
  have h2 : ∃ x ∈ b, v {x} + v a ≥ v b := by
    have h3 : v a < v b := by
      have h4 : v a <  v {x} + v a := by
        apply Int.lt_add_of_pos_left
        exact val_goods x
      apply lt_trans h4 at h1
      exact h1
    revert h3
    exact hef1
  match h2 with
  | ⟨x_1, ⟨ph, pt⟩⟩ =>
    use x_1
    apply And.intro
    exact ph
    rw [Finset.insert_eq]
    rw [add]
    simp
    simp at pt
    rw [Int.add_comm]
    rw [Int.add_assoc]
    have v_x_nonneg : 0 ≤ v {x} := by
      rw [le_iff_eq_or_lt]
      apply Or.intro_right
      exact val_goods x
    refine le_add_of_nonneg_of_le v_x_nonneg ?h.right.hbc
    rw [Int.add_comm]
    exact pt

theorem ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x (hef : ef v a b) (val_goods: value_goods v) (hef1 : ef1 v b a) (x : Nat) (add : additive v) (empt : value_empty v): ef1_mutual v a (insert x b):= by
  rw [ef1_mutual]
  apply And.intro
  revert add
  revert hef
  exact ef_implies_ef1_insert_x
  --
  rw [ef1]
  rw [ef1] at hef1
  intro h1
  -- have h2 : a ≠ ∅ := by
  --   intro h2
  --   rw [value_empty] at empt
  --   rw [h2] at h1
  --   rw [empt] at h1
  --   apply Nat.not_lt_zero (v (insert x b))
  --   exact h1
  rw [Finset.insert_eq]
  rw [add]
  simp

  -- rw [Finset.insert_eq] at h1
  -- rw [add] at h1
  -- rw [Int.add_comm] at h1
  have h2 : v b < v a := by
    rw [Finset.insert_eq] at h1
    rw [add] at h1
    rw [Int.add_comm] at h1
    clear hef hef1 add empt
    have v_x_pos : 0 ≤ v {x} := by
      rw [le_iff_eq_or_lt]
      apply Or.intro_right
      exact val_goods x
    exact lt_of_add_lt_of_nonneg_left h1 v_x_pos

  match hef1 h2 with
  | ⟨x_a, ⟨x_a_mem, x_a_ef1⟩⟩ =>
    use x_a
    apply And.intro
    exact x_a_mem
    simp at x_a_ef1
    rw [Int.add_comm]
    rw [Int.add_assoc]
    have v_x_nonneg : 0 ≤ v {x} := by
      apply le_of_lt_or_eq
      apply Or.intro_left
      exact val_goods x
    refine le_add_of_nonneg_of_le v_x_nonneg ?h.right.hbc
    rw [Int.add_comm]
    exact x_a_ef1









theorem ef_always : (ef v a b ∨ ef v b a):= by
  repeat rw [ef]
  exact Int.le_total (v b) (v a)




theorem ef1_for_n_eq_2 (M : Finset Nat) (val : Finset Nat → Int) (val_goods : value_goods val) (val_add : additive val) (val_emp : value_empty val):
  ∃ a1 a2 : Finset Nat, a1 ∪ a2 = M ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual val a1 a2 := by
  induction M using Finset.induction_on
  case empty =>
    use ∅
    use ∅
    apply And.intro
    simp
    apply And.intro
    simp
    rw [ef1_mutual]
    apply And.intro
    rw [ef1]
    repeat rw [val_emp]
    simp
    rw [ef1]
    repeat rw [val_emp]
    simp
  case insert x s ind inl =>
    match inl with
    | ⟨a1, ⟨a2, ⟨a_union, a_inter, a_mutual_ef1⟩⟩⟩ =>
    have h4 : ef val a1 a2 ∨ ef val a2 a1 := ef_always
    cases h4 with
    | inl h4l =>
      use insert x a2
      use a1
      apply And.intro
      simp
      rw [Finset.union_comm]
      rw [a_union]
      --
      apply And.intro
      rw [Finset.inter_comm]
      rw [Finset.inter_insert_of_not_mem]
      exact a_inter
      --
      rw [← a_union] at ind
      rw [Finset.not_mem_union] at ind
      exact ind.left
      --
      rw [ef1_mutual] at a_mutual_ef1
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x h4l val_goods a_mutual_ef1.right x val_add val_emp)
    | inr h4r =>
      use insert x a1
      use a2
      apply And.intro
      rw [Finset.insert_eq]
      simp
      rw [a_union]
      rw [← Finset.insert_eq]
      --
      apply And.intro
      rw [Finset.inter_comm]
      rw [Finset.inter_insert_of_not_mem]
      rw [Finset.inter_comm]
      exact a_inter
      --
      rw [← a_union] at ind
      rw [Finset.not_mem_union] at ind
      exact ind.right
      --
      rw [ef1_mutual] at a_mutual_ef1
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x h4r val_goods a_mutual_ef1.left x val_add val_emp)
