-- This module serves as the root of the `Test2` library.
-- Import modules here that should be built as part of the library.
import «Test2».Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith.Parsing

def envies (a b : List Nat): Prop :=
  List.sum a < List.sum b

def envyuptoone (a b : List Nat): Prop :=
  (List.sum a < List.sum b) → ∃ x ∈ b,  x > List.sum b - List.sum a


-- theorem
-- assuming two lists of natural numbers a and b
-- and that a does not envy b
-- for any new number x
-- show that adding x to b does not break envy-freeness

theorem t1 (a b : List Nat) (x : Nat) (h : envies b a) : envyuptoone a (x::b) := by
  -- expand definitions
  rw [envyuptoone]
  rw [envies] at h
  intro h1 -- envyuptoone is an implication, so we assume (List.sum a < List.sum b)
  use x -- use x as an example to prove the quantifier
  apply And.intro -- we must now prove both that x is a member of x::b and ef1
  apply List.mem_cons_self x b -- this proves x ∈ x::b
  rw [List.sum_cons]
  simp
  rw [Nat.sub_lt_iff_lt_add]
  rw [add_comm]
  simp
  exact h
  rw [← List.sum_cons]
  rw [Nat.le_iff_lt_or_eq]
  apply Or.intro_left
  exact h1


def additive (v : Finset Nat → Nat) : Prop :=  ∀ a b : Finset Nat, v (a ∪ b) = v a + v b
def value_empty (v : Finset Nat → Nat) : Prop :=  v (∅) = 0
def value_goods (v : Finset Nat → Nat) : Prop := ∀ x : Nat, v {x} > 0

def ef (v: Finset Nat → Nat) (a b : Finset Nat): Prop :=
  v a ≥ v b

def ef1 (v : Finset Nat → Nat) (a b : Finset Nat): Prop :=
  (v a < v b) → ∃ x ∈ b, v a + v {x} ≥ v b

def ef1_mutual (v : Finset Nat → Nat) (a b : Finset Nat): Prop :=
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
  rw [Nat.add_comm]
  apply Nat.add_le_add_right
  exact h1

theorem ef1_impl_ef1_insert_x (add: additive v) (hef1: ef1 v a b) (x : Nat) : ef1 v (insert x a) b:= by
  rw [ef1] at *
  intro h1
  rw [Finset.insert_eq] at h1
  rw [add] at h1
  have h2 : ∃ x ∈ b, v a + v {x} ≥ v b := by
    apply Nat.lt_add_left (v {x}) at h1
    rw [Nat.add_lt_add_iff_left] at h1
    revert h1
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
    rw [add_assoc]
    rw [add_comm]
    apply le_add_right
    exact pt

theorem ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x (hef : ef v a b) (hef1 : ef1 v b a) (x : Nat) (add : additive v) (empt : value_empty v): ef1_mutual v a (insert x b):= by
  rw [ef1_mutual]
  apply And.intro
  revert add
  revert hef
  exact ef_implies_ef1_insert_x
  --
  rw [ef1]
  rw [ef1] at hef1
  intro h1
  rw [Finset.insert_eq]
  rw [add]
  simp
  rw [Finset.insert_eq] at h1
  rw [add] at h1
  rw [add_comm] at h1
  apply Nat.lt_sub_of_add_lt at h1
  apply Nat.lt_add_left (v {x}) at h1
  rw [add_comm] at h1
  rw [Nat.sub_add_cancel] at h1 -- uh oh
  match hef1 h1 with
  | ⟨x_a, ⟨x_a_mem, x_a_ef1⟩⟩ =>
    use x_a
    apply And.intro
    exact x_a_mem
    simp at x_a_ef1
    rw [Nat.add_assoc]
    apply le_add_left
    exact x_a_ef1











theorem ef_always : (ef v a b ∨ ef v b a):= by
  repeat rw [ef]
  exact Nat.le_or_ge (v b) (v a)




theorem ef1_for_n_eq_2 (M : Finset Nat) (val : Finset Nat → Nat) (val_add : additive val) (val_emp : value_empty val):
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
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x h4l a_mutual_ef1.right x val_add val_emp)
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
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x h4r a_mutual_ef1.left x val_add val_emp)
