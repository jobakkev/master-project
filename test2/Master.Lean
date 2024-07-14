import «Master».Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith.Frontend

def additive (v : Finset Nat → Int) : Prop :=
  ∀ a b : Finset Nat, v (a ∪ b) = v a + v b

def value_empty (v : Finset Nat → Int) : Prop :=
  v (∅) = 0

def value_goods (v : Finset Nat → Int) : Prop :=
  ∀ x : Nat, 0 < v {x}

def ef (v: Finset Nat → Int) (a b : Finset Nat): Prop :=
  v a ≥ v b

def ef1 (v : Finset Nat → Int) (a b : Finset Nat): Prop :=
  (v a < v b) → ∃ x ∈ b, v {x} + v a ≥ v b

def ef1_mutual (v : Finset Nat → Int) (a b : Finset Nat): Prop :=
  ef1 v a b ∧ ef1 v b a


-- EF1-mutual is commutative
theorem ef1_mutual_comm
    (vab_mutual : ef1_mutual v a b) :
      (ef1_mutual v b a) := by
  -- ef1_mutual v b a
  rw [ef1_mutual]
  -- ef1 v b a ∧ ef1 v a b
  rw [and_comm]
  -- ef1 v a b ∧ ef1 v b a
  exact vab_mutual

-- If a does not envy b, adding a new item x to b still fulfills EF1 from a to b
theorem ef_implies_ef1_insert_x
    (ef_vab : ef v a b)
    (v_add: additive v):
      ef1 v a (insert x b) := by
  -- ef1 v a (insert x b)
  rw [ef1]
  rw [ef] at ef_vab
  -- v a < v (insert x b) → ∃ x_1 ∈ insert x b, v {x_1} + v a ≥ v (insert x b)
  intro _
  -- ∃ x_1 ∈ insert x b, v {x_1} + v a ≥ v (insert x b)
  use x
  -- x ∈ insert x b ∧ v {x} + v a ≥ v (insert x b)
  apply And.intro
  -- x ∈ insert x b,     v {x} + v a ≥ v (insert x b)
  exact Finset.mem_insert_self x b
  -- v {x} + v a ≥ v (insert x b)
  rw [Finset.insert_eq]
  rw [v_add]
  simp
  -- v b ≤ v a
  exact ef_vab


-- If a does not envy b, and b's anvy toward a satisfies EF1,
-- we can add an item to b while still fulfilling mutual EF1
theorem ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x
    (ef_vab : ef v a b)
    (v_goods: value_goods v)
    (ef1_vba : ef1 v b a)
    (x : Nat)
    (v_add : additive v)
    (v_empty : value_empty v):
      ef1_mutual v a (insert x b):= by
  -- ef1_mutual v a (insert x b)
  rw [ef1_mutual]
  apply And.intro
  -- ef1 v a (insert x b),  f1 v (insert x b) a
  exact ef_implies_ef1_insert_x ef_vab v_add
  -- f1 v (insert x b) a
  rw [ef1]
  -- v (insert x b) < v a → ∃ x_1 ∈ a, v {x_1} + v (insert x b) ≥ v a
  rw [ef1] at ef1_vba
  intro vxb_lt_va
  -- ∃ x_1 ∈ a, v {x_1} + v (insert x b) ≥ v a
  rw [Finset.insert_eq]
  rw [v_add]
  simp
  have vb_lt_va : v b < v a := by
    -- v b < v a
    rw [Finset.insert_eq] at vxb_lt_va
    rw [v_add] at vxb_lt_va
    rw [Int.add_comm] at vxb_lt_va
    have v_x_pos : 0 ≤ v {x} := by
      -- 0 ≤ v {x}
      rw [le_iff_eq_or_lt]
      apply Or.intro_right
      exact v_goods x
    -- v b < v a
    exact lt_of_add_lt_of_nonneg_left vxb_lt_va v_x_pos
  -- ∃x_1 ∈ a, v a ≤ v {x_1} + (v {x} + v b)
  match ef1_vba vb_lt_va with
  | ⟨x_a, ⟨x_a_mem, x_a_ef1⟩⟩ =>
  use x_a
  -- x_a ∈ a ∧ v a ≤ v {x_a} + (v {x} + v b)
  apply And.intro
  -- x_a ∈ a,   v a ≤ v {x_a} + (v {x} + v b)
  exact x_a_mem
  -- v a ≤ v {x_a} + (v {x} + v b)
  simp at x_a_ef1
  rw [Int.add_comm]
  rw [Int.add_assoc]
  have vx_nonneg : 0 ≤ v {x} := by
    -- 0 ≤ v {x}
    apply le_of_lt_or_eq
    apply Or.intro_left
    exact v_goods x
  -- v a ≤ v {x} + (v b + v {x_a})
  refine le_add_of_nonneg_of_le vx_nonneg ?h.right.hbc
  -- v a ≤ v b + v {x_a}
  rw [Int.add_comm]
  exact x_a_ef1
  -- QED

-- For any two bundles, at least one must be unenvied
theorem ef_always : (ef v a b ∨ ef v b a):= by
  repeat rw [ef]
  exact Int.le_total (v b) (v a)



-- An EF1-allocaton always exists for two agents
theorem ef1_for_n_eq_2
  (M : Finset Nat)
  (v : Finset Nat → Int)
  (v_goods : value_goods v)
  (v_add : additive v)
  (v_empty : value_empty v):
    ∃ a1 a2 : Finset Nat,
      a1 ∪ a2 = M ∧
      a1 ∩ a2 = ∅ ∧
      ef1_mutual v a1 a2 := by
  -- ∃ a1 a2, a1 ∪ a2 = M ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual v a1 a2
  induction M using Finset.induction_on -- Induction on M
  case empty => -- Base step: ∅ has an ef1-allocation
    -- ∃ a1 a2, a1 ∪ a2 = ∅ ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual v a1 a2
    use ∅
    use ∅
    -- ∅ ∪ ∅ = ∅ ∧ ∅ ∩ ∅ = ∅ ∧ ef1_mutual v ∅ ∅
    apply And.intro
    -- ∅ ∪ ∅ = ∅,   ∅ ∩ ∅ = ∅ ∧ ef1_mutual v ∅ ∅
    simp
    -- ∅ ∩ ∅ = ∅ ∧ ef1_mutual v ∅ ∅
    apply And.intro
    -- ∅ ∩ ∅ = ∅,   ef1_mutual v ∅ ∅
    simp
    -- ef1_mutual v ∅ ∅
    rw [ef1_mutual]
    rw [and_self_iff]
    -- ef1 v ∅ ∅
    rw [ef1]
    repeat rw [v_empty]
    simp
    -- Base step complete
  case insert x I x_nmem_I exists_ef1_I => -- Inductive step: I has an ef1 allocation, show insert x I has an ef1-allocation
    -- ∃ a1 a2, a1 ∪ a2 = insert x I ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual v a1 a2
    match exists_ef1_I with -- Decompose inductive step into smaller pieces
    | ⟨a1, ⟨a2, ⟨a_union, a_inter, a_mutual_ef1⟩⟩⟩ =>
    have ef_va1a2_or_ef_va2a1 : ef v a1 a2 ∨ ef v a2 a1 := ef_always -- One of the bundles must not envy the other
    cases ef_va1a2_or_ef_va2a1 with -- Case split on which bundle is unenvied
    | inl ef_va1a2 => -- If a2 is unenvied
      -- ∃ a1 a2, a1 ∪ a2 = insert x I ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual v a1 a2
      use insert x a2
      use a1
      -- insert x a2 ∪ a1 = insert x I ∧ insert x a2 ∩ a1 = ∅ ∧ ef1_mutual v (insert x a2) a1
      apply And.intro
      -- insert x a2 ∪ a1 = insert x I,   insert x a2 ∩ a1 = ∅ ∧ ef1_mutual v (insert x a2) a1
      simp
      rw [Finset.union_comm]
      rw [a_union]
      -- insert x a2 ∩ a1 = ∅ ∧ ef1_mutual v (insert x a2) a1
      apply And.intro
      -- insert x a2 ∩ a1 = ∅,    ef1_mutual v (insert x a2) a1
      rw [Finset.inter_comm]
      rw [Finset.inter_insert_of_not_mem]-- This theorem requires x ∉ a1
      exact a_inter
      -- x ∉ a1,    ef1_mutual v (insert x a2) a1
      rw [← a_union] at x_nmem_I
      rw [Finset.not_mem_union] at x_nmem_I
      exact x_nmem_I.left
      -- ef1_mutual v (insert x a2) a1
      rw [ef1_mutual] at a_mutual_ef1
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x
                              ef_va1a2 v_goods a_mutual_ef1.right x v_add v_empty)
      -- Left case complete
    | inr ef_va2a1 => -- If a1 is unenvied
      -- ∃ a1 a2, a1 ∪ a2 = insert x I ∧ a1 ∩ a2 = ∅ ∧ ef1_mutual v a1 a2
      use insert x a1
      use a2
      -- insert x a1 ∪ a2 = insert x I ∧ insert x a1 ∩ a2 = ∅ ∧ ef1_mutual v (insert x a1) a2
      apply And.intro
      -- insert x a1 ∪ a2 = insert x I,   insert x a1 ∩ a2 = ∅ ∧ ef1_mutual v (insert x a1) a2
      rw [Finset.insert_eq]
      simp
      rw [a_union]
      rw [← Finset.insert_eq]
      -- insert x a1 ∩ a2 = ∅ ∧ ef1_mutual v (insert x a1) a2
      apply And.intro
      -- insert x a1 ∩ a2 = ∅,    ef1_mutual v (insert x a1) a2
      rw [Finset.inter_comm]
      rw [Finset.inter_insert_of_not_mem] -- This theorem requires x ∉ a2
      rw [Finset.inter_comm]
      exact a_inter
      -- x ∉ a2,    ef1_mutual v (insert x a1) a2
      rw [← a_union] at x_nmem_I
      rw [Finset.not_mem_union] at x_nmem_I
      exact x_nmem_I.right
      -- ef1_mutual v (insert x a1) a2
      rw [ef1_mutual] at a_mutual_ef1
      exact ef1_mutual_comm (ef_a_b_and_ef1_b_a_implies_mutual_ef1_insert_x
                              ef_va2a1 v_goods a_mutual_ef1.left x v_add v_empty)
      -- Right case complete
    -- Inductive step complete
  -- QED





-- This theorem ended up being unnecessary for the final proof
-- If a's envy toward b satisfies EF1, this is still the case if a new item x is added to a
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
