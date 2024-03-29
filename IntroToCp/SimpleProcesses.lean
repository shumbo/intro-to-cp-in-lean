import Mathlib.Order.Disjoint
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Basic
import «IntroToCp».SimpleChoreographies
import «IntroToCp».Maps

-- ## Syntax

variable {α : Type} [DecidableEq α]

inductive SimpleProc (α : Type) where
  | done
  | send (dst : α) (cont : SimpleProc α)
  | receive (src : α) (cont : SimpleProc α)
deriving Repr, DecidableEq

inductive Name where
  | alice : Name
  | bob : Name
  | charlie : Name
  | buyer : Name
  | seller : Name
  | client : Name
  | gateway : Name
  | server : Name
deriving Repr, DecidableEq

-- Example 3.2
-- for buyer
#check SimpleProc.send Name.alice $ SimpleProc.receive Name.bob $ SimpleProc.done
-- for seller
#check SimpleProc.receive Name.bob $ SimpleProc.send Name.alice $ SimpleProc.done

-- Exercise 3.1
-- 1
example := SimpleProc.receive Name.alice SimpleProc.done
-- 2
example := SimpleProc.send Name.bob SimpleProc.done
-- 3
example := SimpleProc.send Name.charlie SimpleProc.done

-- ## Networks

def SimpleNet (α : Type) [DecidableEq α] := α → SimpleProc α
def SimpleNet.supp (N: SimpleNet α) : Set α := setOf (λ n => N n ≠ SimpleProc.done)

instance {α : Type} [DecidableEq α] (n : α) (N : SimpleNet α) : Decidable (n ∈ SimpleNet.supp N) := by
  unfold SimpleNet.supp
  by_cases N n = SimpleProc.done
  {
    apply isFalse
    intro h
    contradiction
  }
  {
    apply isTrue
    simp
    assumption
  }

def SimpleNet.terminated  : SimpleNet α := λ _ => SimpleProc.done

def SimpleNet.atomic  (p : α) (proc : SimpleProc α) : SimpleNet α := λ x => if p = x then proc else SimpleProc.done

@[simp]
def SimpleNet.update (N: SimpleNet α) (name : α) (proc : SimpleProc α) : SimpleNet α := λ n => if n = name then proc else N n

abbrev simple_net_demo : SimpleNet Name := (SimpleNet.terminated.update Name.alice (SimpleProc.send Name.bob SimpleProc.done))

example : Name.alice ∈ (SimpleNet.supp simple_net_demo) := by
  unfold SimpleNet.supp
  simp [simple_net_demo, SimpleNet.terminated]

example : Name.bob ∉ (SimpleNet.supp simple_net_demo) := by
  unfold SimpleNet.supp
  simp [simple_net_demo, SimpleNet.terminated]


def SimpleNet.parallel (N M : SimpleNet α) (h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)) : SimpleNet α := λ p => if p ∈ SimpleNet.supp N then N p else M p

example : SimpleNet Name := SimpleNet.parallel
  (SimpleNet.terminated.update Name.buyer (SimpleProc.send Name.seller (SimpleProc.receive Name.seller SimpleProc.done)))
  (SimpleNet.terminated.update Name.bob (SimpleProc.receive Name.buyer (SimpleProc.send Name.buyer SimpleProc.done)))
  (by
    simp [SimpleNet.supp, SimpleNet.terminated]
  )

theorem SimpleNet.mem_supp_running {N : SimpleNet α} {p : α} : p ∈ SimpleNet.supp N → N p ≠ SimpleProc.done := by
  intro h
  intro c
  unfold SimpleNet.supp at h
  exact h c

theorem SimpleNet.nmem_supp_terminated {N : SimpleNet α} {p : α} : p ∉ SimpleNet.supp N → N p = SimpleProc.done := by
  intro h
  unfold supp at h
  have := Set.nmem_setOf_iff.mp h
  simp at this
  exact this

theorem SimpleNet.supp_parallel_supp_union: ∀ (N M : SimpleNet α) (h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)), SimpleNet.supp (SimpleNet.parallel N M h) = SimpleNet.supp N ∪ SimpleNet.supp M := by
  intro N M h
  apply Set.ext
  simp
  intro p
  constructor
  {
    intro p_in_supp_par
    by_cases p ∈ SimpleNet.supp N
    {
      rename_i p_in_supp_N
      left
      assumption
    }
    {
      rename_i p_not_in_supp_N
      unfold supp parallel at p_in_supp_par
      simp at p_in_supp_par
      simp [p_not_in_supp_N] at p_in_supp_par
      right
      unfold supp
      simp
      assumption
    }
  }
  {
    intro p_in_supp
    cases p_in_supp
    {
      rename_i p_in_supp_N
      unfold parallel
      unfold supp ; simp
      intro c
      have := SimpleNet.mem_supp_running p_in_supp_N
      simp [this] at c
    }
    {
      rename_i p_in_supp_M
      have := Set.disjoint_right.mp h p_in_supp_M
      unfold parallel supp
      simp
      intro c
      have := SimpleNet.nmem_supp_terminated this
      simp [this] at c
      have := SimpleNet.mem_supp_running p_in_supp_M
      contradiction
    }
  }

theorem SimpleNet.ident {N : SimpleNet α} : SimpleNet.parallel N (SimpleNet.terminated) (by simp [supp, terminated]) = N := by
  unfold parallel
  simp
  funext p
  by_cases p ∈ supp N
  {
    rename_i p_in_supp_N
    simp [p_in_supp_N]
  }
  {
    rename_i p_nmem_supp_N
    simp [p_nmem_supp_N]
    simp [terminated]
    apply Eq.symm
    apply SimpleNet.nmem_supp_terminated
    assumption
  }

theorem SimpleNet.comm {N M : SimpleNet α} {h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)} : SimpleNet.parallel N M h = SimpleNet.parallel M N (disjoint_comm.mp h) := by
  funext p
  unfold parallel
  by_cases p ∈ supp N
  {
    rename_i p_mem_supp_N
    simp [p_mem_supp_N]
    have := Set.disjoint_left.mp h p_mem_supp_N
    simp [this]
  }
  {
    rename_i p_nmem_supp_N
    simp [p_nmem_supp_N]
    by_cases p ∈ supp M
    {
      rename_i p_mem_supp_M
      simp [p_mem_supp_M]
    }
    {
      rename_i p_nmem_supp_M
      simp [*]
      have h₁ := SimpleNet.nmem_supp_terminated p_nmem_supp_M
      have h₂ := SimpleNet.nmem_supp_terminated p_nmem_supp_N
      simp [h₁, h₂]
    }
  }

theorem SimpleNet.assoc
  {N₁ N₂ N₃ : SimpleNet α}
  {h₁ : Disjoint (SimpleNet.supp N₁) (SimpleNet.supp N₂)}
  {h₂ : Disjoint (SimpleNet.supp N₂) (SimpleNet.supp N₃)}
  {h₃ : Disjoint (SimpleNet.supp N₃) (SimpleNet.supp N₁)}
    : SimpleNet.parallel N₁ (SimpleNet.parallel N₂ N₃ h₂) (by {
        have := SimpleNet.supp_parallel_supp_union N₂ N₃ h₂
        simp [this]
        constructor
        exact h₁
        exact disjoint_comm.mp h₃
      })
        =
      SimpleNet.parallel (SimpleNet.parallel N₁ N₂ h₁) N₃ (by {
        have := SimpleNet.supp_parallel_supp_union N₁ N₂ h₁
        simp [this]
        constructor
        exact disjoint_comm.mp h₃
        exact h₂
      }) := by
        funext p
        by_cases p ∈ supp N₁
        {
          rename_i p_mem_supp_N₁
          simp [parallel]
          simp [SimpleNet.supp_parallel_supp_union]
          simp [p_mem_supp_N₁]
        }
        {
          rename_i p_nmem_supp_N₁
          simp [parallel, p_nmem_supp_N₁]
          by_cases p ∈ supp N₂
          {
            rename_i p_mem_supp_N₂
            simp [SimpleNet.supp_parallel_supp_union]
            simp [p_mem_supp_N₂]
          }
          {
            rename_i p_nmem_supp_N₂
            simp [p_nmem_supp_N₂, SimpleNet.supp_parallel_supp_union, p_nmem_supp_N₁]
          }
        }

-- Proposition 3.5 (Exercise 3.4)
theorem SimpleNet.parallel_atomic_terminated (N : SimpleNet α) (p : α) :
    SimpleNet.parallel N (SimpleNet.atomic p SimpleProc.done) (by simp [atomic, supp]) = N := by
      funext name
      by_cases name ∈ supp N
      {
        rename_i name_mem_supp_N
        simp [parallel, name_mem_supp_N]
      }
      {
        rename_i name_nmem_supp_N
        simp [parallel, name_nmem_supp_N]
        have := SimpleNet.nmem_supp_terminated name_nmem_supp_N
        simp [this, atomic]
      }

-- ## Semantics

inductive SimpleNet.Step : (SimpleNet α) → (α × α) → (SimpleNet α) → Prop where
  | comm : ∀ p q P Q (hneq : p ≠ q), Step
    (parallel (atomic p (SimpleProc.send q P)) (atomic q (SimpleProc.receive p Q)) (by simp [atomic, supp, hneq]))
    (p, q)
    (parallel (atomic p P) (atomic q Q) (by {
      simp [supp, atomic]
      by_cases P = SimpleProc.done
      {
        rename_i h
        simp [h]
      }
      {
        rename_i h
        simp [h]
        intro c
        have := c.symm
        contradiction
      }
    }))
  | par : ∀ N N' M μ (h₁ : Disjoint (supp N) (supp M)) (h₂ : Disjoint (supp N') (supp M)), Step N μ N' → Step (parallel N M h₁) μ (parallel N' M h₂)

-- example 3.8
example : SimpleNet.Step
  (SimpleNet.parallel
    (SimpleNet.atomic Name.buyer (SimpleProc.send Name.seller $ SimpleProc.receive Name.seller SimpleProc.done))
    (SimpleNet.atomic Name.seller (SimpleProc.receive Name.buyer $ SimpleProc.send Name.buyer SimpleProc.done))
    (by simp [SimpleNet.supp, SimpleNet.atomic])
  )
  (Name.buyer, Name.seller)
  (SimpleNet.parallel
    (SimpleNet.atomic Name.buyer (SimpleProc.receive Name.seller SimpleProc.done))
    (SimpleNet.atomic Name.seller (SimpleProc.send Name.buyer SimpleProc.done))
    (by simp [SimpleNet.supp, SimpleNet.atomic])
  ) := by
    apply SimpleNet.Step.comm
    simp

-- Fundamental Properties of the Semantics

-- proposition 3.7
theorem SimpleNet.step_nmem_unchange {N N' : SimpleNet α} {μ : (α × α)} {r : α} : Step N μ N' → r ∉ (pn μ) → N r = N' r := by
  intros N_steps r_nmem
  simp [pn] at r_nmem
  induction N_steps with
  | comm p q P Q hneq => {
      simp [parallel, supp, atomic, r_nmem]
      simp at r_nmem
      have ⟨neq₁, neq₂⟩ := not_or.mp r_nmem
      have neq₁' : p ≠ r := by intro c ; have := c.symm ; contradiction
      have neq₂' : q ≠ r := by intro c ; have := c.symm ; contradiction
      simp [neq₁, neq₂, neq₁', neq₂']
  }
  | par N N' M μ d₁ d₂ h₁ N_steps => {
      simp at *
      obtain ⟨p₁, p₂⟩ := μ
      simp [*] at *
      simp [parallel]
      simp [supp]
      have := N_steps r_nmem
      simp [this]
      by_cases N' r = SimpleProc.done
      simp [*]
      simp [*]
  }

def SimpleNet.remove (N: SimpleNet α) (p : α) : SimpleNet α := λ q => if q = p then SimpleProc.done else N q

theorem SimpleNet.supp_remove_subset_supp (N: SimpleNet α) (p : α) : supp (remove N p) ⊆ supp N := by
  simp [supp, remove]

-- proposition 3.8
theorem SimpleNet.nmem_supp_remove_unchange {N : SimpleNet α} : p ∉ supp N → remove N p = N := by
  intro p_nmem_supp_N
  unfold remove
  funext name
  by_cases name = p
  {
    rename_i h
    have := SimpleNet.nmem_supp_terminated p_nmem_supp_N
    simp [this, h]
  }
  {
    rename_i neq
    simp [neq]
  }

-- proposition 3.9
theorem SimpleNet.remove_order_irrelevant {N : SimpleNet α} {p q : α} : (N.remove p).remove q = (N.remove q).remove p := by
  funext name
  by_cases name = q
  {
    rename_i heq
    simp [remove, heq]
  }
  {
    rename_i hneq
    simp [remove, hneq]
  }

-- lemma 3.10

-- FIXME: This proof is too long. There must be a better way.
theorem SimpleNet.step_nmem_step {N N' : SimpleNet α} {μ : (α × α)} {r : α} : Step N μ N' → r ∉ pn μ → Step (N.remove r) μ (N'.remove r) := by
  intros n_steps r_nmem
  induction n_steps with
    -- case 1
  | comm p q P Q h => {
      simp [pn] at r_nmem
      let N := parallel (atomic p (SimpleProc.send q P)) (atomic q (SimpleProc.receive p Q)) (by {
          simp [supp, atomic, h]
      })
      have supp_N : supp N = {p, q} := by
          simp [supp, parallel, atomic]
          apply Set.ext ; intro name
          constructor
          {
            intro h
            simp at h
            by_cases name = p
            {
              rename_i h₂
              simp [h₂]
            }
            {
              rename_i h₂
              simp [h₂]
              simp [*] at *
              exact id h.symm
            }
          }
          {
            intro h
            simp
            by_cases name = p
            {
              rename_i h₂
              simp [h₂]
            }
            {
              rename_i h₂
              simp [*] at *
              exact id h.symm
            }
          }
      have r_nmem_supp_N : r ∉ supp N := by simp [supp_N] ; assumption
      have := SimpleNet.nmem_supp_remove_unchange r_nmem_supp_N
      simp [this]
      let N' := (parallel (atomic p P) (atomic q Q) (by {
        simp [supp, atomic]
        by_cases P = SimpleProc.done
        {
          simp [*]
        }
        {
          simp [*]
          intro c
          exact (h (id c.symm)).elim
        }
      }))
      have supp_N'_subset : supp N' ⊆ {p, q} := by
        simp [supp, atomic, parallel]
        simp [Set.subset_def]; intro name
        intro h
        by_cases p = name
        {
          rename_i h₂
          left ; exact id h₂.symm
        }
        {
          rename_i h₂
          simp [h₂] at h
          right ; exact h.left.symm
        }
      have r_nmem_supp_N' : r ∉ supp N' := by
        exact Set.not_mem_subset supp_N'_subset r_nmem
      have := nmem_supp_remove_unchange r_nmem_supp_N'
      simp [this]
      constructor
      assumption
  }
  -- case 2
  | par M₁ M₁' M₂ μ d₁ d₂ n_steps ih => {
      rename_i d₁ d₂
      by_cases r ∈ supp M₁
      {
        -- case 2.1
        rename_i h
        have := ih r_nmem
        have : remove (parallel M₁ M₂ d₁) r = parallel (remove M₁ r) M₂ (by {
          have := SimpleNet.supp_remove_subset_supp M₁ r
          apply Set.disjoint_of_subset_left
          exact this
          exact d₁
        }) := by
          funext name
          by_cases r = name
          {
            simp [remove, parallel, supp, *]
            have := Set.disjoint_left.mp d₁ h
            have := SimpleNet.nmem_supp_terminated this
            simp [*] at this
            exact this.symm
          }
          {
            rename_i neq
            have : name ≠ r := by intro c ; exact neq c.symm
            simp [remove, parallel, supp, neq, this]
            by_cases M₁ name = SimpleProc.done <;> rename_i h <;> simp [h]
          }
        simp [this]
        have : remove (parallel M₁' M₂ d₂) r = parallel (remove M₁' r) M₂ (by {
          apply Set.disjoint_of_subset_left
          exact SimpleNet.supp_remove_subset_supp M₁' r
          exact d₂
        }) := by
          funext name
          by_cases r = name <;> rename_i h₂
          {
            simp [remove, parallel, supp, h₂]
            have := Set.disjoint_left.mp d₁ h
            have := SimpleNet.nmem_supp_terminated this
            simp [this.symm, h₂]
          }
          {
            have : name ≠ r := by intro c ; exact h₂ c.symm
            simp [remove, parallel, supp, h₂, this]
            by_cases M₁' name = SimpleProc.done <;> rename_i h <;> simp [h]
          }
        simp [this]
        constructor
        exact ih r_nmem
      }
      rename_i r_nmem_supp_M₁
      by_cases r ∈ supp M₂
      {
        -- case 2.2
        have : (remove (parallel M₁ M₂ d₁) r) = parallel M₁ (M₂.remove r) (by {
          apply Set.disjoint_of_subset_right
          exact SimpleNet.supp_remove_subset_supp M₂ r
          exact d₁
        }) := by
          funext name
          simp [remove, parallel]
          by_cases name = r <;> rename_i h₂
          {
            simp [h₂, r_nmem_supp_M₁]
          }
          {
            simp [h₂]
          }
        simp [this]
        have : (remove (parallel M₁' M₂ d₂) r) = parallel M₁' (M₂.remove r ) (by {
          apply Set.disjoint_of_subset_right
          exact SimpleNet.supp_remove_subset_supp M₂ r
          exact d₂

        }) := by
          funext name
          by_cases name = r <;> rename_i h₂
          {
            simp [remove, parallel, supp, h₂]
            by_cases M₁' r = SimpleProc.done
            {
              rename_i h
              simp [h]
            }
            {
              rename_i h
              simp [h]
              subst name
              have := SimpleNet.step_nmem_unchange n_steps r_nmem
              rw [←this]
              have := SimpleNet.nmem_supp_terminated r_nmem_supp_M₁
              exact this.symm
            }
          }
          {
            simp [remove, parallel, supp, h₂]
            by_cases M₁' name = SimpleProc.done <;> rename_i h₃
            {
              simp [h₃]
            }
            {
              simp [h₃]
            }
          }
        simp [this]
        apply Step.par
        exact n_steps
      }
      {
        -- case 2.3
        rename_i r_nmem_supp_M₂
        have x : remove (parallel M₁ M₂ d₁) r = (parallel M₁ M₂ d₁) := by
          apply nmem_supp_remove_unchange
          simp [supp, parallel]
          by_cases M₁ r = SimpleProc.done
          {
            rename_i h₂
            simp [h₂]
            exact nmem_supp_terminated r_nmem_supp_M₂
          }
          {
            rename_i h₂
            simp [h₂]
            exact h₂ (nmem_supp_terminated r_nmem_supp_M₁)
          }
        simp [x]
        have : remove (parallel M₁' M₂ d₂) r = parallel M₁' M₂ d₂ := by
          funext name
          simp [remove, parallel]
          by_cases name = r
          {
            rename_i h₂
            simp [h₂]
            have x := SimpleNet.step_nmem_unchange n_steps r_nmem
            have y := SimpleNet.nmem_supp_terminated r_nmem_supp_M₁
            by_cases r ∈ supp M₁'
            {
              rename_i h₃
              have := SimpleNet.mem_supp_running h₃
              simp [x] at y
              contradiction
            }
            {
              rename_i h₃
              simp [h₃]
              exact (SimpleNet.nmem_supp_terminated r_nmem_supp_M₂).symm
            }
          }
          {
            rename_i h₂
            simp [h₂]
          }
        simp [this]
        constructor
        assumption
      }
  }

def SimpleNet.remove_list (N : SimpleNet α) (ps : List α) : SimpleNet α := match ps with
  | [] => N
  | t::h => (N.remove t).remove_list h

-- TODO: Proposition 3.11

@[simp]
def listToSet (l : List α) : Set α :=
  l.foldr (λ x s => Set.insert x s) ∅


-- lemma 3.12
theorem SimpleNet.step_nmem_step_list {N N' : SimpleNet α} {μ : (α × α)} {rs : List α} : Step N μ N' → Disjoint (listToSet rs) (pn μ) → Step (N.remove_list rs) μ (N'.remove_list rs) := by
  intros N_steps d
  induction rs generalizing N N' with
  | nil => {
    simp [remove_list]
    assumption
  }
  | cons h t ih => {
    by_cases h ∈ pn μ
    {
      -- impossible because h :: t and pn μ are disjoint
      rename_i h_mem
      have := Set.disjoint_right.mp d h_mem
      simp at this
      have : h ∈ Set.insert h (List.foldr (fun x s => Set.insert x s) ∅ t) := by
        exact (this (Or.inl rfl)).elim
      contradiction
    }
    {
      rename_i h_nmem
      simp [remove_list]
      apply ih
      apply step_nmem_step
      assumption
      assumption
      have : listToSet t ⊆ (listToSet (h :: t)) := by
        simp
        simp [Set.subset_def]
        intro x hx
        apply Set.mem_insert_iff.mp
        by_cases x = h <;> simp [*]
      apply Set.disjoint_of_subset_left this
      assumption
    }
  }
