import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Order.Disjoint
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Basic
import «IntroToCp».SimpleChoreographies
import «IntroToCp».Maps

-- ## Syntax

inductive SimpleProc {α : Type} where
  | done
  | send (dst : α) (cont : SimpleProc (α := α))
  | receive (src : α) (cont : SimpleProc (α := α))
deriving Repr, DecidableEq

inductive Name where
  | alice : Name
  | bob : Name
  | charlie : Name
  | buyer : Name
  | seller : Name
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

def SimpleNet (α : Type) [DecidableEq α] := α → SimpleProc (α := α)
def SimpleNet.supp {α : Type} [DecidableEq α] (N: SimpleNet α) : Set α := setOf (λ n => N n ≠ SimpleProc.done)

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

def SimpleNet.terminated {α : Type} [DecidableEq α] : SimpleNet α := λ _ => SimpleProc.done

@[simp]
def SimpleNet.update {α : Type} [DecidableEq α] (N: SimpleNet α) (name : α) (proc : SimpleProc (α := α)) : SimpleNet α := λ n => if h: n = name then proc else N n

abbrev simple_net_demo : SimpleNet Name := (SimpleNet.terminated.update Name.alice (SimpleProc.send Name.bob SimpleProc.done))

example : Name.alice ∈ (SimpleNet.supp simple_net_demo) := by
  unfold SimpleNet.supp
  simp [simple_net_demo, SimpleNet.terminated]

example : Name.bob ∉ (SimpleNet.supp simple_net_demo) := by
  unfold SimpleNet.supp
  simp [simple_net_demo, SimpleNet.terminated]


def SimpleNet.parallel {α : Type} [DecidableEq α] (N M : SimpleNet α) (h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)) : SimpleNet α := λ p => if p ∈ SimpleNet.supp N then N p else M p

example : SimpleNet Name := SimpleNet.parallel
  (SimpleNet.terminated.update Name.buyer (SimpleProc.send Name.seller (SimpleProc.receive Name.seller SimpleProc.done)))
  (SimpleNet.terminated.update Name.bob (SimpleProc.receive Name.buyer (SimpleProc.send Name.buyer SimpleProc.done)))
  (by
    simp [SimpleNet.supp, SimpleNet.terminated, Finset.empty]
  )

theorem SimpleNet.mem_supp_running {α : Type} [DecidableEq α] {N : SimpleNet α} {p : α} : p ∈ SimpleNet.supp N → N p ≠ SimpleProc.done := by
  intro h
  intro c
  unfold SimpleNet.supp at h
  contradiction

theorem SimpleNet.nmem_supp_terminated {α : Type} [DecidableEq α] {N : SimpleNet α} {p : α} : p ∉ SimpleNet.supp N → N p = SimpleProc.done := by
  intro h
  unfold supp at h
  have := Set.nmem_setOf_iff.mp h
  simp at this
  exact this

theorem SimpleNet.supp_parallel_supp_union {α : Type} [DecidableEq α]: ∀ (N M : SimpleNet α) (h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)), SimpleNet.supp (SimpleNet.parallel N M h) = SimpleNet.supp N ∪ SimpleNet.supp M := by
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

theorem SimpleNet.ident {α : Type} [DecidableEq α] {N : SimpleNet α} : SimpleNet.parallel N (SimpleNet.terminated) (by simp [supp, terminated]) = N := by
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

theorem SimpleNet.comm {α : Type} [DecidableEq α] {N M : SimpleNet α} {h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)} : SimpleNet.parallel N M h = SimpleNet.parallel M N (disjoint_comm.mp h) := by
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

theorem SimpleNet.assoc {α : Type} [DecidableEq α]
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
