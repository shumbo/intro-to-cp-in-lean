import Mathlib.Order.Disjoint
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import «IntroToCp».SimpleChoreographies
import «IntroToCp».Maps
import «IntroToCp».Name

open Fintype

variable {α : Type} [DecidableEq α] [fin : Fintype α]

inductive SimpleProc (α : Type) where
| done
| send (dst : α) (cont : SimpleProc α)
| receive (src : α) (cont : SimpleProc α)
deriving Repr, DecidableEq

def SimpleNet (α : Type) [DecidableEq α] [Fintype α] := α → SimpleProc α
def SimpleNet.supp (N : SimpleNet α) : Finset α := (fin.elems).filter (λ name => N name ≠ SimpleProc.done)
def SimpleNet.terminated : SimpleNet α := λ _ => SimpleProc.done
def SimpleNet.atomic  (p : α) (proc : SimpleProc α) : SimpleNet α := λ x => if p = x then proc else SimpleProc.done
def SimpleNet.parallel (N M : SimpleNet α) (_ : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)) : SimpleNet α := λ p => if p ∈ SimpleNet.supp N then N p else M p

@[simp]
def SimpleNet.update (N: SimpleNet α) (name : α) (proc : SimpleProc α) : SimpleNet α := λ n => if n = name then proc else N n

@[simp]
theorem SimpleNet.mem_supp_mem_elems {N : SimpleNet α} {p : α} : p ∈ supp N → p ∈ elems := by
  intro h
  simp [supp] at h
  exact h.left

theorem SimpleNet.mem_supp_running {N : SimpleNet α} {p : α} : p ∈ SimpleNet.supp N → N p ≠ SimpleProc.done := by
  intro h c
  unfold SimpleNet.supp at h
  have := (Finset.mem_filter.mp h).right
  contradiction

theorem SimpleNet.nmem_supp_terminated {N : SimpleNet α} {p : α} : p ∉ SimpleNet.supp N → N p = SimpleProc.done := by
  intro h
  simp [supp] at h
  exact h (fin.complete p)

theorem SimpleNet.supp_parallel_supp_union: ∀ (N M : SimpleNet α) (h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)), SimpleNet.supp (SimpleNet.parallel N M h) = SimpleNet.supp N ∪ SimpleNet.supp M := by
  intros N M h
  apply Finset.ext
  intro p
  constructor
  {
    -- ->
    intro p_mem_supp_par
    simp
    by_cases p ∈ supp N
    {
      left ; assumption
    }
    {
      rename_i p_nmem_supp_N
      right
      simp [supp, parallel] at p_mem_supp_par
      simp [supp]
      constructor
      exact p_mem_supp_par.left
      have := p_mem_supp_par.right
      simp [p_mem_supp_par.left] at this
      by_cases h₂: N p = SimpleProc.done
      {
        simp [h₂] at this
        exact this
      }
      {
        simp [h₂] at this
        have := nmem_supp_terminated p_nmem_supp_N
        contradiction
      }
    }
  }
  {
    -- <-
    intro p_in_supp_union
    simp at p_in_supp_union
    cases p_in_supp_union with
    | inl p_mem_supp_N => {
      simp [supp] at p_mem_supp_N
      simp [supp, parallel, p_mem_supp_N]
    }
    | inr p_mem_supp_M => {
      simp [supp, parallel, p_mem_supp_M]
      constructor
      exact mem_supp_mem_elems p_mem_supp_M
      intro c
      simp [mem_supp_mem_elems p_mem_supp_M] at c
      by_cases h₂ : N p = SimpleProc.done
      {
        simp [h₂] at c
        have := mem_supp_running p_mem_supp_M
        contradiction
      }
      {
        simp [h₂] at c
      }
    }
  }

theorem SimpleNet.ident {N : SimpleNet α} : SimpleNet.parallel N (SimpleNet.terminated) (by simp [supp, terminated]) = N := by
  funext p
  simp [parallel]
  intro h
  have := nmem_supp_terminated h
  unfold terminated
  exact id this.symm

theorem SimpleNet.comm {N M : SimpleNet α} {h : Disjoint (SimpleNet.supp N) (SimpleNet.supp M)} : SimpleNet.parallel N M h = SimpleNet.parallel M N (disjoint_comm.mp h) := by
  funext p
  simp [parallel, supp, fin.complete]
  by_cases h₁ : p ∈ supp N
  {
    have := mem_supp_running h₁
    simp [this]
    by_cases h₂ : p ∈ supp M
    {
      have := Finset.disjoint_left.mp h h₁
      contradiction
    }
    {
      simp [nmem_supp_terminated, h₂]
    }
  }
  {
    have := nmem_supp_terminated h₁
    simp [this]
    by_cases h₂ : p ∈ supp M
    {
      simp [h₂, mem_supp_running]
    }
    {
      simp [h₂, nmem_supp_terminated]
    }
  }

theorem SimpleNet.assoc
  {N₁ N₂ N₃ : SimpleNet α}
  {d₁ : Disjoint (supp N₁) (supp N₂)}
  {d₂ : Disjoint (supp N₂) (supp N₃)}
  {d₃ : Disjoint (supp N₃) (supp N₁)}
  :
    parallel N₁ (parallel N₂ N₃ d₂) (by {
    simp [supp_parallel_supp_union]
    exact { left := d₁, right := id (Disjoint.symm d₃) }
    })
    =
    parallel (parallel N₁ N₂ d₁) N₃ (by simp [supp_parallel_supp_union] ; exact
    { left := id (Disjoint.symm d₃), right := d₂ })
  := by
    funext p
    by_cases p ∈ supp N₁
    {
      rename_i p_mem_supp_N₁
      have := mem_supp_mem_elems p_mem_supp_N₁
      simp [supp, parallel, this, mem_supp_running p_mem_supp_N₁]
    }
    {
      rename_i p_nmem_supp_N₁
      simp [supp, parallel, fin.complete, nmem_supp_terminated p_nmem_supp_N₁]
    }

-- Proposition 3.5 (Exercise 3.4)
theorem SimpleNet.parallel_atomic_terminated (N : SimpleNet α) (p : α) :
  parallel N (atomic p SimpleProc.done) (by simp [atomic, supp]) = N := by
    funext name
    simp [parallel, atomic]
    intro h
    simp [nmem_supp_terminated h]


-- ## Semantics

theorem SimpleNet.disjoint_atomics {x y : SimpleProc α} {p q : α} : p ≠ q → Disjoint (supp (atomic p x)) (supp (atomic q y)) := by
  intro hneq
  simp [supp, atomic]
  apply Finset.disjoint_filter.mpr
  intro r _ hr
  intro c
  have : p = q := by simp [c.left, hr.left]
  exact hneq this

inductive SimpleNet.Step : (SimpleNet α) → (α × α) → (SimpleNet α) → Prop where
  | comm : ∀ p q P Q (hneq : p ≠ q), Step
    (parallel (atomic p (SimpleProc.send q P)) (atomic q (SimpleProc.receive p Q)) (by simp [disjoint_atomics hneq]))
    (p, q)
    (parallel (atomic p P) (atomic q Q) (by simp [disjoint_atomics hneq]))
  | par : ∀ N N' M μ (h₁ : Disjoint (supp N) (supp M)) (h₂ : Disjoint (supp N') (supp M)), Step N μ N' → Step (parallel N M h₁) μ (parallel N' M h₂)

-- proposition 3.7
theorem SimpleNet.step_nmem_unchange {N N' : SimpleNet α} {μ : (α × α)} {r : α} : Step N μ N' → r ∉ (pn μ) → N r = N' r := by
  intros N_steps r_nmem
  induction N_steps with
  | comm p q P Q hneq => {
    simp [parallel, supp, atomic, r_nmem, fin.complete]
    simp [pn] at r_nmem
    have ⟨neq₁, neq₂⟩ := not_or.mp r_nmem
    have neq₁' : p ≠ r := by intro c ; have := c.symm ; contradiction
    have neq₂' : q ≠ r := by intro c ; have := c.symm ; contradiction
    simp [neq₁, neq₂, neq₁', neq₂']
  }
  | par N N' M μ d₁ d₂ h₁ N_steps => {
    simp at *
    obtain ⟨p₁, p₂⟩ := μ
    simp [*] at *
    simp [parallel, supp, fin.complete]
    simp [pn] at r_nmem
    by_cases N r = SimpleProc.done <;> simp [r_nmem, N_steps.symm]
  }

def SimpleNet.remove (N: SimpleNet α) (p : α) : SimpleNet α :=
  λ q => if q = p then SimpleProc.done else N q

theorem SimpleNet.supp_remove_subset_supp (N: SimpleNet α) (p : α) : supp (remove N p) ⊆ supp N := by
  simp [supp, remove]
  apply Finset.subset_iff.mpr
  intro name h
  have := Finset.mem_filter.mp h
  refine Finset.mem_filter.mpr ?_
  constructor
  exact complete name
  exact this.right.right

-- proposition 3.8
theorem SimpleNet.nmem_supp_remove_unchange {N : SimpleNet α} : p ∉ supp N → remove N p = N := by
  intro p_nmem
  have := nmem_supp_terminated p_nmem
  funext name
  by_cases h : p = name
  {
    simp [remove, h]
    rw [h] at this
    exact id this.symm
  }
  {
    simp [remove, h]
    intro c
    exact (h (id c.symm)).elim
  }


-- proposition 3.9
theorem SimpleNet.remove_order_irrelevant {N : SimpleNet α} {p q : α} : (N.remove p).remove q = (N.remove q).remove p := by
  funext r
  by_cases h : r = q <;> simp [remove, h]

-- lemma 3.10
theorem SimpleNet.step_nmem_step {N N' : SimpleNet α} {μ : (α × α)} {r : α} : Step N μ N' → r ∉ pn μ → Step (N.remove r) μ (N'.remove r) := by
  intros N_steps r_nmem
  induction N_steps with
  | comm p q P Q hneq => {
    simp [pn, not_or] at r_nmem
    let N := parallel (atomic p (SimpleProc.send q P)) (atomic q (SimpleProc.receive p Q)) (by { apply disjoint_atomics ; assumption })
    have supp_N : supp N = {p, q} := by
      simp [supp, parallel, atomic, fin.complete]
      apply Finset.ext ; intro name
      apply Iff.intro
      {
        intro h
        by_cases h₁ : p = name
        {
          simp [h₁]
        }
        {
          simp [h₁] at h
          simp
          right
          exact h.right.symm
        }
      }
      {
        intro h
        simp at h
        cases h
        {
          rename_i h
          simp [h, fin.complete]
        }
        {
          rename_i h
          simp [h, fin.complete, hneq]
        }
      }
    have r_nmem_supp_N : r ∉ supp N := by simp [supp_N, not_or] ; assumption
    have := SimpleNet.nmem_supp_remove_unchange r_nmem_supp_N
    simp [this]
    have : remove (parallel (atomic p P) (atomic q Q) (by {apply disjoint_atomics ; assumption})) r = (parallel (atomic p P) (atomic q Q) (by {apply disjoint_atomics ; assumption})) := by
      funext name
      simp [atomic, parallel, supp, remove, fin.complete]
      intro h
      have : p ≠ name := by {
        simp [h]
        intro c
        exact r_nmem.left c.symm
      }
      simp [this]
      have : q ≠ name := by {
        simp [h]
        intro c
        exact r_nmem.right c.symm
      }
      simp [this]
    simp [this]
    constructor
    assumption
  }
  | par M₁ M₁' M₂ μ d₁ d₂ n_steps ih => {
    rename_i d₁ d₂
    by_cases r ∈ supp M₁
    {
      -- case 2.1
      rename_i h
      have := ih r_nmem
      have : remove (parallel M₁ M₂ d₁) r = parallel (remove M₁ r) M₂ (by {
        have := SimpleNet.supp_remove_subset_supp M₁ r
        apply Finset.disjoint_of_subset_left
        exact this
        exact d₁
      }) := by
        funext name
        by_cases r = name
        {
          simp [remove, parallel, supp, *]
          have := Finset.disjoint_left.mp d₁ h
          have := SimpleNet.nmem_supp_terminated this
          simp [*] at this
          exact this.symm
        }
        {
          rename_i neq
          have : name ≠ r := by intro c ; exact neq c.symm
          simp [remove, parallel, supp, neq, this]
        }
      simp [this]
      have : remove (parallel M₁' M₂ d₂) r = parallel (remove M₁' r) M₂ (by {
        apply Finset.disjoint_of_subset_left
        exact SimpleNet.supp_remove_subset_supp M₁' r
        exact d₂
      }) := by
        funext name
        by_cases r = name <;> rename_i h₂
        {
          simp [remove, parallel, supp, h₂]
          have := Finset.disjoint_left.mp d₁ h
          have := SimpleNet.nmem_supp_terminated this
          simp [this.symm, h₂]
        }
        {
          have : name ≠ r := by intro c ; exact h₂ c.symm
          simp [remove, parallel, supp, h₂, this]
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
        apply Finset.disjoint_of_subset_right
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
        apply Finset.disjoint_of_subset_right
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
            simp [h, fin.complete]
            subst name
            have := SimpleNet.step_nmem_unchange n_steps r_nmem
            rw [←this]
            have := SimpleNet.nmem_supp_terminated r_nmem_supp_M₁
            exact this.symm
          }
        }
        {
          simp [remove, parallel, supp, h₂]
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
        simp [supp, parallel, fin.complete]
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

-- remove_list
def SimpleNet.remove_list (N : SimpleNet α) (ps : List α) : SimpleNet α := match ps with
| [] => N
| t::h => (N.remove t).remove_list h

theorem SimpleNet.supp_remove_list_subset_supp (N: SimpleNet α) (ps : List α) : supp (remove_list N ps) ⊆ supp N := by
  induction ps generalizing N with
  | nil => {
      simp [remove_list]
  }
  | cons head tail ih => {
      simp [remove_list]
      have := ih (remove N head)
      apply Set.Subset.trans this
      exact supp_remove_subset_supp N head
  }

theorem SimpleNet.terminated_remove_list_terminated {N: SimpleNet α} {name : α} : N name = SimpleProc.done → ∀ (ps : List α), (remove_list N ps) name = SimpleProc.done := by
  intros h ps
  induction ps generalizing N with
  | nil => simp [remove_list] ; assumption
  | cons head tail ih => {
    simp [remove_list]
    apply ih
    simp [remove]
    by_cases name = head
    {
      intro _
      contradiction
    }
    {
      intro _
      assumption
    }
  }

theorem SimpleNet.remove_list_terminated (N : SimpleNet α) {ps : List α} {name : α} : name ∈ ps → (N.remove_list ps) name = SimpleProc.done := by
  intros name_mem_ps
  induction ps generalizing N with
  | nil => contradiction
  | cons head tail ih => {
    simp [remove_list]
    by_cases h : name = head
    {
      have : (remove N name) name = SimpleProc.done := by
        simp [remove]
      have := terminated_remove_list_terminated this tail
      rw [h] at this
      rw [h]
      assumption
    }
    {
      apply ih
      exact List.mem_of_ne_of_mem h name_mem_ps
    }
  }

-- lemma 3.12
theorem SimpleNet.step_nmem_step_list {N N' : SimpleNet α} {μ : (α × α)} {rs : List α} : Step N μ N' → Disjoint rs.toFinset {μ.fst, μ.snd} → Step (N.remove_list rs) μ (N'.remove_list rs) := by
  intros N_steps d
  induction rs generalizing N N' with
  | nil => simp [remove_list] ; assumption
  | cons head tail ih => {
    obtain ⟨p, q⟩ := μ
    by_cases h : head = p ∨ head = q
    {
      -- impossible because head :: tail and pn μ are disjoint
      cases h <;> simp [*] at d
    }
    {
      simp [remove_list, pn]
      apply ih
      apply step_nmem_step
      {exact N_steps}
      {simp [pn] ; exact h}
      have : tail.toFinset ⊆ (head::tail).toFinset := by simp
      apply Finset.disjoint_of_subset_left this
      exact d
    }
  }

-- ### Transitions and Network Restriction

def SimpleNet.restrict (N: SimpleNet α) (ps : Finset α) : SimpleNet α := λ name => if name ∈ ps then N name else SimpleProc.done

-- proposition 3.13

def SimpleNet.restrict_supp_unchange (N: SimpleNet α) : N.restrict (supp N) = N := by
  simp [restrict, supp]
  funext p
  by_cases N p = SimpleProc.done
  {
    rename_i h
    simp [restrict, h]
  }
  {
    rename_i h
    simp [restrict, h]
    intro c
    simp [fin.complete] at c
  }


-- proposition 3.14

theorem SimpleNet.restrict_supp_subset (N : SimpleNet α) (ps : Finset α) : supp (N.restrict ps) ⊆ supp N := by
  intros name name_mem
  simp [supp, restrict] at name_mem
  by_cases name ∈ ps
  {
    rename_i h
    simp [h] at name_mem
    simp [supp]
    assumption
  }
  {
    rename_i h
    simp [h] at name_mem
  }

-- proposition 3.14

def SimpleNet.parallel_restrict_distrib (N M : SimpleNet α) (d : Disjoint (supp N) (supp M)) (p : Finset α) : (parallel N M d).restrict p = parallel (N.restrict p) (M.restrict p) (by {
  have d₁ := restrict_supp_subset N p
  have d₂ := restrict_supp_subset M p
  apply Finset.disjoint_of_subset_left
  assumption
  apply Finset.disjoint_of_subset_right
  assumption
  assumption
}) := by
  funext name
  simp [restrict, parallel]
  by_cases h₁ : name ∈ supp (restrict N p)
  {
    simp [h₁]
    by_cases h₂ : name ∈ p
    {
      simp [h₂]
      intro c
      have := restrict_supp_subset N p
      have := Finset.mem_of_subset this h₁
      contradiction
    }
    {
      simp [h₂]
    }
  }
  {
    simp [h₁]
    by_cases h₂ : name ∈ p
    {
      simp [h₂]
      intro c
      have := restrict_supp_subset N p
      simp [supp, restrict, fin.complete, h₂] at h₁
      have := mem_supp_running c
      contradiction
    }
    {
      simp [h₂]
    }
  }

-- proposition 3.15

def SimpleNet.nmem_supp_nmem_remove_list (N: SimpleNet α) (ps : List α) (name : α) : name ∉ supp N → name ∉ supp (N.remove_list ps) := by
  intro h
  induction ps generalizing N with
  | nil => {
    simp [supp, remove_list, fin.complete]
    apply nmem_supp_terminated
    assumption
  }
  | cons head tail ih => {
    simp [supp, remove_list, fin.complete]
    have : name ∉ supp (N.remove head) := by
      simp [supp, remove]
      intro _ _
      apply nmem_supp_terminated h
    have := ih (remove N head) this
    apply nmem_supp_terminated
    exact this
  }

def SimpleNet.nmem_remove_list_unchange (N: SimpleNet α) {ps : List α} {name : α} : name ∉ ps → N.remove_list ps name = N name := by
  intro h
  induction ps generalizing N with
  | nil => simp [remove_list]
  | cons head tail ih => {
    simp [remove_list]
    simp [not_or] at h
    have h₁ := h.left
    have h₂ := h.right
    have := ih (remove N head) h₂
    simp [remove, h₁] at this
    assumption
  }


def SimpleNet.mem_remove_list_nmem_supp (N: SimpleNet α) {ps : List α} {name : α} : name ∈ ps → name ∉ supp (N.remove_list ps) := by
  intro h
  induction ps generalizing N with
  | nil => contradiction
  | cons head tail ih => {
    simp at h
    cases h
    {
      rename_i heq
      simp [heq]
      simp [supp, remove_list, fin.complete]
      simp [←heq] at *
      have : name ∉ supp (remove N name) := by simp [supp, remove]
      have := nmem_supp_nmem_remove_list (remove N name) tail name this
      have := nmem_supp_terminated this
      assumption
    }
    {
      rename_i name_in_tail
      simp [remove_list]
      have := ih (remove N head) name_in_tail
      assumption
    }
  }

def SimpleNet.mem_supp_nmem_remove_list_mem_supp (N: SimpleNet α) {ps : List α} {name : α} : name ∈ supp N → name ∉ ps → name ∈ supp (N.remove_list ps) := by
  intros h₁ h₂
  induction ps generalizing N with
  | nil => simp [supp, remove_list, fin.complete, mem_supp_running h₁]
  | cons head tail ih => {
    simp [remove_list, supp, fin.complete]
    simp [not_or] at h₂
    obtain ⟨h₂₁, h₂₂⟩ := h₂
    have : name ∈ supp (remove N head) := by
      simp [remove, supp, fin.complete]
      apply And.intro
      assumption
      exact mem_supp_running h₁
    have := ih (remove N head) this h₂₂
    simp [mem_supp_running this]
  }


def SimpleNet.parallel_remove_restrict (N : SimpleNet α) (ps : List α) :
  N = parallel (N.remove_list ps) (N.restrict ps.toFinset) (by {
    apply Finset.disjoint_right.mpr
    intros name name_mem_supp_restrict
    simp [restrict, supp] at name_mem_supp_restrict
    have name_mem_ps := name_mem_supp_restrict.right.left
    have := remove_list_terminated (N) name_mem_ps
    simp [supp, fin.complete]
    assumption
  }) := by
    funext name
    simp [parallel, remove_list, restrict]
    by_cases h₁ : name ∈ ps
    {
      -- if name is in ps, then N name = (N.restrict ps) name
      simp [h₁]
      have := mem_remove_list_nmem_supp (N) h₁
      simp [this]
    }
    {
      -- if name is not in ps, then N name = N.remove_list ps
      simp [h₁]
      have := nmem_remove_list_unchange (N) h₁
      simp [this]
      -- if N name = terminated
      by_cases h₃ : N name = SimpleProc.done
      {
        simp [h₃]
      }
      {
        have : name ∈ supp N := by simp [supp, fin.complete, h₃]
        have := mem_supp_nmem_remove_list_mem_supp N this h₁
        simp [this]
      }
    }

-- lemma 3.16

theorem SimpleNet.step_restrict_step {N N' : SimpleNet α} {μ : (α × α)} : Step N μ N' → Step (N.restrict (pn μ)) μ (N'.restrict (pn μ)) := by
  simp [pn]
  intro N_steps
  induction N_steps with
  | comm p q P Q hneq => {
    simp
    have : ∀ (P Q : SimpleProc α), P ≠ SimpleProc.done → Q ≠ SimpleProc.done → supp (parallel (atomic p (P)) (atomic q (Q)) (by {
      simp [disjoint_atomics hneq]
    })) = {p, q} := by
      intros P Q hp hq
      simp [supp, parallel, atomic, fin.complete]
      apply Finset.ext ; intro name
      simp [fin.complete]
      apply Iff.intro
      {
        intro h
        by_cases h₁ : name = p
        {
          left ; assumption
        }
        {
          have : p ≠ name := by intro c ; exact h₁ c.symm
          simp [this] at h
          right ; exact id h.left.symm
        }
      }
      {
        intro h
        cases h
        {
          rename_i h₂
          simp [h₂, hp]
        }
        {
          rename_i h₂
          simp [h₂, hq, hneq]
        }
      }
    have x := restrict_supp_unchange (parallel (atomic p (SimpleProc.send q P)) (atomic q (SimpleProc.receive p Q)) (by {
      simp [disjoint_atomics hneq]
    }))
    simp [this] at x
    simp [x]
    have : (restrict (parallel (atomic p P) (atomic q Q) (by simp [disjoint_atomics hneq])) {p, q}) = (parallel (atomic p P) (atomic q Q) (by simp [disjoint_atomics hneq])) := by
      funext name
      simp [atomic, parallel, restrict]
      intro h
      simp [not_or] at h
      obtain ⟨h₁, h₂⟩ := h
      by_cases hh : name ∈ supp (atomic p P)
      {
        have : p ≠ name := by intro c ; exact h₁ (id c.symm)
        simp [hh, this]
      }
      {
        have : q ≠ name := by intro c ; exact h₂ (id c.symm)
        simp [this, hh]
      }
    simp [this]
    constructor
    assumption
  }
  | par M₁ M₁' M₂ μ' d₁ d₂ _ ih => {
    have h₁ := SimpleNet.parallel_restrict_distrib M₁ M₂ d₁ (pn μ')
    simp [pn] at h₁
    have h₂ := SimpleNet.parallel_restrict_distrib M₁' M₂ d₂ (pn μ')
    simp [pn] at h₂
    simp [h₁, h₂]
    apply Step.par
    exact ih
  }
