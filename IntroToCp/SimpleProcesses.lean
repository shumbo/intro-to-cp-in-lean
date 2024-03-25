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

structure SimpNet (α : Type) [DecidableEq α] where
  names : Finset α
  processes (n : α) : Option (SimpleProc (α := α))
  h : ∀ n : α, n ∈ names → Option.isSome (processes n)

def SimpNet.empty {α : Type} [DecidableEq α] : SimpNet α := SimpNet.mk
  Finset.empty
  (λ _ => Option.none)
  (λ n h => by cases h)

@[simp]
def SimpNet.update {α : Type} [DecidableEq α] (N : SimpNet α) (name : α) (proc : SimpleProc (α := α)) : SimpNet α := SimpNet.mk
  (insert name N.names)
  (λ n => if n = name then proc else N.processes n)
  (by
    intros n h
    by_cases n = name
    {
      simp [*]
    }
    {
      rename_i n_neq_name
      have := Finset.mem_of_mem_insert_of_ne h n_neq_name
      simp [n_neq_name]
      have := N.h n this
      exact this
    }
  )

@[simp]
def SimpNet.get {α : Type} [DecidableEq α] (N : SimpNet α) (name : α) (mem : name ∈ N.names) : SimpleProc (α := α) :=
  if h : Option.isSome (N.processes name) then
    (N.processes name).get h
  else by
    have := N.h name mem
    contradiction



@[simp]
def Alice : PName := "Alice"
@[simp]
def Bob : PName := "Bob"

def supp {α : Type} [DecidableEq α] (N : SimpNet α) : Finset α := N.names.filter (λ p => if h : p ∈ N.names then N.get p h ≠ SimpleProc.done else false)

@[simp]
def sn : SimpNet Name := (SimpNet.empty.update
  Name.alice (SimpleProc.send Name.bob SimpleProc.done)
  ).update Name.bob SimpleProc.done

example : Name.alice ∈ (supp sn) := by
  simp [supp, SimpNet.update, SimpNet.get]

example : Name.bob ∉ (supp sn) := by
  intro c
  simp [supp, SimpNet.update, SimpNet.get] at c


theorem SimpNet.supp_subset {α : Type} [DecidableEq α] (N : SimpNet α) : supp N ⊆ N.names := by
  simp [supp]

theorem SimpNet.mem_supp_mem {α : Type} [DecidableEq α] {a : α} (N: SimpNet α) : (a ∈ supp N) → a ∈ N.names := by
  intro h
  have := SimpNet.supp_subset N
  exact Finset.mem_of_subset this h


def SimpNet.parallel {α : Type} [DecidableEq α] (N M : SimpNet α) (h : Disjoint (supp N) (supp M)) : SimpNet α := SimpNet.mk
  ((supp N) ∪ (supp M))
  (λ n => if n ∈ supp N then N.processes n else if n ∈ supp M then M.processes n else none)
  (by
    intro n n_mem
    have := Finset.mem_union.mp n_mem
    cases this
    {
      rename_i n_in_N
      simp [n_in_N]
      have := SimpNet.supp_subset N
      have := Finset.mem_of_subset this n_in_N
      exact N.h n this
    }
    {
      rename_i n_in_M
      simp [n_in_M]
      have : n ∉ supp N := by
        intro c
        have := Finset.disjoint_iff_ne.mp h n c n n_in_M
        contradiction
      by_cases n ∈ N.names
      {
        simp [this]
        have := M.h n
        apply this
        apply SimpNet.mem_supp_mem
        assumption
      }
      {
        simp [this]
        have := SimpNet.supp_subset M
        have := Finset.mem_of_subset this n_in_M
        exact M.h n this
      }
    }
  )

example : SimpNet Name := SimpNet.parallel
  SimpNet.empty
  SimpNet.empty
  (by
    simp [supp, SimpNet.empty, Finset.empty]
  )

example : SimpNet Name := SimpNet.parallel
  (SimpNet.empty.update Name.buyer (SimpleProc.send Name.seller (SimpleProc.receive Name.seller SimpleProc.done)))
  (SimpNet.empty.update Name.bob (SimpleProc.receive Name.buyer (SimpleProc.send Name.buyer SimpleProc.done)))
  (by
    simp [supp, SimpNet.empty, Finset.empty]
  )

-- Proposition 3.2

theorem Finset.disjoint_mem {α : Type u} (a : α) {s : Finset α} {t : Finset α} {h : Disjoint s t} : a ∈ s → a ∉ t := by
  intro a_in_s
  have := Finset.disjoint_left.mp h
  apply this
  assumption

theorem SimpNet.mem_supp_get_proc {α : Type} [DecidableEq α] (N : SimpNet α) : ∀ (n : α) (h : n ∈ supp N), N.get n (SimpNet.supp_subset N h) ≠ SimpleProc.done := by
  intros n n_in_supp_N
  simp [supp] at n_in_supp_N
  let ⟨n_in_N, n_not_done⟩ := n_in_supp_N
  simp [n_in_N] at n_not_done
  have := N.h n n_in_N
  simp [this] at n_not_done
  unfold get
  simp [this]
  assumption

theorem SimpNet.supp_parallel_supp_union {α : Type} [DecidableEq α]: ∀ (N M : SimpNet α) (h : Disjoint (supp N) (supp M)), supp (parallel N M h) = supp N ∪ supp M := by
  intros N M h
  apply Finset.ext
  intro n
  constructor
  {
    intro n_mem_supp_par
    have p := SimpNet.supp_subset (parallel N M h)
    have : (parallel N M h).names = supp N ∪ supp M := by
      simp [supp, SimpNet.parallel]
    rw [this] at p
    exact Finset.mem_of_subset p n_mem_supp_par
  }
  {
    intro n_mem_supp_union
    have := Finset.mem_union.mp n_mem_supp_union
    cases this
    {
      -- n ∈ supp N
      rename_i n_mem_supp_N
      have := Finset.disjoint_left.mp h n_mem_supp_N
      have p₁: (parallel N M h).processes n = N.processes n := by
        simp [parallel]
        intro h
        have := Finset.mem_of_subset (SimpNet.supp_subset N) n_mem_supp_N
        contradiction
      have n_in_N : n ∈ N.names := by
        have := SimpNet.supp_subset N
        exact Finset.mem_of_subset this n_mem_supp_N
      have n_not_done : N.get n n_in_N ≠ SimpleProc.done := by
        apply SimpNet.mem_supp_get_proc
        assumption
      simp [supp, n_in_N, p₁]
      have : n ∈ (parallel N M h).names := by
        unfold parallel
        simp
        apply Or.inl
        exact n_mem_supp_N
      constructor
      {
        assumption
      }
      {
        simp [this]
        intro c
        have h₂ : Option.isSome (N.processes n) := by
          apply N.h n n_in_N
        simp [h₂] at c
        unfold get at n_not_done
        simp [h₂] at n_not_done
        contradiction
      }
    }
    {
      -- n ∈ supp M
      rename_i n_mem_supp_M
      have n_not_mem_supp_N := Finset.disjoint_right.mp h n_mem_supp_M
      have p₁: (parallel N M h).processes n = M.processes n := by
        rw [parallel]
        simp [n_mem_supp_M]
        intro h
        contradiction
      have n_in_M : n ∈ M.names := by apply SimpNet.mem_supp_mem ; assumption
      have n_not_done : M.get n n_in_M ≠ SimpleProc.done := by
        apply SimpNet.mem_supp_get_proc
        assumption
      simp [supp, n_in_M, p₁]
      constructor
      {
        assumption
      }
      {
        have : n ∈ (parallel N M h).names := by
          unfold parallel
          simp
          apply Or.inr
          assumption
        simp [this]
        intro c
        have h₂ : Option.isSome (M.processes n) := by apply M.h n n_in_M
        simp [h₂] at c
        unfold get at n_not_done
        simp [h₂] at n_not_done
        contradiction
      }
    }
  }

def sn' : SimpNet Name := (SimpNet.empty.update
  Name.bob SimpleProc.done
  ).update Name.alice (SimpleProc.send Name.bob SimpleProc.done)

example : sn = sn' := by
  unfold sn
  unfold sn'
  simp
  constructor
  {
    apply Finset.Insert.comm
  }
  {
    funext n
    by_cases n = Name.bob
    {
      rename_i n_is_bob
      simp [n_is_bob]
    }
    {
      rename_i n_is_not_bob
      simp [n_is_not_bob]
    }
  }

theorem SimpNet.empty_supp_empty {α : Type} [DecidableEq α] : supp SimpNet.empty (α := α) = Finset.empty := by
  unfold supp
  unfold SimpNet.empty
  simp
  apply Finset.filter_empty
