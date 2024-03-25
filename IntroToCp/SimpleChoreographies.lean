import Mathlib.Data.Set.Lattice
import «IntroToCp».Relation

open Set

-- # Simple Choreographies

-- ## Syntax

structure PName where
  name : String
deriving BEq, DecidableEq

#eval PName.mk "foo" == PName.mk "bar"

-- Coercion from String to PName
instance : Coe String PName :=
  ⟨PName.mk⟩

instance : ToString PName where
  toString := PName.name

instance : Repr PName where
  reprPrec p prec := p.name

#eval ("x" : PName)

def disjoint (a : Set α) (b : Set α) : Prop := ∀ x y, x ∈ a → y ∈ b → x ≠ y

def s₁ : Set Nat := {1, 2, 3}
def s₂ : Set Nat := {4, 5, 6}

example : disjoint s₁ s₂ := by
  simp [disjoint]
  intro x' y' h1 h2
  cases h1 with
  | inl h1 => cases h2 with
    | inl h2 => simp [h1, h2]
    | inr h2 => cases h2 with
      | inl h2 => simp [h1, h2]
      | inr h2 => rw [mem_singleton_iff] at h2
                  simp [h1, h2]
  | inr h1 => cases h2 with
    | inl h2 => cases h1 with
      | inl h1 => simp [h1, h2]
      | inr h1 => rw [mem_singleton_iff] at h1
                  simp [h1, h2]
    | inr h2 => cases h1 with
      | inl h1 => cases h2 with
        | inl h2 => simp [h1, h2]
        | inr h2 => rw [mem_singleton_iff] at h2
                    simp [h1, h2]
      | inr h1 => cases h2 with
        | inl h2 => rw [mem_singleton_iff] at h1
                    simp [h1, h2]
        | inr h2 => rw [mem_singleton_iff] at h1
                    rw [mem_singleton_iff] at h2
                    simp [h1, h2]

inductive SimpleChor : Type where
  | done : SimpleChor
  -- TODO: do I need p ≠ q?
  | comm (p : PName) (q : PName) (C : SimpleChor) : SimpleChor
deriving Repr

-- terminated choreography
def 𝕆 := SimpleChor.done

notation:10 p " ~> " q " ; " C => SimpleChor.comm p q C

-- example 2.2
#eval "buyer" ~> "seller" ; "seller" ~> "buyer" ; 𝕆

-- Exercise 2.1
def ringProtocol := "Alice" ~> "Bob" ; "Bob" ~> "Charlie" ; "Charlie" ~> "Alice" ; 𝕆

-- Exercise 2.2
def scatterProtocol := "Alice" ~> "Bob" ; "Alice" ~> "Charlie" ; 𝕆

def pn (s : PName × PName) : Set PName := {s.fst, s.snd}

#check pn (("Alice", "Bob"))

inductive Transition : SimpleChor → (PName × PName) → SimpleChor → Prop where
  -- p ~> q ; C → ⟨ p, q ⟩ → C
  | comm : ∀ {p q C}, Transition (p ~> q ; C) (p, q) C
  | delay : Transition C μ C' → disjoint {p, q} (pn μ) → Transition (p ~> q; C) μ (p ~> q; C')

-- Example 2.3
example : Transition ("buyer" ~> "seller" ; "seller" ~> "buyer" ; 𝕆) ("buyer", "seller") ("seller" ~> "buyer" ; 𝕆) := by
  apply Transition.comm

-- Exercise 2.3
example : Transition ringProtocol ("Alice", "Bob") ("Bob" ~> "Charlie" ; "Charlie" ~> "Alice" ; 𝕆) := by
  apply Transition.comm
example : Transition ("Bob" ~> "Charlie" ; "Charlie" ~> "Alice" ; 𝕆) ("Bob", "Charlie") ("Charlie" ~> "Alice" ; 𝕆) := by
  apply Transition.comm
example : Transition ("Charlie" ~> "Alice" ; 𝕆) ("Charlie", "Alice") 𝕆 := by
  apply Transition.comm

example : Transition scatterProtocol ("Alice", "Bob") ("Alice" ~> "Charlie" ; 𝕆) := by
  apply Transition.comm
example : Transition ("Alice" ~> "Charlie" ; 𝕆) ("Alice", "Charlie") 𝕆 := by
  apply Transition.comm

-- Example 2.4
example : Transition ("buyer₁" ~> "seller₁" ; "buyer₂" ~> "seller₂" ; 𝕆) ("buyer₂", "seller₂") ("buyer₁" ~> "seller₁" ; 𝕆) := by
  apply Transition.delay
  . apply Transition.comm
  . simp [pn, disjoint]
    intro x y hx hy
    apply hx.elim <;> intro hx
    all_goals (apply hy.elim)
    all_goals intro c hc
    all_goals (simp [*] at * ; contradiction)

-- Example 2.5
example := "p₁" ~> "q₁" ; "p₂" ~> "q₂" ; "p₃" ~> "q₃" ; 𝕆
example : Transition
            ("p₁" ~> "q₁" ; "p₂" ~> "q₂" ; "p₃" ~> "q₃" ; 𝕆)
            ("p₃", "q₃")
            ("p₁" ~> "q₁" ; "p₂" ~> "q₂" ; 𝕆) := by
            apply Transition.delay
            . apply Transition.delay
              . apply Transition.comm
              . simp [disjoint]
                intro p q hp hq
                intro c
                cases hp with
                | inl hp =>
                  cases hq with
                  | inl hq =>
                    simp at hq
                    simp [hp, hq] at c
                    contradiction
                  | inr hq =>
                    simp at hq
                    simp [hp, hq] at c
                    contradiction
                | inr hp =>
                  cases hq with
                  | inl hq =>
                    simp at hq
                    simp [hp, hq] at c
                    contradiction
                  | inr hq =>
                    simp at hq
                    simp [hp, hq] at c
                    contradiction
            . simp [disjoint]
              intro p q hp hq
              intro c
              cases hp with
              | inl hp =>
                cases hq with
                | inl hq =>
                  simp at hq
                  simp [hp, hq] at c
                  contradiction
                | inr hq =>
                  simp at hq
                  simp [hp, hq] at c
                  contradiction
              | inr hp =>
                cases hq with
                | inl hq =>
                  simp at hq
                  simp [hp, hq] at c
                  contradiction
                | inr hq =>
                  simp at hq
                  simp [hp, hq] at c
                  contradiction


-- Exercise 6: theee communications can be done in any order

-- ## 2.3 Conventions, Notation, and Terminology for Labelled Transition Systems

inductive MultiTransition : SimpleChor → List (PName × PName) → SimpleChor → Prop where
  | rfl : ∀ c, MultiTransition c [] c
  | step : ∀ c μ c' μ' c'',
      Transition c μ c' → MultiTransition c' μ' c'' → MultiTransition c (μ::μ') c''

example : MultiTransition ("p₁" ~> "q₁" ; "p₂" ~> "q₂" ; "p₃" ~> "q₃" ; 𝕆) [("p₁", "q₁"), ("p₂", "q₂"), ("p₃", "q₃")] 𝕆 := by
  apply MultiTransition.step _ _ ("p₂" ~> "q₂" ; "p₃" ~> "q₃" ; 𝕆)
  constructor
  apply MultiTransition.step _ _ ("p₃" ~> "q₃" ; 𝕆)
  constructor
  apply MultiTransition.step _ _ 𝕆
  constructor
  apply MultiTransition.rfl
