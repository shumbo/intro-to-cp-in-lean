-- # 1. Inference Systems

-- ## 1.1 Example: Modeling Flight Connections with Inference Rules

namespace Fig1_2

-- ### 1.1.1 Expressing a Connected Graph with Axioms

-- define city
inductive City where
| odense
| rome
| sydney
| tokyo
| nyc

open City

-- axioms
inductive Conn : City → City → Prop where
| or : Conn odense rome
| rs : Conn rome sydney
| st : Conn sydney tokyo
| tn : Conn tokyo nyc
| nr : Conn nyc rome

-- ### 1.1.2 Schematic Variables
section

-- Define the Walk type with two constructors
inductive Walk : City → City → Prop where
| dir {A B : City} : Conn A B → Walk A B
| comp {A B C : City} : Walk A B → Walk B C → Walk A C

end

-- ## 1.2 Derivations

-- ### 1.2.1 Combining Rules

-- there is a walk from odense to rome with two rules
example : Walk City.odense City.rome := by
  apply Walk.dir
  exact Conn.or

-- ### 1.2.2 Derivations as Trees

example : Walk City.odense City.sydney := by
  -- can't prove this with dir
  apply Walk.dir
  admit

example : Walk odense sydney := by
  apply Walk.comp
  . apply Walk.dir
    exact Conn.or
  . apply Walk.dir
    exact Conn.rs

-- size: the number of nodes in the derivation
-- height: the number of nodes in the longest path from root to leaf

-- ### 1.2.3 Searching for Derivations

example : Walk nyc tokyo := by
  apply Walk.comp
  . apply Walk.dir
    apply Conn.nr
  . apply Walk.comp
    . apply Walk.dir
      apply Conn.rs
    . apply Walk.dir
      apply Conn.st

-- Exercise 1.1

example : Walk nyc sydney := by
  apply Walk.comp
  . apply Walk.dir
    exact Conn.nr
  . apply Walk.dir
    exact Conn.rs

-- Exercise 1.2

example : Walk odense sydney → Walk odense nyc := by
  intro h
  apply Walk.comp
  . exact h
  . apply Walk.comp
    . apply Walk.dir
      exact Conn.st
    . apply Walk.dir
      exact Conn.tn

-- Exercise 1.3

example : Walk nyc nyc := by
  apply Walk.comp
  . apply Walk.dir
    exact Conn.nr
  . apply Walk.comp
    . apply Walk.dir
      exact Conn.rs
    . apply Walk.comp
      . apply Walk.dir
        exact Conn.st
      . apply Walk.dir
        exact Conn.tn

end Fig1_2

-- ### 1.2.5 Subderivations

namespace Fig1_3

inductive City where
| odense
| rome
| sydney
| tokyo
| nyc

open City

inductive Conn : City → City → Prop where
| or : Conn odense rome
| rs : Conn rome sydney
| st : Conn sydney tokyo
| tn : Conn tokyo nyc
| nr : Conn nyc rome
-- new rule
| sym {A B : City} : Conn A B → Conn B A

inductive Walk : City → City → Prop where
| dir {A B : City} : Conn A B → Walk A B
| comp {A B C : City} : Walk A B → Walk B C → Walk A C

-- Exercise 1.4
example : Walk odense odense := by
  apply Walk.comp
  . apply Walk.dir
    exact Conn.or
  . apply Walk.dir
    apply Conn.sym
    exact Conn.or

-- Exercise 1.5
example : ∀ A : City, Walk A A := by
  intro A
  -- then you can go and come back
  have : ∃ B, Conn A B := by
    cases A
    . exact ⟨rome, Conn.or⟩
    . exact ⟨sydney, Conn.rs⟩
    . exact ⟨tokyo, Conn.st⟩
    . exact ⟨nyc, Conn.tn⟩
    . exact ⟨rome, Conn.nr⟩
  apply this.elim
  intro B hB
  have : Conn B A := by apply Conn.sym; assumption
  apply Walk.comp
  . apply Walk.dir
    assumption
  . apply Walk.dir
    assumption

end Fig1_3

-- ## 1.3 Underivable Propositions

namespace Fig1_2

  example : ¬ (Conn City.odense City.nyc) := by
    intro c
    cases c

end Fig1_2

-- ## 1.4 Admissible and Derivable Rules

namespace Fig1_6

  inductive City where
  | odense
  | rome
  | sydney
  | tokyo
  | nyc

  inductive Conn : City → City → Prop where
  | or : Conn odense rome
  | rs : Conn rome sydney
  | st : Conn sydney tokyo
  | tn : Conn tokyo nyc
  | nr : Conn nyc rome

  inductive Walk : City → City → Prop where
  | dir {A B : City} : Conn A B → Walk A B
  | step {A B C : City} : Conn A B → Walk B C → Walk A C

  open City

  example : Walk odense sydney := by
    apply Walk.step
    . apply Conn.or
    . apply Walk.dir
      apply Conn.rs
    . exact rome

end Fig1_6

-- Exercise 1.11
namespace Fig1_6

  open City
  example : Walk sydney nyc := by
    apply Walk.step
    . apply Conn.st
    . apply Walk.dir
      apply Conn.tn
    . exact tokyo

end Fig1_6

-- Exercise 1.12
namespace Fig1_2

  open City
  example : ∀ A B C : City, Walk A B → Conn B C → Walk A C := by
    intros A B C wAB cBC
    apply Walk.comp
    . apply wAB
    . apply Walk.dir
      exact cBC

-- Exercise 1.13

  example : ∀ A B C D : City, Walk A B → Walk B C → Walk C D → Walk A D := by
    intros A B C D wAB wBC wCD
    apply Walk.comp
    . exact wAB
    . apply Walk.comp
      . exact wBC
      . exact wCD

end Fig1_2

-- Proposition 1.7

namespace Fig1_6

  open City
  example : Walk A B → Walk B C → Walk A C := by
    intros wAB wBC
    induction wAB with
    | dir x =>
      apply Walk.step
      . exact x
      . exact wBC
    | step cAB _ ih =>
      apply Walk.step
      . exact cAB
      . exact (ih wBC)

-- Exercise 1.15

  example : Walk A B → Conn B C → Walk A C := by
    intros wAB cBC
    induction wAB with
    | dir c =>
        apply Walk.step
        . exact c
        . apply Walk.dir
          assumption
    | step cAB _ ih =>
        apply Walk.step
        . exact cAB
        . exact (ih cBC)

end Fig1_6
