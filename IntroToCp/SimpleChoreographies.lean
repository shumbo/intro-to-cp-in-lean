import Mathlib.Order.Disjoint
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import «IntroToCp».Relation
import «IntroToCp».Name

variable {α : Type} [DecidableEq α] [fin : Fintype α]

-- # Simple Choreographies

-- ## Syntax

inductive SimpleChor (α : Type) where
  | done : SimpleChor α
  | comm (p : α) (q : α) (C : SimpleChor α) : SimpleChor α
deriving Repr, DecidableEq

-- terminated choreography
def SimpleChor.𝕆 : SimpleChor α := SimpleChor.done

notation:10 p " ~> " q " ; " C => SimpleChor.comm p q C

-- Example 2.2
#eval Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done

-- Exercise 2.1
def ringProtocol := Name.alice ~> Name.bob ; Name.bob ~> Name.charlie ; Name.charlie ~> Name.alice ; SimpleChor.done

-- Exercise 2.2
def scatterProtocol := Name.alice ~> Name.bob ; Name.alice ~> Name.charlie ; SimpleChor.done

-- Semantics

def pn (s : α × α) : Finset α := {s.fst, s.snd}

inductive SimpleChor.Step : SimpleChor α → (α × α) → SimpleChor α → Prop where
  | comm : ∀ {p q : α} {C : SimpleChor α}, Step (p ~> q ; C) (p, q) C
  | delay : ∀ {C C': SimpleChor α} {μ : (α × α)}, Step C μ C' → Disjoint {p, q} (pn μ) → Step (p ~> q ; C) μ (p ~> q ; C')

-- Example 2.3
example : SimpleChor.Step
  (Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done)
  (Name.buyer, Name.seller)
  (Name.seller ~> Name.buyer ; SimpleChor.done) := by apply SimpleChor.Step.comm

inductive SimpleChor.MultiStep : SimpleChor α → List (α × α) → SimpleChor α → Prop where
  | rfl : ∀ (C: SimpleChor α), MultiStep C [] C
  | step : ∀ (C: SimpleChor α) (μ : (α × α)) (C' : SimpleChor α) (μ' : List (α × α)) (C'' : SimpleChor α),
      Step C μ C' → MultiStep C' μ' C'' → MultiStep C (μ :: μ') C''

example : SimpleChor.MultiStep
  (Name.p₁ ~> Name.q₁ ; Name.p₂ ~> Name.q₂ ; Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆)
  [(Name.p₁, Name.q₁), (Name.p₂, Name.q₂), (Name.p₃, Name.q₃)]
  SimpleChor.𝕆
:= by
  apply SimpleChor.MultiStep.step _ _ (Name.p₂ ~> Name.q₂ ; Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  apply SimpleChor.MultiStep.step _ _ (Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  apply SimpleChor.MultiStep.step _ _ (SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  apply SimpleChor.MultiStep.rfl
