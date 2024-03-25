def Relation (α : Type) : Type := α → α → Prop
inductive Relation.Multi {α : Type} (R : Relation α) : Relation α where
  | rfl : ∀ (a : α), Multi R a a
  | step : ∀ (x y z : α),
            R x y → Multi R y z → Multi R x z
