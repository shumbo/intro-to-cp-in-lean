-- Total Maps

def TotalMap (α : Type) := String → α

namespace TotalMap

def empty {α : Type} (v : α) : TotalMap α := λ _ => v
def update {α : Type} (m : TotalMap α) (x : String) (v : α) :=
  λ x' => if x == x' then v else m x'

notation:30 "_" " !-> " v => empty v

#check _ !-> false

notation:30 x " !-> " v ";" m => update m x v
#eval ("bar" !-> true ; _ !-> false) "x"

-- t_apply_empty
def apply_empty : ∀ α: Type, ∀ v : α, ∀ x : String, ((empty v) x) = v := by
  intro α v _
  rfl

-- update_eq
def update_eq : ∀ (α : Type) (m : TotalMap α) x v, (x !-> v ; m) x = v := by
  intro α m x v
  rw [update]
  simp

-- update_neq
def update_neq : ∀ (α : Type) (m : TotalMap α) x₁ x₂ v,
  x₁ ≠ x₂ → (x₁ !-> v; m) x₂ = m x₂ := by
    intro α m x₁ x₂ v h
    rw [update]
    simp [h]

#check ("x" !-> true ; "x" !-> false ; empty true)

-- update_shadow
def update_shadow : ∀ (α : Type) (m : TotalMap α) x v₁ v₂,
  (x !-> v₂ ;( x !-> v₁ ; m)) = (x !-> v₂ ; m) := by
  intros α m x v₁ v₂
  funext x'
  by_cases (x = x')
  . rename_i xeq
    repeat rewrite [update]
    simp [xeq]
  . rename_i xneq
    rw [update, update, update]
    simp [xneq]

-- update_same
def update_same : ∀ (α : Type) (m : TotalMap α) x,
  (x !-> m x ; m) = m := by
    intros α m x
    funext x'
    by_cases (x = x')
    . rename_i xeq
      rewrite [update]
      simp [xeq]
    . rename_i xneq
      rewrite [update]
      simp [xneq]

end TotalMap

-- Partial Maps

def PartialMap (α β: Type) [DecidableEq α] := α → Option β

namespace PartialMap
open Option

def empty {α β : Type} [DecidableEq α] : PartialMap α β := λ _ => none

@[reducible, simp]
def update {α β: Type} [DecidableEq α] (m : PartialMap α β) (x : α) (v : β) :=
  λ x' => if x = x' then some v else m x'

notation:30 x " |-> " v ";" m => update m x v
notation:30 x " |-> " v => update (empty) x v

-- theorem apply_empty : ∀ (α : Type) (x : String), (empty : PartialMap α) x = none := by
--   intros α x
--   rewrite [empty]
--   rfl

-- theorem update_eq : ∀ (α : Type) (m : PartialMap α) x v,
--   (x |-> v ; m) x = some v := by
--   intros α m x v
--   rewrite [update]
--   simp

-- theorem update_neq : ∀ (α : Type) (m : PartialMap α) x₁ x₂ v,
--   x₂ ≠ x₁ → (x₂ |-> v; m) x₁ = m x₁ := by
--     intros α m x₁ x₂ v hneq
--     rewrite [update]
--     simp [hneq]

-- theorem update_shadow : ∀ (α : Type) (m : PartialMap α) x v₁ v₂,
--   (x |-> v₂ ;( x |-> v₁ ; m)) = (x |-> v₂ ; m) := by
--   intros α m x v₁ v₂
--   funext x'
--   by_cases (x = x')
--   . rename_i xeq
--     repeat rewrite [update]
--     simp [xeq]
--   . rename_i xneq
--     rewrite [update, update, update]
--     simp [xneq]

-- theorem update_same : ∀ (α : Type) (m : PartialMap α) x v,
--   m x = some v → (x |-> v ; m) = m := by
--     intros α m x v h
--     funext x'
--     rewrite [update]
--     by_cases (x = x')
--     . rename_i xeq
--       simp [xeq]
--       rewrite [←h, xeq]
--       rfl
--     . rename_i xneq
--       simp [xneq]

-- theorem update_permute : ∀ (α : Type) (m : PartialMap α) x₁ x₂ v₁ v₂,
--   x₁ ≠ x₂ → (x₁ |-> v₁ ; x₂ |-> v₂ ; m) = (x₂ |-> v₂ ; x₁ |-> v₁ ; m) := by
--     intros α m x₁ x₂ v₁ v₂ hneq
--     funext x'
--     rewrite [update, update, update, update]
--     simp
--     by_cases (x₁ = x')
--     . rename_i heq
--       simp [heq]
--       have : x₂ ≠ x' := by
--         rw [←heq]; intro h
--         have : x₁ = x₂ := by rw [Eq.symm h]
--         contradiction
--       rw [heq] at hneq
--       simp [*]
--     . rename_i h
--       simp [*]

-- -- all entries in m are also present in m'
-- def includedin {α : Type} (m m' : PartialMap α) :=
--   ∀ x v, m x = some v → m' x = some v

-- theorem includedin_update : ∀ {α : Type} (m m' : PartialMap α) (x : String) (vx : α),
--   includedin m m' → includedin (x |-> vx ; m) (x |-> vx ; m') := by
--     intros α m m' x vx h
--     intro k v h2
--     rw [update] at h2
--     by_cases (x = k)
--     . rename_i heq
--       simp [heq] at h2
--       rw [update]
--       simp [heq]
--       assumption
--     . rename_i hneq
--       simp [hneq] at h2
--       rw [includedin] at h
--       have := h k v
--       have := this h2
--       rw [update]
--       simp [hneq]
--       assumption

end PartialMap
