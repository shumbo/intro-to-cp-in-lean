import «IntroToCp».Name
import «IntroToCp».SimpleChoreographies
import «IntroToCp».SimpleProcesses

variable {α : Type} [DecidableEq α] [fin : Fintype α]

-- # Endpoint Projection

-- ## Definition of Endpoint Projection

-- definition 4.1

def process_projection (C : SimpleChor α) (r : α) : SimpleProc α := match C with
  | SimpleChor.done => SimpleProc.done
  | SimpleChor.comm p q C' =>
      if r = p then SimpleProc.send q (process_projection C' r) else
      if r = q then SimpleProc.receive p (process_projection C' r) else
      process_projection C' r

-- example 4.1

#eval process_projection (Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done) Name.buyer

-- definition 4.2

def endpoint_projection (C: SimpleChor α) : SimpleNet α := λ p => process_projection C p

#eval endpoint_projection (Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done) Name.alice

-- ## Correctness of Endpoint Projection

-- ### Completeness

-- lemma 4.8

theorem process_projection.nmem_unchange {C C' : SimpleChor α} {μ : (α × α)} : SimpleChor.Step C μ C' → r ∉ pn μ → process_projection C r = process_projection C' r := by
  intros C_steps r_nmem
  induction C_steps generalizing r with
  | comm p q C' => {
    simp [pn, not_or] at r_nmem
    simp [process_projection, r_nmem]
  }
  | delay C₁ μ' C₂ p q _ _ _ ih => {
    by_cases h₁ : r = p
    {
      simp [process_projection, h₁]
      apply ih
      rw [←h₁]
      exact r_nmem
    }
    by_cases h₂ : r = q
    {
      simp [process_projection, h₂, h₁]
      have : p ≠ q := by rw [←h₂] ; intro c ; exact h₁ (id c.symm)
      simp [this.symm]
      apply ih
      rw [←h₂]
      exact r_nmem
    }
    simp [process_projection, h₁, h₂]
    apply ih
    exact r_nmem
  }

-- lemma


-- lemma 4.9

lemma disjoint_remove₂_atomic₂ (N : SimpleNet α) (p q : α) (proc₁ proc₂ : SimpleProc α) (d: p ≠ q): Disjoint
  (SimpleNet.supp ((N.remove p).remove q))
  (SimpleNet.supp (SimpleNet.parallel
    (SimpleNet.atomic p proc₁)
    (SimpleNet.atomic q proc₂)
    (by {apply SimpleNet.disjoint_atomics; exact d})
  ))
:= by
  intro d
  simp [SimpleNet.supp]
  apply Finset.disjoint_filter.mpr
  simp [fin.complete]
  intro r
  simp [SimpleNet.remove, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic]
  intro h₁ h₂ h₃
  simp [Ne.symm h₁, Ne.symm h₂, h₃]

theorem completeness {C : SimpleChor α} {μ : (α × α)} {C' : SimpleChor α} : SimpleChor.Step C μ C' → SimpleNet.Step (endpoint_projection C) μ (endpoint_projection C') := by
  intros C_steps
  have rem := C_steps
  induction C_steps with
  | comm p q C' => {
    let C : SimpleChor α := p ~> q ; C'

    let C_pq := (SimpleNet.parallel
      (SimpleNet.atomic p (SimpleProc.send q (process_projection C' p)))
      (SimpleNet.atomic q (SimpleProc.receive p (process_projection C' q)))
      (by {
        simp [SimpleNet.supp, SimpleNet.atomic]
        apply Finset.disjoint_filter.mpr
        cases C
        {
          rename_i p q neq
          intro r _ h
          rw [h] at neq
          exact id (Ne.symm neq)
        }
        {
          simp [fin.complete]
          apply Ne.symm
          assumption
        }
      })
    )

    let C_rest := (((endpoint_projection C).remove p).remove q)

    let C₁ := SimpleNet.parallel
      C_rest
      C_pq
      (by {
        simp [SimpleNet.supp, SimpleNet.remove, SimpleNet.atomic, SimpleNet.parallel, fin.complete]
        apply Finset.disjoint_filter.mpr
        simp [fin.complete]
        intros r h₁ h₂ h₃
        simp [Ne.symm h₁]
        exact ne_comm.mpr h₂
      })

    let C'_rest := ((endpoint_projection C').remove p).remove q

    let C₂ := SimpleNet.parallel
      C'_rest
      C_pq
      (by {
        simp [SimpleNet.supp, SimpleNet.remove, SimpleNet.atomic, SimpleNet.parallel, fin.complete]
        apply Finset.disjoint_filter.mpr
        simp [fin.complete]
        intros r h₁ h₂ h₃
        simp [Ne.symm h₁]
        exact ne_comm.mpr h₂
      })

    let C₃ := SimpleNet.parallel
      C'_rest
      (SimpleNet.parallel
        (SimpleNet.atomic p (process_projection C' p))
        (SimpleNet.atomic q (process_projection C' q))
        (by {
          simp [SimpleNet.supp, SimpleNet.atomic, process_projection]
          apply Finset.disjoint_filter.mpr
          simp [fin.complete]
          intro c heq
          have := heq.symm
          contradiction
        })
      )
      (by {
        simp [SimpleNet.supp, SimpleNet.remove, SimpleNet.atomic, SimpleNet.parallel, fin.complete]
        apply Finset.disjoint_filter.mpr
        simp [fin.complete]
        intros r h₁ h₂ h₃
        simp [Ne.symm h₁]
        intro c
        exact (h₂ (id c.symm)).elim
      })

    let C₃' := SimpleNet.parallel
      (SimpleNet.parallel
        (SimpleNet.atomic p (process_projection C' p))
        (SimpleNet.atomic q (process_projection C' q))
        (by {
          simp [SimpleNet.supp, SimpleNet.atomic, process_projection]
          apply Finset.disjoint_filter.mpr
          simp [fin.complete]
          intro c heq
          have := heq.symm
          contradiction
        })
      )
      C'_rest
      (by {
        simp [SimpleNet.supp, SimpleNet.remove, SimpleNet.atomic, SimpleNet.parallel, fin.complete]
        apply Finset.disjoint_filter.mpr
        simp [fin.complete]
        intros r h₁ h₂ h₃
        simp [Ne.symm h₂, Ne.symm h₃] at h₁
      })

    have eq₃ : C₃ = C₃' := by
      apply SimpleNet.comm

    have h₁ : endpoint_projection C = C₁ := by
      funext r
      simp [endpoint_projection, process_projection]
      have neq : p ≠ q := by
        cases C
        assumption
        assumption
      by_cases h₁ : r = p
      {
        simp [h₁, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic, SimpleNet.remove]
      }
      simp [h₁]
      by_cases h₂ : r = q
      {
        simp [h₂, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic, SimpleNet.remove, neq]
      }
      simp [h₂]
      simp [SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.remove, h₁, h₂, SimpleNet.atomic, Ne.symm, h₁, h₂, endpoint_projection, process_projection]
      by_cases h₃: process_projection C' r = SimpleProc.done
      simp [h₃]
      simp [h₃]

    have h₂ : ((endpoint_projection C).remove p).remove q = ((endpoint_projection C').remove p).remove q := by
      funext r
      by_cases c₁ : p = r
      {
        simp [SimpleNet.remove, c₁]
      }
      by_cases c₂ : q = r
      {
        simp [SimpleNet.remove, c₂]
      }
      simp [endpoint_projection]
      have : endpoint_projection C r = endpoint_projection C' r := by
        apply process_projection.nmem_unchange
        {
          apply rem
        }
        {
          simp [pn, not_or]
          apply And.intro
          exact Ne.symm c₁
          exact Ne.symm c₂
        }
      simp at this
      simp [SimpleNet.remove, Ne.symm c₁, Ne.symm c₂]
      exact this

    have h₂' : C₁ = C₂ := by
      simp at h₂
      simp
      funext r
      simp [h₂, SimpleNet.parallel]

    have fst : endpoint_projection C = C₂ := by simp [h₁, h₂']

    let C'_pq_stepped := (SimpleNet.parallel
      (SimpleNet.atomic p (process_projection C' p))
      (SimpleNet.atomic q (process_projection C' q))
      (by {
        simp [SimpleNet.supp, SimpleNet.atomic]
        apply Finset.disjoint_filter.mpr
        simp [fin.complete]
        intro h₁ h₂
        have := h₂.symm
        contradiction
      })
    )

    have h_com : SimpleNet.Step C_pq (p, q) C'_pq_stepped := by
      simp
      apply SimpleNet.Step.comm p q
      assumption

    have : SimpleNet.Step C₂ (p, q) C₃ := by
      rw [eq₃]
      simp
      rw [SimpleNet.comm]
      apply SimpleNet.Step.par
      apply h_com

    rw [←fst] at this

    have lst : C₃ = endpoint_projection C' := by
      funext r
      simp [endpoint_projection, process_projection]
      have : p ≠ q := by assumption
      by_cases h₁ : r = p
      {
        simp [h₁, this.symm, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic, SimpleNet.remove]
        intro x ; exact x.symm
      }
      by_cases h₂ : r = q
      {
        simp [h₂, this, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic, SimpleNet.remove]
      }
      simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂, this.symm, SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.atomic, SimpleNet.remove]
      by_cases c₃ : endpoint_projection C' r = SimpleProc.done
      {
        simp [c₃.symm]
        simp [endpoint_projection]
      }
      {
        simp [c₃, endpoint_projection]
        intro x ; exact x.symm
      }

    rw [←lst]
    assumption
  }
  | delay C₁ μ' C₂ p q neq C₁_steps d ih => {
    let N₂ := SimpleNet.parallel
      (((endpoint_projection C₁).remove p).remove q)
      (SimpleNet.parallel
        (SimpleNet.atomic p (SimpleProc.send q (process_projection C₁ p)))
        (SimpleNet.atomic q (SimpleProc.receive p (process_projection C₁ q)))
        (by {apply SimpleNet.disjoint_atomics; assumption})
      )
      (by {
        apply disjoint_remove₂_atomic₂ ; exact neq
      })
    have h₁ : endpoint_projection (p ~> q ; C₁) = N₂ := by
        funext r
        simp [endpoint_projection, process_projection, SimpleNet.parallel, SimpleNet.supp, SimpleNet.remove, fin.complete, SimpleNet.atomic]
        by_cases c₁ : r = p
        {
          simp [c₁, SimpleNet.atomic]
        }
        by_cases c₂ : r = q
        {
          simp [c₁, c₂, Ne.symm neq, neq]
        }
        simp [c₁, c₂, Ne.symm]
        by_cases c₃ : process_projection C₁ r = SimpleProc.done <;> simp [c₃]
    have := ih C₁_steps
    simp at d
    have h₂ := SimpleNet.step_nmem_step (SimpleNet.step_nmem_step this d.left) d.right

    let N₃ := SimpleNet.parallel
      (((endpoint_projection C₂).remove p).remove q)
      (SimpleNet.parallel
        (SimpleNet.atomic p (SimpleProc.send q (process_projection C₁ p)))
        (SimpleNet.atomic q (SimpleProc.receive p (process_projection C₁ q)))
        (by {apply SimpleNet.disjoint_atomics; assumption})
      )
      (by {
        apply disjoint_remove₂_atomic₂ ; exact neq
      })

    have h₂' : SimpleNet.Step N₂ μ' N₃ := by
      simp
      apply SimpleNet.Step.par
      exact h₂

    clear h₂ this
    have h₃₁ := process_projection.nmem_unchange rem d.left
    have h₃₂ := process_projection.nmem_unchange rem d.right

    have h₄ : SimpleNet.parallel
      (((endpoint_projection C₂).remove p).remove q)
      (SimpleNet.parallel
        (SimpleNet.atomic p (process_projection (p ~> q ; C₂) p))
        (SimpleNet.atomic q (process_projection (p ~> q ; C₂) q))
        (by {apply SimpleNet.disjoint_atomics; exact neq})
      )
      (by {
        apply disjoint_remove₂_atomic₂ ; exact neq
      }) = endpoint_projection (p ~> q ; C₂) := by
      funext r
      simp [endpoint_projection, process_projection]
      by_cases c₁ : r = p
      {
        simp [c₁, SimpleNet.parallel, SimpleNet.remove, SimpleNet.supp, SimpleNet.atomic, fin.complete]
      }
      by_cases c₂ : r = q
      {
        simp [c₂, SimpleNet.parallel, SimpleNet.remove, SimpleNet.supp, SimpleNet.atomic, fin.complete]
        intro c ; contradiction
      }
      simp [SimpleNet.parallel, SimpleNet.supp, fin.complete, SimpleNet.remove, SimpleNet.atomic, c₁, c₂]
      simp [endpoint_projection, process_projection]
      intro h
      simp [Ne.symm c₁, Ne.symm c₂] ; exact h.symm

    rw [h₁, ←h₄, ←h₃₁, ←h₃₂]

    have : (SimpleNet.parallel
      (SimpleNet.remove (SimpleNet.remove (endpoint_projection C₂) p) q)
      (SimpleNet.parallel
        (SimpleNet.atomic p (process_projection (p ~> q ; C₁) p))
        (SimpleNet.atomic q (process_projection (p ~> q ; C₁) q))
        (by {apply SimpleNet.disjoint_atomics; exact neq;})
      )
      (by {apply disjoint_remove₂_atomic₂ ; exact neq})
    ) = N₃ := by
      funext r
      simp [SimpleNet.remove, SimpleNet.parallel, SimpleNet.atomic, SimpleNet.supp, fin.complete]
      by_cases c₁ : r = p
      {
        simp [c₁, process_projection]
      }
      by_cases c₂ : r = q
      {
        simp [c₂, neq, process_projection, Ne.symm neq]
      }
      simp [c₁, c₂, Ne.symm]

    rw [←this] at h₂'
    exact h₂'
  }
