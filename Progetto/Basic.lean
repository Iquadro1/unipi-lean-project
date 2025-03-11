--import Mathlib.Data.Set.Finite.Basic
--import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.PGroup
/-- If `s` is a subset of `t` and `t` is finite, then the cardinality of `s` is less than or equal to the cardinality of `t`-/
theorem Set.Finite.card_le_card {α : Type*} {s t : Set α} (ht : t.Finite) (hsub : s ⊆ t) : Nat.card s ≤ Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht hsub)
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_le_card hsub

/-- The cardinality of the union of two disjoint finite sets is the sum of the cardinalities of the sets-/
theorem Set.Finite.card_union_of_disjoint {α : Type*} {s t : Set α} [DecidableEq α] (ht : t.Finite) (hs : s.Finite) (hd : Disjoint s t) : Nat.card ((s ∪ t) : Set α) = Nat.card s + Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype hs
  simp only [Nat.card_eq_card_toFinset]
  rw [toFinset_union]
  apply Finset.card_union_of_disjoint
  exact Set.disjoint_toFinset.mpr hd
