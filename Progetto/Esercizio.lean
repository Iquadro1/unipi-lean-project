import Mathlib.Data.SetLike.Fintype
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.ArchimedeanDensely

open Nat
open Subgroup

variable {G : Type*} {p : Nat}

lemma G_finite (h : Nat.card G = p ^ 4) (pp : p.Prime) : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_iff_zero_lt.mpr (h.symm ▸ Nat.pos_pow_of_pos 4 (Nat.Prime.pos pp)))

variable [Group G]

lemma G_p_group (h : Nat.card G = p ^ 4): IsPGroup p G := IsPGroup.of_card h

lemma G_nontrivial (h : Nat.card G = p ^ 4) (pp : p.Prime) : Nontrivial G := by
  apply (@IsPGroup.nontrivial_iff_card _ _ _  (G_p_group h) ⟨pp⟩ (G_finite h pp)).mpr
  use 4, by norm_num, h

lemma center_finite (h : Nat.card G = p ^ 4) (pp : p.Prime): Finite (Subgroup.center G) := by
  apply @Subtype.finite _ (G_finite h pp)

lemma p3_quotient_not_cyclic (pp : p.Prime) (h : Nat.card G = p ^ 4) (h' : Nat.card (Subgroup.center G) = p ^ 3) : ¬ IsCyclic (G ⧸ (Subgroup.center G)) := by
  by_contra h''

  have G_not_comm : ¬ ∀ (a b : G), a * b = b * a:= by
    intro h''
    have center_all_G : Subgroup.center G = ⊤ := by
      ext g
      apply Iff.trans (Subgroup.mem_center_iff)
      exact Iff.symm ((fun (ha : ∀ z : G, z * g = g * z) ↦ (iff_true_right ha).mpr) (fun g_1 ↦ h'' g_1 g) trivial)
    have : Nat.card (Subgroup.center G) = p ^ 4 := by
      rw [center_all_G]
      exact (h ▸ Subgroup.card_top)
    have : Nat.card (Subgroup.center G) ≠ Nat.card (Subgroup.center G) := by
      nth_rw 1 [h', this]
      exact Nat.ne_of_lt (Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pp) (by norm_num))
    contradiction

  have G_comm (a b : G) : a * b = b * a := by
    apply commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center G))
    rw [QuotientGroup.ker_mk']
  contradiction

lemma p3_quotient_contradiction (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h3_eq : Nat.card ↥(Subgroup.center G) = p ^ 3) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card ↥H = p ^ 3 := by
  have : Nat.card (G ⧸ Subgroup.center G) = Nat.card G / Nat.card (Subgroup.center G) := by
      apply Nat.eq_div_of_mul_eq_right
      · rw [h3_eq]; norm_num; exact Nat.Prime.ne_zero pp
      rw [← (Subgroup.center G).index_eq_card,mul_comm, (Subgroup.center G).index_mul_card]
  have : IsCyclic (G ⧸ Subgroup.center G) := by
    have : Nat.card (G ⧸ Subgroup.center G) = p := by
      rw [this, h, h3_eq, Nat.pow_div (by norm_num) (Nat.Prime.pos pp)]
      norm_num
    apply @isCyclic_of_prime_card _ _ _ ⟨pp⟩ this
  exfalso
  exact (p3_quotient_not_cyclic pp h h3_eq this)

instance p4_G_comm_group [Finite G] (h : Nat.card G = p ^ 4) (h4_eq : Nat.card ↥(Subgroup.center G) = p ^ 4) : CommGroup G := by
  apply Group.commGroupOfCenterEqTop
  have : Nat.card (Subgroup.center G) = Nat.card G := by
    rw [h4_eq, h]
  apply (Subgroup.card_eq_iff_eq_top (Subgroup.center G)).mp this

lemma p4_quotient (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h4_eq : Nat.card ↥(Subgroup.center G) = p ^ 4) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card ↥H = p ^ 3 := by
  have : p^3 ≤ Nat.card G := by
    rw [h]
    exact Nat.pow_le_pow_of_le_right (Nat.Prime.one_le pp) (by norm_num)
  rcases Sylow.exists_subgroup_card_pow_prime_of_le_card pp (G_p_group h) this with ⟨H, h_eq⟩

  have : H.IsCommutative := by
    apply @Subgroup.commGroup_isCommutative _ (@p4_G_comm_group _ _ _ (G_finite h pp) h h4_eq) H
  use H, this , h_eq

lemma exists_diff_if_card [Finite G] (H : Subgroup G) (h : Nat.card H < Nat.card G) : ∃ g : G, g ∉ H := by
  refine not_forall.mp ?_
  by_contra h'
  have : H = ⊤ := by

    ext g
    exact (iff_true_right trivial).mpr (h' g)
  have : Nat.card G = Nat.card H := by

    exact ((Subgroup.card_eq_iff_eq_top H).mpr this).symm

  linarith

lemma card_center_le_centr [Finite G] (g : G) (h' : g ∉ Subgroup.center G) : Nat.card (Subgroup.center G) < Nat.card (Subgroup.centralizer {g}) := by
  have gin : g ∈ Subgroup.centralizer {g} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have : Nat.card (Subgroup.center G) ≤ Nat.card (Subgroup.centralizer {g}) := Subgroup.card_le_of_le (Subgroup.center_le_centralizer {g})

  have : (Subgroup.center G).carrier ⊂ (Subgroup.centralizer {g}).carrier := by
    exact HasSubset.Subset.ssubset_of_not_subset (Subgroup.center_le_centralizer {g}) fun a ↦ h' (a gin)

  apply Set.Finite.card_lt_card Subtype.finite this

lemma closure_center_g_iscomm {g : G} : (Subgroup.closure ({g} ∪ Subgroup.center G)).IsCommutative := by
  refine { is_comm := ?_ }
  refine { comm := ?_ }
  intro ⟨a, ha⟩ ⟨b, hb⟩
  simp

  induction ha, hb using Subgroup.closure_induction₂ with
  | mem x y hx hy =>
    rcases (Set.mem_union x {g} (Subgroup.center G)).mp hx with ⟨hx | hx⟩ | hx
    · rcases (Set.mem_union y {g} (Subgroup.center G)).mp hy with ⟨hy | hy⟩ | hy
      · rfl
      exact Subgroup.mem_center_iff.mp hy g
    · exact Eq.symm (Subgroup.mem_center_iff.mp hx y)
  | one_left x hx => group
  | one_right x hx => group
  | mul_left x y z hx hy hz hxz hyz => rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc]
  | mul_right y z x hy hz hx hxy hxz => rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]
  | inv_left x y hx hy hxy =>
    calc
      x⁻¹ * y = x⁻¹ * (y * x * x⁻¹) := by group
      _ = x⁻¹ * (x * y * x⁻¹) := by rw [hxy]
      _ = y * x⁻¹ := by group
  | inv_right x y hx hy hxy =>
    calc
      x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
      _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hxy]
      _ = y⁻¹ * x := by group

theorem Set.Finite.card_le_card {s t : Set α} (ht : t.Finite) (hsub : s ⊆ t) : Nat.card s ≤ Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht hsub)
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_le_card hsub

lemma le_card_closure [Finite G] {g : G} : Nat.card (({g} ∪ (Subgroup.center G)) : Set G) ≤ Nat.card (Subgroup.closure ({g} ∪ (Subgroup.center G))) := Set.Finite.card_le_card Subtype.finite Subgroup.subset_closure

open Classical

theorem Set.Finite.card_union_of_disjoint {s t : Set α} (ht : t.Finite) (hs : s.Finite) (hd : Disjoint s t) : Nat.card ((s ∪ t) : Set α) = Nat.card s + Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype hs
  simp only [Nat.card_eq_card_toFinset]
  rw [toFinset_union]
  apply Finset.card_union_of_disjoint
  exact Set.disjoint_toFinset.mpr hd

lemma card_closure [Finite G] (pp : p.Prime) (h : Nat.card G = p ^ 4) (h' : Nat.card (Subgroup.center G) = p ^ k) {g : G} (gnin : g ∉ Subgroup.center G) : p ^ (k + 1) ≤ Nat.card (Subgroup.closure ({g} ∪ Subgroup.center G)) := by

  have : p ^ k < Nat.card (({g} ∪ Subgroup.center G) : Set G) := by
    rw [← h']
    have : ((Subgroup.center G) : Set G).Finite := by
      exact Set.toFinite (Subgroup.center G).carrier
    rw [Set.Finite.card_union_of_disjoint this (Set.finite_singleton g) (Set.disjoint_singleton_left.mpr gnin)]
    apply Nat.lt_add_of_pos_left Nat.card_pos
  have : p ^ k < Nat.card (Subgroup.closure ({g} ∪ Subgroup.center G)) := Nat.lt_of_lt_of_le this le_card_closure
  rcases (Nat.dvd_prime_pow (pp)).mp (h ▸ Subgroup.card_subgroup_dvd_card (Subgroup.closure ({g} ∪ Subgroup.center G))) with ⟨j, hj, hj_eq⟩
  have : k < j := by
    apply (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt pp)).mp (hj_eq ▸ this)
  apply Nat.add_one_le_iff.mpr at this
  rw [hj_eq]
  apply (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mpr this

instance commgroup_if_top_comm (h : (⊤ : Subgroup G).IsCommutative) : ∀ (a b : G), a * b = b * a := by
  exact fun a b ↦ mul_comm_of_mem_isCommutative ⊤ trivial trivial

lemma p2_card_closure_center_g [Finite G] (h : Nat.card G = p^4) (pp : Nat.Prime p) (h2_eq : Nat.card ↥(Subgroup.center G) = p ^ 2) {g : G} (gnin : g ∉ Subgroup.center G) : Nat.card (Subgroup.closure ({g} ∪ Subgroup.center G)) = p ^ 3 := by
  have : Nat.card (Subgroup.closure ({g} ∪ Subgroup.center G)) ∣ p ^ 4 := by
      apply h.symm ▸ Subgroup.card_subgroup_dvd_card (Subgroup.closure ({g} ∪ Subgroup.center G))
  rcases (Nat.dvd_prime_pow (pp)).mp this with ⟨k, hk, hk_eq⟩
  have : 3 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp (hk_eq ▸ card_closure pp h h2_eq gnin)
  interval_cases k using this, hk
  · exact hk_eq
  exfalso
  have : Subgroup.closure ({g} ∪ Subgroup.center G) = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top (Subgroup.closure ({g} ∪ Subgroup.center G))).mp ?_
    rw [hk_eq, h]
  have : (⊤ : Subgroup G).IsCommutative := (this.symm ▸ closure_center_g_iscomm)

  have := commgroup_if_top_comm this
  have : g ∈ (Subgroup.center G ) := by
    apply Subgroup.mem_center_iff.mpr (fun g_1 ↦ this g_1 g)
  contradiction

lemma p2_quotient (h : Nat.card G = p ^ 4) (pp : p.Prime) (h2_eq : Nat.card ↥(center G) = p ^ 2) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card ↥H = p ^ 3 := by
  have : Nat.card (Subgroup.center G) < Nat.card G := h2_eq ▸ h ▸ Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pp) (by norm_num)
  obtain ⟨g, gnin⟩ := @exists_diff_if_card _ _ (G_finite h pp) (Subgroup.center G) this
  use Subgroup.closure ({g} ∪ Subgroup.center G), closure_center_g_iscomm , (@p2_card_closure_center_g _ _ _ (G_finite h pp) h pp h2_eq _ gnin)

lemma p1_card_centr_p2_p3 [Finite G] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(Subgroup.center G) = p ^ 1) (g : G) (h' : g ∉ Subgroup.center G) : Nat.card (Subgroup.centralizer {g}) = p ^ 2 ∨ Nat.card (Subgroup.centralizer {g}) = p ^ 3 := by
  have h_centr : Nat.card (Subgroup.centralizer {g}) ∣ p ^ 4 := by
    apply h.symm ▸ Subgroup.card_subgroup_dvd_card (Subgroup.centralizer {g})
  rcases (Nat.dvd_prime_pow (pp)).mp h_centr with ⟨k, hk, hk_eq⟩
  have := h1_eq ▸ (card_center_le_centr g h')
  have k_gt_1 : 1 < k := by
    rw [hk_eq] at this
    apply (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt pp)).mp this
  have : Nat.card (Subgroup.centralizer {g}) < p ^ 4 := by
    by_contra h''
    have : Subgroup.centralizer {g} = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (Subgroup.centralizer {g})).mp ?_
      rw [hk_eq, h]
      push_neg at h''
      apply Nat.le_iff_lt_or_eq.mp at h''
      rcases h'' with (h'' | h'')
      · apply (Nat.le_of_dvd (Nat.pow_pos (Nat.Prime.pos pp)))at h_centr
        rw [hk_eq] at h_centr h''
        linarith
      · rw [← hk_eq, h'']
    have := (Subgroup.centralizer_eq_top_iff_subset).mp this
    have : g ∈ Subgroup.center G := this rfl
    contradiction
  have k_lt_4 : k < 4 := by
    rw [hk_eq] at this
    apply (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt pp)).mp this
  interval_cases k using k_gt_1, k_lt_4
  · left; exact hk_eq
  · right; exact hk_eq

lemma card_conj_class_1 (x : ConjClasses G) : Nat.card x.carrier * Nat.card (Subgroup.centralizer {Classical.choose (ConjClasses.exists_rep x)}) = Nat.card G := by

  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer (Classical.choose (ConjClasses.exists_rep x))]

  rw [← card_prod]
  apply card_congr
  have : x.carrier = MulAction.orbit (ConjAct G) (Classical.choose (ConjClasses.exists_rep x)) := by
    ext h
    apply Iff.trans ConjClasses.mem_carrier_iff_mk_eq
    apply Iff.trans _ (ConjAct.mem_orbit_conjAct).symm
    apply Iff.trans _ ConjClasses.mk_eq_mk_iff_isConj
    constructor
    · intro hh
      rw[hh]
      exact (Classical.choose_spec (ConjClasses.exists_rep x)).symm
    intro hh; rw [hh]
    exact (Classical.choose_spec (ConjClasses.exists_rep x))

  exact this ▸ MulAction.orbitProdStabilizerEquivGroup (ConjAct G) (Classical.choose (ConjClasses.exists_rep x))

lemma card_conj_class_2 [Finite G] : ∀ (x : ConjClasses G) (_ : x ∈ ConjClasses.noncenter G), Nat.card x.carrier = Nat.card G / Nat.card (Subgroup.centralizer {Classical.choose (ConjClasses.exists_rep x)}) := by
  intro x xnonc
  apply (Nat.div_eq_of_eq_mul_left card_pos (card_conj_class_1 x).symm).symm

lemma sum_eq [Finite G] : ∑ᶠ (x : ConjClasses G) (_ : x ∈ (ConjClasses.noncenter G)), Nat.card x.carrier =  ∑ᶠ (x : ConjClasses G) (_ : x ∈ (ConjClasses.noncenter G)) , Nat.card G / Nat.card (Subgroup.centralizer { Classical.choose (ConjClasses.exists_rep x) }) := by
  rw [finsum_congr (λ x ↦ finsum_congr (λ h' ↦ card_conj_class_2 x h'))]

lemma p1_p2_card_centr_exists_p3 (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(Subgroup.center G) = p ^ 1) : ∃ (g' : G), g' ∉ Subgroup.center G ∧ Nat.card (Subgroup.centralizer {g'}) = p ^ 3 := by
  by_contra h'
  push_neg at h'
  have h' : ∀ g' ∉ Subgroup.center G, Nat.card ↥(Subgroup.centralizer {g'}) = p ^ 2 := by
    intro g' g'nin
    rcases (@p1_card_centr_p2_p3 _ _ _ (G_finite h pp) h pp h1_eq g' g'nin) with (h'' | h'')
    · exact h''
    · exfalso
      have := h' g' g'nin
      contradiction

  have eq := @Group.nat_card_center_add_sum_card_noncenter_eq_card G _ (G_finite h pp)
  rw [@sum_eq _ _ (G_finite h pp)] at eq

  have (x : ConjClasses G) (h : x ∈ ConjClasses.noncenter G) : Nat.card G / Nat.card (Subgroup.centralizer {Classical.choose (ConjClasses.exists_rep x)}) = Nat.card G / p ^ 2 := by
    rw [h']

    by_contra h'
    have : ¬ x.carrier.Nontrivial := by
      simp only [Set.Nontrivial]
      push_neg
      intro a ha b hb
      have : a = Classical.choose (ConjClasses.exists_rep x) := by
        have : Classical.choose (ConjClasses.exists_rep x) ∈ x.carrier := by
            apply ConjClasses.mem_carrier_iff_mk_eq.mpr (Classical.choose_spec (ConjClasses.exists_rep x))
        apply IsConj.eq_of_right_mem_center
        · apply ConjClasses.mk_eq_mk_iff_isConj.mp
          apply ConjClasses.mem_carrier_iff_mk_eq.mp

          apply ConjClasses.mem_carrier_iff_mk_eq.mp at this
          rwa [this]
        exact h'

      have : b = Classical.choose (ConjClasses.exists_rep x) := by
        have : Classical.choose (ConjClasses.exists_rep x) ∈ x.carrier := by
            apply ConjClasses.mem_carrier_iff_mk_eq.mpr (Classical.choose_spec (ConjClasses.exists_rep x))
        apply IsConj.eq_of_right_mem_center
        · apply ConjClasses.mk_eq_mk_iff_isConj.mp
          apply ConjClasses.mem_carrier_iff_mk_eq.mp
          apply ConjClasses.mem_carrier_iff_mk_eq.mp at this
          rwa [this]
        exact h'
      rwa [this]
    contradiction
  rw [finsum_congr (λ x ↦ finsum_congr (λ h' ↦ this x h'))] at eq
  simp only [h, h1_eq] at eq
  rw [Nat.pow_div (by norm_num) (Nat.Prime.pos pp), pow_one] at eq

  have : Fintype ↑(ConjClasses.noncenter G) := by
    apply @Fintype.ofFinite _ (@Subtype.finite _ (@instFiniteConjClasses _ _ (G_finite h pp)) _)
  have : ∑ᶠ (x : ConjClasses G) (_ : x ∈ ConjClasses.noncenter G), p ^ 2 = Nat.card (ConjClasses.noncenter G) * p ^ 2 := by

    rw [finsum_mem_eq_toFinset_sum]
    rw [Finset.sum_const, smul_eq_mul]
    congr
    exact Eq.symm (card_eq_card_toFinset (ConjClasses.noncenter G))

  rw [this] at eq
  have : p^2 ∣ p^4 := by
    apply Nat.pow_dvd_pow; norm_num
  have : ¬ p^2 ∣ p + Nat.card (ConjClasses.noncenter G) * p ^ 2 := by
    by_contra h
    have : p^2 ∣ p := by
      apply (Nat.dvd_add_iff_left (Nat.dvd_mul_left (p^2) (Nat.card ({x : ConjClasses G | x.carrier.Nontrivial})))).mpr h
    have : ¬ p^2 ∣ p := by
      apply Nat.not_dvd_of_pos_of_lt (Nat.Prime.pos pp)
      nth_rewrite 1 [← Nat.pow_one p]
      apply Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pp) (by norm_num)
    contradiction
  rw [eq] at this
  contradiction

lemma aux_quotient_centr_not_cyclic [Finite G] (pp : p.Prime) {g : G} (h' : Nat.card (Subgroup.centralizer {g}) = p ^ 3) (hk_eq : Nat.card (Subgroup.center (Subgroup.centralizer {g})) = p ^ 2) : ¬ IsCyclic (Subgroup.centralizer {g} ⧸ (Subgroup.center (Subgroup.centralizer {g}))) := by
  by_contra h''

  have centr_not_comm : ¬ ∀ (a b : Subgroup.centralizer {g}), a * b = b * a := by
    intro h''
    have center_all_centr : Subgroup.center (Subgroup.centralizer {g}) = ⊤ := by
      ext g'
      apply Iff.trans (Subgroup.mem_center_iff)
      exact Iff.symm ((fun (ha : ∀ z : Subgroup.centralizer {g}, z * g' = g' * z) ↦ (iff_true_right ha).mpr) (fun g_1 ↦ h'' g_1 g') trivial)
    have : Nat.card (Subgroup.center (Subgroup.centralizer {g})) = p ^ 3 := by
      rw [center_all_centr]
      exact (h' ▸ Subgroup.card_top)
    have : Nat.card (Subgroup.center (Subgroup.centralizer {g})) ≠ Nat.card (Subgroup.center (Subgroup.centralizer {g})) := by
      nth_rw 1 [hk_eq, this]
      exact Nat.ne_of_lt (Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pp) (by norm_num))
    contradiction
  have centr_comm (a b : (Subgroup.centralizer {g})) : a * b = b * a := by

    apply commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center (Subgroup.centralizer {g})))
    rw [QuotientGroup.ker_mk']
  contradiction

lemma p1_card_centr_p3_comm [Finite G] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(Subgroup.center G) = p ^ 1) (g : G) (gnin : g ∉ Subgroup.center G) (h' : Nat.card (Subgroup.centralizer {g}) = p ^ 3) : (Subgroup.centralizer {g}).IsCommutative := by

  have : IsPGroup p (Subgroup.centralizer {g}) := by
    exact IsPGroup.of_card h'
  rcases @IsPGroup.card_center_eq_prime_pow _ _ _ ⟨pp⟩ _ h' (by norm_num) with ⟨k, hk, hk_eq⟩
  have : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp
    exact h' ▸ hk_eq ▸ Subgroup.card_le_card_group (Subgroup.center ↥(Subgroup.centralizer {g}))
  have : 2 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp
    rw [← hk_eq]
    have g_in : g ∈ (Subgroup.center ↥(Subgroup.centralizer {g})).map (Subgroup.subtype (Subgroup.centralizer {g})) := by
      apply Subgroup.mem_map.mpr
      simp only [Subgroup.mem_center_iff]
      use ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      simp [Subgroup.mem_centralizer_iff]
      intro a h
      exact h.symm

    have : Subgroup.closure ({g} ∪ Subgroup.center G) ≤ (Subgroup.center ↥(Subgroup.centralizer {g})).map (Subgroup.subtype (Subgroup.centralizer {g})) := by
      apply (Subgroup.closure_le ((Subgroup.center ↥(Subgroup.centralizer {g})).map (Subgroup.subtype (Subgroup.centralizer {g})))).mpr
      apply Set.union_subset
      · apply Set.singleton_subset_iff.mpr g_in
      intro a ha
      apply Subgroup.mem_map.mpr
      simp only [Subgroup.mem_center_iff]
      simp [Subgroup.mem_centralizer_iff]
      constructor
      · intro b hb
        exact Subgroup.mem_center_iff.mp ha b
      exact Subgroup.mem_center_iff.mp ha g
    have : Nat.card (Subgroup.closure ({g} ∪ Subgroup.center G)) ≤ Nat.card ((Subgroup.center ↥(Subgroup.centralizer {g})).map (Subgroup.subtype (Subgroup.centralizer {g}))) := Subgroup.card_le_of_le this
    rw [Subgroup.card_subtype (Subgroup.centralizer {g}) (Subgroup.center ↥(Subgroup.centralizer {g}))] at this
    exact Nat.le_trans (card_closure pp h h1_eq gnin) this

  interval_cases k

  · have : Nat.card (Subgroup.centralizer {g} ⧸ Subgroup.center (Subgroup.centralizer {g})) = Nat.card (Subgroup.centralizer {g}) / Nat.card (Subgroup.center (Subgroup.centralizer {g})) := by
      apply Nat.eq_div_of_mul_eq_right
      · rw [hk_eq]; norm_num; exact Nat.Prime.ne_zero pp
      rw [← (Subgroup.center (Subgroup.centralizer {g})).index_eq_card,mul_comm, (Subgroup.center (Subgroup.centralizer {g})).index_mul_card]
    have : IsCyclic (Subgroup.centralizer {g} ⧸ Subgroup.center (Subgroup.centralizer {g})) := by
      have : Nat.card (Subgroup.centralizer {g} ⧸ Subgroup.center (Subgroup.centralizer {g})) = p := by
        rw [this, h', hk_eq, Nat.pow_div (by norm_num) (Nat.Prime.pos pp)]
        norm_num
      apply @isCyclic_of_prime_card _ _ _ ⟨pp⟩ this
    exfalso
    exact (aux_quotient_centr_not_cyclic pp h' hk_eq this)

  · have : Subgroup.center ↥(Subgroup.centralizer {g}) = ⊤ := by
      exact (Subgroup.card_eq_iff_eq_top (Subgroup.center ↥(Subgroup.centralizer {g}))).mp (h' ▸ hk_eq)

    refine {is_comm := ?_}
    refine {comm := ?_}
    intro a b
    apply Subgroup.mem_center_iff.mp (this ▸ Subgroup.mem_top b)

lemma p1_quotient (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(Subgroup.center G) = p ^ 1) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card ↥H = p ^ 3 := by
  have : Nat.card (Subgroup.center G) < Nat.card G := by
    rw [h1_eq, h]
    exact Nat.pow_lt_pow_of_lt (Nat.Prime.one_lt pp) (by norm_num)

  obtain ⟨g, gnin⟩ := @exists_diff_if_card _ _ (G_finite h pp) (Subgroup.center G) this
  rcases (@p1_card_centr_p2_p3 _ _ _ (G_finite h pp) h pp h1_eq g gnin) with h2_eq | h3_eq
  · obtain ⟨g', g'nin, h3_eq⟩ := p1_p2_card_centr_exists_p3 h pp h1_eq
    use Subgroup.centralizer {g'}, @p1_card_centr_p3_comm _ _ _ (G_finite h pp) h pp h1_eq g' g'nin h3_eq, h3_eq
  · use Subgroup.centralizer {g}, @p1_card_centr_p3_comm _ _ _ (G_finite h pp) h pp h1_eq g gnin h3_eq , h3_eq

theorem comm_p3_in_p4 (h : Nat.card G = p ^ 4) (pp : p.Prime) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  rcases (@IsPGroup.card_center_eq_prime_pow _ _ _ ⟨pp⟩ _ h (by norm_num)) with ⟨k, kge0, hk_eq⟩
  have : k ≤ 4 := by
     exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp (hk_eq ▸ h ▸ @Subgroup.card_le_card_group _ _ (Subgroup.center G) (G_finite h pp))
  interval_cases k
  · exact p1_quotient h pp hk_eq
  · exact p2_quotient h pp hk_eq
  · exact p3_quotient_contradiction h pp hk_eq
  · exact p4_quotient h pp hk_eq
