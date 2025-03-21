import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Finiteness
import Progetto.Basic

open Nat Subgroup

variable  {p : ℕ} {G : Type*} [Group G]

/-- Given a prime number `p` and a group `G` of order `p^n` with a center of order `p^(n-1)`, the quotient of `G` by its center is not cyclic-/
lemma aux_quotient_not_cyclic {n k : ℕ} (pp : p.Prime) (h : Nat.card G = p ^ n) (h' : Nat.card (center G) = p ^ k) (h'' : n = k + 1) : ¬ IsCyclic (G ⧸ center G) := by
  by_contra hc
  have G_comm : ∀ a b : G, a * b = b * a := by
    apply commutative_of_cyclic_center_quotient (QuotientGroup.mk' (center G))
    rw [QuotientGroup.ker_mk']
  have center_eq_top : center G = ⊤ := by
    ext g; apply Iff.trans (mem_center_iff)
    exact Iff.symm ((fun (ha : ∀ z : G, z * g = g * z) ↦ (iff_true_right ha).mpr) (fun g_1 ↦ G_comm g_1 g) trivial)
  have card_center_eq : Nat.card (center G) = p ^ n := by
    rw [center_eq_top, ← h, card_top]
  exact Nat.ne_of_lt (Nat.pow_lt_pow_of_lt (Prime.one_lt pp) (h'' ▸ lt_succ_self k)) (h' ▸ card_center_eq)

/--The center cannot have cardinality `p^3`-/
lemma p3_center_contradiction [Fact (p.Prime)] (h : Nat.card G = p ^ 4) (pp : p.Prime) (h3_eq : Nat.card (center G) = p ^ 3) :
    ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  have : Nat.card (G ⧸ center G) = p := by
    calc
      Nat.card (G ⧸ center G) = Nat.card G / Nat.card (center G) := by
        apply Nat.eq_div_of_mul_eq_right (Nat.ne_zero_iff_zero_lt.mpr (h3_eq ▸ Nat.pow_pos (Prime.pos pp)))
        rw [mul_comm]
        apply (card_eq_card_quotient_mul_card_subgroup (center G)).symm
      _ = p := by
        rw [h, h3_eq, Nat.pow_div (by norm_num) (pp.pos)]
        norm_num
  have cyclic_quotient : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card this
  exfalso
  exact (aux_quotient_not_cyclic pp h h3_eq (by norm_num) cyclic_quotient)

/-- If both a group and its center have order `p^4`, then the group is commutative-/
instance card_center_eq_card_comm_group {n : ℕ} [Finite G] (h : Nat.card G = n) (h4_eq : Nat.card (center G) = n) : CommGroup G :=
  Group.commGroupOfCenterEqTop ((card_eq_iff_eq_top (center G)).mp (h4_eq ▸ h.symm))

/-- If the center has order `p^4`, then because of Sylow's first theorem,there exists a subgroup of order `p^3`, which is commutative because every subgroup is commutative -/
lemma p4_center [Finite G] (h : Nat.card G = p ^ 4) (pp : p.Prime) (h4_eq : Nat.card (center G) = p ^ 4) :
    ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  have : p^3 ≤ Nat.card G := h ▸ Nat.pow_le_pow_right (Nat.Prime.one_le pp) (by norm_num)
  rcases Sylow.exists_subgroup_card_pow_prime_of_le_card pp (IsPGroup.of_card h) this with ⟨H, h_eq⟩
  exact ⟨H, @commGroup_isCommutative _ (card_center_eq_card_comm_group h h4_eq) H, h_eq⟩

/-- If a group `G` has a subgroup `H` of cardinality lower than the group's, then there exists an element in `G` not in `H`-/
lemma exists_diff_if_card [Finite G] (H : Subgroup G) (h : Nat.card H < Nat.card G) : ∃ g : G, g ∉ H := by
  by_contra h'
  push_neg at h'
  exact h.not_le (le_of_eq ((card_eq_iff_eq_top H).mpr ((eq_top_iff' H).mpr h')).symm)

/-- The center of a finite group has a lower cardinality of the centralizer of an element not in the center-/
lemma card_center_le_centr [Finite G] (g : G) (h' : g ∉ center G) : Nat.card (center G) < Nat.card (centralizer {g}) :=
  Set.Finite.card_lt_card Subtype.finite (HasSubset.Subset.ssubset_of_not_subset
    (center_le_centralizer {g}) (fun a ↦ h' (a (mem_centralizer_singleton_iff.mpr rfl))))

/-- The subgroup generated by an element `g` and the center is commutative-/
lemma closure_center_g_iscomm {g : G} : (closure ({g} ∪ center G)).IsCommutative := by
  refine ⟨⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_⟩⟩; simp
  induction ha, hb using closure_induction₂ with
  | mem x y hx hy =>
    rcases (Set.mem_union x {g} (center G)).mp hx with ⟨hx | hx⟩ | hx
    · rcases (Set.mem_union y {g} (center G)).mp hy with ⟨hy | hy⟩ | hy
      · rfl
      exact mem_center_iff.mp hy g
    · exact Eq.symm (mem_center_iff.mp hx y)
  | one_left x hx => group
  | one_right x hx => group
  | mul_left x y z hx hy hz hxz hyz => rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc]
  | mul_right y z x hy hz hx hxy hxz => rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]
  | inv_left x y hx hy hxy => calc
      x⁻¹ * y = x⁻¹ * (y * x * x⁻¹) := by group
      _ = x⁻¹ * (x * y * x⁻¹) := by rw [hxy]
      _ = y * x⁻¹ := by group
  | inv_right x y hx hy hxy => calc
      x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
      _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hxy]
      _ = y⁻¹ * x := by group

open Classical

/-- If the center has cardinality `p^k`,then the cardinality of the subgroup generated by the center and an element not in the center is greater than `p^(k+1)`-/
lemma card_closure {k : ℕ} [Finite G] (pp : p.Prime) (h : Nat.card G = p ^ 4) (h' : Nat.card (center G) = p ^ k)
    {g : G} (gnin : g ∉ center G) : p ^ (k + 1) ≤ Nat.card (closure ({g} ∪ center G)) := by
  have : p ^ k < Nat.card (({g} ∪ center G) : Set G) := by
    have : ((center G) : Set G).Finite := by
      exact Set.toFinite (center G).carrier
    rw [← h', Set.Finite.card_union_of_disjoint this
        (Set.finite_singleton g) (Set.disjoint_singleton_left.mpr gnin)]
    exact Nat.lt_add_of_pos_left card_pos
  have : p ^ k < Nat.card (closure ({g} ∪ center G)) := lt_of_lt_of_le this (Set.Finite.card_le_card
    Subtype.finite subset_closure)
  rcases (dvd_prime_pow pp).mp (h ▸ card_subgroup_dvd_card (closure ({g} ∪ center G))) with ⟨j, hj, hj_eq⟩
  exact hj_eq ▸ (pow_le_pow_iff_right₀ (Prime.one_lt pp)).mpr (add_one_le_iff.mpr
    ((pow_lt_pow_iff_right₀ (Prime.one_lt pp)).mp (hj_eq ▸ this)))

/-- A group is commutative if the top subgroup is commutative-/
instance commgroup_if_top_comm (h : (⊤ : Subgroup G).IsCommutative) : ∀ (a b : G), a * b = b * a :=
  fun _ _ ↦ mul_comm_of_mem_isCommutative ⊤ trivial trivial

/-- If the center has cardinality `p^2`, then the subgroup generated by the center and an element not in the center has cardinality `p^3`-/
lemma p2_card_closure_center_g [Finite G] (h : Nat.card G = p^4) (pp : p.Prime) (h2_eq : Nat.card (center G) = p ^ 2)
    {g : G} (gnin : g ∉ center G) : Nat.card (closure ({g} ∪ center G)) = p ^ 3 := by
  rcases (dvd_prime_pow pp).mp (h.symm ▸ card_subgroup_dvd_card (closure ({g} ∪ center G))) with ⟨k, hk, hk_eq⟩
  have : 3 ≤ k := (pow_le_pow_iff_right₀ (Prime.one_lt pp)).mp (hk_eq ▸ card_closure pp h h2_eq gnin)
  interval_cases k using this, hk
  · exact hk_eq
  · have : closure ({g} ∪ center G) = ⊤ := (card_eq_iff_eq_top _).mp (hk_eq ▸ h.symm)
    have : g ∈ center G := mem_center_iff.mpr (fun g_1 ↦ commgroup_if_top_comm (this.symm ▸ closure_center_g_iscomm) g_1 g)
    contradiction

/-- If the center has order `p^2`, then there exists a commutative subgroup of order `p^3`, which is the subgroup generated by the center and an element not in the center-/
lemma p2_center [Finite G] (h : Nat.card G = p ^ 4) (pp : p.Prime) (h2_eq : Nat.card (center G) = p ^ 2) :
    ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  obtain ⟨g, gnin⟩ := exists_diff_if_card (center G)
    (h2_eq ▸ h ▸ Nat.pow_lt_pow_of_lt (Prime.one_lt pp) (by norm_num))
  exact ⟨closure ({g} ∪ center G), closure_center_g_iscomm, p2_card_closure_center_g h pp h2_eq gnin⟩

/-- If the center has order `p`, then the centralizer of an element not in the center has order `p^2` or `p^3`-/
lemma p1_card_centr_p2_p3 [Finite G] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card (center G) = p ^ 1)
  (g : G) (h' : g ∉ center G) : Nat.card (centralizer {g}) = p ^ 2 ∨ Nat.card (centralizer {g}) = p ^ 3 := by
  have h_centr : Nat.card (centralizer {g}) ∣ p ^ 4 := h.symm ▸ card_subgroup_dvd_card (centralizer {g})
  rcases (dvd_prime_pow pp).mp h_centr with ⟨k, hk, hk_eq⟩
  have k_gt_1 : 1 < k := (pow_lt_pow_iff_right₀ (Prime.one_lt pp)).mp (h1_eq ▸ hk_eq ▸ card_center_le_centr g h')
  have k_lt_4 : k < 4 := by
    by_contra h''
    push_neg at h''
    have : k = 4 := by
      apply Nat.eq_iff_le_and_ge.mpr ⟨_, h''⟩
      exact (pow_le_pow_iff_right₀ (Prime.one_lt pp)).mp (hk_eq ▸ h ▸ card_le_card_group (centralizer {g}))
    have : centralizer {g} = ⊤ := by
      apply (card_eq_iff_eq_top _).mp
      rw [h, hk_eq, this]
    exact h' ((centralizer_eq_top_iff_subset).mp this rfl)
  interval_cases k using k_gt_1, k_lt_4
  · exact Or.inl hk_eq
  · exact Or.inr hk_eq

/-- The cardinality of a group is equal to the product of the cardinality of one of its nontrivial conjugacy class for the cardinality of the centralizer of a representative of the class-/
lemma card_conj_class (x : ConjClasses G) : Nat.card x.carrier * Nat.card (centralizer {choose (ConjClasses.exists_rep x)}) = Nat.card G := by
  rw [nat_card_centralizer_nat_card_stabilizer (choose (ConjClasses.exists_rep x)), ← card_prod]
  apply card_congr
  have : x.carrier = MulAction.orbit (ConjAct G) (choose (ConjClasses.exists_rep x)) := by
    ext g
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjAct.mem_orbit_conjAct, ← ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · intro h; rw [h]; exact (choose_spec (ConjClasses.exists_rep x)).symm
    intro h; rw [h]; exact choose_spec (ConjClasses.exists_rep x)
  exact this ▸ MulAction.orbitProdStabilizerEquivGroup (ConjAct G) (choose (ConjClasses.exists_rep x))

/-- The cardinality of a nontrivial conjugacy class is equal to the cardinality of the group divided by the cardinality of the centralizer of a representative of the class-/
lemma card_conj_class' [Finite G] : ∀ (x : ConjClasses G) (_ : x ∈ ConjClasses.noncenter G), Nat.card x.carrier = Nat.card G / Nat.card (centralizer {choose (ConjClasses.exists_rep x)}) := by
  intro x xnonc
  apply (Nat.div_eq_of_eq_mul_left card_pos (card_conj_class x).symm).symm

/-- The sum of the cardinalities of the nontrivial conjugacy classes is equal to the sum of the cardinalities of the centralizers of the representatives of the classes-/
lemma sum_eq [Finite G] : ∑ᶠ (x : ConjClasses G) (_ : x ∈ (ConjClasses.noncenter G)), Nat.card x.carrier =  ∑ᶠ (x : ConjClasses G) (_ : x ∈ (ConjClasses.noncenter G)) , Nat.card G / Nat.card (centralizer {choose (ConjClasses.exists_rep x)}) := by
  rw [finsum_congr (λ x ↦ finsum_congr (λ h' ↦ card_conj_class' x h'))]

/-- If the center has order `p`, then there exists an element not in the center with a centralizer of order `p^3`-/
lemma p1_p2_card_centr_exists_p3 [Finite G] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(center G) = p ^ 1) : ∃ (g' : G), g' ∉ center G ∧ Nat.card (centralizer {g'}) = p ^ 3 := by
  by_contra h'
  push_neg at h'
  have h' : ∀ g' ∉ center G, Nat.card ↥(centralizer {g'}) = p ^ 2 := by
    intro g' g'nin
    rcases (p1_card_centr_p2_p3 h pp h1_eq g' g'nin) with (h'' | h'')
    · exact h''
    · exfalso
      have := h' g' g'nin
      contradiction
  have eq := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  rw [sum_eq] at eq

  have (x : ConjClasses G) (h : x ∈ ConjClasses.noncenter G) : Nat.card G / Nat.card (centralizer {choose (ConjClasses.exists_rep x)}) = Nat.card G / p ^ 2 := by
    rw [h']

    by_contra h'
    have : ¬ x.carrier.Nontrivial := by
      simp only [Set.Nontrivial]
      push_neg
      intro a ha b hb
      have : a = choose (ConjClasses.exists_rep x) := by
        have : choose (ConjClasses.exists_rep x) ∈ x.carrier := by
            apply ConjClasses.mem_carrier_iff_mk_eq.mpr (choose_spec (ConjClasses.exists_rep x))
        apply IsConj.eq_of_right_mem_center
        · apply ConjClasses.mk_eq_mk_iff_isConj.mp
          apply ConjClasses.mem_carrier_iff_mk_eq.mp

          apply ConjClasses.mem_carrier_iff_mk_eq.mp at this
          rwa [this]
        exact h'
      have : b = choose (ConjClasses.exists_rep x) := by
        have : choose (ConjClasses.exists_rep x) ∈ x.carrier := by
            apply ConjClasses.mem_carrier_iff_mk_eq.mpr (choose_spec (ConjClasses.exists_rep x))
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
    apply @Fintype.ofFinite _ (@Subtype.finite _ (instFiniteConjClasses) _)
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

/-- If the center has order `p`, and the centralizer of an element not in the center has order `p^3`, then the centralizer is commutative-/
lemma p1_card_centr_p3_comm [Finite G] [Fact (p.Prime)] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card ↥(center G) = p ^ 1) (g : G) (gnin : g ∉ center G) (h' : Nat.card (centralizer {g}) = p ^ 3) : (centralizer {g}).IsCommutative := by
  have : IsPGroup p (centralizer {g}) := IsPGroup.of_card h'
  rcases IsPGroup.card_center_eq_prime_pow h' (by norm_num) with ⟨k, hk, hk_eq⟩
  have k_le_3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp
    (h' ▸ hk_eq ▸ card_le_card_group (center (centralizer {g})))

  have k_ge_2 : 2 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt pp)).mp
    have g_in : g ∈ (center (centralizer {g})).map (Subgroup.subtype (centralizer {g})) := by
      apply mem_map.mpr; simp [mem_center_iff, mem_centralizer_iff]
      exact fun a ha => ha.symm

    have : closure ({g} ∪ center G) ≤ (center (centralizer {g})).map (Subgroup.subtype (centralizer {g})) := by
      apply (closure_le _).mpr
      apply Set.union_subset
      · exact Set.singleton_subset_iff.mpr g_in
      · intro a ha; apply mem_map.mpr; simp [mem_center_iff, mem_centralizer_iff]
        constructor; exact fun b _ => mem_center_iff.mp ha b
        exact mem_center_iff.mp ha g

    have card_le : Nat.card (closure ({g} ∪ center G)) ≤ Nat.card ((center (centralizer {g})).map (Subgroup.subtype (centralizer {g}))) :=
      card_le_of_le this
    rw [card_subtype] at card_le
    exact le_trans (card_closure pp h h1_eq gnin) (hk_eq ▸ card_le)

  interval_cases k using k_ge_2, k_le_3

  · have : Nat.card (centralizer {g} ⧸ center (centralizer {g})) = p := by
      calc
        Nat.card (centralizer {g} ⧸ center (centralizer {g})) = Nat.card (centralizer {g}) / Nat.card (center (centralizer {g})) := by
          apply Nat.eq_div_of_mul_eq_right (Nat.ne_zero_iff_zero_lt.mpr (hk_eq ▸ Nat.pow_pos (Prime.pos pp)))
          rw [mul_comm]
          apply (card_eq_card_quotient_mul_card_subgroup (center (centralizer {g}))).symm
        _ = p := by
          rw [h', hk_eq, Nat.pow_div (by norm_num) pp.pos]
          norm_num
    have quot_cyclic : IsCyclic (centralizer {g} ⧸ center (centralizer {g})) :=
      isCyclic_of_prime_card this
    exact absurd quot_cyclic (aux_quotient_not_cyclic pp h' hk_eq (by norm_num))

  · exact ⟨⟨fun a b => mem_center_iff.mp
      ((card_eq_iff_eq_top _).mp (h' ▸ hk_eq) ▸ mem_top b) a⟩⟩

/-- If the center has order `p`, then there exists a commutative subgroup of order `p^3`, which is the centralizer of an element not in the center-/
lemma p1_center [Finite G] [Fact (p.Prime)] (h : Nat.card G = p ^ 4) (pp : Nat.Prime p) (h1_eq : Nat.card (center G) = p ^ 1) :
  ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  obtain ⟨g, gnin⟩ := exists_diff_if_card (center G) (h1_eq ▸ h ▸ Nat.pow_lt_pow_of_lt (Prime.one_lt pp) (by norm_num))
  rcases (p1_card_centr_p2_p3 h pp h1_eq g gnin) with h2_eq | h3_eq
  · obtain ⟨g', g'nin, h3_eq⟩ := p1_p2_card_centr_exists_p3 h pp h1_eq
    exact ⟨centralizer {g'}, p1_card_centr_p3_comm h pp h1_eq g' g'nin h3_eq, h3_eq⟩
  · exact ⟨centralizer {g}, p1_card_centr_p3_comm h pp h1_eq g gnin h3_eq, h3_eq⟩

/-- Main theorem: any group of order `p^4` contains a commutative subgroup of order `p^3`-/
theorem comm_p3_in_p4 (h : Nat.card G = p ^ 4) (pp : p.Prime) : ∃ H : Subgroup G, H.IsCommutative ∧ Nat.card H = p ^ 3 := by
  have : Finite G :=
  Nat.finite_of_card_ne_zero (Nat.ne_zero_iff_zero_lt.mpr (h.symm ▸ (Nat.pow_pos (Nat.Prime.pos pp))))
  have pp_fact : Fact (p.Prime) := ⟨pp⟩
  rcases (IsPGroup.card_center_eq_prime_pow h (by norm_num)) with ⟨k, _, hk_eq⟩
  have : k ≤ 4 := (pow_le_pow_iff_right₀ (Prime.one_lt pp)).mp (hk_eq ▸ h ▸ card_le_card_group (center G))
  interval_cases k
  · exact p1_center h pp hk_eq
  · exact p2_center h pp hk_eq
  · exact p3_center_contradiction h pp hk_eq
  · exact p4_center h pp hk_eq
