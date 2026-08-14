import ZFLean.Basic
import ZFLean.Naturals
import ZFLean.Functions

namespace ZFSet


def isInfinite (A : ZFSet) : Prop :=
  ∃ (f: ZFSet) (hf: Nat.IsFunc A f), f.IsInjective

/-!
We have a predicate `isFinite` defined in `ZFSet.Functions` and we would like to have that
`∀ A : ZFSet, A.isInfinite ↔ ¬ A.isFinite`.

The forward direction is obtained by the pigeonhole principle, that is proving there are no
injections from a `n : ZFNat` to `m : ZFNat` given that `n < m`. The reverse
direction consist of constructing a injective function from `Nat` to `A` given that for all
`n : ZFNat` and `f` a function from `A` to `n`, `f` is not injective.
-/


-- TODO is this interesting enough to be put in Functions.lean ?
theorem func_to_empty_is_from_empty (f A : ZFSet) (hf : A.IsFunc ∅ f) : A = ∅ := by
  by_contra not_empty
  rw [←Ne.eq_def, nonempty_exists_iff] at not_empty
  obtain ⟨x, x_in_A⟩ := not_empty
  let y := fapply f (is_func_is_pfunc hf) ⟨x, by rwa [is_func_dom_eq]⟩
  have y_in_empty := fapply_mem_range (is_func_is_pfunc hf) (by rwa [is_func_dom_eq])
  exact notMem_empty y y_in_empty

theorem no_func_from_1_to_0 (f : ZFSet) : ¬IsFunc (1 : ZFNat).val (0 : ZFNat).val f := by
  intro hf
  convert func_to_empty_is_from_empty f (1 : ZFNat).val hf
  rw [false_iff, ←Ne.eq_def, nonempty_exists_iff]
  exact ⟨∅, mem_insert ∅ ∅⟩

lemma lt_succ_of_lt {m n : ZFNat} (m_lt_n : m < n) : m < n.succ := by
  trans n
  · exact m_lt_n
  · exact ZFNat.lt_succ

section Pigeonhole
-- Essentially a restriction, maybe when those are ready we can define them
-- For now there
open Classical in
noncomputable def pigeonhole_func (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f) :=
  λᶻ : i.succ.val → i.val| x ↦ if hxi : x ∈ i.succ.val then
    have hx : x ∈ f.Dom := by
      rw [is_func_dom_eq]
      change (⟨x, ZFNat.mem_Nat_of_mem_mem_Nat i.succ.prop hxi⟩ : ZFNat) < i.succ.succ
      exact lt_succ_of_lt hxi
    fapply f (hf:= ZFSet.is_func_is_pfunc hf) ⟨x, hx⟩
  else ∅


theorem pigeonhole_func_is_func (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f)
    (hr : ∀ j < i.succ, j.val.pair i.val ∉ f) :
    IsFunc i.succ.val i.val (pigeonhole_func i f hf) := by
  apply lambda_isFunc
  intro x hx
  rw [dif_pos hx]
  dsimp only
  generalize_proofs f_is_pfunc _ x_in_dom
  have y_in_isucc := fapply_mem_range f_is_pfunc x_in_dom
  lift (fapply f f_is_pfunc ⟨x, x_in_dom⟩).val to ZFNat with y hy
  · exact ZFNat.mem_Nat_of_mem_mem_Nat i.succ.prop y_in_isucc
  change y < i
  apply Or.resolve_right
  · apply LE.le.lt_or_eq
    rw [ZFNat.lt_le_iff]
    exact y_in_isucc
  · intro y_is_i
    rw [←y_is_i] at hr hx
    have x_not_related_to_y := hr ⟨x, ZFNat.mem_Nat_of_mem_mem_Nat (ZFNat.succ y).prop hx⟩ hx
    have x_related_to_y := hy ▸ fapply.def f_is_pfunc x_in_dom
    contradiction

theorem pigeonhole_func_is_restriction (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f)
    (hr : ∀ j < i.succ, j.val.pair i.val ∉ f) :
    ∀ x < i.succ, ∀ y < i,
    x.val.pair y.val ∈ f ↔ x.val.pair y.val ∈ (pigeonhole_func i f hf) := by
  intro x x_in_isucc y y_in_i
  set ph := pigeonhole_func i f hf
  have ph_isFunc := pigeonhole_func_is_func i f hf hr
  have x_in_domf : x.val ∈ f.Dom := by
        rw [is_func_dom_eq]
        change x < i.succ.succ
        trans i.succ
        · exact x_in_isucc
        · exact ZFNat.lt_succ
  constructor
  case mp =>
    intro fx_is_y
    unfold ph pigeonhole_func
    rw [lambda_spec]
    and_intros
    · exact x_in_isucc
    · exact y_in_i
    rw [dif_pos (by exact x_in_isucc)]
    have h := Eq.symm <| fapply.of_pair (is_func_is_pfunc hf) fx_is_y
    rw [Subtype.ext_iff] at h
    exact h
  case mpr =>
    intro y_is_phx
    unfold ph pigeonhole_func at y_is_phx
    rw [lambda_spec] at y_is_phx
    obtain ⟨_, _, y_is_phx⟩ := y_is_phx
    rw [dif_pos (by exact x_in_isucc)] at y_is_phx
    · exact y_is_phx ▸ fapply.def (is_func_is_pfunc hf) x_in_domf

open Classical in
noncomputable def pigeonhole_func_swapped (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f)
    (j : ZFNat) :=
  λᶻ : i.succ.val → i.val| x ↦ if hxi : x ∈ i.succ.val then
    if x = j.val then
      fapply f (hf := ZFSet.is_func_is_pfunc hf)
        ⟨i.succ.val, by rw [is_func_dom_eq]; exact ZFNat.lt_succ⟩
    else
      have hx : x ∈ f.Dom := by
        rw [is_func_dom_eq]
        change (⟨x, ZFNat.mem_Nat_of_mem_mem_Nat i.succ.prop hxi⟩ : ZFNat) < i.succ.succ
        exact lt_succ_of_lt hxi
      fapply f (hf := ZFSet.is_func_is_pfunc hf) ⟨x, hx⟩
  else ∅

theorem pigeonhole_func_swapped_is_func (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f) (j : ZFNat)
    (only_j_related_to_i : ∀ k < i.succ, k ≠ j → k.val.pair i.val ∉ f)
    (isucc_not_related_i : i.succ.val.pair i.val ∉ f) :
    IsFunc i.succ.val i.val (pigeonhole_func_swapped i f hf j) := by
  apply lambda_isFunc
  intro x hx
  rw [dif_pos hx]
  by_cases hswap: x = j.val
  · rw [if_pos hswap]
    generalize_proofs f_is_pfunc _ isucc_in_domf
    lift (fapply f f_is_pfunc ⟨i.succ, isucc_in_domf⟩).val to ZFNat with y hy
    · apply ZFNat.mem_Nat_of_mem_mem_Nat i.succ.prop
      exact fapply_mem_range f_is_pfunc isucc_in_domf
    change y < i
    rw [lt_iff_le_and_ne]
    and_intros
    · rw [ZFNat.lt_le_iff]
      exact_mod_cast
        hy ▸ fapply_mem_range f_is_pfunc (by rw [is_func_dom_eq]; exact ZFNat.lt_succ)
    · intro y_is_i
      have isucc_related_to_i  := y_is_i ▸ hy ▸ fapply.def f_is_pfunc isucc_in_domf
      contradiction
  · rw [if_neg hswap]
    dsimp only
    generalize_proofs f_is_pfunc _ x_in_domf
    lift (fapply f f_is_pfunc ⟨x, x_in_domf⟩).val to ZFNat with y hy
    · apply ZFNat.mem_Nat_of_mem_mem_Nat i.succ.prop
      exact fapply_mem_range f_is_pfunc x_in_domf
    change y < i
    apply Or.resolve_right
    · apply LE.le.lt_or_eq
      rw [ZFNat.lt_le_iff]
      exact_mod_cast (hy ▸ fapply_mem_range f_is_pfunc x_in_domf)
    · intro y_is_i
      rw [←y_is_i] at only_j_related_to_i hf hx
      apply only_j_related_to_i ⟨x, ZFNat.mem_Nat_of_mem_mem_Nat (ZFNat.succ y).prop hx⟩
       hx (by rwa [←Subtype.coe_ne_coe])
      exact hy ▸ fapply.def f_is_pfunc x_in_domf

-- It is not really a restriction
-- Here only one side of the equivalence is proven, since the other one is not used
open Classical in
theorem pigeonhole_func_swapped_is_restriction (i : ZFNat)
    (f : ZFSet) (hf : IsFunc i.succ.succ.val i.succ.val f) (j : ZFNat) :
    ∀ x < i.succ, ∀ y < i,
    x.val.pair y.val ∈ pigeonhole_func_swapped i f hf j
    → if x.val = j.val then i.succ.val.pair y.val ∈ f else x.val.pair y.val ∈ f := by
  intro x x_in_isucc y y_in_i x_y_related_ph
  by_cases x_is_j : x.val = j.val
  · rw [if_pos x_is_j]
    have j_y_related_ph := x_is_j ▸ x_y_related_ph
    erw [lambda_spec] at j_y_related_ph
    obtain ⟨j_in_isucc, _, j_y_related_ph⟩ := j_y_related_ph
    rw [dif_pos j_in_isucc, if_pos rfl] at j_y_related_ph
    rw [← fapply_iff]
    exact j_y_related_ph
  · rw [if_neg x_is_j]
    erw [lambda_spec] at x_y_related_ph
    obtain ⟨j_in_isucc, _, x_y_related_ph⟩ := x_y_related_ph
    rw [dif_pos j_in_isucc, if_neg x_is_j] at x_y_related_ph
    rw [x_y_related_ph]
    apply fapply.def

theorem pigeonhole_succ (zn : ZFNat) (f : ZFSet) (hf : IsFunc zn.succ.val zn.val f) :
    ∃ k1 < zn.succ, ∃ k2 < zn.succ, ∃ l < zn,
    k1.val.pair l ∈ f ∧ k2.val.pair l ∈ f  ∧ k1 ≠ k2 := by
  induction zn generalizing f with
  | zero =>
    nomatch no_func_from_1_to_0 f hf
  | succ i ih =>
    replace hf := ZFNat.add_one_eq_succ ▸ hf
    rw [ZFNat.add_one_eq_succ]
    by_cases hr : ∀ j < i.succ, j.val.pair i.val ∉ f
    · let ph := pigeonhole_func i f hf
      have phf := pigeonhole_func_is_func i f hf hr
      have ⟨k1, k1_in_isucc, k2, k2_in_isucc, l, l_in_i, k1_l_related, k2_l_related, k1_neq_k2⟩  :=
        ih ph phf
      exists k1, lt_succ_of_lt k1_in_isucc,
        k2, lt_succ_of_lt k2_in_isucc,
        l, lt_succ_of_lt l_in_i
      and_intros
      · have k1_l_also_in_f :=  pigeonhole_func_is_restriction i f hf hr
          k1 k1_in_isucc l l_in_i
        rw [←k1_l_also_in_f] at k1_l_related
        exact k1_l_related
      · have k2_l_also_in_f :=  pigeonhole_func_is_restriction i f hf hr
          k2 k2_in_isucc l l_in_i
        rw [←k2_l_also_in_f] at k2_l_related
        exact k2_l_related
      · exact k1_neq_k2
    · push Not at hr
      obtain ⟨j, j_lt_isucc, j_related_to_i⟩ := hr
      have j_lt_isuccsucc: j < i.succ.succ := by
        trans i.succ
        · exact j_lt_isucc
        · exact ZFNat.lt_succ
      by_cases hs : i.succ.val.pair i.val ∈ f
      · exists j, j_lt_isuccsucc, i.succ, ZFNat.lt_succ, i, ZFNat.lt_succ
        and_intros
        · exact j_related_to_i
        · exact hs
        · exact ZFNat.lt_imp_ne j_lt_isucc
      · by_cases ht: ∀ k < i.succ, k ≠ j → k.val.pair i.val ∉ f
        · let ph := pigeonhole_func_swapped i f hf j
          have phf := pigeonhole_func_swapped_is_func i f hf j ht hs
          have ⟨
            k1, k1_in_isucc,
            k2, k2_in_isucc,
            l, l_in_i,
            k1_l_related, k2_l_related, k1_neq_k2⟩ :=
            ih ph phf
          by_cases hu : k1 = j ∨ k2 = j
          · wlog h: k1 = j generalizing k1 k2
            · exact this
                k2 k2_in_isucc
                k1 k1_in_isucc
                k2_l_related k1_l_related
                k1_neq_k2.symm hu.symm
                <| hu.resolve_left h
            · exists
                i.succ, ZFNat.lt_succ,
                k2, lt_succ_of_lt k2_in_isucc,
                l,  lt_succ_of_lt l_in_i
              and_intros
              · have k1_l_also_in_f := pigeonhole_func_swapped_is_restriction i f hf j
                  k1 k1_in_isucc
                  l l_in_i
                  k1_l_related
                rw [SetLike.coe_eq_coe, if_pos h] at k1_l_also_in_f
                exact k1_l_also_in_f
              · have k2_l_also_in_f := pigeonhole_func_swapped_is_restriction i f hf j
                  k2 k2_in_isucc
                  l l_in_i
                  k2_l_related
                rw [SetLike.coe_eq_coe, if_neg (h ▸ k1_neq_k2.symm)] at k2_l_also_in_f
                exact k2_l_also_in_f
              · rw [ne_comm]
                intro k2_is_isucc
                exact mem_irrefl i.succ.val (k2_is_isucc ▸ k2_in_isucc)
          · exists
              k1, lt_succ_of_lt k1_in_isucc,
              k2, lt_succ_of_lt k2_in_isucc,
              l,  lt_succ_of_lt l_in_i
            push Not at hu
            and_intros
            · have k1_l_also_in_f := pigeonhole_func_swapped_is_restriction i f hf j
                k1 k1_in_isucc
                l l_in_i
                k1_l_related
              rw [SetLike.coe_eq_coe, if_neg hu.left] at k1_l_also_in_f
              exact k1_l_also_in_f
            · have k2_l_also_in_f := pigeonhole_func_swapped_is_restriction i f hf j
                k2 k2_in_isucc
                l l_in_i
                k2_l_related
              rw [SetLike.coe_eq_coe, if_neg hu.right] at k2_l_also_in_f
              exact k2_l_also_in_f
            · exact k1_neq_k2
        · push Not at ht
          obtain ⟨k, k_in_isucc, k_neq_j, k_related_to_i⟩ := ht
          exists k, lt_succ_of_lt k_in_isucc,
            j, lt_succ_of_lt j_lt_isucc,
            i, ZFNat.lt_succ



theorem pigeonhole (a b : ZFNat) (a_gt_b : b < a) (f : ZFSet) (hf : IsFunc a b f) :
    ∃ k1 < a, ∃ k2 < a, ∃ l < b,
      k1.val.pair l ∈ f ∧ k2.val.pair l ∈ f ∧ k1 ≠ k2 := by
  let z := f.Restr (is_func_is_pfunc hf) b.succ
  have bsucc_sub_a : b.succ.val ⊆ a.val := by
    rw [subset_def]
    intro x x_in_bsucc
    lift x to ZFNat with n hn
    · exact ZFNat.mem_Nat_of_mem_mem_Nat b.succ.prop x_in_bsucc
    change n < a
    change n < b.succ at x_in_bsucc
    apply ZFNat.lt_of_succ_le
    trans b.succ
    all_goals rwa [ZFNat.le_lt_iff]
  have z_isFunc := f.IsFunc_Restr_of_IsFunc hf bsucc_sub_a
  obtain ⟨
    k1, k1_in_bsucc,
    k2, k2_in_bsucc,
    l,  l_in_b,
    k1_l_related, k2_l_related, k1_neq_k2⟩
      := pigeonhole_succ b z z_isFunc
  have helper {n : ZFNat} (n_lt_bsucc : n < b.succ) :
    n < a := by
    apply ZFNat.lt_of_succ_le
    trans b.succ
    all_goals rwa [ZFNat.le_lt_iff]
  exists
    k1, helper k1_in_bsucc,
    k2, helper k2_in_bsucc,
    l, l_in_b
  and_intros
  · apply And.left
    rwa [←f.mem_Restr_iff _ bsucc_sub_a]
  · apply And.left
    rwa [←f.mem_Restr_iff _ bsucc_sub_a]
  · exact k1_neq_k2
end Pigeonhole

theorem all_nat_sub_nat (n : ZFNat) : n.val ⊆ Nat := by
  obtain ⟨n, n_in_Nat⟩ := n
  dsimp
  intro m m_in_n
  exact ZFNat.mem_Nat_of_mem_mem_Nat n_in_Nat m_in_n


theorem all_nat_finite (n : ZFNat) (f : ZFSet) (hf : Nat.IsFunc n.val f) : ¬ f.IsInjective hf := by
  unfold IsInjective
  push Not
  simp_rw [exists_and_left]
  let restr  := f.Restr (is_func_is_pfunc hf) n.succ
  have restrf := f.IsFunc_Restr_of_IsFunc hf <| all_nat_sub_nat n.succ
  obtain ⟨w1, _, w2, _, l, l_in_bsucc, w1_l_related, w2_l_related, w1_neq_w2⟩
    := pigeonhole_succ n restr restrf
  exists w1.val, w1.prop, w2.val, w2.prop, l.val, l_in_bsucc
  and_intros
  · apply And.left
    rwa [←f.mem_Restr_iff _ <| all_nat_sub_nat n.succ]
  · apply And.left
    rwa [←f.mem_Restr_iff _ <| all_nat_sub_nat n.succ]
  · exact_mod_cast w1_neq_w2

section NotFiniteChosenFunction

/--
Given the previous partial function `g`, since `g⁻¹` is a function from `A` to `m`, by the
`not_finite` hypothesis `g⁻¹` is not injective. Because `g` is injective, `g⁻¹` is also injective on
`g.Range`. So injective problems of `g⁻¹` are outside `g.Range` and  we are able to extract
a `y ∈ A \ g.Range`.
-/
lemma not_finite_chosen_function_partial_untouched (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective) (m : ℕ)
  (g : ZFSet) (hg : (m : ZFNat).val.IsFunc A g) (hig : g.IsInjective) :
    Nonempty (↑(A \ g.Range)) := by
  set untouched := A \ g.Range
  cases hi' : m with
  | zero =>
    rw [hi',Nat.cast_zero, ZFNat.nat_zero_eq, Subtype.coe_mk] at hg
    specialize not_finite 1
    let proj := λᶻ: A → (1 : ZFNat)| x ↦ (0 : ZFNat)
    let hproj : A.IsFunc (1 : ZFNat) proj := by
      apply lambda_isFunc
      intro _ _
      change (0: ZFNat) < (0 : ZFNat).succ
      exact ZFNat.zero_lt_succ
    have not_inj := not_finite proj hproj
    unfold IsInjective at not_inj
    push Not at not_inj
    obtain ⟨x1, _, _, x1_in_A, _⟩ := not_inj
    exists x1
    unfold untouched
    rw [mem_sdiff, and_iff_right x1_in_A]
    have g_sub_e : g = ∅ := by
      apply subset_of_empty
      trans (∅ : ZFSet).prod A
      · exact is_rel_of_is_func hg
      · intro z z_in_prod
        rw [mem_prod] at z_in_prod
        obtain ⟨z', z_in_e, _⟩ := z_in_prod
        nomatch (notMem_empty z') z_in_e
    conv => right; left; left; rw [g_sub_e]
    unfold Range
    rw [mem_sep, and_iff_right x1_in_A]
    push Not
    intro _ _
    apply notMem_empty
  | succ i' =>
    specialize not_finite m
    have nonemptydom : Nonempty g.Dom := by
      rw [is_func_dom_eq]
      exists ((0 : ℕ) : Nat)
      rw [←ZFNat.lt_def]
      apply ZFNat.pos_of_ne_zero
      rw [hi',Nat.cast_add,Nat.cast_one,ZFNat.add_one_eq_succ]
      exact (ZFNat.succ_ne_zero i' ·.symm)
    have inv_spec := (hig.apply_inj hg).leftInverse.choose_spec
    set inv := (hig.apply_inj hg).leftInverse.choose
    classical
    let og := λᶻ: A → (m : ZFNat)| y ↦ if y_in_A : y ∈ A then
      inv ⟨y, y_in_A⟩
      else (0 : Nat)
    have hog : A.IsFunc (m : ZFNat) og := by
      apply lambda_isFunc
      intro y y_in_A
      rw [dif_pos y_in_A]
      set x := inv ⟨y, y_in_A⟩
      conv => left; rw [←is_func_dom_eq hg]
      exact x.prop
    have w := not_finite og hog
    unfold IsInjective at w
    push Not at w
    obtain ⟨y1, y2, x, y1_in_A, y2_in_A, x_in_i, y1_img_x, y2_img_x, y1_ne_y2⟩ := w
    lift x to g.Dom using (by rwa [is_func_dom_eq]) with x
    rw [lambda_spec, and_iff_right (by assumption), and_iff_right (by assumption),
      dif_pos (by assumption), SetLike.coe_eq_coe] at y1_img_x y2_img_x
    by_cases y1_untouched : y1 ∈ untouched
    · exists y1
    by_cases y2_untouched : y2 ∈ untouched
    · exists y2
    · unfold untouched at y1_untouched y2_untouched
      rw [mem_sdiff, and_iff_right (by assumption), not_not] at y1_untouched y2_untouched
      have of_inv_inrange {y: A} (y_r: y.val ∈ g.Range) (y_img_x: x = (inv y)) : y = @ᶻg x := by
        rw [mem_sep, and_iff_right y.prop] at y_r
        obtain ⟨x', x'_in_dom, x'_y_related ⟩ := y_r
        rw [←fapply_iff (is_func_is_pfunc hg) x'_in_dom, SetLike.coe_eq_coe] at x'_y_related
        rw [x'_y_related, inv_spec] at y_img_x
        rw [x'_y_related, eq_comm]
        congr
      have x_img_y1 := of_inv_inrange y1_untouched y1_img_x
      have x_img_y2 := of_inv_inrange y2_untouched y2_img_x
      unfold IsInjective at hig
      rw [←x_img_y2,Subtype.mk_eq_mk] at x_img_y1
      nomatch y1_ne_y2 x_img_y1

open Classical in
/--
The next partial function is an extension of the previous one.
-/
noncomputable abbrev not_finite_chosen_function_partial_def {A g : ZFSet} {m : ℕ}
  (hg : (m : ZFNat).val.IsFunc A g) (y : ZFSet) :=
  λᶻ: ((m + 1: ℕ) : ZFNat) → A|k ↦
      if h: k ∈ (m : ZFNat).val then @ᶻg ⟨k, by rwa [is_func_dom_eq]⟩
      else y

/--
The next partial function is still a function, since the previous was already one.
-/
lemma not_finite_chosen_function_partial_isFunc {A g y : ZFSet} {m : ℕ}
  (hg : (m : ZFNat).val.IsFunc A g) (y_untouched : y ∈ A \ g.Range) :
    ((m + 1: ℕ) : ZFNat).val.IsFunc A <| not_finite_chosen_function_partial_def hg y := by
  classical
  apply lambda_isFunc
  intro x' x_in_isucc
  lift x' to ZFNat with x hx
  · exact ZFNat.mem_Nat_of_mem_mem_Nat (m + 1 : ZFNat).prop x_in_isucc
  change x < (m + 1: ZFNat) at x_in_isucc
  rw [ZFNat.add_one_eq_succ,←ZFNat.lt_le_iff,le_iff_lt_or_eq] at x_in_isucc
  apply x_in_isucc.elim
  · intro x_lt_i
    change x.val ∈ (m : ZFNat).val at x_lt_i
    rw [dif_pos x_lt_i]
    exact fapply_mem_range (is_func_is_pfunc hg) (by rwa [is_func_dom_eq])
  · rintro rfl
    rw [dif_neg <| mem_irrefl (m : ZFNat).val]
    apply And.left
    rwa [←mem_sdiff]

/--
The next partial function is still injective, since the previous was already.
-/
lemma not_finite_chosen_function_partial_isInj {A g y : ZFSet} {m : ℕ}
  {hg : (m : ZFNat).val.IsFunc A g} (hig : g.IsInjective) (y_untouched : y ∈ A \ g.Range) :
    (not_finite_chosen_function_partial_def hg y).IsInjective
    <| not_finite_chosen_function_partial_isFunc hg y_untouched := by
  let (eq := hgs) gs := not_finite_chosen_function_partial_def hg y
  intro x1' x2' z x1_in_isucc x2_in_isucc z_in_A x1_z_related x2_z_related
  rw [Nat.cast_add,Nat.cast_one,ZFNat.add_one_eq_succ] at x1_in_isucc x2_in_isucc
  lift x1' to ZFNat using ZFNat.mem_Nat_of_mem_mem_Nat (m : ZFNat).succ.prop x1_in_isucc
    with x1 hx1
  lift x2' to ZFNat using ZFNat.mem_Nat_of_mem_mem_Nat (m : ZFNat).succ.prop x2_in_isucc
    with x2 hx2
  by_cases hz : z ∈ A \ g.Range
  · have x_eq_i (x: ZFNat) (x_z_related: x.val.pair z ∈ gs) (x_in_isucc: x < (m : ZFNat).succ)
      : x = (m : ZFNat) := by
      apply eq_of_le_of_not_lt
      · rwa [ZFNat.lt_le_iff]
      · intro x_in_i
        change x.val ∈ (m : ZFNat).val at x_in_i
        rw [hgs,lambda_spec, dif_pos x_in_i, fapply_iff] at x_z_related
        rw [mem_sdiff] at hz
        nomatch hz.right <| (is_func_is_pfunc hg).mem_range_of_mem x_z_related.right.right
    trans (m : ZFNat).val
    · exact_mod_cast x_eq_i x1 x1_z_related x1_in_isucc
    · symm
      exact_mod_cast x_eq_i x2 x2_z_related x2_in_isucc
  · have x_in_domG (x : ZFNat) (x_z_related: x.val.pair z ∈ gs) : x.val ∈ (m : ZFNat).val := by
      by_contra
      rw [lambda_spec, dif_neg this] at x_z_related
      obtain ⟨_,_,z_is_y⟩ := x_z_related
      subst z_is_y
      contradiction
    have x_z_related_g (x : ZFNat) (x_z_related: x.val.pair z ∈ gs) : x.val.pair z ∈ g := by
      have x_in_i := (x_in_domG x x_z_related)
      rw [lambda_spec, dif_pos x_in_i, fapply_iff] at x_z_related
      apply And.right
      · apply And.right
        exact x_z_related
    apply hig x1 x2 z (x_in_domG x1 x1_z_related) (x_in_domG x2 x2_z_related) z_in_A
    · exact x_z_related_g x1 x1_z_related
    · exact x_z_related_g x2 x2_z_related

/--
A partial function from `A` to `m` that is injective. They are constructed inductively.
-/
noncomputable def not_finite_chosen_function_partial (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
  (m : ℕ)
  : { g // ∃ hg : ((m: ZFNat).val.IsFunc A g), g.IsInjective} :=
  match m with
  | 0 => by
    exists ∅, is_func_empty
    intro x _ _ x_mem_empty
    nomatch notMem_empty x x_mem_empty
  | m + 1  => by
    obtain ⟨g,hg'⟩ := not_finite_chosen_function_partial A not_finite m
    have hig := hg'.choose_spec
    replace hg := hg'.choose
    have ⟨y, y_untouched⟩ := Nonempty.some
      <| not_finite_chosen_function_partial_untouched A not_finite m g hg hig
    exact ⟨
      not_finite_chosen_function_partial_def hg y,
      not_finite_chosen_function_partial_isFunc hg y_untouched,
      not_finite_chosen_function_partial_isInj hig y_untouched⟩

def not_finite_chosen_function_partial_nested_next (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
  (m : ℕ) :
    (not_finite_chosen_function_partial A not_finite m).val ⊆
      (not_finite_chosen_function_partial A not_finite (m + 1)).val := by
  induction m with
  | zero =>
    rw [not_finite_chosen_function_partial]
    apply empty_subset
  | succ i =>
    rw [subset_def]
    intro z
    conv =>
      congr
      all_goals
        rw [not_finite_chosen_function_partial]
        dsimp only
        rw [not_finite_chosen_function_partial_def, mem_lambda]
    rintro ⟨x, y, rfl,x_in_isucc,y_in_A,y_eq⟩
    exists x, y, rfl
    split_ands
    · change x ∈ (i + 1 + 1: ZFNat).val
      let zx : ZFNat := ⟨x, ZFNat.mem_Nat_of_mem_mem_Nat (i + 1 : ZFNat).prop x_in_isucc⟩
      have zx_x : x = zx.val := rfl
      rw [zx_x,←ZFNat.lt_def] at ⊢ x_in_isucc
      rw [Nat.cast_add, Nat.cast_one] at x_in_isucc
      rw [ZFNat.add_one_eq_succ]
      exact lt_succ_of_lt x_in_isucc
    · exact y_in_A
    · rw [dif_pos x_in_isucc,
        fapply_iff
          <| is_func_is_pfunc <| Exists.choose <| Subtype.prop
          <| A.not_finite_chosen_function_partial not_finite (i + 1),
        not_finite_chosen_function_partial, lambda_spec]
      trivial

def not_finite_chosen_function_partial_nested (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
  {m n : ℕ} (mlen : m ≤ n) :
    (not_finite_chosen_function_partial A not_finite m).val ⊆
      (not_finite_chosen_function_partial A not_finite n).val := by
  induction n with
  | zero =>
    apply Nat.le_zero.mp at mlen
    rw [mlen]
  | succ n hn =>
    rcases mlen with rfl | mlen
    · rfl
    · trans
      · exact hn mlen
      · exact not_finite_chosen_function_partial_nested_next A not_finite n

noncomputable
def not_finite_chosen_function (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
  := ⋃ n :  ℕ, A.not_finite_chosen_function_partial not_finite n

lemma Nat_as_union_of_finite_intervals : Nat = ⋃ n : ℕ, (n : ZFNat) := by
  ext z
  rw [mem_iUnion]
  constructor
  · intro z_in_Nat
    let zn : ZFNat := ⟨z, z_in_Nat⟩
    have r : z = zn.val := rfl
    exists zn.toNat + 1
    rw [r,←ZFNat.lt_def,Nat.cast_add,Nat.cast_one,ZFNat.toNat_eq,ZFNat.add_one_eq_succ]
    exact ZFNat.lt_succ
  · rintro ⟨i, z_in_i⟩
    exact ZFNat.mem_Nat_of_mem_mem_Nat (i : ZFNat).prop z_in_i

theorem not_finite_chosen_function_IsFunc_iUnion (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
    : (⋃ n : ℕ, (n : ZFNat)).IsFunc (⋃ _ : ℕ, A) (A.not_finite_chosen_function not_finite) := by
  have uA : A = ⋃ _ : ℕ, A := by ext z ; rw [mem_iUnion, exists_const]
  conv => enter [3] ; rw [not_finite_chosen_function]
  apply isFunc_of_iUnion_of_isFunc
  · intro i
    exact Exists.choose <| Subtype.prop <| A.not_finite_chosen_function_partial not_finite i
  · intro i j
    refine Or.imp ?_ ?_  <| Nat.le_or_ge i j
    <;> intro cmp
    <;> exact A.not_finite_chosen_function_partial_nested not_finite cmp

theorem not_finite_chosen_function_IsInjective_iUnion (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective) :
    (not_finite_chosen_function A not_finite
    ).IsInjective (not_finite_chosen_function_IsFunc_iUnion A not_finite) := by
  conv_lhs => rw [not_finite_chosen_function]
  apply isInjective_of_iUnion_of_isInjective
  · intro i j
    refine Or.imp ?_ ?_  <| Nat.le_or_ge i j
    <;> intro cmp
    <;> exact A.not_finite_chosen_function_partial_nested not_finite cmp
  · intro i
    exact Exists.choose_spec <| Subtype.prop <| A.not_finite_chosen_function_partial not_finite i

theorem not_finite_chosen_function_IsFunc (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective)
    : Nat.IsFunc A (A.not_finite_chosen_function not_finite) := by
  have uA : A = ⋃ _ : ℕ, A := by ext z ; rw [mem_iUnion, exists_const]
  conv =>
    congr
    · rw [Nat_as_union_of_finite_intervals]
    · rw [uA]
    · skip
  exact not_finite_chosen_function_IsFunc_iUnion A not_finite

theorem not_finite_chosen_function_IsInjective (A : ZFSet)
  (not_finite :
    ∀ (n : ZFNat) (f : ZFSet) (hf : A.IsFunc n f), ¬ f.IsInjective) :
    (not_finite_chosen_function A not_finite
    ).IsInjective (not_finite_chosen_function_IsFunc A not_finite) := by
  generalize_proofs hf
  have equiv :
    (⋃ n : ℕ, (n : ZFNat)).IsFunc (⋃ _ : ℕ, A) (A.not_finite_chosen_function not_finite)
    = Nat.IsFunc A (A.not_finite_chosen_function not_finite) := by
    ext
    have uA : A = ⋃ _ : ℕ, A := by ext z ; rw [mem_iUnion, exists_const]
    conv_rhs =>
      congr
      · rw [Nat_as_union_of_finite_intervals]
      · rw [uA]
      · skip
  have solution := not_finite_chosen_function_IsInjective_iUnion A not_finite
  fail_if_success exact solution
  sorry
end NotFiniteChosenFunction

theorem isInfinite_not_isFinite (A : ZFSet) : A.isInfinite = ¬ A.IsFinite := by
  unfold isInfinite IsFinite
  push Not
  apply propext
  constructor
  · rintro ⟨f, hf, hif⟩ n g n_mem_Nat hg
    let h := composition g f Nat A n
    let hh: Nat.IsFunc n h := IsFunc_of_composition_IsFunc (mem_funs.mp hg) hf
    by_contra hig
    have hih := hif.composition_of_injective hig
    exact all_nat_finite ⟨n, n_mem_Nat⟩ h hh hih
  · intro not_finite
    simp_rw [mem_funs] at not_finite
    replace not_finite := (fun (n : ZFNat) f => not_finite n.val f n.prop)
    have hchosen  := not_finite_chosen_function_IsFunc A not_finite
    have hchoseni := not_finite_chosen_function_IsInjective A not_finite
    set chosen := A.not_finite_chosen_function not_finite
    exists chosen, hchosen
end ZFSet
