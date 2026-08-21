import Mathlib.SetTheory.ZFC.Basic
import ZFLean.Basic


namespace ZFSet

def isGraph (G : ZFSet) := ∀ z ∈ G, ∃ (x y : ZFSet), x.pair y = z

abbrev Graph := Subtype isGraph

namespace Graph

theorem isGraph_of_union_of_pairs {E : ZFSet} {f₁ f₂ : E → ZFSet} :
    isGraph (⋃ (x : E), {(f₁ x).pair (f₂ x)}) := by
  intro d
  simp_rw [mem_iUnion, mem_singleton]
  rintro ⟨p, rfl⟩
  simp_rw [pair_inj, exists_eq_right, exists_eq]

theorem isGraph_of_sep_prod {E F : ZFSet} {f : ZFSet → Prop} :
    isGraph ((E.prod F).sep f) := by
  intro p
  rw [mem_sep, mem_prod]
  rintro ⟨⟨x,_,y,_,rfl⟩,_⟩
  exact ⟨x, y, rfl⟩

theorem mem_graph {G : Graph} {p : ZFSet} :
  p ∈ G.val ↔ ∃ (x y : ZFSet), x.pair y = p ∧ x.pair y ∈ G.val := by
  have w := G.prop p
  constructor
  · intro memG
    obtain ⟨x, y, rfl⟩ := G.prop p memG
    exact ⟨x, y, rfl, memG⟩
  · rintro ⟨x, y, rfl, memG⟩
    exact memG

theorem exists_mem_graph {G : Graph} (P : ZFSet → Prop) :
    (∃ (p : G.val), P p.val) ↔ ∃ x y : ZFSet, x.pair y ∈ G.val ∧ P (x.pair y) := by
  simp_rw [Subtype.exists]
  conv => enter [1, 1, _] ; rw [exists_prop,mem_graph]
  simp_rw [existsAndEq, true_and]

@[ext]
theorem ext {G F : Graph} : (∀ x y : ZFSet, x.pair y ∈ G.val ↔ x.pair y ∈ F.val) → G = F := by
  intro h
  ext z
  conv =>
    conv => congr <;> rw [mem_graph]
    enter [1, 1, x, 1, y]
    rw [h x y]

theorem subgraph_iff {G F : Graph} :
    G.val ⊆ F.val ↔ ∀ x y : ZFSet, x.pair y ∈ G.val → x.pair y ∈ F.val := by
  rw [subset_def]
  conv =>
    enter [1, z]
    rw [mem_graph, mem_graph]
  constructor
  · intro h x y memG
    specialize @h (x.pair y) ⟨x, y, rfl, memG⟩
    conv at h => enter [1, _, 1, _] ; rw [eq_comm, pair_inj]
    obtain ⟨_,_,⟨rfl,rfl⟩,h⟩ := h
    exact h
  · intro h _
    rintro ⟨x, y, rfl, memG⟩
    specialize h x y memG
    exact mem_graph.mp h

noncomputable def ran (G : ZFSet) : ZFSet := (⋃ (z : G), {z.val.π₁})
noncomputable def dom (G : ZFSet) : ZFSet := (⋃ (z : G), {z.val.π₂})

theorem prod_right_eq_ran (A B : ZFSet) (h : B ≠ ∅) : ran (A.prod B) = A := by
  ext z
  rw [ran, mem_iUnion]
  simp only [mem_singleton, Subtype.exists, mem_prod, exists_prop, ↓existsAndEq, and_true, π₁_pair,
    exists_and_right, exists_and_left, exists_eq_right', and_iff_left_iff_imp]
  intro _
  exact nonempty_exists_iff.mp h

theorem prod_left_eq_dom (A B : ZFSet) (h : A ≠ ∅) : dom (A.prod B) = B := by
  ext z
  rw [dom, mem_iUnion]
  simp only [mem_singleton, Subtype.exists, mem_prod, exists_prop, ↓existsAndEq, and_true, π₂_pair,
    exists_eq_right', exists_and_right, and_iff_right_iff_imp]
  intro _
  exact nonempty_exists_iff.mp h

theorem mem_ran {G : Graph} {x : ZFSet} : x ∈ ran G.val ↔ ∃ y, x.pair y ∈ G.val := by
  simp_rw [ran, mem_iUnion, mem_singleton, exists_mem_graph (x = ·.π₁), π₁_pair,
    exists_and_right, exists_eq_right']
theorem mem_dom {G : Graph} {y : ZFSet} : y ∈ dom G.val ↔ ∃ (x : ZFSet), x.pair y ∈ G.val := by
  simp_rw [dom, mem_iUnion, mem_singleton, exists_mem_graph (y = ·.π₂), π₂_pair]
  rw [exists_comm]
  simp_rw [exists_and_right, exists_eq_right']

theorem graph_is_rel_dom_range (G : Graph) : G.val ⊆ (ran G.val).prod (dom G.val) := by
  intro z h
  obtain ⟨x, y, rfl⟩ := G.prop z h
  rw [pair_mem_prod, mem_ran, mem_dom]
  exact ⟨⟨y,h⟩,x,h⟩

noncomputable instance : Inv Graph where
  inv G := ⟨⋃ (p : G.val), {p.val.π₂.pair p.val.π₁}, isGraph_of_union_of_pairs⟩

theorem mem_inv_iff (G : Graph) (x y : ZFSet) : x.pair y ∈ G⁻¹.val ↔ y.pair x ∈ G.val := by
  rw [Inv.inv, instInv]
  dsimp only
  simp_rw [mem_iUnion, mem_singleton, exists_mem_graph (fun i => x.pair y = i.π₂.pair i.π₁),
    π₁_pair, π₂_pair, pair_inj, existsAndEq, and_true]

theorem inv_involutive : Function.Involutive instInv.inv := by
  intro G
  ext x y
  rw [mem_inv_iff, mem_inv_iff]

theorem inv_ran {G : Graph} : ran (G⁻¹.val) = dom G.val := by
  ext y
  rw [mem_ran]
  conv => enter [1, 1, x] ; rw [mem_inv_iff]
  rw [mem_dom]

theorem inv_dom {G : Graph} : dom (G⁻¹.val) = ran G.val := by
  rw [←@inv_involutive G, inv_ran, inv_involutive]

def isSymmetric (G : Graph) := G = G⁻¹

theorem isSymmetric_iff (G : Graph) :
  G.isSymmetric ↔ ∀ x y : ZFSet, x.pair y ∈ G.val ↔ y.pair x ∈ G.val := by
  rw [isSymmetric, Graph.ext_iff]
  conv =>
    enter [1, x, y]
    rw [mem_inv_iff]

noncomputable def composition (G F : Graph) : Graph :=
  ⟨⋃ (t : (F.val.prod G.val).sep fun t => t.π₂.π₁  = t.π₁.π₂), {t.val.π₁.π₁.pair t.val.π₂.π₂},
    isGraph_of_union_of_pairs⟩

scoped infixr:90 " ∘ᶻ "  => composition

theorem mem_composition_iff (G F : Graph) (x z : ZFSet) :
    x.pair z ∈ (G ∘ᶻ F).val ↔ ∃ y : ZFSet, x.pair y ∈ F.val ∧ y.pair z ∈ G.val := by
  simp_rw [(· ∘ᶻ ·), mem_iUnion, mem_singleton, Subtype.exists, mem_sep, exists_prop, mem_prod,
    existsAndEq, and_true, π₁_pair, π₂_pair]
  conv =>
    enter [1,1,a,1,b]
    rw [mem_graph,mem_graph]
  simp_rw [existsAndEq, true_and, π₁_pair, π₂_pair, existsAndEq, and_true, pair_inj, existsAndEq,
    and_true]

def isTransitive (G : Graph) := (G ∘ᶻ G).val ⊆ G

theorem isTransitive_iff (G : Graph) :
    G.isTransitive ↔ ∀ x y z : ZFSet, x.pair y ∈ G.val ∧ y.pair z ∈ G.val → x.pair z ∈ G.val := by
  simp_rw [isTransitive, subgraph_iff, mem_composition_iff, forall_exists_index]
  conv =>
    enter [1, x]
    rw [forall_comm]

noncomputable def diag (E : ZFSet) : Graph :=
  ⟨⋃ (x : E), {x.val.pair x.val}, isGraph_of_union_of_pairs⟩

theorem mem_diag_iff (E x y : ZFSet) : x.pair y ∈ (diag E).val ↔ x = y ∧ x ∈ E := by
  simp_rw [diag, mem_iUnion, Subtype.exists, exists_prop, mem_singleton, pair_inj, existsAndEq,
    true_and]
  rw [and_comm, eq_comm]

def isFunctional (G : Graph) := G ∘ᶻ G⁻¹ = (diag <| dom G)

theorem isFunctional_iff (G : Graph) :
    G.isFunctional ↔ ∀ x y₁ y₂ : ZFSet, x.pair y₁ ∈ G.val ∧ x.pair y₂ ∈ G.val → y₁ = y₂ := by
  simp_rw [isFunctional, Graph.ext_iff, mem_composition_iff, mem_diag_iff, mem_inv_iff, mem_dom]
  constructor
  · rintro h x y₁ y₂ ⟨memG₁, memG₂⟩
    specialize h y₁ y₂
    exact And.left <| h.mp ⟨x, memG₁, memG₂⟩
  · intro h y₁ y₂
    constructor
    · rintro ⟨x, memG₁, memG₂⟩
      constructor
      · exact h x y₁ y₂ ⟨memG₁, memG₂⟩
      · exact ⟨x, memG₁⟩
    · rintro ⟨rfl, memDom⟩
      conv => enter [1, x] ; rw [and_self]
      exact memDom

def isInjective (G : Graph) := G⁻¹ ∘ᶻ G = (diag <| ran G)

theorem isInjective_iff_inv_isFunctional {G : Graph} : G.isInjective ↔ G⁻¹.isFunctional := by
  rw [isInjective, isFunctional, inv_involutive, inv_dom]

theorem isInjective_iff (G : Graph) :
    G.isInjective ↔ ∀ y x₁ x₂ : ZFSet, x₁.pair y ∈ G.val ∧ x₂.pair y ∈ G.val → x₁ = x₂ := by
  rw [←G.inv_involutive, isInjective_iff_inv_isFunctional, inv_involutive]
  conv => enter [2, _, _, _, 1] ; congr <;> rw [mem_inv_iff]
  rw [isFunctional_iff]


def isReflexive (G : Graph) (E : ZFSet) := (diag E).val ⊆ G.val

theorem isReflexive_iff (G : Graph) (E : ZFSet) :
    G.isReflexive E ↔ ∀ x : ZFSet, x ∈ E → x.pair x ∈ G.val := by
  simp_rw [isReflexive, subgraph_iff, mem_diag_iff, and_imp, forall_eq']

def isEquivalence (G : Graph) (E : ZFSet) := G.isSymmetric ∧ G.isTransitive ∧ G.isReflexive E

def toRelation (G : Graph) (E : ZFSet) : E → E → Prop := fun (x y : E) => x.val.pair y.val ∈ G.val

theorem Equivalence_of_isEquivalence (G : Graph) {E : ZFSet} :
    G.isEquivalence E → Equivalence (G.toRelation E) := by
  unfold toRelation
  rw [isEquivalence, isSymmetric_iff, isTransitive_iff, isReflexive_iff]
  rintro ⟨hs, ht, hr⟩
  constructor <;> grind

theorem isEquivalence_iff_Equivalence (G : Graph) (E : ZFSet) (h : E = ran G.val ∧ E = dom G.val) :
    G.isEquivalence E ↔ Equivalence (G.toRelation E) := by
  rw [iff_iff_implies_and_implies, and_iff_right <| Equivalence_of_isEquivalence G,
    isEquivalence, isSymmetric_iff, isTransitive_iff, isReflexive_iff]
  unfold toRelation
  rintro ⟨hr, hs, ht⟩
  simp_rw [Subtype.forall] at hr hs ht
  have memE (x y : ZFSet) : x.pair y ∈ G.val → x ∈ E ∧ y ∈ E := by
    intro memG
    apply graph_is_rel_dom_range G at memG
    rw [←h.left, ←h.right, pair_mem_prod] at memG
    exact memG
  grind

def fromRelation (E : ZFSet) (r : ZFSet → ZFSet → Prop) : Graph :=
    ⟨(E.prod E).sep fun p => r p.π₁ p.π₂, isGraph_of_sep_prod⟩

theorem mem_fromRelation (E : ZFSet) (r : ZFSet → ZFSet → Prop) (x y : ZFSet) :
    x.pair y ∈ (fromRelation E r).val ↔ x ∈ E ∧ y ∈ E ∧ r x y := by
  simp_rw [fromRelation, mem_sep, mem_prod, pair_inj, existsAndEq, and_true, π₁_pair, π₂_pair,
    and_assoc]

theorem isEquivalence_of_Equivalence {E : ZFSet} (r : ZFSet → ZFSet → Prop) :
    @Equivalence E (r · ·) → (Graph.fromRelation E r).isEquivalence E := by
  rintro ⟨r, s, t⟩
  simp_rw [Subtype.forall] at r s t
  unfold isEquivalence
  simp_rw [isSymmetric_iff, isTransitive_iff, isReflexive_iff, mem_fromRelation]
  grind

theorem Equivalence_iff_isEquivalence {E : ZFSet} (r : ZFSet → ZFSet → Prop) :
    @Equivalence E (r · ·) ↔ (Graph.fromRelation E r).isEquivalence E := by
  rw [iff_iff_implies_and_implies, and_iff_right <| isEquivalence_of_Equivalence r]
  simp_rw [isEquivalence, isSymmetric_iff, isTransitive_iff, isReflexive_iff, mem_fromRelation]
  intro ⟨hs, ht, hr⟩
  constructor <;> simp_rw [Subtype.forall] <;> grind

open Classical in
def extended_relation {E : ZFSet} (r : (E → E → Prop)) : ZFSet → ZFSet → Prop :=  fun x y =>
  if h : x ∈ E ∧ y ∈ E then r ⟨x, h.left⟩ ⟨y, h.right⟩
  else if x ∉ E ∧ y ∉ E then True -- required to keep symmetry/reflexitivity
  else False

theorem extended_relation.Equivalence_iff {E : ZFSet} (r : (E → E → Prop)) :
    Equivalence r ↔ @Equivalence E (extended_relation r · ·) := by
  constructor <;> rintro ⟨r, s, t⟩ <;> constructor
  <;> simp_rw [extended_relation, Subtype.forall] at ⊢ r s t <;> grind

def Equiv_Equivalence_isEquivalence {E : ZFSet} :
    Equiv {r : (E → E → Prop) // Equivalence r}
      { G : Graph // G.isEquivalence E ∧ E = ran G.val ∧ E = dom G.val} where
  toFun r := ⟨fromRelation E <| extended_relation r.val, by
    exists isEquivalence_of_Equivalence (extended_relation r.val)
        <| (extended_relation.Equivalence_iff r.val).mp r.prop
    simp_rw [ZFSet.ext_iff, mem_ran, mem_dom]
    constructor
    all_goals
      intro p
      simp_rw [mem_fromRelation, extended_relation]
      constructor
      · intro memE
        exists p, memE, memE
        rw [dif_pos ⟨memE, memE⟩]
        exact r.prop.refl _
      · rintro ⟨_, mem1, mem2,_⟩
        assumption
  ⟩
  invFun G := ⟨G.val.toRelation E, Equivalence_of_isEquivalence G.val G.prop.left⟩
  left_inv r := by
    ext x y
    dsimp only
    rw [toRelation, mem_fromRelation, and_iff_right x.prop, and_iff_right y.prop, extended_relation,
      dif_pos ⟨x.prop, y.prop⟩]
  right_inv G := by
    ext x y
    dsimp only
    rw [mem_fromRelation, extended_relation]
    constructor
    · rintro ⟨mx, my, h⟩
      rw [dif_pos ⟨mx, my⟩, toRelation] at h
      exact h
    · have h := G.prop.left
      rw [isEquivalence] at h
      intro p
      have x_in_E := mem_ran.mpr ⟨y, p⟩
      rw [←ZFSet.ext_iff.mp G.prop.right.left x] at x_in_E
      have y_in_E := mem_dom.mpr ⟨x, p⟩
      rw [←ZFSet.ext_iff.mp G.prop.right.right y] at y_in_E
      exists x_in_E, y_in_E
      rw [dif_pos ⟨x_in_E, y_in_E⟩, toRelation]
      exact p

end Graph

noncomputable def ZQuotient (E : ZFSet) (G : Graph) : ZFSet :=
  ⋃ (x : E),  {E.sep fun y => x.val.pair y ∈ G.val}

namespace ZQuotient
/-! TODO : write some facts about classes/elements (eg : they form a partition, the quotient is the
  the same as the  set of maximal subsets of the dom × range product that contain equivalent
  elements).
-/

noncomputable def witness {E : ZFSet} {G : Graph} (C : E.ZQuotient G) : E :=
  match C with
  | ⟨c, hclass⟩ => by
    rw [ZQuotient, mem_iUnion] at hclass
    exact hclass.choose

theorem witness_of_eclass_mem_eclass {E : ZFSet} {G : Graph} {GisEquiv : G.isEquivalence E}
  (C : E.ZQuotient G) : (witness C).val ∈ C.val := by
  unfold witness
  obtain ⟨c, hclass⟩ := C
  rw [ZQuotient, mem_iUnion] at hclass
  dsimp only
  change hclass.choose.val ∈ c
  have h := hclass.choose_spec
  rw [mem_singleton, ZFSet.ext_iff] at h
  apply Iff.mpr <| h hclass.choose
  rw [mem_sep]
  exists hclass.choose.prop
  obtain ⟨_,_,hr⟩ := GisEquiv
  rw [Graph.isReflexive_iff] at hr
  apply hr hclass.choose.val hclass.choose.prop


def toSetoid {E : ZFSet} {G : Graph} (GisEquiv : G.isEquivalence E) : Setoid E where
  r :=  G.toRelation E
  iseqv := G.Equivalence_of_isEquivalence GisEquiv

noncomputable def equivZQuotient {E : ZFSet} {G : Graph} (GisEquiv : G.isEquivalence E) :
  Equiv (ZQuotient E G) (Quotient <| toSetoid  GisEquiv) where
  toFun h := ⟦witness h⟧
  invFun w := ⟨E.sep fun w' => w.out.val.pair w' ∈ G.val, by
    rw [ZQuotient, mem_iUnion]
    exists w.out
    rw [mem_singleton]⟩
  left_inv := by
    rintro ⟨c, hc⟩
    rw [ZQuotient, mem_iUnion] at hc
    let hw'' := hc.choose_spec
    rw [mem_singleton, ZFSet.ext_iff] at hw''
    simp only [Subtype.mk.injEq]
    ext w'
    rw [mem_sep, hw'', mem_sep]
    unfold witness
    change _ ∧ ⟦hc.choose⟧.out.val.pair w' ∈ G.val ↔ _
    constructor
    · rintro ⟨w'_in_E, related⟩
      lift w' to E using w'_in_E
      exists w'.prop
      change (toSetoid  GisEquiv).r hc.choose w'
      rw [← @Quotient.eq]
      change (toSetoid GisEquiv).r ⟦hc.choose⟧.out w' at related
      rw [← @Quotient.eq, Quotient.out_eq] at related
      exact related
    · rintro ⟨w'_in_E, related⟩
      lift w' to E using w'_in_E
      exists w'.prop
      change (toSetoid  GisEquiv).r hc.choose w' at related
      rw [← @Quotient.eq] at related
      change (toSetoid  GisEquiv).r ⟦hc.choose⟧.out w'
      rw [← @Quotient.eq, Quotient.out_eq]
      exact related
  right_inv := by
    intro w
    dsimp only
    simp_rw [Quotient.mk_eq_iff_out]
    change (G.toRelation E) _ w.out
    generalize_proofs h
    set C : E.ZQuotient G := ⟨_, h⟩ with hc
    rw [Graph.toRelation]
    have wit_mem_c := @witness_of_eclass_mem_eclass _ _ GisEquiv C
    rw [Subtype.ext_iff, ZFSet.ext_iff] at hc
    obtain ⟨hs, _, _⟩ := GisEquiv
    rw [Graph.isSymmetric_iff] at hs
    rw [hc, mem_sep, hs] at wit_mem_c
    exact wit_mem_c.right

noncomputable def equivQuotientFromRel {E : ZFSet} {r : E → E → Prop} (re : Equivalence r) :
    Equiv
      (Quotient <| toSetoid (Graph.Equiv_Equivalence_isEquivalence ⟨r, re⟩).prop.left)
      (Quotient ⟨r,re⟩) := by
  apply Quotient.congrRight
  unfold toSetoid
  dsimp only
  change ∀ _ _, (Graph.Equiv_Equivalence_isEquivalence.invFun <|
    Graph.Equiv_Equivalence_isEquivalence.toFun _).val _ _ ↔ _
  intro x y
  rw [Graph.Equiv_Equivalence_isEquivalence.left_inv]

noncomputable def equivZQuotientFromRel {E : ZFSet} {r : E → E → Prop} (re : Equivalence r) :
    Equiv (ZQuotient E <| Graph.Equiv_Equivalence_isEquivalence ⟨r, re⟩) (Quotient ⟨r,re⟩) :=
  Equiv.trans
    (equivZQuotient (Graph.Equiv_Equivalence_isEquivalence ⟨r, re⟩).prop.left)
    (equivQuotientFromRel re)

end ZQuotient

end ZFSet
