/-
  # Zorn's lemma #

  Zorn's lemma is a classical set theory result whose proof requires the axiom of choice.
  It states that in a partially ordered set in which every chain is bounded above, there
  is a maximal element.

  For this first exercise, we formalize a proof of Zorn's lemma due to Incatasciato and
  Sánchez Terraf, found in the last section of `https://arxiv.org/pdf/2404.11638`.
  They actually have their own lean4 formalization linked in their paper.
  I've set this up a bit differently from theirs, though.

  For the purposes of learning, we do this proof from (closer to) first principles,
  not using existing mathlib API for `Chain` or bounds. For the same reason, the way things
  are done here is far from optimized. Even so, we adopt a style somewhat similar to mathlib,
  using a lot of 'little' lemmas to abstract definitions.
-/
import Mathlib.Data.Set.Lattice

open Set


-- This line gives us a nonempty type `α` with a partial order `≤` to work with,
-- and makes `C,D,S` default to mean sets in `α` and `c,d,x,y` default to mean elements of `α`.
variable {α : Type*} [Nonempty α] [PartialOrder α] {C D S U: Set α} {b c d x y z : α}

section Bounds

/-- An upper bound for a set `S` is something weakly above everything in `S`. -/
def IsUB (S : Set α) (b : α) := ∀ x ∈ S, x ≤ b

/-- A strict upper bound for a set `S` is something strictly above everything in `S`. -/
def IsStrictUB (S : Set α) (b : α) := ∀ x ∈ S, x < b

/-- Every strict upper bound is also a weak upper bound.
trivial lemmas like the next two are common in mathlib.
The dot in the theorem name means you can use comsspact notation to refer to the results;
if you have `(h : IsStrictUB S b)`, you can write `h.isUB` to quickly prove `IsUB S b`. -/
theorem IsStrictUB.isUB (h : IsStrictUB S b) : IsUB S b := by
  intro x xS
  have h': x < b := by
    apply h
    exact xS
  apply le_of_lt
  exact h'


/- Again, we use dot notation; if `h : IsStrictUB S b`, then `h.not_mem` proves `b ∉ S`.-/
theorem IsStrictUB.not_mem (h : IsStrictUB S b) : b ∉ S := by
contrapose! h
intro hh
let hhh: b < b := by
  apply hh b
  exact h
apply (lt_self_iff_false b).mp
exact hhh

  -- `exact fun hbS ↦ (h b hbS).ne rfl` works as a one-line proof here.

/-- `a : α` is maximal if there are no elements `b : α` with `a < b`-/
def IsMaximal (a : α) := ∀ b, a ≤ b → a = b

end Bounds

section Chain

/-- `C : Set α` is a chain if any of its two members are comparable under `≤` in one direction or
another. -/
def IsChain (C : Set α) : Prop := ∀ x y, x ∈ C → y ∈ C → (x ≤ y ∨ y ≤ x)

theorem isChain_empty : IsChain (∅ : Set α) := by
  -- This proof happens to work even with my garbage definition for `IsChain`.
  -- It should also work without modification for your correct definition.
  simp [IsChain]

/- A lemma to make `IsChain` a little more palatable to work with. -/
theorem IsChain.le_or_le_of_mem_of_mem (hC : IsChain C) (hxC : x ∈ C) (hyC : y ∈ C) :
    x ≤ y ∨ y ≤ x := by
  apply hC
  exact hxC
  exact hyC

example: ∀ p: Prop, p ∨ ¬ p := by
exact fun p ↦ Classical.em p

-- let p := x = y
--  have Op : p ∨ ¬ p := by
--    exact fun p ↦ Classical.em p


/-- We can actually get something stronger. Use the last lemma to prove this. -/
theorem IsChain.le_or_lt_of_mem_of_mem (hC : IsChain C) (hxC : x ∈ C) (hyC : y ∈ C) :
x ≤ y ∨ y < x := by
  have lem : x ≤ y ∨ y ≤ x := by
    apply IsChain.le_or_le_of_mem_of_mem hC hxC hyC
  by_cases h : x = y
  · left
    rw [h]
  --apply le_rfl
  rcases lem with a | b -- why rcases works but cases does not? this is for naming
  -- answer is that rcases uses different notation than cases https://leanprover.github.io/theorem_proving_in_lean4/tactics.html
  · exact Or.inl a
  have p : y < x := by
    apply lt_of_le_of_ne
    exact b
    contrapose! h
    apply symm
    exact h
  right
  exact p

theorem IsChain.insert_UB (hC : IsChain C) (hb : IsUB C b) : IsChain (insert b C) := by
  unfold IsChain at hC ⊢
  unfold IsUB at hb
  intro x y xIC yIC
  have h : ∀ z , z ∈ (insert b C) → ¬ (z ∈ C) → z=b := by
    intro z zI zC
    rcases zI with A | B
    exact A
    contradiction
  by_cases xiC : x ∈ C
  · by_cases yC : y ∈ C
    · apply hC ; exact xiC ; exact yC
    left
    have yb : y=b := by
      apply h y yIC yC
    rw [yb] ; apply hb ; exact xiC
  have xb : x=b := by apply h x xIC xiC
  by_cases yC : y ∈ C
  right ; rw [xb] ; apply hb ; exact yC
  have yb : y=b := by
      apply h y yIC yC
  left; rw [xb,yb]

-- Can you prove this in one line using a term?
theorem IsChain.subset_isChain {C S : Set α} (hC : IsChain C) (hSC : S ⊆ C) : IsChain S := by
  intro x y hx hy
  unfold IsChain at hC
  exact hC x y (mem_of_mem_of_subset hx hSC) (mem_of_mem_of_subset hy hSC)

end Chain
section Segment

/-- `IsSegmentOf S C` means that `C` is a chain, `S` is contained in `C`, and something else.
As a conjunction of three separate conditions, definitions like this can be a little unwieldy
to work with.
The lemmas after this give more pleasant ways to interact with the definition. -/
def IsSegmentOf (S C : Set α) := (S ⊆ C) ∧ (IsChain C) ∧ (∀ x y, x ∈ C → y ∈ S → x ≤ y → x ∈ S)

theorem IsSegmentOf.subset {S C : Set α} (h : IsSegmentOf S C) : S ⊆ C :=
  h.1
  -- If `h : P ∧ Q` then `h.1` or `h.left` means `P`.

theorem IsSegmentOf.chain_right (h : IsSegmentOf S C) : IsChain C :=
  h.2.1
  -- This proof should be five characters long.

theorem IsSegmentOf.chain_left (h : IsSegmentOf S C) : IsChain S := by
  apply IsChain.subset_isChain
  exact h.2.1
  exact h.1
  -- Try to prove this by combining previous lemmas rather than by diving into definitions.

theorem IsSegmentOf.mem_of_mem_of_le {x y : α} (h : IsSegmentOf S C) (hx : x ∈ C) (hy : y ∈ S)
    (hxy : x ≤ y) : x ∈ S :=
  h.2.2 x y hx hy hxy

theorem IsChain.isSegmentOf_self (h : IsChain C) : IsSegmentOf C C := by
  unfold IsSegmentOf
  -- this is too easy to write a proof. `tauto` can solve it.
  tauto

theorem IsSegmentOf.subset_right (h : IsSegmentOf S C) (hD : IsChain D) (hSD : S ⊆ D)
    (hDC : D ⊆ C) : IsSegmentOf S D := by
  unfold IsSegmentOf
  -- Here you have a goal of the form `P ∧ Q ∧ R`. You can split into subgoals either
  -- by typing `constructor` in two places, or with a `refine` like below.
  refine ⟨?_, ?_, ?_⟩
  · exact hSD
  · exact hD
  intro x y hxD hyS hxy
  exact h.mem_of_mem_of_le (mem_of_mem_of_subset hxD hDC) hyS hxy
-- exact ⟨hSD, hD, h.mem_of_mem_of_le (mem_of_mem_of_subset hsD hDC) hyS hxy⟩


-- even this can be a one-liner.
theorem IsSegmentOf.trans (h : IsSegmentOf S C) (h' : IsSegmentOf C D) : IsSegmentOf S D := by
refine ⟨Subset.trans h.1 h'.1 ,h'.2.1,?_⟩
exact fun x y xD yS xley ↦ h.2.2 x y (h'.2.2 x y xD (mem_of_mem_of_subset yS h.1) xley) yS xley
/- Is a one line really the best here???
I feel like it is way more clear using lemmas
refine ⟨Subset.trans h.1 h'.1 , h'.2.1,?_⟩
intro x y xD yS xley
have lem : y ∈ C := by
  apply (mem_of_mem_of_subset yS h.1)
have lemm: x ∈ C := by
  exact h'.2.2 x y xD lem xley
exact h.2.2 x y lemm yS xley
-/

-- exact fun h h' ↦ ⟨ ⟩
--  refine ⟨Subset.trans h.1 h'.1 , h'.2.1, sorry⟩ -- I have to solve this with fun  fun x y ?_

theorem IsSegmentOf.exists_strictUB_mem_of_ne (h : IsSegmentOf S U) (hne : S ≠ U) :
    ∃ d ∈ U, IsStrictUB S d := by
  -- since `S` is a strict subset of `U`, there is some `d ∈ U \ S`. Any such `d` will work.
  have h_ssubset : S ⊂ U := by
    exact Set.ssubset_iff_subset_ne.mpr ⟨h.1, hne⟩
  obtain ⟨d, hdU, hdS⟩ := exists_of_ssubset h_ssubset
  use d, hdU
  intro c hcS

  -- Because `U` is a chain, we either have `c ≤ d` or `d < c`.
  have le_or_lt : d ≤ c ∨ c < d := by
    exact IsChain.le_or_lt_of_mem_of_mem h.2.1 hdU (mem_of_mem_of_subset hcS h.1)

  obtain (hdc | hcd) := le_or_lt
  · -- Use the fact that `S` is a segment of `U` to get a contradiction in this case.
    have NhdU : d ∈ S := by exact (h.2.2 d c hdU hcS hdc)
    contradiction
  exact hcd

/- This is a theorem about an arbitrary union of segments. So `Ss` (pronounced 'esses`)
is a set of sets, each of which is a segment by hypothesis.
There are different flavours of arbitrary union in lean;
the one here `⋃₀ Ss` means the union of the sets in `Ss`, where `Ss` is a set of sets
(as opposed to a list or a sequence of sets one might take the union of).
There is no need to actually unfold the definition of `⋃₀`;
the mathlib lemmas `sUnion_subset_iff` and `mem_sUnion` are enough to interact with it.
I've left the proof in full here, but make sure you follow it. -/
theorem IsChain.sUnion_segmentOf {C : Set α} (hC : IsChain C) (Ss : Set (Set α))
    (h_Ss : ∀ S ∈ Ss, IsSegmentOf S C) : IsSegmentOf (⋃₀ Ss) C := by
  refine ⟨?_,?_,?_⟩
  · rw [sUnion_subset_iff]
    intro S hS
    exact (h_Ss S hS).subset
  · exact hC
  simp only [mem_sUnion, forall_exists_index, and_imp]
  intro x y hx S hS hy hxy
  use S
  refine ⟨hS, ?_⟩
  exact (h_Ss S hS).mem_of_mem_of_le hx hy hxy

end Segment

section Good
/-
Here we are departing more from the way we tend to write proofs on paper.
Definitions of chains, bounds, segments are standard enough that separating them from the
main proof, and having definitions and lemmas about them separately makes sense.

But here we are going to do the same with the technical notion of a 'Good' chain that appears only
in the details of the proof in the paper. It generally makes for less chaotic code to write things
this way - even when an auxiliary lemma will only be used once inside a proof,
it can be nice to separate out the lemma into its own little package.
It increases modularity, readability, and usually also performance.
-/

/-- `GoodWRT b C` means that `C` is a chain, and `S ∪ {b S}` is a segment of `C` for every proper
segment `S` of `C`.
(It wouldn't be unreasonable to write a couple of API lemmas like `GoodWRT.isChain` here to avoid
having to use this definition directly, but the definition is technical enough that I didn't
bother here. Do so if you'd like though! ) -/
def GoodWRT (b : Set α → α) (C : Set α) :=
    IsChain C ∧ ∀ S, IsSegmentOf S C → S ≠ C → IsSegmentOf (insert (b S) S) C

/- The statement that the authors call 'Comparability' of good chains. -/
theorem goodWRT_comparability {C C' : Set α} {b : Set α → α} (hb : ∀ C, IsChain C → b C ∉ C)
    (hC : GoodWRT b C) (hC' : GoodWRT b C') : IsSegmentOf C' C ∨ IsSegmentOf C C' := by
  -- consider the union of all the sets that are segments of both `C` and `C'`.
  let mutualSegs := {S | IsSegmentOf S C ∧ IsSegmentOf S C'}
  let U := ⋃₀ mutualSegs

  have hUC : IsSegmentOf U C := by
    refine ⟨?_, hC.1,?_⟩
    rw [sUnion_subset_iff]
    intro S hS
    obtain ⟨SsC,_⟩ := hS
    exact SsC.1
    intro x y xC yU xley
    --apply mem_sUnion.mp at yU
    let ⟨S,hhS⟩ := yU
    let ⟨hS,yS⟩ := hhS
    let ⟨aH,_⟩ := hS
    apply mem_sUnion.mpr
    use S
    exact ⟨hS,aH.2.2 x y xC yS xley⟩
    --exact fun x y xC yU xley ↦ (mem_of_mem_of_subset hcS h.1)
  have hUC' : IsSegmentOf U C' := by
    refine ⟨?_, hC'.1,?_⟩
    rw [sUnion_subset_iff]
    intro S hS
    obtain ⟨_,SsC'⟩ := hS
    exact SsC'.1
    intro x y xC yU xley
    --apply mem_sUnion.mp at yU
    let ⟨S,hhS⟩ := yU
    let ⟨hS,yS⟩ := hhS
    let ⟨_,bH⟩ := hS
    apply mem_sUnion.mpr
    use S
    exact ⟨hS,bH.2.2 x y xC yS xley⟩

  -- If `U = C` or `U = C'`, there isn't much to prove.
  by_cases hUC_eq : U = C
  · right; rw [←hUC_eq]; assumption
  by_cases hUC'_eq : U = C'
  · left; rw [←hUC'_eq]; assumption

  -- Otherwise, we chase a contradiction.
  exfalso

  -- use `hC` and `hC'` to prove the following.
  have hCseg : IsSegmentOf (insert (b U) U) C := by
    apply hC.2 U hUC hUC_eq

  have hC'seg : IsSegmentOf (insert (b U) U) C' := by
    apply hC'.2 U hUC' hUC'_eq

  apply hb _ hUC.chain_left
  have hbU : insert (b U) U ⊆ U := by
    -- use the definition of `U` and `subset_sUnion_of_mem` to prove this
    apply subset_sUnion_of_mem
    exact ⟨hCseg,hC'seg⟩


  rw [insert_subset_iff] at hbU
  exact hbU.1

theorem GoodWRT_sUnion_chain (b : Set α → α) (hb : ∀ C, IsChain C → b C ∉ C) :
    IsChain (⋃₀ {C : Set α | GoodWRT b C}) := by
  intro x y hx hy
  simp only [mem_sUnion, mem_setOf_eq] at hx hy
  obtain ⟨Sx, hSx, hxSx⟩ := hx
  obtain ⟨Sy, hSy, hySy⟩ := hy
  obtain (h | hh) := goodWRT_comparability hb hSx hSy
  · -- use the fact that `Sx` is a chain.
    have hySx : y ∈ Sx := by
      exact mem_of_mem_of_subset hySy h.1
    exact IsChain.le_or_le_of_mem_of_mem hSx.1 hxSx hySx
  -- use the fact that `Sy` is a chain.
  have hxSy : x ∈ Sy := by
    exact mem_of_mem_of_subset hxSx hh.1
  exact IsChain.le_or_le_of_mem_of_mem hSy.1 hxSy hySy



/-- If `b` is a function that chooses a strict upper bound for each chain `C`,
then inserting `b C` to `C` preserves goodness of `C`.
This lemma is implicitly asserted without proof in the last line of the proof in the paper,
but takes a little thought to prove... -/
theorem GoodWRT.insert_ub (b : Set α → α) (hb : ∀ C, IsChain C → IsStrictUB C (b C))
    (h : GoodWRT b C) : GoodWRT b (insert (b C) C) := by

  -- I wouldn't recommmend unfolding all the definitions here.
  have h_chain : IsChain (insert (b C) C) := by
    apply IsChain.insert_UB h.1
    exact (hb C h.1).isUB

  constructor
  · exact h_chain

  intro S hSeg hne
  -- We will argue that `S` is a proper segment of `C`.
  -- If `S = C`, we can use `isSegmentOf_self`.
  obtain (hSC | hSneC) := eq_or_ne S C
  · rw [hSC]
    exact hSeg.chain_right.isSegmentOf_self

  -- First show that `S ⊆ C`.
  -- Since `S` is contained in `C ∪ {b C}`, this amounts to showing that `b C ∉ S`.
  have hbCS : b C ∉ S := by
    -- suppose that `b C ∈ S`,...
    intro hbCS
    -- we will derive a contradiction to `hne` by showing that `S = insert (b C) C`.
    apply hne
    -- containment is easy in one direction
    refine hSeg.subset.antisymm (insert_subset hbCS ?_)

    -- for the other, use `hSeg` and the fact that `b` picks upper bounds.
    intro c cC
    have clebC : c ≤ (b C) := by
      exact (hb C h.1).isUB c cC
    refine IsSegmentOf.mem_of_mem_of_le hSeg (?_) hbCS clebC
    exact mem_insert_of_mem (b C) cC

  have hS := hSeg.subset
  rw [subset_insert_iff_of_not_mem hbCS] at hS

  -- Now show that `S` is a segment of `C`.
  have hSC : IsSegmentOf S C := by
    refine ⟨hS,h.1,?_⟩
    intro x y xC yS xley
    apply IsSegmentOf.mem_of_mem_of_le hSeg (mem_insert_of_mem (b C) xC) yS xley

  -- Now use the goodness of `S`.
  have hSeg' := h.2 S hSC hSneC

  refine ⟨?_, ?_, ?_⟩
  · exact hSeg'.subset.trans (subset_insert _ _)
  · exact h_chain

  intro x y hx hy hxy

  -- Split into cases depending on whether `x = b C` or `x ∈ C`
  simp_rw [mem_insert_iff] at hx
  obtain (rfl | hxC) := hx
  · -- Since `b C ≤ y ∈ S ∪ {b s} ⊆ C`, this contradicts `b C` being a strict UB for `C`.
    have lem : y < (b C) := by
      apply (hb C h.1) y
      exact mem_of_subset_of_mem hSeg'.1 hy
    exfalso
    have imp : y < y := by
      apply lt_of_lt_of_le lem hxy
    exact (lt_self_iff_false y).mp imp

  exact hSeg'.mem_of_mem_of_le hxC hy hxy

end Good

theorem zorn (h : ∀ C, IsChain C → ∃ (b : α), IsUB C b) : ∃ (m :α ), IsMaximal m := by
  unfold IsMaximal
  -- suppose not!
  by_contra! h_con

  -- Every chain has a *strict* upper bound.
  -- The phrasing here is a little odd, since the existence asserts some choice of `b`
  -- that doesn't matter when `C` isn't a chain. It will be more convenient for applying
  -- choice though, since the function we get will be well-defined for every set rather
  -- than depend on a proof the set is a chain.
  have h_strictUB : ∀ (C : Set α), ∃ (b : α), IsChain C → IsStrictUB C b := by
    intro C
    by_cases hC : IsChain C
    · -- use `h` and `h_con` to find a strict upper bound.
      have eUBC : ∃ b, IsUB C b := by exact h C hC
      have ⟨m,mUBC⟩ := eUBC
      have ⟨b,mleb,mneb⟩ := (h_con m)
      use b
      intro ?_ c cC
      apply lt_of_le_of_lt (mUBC c cC)
      exact lt_of_le_of_ne mleb mneb


    -- There isn't anything to prove if `C` isn't a chain - the simplifier does the work for us.
    simp [hC]

  -- This line is where you're using the axiom of choice.
  -- Whenever you go from a `∀ _, ∃ _` statement to a function, that's the axiom of choice.
  -- choice as a formal theorem statement is of course somewhere in mathlib/lean,
  -- but the way to invoke it for things like this is with the `choose` tactic,
  -- which turns an existence statement into the existence of a function.
  -- This line produces a function `b` and a statement `hb` that talks about `b`.
  -- Look carefully at what properties they have.
  choose b hb using h_strictUB

  have hb_not_mem : ∀ C, IsChain C → b C ∉ C := by
    -- use `IsStrictUB.not_mem` and `hb`.
    intro nC cnC
    apply IsStrictUB.not_mem  (hb nC cnC)

  -- define `U` as in the paper proof.
  let U := ⋃₀ {C : Set α | GoodWRT b C}

  -- we already prove the lemma that implies that `U` is a chain.
  have hU_chain : IsChain U := GoodWRT_sUnion_chain b hb_not_mem

  have forall_good_segment : ∀ D, GoodWRT b D → IsSegmentOf D U := by
    -- Use comparability. This is one of the harder `sorry`s.
    intro D GbD
    refine ⟨?_ ,hU_chain,?_⟩
    · apply subset_sUnion_of_mem
      exact GbD
    intro x y xU yD xley
    apply mem_sUnion.mp at xU

    have ⟨C,CiWRT,xC⟩:= xU
    have GbC : GoodWRT b C := by exact CiWRT
    obtain (DsC|CsD) := goodWRT_comparability hb_not_mem GbC GbD
    · apply DsC.2.2 x y xC yD xley
    exact mem_of_subset_of_mem CsD.1 xC

  have hU_good : GoodWRT b U := by
    unfold GoodWRT
    constructor
    · exact hU_chain
    intro S hS hSne
    obtain ⟨d, hdU, hSd⟩ := hS.exists_strictUB_mem_of_ne hSne

    -- Since `d ∈ U`, there is a good chain `D` containing `d`.
    simp_rw [U, mem_sUnion, mem_setOf] at hdU
    obtain ⟨D, hD, hdD⟩ := hdU

    have hDU := forall_good_segment D hD

    have hSD : S ⊆ D := by
      intro s sS
      apply hDU.2.2 s d (mem_of_subset_of_mem hS.1 sS) hdD
      exact le_of_lt (hSd s sS)

    have hSD_seg : IsSegmentOf S D := by
      refine ⟨hSD,hD.1,?_⟩
      intro x y xD yS xley
      apply hS.2.2 x y (mem_of_subset_of_mem hDU.1 xD) yS xley

    have hSneD : S ≠ D := by
      intro h_eq
      subst h_eq
      -- the above two lines can be replaced by `rintro rfl`.
      -- use `StrictUB.not_mem`.
      apply IsStrictUB.not_mem hSd
      exact hdD

    have hbSD := hD.2 S hSD_seg hSneD
    exact hbSD.trans hDU

  -- As we proved earlier, inserting `b U` to `U` preserves goodness...
  have hU_ins_good := hU_good.insert_ub hb


  -- But this means that `U ∪ {b U}` is a subset of `U`, ...
  have h_ins : insert (b U) U ⊆ U := by
    apply IsSegmentOf.subset
    apply forall_good_segment
    exact hU_ins_good

  -- ... which contradicts `b U ∉ U`.
  have nbU :  ¬ (b U ∈ U) := by
    apply hb_not_mem U hU_good.1

  have bU : b U ∈ U := by
    apply mem_of_subset_of_mem h_ins (mem_insert (b U) U)

  contradiction

/- BONUS : the above proof uses `Nonempty α`, which we assumed way at the beginning,
as an assumption. If it is removed, something will break. What breaks, why, and can it be fixed? -/



/-
For the fastidious: try to note the capitalization conventions in all of the above.
The conventions are a mixture of quite a few different rules;
See https://leanprover-community.github.io/contribute/style.html .
-/