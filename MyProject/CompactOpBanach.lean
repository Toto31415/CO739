
/-
Let X,Y be Banach spaces, and T ∈ B(X,Y). (bounded linear operators from X → Y)
Given r>0, we denote X_r to be the closed ball of radius r in X

# Definition: T is compact if Cl(T(X_1)) is compact in Y

The theorem that we will prove is the equivalence of the following 
characterizations of compact operators on Banach Spaces
# The Following Are Equivalent
* 1) `T` is compact

* 2) `Cl(T(F))` is compact in `Y` for all bounded subsets `F` of `X`

* 3) If `{x_n}_{n=1}^∞` is a bounded sequence in `X`, 
then `{T(x_n)}_{n=1}^∞` has a convergent subsequence in `Y`

* 4) `T(X_1)` is totally bounded 
-/

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.GroupTheory.GroupAction.Basic

open Filter Metric Function Set Topology Bornology
open TopologicalSpace UniformSpace NormedSpace
open Classical Pointwise
open Uniformity
open ContinuousLinearMap

/-
Here we declare all the variables that we are going to use to define our statements
we want `𝔽` and `𝕂` to be Normed fields 
now since they are not necesarily the same field in order to define linear maps between them
we need isomorphisms `σ` and `σ'` that are also isometries

Now we claim that `V` and `W` are Normed vector spaces over 𝔽 and 𝕂 respectively
In order to define them as such lean needs to know that the additive structure on the V,W
are normed commutative groups

Finally `T` simply is a continuous linear map 
between these two modules that are Normed vector spaces
-/

variable {𝕜 𝔽 : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝔽] 
variable {σ' : 𝕜 →+* 𝔽} {σ : 𝔽 →+* 𝕜} 
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] 
variable [RingHomIsometric σ] [RingHomIsometric σ']
variable {W : Type*} 
[NormedAddCommGroup W] 
[NormedSpace 𝕜 W] 
variable {V : Type*} 
[NormedAddCommGroup V] 
[NormedSpace 𝔽 V] 
variable (T : V →SL[σ] W) 

/-
We now write our 4 definitions of compactness
-/

-- Characterization 1) T is compact (Closure of the image of the unit ball is compact)
def PreCompactImageofUnitBall (T : V → W) : Prop :=
  IsCompact (closure (image T (Metric.closedBall 0 1)))

-- Characterization 2) Cl(T(S)) is compact for all bounded F
def CompactImageofBounded (T : V → W) : Prop :=
  ∀ S : Set V, IsBounded S → IsCompact (closure (image T S))

-- Characterization 3) If {a_n}_{n=1}^∞ is a bounded sequence in X, 
-- then {T(a_n)}_{n=1}^∞ has a convergent subsequence in Y
-- having a convergent subsequence means that there is a limit point L
-- and a monotone function φ : ℕ → ℕ that gives us the subsequence 
-- that converges (that is) Filter {T(a φ n)}_{n=1}^∞ Tends to atTop L
def SeqCompactnessofBoundedSeq (T : V → W) : Prop :=
  (a : ℕ → V) → IsBounded (range a) → ∃ L ∈ closure (range (T ∘ a)), 
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (T ∘ a ∘ φ) Filter.atTop (nhds L)

-- Characterization 4) T(X_1) is totally bounded 
def TotBoundedImageofUnitBall [Zero V] (T : V → W) : Prop :=
  TotallyBounded (image T (Metric.closedBall 0 1))


/-
# We now prove the characterizations
The strategy to prove their equivalence will be to show
1 → 2 → 3 → 4 → 1
-/

/-
# Proof of 1) → 2)
  Suppose F is bounded on X, then F ⊆ X_r for some r > 0
  Multiplication by non zero constants is a homeomorphism
  Hence Cl(T(F)) ⊆ Cl(T(X_r)) = Cl(rT(X_1)) = rCl(T(X_1))
  Last set is image of compact under a homeomorphism so it is compact
-/

theorem One_Implies_Two : PreCompactImageofUnitBall T → CompactImageofBounded T := by 
  intro One
  -- We have : PreCompactImageofUnitBall ⇑T as an assumption
  unfold CompactImageofBounded
  -- Our goals is:  ∀ (S : Set V), IsBounded S → IsCompact (closure (⇑T '' S))
  intro S bS
  -- S : Set V , bS : IsBounded S
  rw [NormedSpace.isBounded_iff_subset_smul_ball 𝔽] at bS
  -- (S being bounded implies S is inside some scaled ball) ∃ a, S ⊆ a • ball 0 1 
  obtain ⟨a,hS⟩ := bS 
  -- a : 𝔽 , S ⊆ a • ball 0 1

  -- Lem shows that : T (S) ⊂ (σ a) Cl (T V_1) (V_1 is the closed ball of V with radious 1)
  have Lem : (image T S) ⊆ (σ a) • (closure (image T (closedBall (0 : V) 1))) := by
    intro w hw 
    obtain ⟨v,⟨hv,heq⟩⟩ := hw
    obtain ⟨v',⟨hu,hU⟩⟩ := mem_of_mem_of_subset hv hS
    -- So far we have w ∈ T(S) , w=T(v) , v = a v' , v' ∈ V_1   
    let Hv : a • v' = v := hU    
    rw [← Hv] at heq 
    refine ⟨?_,⟨?_,?_⟩⟩
    -- w ∈ σ a • closure (⇑T '' closedBall 0 1) iff the following 3 conditions are satified
    -- 1) there is a w' ∈ W (we use w'=T v')
    · exact T v'
    -- 2) w' =T v' ∈ closure (⇑T '' closedBall 0 1)
    · apply mem_of_mem_of_subset (mem_image_of_mem (⇑T) hu) 
      -- using the fact that (⇑T '' closedBall 0 1) ⊆ closure (⇑T '' closedBall 0 1)
      let balls : ⇑T '' ball 0 1 ⊆ ⇑T '' closedBall 0 1 := by
        apply Set.image_subset
        exact ball_subset_closedBall
      exact balls.trans subset_closure
    -- 3) w = (σ a) T v' = (σ a) T v'
    · let betaReduc : (fun x ↦ σ a • x) (T v') = (σ a) • (T v') := rfl  
      rw [← heq,betaReduc]
      apply Eq.symm
      exact (ContinuousLinearMap.map_smulₛₗ T a v') 
  -- We now use the fact that closed subsets of compact sets are compact
  rw [← exists_isCompact_superset_iff] 
  -- So we want to find ∃ K, IsCompact K ∧ ⇑T '' S ⊆ K
  -- Here we use the same set as in our Lemma Lem
  use (σ a) • closure (image T (closedBall (0 : V) 1))
  refine ⟨?_,Lem⟩
  -- By continuity of scalar multiplication K being compact implies (σ a) K is compact 
  apply IsCompact.smul
  exact One 
  
 
/-
# Proof of 2) → 3)
  If F={x_n}_{n=1}^∞ is bounded then by assumption Cl(T(F)) is compact
  Hence by characterization of compactness on metric space it has a convergent subsequence
  So for any subsequence in T(F) ⊆ Cl(T(F)) also has a convergent subsequence
-/
theorem Two_Implies_Three : CompactImageofBounded T → SeqCompactnessofBoundedSeq T := by 
  intro Two 
  unfold CompactImageofBounded at Two
  -- We start with our assumption that: CompactImageofBounded T
  unfold SeqCompactnessofBoundedSeq
  intro a Boundseq
  -- We introduce a bounded sequence {a(n)}_{n=1}^∞ ∈ V 
  -- Our goal is to show that ∃ L ∈ Closure ({T a(n)}) such that 
  -- this L is the limit of some subsequence {T a(φ n)}

  -- Characterization 2 tells us that Closure ({T a(n)}) is compact since {T a(n)} is bounded
  have compactRange : IsCompact (closure (⇑T '' (range a))) := by 
    exact Two (range a) Boundseq 
  -- On metric spaces compact ↔ sequentially compact 
  -- Hence we have that Closure ({T a(n)}) is sequentially compact
  have seqCompactRange : IsSeqCompact (closure (⇑T '' (range a))) := by 
    apply IsCompact.isSeqCompact
    exact compactRange 
  unfold IsSeqCompact at seqCompactRange

  let x := T ∘ a
  -- The key to solving our goal is to first show that
  -- x n = T (a n) ∈ closure (⇑T '' range a))
  have key : (∀ (n : ℕ), x n ∈ closure (⇑T '' range a)) := by 
    intro n 
    -- by construction we already have x n = T (a n) ∈ (⇑T '' range a))
    have InRan : x n ∈ (⇑T '' range a) := by
      have Hxn : x n = (T ∘ a) n := by 
        exact rfl
      rw [Hxn]
      rw [mem_image]
      use (a n)
      refine ⟨?_,?_⟩
      exact mem_range_self n
      exact Hxn
    -- so we use the standard tactic that (⇑T '' range a)) ⊆ closure (⇑T '' range a))
    apply mem_of_mem_of_subset InRan
    exact subset_closure
  
  -- this is a trivial small lemma to rewrite our goal into something easier to work with
  have rangeLemma : range (⇑T ∘ a) = ⇑T '' range a := by
    exact range_comp (⇑T) a
  rw [rangeLemma]
  -- Now the goal changes where L lives into
  -- ∃ L ∈ closure (⇑T '' range a), (T ∘ a ∘ φ) Tends to L

  -- Remember when we used our characterization 2 to prove the range was sequentially compact?
  -- well we use it now
  exact seqCompactRange key
   
/-
# Proof of 3) → 4)
  We will show Cl(T(X_1)) is compact. 
-/

theorem Three_Implies_Four [CompleteSpace V] [CompleteSpace W] : 
SeqCompactnessofBoundedSeq T → TotBoundedImageofUnitBall T := by 
  intro three 
  unfold SeqCompactnessofBoundedSeq at three 
  unfold TotBoundedImageofUnitBall 
  -- Our goal is to show that T (V_1) is totally bounded (V_1 is the closed unit ball of V)
  -- Now T (V_1) is totally bounded if closure T (V_1) is
  apply TotallyBounded.subset subset_closure
  -- We also know that in metric spaces if you are sequentially compact then you are totally bounded
  -- So lets change our goal into showing that closure T (V_1) is sequentially compact
  apply IsSeqCompact.totallyBounded
  unfold IsSeqCompact 
  -- So we introduce a sequence {y(n)} ∈ closure T (V_1)
  intro y Hy 
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  /-
    Since each y(n) ∈ Closure T (V_1) then there must exists some x(n) such that
    y(n) and T(x(n)) are very close (in particular we want them at distance 1/(n+1))

    In order to show this theorem we translate convergence from the world of filters into
    ε,δ world and crawl our way to get this nice bound

    By definition of the closure we should be able to find at least one x(n) with this property
    However since it is not unique I decided to use axiom of choice to make a sequence out of them
  -/
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  have ExistsX : ∃ x : ℕ → V , ∀ n, 
  (x n ∈ closedBall 0 1 ∧ ‖(y n) -  T (x n)‖ ≤ (1/(n+1)) ):= by 
    -- We localize our question, and show x(n) exists for each (n : ℕ)
    have forallExists : ∀ (n : ℕ) , 
    ∃ xN ∈ (closedBall (0 : V) 1), ‖(y n) -  T (xN)‖ ≤ (1/(n+1)) := by 
      intro n 
      have Hyn : y n ∈ closure (⇑T '' closedBall 0 1) := by 
        apply Hy 
      rw [SeminormedAddCommGroup.mem_closure_iff] at Hyn
      have helperLemma : ∃ b ∈ ⇑T '' closedBall 0 1, ‖y n - b‖ ≤ (1/(n+1)) := by 
        obtain ⟨b,⟨bInSet,LE⟩⟩ := Hyn (1/(n+1)) Nat.one_div_pos_of_nat
        refine ⟨b,⟨bInSet,le_of_lt LE⟩⟩
      obtain ⟨Txn,⟨⟨v,⟨vInBall,TvEqTxn⟩⟩,ineq⟩⟩ := helperLemma  
      use v 
      refine ⟨vInBall,?_⟩
      rw [TvEqTxn]
      exact ineq 
    --Now that we know they exists we construct the sequence
    apply Classical.axiomOfChoice forallExists -- Here we use choice
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  obtain ⟨x,closeCondition⟩ := ExistsX
  -- We want to show that {x(n)} is a bounded sequence 
  have Bx : IsBounded (range x) := by 
    -- By construction of x(n) we know range x ∈  (closedBall (0:V) 1) 
    have subsetofBall : (range x) ⊆ (closedBall (0:V) 1) := by 
      intro xn hxn 
      obtain ⟨n,Hxn⟩ := hxn
      rw [← Hxn]
      obtain ⟨xnInball,_⟩ := closeCondition n 
      exact xnInball
    -- We know V_1 is bounded
    have ballIsbounded : IsBounded (closedBall (0: V) 1) := by 
      exact isBounded_closedBall
    -- Hence a subset of it will also be bounded
    exact IsBounded.subset ballIsbounded subsetofBall
  
  -- Here is where we use Characterization 3
  -- We use to find a convergent subsequence of {x(n)}
  --Namely x(φ n) → L
  obtain ⟨L,⟨hL,⟨φ,⟨phiMono,converges⟩⟩⟩⟩ := three x Bx

  -- The idea now is that since y(n) and x(n) are so close
  -- then L being a limit of x(φ n) must also be the limit of y(φ n)
  -- So it would be the limit of some subsequence of {y(n)}
  use L
  -- Small lemma to rewrite our goal
  -- this says that closure {T (x n)} ⊆ closure T (closedBall 0 1)
  have setLemma : closure (range (⇑T ∘ x)) ⊆ closure (⇑T '' (closedBall 0 1)) := by 
    -- If {T (x n)} ⊆ T (closedBall 0 1) we would be done, so we show this
    -- which is true from construction of {x(n)}
    have helper : range (⇑T ∘ x) ⊆ ⇑T '' (closedBall 0 1):= by
      intro txa Htxa 
      obtain ⟨k,hEq⟩ := Htxa
      rw [← hEq] 
      apply mem_image_of_mem T
      obtain ⟨xkInball,_⟩ := closeCondition k
      exact xkInball
    -- We now use monotonicity of the closure
    apply closure_mono helper 
  refine ⟨?_,⟨φ,⟨phiMono,?_⟩⟩⟩
  · apply mem_of_mem_of_subset hL 
    exact setLemma
  -- OUR goal is now reduced to showing that Tendsto (y ∘ φ) atTop (𝓝 L) !!
  -- Here is where we travel to ε,δ world again.
  rw [NormedAddCommGroup.tendsto_atTop']
  intro ε nne 
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  /- 
    Since we want to show that ∃ N, ∀ (n : ℕ), N < n → ‖(y ∘ φ) n - L‖ < ε
    then we will use the classic triangle inequality technique 

    1) ‖(y ∘ φ) n - L‖ ≤ ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ + ‖T ((x ∘ φ) n) - L‖
    2) ‖T ((x ∘ φ) n) - L‖ < ε/2
    3) ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ ≤ ε/2

    Hence we prove these 3 lemmas
    the idea is that our goal should follow easily from this
  -/
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  -- 1) Triangle inequality
  have LemmaOne : ∀ (n : ℕ) , 
  ‖(y ∘ φ) n - L‖ ≤ ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ + ‖T ((x ∘ φ) n) - L‖ := by 
    exact fun n ↦ norm_sub_le_norm_sub_add_norm_sub ((y ∘ φ) n) (T ((x ∘ φ) n)) L
  -- 2) Second summand of triangle inequality < ε/2
  -- We have shown that Tendsto (⇑T ∘ x ∘ φ) atTop (𝓝 L) 
  -- hence translating to ε,δ world gives us our result
  have LemmaTwo : ∃ N : ℕ , ∀ (n : ℕ), (N < n) → ‖T ((x ∘ φ) n) - L‖ < (ε/2) := by 
    rw [NormedAddCommGroup.tendsto_atTop'] at converges 
    have hnne : 0 < ε/2 := by 
      exact half_pos nne
    obtain ⟨N,HN⟩ := converges (ε/2) hnne 
    use N
    intro n hn 
    apply HN n hn 
  -- 3) First summand of triangle ineq ≤ ε/2
  -- We prove the following inequalities in order to show our goal
  -- ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ ≤ 1/(n' + 1) ≤ 1/(M+1) ≤  ε/2
  have LemmaThree : ∃ M : ℕ , ∀ (n : ℕ), (M < n) → ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ ≤ (ε/2) := by 
    -- These lines are only saying that we can find and integer M such that 
    -- 1/(M+1) ≤ ε/2
    have hnne : 0 < ε/2 := by 
      exact half_pos nne
    let M : ℕ := Nat.ceil (2/ε)
    have lessThan1 : (1/(M+1)) ≤ (ε/2) := by 
      have arith : 1/(2/ε) = (ε/2) := one_div_div 2 ε
      rw [← arith,one_div_le_one_div]
      · apply le_trans (Nat.le_ceil (2 / ε)) 
        have H : ⌈2 / ε⌉₊ ≤ M := Nat.le_refl ⌈2 / ε⌉₊
        apply le_trans (Nat.cast_le.mpr H)
        apply le_add_of_le_of_nonneg (le_refl (M : ℝ))
        exact zero_le_one' ℝ
      · exact Nat.cast_add_one_pos M 
      · have arith2 : (2/ε) = 1/(ε/2) := Eq.symm (one_div_div ε 2)
        rw [arith2,one_div_pos]
        exact hnne

    use M 
    intro n hn 
    let n' : ℕ := φ n 
    -- Since φ is a monotone function then M < φ(n)=n'
    have hn' : M < n' := by 
      apply lt_of_lt_of_le hn 
      apply StrictMono.id_le phiMono 
    -- We have ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ ≤ 1/((φ n) +1) = 1/(n' + 1) from construction of {x(n)}
    have lessThan2 : ‖(y ∘ φ) n  - T (x (φ n))‖ ≤ 1 / (n' + 1) := by 
      obtain ⟨_,H⟩ := closeCondition n' 
      exact H
    -- Since M < φ(n) = n' then 1/(n'+1) ≤ 1/(M+1)
    have lessThan3 : 1/((n'+1) : ℝ) ≤ 1/((M+1) : ℝ) := by 
      have nzR : 0 < ((M + 1) : ℝ) := Nat.cast_add_one_pos M
      apply one_div_le_one_div_of_le nzR
      have Mltn : (M : ℝ) ≤ (n' : ℝ) := by 
        have IntLt : M ≤ n' := le_of_lt hn' 
        exact Nat.cast_le.mpr IntLt -- (Note*) This is interesting, it means I can cast inequlities 
      exact add_le_add_right Mltn 1
    -- We now have As we wanted
    -- ‖((y ∘ φ) n) - T ((x ∘ φ) n)‖ ≤ 1/(n' + 1) ≤ 1/(M+1) ≤  ε/2
    apply le_trans (le_trans lessThan2 lessThan3)
    exact lessThan1
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------  
    -- We can now collect our result!
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  obtain ⟨N,two⟩ := LemmaTwo
  obtain ⟨M,three⟩ := LemmaThree
  use (N+M) 
  intro n hn 
  apply lt_of_le_of_lt
  · apply LemmaOne 
  have IneqR : ‖T ((x ∘ φ) n) - L‖ < ε / 2 := by 
    have nBig : N < n := by 
      exact Nat.lt_of_add_right_lt hn
    apply two n nBig 
  have IneqL : ‖(y ∘ φ) n - T ((x ∘ φ) n)‖ ≤ ε / 2 := by 
    have nBig : M < n := by 
      rw [add_comm] at hn
      exact Nat.lt_of_add_right_lt hn
    apply three n nBig 
  have arith : ε = (ε/2) + (ε/2) := Eq.symm (add_halves ε)
  rw [arith]
  apply add_lt_add_of_le_of_lt IneqL IneqR
  ---------------------------------------------------------------------------------
  ---------------------------------------------------------------------------------
  

/-
# Proof of 4) → 1)
  By characterization of compactness in metric spaces it suffices to show
  Cl(T(X_1)) is complete and totally bounded, 
  however it is already complete since it is a closed subset of a Banach space
  It is totally bounded by assumption so we are done!
-/
theorem Four_Implies_One [CompleteSpace V] [CompleteSpace W] : 
TotBoundedImageofUnitBall T → PreCompactImageofUnitBall T := by 
  intro Four 
  unfold PreCompactImageofUnitBall 
  unfold TotBoundedImageofUnitBall at Four
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_,?_⟩
  · apply TotallyBounded.closure
    exact Four 
  apply IsClosed.isComplete
  exact isClosed_closure

-- I used https://leansearch.net/ to find some names of theorems, this is a great website
