import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

noncomputable section

/-
  Erdős 248 Hybrid Sieve Framework (Lean 4, Mathlib)

  This file encodes the logical architecture of the conditional proof:

  1. Arithmetic definitions: ω, λ, C_k, Kcrit, BadSetAtK, CoreSet, B_tail, G.
  2. Analytic inputs (axioms): per-shift Markov bound, uniform geometric-series
     tail decay, and asymptotic dominance.
  3. Logic engine: a proved union-bound inequality and a (currently axiomatized)
     core–tail cardinality inequality and difference inequality.
  4. Main framework theorem: if the analytic inputs and core density hold,
     then |G| > 0 for all sufficiently large N.

  All hard analytic and a couple of simple combinatorial/algebraic facts are
  stated as axioms to keep this file focused on the architecture.
-/

-- ==============================================================================
-- 1. DEFINITIONS
-- ==============================================================================

/-- ω(n): number of distinct prime factors of n. -/
def omega (n : ℕ) : ℕ :=
  n.primeFactorsList.dedup.length

/-- λ(N) = log log N. -/
def lambda (N : ℕ) : ℝ :=
  Real.log (Real.log N)

/-- Linear constraint C·k. -/
def C_k (c : ℝ) (k : ℕ) : ℝ :=
  c * k

/-- Critical transition point K_crit. -/
def Kcrit (N : ℕ) (alpha c : ℝ) : ℕ :=
  ⌊alpha / (c * lambda N)⌋.toNat

/-- Bad set at a specific shift k (where ω(n+k) exceeds the linear bound). -/
def BadSetAtK (N : ℕ) (c : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Icc N (2 * N)).filter
    (fun n => (omega (n + k) : ℝ) > C_k c k)

/-- Core set: integers n ∈ [N,2N] where all small shifts satisfy the ω-bound. -/
def CoreSet (N : ℕ) (alpha c : ℝ) : Finset ℕ :=
  (Finset.Icc N (2 * N)).filter
    (fun n =>
      ∀ k, 1 ≤ k → k ≤ Kcrit N alpha c →
        (omega (n + k) : ℝ) ≤ max 2 (C_k c k))

/-- Tail bad set: finite union of bad sets for k > K_crit. -/
def B_tail (N : ℕ) (alpha c : ℝ) : Finset ℕ :=
  (Finset.Icc (Kcrit N alpha c + 1) N).biUnion (fun k => BadSetAtK N c k)

/-- Good set: core points that survive all tail exclusions. -/
def G (N : ℕ) (alpha c : ℝ) : Finset ℕ :=
  CoreSet N alpha c \ B_tail N alpha c

-- ==============================================================================
-- 2. ANALYTIC INPUTS (AXIOMS)
-- ==============================================================================

/-- Hypothesis 1: core density \(N / (log N)^A\). -/
def Hcore (N : ℕ) (alpha c A : ℝ) : Prop :=
  ((CoreSet N alpha c).card : ℝ) ≥ (N : ℝ) / (Real.log N) ^ A

/--
Axiom 1 (per-shift Selberg–Delange / Markov bound).

For each fixed k, the bad set `BadSetAtK` has size at most
  α^{-C_k c k} · 2N·(λ(N))^{α-1}.
-/
axiom Omega_Markov_Final
  (N : ℕ) (c : ℝ) (k : ℕ) (alpha : ℝ)
  (h_alpha : 1 < alpha) (h_alpha20 : alpha ≤ 20) (hk : k ≤ N) :
  let T := C_k c k
  ((BadSetAtK N c k).card : ℝ)
    ≤ (alpha ^ (-T)) * (2 * N * (lambda N)^(alpha - 1))

/--
Axiom 2 (uniform geometric-series tail decay).

There exists a constant C' (depending only on α and c) such that
for all sufficiently large N:

  ∑_{k > Kcrit} Markov_Bound_Term(N,α,c,k)
    ≤ C' · N / (log N)^{β+1},

where β = α·log(α/e).
-/
axiom Geometric_Series_Bound
  (alpha c : ℝ)
  (h_alpha : alpha > Real.exp 1) (h_alpha20 : alpha ≤ 20) (h_c : c > 0) :
  ∃ C' : ℝ, C' > 0 ∧
    ∀ ⦃N : ℕ⦄, N ≥ 100 →
      (∑ k ∈ Finset.Icc (Kcrit N alpha c + 1) N,
        (alpha ^ (-C_k c k)) * (2 * N * (lambda N)^(alpha - 1)))
        ≤ C' * N /
          (Real.log N)^(alpha * Real.log (alpha / Real.exp 1) + 1)

/--
Axiom 3 (asymptotic dominance).

If A < β+1, then for some N0, the quantity

  N/(log N)^A − C'·N/(log N)^{β+1}

is strictly positive for all N ≥ N0.
-/
axiom Victory_Arithmetic (A beta C' : ℝ) (h_victory : A < beta + 1) :
  ∃ N0 : ℕ, ∀ N, N ≥ N0 →
    (N : ℝ) / (Real.log N)^A - C' * N / (Real.log N)^(beta + 1) > 0

-- ==============================================================================
-- 3. LOGIC ENGINE
-- ==============================================================================

/-- The explicit per-k Markov bound term. -/
def Markov_Bound_Term (N : ℕ) (alpha c : ℝ) (k : ℕ) : ℝ :=
  (alpha ^ (-C_k c k)) * (2 * N * (lambda N)^(alpha - 1))

/--
Union bound: the size of the tail set is at most the sum of per-k Markov bounds.
-/
lemma Tail_Is_Sum_Of_Bounds
  (N : ℕ) (alpha c : ℝ)
  (h_alpha : 1 < alpha) (h_alpha20 : alpha ≤ 20) :
  ((B_tail N alpha c).card : ℝ)
    ≤ ∑ k ∈ Finset.Icc (Kcrit N alpha c + 1) N,
        Markov_Bound_Term N alpha c k := by
  -- abbreviate the k-range
  let range_k := Finset.Icc (Kcrit N alpha c + 1) N

  -- 1. |B_tail| ≤ ∑ |BadSetAtK| (in ℕ)
  have h1_nat :
      (B_tail N alpha c).card
        ≤ ∑ k ∈ range_k, (BadSetAtK N c k).card := by
    -- B_tail is exactly this biUnion
    simpa [B_tail, range_k] using
      (Finset.card_biUnion_le
        (s := range_k) (t := fun k => BadSetAtK N c k))

  -- cast that inequality to ℝ
  have h1 :
      ((B_tail N alpha c).card : ℝ)
        ≤ ∑ k ∈ range_k, ((BadSetAtK N c k).card : ℝ) := by
    exact_mod_cast h1_nat

  -- 2. For each k, |BadSetAtK| ≤ Markov_Bound_Term using Omega_Markov_Final
  have h2 :
      ∑ k ∈ range_k, ((BadSetAtK N c k).card : ℝ)
        ≤ ∑ k ∈ range_k, Markov_Bound_Term N alpha c k := by
    apply Finset.sum_le_sum
    intro k hk
    -- k ≤ N because k ∈ [Kcrit+1, N]
    have hk_le_N : k ≤ N := (Finset.mem_Icc.mp hk).2
    -- apply per-k analytic bound
    have hMk :=
      Omega_Markov_Final N c k alpha h_alpha h_alpha20 hk_le_N
    -- syntactic alignment with Markov_Bound_Term
    simpa [Markov_Bound_Term, C_k] using hMk

  -- 3. Combine
  exact le_trans h1 h2

/--
Basic combinatorial inequality in Finset form (axiom for now):

  |G| ≥ |Core| − |Tail|.

In words: removing at most |B_tail| elements from `CoreSet` cannot
reduce its cardinality by more than |B_tail|. This is a straightforward
lemma from `Finset.card` theory (using intersections), left as future work.
-/
axiom G_Cardinality_Lower_Bound (N : ℕ) (alpha c : ℝ) :
  ((G N alpha c).card : ℝ)
    ≥ ((CoreSet N alpha c).card : ℝ)
      - ((B_tail N alpha c).card : ℝ)

/--
Algebraic inequality (axiom for now):

From:
  (1) ((CoreSet N α c).card : ℝ) ≥ N / (log N)^A
  (2) ((B_tail N α c).card : ℝ) ≤ C' N / (log N)^{β+1},

we get:
  N/(log N)^A − C' N/(log N)^{β+1}
    ≤ ((CoreSet N α c).card : ℝ) − ((B_tail N α c).card : ℝ).

This is standard real algebra; left as a small separate exercise.
-/
axiom Core_Tail_Diff_Lower
  (A beta C' : ℝ) (N : ℕ) (alpha c : ℝ)
  (h_core : ((CoreSet N alpha c).card : ℝ) ≥ (N : ℝ) / (Real.log N)^A)
  (h_tail_bound : ((B_tail N alpha c).card : ℝ)
    ≤ C' * N / (Real.log N)^(beta + 1)) :
  (N : ℝ) / (Real.log N)^A
    - C' * N / (Real.log N)^(beta + 1)
    ≤ ((CoreSet N alpha c).card : ℝ)
      - ((B_tail N alpha c).card : ℝ)

-- ==============================================================================
-- 4. MAIN FRAMEWORK THEOREM
-- ==============================================================================

/--
Conditional hybrid sieve framework.

Assuming:
  • α > e, α ≤ 20, c > 0,
  • Hcore holds for all sufficiently large N,
  • the analytic axioms Omega_Markov_Final, Geometric_Series_Bound, Victory_Arithmetic,
  • and the combinatorial/algebraic axioms above,

then for all sufficiently large N, the good set `G N α c` is nonempty.
-/
theorem Erdos_248_Framework_Complete
  (alpha c A : ℝ)
  (h_alpha : alpha > Real.exp 1)
  (h_alpha20 : alpha ≤ 20)
  (h_c : c > 0)
  (h_victory : A < alpha * Real.log (alpha / Real.exp 1) + 1)
  (h_core_valid : ∀ ⦃N : ℕ⦄, N ≥ 100 → Hcore N alpha c A) :
  ∃ N0, ∀ ⦃N : ℕ⦄, N ≥ N0 → ((G N alpha c).card : ℝ) > 0 := by

  classical

  -- define β = α log(α/e)
  let beta := alpha * Real.log (alpha / Real.exp 1)
  have h_beta_def : beta = alpha * Real.log (alpha / Real.exp 1) := rfl

  -- α > 1 from α > e
  have h_alpha_gt_1 : 1 < alpha := by
    have h_e_gt_1 : 1 < Real.exp 1 := by
      have : (0 : ℝ) < 1 := zero_lt_one
      exact Real.one_lt_exp_iff.mpr this
    linarith

  -- 1. Get uniform C' and the tail sum bound from the geometric-series axiom
  obtain ⟨C', hC_pos, h_geom⟩ :=
    Geometric_Series_Bound alpha c h_alpha h_alpha20 h_c

  -- 2. Arithmetic dominance threshold from Victory_Arithmetic
  have h_victory_beta :
      A < beta + 1 := by simpa [h_beta_def] using h_victory
  obtain ⟨N0_arith, h_arith⟩ :=
    Victory_Arithmetic A beta C' h_victory_beta

  -- 3. Choose a global N0 ≥ 100 and ≥ N0_arith
  let N0 := max 100 N0_arith

  refine ⟨N0, ?_⟩
  intro N hN_ge

  -- N is large enough for logs and arithmetic dominance
  have hN_ge_100 : N ≥ 100 :=
    le_trans (le_max_left _ _) hN_ge
  have hN_ge_N0_arith : N ≥ N0_arith :=
    le_trans (le_max_right _ _) hN_ge

  -- core bound at this N
  have h_core := h_core_valid (N := N) hN_ge_100

  -- tail: union bound + geometric-series bound (using the uniform C')
  have h_tail_union :=
    Tail_Is_Sum_Of_Bounds N alpha c h_alpha_gt_1 h_alpha20
  have h_tail_geom :=
    h_geom (N := N) hN_ge_100
  have h_tail_bound :
      ((B_tail N alpha c).card : ℝ)
        ≤ C' * N / (Real.log N)^(beta + 1) := by
    -- rewrite exponent in geom bound to use beta
    have : alpha * Real.log (alpha / Real.exp 1) + 1 = beta + 1 := by
      simp [h_beta_def]
    have h_tail_geom' := by
      simpa [this] using h_tail_geom
    exact le_trans h_tail_union h_tail_geom'

  -- combinatorial inequality |G| ≥ |Core| − |Tail|
  have h_set :=
    G_Cardinality_Lower_Bound N alpha c

  -- arithmetic positivity at N from Victory_Arithmetic
  have h_pos :
      (N : ℝ) / (Real.log N)^A
        - C' * N / (Real.log N)^(beta + 1) > 0 :=
    h_arith N hN_ge_N0_arith

  -- algebraic step: main − tailTerm ≤ |Core| − |Tail|
  have h_diff_lower :
      (N : ℝ) / (Real.log N)^A
        - C' * N / (Real.log N)^(beta + 1)
      ≤ ((CoreSet N alpha c).card : ℝ)
        - ((B_tail N alpha c).card : ℝ) :=
    Core_Tail_Diff_Lower A beta C' N alpha c h_core h_tail_bound

  -- from |G| ≥ |Core| − |Tail|, get (Core − Tail) ≤ |G|
  have h_core_tail_le_G :
      ((CoreSet N alpha c).card : ℝ)
        - ((B_tail N alpha c).card : ℝ)
      ≤ ((G N alpha c).card : ℝ) := by
    -- h_set is |G| ≥ |Core| − |Tail|
    -- so (Core − Tail) ≤ |G|
    have := h_set
    exact this

  -- chain: main−tail ≤ Core−Tail ≤ |G|
  have h_lower :
      (N : ℝ) / (Real.log N)^A
        - C' * N / (Real.log N)^(beta + 1)
      ≤ ((G N alpha c).card : ℝ) :=
    le_trans h_diff_lower h_core_tail_le_G

  -- conclusion: |G| > 0
  exact lt_of_lt_of_le h_pos h_lower
