/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.iCMA
import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signatures as a 1-Round Message Transmission Protocol

A non-interactive `SignatureAlg` is precisely a 1-round message transmission
protocol in the sense of Dodis–Fiore: the sender signs the plaintext and
transmits `(msg, σ)`; the receiver verifies and outputs `some msg` on accept,
`none` on reject.

The sender key is the pair `(pk, sk)` since `SignatureAlg.sign` consumes both
inputs (some hash-and-sign schemes bind the signature to `pk`); the receiver
key is `pk` alone.

This file constructs the wrapper `ofSignatureAlg`, proves that perfect
completeness of the underlying scheme lifts to perfect correctness of the
wrapped protocol, and gives a reduction from EUF-CMA forgers against the
signature scheme to iCMA adversaries against the wrapped MTP — establishing
`unforgeableAdv.advantage ≤ iCMA.Advantage` (note the direction: this
testifies that iCMA is *no harder than* EUF-CMA, not the other way around;
the reverse direction would require strong unforgeability since iCMA's
ping-pong check is on `(msg, σ)` pairs, not just on `msg`).
-/

namespace Interaction
namespace MessageTransmissionProtocol

open Spec OracleSpec OracleComp ENNReal

/-- Wrap a non-interactive `SignatureAlg` as a 1-round message transmission
protocol. The single move is the pair `(msg, σ)`, owned by the sender.

The sender's key is `(pk, sk)`: `SignatureAlg.sign` consumes both inputs (some
hash-and-sign schemes bind `σ` to `pk`). The receiver's key is `pk` alone. -/
def ofSignatureAlg {m : Type → Type} [Monad m] {M PK SK S : Type}
    (sigAlg : SignatureAlg m M PK SK S) :
    MessageTransmissionProtocol m M (PK × SK) PK where
  steps := [⟨M × S, .sender⟩]
  setup := (fun keys => (keys, keys.1)) <$> sigAlg.keygen
  sender keys msg := do
    let σ ← sigAlg.sign keys.1 keys.2 msg
    return ⟨(msg, σ), ()⟩
  receiver pk := fun ms => do
    let v ← sigAlg.verify pk ms.1 ms.2
    return (if v then some ms.1 else none)

variable {m : Type → Type} [Monad m] [LawfulMonad m] {M PK SK S : Type}
  [DecidableEq M]

/-- The wrapped correctness experiment reduces to the underlying signature
completeness experiment. -/
theorem CorrectExp_ofSignatureAlg
    (sigAlg : SignatureAlg m M PK SK S) (msg : M) :
    (ofSignatureAlg sigAlg).CorrectExp msg = (do
      let keys ← sigAlg.keygen
      let σ ← sigAlg.sign keys.1 keys.2 msg
      sigAlg.verify keys.1 msg σ) := by
  unfold MessageTransmissionProtocol.CorrectExp
  simp only [ofSignatureAlg, exec, SenderProgram, ReceiverProgram, monad_norm,
    Function.comp_apply, pure_bind]
  have h : ∀ v : Bool, decide ((if v then some msg else none) = some msg) = v := by
    intro v; cases v <;> simp
  simp only [h, bind_pure]

/-- Perfect completeness of `SignatureAlg` lifts to perfect correctness of the
wrapped 1-round message transmission protocol. -/
theorem PerfectlyCorrect_ofSignatureAlg
    (sigAlg : SignatureAlg m M PK SK S) (runtime : ProbCompRuntime m)
    (h : sigAlg.PerfectlyComplete runtime) :
    (ofSignatureAlg sigAlg).PerfectlyCorrect runtime := by
  intro msg
  rw [CorrectExp_ofSignatureAlg]
  exact h msg

/-! ## EUF-CMA → iCMA reduction

Given an EUF-CMA forger `B` against `sigAlg`, we build an iCMA adversary
against `ofSignatureAlg sigAlg` that simulates `B`'s signing oracle by
starting a fresh iCMA session on each query and reading the signature off
the honest sender's `(msg, σ)` move. The iCMA adversary submits `B`'s
forged `(msg*, σ*)` as its challenge.

The bound `unforgeableAdv.advantage ≤ iCMA.Advantage` then expresses that
iCMA security implies EUF-CMA security — so iCMA is at least as strong a
notion. The reverse direction would need strong-unforgeability of the
signature scheme; see the file docstring. -/
section iCMAReduction

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S] [Nonempty S]

/-- The iCMA adversary built from an EUF-CMA forger. Each `M →ₒ S` query of
`B` is translated into an iCMA `Start` followed by a `Query (sid, 0)`,
extracting σ from the honest sender's `(msg, σ)` move. The unreachable
`none` branch defaults to an arbitrary signature; it never fires when the
iCMA queries are well-formed (which they are by construction here). -/
noncomputable def iCMAReduction
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (B : SignatureAlg.unforgeableAdv sigAlg) :
    iCMA.Adversary (ofSignatureAlg sigAlg) where
  challengeStrategy := fun pk =>
    show OracleComp _ ((M × S) × Unit) from do
      let signImpl : QueryImpl (M →ₒ S)
          (OracleComp (spec + iCMA.OSpec (ofSignatureAlg sigAlg).steps M)) :=
        fun (msg : M) => do
          let startIdx : (spec + iCMA.OSpec (ofSignatureAlg sigAlg).steps M).Domain :=
            Sum.inr (Sum.inl (Sum.inl msg))
          let sid : ℕ ← liftM (OracleSpec.query startIdx)
          let i : Fin (ofSignatureAlg sigAlg).steps.length :=
            ⟨0, by simp [ofSignatureAlg]⟩
          let queryIdx : (spec + iCMA.OSpec (ofSignatureAlg sigAlg).steps M).Domain :=
            Sum.inr (Sum.inr (sid, i))
          let opt : Option (M × S) ← liftM (OracleSpec.query queryIdx)
          match opt with
          | some (_, σ) => pure σ
          | none => pure (Classical.arbitrary S)
      let combinedImpl := (QueryImpl.id' spec).addLift signImpl
      let (msg, σ) ← simulateQ combinedImpl (B.main pk)
      pure ((msg, σ), ())

/-! ## Proof structure

The bound `unforgeableAdv_advantage_le_iCMA_advantage` factors through three
ingredients:

1. **`unforgeJoint sigAlg B`** — the shared OC-spec computation that runs
   `keygen`, simulates `B` with the WriterT-based signing oracle, and
   verifies. It exposes the data needed by both win conditions:
   `(msg*, σ*, log, verified)`.

2. **Step 2 (`unforgeableExp_factors`).** `unforgeableExp` factors as
   `combiner_unforge <$> runtime.evalDist (unforgeJoint sigAlg B)` where
   `combiner_unforge (msg, σ, log, verified) := !log.wasQueried msg && verified`.
   This is essentially a refactoring of the existing `unforgeableExp` definition
   to expose σ.

3. **Step 1 (`iCMAGame_factors`, the operational equivalence).** The iCMA
   `Game` body factors as `combiner_iCMA <$> runtime.evalDist (unforgeJoint sigAlg B)`
   where `combiner_iCMA (msg, σ, log, verified) := verified && !decide (∃ entry ∈ log,
   entry.fst = msg ∧ entry.snd = σ)`. Note: this combiner *depends on σ* (not just
   `msg`), reflecting that iCMA's ping-pong checks the whole `(msg, σ)` move pair.

   The factoring is the deep operational lemma: it requires showing that simulating
   `B`'s `M →ₒ S` queries through `iCMAReduction`'s `Start`-then-`Query` pattern
   in the iCMA `oracleImpl` produces the same OC-spec actions (same σ values) as
   the direct `signingOracle`, *and* that the iCMA `completedTranscripts` ends up
   with the same `(msg, σ)`-pair multiset as the WriterT `QueryLog`.

4. **Final bound (`iCMAReduction_advantage_bound`).** Pointwise,
   `combiner_unforge ⟹ combiner_iCMA`: if `msg ∉ log.queries`, then there's
   no `(msg, σ)` entry at all, so the iCMA combiner's outer existential fails
   ⟹ `combiner_iCMA = verified ∧ ¬False = verified`; and `combiner_unforge =
   ¬False ∧ verified = verified`. Both sides agree. When `msg ∈ log.queries`,
   `combiner_unforge = false` and `combiner_iCMA` may still be true — making the
   iCMA bound at least as large.

The theorem follows from `probEvent_mono` applied to the pointwise implication.

Below: `unforgeJoint`, the Step-2 factoring, and the final theorem (modulo
`iCMAGame_factors`, sorry'd). -/

/-- The shared joint OC-spec computation: runs `keygen`, simulates `B` with the
signing oracle, and verifies. Exposes `(msg, σ, log, verified)` for use by both
win conditions. -/
private noncomputable def unforgeJoint
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (B : SignatureAlg.unforgeableAdv sigAlg) :
    OracleComp spec (M × S × QueryLog (M →ₒ S) × Bool) :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let ((msg, σ), log) ← (simulateQ impl (B.main pk)).run
    let verified ← sigAlg.verify pk msg σ
    pure (msg, σ, log, verified)

/-- **Step 2.** `unforgeableExp` factors through `unforgeJoint`. -/
private lemma unforgeableExp_factors
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) = f <$> runtime.evalDist mx)
    (B : SignatureAlg.unforgeableAdv sigAlg) :
    letI : DecidableEq M := Classical.decEq M
    SignatureAlg.unforgeableExp runtime B =
      (fun data : M × S × QueryLog (M →ₒ S) × Bool =>
        !data.2.2.1.wasQueried data.1 && data.2.2.2)
        <$> runtime.evalDist (unforgeJoint B) := by
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  unfold SignatureAlg.unforgeableExp unforgeJoint
  rw [← h_pull]
  congr 1
  simp only [monad_norm, bind_pure_comp, Function.comp_apply, pure_bind]
  rfl

/-- **Step 1 (operational equivalence, sorry'd).** The iCMA `Game` body, when
given the reduction of an unforgeable adversary, factors through the same joint
`unforgeJoint`, with a Bool combiner that checks the full `(msg, σ)`-pair against
the log entries (matching iCMA's per-move ping-pong condition).

This is the deep operational lemma between the `WriterT QueryLog` and `StateT
GameState` representations. Closing it requires a structural induction on `B`'s
`OracleComp` term showing:
  * Each `M →ₒ S` query of `B` produces the same σ in both simulations.
  * The iCMA `oracleImpl`'s `completedTranscripts` field, after running the
    reduction, contains exactly the `(msg, σ)` entries of the WriterT log,
    paired with timestamps. -/
private lemma iCMAGame_factors
    [DecidableEq M] [DecidableEq S]
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (B : SignatureAlg.unforgeableAdv sigAlg) :
    iCMA.Game (ofSignatureAlg sigAlg) runtime (iCMAReduction B) =
      (fun data : M × S × QueryLog (M →ₒ S) × Bool =>
        data.2.2.2 &&
        !decide (∃ entry ∈ data.2.2.1, entry.fst = data.1 ∧ entry.snd = data.2.1))
        <$> runtime.evalDist (unforgeJoint B) := by
  -- The `iCMA.Game` body uses `iCMA.runChallenge` (a *private* helper inside
  -- `iCMA.lean`), so unfolding it across the file boundary is blocked. Closing
  -- this lemma in-place would require either:
  --   * promoting `runChallenge` (and supporting helpers like `consumeStep`,
  --     `advanceSenderStepAt`, `commitAdvance`) from `private` to public, then
  --     a long simp/unfold chain to reduce `iCMA.Game` for the 1-round case
  --     into the form of `unforgeJoint`, OR
  --   * proving an exposed equation lemma `iCMA.Game_ofSignatureAlg_eq` *inside*
  --     `iCMA.lean` (or in a sibling file with internal access) that gives the
  --     specialized form for 1-round protocols, then using that lemma here.
  --
  -- Either path is a substantial standalone work item: the 1-round
  -- specialization needs to walk the `simulateQ` of `B.main pk` through the
  -- `addLift` of `id'` and `signImpl`, threading `StateT GameState`, and
  -- ultimately show the `(msg, σ)` output and the `completedTranscripts`
  -- field reproduce the WriterT-log shape. The right home for that work is
  -- `iCMA.lean` itself, where the helpers are visible.
  sorry

/-- **Step 4.** The final advantage bound. Combines Step-1 and Step-2 factorings
with the pointwise implication `combiner_unforge ⟹ combiner_iCMA`. The
`h_pull` hypothesis on `runtime` mirrors the convention in
`unforgeableAdv.advantage_le_unforgeableExpNoFresh`. -/
theorem unforgeableAdv_advantage_le_iCMA_advantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} (f : α → β) (mx : OracleComp spec α),
      runtime.evalDist (mx >>= fun x => pure (f x)) = f <$> runtime.evalDist mx)
    (B : SignatureAlg.unforgeableAdv sigAlg) :
    B.advantage runtime ≤ iCMA.Advantage runtime (iCMAReduction B) := by
  letI : DecidableEq M := Classical.decEq M
  unfold SignatureAlg.unforgeableAdv.advantage iCMA.Advantage
  rw [unforgeableExp_factors runtime h_pull B, iCMAGame_factors runtime B]
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
      probEvent_map, probEvent_map]
  refine probEvent_mono fun ⟨msg, σ, log, verified⟩ _ h_unforge => ?_
  -- h_unforge : (!log.wasQueried msg && verified) = true
  -- Show: (verified && !decide (∃ entry ∈ log, entry.fst = msg ∧ entry.snd = σ)) = true.
  obtain ⟨h_fresh, h_verified⟩ := (Bool.and_eq_true _ _).mp h_unforge
  refine (Bool.and_eq_true _ _).mpr ⟨h_verified, ?_⟩
  -- Goal: `!decide (∃ entry ∈ log, entry.fst = msg ∧ entry.snd = σ) = true`.
  -- From `h_fresh`, no log entry has `fst = msg`, so the existential fails.
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and]
  intro entry h_mem h_fst _
  rw [Bool.not_eq_true', QueryLog.wasQueried, decide_eq_false_iff_not,
      QueryLog.getQ_ne_nil_iff_mem_map_fst] at h_fresh
  exact h_fresh (List.mem_map.mpr ⟨entry, h_mem, h_fst⟩)

end iCMAReduction

end MessageTransmissionProtocol
end Interaction
