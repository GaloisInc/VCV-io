/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.iCCA
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.CryptoFoundations.AsymmEncAlg.INDCCA

/-!
# Asymmetric Encryption as a 1-Round Message Transmission Protocol

A non-interactive `AsymmEncAlg` is precisely a 1-round message transmission
protocol in the sense of Dodis–Fiore: the sender encrypts the plaintext to a
ciphertext and transmits it; the receiver decrypts.

This file constructs the wrapper `ofAsymmEncAlg`, proves that perfect
correctness of the underlying scheme lifts to perfect correctness of the
wrapped protocol, and gives a reduction from iCCA adversaries against the
wrapped MTP to IND-CCA adversaries against the underlying scheme — yielding
`Pr[= true | iCCA.Game] ≤ Pr[= true | IND_CCA_Game]` (i.e. iCCA is
*at least as restrictive* as IND-CCA: A's iCCA win events are a subset of
A's IND-CCA win events under the natural reduction).
-/

namespace Interaction
namespace MessageTransmissionProtocol

open Spec OracleSpec OracleComp ENNReal

/-- Wrap a non-interactive `AsymmEncAlg` as a 1-round message transmission
protocol. The single move is the ciphertext, owned by the sender (the only
party that speaks). -/
def ofAsymmEncAlg {m : Type → Type} [Monad m] {M PK SK C : Type}
    (encAlg : AsymmEncAlg m M PK SK C) :
    MessageTransmissionProtocol m M PK SK where
  steps := [⟨C, .sender⟩]
  setup := encAlg.keygen
  sender pk msg := do
    let c ← encAlg.encrypt pk msg
    return ⟨c, ()⟩
  receiver sk := fun c => encAlg.decrypt sk c

variable {m : Type → Type} [Monad m] [LawfulMonad m] {M PK SK C : Type}
  [DecidableEq M]

/-- The wrapped correctness experiment is the same monadic computation as the
underlying `AsymmEncAlg.CorrectExp`. -/
theorem CorrectExp_ofAsymmEncAlg (encAlg : AsymmEncAlg m M PK SK C) (msg : M) :
    (ofAsymmEncAlg encAlg).CorrectExp msg = encAlg.CorrectExp msg := by
  unfold MessageTransmissionProtocol.CorrectExp
    AsymmEncAlg.CorrectExp
  simp only [ofAsymmEncAlg, exec, SenderProgram, ReceiverProgram, monad_norm]

/-- Perfect correctness of `AsymmEncAlg` lifts to perfect correctness of the
wrapped 1-round message transmission protocol. -/
theorem PerfectlyCorrect_ofAsymmEncAlg
    (encAlg : AsymmEncAlg m M PK SK C) (runtime : ProbCompRuntime m)
    (h : encAlg.PerfectlyCorrect runtime) :
    (ofAsymmEncAlg encAlg).PerfectlyCorrect runtime := by
  intro msg
  rw [CorrectExp_ofAsymmEncAlg]
  exact h msg

/-! ## iCCA → IND-CCA reduction

Given an iCCA adversary `A` against `ofAsymmEncAlg encAlg`, we build an
IND-CCA adversary `B` against `encAlg` that simulates `A`. The translation
of `A`'s iCCA OSpec queries into `B`'s IND-CCA decryption-oracle queries
is stateless:

* `Start ()` → return any sid (we use `0`); IND-CCA has no session
  abstraction.
* `Submit (_, ⟨0, c⟩)` → query the IND-CCA decryption oracle on `c`,
  return the resulting `Option M`.
* `Query (_, 0)` → return `none` (a sender-step query is meaningless when
  `A` itself plays sender in oracle sessions; mirrors the iCCA
  `oracleImpl` behavior at sender steps).

The bound `Pr[= true | iCCA.Game] ≤ Pr[= true | IND_CCA_Game (reduce A)]`
holds *pointwise* on the random tape: trajectories where `A` would win
iCCA require `¬ ping-pong`, on which `A`'s view in iCCA matches its view
under the IND-CCA reduction (cStar never appears in queries), so the
guess `b'` is the same. Trajectories with ping-pong contribute `0` to the
iCCA side. -/
section iCCAReduction

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {M PK SK C : Type}
  [DecidableEq C]

/-- Translate iCCA OSpec queries to `OC (spec + (C →ₒ Option M))` actions:
`Start` returns a dummy sid; `Submit ⟨_, ⟨_, c⟩⟩` decrypts via the
`(C →ₒ Option M)` oracle; `Query _` returns `none` (sender-step queries
aren't meaningful in iCCA when A plays sender). -/
private def iCCATranslate
    (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :
    QueryImpl (iCCA.OSpec (ofAsymmEncAlg encAlg).steps M)
      (OracleComp (spec + (C →ₒ Option M))) := fun q => by
  match q with
  | Sum.inl (Sum.inl ()) =>
    change OracleComp (spec + (C →ₒ Option M)) ℕ
    exact pure 0
  | Sum.inl (Sum.inr ⟨_, ⟨⟨0, _⟩, c⟩⟩) =>
    change OracleComp (spec + (C →ₒ Option M)) (Option M)
    let q : OracleQuery (spec + (C →ₒ Option M)) (Option M) :=
      OracleSpec.query (Sum.inr c)
    exact (q : OracleComp (spec + (C →ₒ Option M)) (Option M))
  | Sum.inr ⟨_, ⟨0, _⟩⟩ =>
    change OracleComp (spec + (C →ₒ Option M)) (Option (C × Option M))
    exact pure none

/-- The IND-CCA adversary built from an iCCA adversary against the
wrapped MTP. -/
noncomputable def iCCAReduction
    {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    (A : iCCA.Adversary (ofAsymmEncAlg encAlg)) :
    encAlg.IND_CCA_Adversary where
  State := A.State
  chooseMessages pk :=
    let combinedImpl : QueryImpl (spec + iCCA.OSpec (ofAsymmEncAlg encAlg).steps M)
        (OracleComp (spec + (C →ₒ Option M))) :=
      (QueryImpl.id' spec).addLift (iCCATranslate encAlg)
    simulateQ combinedImpl (A.phase1 pk)
  distinguish state cStar :=
    let recvFn : C → OracleComp (spec + iCCA.OSpec (ofAsymmEncAlg encAlg).steps M) Bool :=
      A.phase2 state
    let combinedImpl : QueryImpl (spec + iCCA.OSpec (ofAsymmEncAlg encAlg).steps M)
        (OracleComp (spec + (C →ₒ Option M))) :=
      (QueryImpl.id' spec).addLift (iCCATranslate encAlg)
    simulateQ combinedImpl (recvFn cStar)

/-- **iCCA → IND-CCA bound.** `A`'s iCCA win probability is at most the
IND-CCA win probability of the reduced adversary.

Proof structure mirrors the EUF-CMA → iCMA test in `OfSignatureAlg.lean`:
both sides factor through a shared joint OC computation that exposes
`(b, b', queryLog)` from running `A` with the simulated decryption oracle.
The iCCA combiner additionally requires `¬ ping-pong` (i.e. `cStar` not
in the query log), making the iCCA Bool a *strict subset* of the
IND-CCA Bool — so the inequality holds pointwise.

Closing this requires the same kind of operational equivalence between
the iCCA `StateT GameState` bookkeeping and the IND-CCA `OC spec`-based
decryption simulation as in the iCMA case (`iCMAGame_factors`).
Deferred. -/
theorem iCCA_advantage_le_IND_CCA_advantage
    {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    (runtime : ProbCompRuntime (OracleComp spec))
    (A : iCCA.Adversary (ofAsymmEncAlg encAlg)) :
    Pr[= true | iCCA.Game (ofAsymmEncAlg encAlg) runtime A] ≤
    Pr[= true | AsymmEncAlg.IND_CCA_Game runtime (iCCAReduction A)] := by
  sorry

end iCCAReduction

end MessageTransmissionProtocol
end Interaction
