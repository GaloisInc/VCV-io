/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.Interaction.TwoParty.Strategy
import VCVio.OracleComp.ProbCompLift
import VCVio.EvalDist.Defs.Instances

/-!
# Message Transmission Protocols

A two-party interactive protocol in which a sender `S` transmits a message
`m ∈ M` to a receiver `R`, formalized in the style of Dodis and Fiore (Sec. 2.1
of *Unilaterally-Authenticated Key Exchange*). The interaction shape and role
assignment are encoded directly with the existing two-party machinery
(`Spec.Strategy.withRoles` / `Spec.Counterpart`), so an honest run of the
protocol is just `Spec.Strategy.runWithRoles` and produces a transcript along
with the receiver's output.

This module defines:

* `MessageTransmissionProtocol m M SendK RecvK` — the structural notion
  `(Setup, S, R)`. The sender carries no terminal output, so its strategy
  output type is `Unit`; the receiver's output is `Option M` (`none` ≡ ⊥).
* `exec` / `execOutput` — running the honest sender against the honest
  receiver, producing the transcript-plus-output pair (or just the output).
  This is the formal counterpart of the paper's `⟨S(sendk, m), R(recvk)⟩ = m'`
  notation.
* `PerfectlyCorrect` — Definition 1 in the perfect-correctness variant,
  matching the convention used by `SymmEncAlg.Complete` and
  `AsymmEncAlg.PerfectlyCorrect`.

Security properties (matching transcripts, ping-pong adversaries, iCCA / iCMA
security) are deliberately deferred to sibling modules.
-/

namespace Interaction

open Spec

/-- A message transmission protocol in the sense of Dodis–Fiore (Sec. 2.1):
a possibly-interactive two-party protocol with sender keys in `SendK`,
receiver keys in `RecvK`, and message space `M`.

* `spec` is the interaction shape (sequence of move spaces).
* `roles` assigns each move to the sender or the receiver.
* `setup` produces a fresh `(sendk, recvk)` pair.
* `sender sendk msg` is the honest sender's role-decorated strategy on
  message `msg`; the sender has no terminal output (`Unit`).
* `receiver recvk` is the honest receiver's counterpart strategy; its output
  is `some msg` on accept, `none` on reject. -/
@[ext]
structure MessageTransmissionProtocol
    (m : Type → Type) [Monad m] (M SendK RecvK : Type) where
  spec : Spec.{0}
  roles : RoleDecoration spec
  setup : m (SendK × RecvK)
  sender : SendK → M → Strategy.withRoles m spec roles (fun _ => Unit)
  receiver : RecvK → Counterpart m spec roles (fun _ => Option M)

namespace MessageTransmissionProtocol

variable {m : Type → Type} [Monad m] {M SendK RecvK : Type}

/-! ## Honest execution -/

/-- Execute the honest sender on message `msg` against the honest receiver,
returning the joint transcript paired with the receiver's output. The sender's
trivial `Unit` output is dropped.

This is the formal counterpart of the paper's `⟨S(sendk, m), R(recvk)⟩ = m'`
notation: `m'` is the second component of the returned sigma. -/
def exec (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : M) :
    m ((_ : Transcript mtp.spec) × Option M) :=
  (fun (z : (_ : Transcript mtp.spec) × Unit × Option M) => ⟨z.1, z.2.2⟩) <$>
    Strategy.runWithRoles mtp.spec mtp.roles
      (mtp.sender sendk msg) (mtp.receiver recvk)

/-- The receiver's output of an honest run, with the transcript discarded. -/
def execOutput (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : M) : m (Option M) :=
  Sigma.snd <$> mtp.exec sendk recvk msg

/-! ## Correctness -/

section Correct

variable [DecidableEq M]

/-- Correctness experiment: sample fresh keys, run the honest sender on `msg`
against the honest receiver, and return `true` iff the receiver's output is
`some msg`. -/
def CorrectExp (mtp : MessageTransmissionProtocol m M SendK RecvK) (msg : M) :
    m Bool := do
  let ⟨sendk, recvk⟩ ← mtp.setup
  let out ← mtp.execOutput sendk recvk msg
  return decide (out = some msg)

/-- A message transmission protocol is *perfectly correct* under the given
probabilistic runtime when, for every message, the receiver outputs that
message with probability `1` in an honest run.

Definition 1 of Dodis–Fiore allows a negligible failure probability; the
perfect variant defined here matches the existing convention in this library
(`SymmEncAlg.Complete`, `AsymmEncAlg.PerfectlyCorrect`). Statistical or
asymptotic correctness can be layered on top later. -/
def PerfectlyCorrect (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : M), Pr[= true | runtime.evalDist (mtp.CorrectExp msg)] = 1

end Correct

end MessageTransmissionProtocol

end Interaction
