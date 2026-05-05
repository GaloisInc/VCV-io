/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.MessageTransmissionProtocol.Defs

/-!
# Timestamped Transcripts, Matching, and Ping-Pong Adversaries

Definitions 2, 3, and 4 of Dodis–Fiore (Sec. 2.1, "Unilaterally-Authenticated
Key Exchange"), specialized to the linear (non-dependent) protocol shape used
by `MessageTransmissionProtocol`.

* `Transcript steps` — the (untimed) per-step list of moves through the
  protocol.
* `TimestampedTranscript steps` — the same path, with one `ℕ` timestamp per
  move (Definition 2). The paper's "global counter" ticks once per message
  sent across all sessions; we record the resulting per-message stamp.
* `TimestampedTranscript.untimed` / `.timestamps` / `.Monotone` —
  projections and the strict-monotone-timestamps invariant inherited from
  the global counter.
* `TimestampedTranscript.Matches` — Definition 3, per-position form. Because
  the protocol is linear (move types are fixed in advance, not chosen as a
  function of prior moves), the recursive call typechecks directly: no
  existential message-equality witness, no `▸` transport cast. The relation
  is asymmetric: `Matches steps t₁ t₂` is the paper's `t₁ ⊆ t₂`. With
  `Monotone` on each operand it is equivalent to the paper's full chain
  `t_1 < t'_1 < t'_2 < t_2 < …` (or its dual when `S` speaks first), by
  transitivity.
* `TimestampedTranscript.IsPingPong` — Definition 4, asserting that at least
  one of the adversary's oracle session transcripts matches the challenge
  transcript.

iCCA / iCMA security (Definitions 5 & 6) are deferred to sibling files.
-/

namespace Interaction
namespace MessageTransmissionProtocol

/-- The per-step list of moves through a linear message transmission
protocol. The flat product mirrors the spec list directly. -/
def Transcript : List LinearStep → Type
  | [] => Unit
  | step :: rest => step.moveType × Transcript rest

/-- A `Transcript` plus a `ℕ` timestamp on each move (Definition 2 of
Dodis–Fiore, Sec. 2.1). -/
def TimestampedTranscript : List LinearStep → Type
  | [] => Unit
  | step :: rest => step.moveType × ℕ × TimestampedTranscript rest

namespace TimestampedTranscript

/-- Drop the timestamps to recover the underlying `Transcript`. -/
def untimed : (steps : List LinearStep) →
    TimestampedTranscript steps → Transcript steps
  | [], _ => ()
  | _ :: _, ⟨m, _, ts⟩ => ⟨m, untimed _ ts⟩

/-- Extract the list of timestamps along the path. -/
def timestamps : (steps : List LinearStep) →
    TimestampedTranscript steps → List ℕ
  | [], _ => []
  | _ :: _, ⟨_, t, ts⟩ => t :: timestamps _ ts

/-- Strictly increasing timestamps along the path: the invariant inherited
from the paper's global counter. Equivalent to monotonicity of the
`timestamps` list under `· < ·`. -/
def Monotone (steps : List LinearStep)
    (ts : TimestampedTranscript steps) : Prop :=
  (timestamps steps ts).IsChain (· < ·)

/-- Definition 3 (Matching Transcripts) of Dodis–Fiore, per-position form:
messages are equal pointwise, and at each move the timestamp comparison is
dictated by which party speaks. With `Monotone` on each argument, this is
equivalent to the paper's full chain `t_1 < t'_1 < t'_2 < t_2 < …` (or the
dual when `S` speaks first), by transitivity.

Asymmetric: `Matches steps t₁ t₂` is the paper's `t₁ ⊆ t₂` (the relation
is not symmetric, hence the use of `⊆` rather than an equivalence symbol).

Linear protocols make this clean: both transcripts have the same flat
shape `step.moveType × ℕ × …`, so the recursive call typechecks directly
(no existential witness, no transport cast). -/
def Matches : (steps : List LinearStep) →
    TimestampedTranscript steps → TimestampedTranscript steps → Prop
  | [], _, _ => True
  | step :: rest, ⟨m₁, t₁, ts₁⟩, ⟨m₂, t₂, ts₂⟩ =>
      m₁ = m₂ ∧
      (match step.speaker with
        | .sender => t₂ < t₁
        | .receiver => t₁ < t₂) ∧
      Matches rest ts₁ ts₂

/-- Definition 4 (Ping-pong Adversary) of Dodis–Fiore (Sec. 2.1):
the adversary is "ping-pong" iff at least one of its oracle session
transcripts matches the challenge transcript.

Following the paper's convention `T ⊆ T*` (Definition 3, the matching
relation), the oracle transcript is the first argument of `Matches` and the
challenge is the second. -/
def IsPingPong (steps : List LinearStep)
    (challenge : TimestampedTranscript steps)
    (oracleTranscripts : List (TimestampedTranscript steps)) : Prop :=
  ∃ T ∈ oracleTranscripts, Matches steps T challenge

end TimestampedTranscript

end MessageTransmissionProtocol
end Interaction
