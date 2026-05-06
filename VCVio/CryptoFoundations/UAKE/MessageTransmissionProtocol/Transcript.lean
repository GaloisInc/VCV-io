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
* `TimestampedTranscript.untimed` / `.timestamps` — projections.
* `TimestampedTranscript.Matches` — Definition 3, captured as one strict
  zigzag chain through the two transcripts. The chain check operates on
  roles and timestamps only; move types appear only to type the
  message-equality predicate.
* `TimestampedTranscript.IsPingPong` — Definition 4, asserting that at least
  one of the adversary's oracle session transcripts matches the challenge
  transcript.

Throughout this file we follow the paper's notation: `T` and `T'` denote the
two transcripts being compared, with `t` (no prime) the timestamp from `T`
and `t'` (prime) the timestamp from `T'`. At a sender step the chain
contributes `[t', t]` (`t'` first) and at a receiver step `[t, t']`.

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

/-- Pointwise message equality between two transcripts of the same shape.
The Def. 3 component "`M_i = M'_i` for all `i`". -/
def messagesEqual : (steps : List LinearStep) →
    TimestampedTranscript steps → TimestampedTranscript steps → Prop
  | [], _, _ => True
  | _ :: _, ⟨m, _, ts⟩, ⟨m', _, ts'⟩ =>
      m = m' ∧ messagesEqual _ ts ts'

/-- The interleaved timestamp sequence from two transcripts. At each step
the role determines the local order: a receiver step contributes `[t, t']`
(`T` first); a sender step contributes `[t', t]` (`T'` first). Concatenated
across all steps, the resulting list is exactly the sequence of timestamps
appearing in the paper's chain `t_1 < t'_1 < t'_2 < t_2 < …` (or its dual
when `S` speaks first). The chain check operates on this list — only roles
and timestamps participate; `step.moveType` plays no role in it. -/
def interleavedTimestamps : (steps : List LinearStep) →
    TimestampedTranscript steps → TimestampedTranscript steps → List ℕ
  | [], _, _ => []
  | step :: rest, ⟨_, t, ts⟩, ⟨_, t', ts'⟩ =>
      (match step.speaker with
        | .receiver => [t, t']
        | .sender => [t', t]) ++
      interleavedTimestamps rest ts ts'

/-- Definition 3 of Dodis–Fiore (Sec. 2.1, "Matching Transcripts"):
`T ⊆ T'` iff messages are pointwise equal and the interleaved timestamp
sequence is strictly increasing. -/
def Matches (steps : List LinearStep)
    (T T' : TimestampedTranscript steps) : Prop :=
  messagesEqual steps T T' ∧
  (interleavedTimestamps steps T T').IsChain (· < ·)

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

/-! ## Examples

Test cases that exercise `Matches` on small concrete inputs. These also
serve as documentation of how the predicate behaves in the simplest
non-trivial cases. -/

/-- Empty transcripts trivially match. -/
example : Matches [] () () := by
  refine ⟨trivial, ?_⟩
  simp [interleavedTimestamps]

/-- 1-round single-sender protocol: `Matches T T'` requires `t' < t`
(paper notation) at the sender step, here `5 < 10`. -/
example : Matches [⟨ℕ, .sender⟩] ⟨42, 10, ()⟩ ⟨42, 5, ()⟩ := by
  refine ⟨⟨rfl, trivial⟩, ?_⟩
  simp [interleavedTimestamps, List.isChain_cons]

/-- The same protocol but with the timestamps in the wrong direction —
`t' ≮ t` here, so the chain fails. -/
example : ¬ Matches [⟨ℕ, .sender⟩] ⟨42, 5, ()⟩ ⟨42, 10, ()⟩ := by
  rintro ⟨_, hChain⟩
  simp [interleavedTimestamps, List.isChain_cons] at hChain

/-- Mismatched messages defeat `messagesEqual`, regardless of timestamps. -/
example : ¬ Matches [⟨ℕ, .sender⟩] ⟨42, 10, ()⟩ ⟨7, 5, ()⟩ := by
  rintro ⟨⟨h, _⟩, _⟩
  exact absurd h (by decide)

/-- A 2-round R-then-S protocol with the paper's standard chain pattern
`t_1 < t'_1 < t'_2 < t_2`. The interleaved list here is `[1, 2, 3, 4]`. -/
example : Matches [⟨ℕ, .receiver⟩, ⟨ℕ, .sender⟩]
    ⟨0, 1, 0, 4, ()⟩ ⟨0, 2, 0, 3, ()⟩ := by
  refine ⟨⟨rfl, rfl, trivial⟩, ?_⟩
  simp [interleavedTimestamps, List.isChain_cons]

/-- A sender-then-sender configuration where each step's local constraint
holds (`t'_1 < t_1` is `4 < 5`; `t'_2 < t_2` is `3 < 8`) but the cross-step
link `t_1 < t'_2` (`5 < 3`) fails. The chain rules this case out. -/
example : ¬ Matches [⟨ℕ, .sender⟩, ⟨ℕ, .sender⟩]
    ⟨0, 5, 0, 8, ()⟩ ⟨0, 4, 0, 3, ()⟩ := by
  rintro ⟨_, hChain⟩
  simp [interleavedTimestamps, List.isChain_cons] at hChain

end TimestampedTranscript

end MessageTransmissionProtocol
end Interaction
