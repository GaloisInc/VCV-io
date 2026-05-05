/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.Interaction.TwoParty.Decoration

/-!
# Timestamped Transcripts, Matching, and Ping-Pong Adversaries

Definitions 2, 3, and 4 of Dodis–Fiore (Sec. 2.1, "Unilaterally-Authenticated
Key Exchange").

* `Spec.TimestampedTranscript spec` — a `Spec.Transcript`-shaped path with a
  `ℕ` timestamp on each move (Definition 2). The paper's "global counter"
  ticks once per message sent across all sessions; we record the resulting
  per-message stamp.
* `Spec.TimestampedTranscript.untimed` / `.timestamps` / `.Monotone` —
  projections and the strict-monotone-timestamps invariant inherited from
  the global counter.
* `Spec.TimestampedTranscript.Matches` — Definition 3, per-position form. The
  relation is asymmetric. With `Monotone` on each operand it is equivalent to
  the paper's full chain `t_1 < t'_1 < t'_2 < t_2 < …` (or its dual when `S`
  speaks first), by transitivity.
* `Spec.TimestampedTranscript.IsPingPong` — Definition 4, asserting that at
  least one of the adversary's oracle session transcripts matches the
  challenge transcript.

iCCA / iCMA security (Definitions 5 & 6) are deferred to sibling files.
-/

universe u

namespace Interaction

namespace Spec

/-- A protocol transcript with a `ℕ` timestamp on each move (Definition 2 of
Dodis–Fiore, Sec. 2.1). The shape mirrors `Spec.Transcript`, with one timestamp
recorded for each message in the path. -/
def TimestampedTranscript : Spec.{u} → Type u
  | .done => PUnit
  | .node X rest => (x : X) × ℕ × TimestampedTranscript (rest x)

namespace TimestampedTranscript

/-- Drop the timestamps to recover the underlying `Spec.Transcript`. -/
def untimed : {spec : Spec.{u}} → TimestampedTranscript spec → Transcript spec
  | .done, _ => ⟨⟩
  | .node _ _, ⟨x, _, ts⟩ => ⟨x, ts.untimed⟩

/-- Extract the list of timestamps along the path, root → leaf. -/
def timestamps : {spec : Spec.{u}} → TimestampedTranscript spec → List ℕ
  | .done, _ => []
  | .node _ _, ⟨_, t, ts⟩ => t :: ts.timestamps

/-- Strictly increasing timestamps along the path: the invariant inherited
from the paper's global counter. Equivalent to monotonicity of the
`timestamps` list under `· < ·`. -/
def Monotone {spec : Spec.{u}} (ts : TimestampedTranscript spec) : Prop :=
  ts.timestamps.IsChain (· < ·)

end TimestampedTranscript

end Spec

/-- Definition 3 (Matching Transcripts) of Dodis–Fiore, per-position form:
messages are equal pointwise, and at each move the timestamp comparison is
dictated by which party speaks. With `Spec.TimestampedTranscript.Monotone` on
each argument, this is equivalent to the paper's full chain
`t_1 < t'_1 < t'_2 < t_2 < …` (or the dual when `S` speaks first), by
transitivity.

Asymmetric: `Matches roles t₁ t₂` is the paper's `t₁ ⊆ t₂` (the relation
is not symmetric, hence the use of `⊆` rather than an equivalence symbol).

The message-equality witness is packaged as an existential because the
recursive call needs to transport the second transcript's tail across that
equation. -/
def Spec.TimestampedTranscript.Matches :
    {spec : Spec.{u}} → RoleDecoration spec →
    Spec.TimestampedTranscript spec → Spec.TimestampedTranscript spec → Prop
  | .done, _, _, _ => True
  | .node _ _, ⟨.sender, rRest⟩, ⟨x₁, t₁, ts₁⟩, ⟨x₂, t₂, ts₂⟩ =>
      ∃ h : x₂ = x₁, t₂ < t₁ ∧
        Spec.TimestampedTranscript.Matches (rRest x₁) ts₁ (h ▸ ts₂)
  | .node _ _, ⟨.receiver, rRest⟩, ⟨x₁, t₁, ts₁⟩, ⟨x₂, t₂, ts₂⟩ =>
      ∃ h : x₂ = x₁, t₁ < t₂ ∧
        Spec.TimestampedTranscript.Matches (rRest x₁) ts₁ (h ▸ ts₂)

/-- Definition 4 (Ping-pong Adversary) of Dodis–Fiore (Sec. 2.1):
the adversary is "ping-pong" iff at least one of its oracle session
transcripts matches the challenge transcript.

Following the paper's convention `T ⊆ T*` (Definition 3, the matching
relation), the oracle transcript is the first argument of `Matches` and the
challenge is the second. -/
def Spec.TimestampedTranscript.IsPingPong {spec : Spec.{u}}
    (roles : RoleDecoration spec)
    (challenge : Spec.TimestampedTranscript spec)
    (oracleTranscripts : List (Spec.TimestampedTranscript spec)) : Prop :=
  ∃ T ∈ oracleTranscripts,
    Spec.TimestampedTranscript.Matches roles T challenge

end Interaction
