/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.UAKE.Defs
import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# PQXDH (Post-Quantum Extended Diffie–Hellman) as a UAKE Protocol

A Lean formalization of the PQXDH key agreement protocol from Sec. 3 of
the Signal specification *The PQXDH Key Agreement Protocol* (Kret &
Schmidt), expressed as a `UAKEProtocol` in our framework.

## Overview

PQXDH establishes a shared session key between an initiator (Alice) and a
responder (Bob, who holds a long-term identity key). Bob publishes a
*prekey bundle* containing his identity key, signed prekey, optional
one-time prekey, and a signed post-quantum KEM prekey. Alice fetches the
bundle, verifies signatures, and sends an initial message containing her
identity key, ephemeral key, and a KEM ciphertext. Both parties then
derive a shared session key from four DH outputs and a KEM-shared secret
combined through a KDF.

In our UAKE model:

* `T` (responder, keyed) ≅ Bob: holds the prekey-bundle secrets (`TK`).
* `U` (initiator, unkeyed) ≅ Alice: receives Bob's bundle (`UK`).
* The protocol is one round with Alice speaking; Bob's processing
  happens at message reception (no explicit Bob-spoken message), which
  technically violates the WLOG-T-speaks-last convention from
  Dodis–Fiore.
* Alice's identity key `IK_A` is generated *per session* in this UAKE
  view. In the original PQXDH it is a long-term key, but the UAKE
  framework only authenticates `T`.
* This file follows the spec's *with-OPK* variant.
* AEAD encryption / associated data are *not* modeled; we capture only
  the key-agreement structure.

## Instantiation

The cryptographic primitives are reused from the existing repo:

* The signature scheme is a `SignatureAlg m Bytes CurvePK CurveSK Sig`
  (`VCVio/CryptoFoundations/SignatureAlg.lean`). This abstracts the
  paper's recommended XEdDSA over curve25519/curve448.
* The post-quantum KEM is a `KEMScheme m KEMSS KEMPK KEMSK KEMCT`
  (`VCVio/CryptoFoundations/KeyEncapMech.lean`). This abstracts the
  paper's recommended ML-KEM (CRYSTALS-Kyber-1024).
* `dh`, `kdf`, encodings, and KEM decapsulation are taken to be *pure*
  deterministic functions, matching their nature in the spec (HKDF and
  EC scalar-mult have no randomness).

## Correctness

`pqxdh_PerfectlyCorrect` shows that, given perfectly correct primitives
plus DH symmetry over honest keypairs, the resulting `UAKEProtocol` is
perfectly correct in the sense of `UAKEProtocol.PerfectlyCorrect`
(Definition 7 of Dodis–Fiore).
-/

open Interaction
open Interaction.MessageTransmissionProtocol
open Interaction.UAKE

namespace Examples.PQXDH

/-! ## Cryptographic primitives needed for PQXDH -/

/-- Cryptographic primitives needed to instantiate the PQXDH key agreement
protocol: a Diffie–Hellman group, a curve-keyed signature scheme, a
post-quantum KEM, and a KDF combining four DH outputs with the KEM-shared
secret into a session key.

`dh`, `kdf`, encodings, and `kem.decaps`'s deterministic core are kept
pure since they have no randomness in the spec. Signature, KEM keygen,
and KEM encapsulation remain monadic (genuine randomness sources). -/
structure PQXDHParams (m : Type → Type) [Monad m] where
  -- Curves
  CurvePK : Type
  CurveSK : Type
  DHResult : Type
  /-- DH function. Pure: by spec, `DH(PK1, PK2)` is a deterministic
  Montgomery-curve scalar multiplication. -/
  dh : CurveSK → CurvePK → DHResult
  -- Bytes / encodings
  Bytes : Type
  encodeEC : CurvePK → Bytes
  -- Signature scheme (curve-keyed; XEdDSA)
  Signature : Type
  sig : SignatureAlg m Bytes CurvePK CurveSK Signature
  -- Post-quantum KEM (ML-KEM-style)
  KEMPK : Type
  KEMSK : Type
  KEMCT : Type
  KEMSS : Type
  kem : KEMScheme m KEMSS KEMPK KEMSK KEMCT
  encodeKEM : KEMPK → Bytes
  -- KDF
  SessionKey : Type
  /-- The KDF takes the four DH outputs `DH1..DH4` and the KEM-shared
  secret `SS`, and produces a session key. Pure: HKDF is deterministic. -/
  kdf : DHResult → DHResult → DHResult → DHResult → KEMSS → SessionKey

variable {m : Type → Type} [Monad m] (params : PQXDHParams m)

/-! ## Protocol-specific record types -/

/-- Bob's prekey bundle (the public key `UK` in UAKE terms). -/
structure Bundle where
  /-- Bob's long-term identity key `IK_B`. -/
  ik : params.CurvePK
  /-- Bob's signed prekey `SPK_B`. -/
  spk : params.CurvePK
  /-- Signature on `EncodeEC(SPK_B)` under `IK_B`. -/
  spkSig : params.Signature
  /-- Bob's one-time prekey `OPK_B`. -/
  opk : params.CurvePK
  /-- Bob's PQKEM prekey `PQPK_B`. -/
  pqpk : params.KEMPK
  /-- Signature on `EncodeKEM(PQPK_B)` under `IK_B`. -/
  pqpkSig : params.Signature

/-- Bob's secret keys (the secret key `TK` in UAKE terms). -/
structure Secrets where
  ikSk : params.CurveSK
  spkSk : params.CurveSK
  opkSk : params.CurveSK
  pqpkSk : params.KEMSK

/-- Alice's initial message: `(IK_A, EK_A, CT)`. -/
structure Message where
  ika : params.CurvePK
  eka : params.CurvePK
  ct : params.KEMCT

/-! ## The PQXDH protocol -/

/-- Construct the PQXDH UAKE protocol from cryptographic primitives.

* **Setup** (Sec. 3.2 *Publishing keys*): Bob generates his identity
  key, signed prekey, one-time prekey, and signed PQKEM prekey, then
  signs `SPK_B` and `PQPK_B` with `IK_B`.
* **Initiator** (Sec. 3.3 *Sending the initial message*): Alice
  verifies the two signatures, generates her ephemeral identity key
  `IK_A` and ephemeral key `EK_A`, KEM-encapsulates to `PQPK_B`,
  computes the four DH outputs, derives `SK` via `KDF`, and sends
  `(IK_A, EK_A, CT)`. She accepts iff signatures verify.
* **Responder** (Sec. 3.4 *Receiving the initial message*): Bob KEM-
  decapsulates `CT`, computes the four DH outputs, derives `SK` via
  `KDF`. He accepts iff KEM decapsulation succeeds. -/
noncomputable def pqxdhProtocol :
    UAKEProtocol m params.SessionKey (Bundle params) (Secrets params) where
  steps := [⟨Message params, .receiver⟩]
  setup := do
    let (ik, ikSk) ← params.sig.keygen
    let (spk, spkSk) ← params.sig.keygen
    let spkSig ← params.sig.sign ik ikSk (params.encodeEC spk)
    let (opk, opkSk) ← params.sig.keygen
    let (pqpk, pqpkSk) ← params.kem.keygen
    let pqpkSig ← params.sig.sign ik ikSk (params.encodeKEM pqpk)
    pure (
      { ik := ik, spk := spk, spkSig := spkSig
        opk := opk, pqpk := pqpk, pqpkSig := pqpkSig },
      { ikSk := ikSk, spkSk := spkSk, opkSk := opkSk, pqpkSk := pqpkSk })
  responder secrets := fun msg => do
    match ← params.kem.decaps secrets.pqpkSk msg.ct with
    | none => pure none
    | some ss =>
      let dh1 := params.dh secrets.spkSk msg.ika
      let dh2 := params.dh secrets.ikSk msg.eka
      let dh3 := params.dh secrets.spkSk msg.eka
      let dh4 := params.dh secrets.opkSk msg.eka
      pure (some (params.kdf dh1 dh2 dh3 dh4 ss))
  initiator bundle := do
    let sigSpkOk ← params.sig.verify bundle.ik (params.encodeEC bundle.spk) bundle.spkSig
    let sigPqpkOk ← params.sig.verify bundle.ik (params.encodeKEM bundle.pqpk) bundle.pqpkSig
    let (ika, ikaSk) ← params.sig.keygen
    let (eka, ekaSk) ← params.sig.keygen
    let (ct, ss) ← params.kem.encaps bundle.pqpk
    let dh1 := params.dh ikaSk bundle.spk
    let dh2 := params.dh ekaSk bundle.ik
    let dh3 := params.dh ekaSk bundle.spk
    let dh4 := params.dh ekaSk bundle.opk
    let sk := params.kdf dh1 dh2 dh3 dh4 ss
    let msg : Message params := { ika := ika, eka := eka, ct := ct }
    pure (msg, if sigSpkOk && sigPqpkOk then some sk else none)

/-! ## Correctness

PQXDH is correct (Definition 7 of Dodis–Fiore) when its primitives are
correct: the signature scheme is perfectly complete, the KEM is perfectly
correct, and the Diffie–Hellman function is symmetric over honest
keypairs (`dh sk₁ pk₂ = dh sk₂ pk₁` whenever both `(pk₁, sk₁)` and
`(pk₂, sk₂)` come from honest `keygen` runs). -/

/-- The PQXDH parameters are *correct* (pointwise / support-based form,
strong enough to drive the correctness proof).

Pointwise rather than `Pr[…] = 1` because the proof needs to reason about
*every* sample-tape in the support of `CorrectExp` — not just the
marginal distribution. Each predicate constrains the support of the
relevant sub-computation.

* `sigCompletes`: for any `(pk, sk)` produced by `keygen` and any `σ`
  produced by `sign pk sk msg`, *every* output of `verify pk msg σ` is
  `true`. Stronger than `params.sig.PerfectlyComplete runtime`, but
  follows from it together with `NeverFail` for `verify`.
* `kemCorrect`: for any `(pk, sk)` and `(ct, ss)` from `keygen` /
  `encaps`, *every* output of `decaps sk ct` is `some ss`.
* `dhSymm`: for any two `keygen`-produced pairs `(pk₁, sk₁), (pk₂, sk₂)`,
  the DH outputs are symmetric: `dh sk₁ pk₂ = dh sk₂ pk₁`. -/
structure PQXDHCorrect (params : PQXDHParams m) (runtime : ProbCompRuntime m) : Prop where
  /-- Signature verification of an honest signature is always `true`. -/
  sigCompletes : ∀ (msg : params.Bytes) (pk : params.CurvePK) (sk : params.CurveSK)
      (σ : params.Signature),
    (pk, sk) ∈ support (runtime.evalDist params.sig.keygen) →
    σ ∈ support (runtime.evalDist (params.sig.sign pk sk msg)) →
    support (runtime.evalDist (params.sig.verify pk msg σ)) ⊆ {true}
  /-- KEM decapsulation of an honest encapsulation always recovers the
  shared secret. -/
  kemCorrect : ∀ (pk : params.KEMPK) (sk : params.KEMSK)
      (ct : params.KEMCT) (ss : params.KEMSS),
    (pk, sk) ∈ support (runtime.evalDist params.kem.keygen) →
    (ct, ss) ∈ support (runtime.evalDist (params.kem.encaps pk)) →
    support (runtime.evalDist (params.kem.decaps sk ct)) ⊆ {some ss}
  /-- DH symmetry over honest keypairs. -/
  dhSymm : ∀ (pk₁ : params.CurvePK) (sk₁ : params.CurveSK)
      (pk₂ : params.CurvePK) (sk₂ : params.CurveSK),
    (pk₁, sk₁) ∈ support (runtime.evalDist params.sig.keygen) →
    (pk₂, sk₂) ∈ support (runtime.evalDist params.sig.keygen) →
    params.dh sk₁ pk₂ = params.dh sk₂ pk₁

/-- **PQXDH correctness theorem (Definition 7).** If the underlying
primitives are correct (signatures complete, KEM correct, DH symmetric),
then `pqxdhProtocol params` is perfectly correct as a UAKE protocol.

Proof structure:

1. Unfold `UAKEProtocol.PerfectlyCorrect`, `.CorrectExp`, `.exec`,
   `execBoth`, `pqxdhProtocol`. The 1-step `.receiver` `execBoth` reduces
   to `let (msg, kU) ← initiator bundle; let kT ← responder secrets msg;
   pure (kT, kU)`.

2. Trace through the do-block: keygens produce honest pairs; sigs
   produce signatures that verify (by `sigComplete`); KEM encaps then
   decaps recovers `ss` (by `kemCorrect`); the DH outputs match by
   `dhSymm`; both sides apply the same pure `kdf` to the same inputs,
   giving a common session key `sk`.

3. The conditional `kU.isSome ∧ kT.isSome → kU = kT` then evaluates to
   `True`, so `decide` is `true` and `Pr[= true | …] = 1`. -/
theorem pqxdh_PerfectlyCorrect
    (params : PQXDHParams m) (runtime : ProbCompRuntime m)
    [DecidableEq params.SessionKey]
    (hRuntimeNoFail : Pr[⊥ | runtime.evalDist (pqxdhProtocol params).CorrectExp] = 0)
    (hRuntimeBind : ∀ {α β : Type} (mx : m α) (my : α → m β),
      runtime.evalDist (mx >>= my) =
        runtime.evalDist mx >>= fun x => runtime.evalDist (my x))
    (hRuntimePure : ∀ {α : Type} (x : α), runtime.evalDist (pure x : m α) = pure x)
    (h : PQXDHCorrect params runtime) :
    (pqxdhProtocol params).PerfectlyCorrect runtime := by
  -- Strategy: show `support (runtime.evalDist CorrectExp) ⊆ {true}`, then
  -- apply `probOutput_eq_one_of_support_subset_singleton`.
  apply probOutput_eq_one_of_support_subset_singleton hRuntimeNoFail
  intro b hb
  -- Unfold the protocol. After unfolding, `hb` is membership in
  -- `support (runtime.evalDist (do ...))`. Use `hRuntimeBind` /
  -- `hRuntimePure` to push `runtime.evalDist` through every bind, then
  -- `mem_support_bind_iff` / `mem_support_pure_iff` to peel existentials.
  simp only [UAKE.UAKEProtocol.CorrectExp,
    UAKE.UAKEProtocol.exec, UAKE.execBoth, pqxdhProtocol,
    bind_assoc, pure_bind, bind_pure, hRuntimeBind, hRuntimePure,
    mem_support_bind_iff, mem_support_pure_iff] at hb
  -- After simp, `hb` is a chain of existentials. Peel them off.
  obtain ⟨⟨ik, ikSk⟩, hIk, hb⟩ := hb
  obtain ⟨⟨spk, spkSk⟩, hSpk, hb⟩ := hb
  obtain ⟨spkSig, hSpkSig, hb⟩ := hb
  obtain ⟨⟨opk, opkSk⟩, hOpk, hb⟩ := hb
  obtain ⟨⟨pqpk, pqpkSk⟩, hPqpk, hb⟩ := hb
  obtain ⟨pqpkSig, hPqpkSig, hb⟩ := hb
  obtain ⟨sigSpkOk, hSigSpkOk, hb⟩ := hb
  obtain ⟨sigPqpkOk, hSigPqpkOk, hb⟩ := hb
  obtain ⟨⟨ika, ikaSk⟩, hIka, hb⟩ := hb
  obtain ⟨⟨eka, ekaSk⟩, _hEka, hb⟩ := hb
  obtain ⟨⟨ct, ss⟩, hCt, hb⟩ := hb
  obtain ⟨mss, hMss, hb⟩ := hb
  -- Now `hb : b = decide (kU.isSome ∧ kT.isSome → kU = kT)` for the
  -- specific kU and kT computed from the sampled values.
  --
  -- Use the primitives' correctness:
  --
  -- 1. `sigSpkOk = true`: from `h.sigCompletes` applied to (ik, ikSk),
  --    spkSig (which is `sign ik ikSk (encodeEC spk)`).
  have hSigSpkTrue : sigSpkOk = true :=
    h.sigCompletes _ ik ikSk spkSig hIk hSpkSig hSigSpkOk
  -- 2. `sigPqpkOk = true`: similarly.
  have hSigPqpkTrue : sigPqpkOk = true :=
    h.sigCompletes _ ik ikSk pqpkSig hIk hPqpkSig hSigPqpkOk
  -- 3. `mss = some ss`: from `h.kemCorrect`.
  have hMssEq : mss = some ss :=
    h.kemCorrect pqpk pqpkSk ct ss hPqpk hCt hMss
  -- 4. DH symmetry: each of DH1..DH4 equals across both sides.
  have hDh1 : params.dh ikaSk spk = params.dh spkSk ika := h.dhSymm _ _ _ _ hIka hSpk
  have hDh2 : params.dh ekaSk ik = params.dh ikSk eka := h.dhSymm _ _ _ _ _hEka hIk
  have hDh3 : params.dh ekaSk spk = params.dh spkSk eka := h.dhSymm _ _ _ _ _hEka hSpk
  have hDh4 : params.dh ekaSk opk = params.dh opkSk eka := h.dhSymm _ _ _ _ _hEka hOpk
  -- Substitute and reduce.
  subst hSigSpkTrue
  subst hSigPqpkTrue
  subst hMssEq
  simp only [Bool.and_self, hDh1, hDh2, hDh3, hDh4,
    hRuntimePure, Option.isNone] at hb
  -- After all simplifications, `hb` is reducible to `b = true`.
  simpa using hb

end Examples.PQXDH
