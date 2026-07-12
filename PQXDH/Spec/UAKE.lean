/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import PQXDH.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.ToMathlib
import PQXDH.ToVCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# PQXDH modeled as a DF'17-style UAKE

Model simplifications
* **Unilateral authentication:** UAKE is unilaterally authenticated. In
  principle, it should be possible to model a protocol in both directions to
  show multilateral authentication. However, we model security only for the
  "Bob authenticates to Alice" direction. This is because UAKE security
  requires explicit authentication, and Alice's authentication to Bob is
  implicit via the adversary being unable to compute the DH output, rather than
  relying on Alice's signature (she signs nothing).
* **SUF-CMA signature (not EUF-CMA):** Since UAKE is a
  transcript-matching-style definition, our security theorems are subject to
  harmless but definition-breaking "no-match" attacks on the signature scheme.
  See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS
  2017) for a reference on attacks of this kind.
* **Bob's extra message:** In the PQXDH spec, the exchange ends at Alice's
  first message to Bob, but UAKE requires that the last message be sent by the
  keyed party (Bob). Therefore we add an extra message from Bob under the AEAD
  at the end of the protocol. This would represent the second message in the
  conversation between Alice and Bob.
* **Medium-term secrets as long-term:** The spec describes SPK and PQSPK as
  "changed periodically", but the UAKE security game only allows for permanent
  (via setup) and per-session (via init) keys. We model SPK (and its signature)
  as permanent, along with IK{A|B}.
* **No fallback KEM key:** We do not (currently) model the spec's last-resort
  KEM key (PQSPK). We generate a one-time KEM key (PQOPKᵢ) every time. This is
  a pure simplification, and we plan to extend the model to include the
  last-resort KEM key in the future.

Protocol questions:
* **Key reuse between DH and SignatureAlg:** We assume that Bob's identity key
  contains separate keys for DH exchange and signing. This matches the "no key
  reuse" simplification mentioned in Sec. 4 of the spec that other formal
  analyses required.
* **Separate AEAD key:** The PQXDH spec uses the same KDF output for both
  Alice's AEAD key and the final result of the key exchange, but this seems to
  preclude key indistinguishability. This is because the adversary can try
  using the candidate key to decrypt Alice's message. This will fail for a
  random key (with high likelihood) but succeed for the real key, thus
  distinguishing them. The spec allows KA to be SK or PRF(SK, ·), but both
  variants break key indistinguishability. This could be easily fixed by using
  the KDF output as the key to a PRF that generates **both** SK and KA, but
  the spec **only describes a PRF-derived KA**, which is insufficient. We
  sidestep this and model the final key and Alice's AEAD (and Bob's AEAD key;
  see bullet 3 of "Model simplifications") as separate KDF outputs.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def recipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (RecipientIdentity F G SPK SSK S)
      (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

section CorrectnessLemmas

private lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

private lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

private lemma fst_eq_smul_of_mem_support_dhKeygen
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G} {x : G × F}
    (hx : x ∈ support (dhKeygen (F := F) gen)) : x.1 = x.2 • gen := by
  simp only [dhKeygen, mem_support_bind_iff, mem_support_uniformSample, support_pure,
    Set.mem_singleton_iff, true_and] at hx
  obtain ⟨sk, rfl⟩ := hx
  rfl

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : G ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

private lemma decaps_eq_some_of_perfectlyCorrect [DecidableEq SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqkem.keygen)
    {cs : CT × SS} (hcs : cs ∈ support (P.pqkem.encaps kp.1))
    {r : Option SS} (hr : r ∈ support (P.pqkem.decaps kp.2 cs.1)) : r = some cs.2 := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hmem : decide (r = some cs.2) ∈ support P.pqkem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨cs, hcs, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
    simp
  rw [h] at hmem
  simpa using hmem

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : K) (ad : G × G × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample K, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

private lemma mem_support_initiate
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : InitiatorParameters F G SPK Msg} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {r : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
    ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
    ∃ ctxt ∈ support (P.aead.encrypt
        (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
          Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.1
        (p.ikA.1, p.ikB, bundle.pqpkB.1) p.msg),
      r = some (⟨p.ikA.1, ekA.1, cs.1, bundle.spkB.2, bundle.pqpkB.2,
          Option.map Prod.snd bundle.opkB, ctxt⟩,
        ⟨(P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).1,
          (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.2,
          (p.ikA.1, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := hr
  exact ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩

private lemma dh_comm [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G}
    {x y : G × F} (hx : x ∈ support (dhKeygen (F := F) gen))
    (hy : y ∈ support (dhKeygen (F := F) gen)) : DH x.2 y.1 = DH y.2 x.1 := by
  rw [fst_eq_smul_of_mem_support_dhKeygen hx, fst_eq_smul_of_mem_support_dhKeygen hy,
    DH, DH, smul_smul, smul_smul, mul_comm]

private lemma mem_support_accept
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : RecipientParameters F G PQPK PQSK SPK SSK S}
    {im : InitialMessage G CT C IdC IdK} {ss : SS} {m₀ : Msg}
    {r : Option (SessionContext G PQPK Msg K)}
    (hid₁ : im.idSPK = P.idEC p.spkB.1)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = Option.map (fun opk => P.idEC opk.1) p.opkB)
    (hdec : ∀ o ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct), o = some ss)
    (hdecr : P.aead.decrypt
        (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.1
        (im.ikA, p.ikB.1, p.pqpkB.1) im.ctxt = some m₀)
    (hr : r ∈ support (accept P p im)) :
    r = some ⟨(P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).1,
      (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.2,
      (im.ikA, p.ikB.1, p.pqpkB.1), m₀⟩ := by
  simp only [accept, hid₁, hid₂, hid₃, ne_eq, not_true, or_self, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, o, ho, hr⟩ := hr
  obtain rfl := hdec _ ho
  simp only [hdecr, support_pure, Set.mem_singleton_iff] at hr
  exact hr

private lemma opkB_mem_of_genOPK {F G : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    {gen : G} {hasOPK : Bool} {opkB : Option (G × F)}
    (h : opkB ∈ support (genOPK gen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support (dhKeygen (F := F) gen) := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

private lemma run_support_initiator
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
  obtain ⟨conf, hconf, rfl⟩ := hsr
  have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
  simp only [confirm, hconfirm, mem_support_bind_iff] at hy
  simp only [if_true, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, rfl, hy⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2⟩ := hout
  exact ⟨_, h1, h2⟩

private lemma run_support_recipient
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, spkSigB⟩ ⟨ikA, ikB.1, sigkB.1, msg⟩ (4 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
  obtain ⟨conf, hconf, rfl⟩ := hsr
  have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
  simp only [confirm, hconfirm, mem_support_bind_iff] at hy
  simp only [if_true, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, rfl, hy⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2⟩ := hout
  exact ⟨_, h1, h2⟩

end CorrectnessLemmas

theorem uakeInitiator_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hspkSigB hrun

theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, rfl⟩,
    hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hspkSigB hrun

def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type}
    {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

private lemma finalize_true_add_false_eq_one {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (K1 : Option K)
    (hKb : cr.K0 = K1) :
    Pr[= true | UAKE.finalize A st cr true K1] +
      Pr[= true | UAKE.finalize A st cr false K1] = 1 := by
  obtain ⟨aSt, env, tk⟩ := st
  simp only [UAKE.finalize, hKb, ite_self, monadLift_self]
  generalize (simulateQ (UAKE.oracleImpl proto tk) (A.post aSt K1)).run env = run
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add,
    ← tsum_probOutput_of_liftM_PMF run]
  refine tsum_congr fun x => ?_
  have hsum : Pr[= true | if UAKE.fullPingPong x.2 cr = true then ($ᵗ Bool)
        else pure (x.1 == true)] +
      Pr[= true | if UAKE.fullPingPong x.2 cr = true then ($ᵗ Bool)
        else pure (x.1 == false)] = 1 := by
    cases hfpp : UAKE.fullPingPong x.2 cr
    · cases hx : x.1 <;> simp
    · simp [probOutput_uniformSample, Fintype.card_bool, ENNReal.inv_two_add_inv_two]
  rw [← mul_add, hsum, mul_one]

private lemma finalize_none_half {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (hK0 : cr.K0 = none) :
    Pr[= true | do let b ← $ᵗ Bool; UAKE.finalize A st cr b none] = 1 / 2 := by
  rw [probOutput_bind_uniformBool (fun b => UAKE.finalize A st cr b none) true,
    finalize_true_add_false_eq_one A st cr none hK0]

def kdfPRF [SampleableType SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme SS (G × G × G × Option G) (K × K × K) where
  keygen := $ᵗ SS
  eval := fun ss q => P.kdf (q.1, q.2.1, q.2.2.1, q.2.2.2, ss)

def kdfPRFDH [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme F (G × G × Option G × SS) (K × K × K) where
  keygen := $ᵗ F
  eval := fun c q => P.kdf (q.1, q.2.1, c • P.gen, q.2.2.1, q.2.2.2)

private lemma probOutput_bind_if_true_uniformBool {α : Type} (m : ProbComp α) (c : α → Bool) :
    Pr[= true | do let x ← m; if c x then (pure true : ProbComp Bool) else $ᵗ Bool] =
      1 / 2 + Pr[= true | do let x ← m; pure (c x)] / 2 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  conv_rhs => rw [show (1 : ℝ≥0∞) / 2 = (∑' x, Pr[= x | m]) / 2 from by
    rw [tsum_probOutput_of_liftM_PMF]]
  simp only [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  cases hcx : c x
  · simp [probOutput_uniformSample, Fintype.card_bool]
  · have hp : Pr[= x | m] = Pr[= x | m] * 2⁻¹ + Pr[= x | m] * 2⁻¹ := by
      rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    simpa [probOutput_uniformSample, Fintype.card_bool] using hp

def initiateIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, _SS) ← P.pqkem.encaps bundle.pqpkB.1
  let (SK, KA, KB) ← ($ᵗ (K × K × K) : ProbComp _)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1, ekA := ekA.1, ct := CT, idSPK := bundle.spkB.2,
                 idPQPK := bundle.pqpkB.2, idOPK := bundle.opkB.map Prod.snd, ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

private lemma initiateIdeal_verify_of_accept [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (bundle : PreKeyBundle G PQPK S IdC IdK)
    {r : InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K}
    (hr : some r ∈ support (initiateIdeal P p bundle)) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB) := by
  simp only [initiateIdeal] at hr
  split at hr
  · simp at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okSPK, hSPK, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okPQPK, hPQPK, hr⟩ := hr
    split at hr
    · simp at hr
    · rename_i hcond
      cases okSPK <;> cases okPQPK <;> simp_all

def initiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiateIdeal P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← $ᵗ K; pure (some (some SK))
    | _ => pure none

private lemma initiatorIdeal_step_bundle_verify [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (b : PreKeyBundle G PQPK S IdC IdK)
    {st' : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K}
    {w' : Message G PQPK CT S C IdC IdK} {done : Bool}
    (hst : Party.StepResult.acceptAndSend st' w' done ∈
      support ((initiatorIdeal P).step (Sum.inl p) (Message.bundle b))) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC b.spkB.1) b.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM b.pqpkB.1) b.pqpkSigB) := by
  simp only [initiatorIdeal] at hst
  obtain ⟨r, hr, hst⟩ := (mem_support_bind_iff _ _ _).1 hst
  cases r with
  | none => simp at hst
  | some imctx => exact initiateIdeal_verify_of_accept P p b hr

private lemma initiatorIdeal_output_completed [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    {y : Option (Option K)} (hy : y ∈ support ((initiatorIdeal P).output st))
    (hjoin : y.join.isSome) :
    ∃ SK, st = Sum.inr (Sum.inr SK) := by
  cases st with
  | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
             subst hy; simp at hjoin
  | inr st2 =>
    cases st2 with
    | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
               subst hy; simp at hjoin
    | inr SK => exact ⟨SK, rfl⟩

def uakeInitiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdeal P
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toIdeal
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

section SignatureReduction

def publishForger (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK SPK SSK S) :
    OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) (PreKeyBundle G PQPK S IdC IdK) := do
  let pqpkSigB ← liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
    (Sum.inr (EncodeKEM p.pqpkB.1)))
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

def recipientForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party (OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)))
      (RecipientIdentity F G SPK SSK S) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← liftM (genOPK P.gen hasOPK)
    let pqpkB ← liftM P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publishForger P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← liftM (accept P p im) with
        | some ctx => do
            let conf ← liftM (P.aead.encrypt ctx.kb ctx.ad ctx.msg)
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

private lemma simulateQ_publishForger
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK SPK SSK S) (pk : SPK) (sk : SSK) :
    simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (publishForger P p) =
    (do
      let pqpkSigB ← P.sig.signingOracle pk sk (EncodeKEM p.pqpkB.1)
      pure { ikB := p.ikB.1
             spkB := (p.spkB.1, P.idEC p.spkB.1)
             spkSigB := p.spkSigB
             pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
             pqpkSigB := pqpkSigB
             opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }) := by
  unfold publishForger
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

private lemma publishForger_sigkB_irrel
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (ikB : G × F) (s1 s2 : SPK × SSK) (spkB : G × F) (spkSigB : S) (opkB : Option (G × F))
    (pqpkB : PQPK × PQSK) :
    publishForger P ⟨ikB, s1, spkB, spkSigB, opkB, pqpkB⟩
      = publishForger P ⟨ikB, s2, spkB, spkSigB, opkB, pqpkB⟩ := rfl

private lemma recipient_step_sigkB_irrel [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K) (s2 : SPK × SSK)
    (w : Message G PQPK CT S C IdC IdK) :
    (recipient P hasOPK).step
        (Sum.elim (fun p => Sum.inl { p with sigkB := s2 }) Sum.inr st) w
      = (recipient P hasOPK).step st w := by
  cases st <;> cases w <;> rfl

private lemma simulateQ_sigImpl_liftM {α : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (oa : ProbComp α) :
    simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (liftM oa : OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α) =
    (liftM oa : WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp α) := by
  rw [← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left]
  induction oa using OracleComp.inductionOn with
  | pure x => simp [liftM_pure]
  | query_bind t oa ih => simp [ih, liftM_bind]

private lemma fst_run_liftM {α : Type} (oa : ProbComp α) :
    Prod.fst <$> (liftM oa : WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp α).run = oa := by
  rw [WriterT.liftM_def']
  simp [WriterT.run, WriterT.mk, Functor.map_map]

private lemma run_sim_liftM_bind {α β : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (oa : ProbComp α) (f : α → OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) β) :
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (liftM oa >>= f)).run =
    oa >>= fun a => (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (f a)).run := by
  rw [simulateQ_bind, simulateQ_sigImpl_liftM, WriterT.run_bind', WriterT.run_liftM]
  refine Eq.trans (bind_map_left (m := ProbComp) _ _ _) ?_
  refine bind_congr fun a => ?_
  simp only [List.empty_eq, List.nil_append]
  exact id_map _

private lemma run_sim_bind_pure {α β : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (mx : OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α) (g : α → β) :
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (mx >>= fun a => pure (g a))).run =
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      mx).run >>= fun p => pure (g p.1, p.2) := by
  rw [simulateQ_bind, WriterT.run_bind']
  refine bind_congr fun p => ?_
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, Prod.map_apply, id_eq, List.empty_eq,
    List.append_nil]

private lemma fst_run_signingOracle
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (msg : G ⊕ PQPK) :
    Prod.fst <$> (P.sig.signingOracle pk sk msg).run = P.sig.sign pk sk msg := by
  have h := QueryImpl.fst_map_run_withLogging (m := ProbComp) (spec := (G ⊕ PQPK) →ₒ S)
    (fun m => P.sig.sign pk sk m)
    (liftM (OracleSpec.query (spec := (G ⊕ PQPK) →ₒ S) msg))
  simp only [simulateQ_spec_query] at h
  exact h

private lemma run_signingOracle
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (msg : G ⊕ PQPK) :
    (P.sig.signingOracle pk sk msg).run
      = (fun σ => (σ, ([⟨msg, σ⟩] : QueryLog ((G ⊕ PQPK) →ₒ S)))) <$> P.sig.sign pk sk msg := by
  simp only [SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
    WriterT.run_bind', WriterT.run_liftM, WriterT.run_tell,
    List.empty_eq, List.nil_append, List.cons_append, bind_pure_comp, map_bind, monad_norm]
  refine bind_congr fun σ => ?_
  simp only [Function.comp_def, WriterT.run_pure', pure_bind, Prod.map_apply, id_eq,
    List.nil_append, List.empty_eq]

private lemma fst_run_sim_queryBind {α : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (m : G ⊕ PQPK) (f : S → OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
        (m := ProbComp)).liftTarget (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp)
        + P.sig.signingOracle pk sk)
      (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S)) (Sum.inr m)) >>= f)).run =
    P.sig.sign pk sk m >>= fun σ =>
      Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
          (m := ProbComp)).liftTarget (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp)
          + P.sig.signingOracle pk sk)
        (f σ)).run := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, WriterT.fst_map_run_bind']
  exact congrArg (· >>= _) (fst_run_signingOracle P pk sk m)

private lemma run_sim_queryBind_pure {α β : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (m : G ⊕ PQPK) (f : S → OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α) (g : α → β) :
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S)) (Sum.inr m)) >>=
        fun σ => f σ >>= fun a => pure (g a))).run =
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S)) (Sum.inr m)) >>=
        fun σ => f σ)).run >>= fun p => pure (g p.1, p.2) := by
  rw [← bind_assoc]
  exact run_sim_bind_pure P pk sk _ g

private lemma run_simulateQ_publishForger
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK SPK SSK S) (pk : SPK) (sk : SSK) :
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (publishForger P p)).run =
    (do
      let pqpkSigB ← P.sig.sign pk sk (EncodeKEM p.pqpkB.1)
      pure (({ ikB := p.ikB.1
               spkB := (p.spkB.1, P.idEC p.spkB.1)
               spkSigB := p.spkSigB
               pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
               pqpkSigB := pqpkSigB
               opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) } :
                PreKeyBundle G PQPK S IdC IdK),
        ([⟨EncodeKEM p.pqpkB.1, pqpkSigB⟩] :
          QueryLog ((G ⊕ PQPK) →ₒ S)))) := by
  rw [simulateQ_publishForger]
  simp only [WriterT.run_bind', run_signingOracle, WriterT.run_pure', bind_map_left]
  simp only [map_pure, Prod.map_apply, id_eq, List.cons_append, List.nil_append,
    List.empty_eq]

private lemma fst_run_recipientForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (idn : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK)
    (hsig : idn.sigkB = (pk, sk)) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((recipientForger P hasOPK).init idn)).run =
    (recipient P hasOPK).init idn := by
  simp only [recipientForger, recipient, publish, simulateQ_bind, simulateQ_sigImpl_liftM,
    simulateQ_publishForger, simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
    fst_run_liftM, fst_run_signingOracle, hsig]

private lemma run_recipientForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (idn : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) :
    (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((recipientForger P hasOPK).init idn)).run =
    (do
      let opkB ← genOPK P.gen hasOPK
      let pqpkB ← P.pqkem.keygen
      let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
        { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
          opkB := opkB, pqpkB := pqpkB }
      let pqpkSigB ← P.sig.sign pk sk (EncodeKEM p.pqpkB.1)
      pure (Party.InitResult.speakFirst (Sum.inl p)
              (Message.bundle { ikB := p.ikB.1
                                spkB := (p.spkB.1, P.idEC p.spkB.1)
                                spkSigB := p.spkSigB
                                pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
                                pqpkSigB := pqpkSigB
                                opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }),
            ([⟨EncodeKEM p.pqpkB.1, pqpkSigB⟩] :
              QueryLog ((G ⊕ PQPK) →ₒ S)))) := by
  simp only [recipientForger, simulateQ_bind, simulateQ_sigImpl_liftM, simulateQ_pure,
    WriterT.run_bind', WriterT.run_liftM, run_simulateQ_publishForger, WriterT.run_pure',
    bind_map_left]
  simp only [map_bind, map_pure, bind_assoc, pure_bind, Prod.map_apply, id_eq, List.nil_append,
    List.empty_eq, List.append_nil]

private lemma fst_run_recipientForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((recipientForger P hasOPK).step st w)).run =
    (recipient P hasOPK).step st w := by
  cases st with
  | inr SK =>
    cases w <;>
      simp only [recipientForger, recipient, simulateQ_pure, WriterT.fst_map_run_pure']
  | inl p =>
    cases w with
    | initial im =>
      simp only [recipientForger, recipient, simulateQ_bind, simulateQ_sigImpl_liftM,
        WriterT.fst_map_run_bind', fst_run_liftM]
      refine bind_congr fun r => ?_
      cases r with
      | none => simp only [simulateQ_pure, WriterT.fst_map_run_pure']
      | some ctx =>
        simp only [simulateQ_bind, simulateQ_sigImpl_liftM, simulateQ_pure,
          WriterT.fst_map_run_bind', WriterT.fst_map_run_pure', fst_run_liftM]
    | bundle b =>
      simp only [recipientForger, recipient, simulateQ_pure, WriterT.fst_map_run_pure']
    | confirmation c =>
      simp only [recipientForger, recipient, simulateQ_pure, WriterT.fst_map_run_pure']

private lemma fst_run_recipientForger_output [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K) (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((recipientForger P hasOPK).output st)).run =
    (recipient P hasOPK).output st := by
  cases st <;>
    simp only [recipientForger, recipient, simulateQ_pure, WriterT.fst_map_run_pure']

def initiatorIdealForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party (OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)))
      (InitiatorParameters F G SPK Msg) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← liftM (initiateIdeal P p b) with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← liftM ($ᵗ K : ProbComp K); pure (some (some SK))
    | _ => pure none

private lemma fst_run_initiatorIdealForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((initiatorIdealForger P).init p)).run =
    (initiatorIdeal P).init p := by
  simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']

private lemma fst_run_initiatorIdealForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((initiatorIdealForger P).step st w)).run =
    (initiatorIdeal P).step st w := by
  cases st with
  | inl p =>
    cases w with
    | bundle b =>
      simp only [initiatorIdealForger, initiatorIdeal, simulateQ_bind, simulateQ_sigImpl_liftM,
        WriterT.fst_map_run_bind', fst_run_liftM]
      refine bind_congr fun r => ?_
      cases r with
      | none => simp only [simulateQ_pure, WriterT.fst_map_run_pure']
      | some x => simp only [simulateQ_pure, WriterT.fst_map_run_pure']
    | initial im =>
      simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
    | confirmation c =>
      simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
  | inr rest =>
    cases rest with
    | inl ctx =>
      cases w with
      | confirmation conf =>
        simp only [initiatorIdealForger, initiatorIdeal]
        cases confirm P ctx conf with
        | none => simp only [simulateQ_pure, WriterT.fst_map_run_pure']
        | some SK => simp only [simulateQ_pure, WriterT.fst_map_run_pure']
      | bundle b =>
        simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
      | initial im =>
        simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
    | inr SK =>
      cases w <;>
        simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']

private lemma fst_run_initiatorIdealForger_output [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((initiatorIdealForger P).output st)).run =
    (initiatorIdeal P).output st := by
  rcases st with p | ctx | SK
  · simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
  · simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']
  · simp only [initiatorIdealForger, initiatorIdeal, run_sim_liftM_bind, map_bind]
    refine bind_congr fun sk => ?_
    simp only [simulateQ_pure, WriterT.fst_map_run_pure']

def schemeForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme (OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S))) K
      (InitiatorParameters F G SPK Msg) (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := liftM (setup P msg)
  U := initiatorIdealForger P
  T := recipientForger P hasOPK

def _root_.AKE.UAKE.Adversary.toForger
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (schemeForger P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

def envFI [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (e : UAKE.Env (schemeForger P msg hasOPK)) : UAKE.Env (uakeInitiatorIdeal P msg hasOPK) :=
  { clock := e.clock
    challenge := e.challenge
    challengeDone := e.challengeDone
    tSessions := e.tSessions.map fun t => ⟨t.state, t.transcript, t.key, t.revealed⟩ }

def crFI [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (cr : UAKE.ChallengeResult (schemeForger P msg hasOPK)) :
    UAKE.ChallengeResult (uakeInitiatorIdeal P msg hasOPK) :=
  { K0 := cr.K0, challengeTr := cr.challengeTr, oracleTrs := cr.oracleTrs }

private lemma schemeForger_T [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeForger P msg hasOPK).T = recipientForger P hasOPK := rfl

private lemma uakeInitiatorIdeal_T [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).T = recipient P hasOPK := rfl

private lemma schemeForger_U [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeForger P msg hasOPK).U = initiatorIdealForger P := rfl

private lemma uakeInitiatorIdeal_U [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).U = initiatorIdeal P := rfl

private lemma schemeForger_rounds [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeForger P msg hasOPK).rounds = 3 := rfl

private lemma uakeInitiatorIdeal_rounds [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).rounds = 3 := rfl

private lemma crFI_authBreak [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (r : UAKE.ChallengeResult (schemeForger P msg hasOPK)) :
    ((crFI P msg hasOPK r).K0.isSome && !UAKE.isPingPong (crFI P msg hasOPK r))
      = (r.K0.isSome && !UAKE.isPingPong r) := by
  simp only [crFI, UAKE.isPingPong, schemeForger_rounds, uakeInitiatorIdeal_rounds]

def envSig [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (s2 : SPK × SSK) (e : UAKE.Env (schemeForger P msg hasOPK)) :
    UAKE.Env (schemeForger P msg hasOPK) :=
  { clock := e.clock
    challenge := e.challenge
    challengeDone := e.challengeDone
    tSessions := e.tSessions.map fun t =>
      ⟨Sum.elim (fun p => Sum.inl { p with sigkB := s2 }) Sum.inr t.state,
        t.transcript, t.key, t.revealed⟩ }

private lemma fst_run_oracleImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK)) (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.opImpl (schemeForger P msg hasOPK) tk op).run s)).run) =
    (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run (envFI P msg hasOPK s) := by
  cases op with
  | revealT sid =>
    cases hs : s.tSessions[sid]? <;>
      simp [UAKE.opImpl, envFI, hs, List.getElem?_map, List.map_set, simulateQ_pure,
        ]
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, schemeForger_T, uakeInitiatorIdeal_T,
      simulateQ_bind, simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
      fst_run_recipientForger_init _ _ _ _ _ hsig, map_bind, map_pure]
    refine bind_congr fun r => ?_
    simp only [
      Prod.map_apply, id_eq, envFI]
    cases r <;>
      exact congrArg pure (Prod.ext (Prod.ext (List.length_map _).symm rfl)
        (by simp [List.map_append]))
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,

      pure_bind, schemeForger_T, uakeInitiatorIdeal_T,
      envFI, List.getElem?_map]
    cases hs : s.tSessions[sid]? with
    | none => simp [envFI, Prod.map]
    | some t =>
      cases hk : t.key with
      | some k => simp [hk, envFI, Prod.map]
      | none =>
        simp only [hk, Option.map_some, StateT.run_bind, StateT.run_monadLift,
          monadLift_self,
          bind_assoc, pure_bind, simulateQ_bind,
          WriterT.fst_map_run_bind',
          fst_run_recipientForger_step _ _ _ _ pk sk, map_bind]
        refine bind_congr fun sr => ?_
        cases sr with
        | reject =>
          simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
            Prod.map_apply, id_eq, envFI]
        | acceptAndSend st' w' done =>
          cases done with
          | false =>
            simp only [reduceCtorEq, reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              pure_bind, simulateQ_pure,
              WriterT.fst_map_run_pure', map_pure]
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
          | true =>
            simp only [reduceIte, StateT.run_bind, StateT.run_monadLift,
              StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
              simulateQ_bind, simulateQ_pure, WriterT.fst_map_run_bind',
              WriterT.fst_map_run_pure', fst_run_recipientForger_output _ _ _ pk sk, map_bind,
              map_pure]
            refine bind_congr fun key => ?_
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
        | complete st' =>
          simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            monadLift_self, bind_assoc, pure_bind, simulateQ_bind,
            simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
            fst_run_recipientForger_output _ _ _ pk sk, map_bind, map_pure]
          refine bind_congr fun key => ?_
          exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
  | stepChallenge w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,

      pure_bind, schemeForger_U, uakeInitiatorIdeal_U, envFI]
    split
    · simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
        Prod.map_apply, id_eq, envFI]
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, simulateQ_bind,
        WriterT.fst_map_run_bind',
        fst_run_initiatorIdealForger_step _ _ _ pk sk, map_bind]
      refine bind_congr fun sr => ?_
      cases sr <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          simulateQ_pure,
          WriterT.fst_map_run_pure', map_pure, Prod.map_apply, id_eq, envFI] <;> rfl

private lemma fst_run_oracleImpl_sigkB [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (s2 : SPK × SSK) (pk : SPK) (sk : SSK)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK)) (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envSig P msg hasOPK s2) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.opImpl (schemeForger P msg hasOPK) tk op).run s)).run) =
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.opImpl (schemeForger P msg hasOPK) ⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩ op).run
          (envSig P msg hasOPK s2 s))).run := by
  cases op with
  | revealT sid =>
    cases hs : s.tSessions[sid]? <;>
      simp [UAKE.opImpl, envSig, hs, List.getElem?_map, List.map_set, simulateQ_pure]
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, schemeForger_T, recipientForger,
      simulateQ_bind, simulateQ_pure, simulateQ_sigImpl_liftM, simulateQ_publishForger,
      WriterT.fst_map_run_bind', WriterT.fst_map_run_pure', fst_run_liftM, fst_run_signingOracle,
      map_bind, map_pure]
    refine bind_congr fun opkB => bind_congr fun pqpkB =>
      bind_congr fun pqpkSigB => ?_
    exact congrArg pure (Prod.ext (Prod.ext (by simp [envSig, List.length_map]) rfl)
      (by simp [envSig, List.map_append]))
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,

      pure_bind, schemeForger_T, envSig, List.getElem?_map]
    cases hs : s.tSessions[sid]? with
    | none =>
      simp only [Option.map_none, StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure',
        map_pure, Prod.map_apply, id_eq, envSig]
      rfl
    | some t =>
      cases hk : t.key with
      | some k =>
        simp only [hk, Option.map_some, StateT.run_pure, simulateQ_pure,
          WriterT.fst_map_run_pure', map_pure, Prod.map_apply, id_eq, envSig]
        rfl
      | none =>
        simp only [hk, Option.map_some, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind, simulateQ_bind, WriterT.fst_map_run_bind',
          fst_run_recipientForger_step _ _ _ _ pk sk, map_bind]
        cases hst : t.state with
        | inr kk => cases w <;> rfl
        | inl p =>
          cases w with
          | bundle b => rfl
          | confirmation c => rfl
          | initial im =>
            have halign := recipient_step_sigkB_irrel P hasOPK (Sum.inl p) s2 (Message.initial im)
            refine Eq.trans ?_ (congrArg (· >>= _) halign.symm)
            beta_reduce
            refine bind_congr_of_forall_mem_support _ fun a ha => ?_
            simp only [recipient] at ha
            obtain ⟨r, hr, ha⟩ := (mem_support_bind_iff _ _ _).1 ha
            cases r with
            | none =>
              obtain rfl := (mem_support_pure_iff' _ _).1 ha
              rfl
            | some ctx =>
              obtain ⟨conf, hconf, ha⟩ := (mem_support_bind_iff _ _ _).1 ha
              obtain rfl := (mem_support_pure_iff' _ _).1 ha
              simp only [reduceIte, StateT.run_bind, StateT.run_monadLift,
                StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc,
                pure_bind, simulateQ_bind, simulateQ_pure,
                WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
                fst_run_recipientForger_output _ _ _ pk sk, map_bind, map_pure]
              refine bind_congr fun key => ?_
              refine congrArg pure (Prod.ext rfl ?_)
              simp only [Prod.map_snd, envSig, List.map_set, Sum.elim_inr]
              rfl
  | stepChallenge w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,

      pure_bind, schemeForger_U, envSig]
    split
    · simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
        Prod.map_apply, id_eq, envSig]
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, simulateQ_bind,
        WriterT.fst_map_run_bind',
        fst_run_initiatorIdealForger_step _ _ _ pk sk, map_bind]
      refine bind_congr fun sr => ?_
      cases sr <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          simulateQ_pure,
          WriterT.fst_map_run_pure', map_pure, Prod.map_apply, id_eq, envSig]

private lemma snd_run_oracleImpl_revealT [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK)
    (sid : ℕ) (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.snd <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((UAKE.opImpl (schemeForger P msg hasOPK) tk (.revealT sid)).run s)).run
      = pure (∅ : QueryLog ((G ⊕ PQPK) →ₒ S)) := by
  simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind]
  cases s.tSessions[sid]? <;>
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure,
      WriterT.run_pure', map_pure]

private lemma fst_run_withUnif_query_sigkB [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (s2 : SPK × SSK) (pk : SPK) (sk : SSK)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envSig P msg hasOPK s2) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.oracleImpl (schemeForger P msg hasOPK) tk q).run s)).run) =
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.oracleImpl (schemeForger P msg hasOPK) ⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩ q).run
          (envSig P msg hasOPK s2 s))).run := by
  cases q with
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr]
    exact fst_run_oracleImpl_sigkB P msg hasOPK tk s2 pk sk op s
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, simulateQ_map, simulateQ_sigImpl_liftM,
      Functor.map_map, envSig]

private lemma fst_run_withUnif_oracleImpl_sigkB [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (s2 : SPK × SSK) (pk : SPK) (sk : SSK)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envSig P msg hasOPK s2) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK) tk) oa).run s)).run) =
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK)
          ⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩) oa).run (envSig P msg hasOPK s2 s))).run := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, WriterT.fst_map_run_pure', map_pure,
      Prod.map_apply, id_eq]
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, WriterT.fst_map_run_bind', map_bind, ih]
    rw [← fst_run_withUnif_query_sigkB P msg hasOPK tk s2 pk sk q s]
    simp only [bind_map_left, Prod.map_fst, Prod.map_snd, id_eq]

private lemma fst_run_withUnif_query [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.oracleImpl (schemeForger P msg hasOPK) tk q).run s)).run) =
    (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run
      (envFI P msg hasOPK s) := by
  cases q with
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr]
    exact fst_run_oracleImpl P msg hasOPK tk pk sk hsig op s
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, simulateQ_map, simulateQ_sigImpl_liftM,
      Functor.map_map, envFI]

private lemma fst_run_withUnif_oracleImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK) tk) oa).run s)).run) =
    (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run
      (envFI P msg hasOPK s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, WriterT.fst_map_run_pure', map_pure,
      Prod.map_apply, id_eq]
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, WriterT.fst_map_run_bind', map_bind, ih]
    rw [← fst_run_withUnif_query P msg hasOPK tk pk sk hsig q s]
    simp only [bind_map_left, Prod.map_fst, Prod.map_snd, id_eq]

private lemma fst_run_withUnif_init [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (c : ℕ) (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK) tk) oa).run
          ⟨c, ⟨st, tr⟩, false, []⟩)).run) =
    (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run
      ⟨c, ⟨st, tr⟩, false, []⟩ := by
  have h := fst_run_withUnif_oracleImpl P msg hasOPK tk pk sk hsig oa
    (⟨c, ⟨st, tr⟩, false, []⟩ : UAKE.Env (schemeForger P msg hasOPK))
  simpa [envFI] using h

private lemma fst_run_challengeSession [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    (fun r => (crFI P msg hasOPK r.1,
        (r.2.1, envFI P msg hasOPK r.2.2.1, r.2.2.2))) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run) =
    UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK) A.toIdeal uk tk := by
  unfold UAKE.challengeSession
  simp only [schemeForger_U, uakeInitiatorIdeal_U, AKE.UAKE.Adversary.toForger,
    AKE.UAKE.Adversary.toIdeal, simulateQ_bind, simulateQ_pure,
    WriterT.fst_map_run_bind', WriterT.fst_map_run_pure', map_bind, map_pure,
    fst_run_initiatorIdealForger_init _ _ pk sk]
  refine bind_congr fun u0 => ?_
  have h := fst_run_withUnif_init P msg hasOPK tk pk sk hsig (A.challenge uk u0.opening)
    (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) u0.opening 0).2 u0.state
    (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) u0.opening 0).1
  refine Eq.trans ?_ (congrArg (· >>= _) h)
  beta_reduce
  conv_rhs => rw [bind_map_left]
  refine bind_congr fun a => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq, envFI, List.map_map, Function.comp_def, crFI,
    fst_run_initiatorIdealForger_output _ _ pk sk]

private lemma fst_run_withUnif_init_sigkB [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S) (s2 : SPK × SSK) (pk : SPK) (sk : SSK)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (c : ℕ) (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    Prod.map id (envSig P msg hasOPK s2) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK) tk) oa).run
          ⟨c, ⟨st, tr⟩, false, []⟩)).run) =
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (UAKE.oracleImpl (schemeForger P msg hasOPK)
          ⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩) oa).run ⟨c, ⟨st, tr⟩, false, []⟩)).run := by
  have h := fst_run_withUnif_oracleImpl_sigkB P msg hasOPK tk s2 pk sk oa
    (⟨c, ⟨st, tr⟩, false, []⟩ : UAKE.Env (schemeForger P msg hasOPK))
  simpa [envSig] using h

private lemma fst_run_challengeSession_sigkB [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (s2 : SPK × SSK) (pk : SPK) (sk : SSK)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    (fun r => (r.1, (r.2.1, envSig P msg hasOPK s2 r.2.2.1,
        (⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩ : RecipientIdentity F G SPK SSK S)))) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run) =
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
          ⟨tk.ikB, s2, tk.spkB, tk.spkSigB⟩)).run := by
  unfold UAKE.challengeSession
  simp only [schemeForger_U, AKE.UAKE.Adversary.toForger, simulateQ_bind, simulateQ_pure,
    WriterT.fst_map_run_bind', WriterT.fst_map_run_pure', map_bind, map_pure]
  refine bind_congr fun u0 => ?_
  have h := fst_run_withUnif_init_sigkB P msg hasOPK tk s2 pk sk (A.challenge uk u0.opening)
    (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) u0.opening 0).2 u0.state
    (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) u0.opening 0).1
  refine Eq.trans ?_ (congrArg (· >>= _) h)
  beta_reduce
  conv_rhs => rw [bind_map_left]
  refine bind_congr fun a => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq, envSig, List.map_map, Function.comp_def,
    fst_run_initiatorIdealForger_output _ _ pk sk]

def extractForgery [Inhabited G] [Inhabited S] (guess : Bool)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) : (G ⊕ PQPK) × S :=
  match tr.entries.findSome? (fun e => match e.1 with
    | .bundle b =>
        some (if guess then (EncodeKEM b.pqpkB.1, b.pqpkSigB) else (EncodeEC b.spkB.1, b.spkSigB))
    | _ => none) with
  | some fs => fs
  | none => (EncodeEC default, default)

def sigForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : P.sig.unforgeableAdv where
  main := fun pk => do
    let ikA ← liftM (dhKeygen P.gen)
    let ikB ← liftM (dhKeygen P.gen)
    let spkB ← liftM (dhKeygen P.gen)
    let guess ← liftM ($ᵗ Bool)
    let spkSigB ← liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
      (Sum.inr (EncodeEC spkB.1)))
    let uk : InitiatorParameters F G SPK Msg := ⟨ikA, ikB.1, pk, msg⟩
    let tk : RecipientIdentity F G SPK SSK S := ⟨ikB, (pk, default), spkB, spkSigB⟩
    let (_, _, env, _) ← UAKE.challengeSession (proto := schemeForger P msg hasOPK)
      A.toForger uk tk
    return extractForgery guess env.challenge.transcript

end SignatureReduction

section AeadReduction

def setCtxKb {G PQPK Msg K : Type} (k : K) (ctx : SessionContext G PQPK Msg K) :
    SessionContext G PQPK Msg K :=
  { ctx with kb := k }

def confirmOfDec {G PQPK Msg K : Type} [DecidableEq Msg]
    (ctx : SessionContext G PQPK Msg K) (m : Option Msg) : Option K :=
  if m = some ctx.msg then some ctx.sk else none

def initiatorIdealAeadForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party (OracleComp (unifSpec +
        ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg))))
      (InitiatorParameters F G SPK Msg) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← liftM (initiateIdeal P p b) with
        | some (im, ctx) =>
            pure (.acceptAndSend (.inr (.inl (setCtxKb default ctx))) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf => do
        let m ← liftM (OracleSpec.query (spec := unifSpec +
            ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg)))
          (Sum.inr (Sum.inr (ctx.ad, conf))))
        match confirmOfDec ctx m with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← liftM ($ᵗ K : ProbComp K); pure (some (some SK))
    | _ => pure none

def recipientAeadForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party (OracleComp (unifSpec +
        ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg))))
      (RecipientIdentity F G SPK SSK S) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := (recipient P hasOPK).State
  init := fun idn => liftM ((recipient P hasOPK).init idn)
  step := fun st w => liftM ((recipient P hasOPK).step st w)
  output := fun st => liftM ((recipient P hasOPK).output st)

def schemeAeadForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme (OracleComp (unifSpec +
        ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg)))) K
      (InitiatorParameters F G SPK Msg) (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := liftM (setup P msg)
  U := initiatorIdealAeadForger P
  T := recipientAeadForger P hasOPK

def _root_.AKE.UAKE.Adversary.toAeadForger
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (schemeAeadForger P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

def aeadForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    AEAD.INT_CTXT_D_Adversary P.aead where
  run := do
    let uktk ← liftM (setup P msg)
    let _ ← UAKE.challengeSession (proto := schemeAeadForger P msg hasOPK)
      A.toAeadForger uktk.1 uktk.2
    pure ()

def initiatorIdealFixed [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiateIdeal P p b with
        | some (im, ctx) =>
            pure (.acceptAndSend (.inr (.inl (setCtxKb k ctx))) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirmOfDec ctx (P.aead.decrypt k ctx.ad conf) with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← $ᵗ K; pure (some (some SK))
    | _ => pure none

def uakeInitiatorIdealFixed [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdealFixed P k
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toFixed
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (k : K) :
    UAKE.Adversary (uakeInitiatorIdealFixed P msg hasOPK k) where
  State := A.State
  challenge := A.challenge
  post := A.post

end AeadReduction

def stAF {G PQPK Msg K : Type} (k : K)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K) :
    InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K :=
  match st with
  | .inr (.inl ctx) => .inr (.inl (setCtxKb k ctx))
  | st => st

@[simp] lemma stAF_inl {G PQPK Msg K : Type} (k : K) (p : InitiatorParameters F G SPK Msg) :
    stAF (PQPK := PQPK) k (.inl p) = .inl p := rfl

@[simp] lemma stAF_inr_inl {G PQPK Msg K : Type} (k : K) (ctx : SessionContext G PQPK Msg K) :
    stAF (F := F) (SPK := SPK) k (.inr (.inl ctx)) = .inr (.inl (setCtxKb k ctx)) := rfl

@[simp] lemma stAF_inr_inr {G PQPK Msg K : Type} (k k' : K) :
    stAF (F := F) (G := G) (SPK := SPK) (PQPK := PQPK) (Msg := Msg) k (.inr (.inr k'))
      = .inr (.inr k') := rfl

def envAF [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (e : UAKE.Env (schemeAeadForger P msg hasOPK)) :
    UAKE.Env (uakeInitiatorIdealFixed P msg hasOPK k) :=
  { clock := e.clock
    challenge := ⟨stAF k e.challenge.state, e.challenge.transcript⟩
    challengeDone := e.challengeDone
    tSessions := e.tSessions.map fun t => ⟨t.state, t.transcript, t.key, t.revealed⟩ }

def crAF [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (cr : UAKE.ChallengeResult (schemeAeadForger P msg hasOPK)) :
    UAKE.ChallengeResult (uakeInitiatorIdealFixed P msg hasOPK k) :=
  { K0 := cr.K0, challengeTr := cr.challengeTr, oracleTrs := cr.oracleTrs }

@[simp] lemma setCtxKb_ad {G PQPK Msg K : Type} (k : K) (ctx : SessionContext G PQPK Msg K) :
    (setCtxKb k ctx).ad = ctx.ad := rfl

@[simp] lemma setCtxKb_msg {G PQPK Msg K : Type} (k : K) (ctx : SessionContext G PQPK Msg K) :
    (setCtxKb k ctx).msg = ctx.msg := rfl

@[simp] lemma setCtxKb_sk {G PQPK Msg K : Type} (k : K) (ctx : SessionContext G PQPK Msg K) :
    (setCtxKb k ctx).sk = ctx.sk := rfl

@[simp] lemma setCtxKb_setCtxKb {G PQPK Msg K : Type} (k k' : K)
    (ctx : SessionContext G PQPK Msg K) :
    setCtxKb k (setCtxKb k' ctx) = setCtxKb k ctx := rfl

def srAF {St W : Type} (f : St → St) :
    Party.StepResult St W → Party.StepResult St W
  | .acceptAndSend st w done => .acceptAndSend (f st) w done
  | .complete st => .complete (f st)
  | .reject => .reject

@[simp] lemma confirmOfDec_setCtxKb {G PQPK Msg K : Type} [DecidableEq Msg]
    (k : K) (ctx : SessionContext G PQPK Msg K) (m : Option Msg) :
    confirmOfDec (setCtxKb k ctx) m = confirmOfDec ctx m := rfl

private lemma simulateQ_decImpl_liftM {α : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C] [SampleableType K]
    (oa : ProbComp α) :
    simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      (liftM oa : OracleComp (unifSpec +
        ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg))) α) =
    (liftM oa : StateT (List ((G × G × PQPK) × C) × Bool) ProbComp α) := by
  rw [← OracleComp.liftComp_eq_liftM, AEAD.withUnif, QueryImpl.simulateQ_add_liftComp_left]
  induction oa using OracleComp.inductionOn with
  | pure x => simp [liftM_pure]
  | query_bind t oa ih => simp [ih, liftM_bind]

private lemma fst_run_dec_liftM {α : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C] [SampleableType K]
    (oa : ProbComp α) (s : List ((G × G × PQPK) × C) × Bool) :
    Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      (liftM oa : OracleComp (unifSpec +
        ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg))) α)).run s
      = oa := by
  rw [simulateQ_decImpl_liftM]
  erw [StateT.run_liftM]
  simp

private lemma run_dec_liftM_bind {α β : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C] [SampleableType K]
    (oa : ProbComp α)
    (f : α → OracleComp (unifSpec +
      ((((G × G × PQPK) × Msg) →ₒ C) + (((G × G × PQPK) × C) →ₒ Option Msg))) β)
    (s : List ((G × G × PQPK) × C) × Bool) :
    (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k)) (liftM oa >>= f)).run s =
    oa >>= fun a => (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k)) (f a)).run s := by
  rw [simulateQ_bind, simulateQ_decImpl_liftM, StateT.run_bind]
  erw [StateT.run_liftM]
  rw [bind_assoc]
  simp

private lemma fst_run_dec_initiatorAF_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) (s : List ((G × G × PQPK) × C) × Bool) :
    srAF (stAF k) <$> (Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((initiatorIdealAeadForger P).step st w)).run s) =
    (initiatorIdealFixed P k).step (stAF k st) w := by
  rcases st with p | ctx | k' <;> rcases w with b | im | c
  case inl.bundle =>
    simp only [initiatorIdealAeadForger, initiatorIdealFixed, stAF, run_dec_liftM_bind, map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ⟨im', ctx'⟩ <;>
      simp [srAF, stAF, simulateQ_pure, StateT.run_pure]
  case inr.inl.confirmation =>
    simp only [initiatorIdealAeadForger, initiatorIdealFixed, stAF, simulateQ_bind,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, map_bind]
    have hh : ((AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        (Sum.inr (Sum.inr (ctx.ad, c)))).run s
        = pure (P.aead.decrypt k ctx.ad c,
            (s.1, s.2 || ((P.aead.decrypt k ctx.ad c).isSome && decide ((ctx.ad, c) ∉ s.1)))) :=
      rfl
    rw [hh]
    erw [pure_bind]
    rcases hcd : confirmOfDec ctx (P.aead.decrypt k ctx.ad c) with _ | SK <;>
      simp [hcd, srAF, simulateQ_pure, StateT.run_pure]
  all_goals
    simp [initiatorIdealAeadForger, initiatorIdealFixed, stAF, srAF, simulateQ_pure,
      StateT.run_pure]

private lemma schemeAeadForger_T [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeAeadForger P msg hasOPK).T = recipientAeadForger P hasOPK := rfl

private lemma schemeAeadForger_U [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeAeadForger P msg hasOPK).U = initiatorIdealAeadForger P := rfl

private lemma uakeInitiatorIdealFixed_T [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) :
    (uakeInitiatorIdealFixed P msg hasOPK k).T = recipient P hasOPK := rfl

private lemma uakeInitiatorIdealFixed_U [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) :
    (uakeInitiatorIdealFixed P msg hasOPK k).U = initiatorIdealFixed P k := rfl

private lemma fst_run_dec_initiatorAF_output [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (s : List ((G × G × PQPK) × C) × Bool) :
    Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((initiatorIdealAeadForger P).output st)).run s =
    (initiatorIdealFixed P k).output (stAF k st) := by
  rcases st with p | ctx | k'
  · simp [initiatorIdealAeadForger, initiatorIdealFixed, stAF, simulateQ_pure, StateT.run_pure]
  · simp [initiatorIdealAeadForger, initiatorIdealFixed, stAF, simulateQ_pure, StateT.run_pure]
  · simp only [initiatorIdealAeadForger, initiatorIdealFixed, stAF, run_dec_liftM_bind, map_bind]
    refine bind_congr fun SK => ?_
    simp [simulateQ_pure, StateT.run_pure]

private lemma fst_run_dec_opImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (schemeAeadForger P msg hasOPK))
    (s : List ((G × G × PQPK) × C) × Bool) :
    Prod.map id (envAF P msg hasOPK k) <$>
      (Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        ((UAKE.opImpl (schemeAeadForger P msg hasOPK) tk op).run env)).run s) =
    (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk op).run
      (envAF P msg hasOPK k env) := by
  cases op with
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, schemeAeadForger_T, uakeInitiatorIdealFixed_T,
      recipientAeadForger, run_dec_liftM_bind, map_bind, map_pure]
    refine bind_congr fun r => ?_
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq, envAF]
    exact congrArg pure (Prod.ext (Prod.ext (List.length_map _).symm rfl)
      (by simp [List.map_append]))
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,
      pure_bind, schemeAeadForger_T, uakeInitiatorIdealFixed_T,
      envAF, List.getElem?_map]
    cases hs : env.tSessions[sid]? with
    | none => simp [envAF, Prod.map]
    | some t =>
      cases hk : t.key with
      | some kk => simp [hk, envAF, Prod.map]
      | none =>
        simp only [hk, Option.map_some, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind,
          recipientAeadForger, run_dec_liftM_bind, map_bind]
        refine bind_congr fun sr => ?_
        cases sr with
        | reject =>
          simp only [StateT.run_pure, simulateQ_pure, map_pure,
            Prod.map_apply, id_eq, envAF]
        | acceptAndSend st' w' done =>
          cases done with
          | false =>
            simp only [reduceCtorEq, reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, simulateQ_pure, map_pure]
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envAF]))
          | true =>
            simp only [reduceIte, StateT.run_bind, StateT.run_monadLift,
              StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
              recipientAeadForger, run_dec_liftM_bind, map_bind, map_pure]
            refine bind_congr fun key => ?_
            simp only [simulateQ_pure, StateT.run_pure, map_pure]
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envAF]))
        | complete st' =>
          simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            monadLift_self, bind_assoc, pure_bind,
            recipientAeadForger, run_dec_liftM_bind, map_bind, map_pure]
          refine bind_congr fun key => ?_
          simp only [simulateQ_pure, StateT.run_pure, map_pure]
          exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envAF]))
  | revealT sid =>
    cases hs : env.tSessions[sid]? <;>
      simp [UAKE.opImpl, envAF, hs, List.getElem?_map, List.map_set, simulateQ_pure]
  | stepChallenge w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get,
      pure_bind, schemeAeadForger_U, uakeInitiatorIdealFixed_U, envAF]
    split
    · simp only [StateT.run_pure, simulateQ_pure, map_pure, Prod.map_apply, id_eq, envAF]
      rfl
    · simp only [StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, map_bind]
      rcases henv : env.challenge.state with p | ctx | k' <;> rcases w with b | im | c <;>
        simp only [henv, initiatorIdealAeadForger, initiatorIdealFixed, stAF_inl,
          stAF_inr_inl, stAF_inr_inr]
      case inl.bundle =>
        rw [run_dec_liftM_bind]
        simp only [bind_assoc]
        show initiateIdeal P p b >>= _ = initiateIdeal P p b >>= _
        refine bind_congr fun r => ?_
        rcases r with _ | ⟨im', ctx'⟩ <;>
          (simp [simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_set,
            pure_bind, envAF, setCtxKb_setCtxKb, henv]; try rfl)
      case inr.inl.confirmation =>
        rw [simulateQ_bind, simulateQ_query]
        simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]
        have hh : ((AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
            (Sum.inr (Sum.inr (ctx.ad, c)))).run s
            = pure (P.aead.decrypt k ctx.ad c,
                (s.1, s.2 || ((P.aead.decrypt k ctx.ad c).isSome
                  && decide ((ctx.ad, c) ∉ s.1)))) := rfl
        rw [hh]
        erw [pure_bind]
        simp only [setCtxKb_ad, confirmOfDec_setCtxKb]
        rcases hcd : confirmOfDec ctx (P.aead.decrypt k ctx.ad c) with _ | SK <;>
          (simp [hcd, simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_set,
            pure_bind, envAF, henv]; try rfl)
      all_goals
        (simp [simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_set,
          pure_bind, envAF, henv]; try rfl)

private lemma fst_run_dec_query [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (schemeAeadForger P msg hasOPK))
    (s : List ((G × G × PQPK) × C) × Bool) :
    Prod.map id (envAF P msg hasOPK k) <$>
      (Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        ((UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk q).run env)).run s) =
    (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk q).run
      (envAF P msg hasOPK k env) := by
  cases q with
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr]
    exact fst_run_dec_opImpl P msg hasOPK k tk op env s
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, simulateQ_map, simulateQ_decImpl_liftM,
      Functor.map_map, envAF]

private lemma fst_run_dec_oracleImpl_run [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (env : UAKE.Env (schemeAeadForger P msg hasOPK))
    (s : List ((G × G × PQPK) × C) × Bool) :
    Prod.map id (envAF P msg hasOPK k) <$>
      (Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        ((simulateQ (UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk) oa).run env)).run s) =
    (simulateQ (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk) oa).run
      (envAF P msg hasOPK k env) := by
  induction oa using OracleComp.inductionOn generalizing env s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind, ih]
    rw [← fst_run_dec_query P msg hasOPK k tk q env s]
    simp only [bind_map_left, Prod.map_fst, Prod.map_snd, id_eq]

private lemma fst_run_dec_challengeSession [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    (fun r => (crAF P msg hasOPK k r.1,
        (r.2.1, envAF P msg hasOPK k r.2.2.1, r.2.2.2))) <$>
      (Prod.fst <$> (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        (UAKE.challengeSession (proto := schemeAeadForger P msg hasOPK)
          A.toAeadForger uk tk)).run ([], false)) =
    UAKE.challengeSession (proto := uakeInitiatorIdealFixed P msg hasOPK k)
      (A.toFixed k) uk tk := by
  unfold UAKE.challengeSession
  simp only [schemeAeadForger_U, uakeInitiatorIdealFixed_U, AKE.UAKE.Adversary.toAeadForger,
    AKE.UAKE.Adversary.toFixed, initiatorIdealAeadForger, initiatorIdealFixed,
    simulateQ_bind, simulateQ_pure, StateT.run_pure, StateT.run_bind, pure_bind, map_bind,
    Party.InitResult.opening, Party.InitResult.state]
  have h := fst_run_dec_oracleImpl_run P msg hasOPK k tk (A.challenge uk none)
    ⟨(recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).2,
      ⟨Sum.inl uk, (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).1⟩,
      false, []⟩ ([], false)
  refine Eq.trans ?_ (congrArg (· >>= _) h)
  beta_reduce
  conv_rhs => rw [bind_map_left]
  conv_rhs => rw [bind_map_left]
  show (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((simulateQ (UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk)
        (A.challenge uk none)).run
        ⟨(recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).2,
          ⟨Sum.inl uk, (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).1⟩,
          false, []⟩)).run ([], false) >>= _
    = (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((simulateQ (UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk)
        (A.challenge uk none)).run
        ⟨(recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).2,
          ⟨Sum.inl uk, (recordOpt (⟨[]⟩ : Transcript (Message G PQPK CT S C IdC IdK)) none 0).1⟩,
          false, []⟩)).run ([], false) >>= _
  refine bind_congr fun a => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rcases hst : a.1.2.challenge.state with p | ctx | SK
  · simp [envAF, hst, simulateQ_pure, StateT.run_pure, crAF, List.map_map,
      Function.comp_def]
  · simp [envAF, hst, simulateQ_pure, StateT.run_pure, crAF, List.map_map,
      Function.comp_def]
  · simp only [envAF, hst, stAF_inr_inr, run_dec_liftM_bind, map_bind, bind_assoc]
    show ($ᵗ K : ProbComp K) >>= _ = ($ᵗ K : ProbComp K) >>= _
    refine bind_congr fun SK' => ?_
    simp [simulateQ_pure, StateT.run_pure, crAF, List.map_map, Function.comp_def, hst]

def aliceDone {F G SPK PQPK Msg K : Type}
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K) : Prop :=
  ∃ SK, st = Sum.inr (Sum.inr SK)

@[simp] lemma aliceDone_inl {F G SPK PQPK Msg K : Type}
    (p : InitiatorParameters F G SPK Msg) :
    ¬ aliceDone (K := K) (PQPK := PQPK) (Sum.inl p) := by
  rintro ⟨SK, h⟩; exact absurd h (by simp)

@[simp] lemma aliceDone_inr_inl {F G SPK PQPK Msg K : Type}
    (ctx : SessionContext G PQPK Msg K) :
    ¬ aliceDone (F := F) (SPK := SPK) (Sum.inr (Sum.inl ctx)) := by
  rintro ⟨SK, h⟩; exact absurd h (by simp)

@[simp] lemma aliceDone_inr_inr {F G SPK PQPK Msg K : Type} (SK : K) :
    aliceDone (F := F) (G := G) (SPK := SPK) (PQPK := PQPK) (Msg := Msg)
      (Sum.inr (Sum.inr SK)) := ⟨SK, rfl⟩

private lemma dec_opImpl_inv [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (schemeAeadForger P msg hasOPK))
    (s : List ((G × G × PQPK) × C) × Bool)
    (hs1 : s.1 = []) (hs2 : aliceDone env.challenge.state → s.2 = true)
    {p : ((UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range op ×
        UAKE.Env (schemeAeadForger P msg hasOPK)) × (List ((G × G × PQPK) × C) × Bool)}
    (hp : p ∈ support ((simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((UAKE.opImpl (schemeAeadForger P msg hasOPK) tk op).run env)).run s)) :
    p.2.1 = [] ∧ (aliceDone p.1.2.challenge.state → p.2.2 = true) := by
  cases op with
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
      schemeAeadForger_T, recipientAeadForger, run_dec_liftM_bind] at hp
    obtain ⟨r, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hs1, fun hd => hs2 hd⟩
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs1, fun hd => hs2 hd⟩
    · rcases htk : t.key with _ | kk
      · simp only [hsx, htk, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
          StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
          schemeAeadForger_T, recipientAeadForger, run_dec_liftM_bind] at hp
        obtain ⟨sr, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
        rcases sr with ⟨st', w', done⟩ | st' | _
        · rcases done with _ | _
          · simp only [Bool.false_eq_true, if_false, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, simulateQ_bind, simulateQ_pure] at hp
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨hs1, fun hd => hs2 hd⟩
          · simp only [if_true, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
              StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
              run_dec_liftM_bind] at hp
            obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
            simp only [simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨hs1, fun hd => hs2 hd⟩
        · simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            monadLift_self, bind_assoc, pure_bind, run_dec_liftM_bind] at hp
          obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hp
          subst hp
          exact ⟨hs1, fun hd => hs2 hd⟩
        · simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hp
          subst hp
          exact ⟨hs1, fun hd => hs2 hd⟩
      · simp only [hsx, htk, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨hs1, fun hd => hs2 hd⟩
  | revealT sid =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs1, fun hd => hs2 hd⟩
    · simp only [hsx, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs1, fun hd => hs2 hd⟩
  | stepChallenge w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hdone : env.challengeDone with _ | _
    · simp only [hdone, Bool.false_eq_true, if_false, StateT.run_bind, bind_assoc,
        schemeAeadForger_U] at hp
      rcases henv : env.challenge.state with q | ctx | k' <;>
        rcases w with b | im | c <;>
        simp only [henv, initiatorIdealAeadForger, StateT.run_monadLift, monadLift_self,
          StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hp
      case inl.bundle =>
        rw [run_dec_liftM_bind] at hp
        obtain ⟨r, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
        rcases r with _ | ⟨im', ctx'⟩ <;>
          simp only [simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_set,
            pure_bind, support_pure, Set.mem_singleton_iff] at hp <;>
          subst hp
        · exact ⟨hs1, fun hd => hs2 (henv ▸ hd)⟩
        · exact ⟨hs1, fun hd => absurd hd (by simp)⟩
      case inr.inl.confirmation =>
        rw [simulateQ_bind, simulateQ_query] at hp
        simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_bind] at hp
        have hh : ((AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
            (Sum.inr (Sum.inr (ctx.ad, c)))).run s
            = pure (P.aead.decrypt k ctx.ad c,
                (s.1, s.2 || ((P.aead.decrypt k ctx.ad c).isSome
                  && decide ((ctx.ad, c) ∉ s.1)))) := rfl
        rw [hh] at hp
        erw [pure_bind] at hp
        rcases hcd : confirmOfDec ctx (P.aead.decrypt k ctx.ad c) with _ | SK <;>
          simp only [hcd, simulateQ_pure, StateT.run_pure, StateT.run_bind, StateT.run_set,
            pure_bind, support_pure, Set.mem_singleton_iff] at hp <;>
          subst hp
        · refine ⟨hs1, fun hd => ?_⟩
          have := hs2 (henv ▸ hd)
          simp [this]
        · refine ⟨hs1, fun _ => ?_⟩
          have hdec : (P.aead.decrypt k ctx.ad c).isSome = true := by
            rcases hm : P.aead.decrypt k ctx.ad c with _ | m'
            · rw [hm] at hcd; simp [confirmOfDec] at hcd
            · rfl
          simp [hdec, hs1]
      all_goals
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hp
      all_goals subst hp
      all_goals exact ⟨hs1, fun hd => hs2 (henv ▸ hd)⟩
    · simp only [hdone, if_true, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs1, fun hd => hs2 hd⟩

private lemma dec_query_inv [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (schemeAeadForger P msg hasOPK))
    (s : List ((G × G × PQPK) × C) × Bool)
    (hs1 : s.1 = []) (hs2 : aliceDone env.challenge.state → s.2 = true)
    {p : (((unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range q) ×
        UAKE.Env (schemeAeadForger P msg hasOPK)) × (List ((G × G × PQPK) × C) × Bool)}
    (hp : p ∈ support ((simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk q).run env)).run s)) :
    p.2.1 = [] ∧ (aliceDone p.1.2.challenge.state → p.2.2 = true) := by
  cases q with
  | inl u =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply] at hp
    erw [StateT.run_monadLift] at hp
    rw [run_dec_liftM_bind] at hp
    obtain ⟨a, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hs1, fun hd => hs2 hd⟩
  | inr op => exact dec_opImpl_inv P msg hasOPK k tk op env s hs1 hs2 hp

private lemma dec_run_inv [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X) :
    ∀ (env : UAKE.Env (schemeAeadForger P msg hasOPK))
      (s : List ((G × G × PQPK) × C) × Bool)
      (z : (X × UAKE.Env (schemeAeadForger P msg hasOPK)) ×
        (List ((G × G × PQPK) × C) × Bool)),
      s.1 = [] → (aliceDone env.challenge.state → s.2 = true) →
      z ∈ support ((simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        ((simulateQ (UAKE.oracleImpl (schemeAeadForger P msg hasOPK) tk) oa).run env)).run s) →
      z.2.1 = [] ∧ (aliceDone z.1.2.challenge.state → z.2.2 = true) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro env s z hs1 hs2 hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs1, hs2⟩
  | query_bind q f ih =>
    intro env s z hs1 hs2 hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
    obtain ⟨h1, h2⟩ := dec_query_inv P msg hasOPK k tk q env s hs1 hs2 hp
    exact ih p.1.1 p.1.2 p.2 z h1 h2 hz

private lemma dec_output_inv [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (k : K)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (s1 : List ((G × G × PQPK) × C) × Bool)
    {q : Option (Option K) × (List ((G × G × PQPK) × C) × Bool)}
    (hq : q ∈ support ((simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      ((initiatorIdealAeadForger P).output st)).run s1)) :
    q.2 = s1 ∧ (q.1.join.isSome = true → aliceDone st) := by
  rcases st with p | ctx | SK
  · simp only [initiatorIdealAeadForger, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨rfl, by simp⟩
  · simp only [initiatorIdealAeadForger, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨rfl, by simp⟩
  · simp only [initiatorIdealAeadForger] at hq
    rw [run_dec_liftM_bind] at hq
    obtain ⟨SK', -, hq⟩ := (mem_support_bind_iff _ _ _).1 hq
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨rfl, fun _ => by simp⟩

private lemma dec_challengeSession_flag [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    ∀ z ∈ support ((simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
        (UAKE.challengeSession (proto := schemeAeadForger P msg hasOPK)
          A.toAeadForger uk tk)).run ([], false)),
      z.1.1.K0.isSome = true → z.2.2 = true := by
  intro z hz
  unfold UAKE.challengeSession at hz
  simp only [schemeAeadForger_U, AKE.UAKE.Adversary.toAeadForger,
    simulateQ_bind, simulateQ_pure, StateT.run_pure, StateT.run_bind, pure_bind,
    Party.InitResult.opening, Party.InitResult.state] at hz
  obtain ⟨u0, hu0, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  obtain ⟨p1, hp1, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  obtain ⟨p2, hp2, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  intro hK0
  have h1 := dec_run_inv P msg hasOPK k tk (A.challenge uk u0.1.opening)
    ⟨(recordOpt ⟨[]⟩ u0.1.opening 0).2, ⟨u0.1.state, (recordOpt ⟨[]⟩ u0.1.opening 0).1⟩,
      false, []⟩ u0.2 p1 ?_ ?_ hp1
  · have h2 := dec_output_inv P k p1.1.2.challenge.state p1.2 hp2
    have hAD := h2.2 hK0
    have := h1.2 hAD
    rw [h2.1]
    exact this
  · simp only [initiatorIdealAeadForger, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hu0
    subst hu0
    rfl
  · simp only [initiatorIdealAeadForger, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hu0
    subst hu0
    simp

def envIF [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (e : UAKE.Env (uakeInitiatorIdeal P msg hasOPK)) :
    UAKE.Env (uakeInitiatorIdealFixed P msg hasOPK k) :=
  { clock := e.clock
    challenge := ⟨e.challenge.state, e.challenge.transcript⟩
    challengeDone := e.challengeDone
    tSessions := e.tSessions.map fun t => ⟨t.state, t.transcript, t.key, t.revealed⟩ }

private lemma map_run_opImpl_IF [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hyps : ∀ w, op = UAKE.Op.stepChallenge w →
      (∀ p, env.challenge.state ≠ Sum.inl p) ∧
        (∀ ctx, env.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k)) :
    Prod.map id (envIF P msg hasOPK k) <$>
      (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run env =
    (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk op).run
      (envIF P msg hasOPK k env) := by
  cases op with
| openT =>
  simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
    StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
    uakeInitiatorIdeal_T, uakeInitiatorIdealFixed_T, map_bind]
  show (recipient P hasOPK).init tk >>= _ = (recipient P hasOPK).init tk >>= _
  refine bind_congr fun r => ?_
  simp only [map_pure, Prod.map_apply, id_eq, envIF]
  exact congrArg pure (Prod.ext (Prod.ext (List.length_map _).symm rfl)
    (by simp [List.map_append]))
| stepT sid w =>
  simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind,
    uakeInitiatorIdeal_T, uakeInitiatorIdealFixed_T, envIF, List.getElem?_map]
  cases hs : env.tSessions[sid]? with
  | none => simp [envIF, Prod.map]
  | some t =>
    cases hk : t.key with
    | some kk => simp [hk, envIF, Prod.map]
    | none =>
      simp only [hk, Option.map_some, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, map_bind]
      show (recipient P hasOPK).step t.state w >>= _
        = (recipient P hasOPK).step t.state w >>= _
      refine bind_congr fun sr => ?_
      cases sr with
      | reject => simp [envIF, Prod.map]
      | acceptAndSend st' w' done =>
        cases done with
        | false =>
          simp only [reduceCtorEq, reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, map_pure]
          exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envIF]))
        | true =>
          simp only [reduceIte, StateT.run_bind, StateT.run_monadLift,
            StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
            map_bind]
          show (recipient P hasOPK).output st' >>= _
            = (recipient P hasOPK).output st' >>= _
          refine bind_congr fun key => ?_
          simp only [map_pure]
          exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envIF]))
      | complete st' =>
        simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set,
          StateT.run_pure, monadLift_self, bind_assoc, pure_bind, map_bind]
        show (recipient P hasOPK).output st' >>= _
          = (recipient P hasOPK).output st' >>= _
        refine bind_congr fun key => ?_
        simp only [map_pure]
        exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envIF]))
| revealT sid =>
  cases hs : env.tSessions[sid]? <;>
    simp [UAKE.opImpl, envIF, hs, List.getElem?_map, List.map_set]
| stepChallenge w =>
  obtain ⟨hpre, hkb⟩ := hyps w rfl
  simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind,
    uakeInitiatorIdeal_U, uakeInitiatorIdealFixed_U, envIF]
  split
  · simp [envIF, Prod.map]; try rfl
  · rcases henv : env.challenge.state with p | ctx | k'
    · exact absurd henv (hpre p)
    · rcases w with b | im | c <;>
        simp only [henv, initiatorIdeal, initiatorIdealFixed, StateT.run_bind,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, monadLift_self,
          bind_assoc, pure_bind, map_bind]
      case confirmation =>
        rw [show confirm P ctx c
            = confirmOfDec ctx (P.aead.decrypt ctx.kb ctx.ad c) from rfl,
          hkb ctx henv]
        rcases hcd : confirmOfDec ctx (P.aead.decrypt k ctx.ad c) with _ | SK <;>
          (simp [hcd, envIF, henv]; try rfl)
      all_goals (simp [envIF, henv]; try rfl)
    · rcases w with b | im | c <;>
        simp only [henv, initiatorIdeal, initiatorIdealFixed, StateT.run_bind,
          StateT.run_monadLift, StateT.run_set, StateT.run_pure, monadLift_self,
          bind_assoc, pure_bind, map_bind] <;>
        (simp [envIF, henv]; try rfl)


private lemma map_run_query_IF [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hpre : ∀ p, env.challenge.state ≠ Sum.inl p)
    (hkb : ∀ ctx, env.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k) :
    Prod.map id (envIF P msg hasOPK k) <$>
      (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env =
    (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk q).run
      (envIF P msg hasOPK k env) := by
  cases q with
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, Functor.map_map, envIF]
  | inr op => exact map_run_opImpl_IF P msg hasOPK k tk op env (fun w _ => ⟨hpre, hkb⟩)

private lemma post_inv_opImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hpre : ∀ p', env.challenge.state ≠ Sum.inl p')
    (hkb : ∀ ctx, env.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k)
    {p : (UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range op ×
      UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hp : p ∈ support ((UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run env)) :
    (∀ p', p.2.challenge.state ≠ Sum.inl p') ∧
      (∀ ctx, p.2.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k) := by
  cases op with
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
    obtain ⟨r, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hpre, hkb⟩
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hpre, hkb⟩
    · rcases htk : t.key with _ | kk
      · simp only [hsx, htk, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
          StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
        obtain ⟨sr, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
        rcases sr with ⟨st', w', done⟩ | st' | _
        · rcases done with _ | _
          · simp only [Bool.false_eq_true, if_false, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨hpre, hkb⟩
          · simp only [if_true, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
              StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
            obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
            simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp
            exact ⟨hpre, hkb⟩
        · simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            monadLift_self, bind_assoc, pure_bind] at hp
          obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
          simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          exact ⟨hpre, hkb⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          exact ⟨hpre, hkb⟩
      · simp only [hsx, htk, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨hpre, hkb⟩
  | revealT sid =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hpre, hkb⟩
    · simp only [hsx, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hpre, hkb⟩
  | stepChallenge w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hdone : env.challengeDone with _ | _
    · simp only [hdone, Bool.false_eq_true, if_false, StateT.run_bind, bind_assoc,
        uakeInitiatorIdeal_U] at hp
      rcases henv : env.challenge.state with q | ctx | k'
      · exact absurd henv (hpre q)
      · rcases w with b | im | c <;>
          simp only [henv, initiatorIdeal, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hp
        case confirmation =>
          rcases hcd : confirm P ctx c with _ | SK <;>
            simp only [hcd, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff] at hp <;>
            subst hp
          · exact ⟨hpre, hkb⟩
          · exact ⟨by simp, fun ctx' h => by injection h with h2; injection h2⟩
        all_goals
          simp only [support_pure, Set.mem_singleton_iff] at hp
        all_goals subst hp
        all_goals exact ⟨hpre, hkb⟩
      · rcases w with b | im | c <;>
          simp only [henv, initiatorIdeal, StateT.run_monadLift, monadLift_self,
            StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
            support_pure, Set.mem_singleton_iff] at hp <;>
          subst hp <;>
          exact ⟨hpre, hkb⟩
    · simp only [hdone, if_true, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hpre, hkb⟩

private lemma post_inv_query [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hpre : ∀ p', env.challenge.state ≠ Sum.inl p')
    (hkb : ∀ ctx, env.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k)
    {p : ((unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range q) ×
      UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hp : p ∈ support ((UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env)) :
    (∀ p', p.2.challenge.state ≠ Sum.inl p') ∧
      (∀ ctx, p.2.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k) := by
  cases q with
  | inl u =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply] at hp
    erw [StateT.run_monadLift] at hp
    obtain ⟨a, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hpre, hkb⟩
  | inr op => exact post_inv_opImpl P msg hasOPK k tk op env hpre hkb hp

private lemma probOutput_ideal_fixed_post [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X) :
    ∀ (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
      (y : X × UAKE.Env (uakeInitiatorIdealFixed P msg hasOPK k)),
      (∀ p', env.challenge.state ≠ Sum.inl p') →
      (∀ ctx, env.challenge.state = Sum.inr (Sum.inl ctx) → ctx.kb = k) →
      Pr[= y | Prod.map id (envIF P msg hasOPK k) <$>
        (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run env]
      = Pr[= y | (simulateQ (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk)
          oa).run (envIF P msg hasOPK k env)] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro env y hpre hkb
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q f ih =>
    intro env y hpre hkb
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← map_run_query_IF P msg hasOPK k tk q env hpre hkb]
    conv_rhs => rw [map_eq_bind_pure_comp, bind_assoc]
    refine probOutput_bind_congr fun p hp => ?_
    obtain ⟨h1, h2⟩ := post_inv_query P msg hasOPK k tk q env hpre hkb hp
    simp only [Function.comp_def, pure_bind]
    exact ih p.1 p.2 y h1 h2

private lemma probOutput_bind_congr_left' {γ δ : Type} (m₁ m₂ : ProbComp γ)
    (g : γ → ProbComp δ) (w : δ) (h : ∀ x, Pr[= x | m₁] = Pr[= x | m₂]) :
    Pr[= w | m₁ >>= g] = Pr[= w | m₂ >>= g] := by
  simp only [probOutput_bind_eq_tsum]
  exact tsum_congr fun x => by rw [h x]

private lemma probOutput_map_bind' {γ ε δ : Type} (m : ProbComp γ) (f : γ → ε)
    (g : ε → ProbComp δ) (w : δ) :
    Pr[= w | (f <$> m) >>= g] = Pr[= w | m >>= fun x => g (f x)] := by
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

private lemma map_run_query_IF_pre [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (k : K) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hq : ∀ w, q ≠ Sum.inr (UAKE.Op.stepChallenge w)) :
    Prod.map id (envIF P msg hasOPK k) <$>
      (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env =
    (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk q).run
      (envIF P msg hasOPK k env) := by
  cases q with
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, Functor.map_map, envIF]
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr]
    exact map_run_opImpl_IF P msg hasOPK k tk op env
      (fun w hw => absurd (hw ▸ rfl) (hq w))

private lemma state_preserved_opImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hop : ∀ w, op ≠ UAKE.Op.stepChallenge w)
    {p : (UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range op ×
      UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hp : p ∈ support ((UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run env)) :
    p.2.challenge.state = env.challenge.state := by
  cases op with
  | openT =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
    obtain ⟨r, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl
  | stepT sid w =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rfl
    · rcases htk : t.key with _ | kk
      · simp only [hsx, htk, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
          StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
        obtain ⟨sr, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
        rcases sr with ⟨st', w', done⟩ | st' | _
        · rcases done with _ | _
          · simp only [Bool.false_eq_true, if_false, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hp
            subst hp
            rfl
          · simp only [if_true, StateT.run_bind, StateT.run_monadLift, StateT.run_set,
              StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
            obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
            simp only [support_pure, Set.mem_singleton_iff] at hp
            subst hp
            rfl
        · simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set,
            StateT.run_pure, monadLift_self, bind_assoc, pure_bind] at hp
          obtain ⟨key, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
          simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          rfl
        · simp only [support_pure, Set.mem_singleton_iff] at hp
          subst hp
          rfl
      · simp only [hsx, htk, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        rfl
  | revealT sid =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind] at hp
    rcases hsx : env.tSessions[sid]? with _ | t
    · simp only [hsx, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rfl
    · simp only [hsx, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rfl
  | stepChallenge w => exact absurd rfl (hop w)

private lemma state_preserved_query [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (hq : ∀ w, q ≠ Sum.inr (UAKE.Op.stepChallenge w))
    {p : ((unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Range q) ×
      UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hp : p ∈ support ((UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env)) :
    p.2.challenge.state = env.challenge.state := by
  cases q with
  | inl u =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply] at hp
    erw [StateT.run_monadLift] at hp
    obtain ⟨a, -, hp⟩ := (mem_support_bind_iff _ _ _).1 hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl
  | inr op =>
    exact state_preserved_opImpl P msg hasOPK tk op env
      (fun w hw => absurd (hw ▸ rfl) (hq w)) hp

private lemma probOutput_triple_resample {β : Type}
    [SampleableType K] [Fintype K] [Inhabited K]
    (g : K × K × K → ProbComp β) (y : β) :
    Pr[= y | ($ᵗ (K × K × K) : ProbComp _) >>= g]
      = Pr[= y | ($ᵗ K : ProbComp K) >>= fun k =>
          ($ᵗ (K × K × K) : ProbComp _) >>= fun t => g (t.1, t.2.1, k)] := by
  classical
  have h0 : (Fintype.card K : ℝ≥0∞) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have htop : (Fintype.card K : ℝ≥0∞) ≠ ⊤ := by simp
  have hcancel : (Fintype.card K : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel h0 htop
  simp only [probOutput_bind_eq_tsum, probOutput_uniformSample, tsum_fintype,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl htop),
    ENNReal.mul_inv (Or.inl h0) (Or.inl htop)]
  ring_nf
  rw [mul_right_comm,
    show ((Fintype.card K : ℝ≥0∞))⁻¹ ^ 4
      = (Fintype.card K : ℝ≥0∞)⁻¹ ^ 3 * (Fintype.card K : ℝ≥0∞)⁻¹ from pow_succ _ 3,
    mul_assoc ((Fintype.card K : ℝ≥0∞)⁻¹ ^ 3), hcancel, mul_one]

private lemma probOutput_uniform_bind_comm {α β : Type}
    [SampleableType K] [Fintype K] [Inhabited K]
    (m : ProbComp α) (g : K → α → ProbComp β) (y : β) :
    Pr[= y | ($ᵗ K : ProbComp K) >>= fun k => m >>= fun x => g k x]
      = Pr[= y | m >>= fun x => ($ᵗ K : ProbComp K) >>= fun k => g k x] := by
  rw [probOutput_bind_bind_swap]

private lemma initiateIdeal_resample [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p0 : InitiatorParameters F G SPK Msg) (b : PreKeyBundle G PQPK S IdC IdK)
    {β : Type}
    (h : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K) → ProbComp β)
    (y : β) :
    Pr[= y | initiateIdeal P p0 b >>= h]
      = Pr[= y | ($ᵗ K : ProbComp K) >>= fun k => initiateIdeal P p0 b >>= fun r =>
          h (Option.map (Prod.map id (setCtxKb k)) r)] := by
  unfold initiateIdeal
  by_cases h1 : b.ikB ≠ p0.ikB
  · simp only [if_pos h1, pure_bind, Option.map_none]
    rw [probOutput_bind_const, probFailure_uniformSample]
    simp
  · simp only [if_neg h1, bind_assoc, pure_bind]
    rw [probOutput_uniform_bind_comm]
    refine probOutput_bind_congr fun ok1 _ => ?_
    rw [probOutput_uniform_bind_comm]
    refine probOutput_bind_congr fun ok2 _ => ?_
    rcases h2 : (!(ok1 && ok2)) with _ | _
    · simp only [h2, Bool.false_eq_true, if_false, bind_assoc]
      rw [probOutput_uniform_bind_comm]
      refine probOutput_bind_congr fun ekA _ => ?_
      rw [probOutput_uniform_bind_comm]
      refine probOutput_bind_congr fun ctss _ => ?_
      rw [probOutput_triple_resample]
      refine probOutput_bind_congr fun k _ => probOutput_bind_congr fun t _ => ?_
      refine probOutput_bind_congr fun ctxt _ => ?_
      simp [setCtxKb, Prod.map]
    · simp only [h2, if_true, pure_bind, Option.map_none]
      rw [probOutput_bind_const, probFailure_uniformSample]
      simp

private lemma probOutput_ideal_fixed_pre [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X) :
    ∀ (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK)) (p0 : InitiatorParameters F G SPK Msg),
      env.challenge.state = Sum.inl p0 →
      Pr[= true | (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run env
          >>= fun r => (initiatorIdeal P).output r.2.challenge.state
          >>= fun k0 => pure k0.join.isSome]
        = Pr[= true | ($ᵗ K : ProbComp K) >>= fun k =>
            (simulateQ (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk) oa).run
              (envIF P msg hasOPK k env)
            >>= fun r => (initiatorIdealFixed P k).output r.2.challenge.state
            >>= fun k0 => pure k0.join.isSome] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro env p0 henv
    have houtI : (initiatorIdeal P).output
        ((⟨x, env⟩ : X × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)).2.challenge.state)
        = pure none := by
      show (initiatorIdeal P).output env.challenge.state = pure none
      rw [henv]
      rfl
    have houtF : ∀ k : K, (initiatorIdealFixed P k).output
        ((⟨x, envIF P msg hasOPK k env⟩ :
          X × UAKE.Env (uakeInitiatorIdealFixed P msg hasOPK k)).2.challenge.state)
        = pure none := by
      intro k
      show (initiatorIdealFixed P k).output (envIF P msg hasOPK k env).challenge.state
        = pure none
      have : (envIF P msg hasOPK k env).challenge.state = Sum.inl p0 := henv
      rw [this]
      rfl
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, houtI, houtF]
    rw [probOutput_bind_const, probFailure_uniformSample]
    simp
  | query_bind q f ih =>
    intro env p0 henv
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    by_cases hq : ∀ w, q ≠ Sum.inr (UAKE.Op.stepChallenge w)
    · have hcomp : ∀ k : K,
          ((UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk q).run
            (envIF P msg hasOPK k env) >>= fun r =>
            (simulateQ (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk)
              (f r.1)).run r.2 >>= fun r' =>
            (initiatorIdealFixed P k).output r'.2.challenge.state >>= fun k0 =>
            pure k0.join.isSome)
          = ((UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env >>= fun p =>
            (simulateQ (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk)
              (f p.1)).run (envIF P msg hasOPK k p.2) >>= fun r' =>
            (initiatorIdealFixed P k).output r'.2.challenge.state >>= fun k0 =>
            pure k0.join.isSome) := by
        intro k
        rw [← map_run_query_IF_pre P msg hasOPK k tk q env hq]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind,
          Prod.map_fst, Prod.map_snd, id_eq]
      simp only [hcomp]
      rw [probOutput_bind_bind_swap]
      refine probOutput_bind_congr fun p hp => ?_
      have hst := state_preserved_query P msg hasOPK tk q env hq hp
      exact ih p.1 p.2 p0 (hst.trans henv)
    · push_neg at hq
      obtain ⟨w, rfl⟩ := hq
      rcases hdone : env.challengeDone with _ | _
      · rcases w with b | im | c
        · have hIB : (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.bundle b)))).run env
              = initiateIdeal P p0 b >>= fun r =>
                pure (match r with
                  | some (im, ctx) =>
                    (Sum.inl (Message.initial im),
                      ⟨(recordOne (recordOne env.challenge.transcript (Message.bundle b)
                          env.clock).1 (Message.initial im)
                          (recordOne env.challenge.transcript (Message.bundle b) env.clock).2).2,
                        ⟨Sum.inr (Sum.inl ctx),
                          (recordOne (recordOne env.challenge.transcript (Message.bundle b)
                            env.clock).1 (Message.initial im)
                            (recordOne env.challenge.transcript (Message.bundle b)
                              env.clock).2).1⟩,
                        false, env.tSessions⟩)
                  | none => (Sum.inr (), env)) := by
            show (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (UAKE.Op.stepChallenge (Message.bundle b))).run env = _
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdone,
              Bool.false_eq_true, if_false, uakeInitiatorIdeal_U, henv, initiatorIdeal,
              StateT.run_monadLift, monadLift_self, StateT.run_pure, StateT.run_set,
              bind_assoc]
            refine bind_congr fun r => ?_
            rcases r with _ | ⟨im, ctx⟩ <;> rfl
          have hFB : ∀ k : K, (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.bundle b)))).run
                (envIF P msg hasOPK k env)
              = initiateIdeal P p0 b >>= fun r =>
                pure (match r with
                  | some (im, ctx) =>
                    (Sum.inl (Message.initial im),
                      ⟨(recordOne (recordOne (envIF P msg hasOPK k env).challenge.transcript
                          (Message.bundle b) (envIF P msg hasOPK k env).clock).1
                          (Message.initial im)
                          (recordOne (envIF P msg hasOPK k env).challenge.transcript
                            (Message.bundle b) (envIF P msg hasOPK k env).clock).2).2,
                        ⟨Sum.inr (Sum.inl (setCtxKb k ctx)),
                          (recordOne (recordOne (envIF P msg hasOPK k env).challenge.transcript
                            (Message.bundle b) (envIF P msg hasOPK k env).clock).1
                            (Message.initial im)
                            (recordOne (envIF P msg hasOPK k env).challenge.transcript
                              (Message.bundle b) (envIF P msg hasOPK k env).clock).2).1⟩,
                        false, (envIF P msg hasOPK k env).tSessions⟩)
                  | none => (Sum.inr (), envIF P msg hasOPK k env)) := by
            intro k
            show (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (UAKE.Op.stepChallenge (Message.bundle b))).run (envIF P msg hasOPK k env) = _
            have henvF : (envIF P msg hasOPK k env).challenge.state = Sum.inl p0 := henv
            have hdoneF : (envIF P msg hasOPK k env).challengeDone = false := hdone
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdoneF,
              Bool.false_eq_true, if_false, uakeInitiatorIdealFixed_U, henvF,
              initiatorIdealFixed, StateT.run_monadLift, monadLift_self, StateT.run_pure,
              StateT.run_set, bind_assoc]
            refine bind_congr fun r => ?_
            rcases r with _ | ⟨im, ctx⟩ <;> rfl
          simp only [hIB, hFB, bind_assoc, pure_bind]
          rw [initiateIdeal_resample]
          conv_rhs => rw [probOutput_uniform_bind_comm]
          conv_lhs => rw [probOutput_uniform_bind_comm]
          refine probOutput_bind_congr fun r hr => ?_
          rcases r with _ | ⟨im, ctx⟩
          · simp only [Option.map_none]
            rw [probOutput_bind_const, probFailure_uniformSample]
            simp only [tsub_zero, one_mul]
            exact ih (Sum.inr ()) env p0 henv
          · simp only [Option.map_some, Prod.map_apply, id_eq]
            refine probOutput_bind_congr fun k _ => ?_
            have hpost := probOutput_ideal_fixed_post P msg hasOPK k tk
              (f (Sum.inl (Message.initial im)))
            have htail : (fun (r' : X × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)) =>
                (initiatorIdeal P).output r'.2.challenge.state >>=
                  fun k0 => pure k0.join.isSome)
                = (fun z => (initiatorIdealFixed P k).output
                    (Prod.map (id : X → X) (envIF P msg hasOPK k) z).2.challenge.state >>=
                    fun k0 => pure k0.join.isSome) := rfl
            rw [htail,
              ← probOutput_map_bind' _ (Prod.map id (envIF P msg hasOPK k))
                (fun w => (initiatorIdealFixed P k).output w.2.challenge.state >>=
                  fun k0 => pure k0.join.isSome)]
            exact probOutput_bind_congr_left' _ _ _ _
              (fun z => hpost _ z (fun p' h => by simp at h)
                (fun ctx' h => by
                  injection h with h2
                  injection h2 with h3
                  subst h3
                  rfl))
        · have hIT : (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.initial im)))).run env
              = pure (Sum.inr (), env) := by
            show (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (UAKE.Op.stepChallenge (Message.initial im))).run env = _
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdone,
              Bool.false_eq_true, if_false, uakeInitiatorIdeal_U, henv, initiatorIdeal,
              StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc]
            rfl
          have hFT : ∀ k : K, (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.initial im)))).run
                (envIF P msg hasOPK k env)
              = pure (Sum.inr (), envIF P msg hasOPK k env) := by
            intro k
            show (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (UAKE.Op.stepChallenge (Message.initial im))).run (envIF P msg hasOPK k env) = _
            have henvF : (envIF P msg hasOPK k env).challenge.state = Sum.inl p0 := henv
            have hdoneF : (envIF P msg hasOPK k env).challengeDone = false := hdone
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdoneF,
              Bool.false_eq_true, if_false, uakeInitiatorIdealFixed_U, henvF,
              initiatorIdealFixed, StateT.run_monadLift, monadLift_self, StateT.run_pure,
              bind_assoc]
            rfl
          simp only [hIT, hFT, pure_bind]
          exact ih (Sum.inr ()) env p0 henv
        · have hIT : (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.confirmation c)))).run env
              = pure (Sum.inr (), env) := by
            show (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk
              (UAKE.Op.stepChallenge (Message.confirmation c))).run env = _
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdone,
              Bool.false_eq_true, if_false, uakeInitiatorIdeal_U, henv, initiatorIdeal,
              StateT.run_monadLift, monadLift_self, StateT.run_pure, bind_assoc]
            rfl
          have hFT : ∀ k : K, (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (Sum.inr (UAKE.Op.stepChallenge (Message.confirmation c)))).run
                (envIF P msg hasOPK k env)
              = pure (Sum.inr (), envIF P msg hasOPK k env) := by
            intro k
            show (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
              (UAKE.Op.stepChallenge (Message.confirmation c))).run
                (envIF P msg hasOPK k env) = _
            have henvF : (envIF P msg hasOPK k env).challenge.state = Sum.inl p0 := henv
            have hdoneF : (envIF P msg hasOPK k env).challengeDone = false := hdone
            simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdoneF,
              Bool.false_eq_true, if_false, uakeInitiatorIdealFixed_U, henvF,
              initiatorIdealFixed, StateT.run_monadLift, monadLift_self, StateT.run_pure,
              bind_assoc]
            rfl
          simp only [hIT, hFT, pure_bind]
          exact ih (Sum.inr ()) env p0 henv
      · have hIT : (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk
            (Sum.inr (UAKE.Op.stepChallenge w))).run env
            = pure (Sum.inr (), env) := by
          show (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk
            (UAKE.Op.stepChallenge w)).run env = _
          simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdone, if_true,
            StateT.run_pure]
          rfl
        have hFT : ∀ k : K, (UAKE.oracleImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
            (Sum.inr (UAKE.Op.stepChallenge w))).run (envIF P msg hasOPK k env)
            = pure (Sum.inr (), envIF P msg hasOPK k env) := by
          intro k
          show (UAKE.opImpl (uakeInitiatorIdealFixed P msg hasOPK k) tk
            (UAKE.Op.stepChallenge w)).run (envIF P msg hasOPK k env) = _
          have hdoneF : (envIF P msg hasOPK k env).challengeDone = true := hdone
          simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind, hdoneF, if_true,
            StateT.run_pure]
          rfl
        simp only [hIT, hFT, pure_bind]
        exact ih (Sum.inr ()) env p0 henv
private lemma ideal_game_eq_fixed_avg [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    Pr[= true | do
        let x ← (uakeInitiatorIdeal P msg hasOPK).setup
        let r ← UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK)
          A.toIdeal x.1 x.2
        pure r.1.K0.isSome]
      = Pr[= true | do
        let k ← ($ᵗ K : ProbComp K)
        let x ← (uakeInitiatorIdealFixed P msg hasOPK k).setup
        let r ← UAKE.challengeSession (proto := uakeInitiatorIdealFixed P msg hasOPK k)
          (A.toFixed k) x.1 x.2
        pure r.1.K0.isSome] := by
  have hsetI : (uakeInitiatorIdeal P msg hasOPK).setup = setup P msg := rfl
  have hsetF : ∀ k : K, (uakeInitiatorIdealFixed P msg hasOPK k).setup = setup P msg :=
    fun _ => rfl
  simp only [hsetI, hsetF]
  conv_rhs => rw [probOutput_uniform_bind_comm]
  refine probOutput_bind_congr fun x _ => ?_
  unfold UAKE.challengeSession
  have hInitI : ((uakeInitiatorIdeal P msg hasOPK).U.init x.1 : ProbComp _)
      = pure (Party.InitResult.waitForMsg (Sum.inl x.1)) := rfl
  have hInitF : ∀ k : K, ((uakeInitiatorIdealFixed P msg hasOPK k).U.init x.1 : ProbComp _)
      = pure (Party.InitResult.waitForMsg (Sum.inl x.1)) := fun _ => rfl
  simp only [AKE.UAKE.Adversary.toIdeal, AKE.UAKE.Adversary.toFixed, hInitI, hInitF,
    pure_bind, bind_assoc, Party.InitResult.opening, Party.InitResult.state]
  exact probOutput_ideal_fixed_pre P msg hasOPK x.2 (A.challenge x.1 none) _ x.1 rfl

private lemma probOutput_fstmap_le {γ δ ε : Type} (oa : ProbComp (γ × δ)) (m : γ → ε)
    (F : ε → Bool) (G : γ × δ → Bool)
    (h : ∀ z ∈ support oa, F (m z.1) = true → G z = true) :
    Pr[= true | (m <$> (Prod.fst <$> oa)) >>= fun r => pure (F r)]
      ≤ Pr[= true | oa >>= fun z => pure (G z)] := by
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  refine probOutput_bind_mono fun z hz => ?_
  rcases hF : F (m z.1) with _ | _
  · simp [hF]
  · simp [hF, h z hz hF]

set_option maxHeartbeats 800000 in
private lemma fixed_game_le_flag_game [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq (G × G × PQPK)] [DecidableEq C]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (k : K) :
    Pr[= true | do
        let x ← (uakeInitiatorIdealFixed P msg hasOPK k).setup
        let r ← UAKE.challengeSession (proto := uakeInitiatorIdealFixed P msg hasOPK k)
          (A.toFixed k) x.1 x.2
        pure r.1.K0.isSome]
      ≤ Pr[= true | do
        let z ← (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
          (aeadForger P msg hasOPK A).run).run ([], false)
        pure z.2.2] := by
  have hR : (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
      (aeadForger P msg hasOPK A).run).run ([], false)
      = setup P msg >>= fun uktk =>
          (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
            (UAKE.challengeSession (proto := schemeAeadForger P msg hasOPK)
              A.toAeadForger uktk.1 uktk.2)).run ([], false) >>= fun rs =>
          pure ((), rs.2) := by
    simp only [aeadForger, simulateQ_bind, StateT.run_bind,
      simulateQ_pure, StateT.run_pure, simulateQ_decImpl_liftM]
    erw [StateT.run_liftM]
    simp only [bind_assoc, pure_bind]
  rw [hR]
  have hset : (uakeInitiatorIdealFixed P msg hasOPK k).setup = setup P msg := rfl
  rw [hset]
  simp only [bind_assoc, pure_bind]
  refine probOutput_bind_mono fun uktk _ => ?_
  rw [← fst_run_dec_challengeSession P msg hasOPK k uktk.1 uktk.2 A]
  generalize hRUN : (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
    (UAKE.challengeSession (proto := schemeAeadForger P msg hasOPK)
      A.toAeadForger uktk.1 uktk.2)).run ([], false) = RUN
  refine probOutput_fstmap_le RUN _ _ _ fun z hz hK => ?_
  rw [← hRUN] at hz
  exact dec_challengeSession_flag P msg hasOPK k uktk.1 uktk.2 A z hz hK


private lemma probOutput_true_and_partition {α : Type} (X : ProbComp α) (b c : α → Bool) :
    Pr[= true | do let x ← X; pure (b x)]
      = Pr[= true | do let x ← X; pure (b x && c x)]
        + Pr[= true | do let x ← X; pure (b x && !c x)] := by
  simp only [probOutput_bind_eq_tsum, probOutput_pure]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  rw [← mul_add]
  congr 1
  cases b x <;> cases c x <;> simp

noncomputable def idealAuthBreak [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ≥0∞ :=
  Pr[= true | do
    let x ← (uakeInitiatorIdeal P msg hasOPK).setup
    let r ← UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK) A.toIdeal x.1 x.2
    pure (r.1.K0.isSome && !UAKE.isPingPong r.1)]

private lemma uakeInitiatorIdeal_setup [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).setup = setup P msg := rfl

private lemma idealAuthBreak_eq_forger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    idealAuthBreak P msg hasOPK A =
    Pr[= true | do
      let ikA ← dhKeygen P.gen
      let ikB ← dhKeygen P.gen
      let sigkB ← P.sig.keygen
      let spkB ← dhKeygen P.gen
      let r ← Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
          (m := ProbComp)).liftTarget (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp)
          + P.sig.signingOracle sigkB.1 sigkB.2)
        (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
            (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
          UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger
            ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, (sigkB.1, default), spkB, spkSigB⟩)).run
      pure (r.1.K0.isSome && !UAKE.isPingPong r.1)] := by
  unfold idealAuthBreak
  simp only [uakeInitiatorIdeal_setup, setup, bind_assoc, pure_bind]
  congr 1
  refine bind_congr fun ikA => bind_congr fun ikB =>
    bind_congr fun sigkB => bind_congr fun spkB => ?_
  rw [fst_run_sim_queryBind P sigkB.1 sigkB.2, bind_assoc]
  refine bind_congr fun spkSigB => ?_
  rw [← fst_run_challengeSession P msg hasOPK ⟨ikA, ikB.1, sigkB.1, msg⟩
    ⟨ikB, sigkB, spkB, spkSigB⟩ sigkB.1 sigkB.2 rfl A,
    ← fst_run_challengeSession_sigkB P msg hasOPK ⟨ikA, ikB.1, sigkB.1, msg⟩
    ⟨ikB, sigkB, spkB, spkSigB⟩ (sigkB.1, default) sigkB.1 sigkB.2 A]
  simp only [Functor.map_map]
  refine Eq.trans (bind_map_left (m := ProbComp) _ _ _) ?_
  refine Eq.trans ?_ (bind_map_left (m := ProbComp) _ _ _).symm
  refine bind_congr fun r => ?_
  exact congrArg pure (crFI_authBreak P msg hasOPK r.1.1)

private lemma sigForger_strongAdvantage_eq [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq S]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    ((sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp) =
    Pr[= true | do
      let pksk ← P.sig.keygen
      let ikA ← dhKeygen P.gen
      let ikB ← dhKeygen P.gen
      let spkB ← dhKeygen P.gen
      let guess ← ($ᵗ Bool : ProbComp _)
      let cl ← (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
          (m := ProbComp)).liftTarget (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp)
          + P.sig.signingOracle pksk.1 pksk.2)
        (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
            (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
          UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger
            ⟨ikA, ikB.1, pksk.1, msg⟩ ⟨ikB, (pksk.1, default), spkB, spkSigB⟩)).run
      let fs := extractForgery guess cl.1.2.2.1.challenge.transcript
      let verified ← P.sig.verify pksk.1 fs.1 fs.2
      pure (!cl.2.wasQueriedWith fs.1 fs.2 && verified)] := by
  unfold SignatureAlg.unforgeableAdv.strongAdvantage SignatureAlg.stronglyUnforgeableExp
  rw [probOutput_probComp_evalDist]
  simp only [sigForger, run_sim_liftM_bind, run_sim_queryBind_pure, bind_assoc, pure_bind]
  refine congrArg (fun c => probOutput c true) ?_
  refine bind_congr fun a => bind_congr fun b => bind_congr fun c => bind_congr fun d =>
    bind_congr fun e => bind_congr fun f => bind_congr fun g => ?_
  congr 1
  refine congrArg (fun q => !q && g) ?_
  congr 1
  congr 1 <;> subsingleton

private def ChallengeBundlesVerify [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (uk : InitiatorParameters F G SPK Msg)
    (ch : Session (InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
      (Message G PQPK CT S C IdC IdK)) : Prop :=
  (∀ p, ch.state = Sum.inl p → p = uk) ∧
  (∀ e ∈ ch.transcript.entries, ∀ b, e.1 = Message.bundle b →
    true ∈ support (P.sig.verify uk.sigpkB (EncodeEC b.spkB.1) b.spkSigB) ∧
      true ∈ support (P.sig.verify uk.sigpkB (EncodeKEM b.pqpkB.1) b.pqpkSigB)) ∧
  ((∀ p, ch.state ≠ Sum.inl p) → ∃ e ∈ ch.transcript.entries, ∃ b, e.1 = Message.bundle b)

private lemma initiatorIdeal_step_accept_bundle [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (state : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w w' : Message G PQPK CT S C IdC IdK)
    (st' : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K) (done : Bool)
    (hsr : Party.StepResult.acceptAndSend st' w' done ∈ support ((initiatorIdeal P).step state w)) :
    ∃ p b im ctx, state = Sum.inl p ∧ w = Message.bundle b ∧ w' = Message.initial im ∧
      st' = Sum.inr (Sum.inl ctx) ∧ some (im, ctx) ∈ support (initiateIdeal P p b) := by
  cases state with
  | inl p =>
    cases w with
    | bundle b =>
      simp only [initiatorIdeal] at hsr
      obtain ⟨r, hr, hsr⟩ := (mem_support_bind_iff _ _ _).1 hsr
      cases r with
      | none => exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | some imctx =>
        obtain ⟨im, ctx⟩ := imctx
        have heq := (mem_support_pure_iff' _ _).1 hsr
        injection heq with h1 h2 h3
        subst h1; subst h2
        exact ⟨p, b, im, ctx, rfl, rfl, rfl, rfl, hr⟩
    | initial im =>
      simp only [initiatorIdeal] at hsr
      exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
    | confirmation c =>
      simp only [initiatorIdeal] at hsr
      exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
  | inr rest =>
    cases rest with
    | inl ctx =>
      cases w with
      | bundle b =>
        simp only [initiatorIdeal] at hsr
        exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | initial im =>
        simp only [initiatorIdeal] at hsr
        exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | confirmation conf =>
        simp only [initiatorIdeal] at hsr
        cases hcf : confirm P ctx conf with
        | none => rw [hcf] at hsr; exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
        | some SK => rw [hcf] at hsr; exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
    | inr SK =>
      cases w <;>
        (simp only [initiatorIdeal] at hsr
         exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp))

private lemma initiatorIdeal_step_complete_conf [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (state : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK)
    (st' : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (hsr : Party.StepResult.complete st' ∈ support ((initiatorIdeal P).step state w)) :
    ∃ ctx conf SK, state = Sum.inr (Sum.inl ctx) ∧ w = Message.confirmation conf ∧
      st' = Sum.inr (Sum.inr SK) := by
  cases state with
  | inl p =>
    cases w with
    | bundle b =>
      simp only [initiatorIdeal] at hsr
      obtain ⟨r, -, hsr⟩ := (mem_support_bind_iff _ _ _).1 hsr
      cases r with
      | none => exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | some imctx =>
        obtain ⟨im, ctx⟩ := imctx
        exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
    | initial im =>
      simp only [initiatorIdeal] at hsr
      exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
    | confirmation c =>
      simp only [initiatorIdeal] at hsr
      exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
  | inr rest =>
    cases rest with
    | inl ctx =>
      cases w with
      | bundle b =>
        simp only [initiatorIdeal] at hsr
        exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | initial im =>
        simp only [initiatorIdeal] at hsr
        exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
      | confirmation conf =>
        simp only [initiatorIdeal] at hsr
        cases hcf : confirm P ctx conf with
        | none => rw [hcf] at hsr; exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp)
        | some SK =>
          rw [hcf] at hsr
          have heq := (mem_support_pure_iff' _ _).1 hsr
          injection heq with h1
          exact ⟨ctx, conf, SK, rfl, rfl, h1.symm⟩
    | inr SK =>
      cases w <;>
        (simp only [initiatorIdeal] at hsr
         exact absurd ((mem_support_pure_iff' _ _).1 hsr) (by simp))

private lemma challengeBundlesVerify_withUnif_query [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env0 : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    {renv : _ × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hinv : ChallengeBundlesVerify P uk env0.challenge)
    (hmem : renv ∈ support
      ((UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env0)) :
    ChallengeBundlesVerify P uk renv.2.challenge := by
  cases q with
  | inl u =>
    have hch : renv.2 = env0 := by
      simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        HasQuery.toQueryImpl_apply] at hmem
      erw [StateT.run_liftM] at hmem
      obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hmem
      obtain rfl := (mem_support_pure_iff' _ _).1 hr
      rfl
    rw [hch]; exact hinv
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr] at hmem
    cases op with
    | openT =>
      have hch : renv.2.challenge = env0.challenge := by
        simp only [UAKE.opImpl, uakeInitiatorIdeal_T] at hmem
        simp at hmem
        obtain ⟨r, -, hr⟩ := hmem
        simp at hr; subst hr; rfl
      rw [hch]; exact hinv
    | stepT sid w =>
      have hch : renv.2.challenge = env0.challenge := by
        simp only [UAKE.opImpl, uakeInitiatorIdeal_T] at hmem
        cases hs : env0.tSessions[sid]? with
        | none => simp [hs] at hmem; subst hmem; rfl
        | some t =>
          cases hk : t.key with
          | some v => simp [hs, hk] at hmem; subst hmem; rfl
          | none =>
            simp [hs, hk] at hmem
            obtain ⟨sr, -, hr⟩ := Set.mem_iUnion₂.1 hmem
            cases sr with
            | reject => simp at hr; subst hr; rfl
            | acceptAndSend st' w' done =>
              cases done with
              | false => simp at hr; subst hr; rfl
              | true =>
                obtain ⟨y, -, hr2⟩ := (mem_support_bind_iff _ _ _).1 hr
                simp at hr2; subst hr2; rfl
            | complete st' =>
              obtain ⟨key, -, hr2⟩ := (mem_support_bind_iff _ _ _).1 hr
              simp at hr2; subst hr2; rfl
      rw [hch]; exact hinv
    | revealT sid =>
      have hch : renv.2.challenge = env0.challenge := by
        simp only [UAKE.opImpl] at hmem
        cases hs : env0.tSessions[sid]? with
        | none => simp [hs] at hmem; subst hmem; rfl
        | some t => simp [hs] at hmem; subst hmem; rfl
      rw [hch]; exact hinv
    | stepChallenge w =>
      simp only [UAKE.opImpl, uakeInitiatorIdeal_U] at hmem
      by_cases hdone : env0.challengeDone = true
      · simp [hdone] at hmem; subst hmem; exact hinv
      · simp [hdone] at hmem
        obtain ⟨ha, hb, hc⟩ := hinv
        obtain ⟨sr, hsr, hr⟩ := Set.mem_iUnion₂.1 hmem
        cases sr with
        | reject =>
          obtain rfl := (mem_support_pure_iff' _ _).1 hr
          exact ⟨ha, hb, hc⟩
        | acceptAndSend st' w' done =>
          obtain ⟨p, b, im, ctx, hstate, hwb, hw', hst', hinit⟩ :=
            initiatorIdeal_step_accept_bundle P _ w w' st' done hsr
          have hp : p = uk := ha p hstate
          subst hp
          have hver := initiateIdeal_verify_of_accept P p b hinit
          subst hwb; subst hw'; subst hst'
          simp at hr
          subst hr
          refine ⟨?_, ?_, ?_⟩
          · intro q hq; exact absurd hq (by simp)
          · intro e he bb hbb
            simp only [recordOne, List.mem_append, List.mem_singleton] at he
            rcases he with (he | he) | he
            · exact hb e he bb hbb
            · subst he; simp only [Message.bundle.injEq] at hbb; subst hbb; exact hver
            · subst he; simp at hbb
          · intro _
            exact ⟨(Message.bundle b, env0.clock), by simp [recordOne], b, rfl⟩
        | complete st' =>
          obtain ⟨ctx, conf, SK, hstate, hwc, hst'⟩ :=
            initiatorIdeal_step_complete_conf P _ w st' hsr
          simp at hr
          subst hr
          refine ⟨?_, ?_, ?_⟩
          · intro q hq; rw [hst'] at hq; exact absurd hq (by simp)
          · intro e he bb hbb
            simp only [recordOne, List.mem_append, List.mem_singleton] at he
            rcases he with he | he
            · exact hb e he bb hbb
            · subst he; rw [hwc] at hbb; simp at hbb
          · intro _
            obtain ⟨e, he, bb, hbb⟩ := hc (by rw [hstate]; intro q; simp)
            exact ⟨e, by simp only [recordOne, List.mem_append]; exact Or.inl he, bb, hbb⟩

private lemma challengeBundlesVerify_run [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X) :
    ∀ (env0 : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
      (renv : X × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)),
      ChallengeBundlesVerify P uk env0.challenge →
      renv ∈ support
        ((simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run
          env0) →
      ChallengeBundlesVerify P uk renv.2.challenge := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro env0 renv hinv hmem
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hinv
  | query_bind q oa' ih =>
    intro env0 renv hinv hmem
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind] at hmem
    obtain ⟨pr, hpr, hr⟩ := (mem_support_bind_iff _ _ _).1 hmem
    exact ih pr.1 pr.2 renv
      (challengeBundlesVerify_withUnif_query P msg hasOPK uk tk q env0 hinv hpr) hr

private lemma oracleImpl_challengeDone_true [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env0 : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    {renv : _ × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hdone : env0.challengeDone = true)
    (hmem : renv ∈ support ((UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run env0)) :
    renv.2.challengeDone = true := by
  cases op with
  | openT =>
    have hch : renv.2.challengeDone = env0.challengeDone := by
      simp only [UAKE.opImpl, uakeInitiatorIdeal_T] at hmem
      simp at hmem
      obtain ⟨r, -, hr⟩ := hmem
      subst hr; rfl
    rw [hch]; exact hdone
  | stepT sid w =>
    have hch : renv.2.challengeDone = env0.challengeDone := by
      simp only [UAKE.opImpl, uakeInitiatorIdeal_T] at hmem
      cases hs : env0.tSessions[sid]? with
      | none => simp [hs] at hmem; subst hmem; rfl
      | some t =>
        cases hk : t.key with
        | some v => simp [hs, hk] at hmem; subst hmem; rfl
        | none =>
          simp [hs, hk] at hmem
          obtain ⟨sr, -, hr⟩ := hmem
          cases sr with
          | reject => simp at hr; subst hr; rfl
          | acceptAndSend st' w' done =>
            cases done with
            | false => simp at hr; subst hr; rfl
            | true =>
              obtain ⟨y, -, hr2⟩ := (mem_support_bind_iff _ _ _).1 hr
              simp at hr2; subst hr2; rfl
          | complete st' =>
            obtain ⟨key, -, hr2⟩ := (mem_support_bind_iff _ _ _).1 hr
            simp at hr2; subst hr2; rfl
    rw [hch]; exact hdone
  | revealT sid =>
    have hch : renv.2.challengeDone = env0.challengeDone := by
      simp only [UAKE.opImpl] at hmem
      cases hs : env0.tSessions[sid]? with
      | none => simp [hs] at hmem; subst hmem; rfl
      | some t => simp [hs] at hmem; subst hmem; rfl
    rw [hch]; exact hdone
  | stepChallenge w =>
    simp only [UAKE.opImpl, uakeInitiatorIdeal_U] at hmem
    simp [hdone] at hmem
    subst hmem; exact hdone

private lemma oracleImpl_challenge_frame [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (ch : Session (InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
      (Message G PQPK CT S C IdC IdK))
    (hdone : env.challengeDone = true) :
    (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run { env with challenge := ch }
      = (fun p => (p.1, { p.2 with challenge := ch }))
        <$> (UAKE.opImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run env := by
  cases op with
  | openT =>
    simp only [UAKE.opImpl, uakeInitiatorIdeal_T, StateT.run_bind, StateT.run_monadLift,
      StateT.run_get, StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
      map_bind, map_pure]
  | stepT sid w =>
    simp only [UAKE.opImpl, uakeInitiatorIdeal_T, StateT.run_bind, StateT.run_get, pure_bind]
    cases hs : env.tSessions[sid]? with
    | none => simp [StateT.run_pure, map_pure]
    | some t =>
      cases hk : t.key with
      | some v => simp [hk, StateT.run_pure, map_pure]
      | none =>
        simp only [hk, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun sr => ?_
        cases sr with
        | reject => simp [StateT.run_pure, map_pure]
        | acceptAndSend st' w' done =>
          cases done <;>
            simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_map,
              monadLift_self, map_pure]
        | complete st' =>
          simp [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_map,
            monadLift_self, map_pure]
  | revealT sid =>
    simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind]
    cases hs : env.tSessions[sid]? with
    | none => simp [StateT.run_pure, map_pure]
    | some t =>
      simp [StateT.run_set, map_pure]
  | stepChallenge w =>
    simp only [UAKE.opImpl, uakeInitiatorIdeal_U, StateT.run_bind, StateT.run_get, pure_bind,
      hdone, if_true, StateT.run_pure, map_pure]

private lemma withUnif_challenge_frame [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (ch : Session (InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
      (Message G PQPK CT S C IdC IdK))
    (hdone : env.challengeDone = true) :
    (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run { env with challenge := ch }
      = (fun p => (p.1, { p.2 with challenge := ch }))
        <$> (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env := by
  cases q with
  | inl u =>
    simp [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, Functor.map_map]
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr]
    exact oracleImpl_challenge_frame P msg hasOPK tk op env ch hdone

private lemma withUnif_challengeDone_true [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    {renv : _ × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)}
    (hdone : env.challengeDone = true)
    (hmem : renv ∈ support ((UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk q).run env)) :
    renv.2.challengeDone = true := by
  cases q with
  | inl u =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply] at hmem
    erw [StateT.run_liftM] at hmem
    obtain ⟨a, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hmem
    obtain rfl := (mem_support_pure_iff' _ _).1 hr
    exact hdone
  | inr op =>
    simp only [UAKE.oracleImpl, QueryImpl.add_apply_inr] at hmem
    exact oracleImpl_challengeDone_true P msg hasOPK tk op env hdone hmem

private lemma run_post_frame [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X) :
    ∀ (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
      (ch : Session (InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
        (Message G PQPK CT S C IdC IdK)),
      env.challengeDone = true →
      (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run
          { env with challenge := ch }
        = (fun p => (p.1, { p.2 with challenge := ch }))
          <$> (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) oa).run
            env := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro env ch hdone
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q oa' ih =>
    intro env ch hdone
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [withUnif_challenge_frame P msg hasOPK tk q env ch hdone, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun p hp => ?_
    exact ih p.1 p.2 ch (withUnif_challengeDone_true P msg hasOPK tk q env hdone hp)

private lemma extractForgery_verify [Inhabited G] [Inhabited S]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (guess : Bool) (uk : InitiatorParameters F G SPK Msg)
    (tr : Transcript (Message G PQPK CT S C IdC IdK))
    (hall : ∀ e ∈ tr.entries, ∀ b, e.1 = Message.bundle b →
      true ∈ support (P.sig.verify uk.sigpkB (EncodeEC b.spkB.1) b.spkSigB) ∧
        true ∈ support (P.sig.verify uk.sigpkB (EncodeKEM b.pqpkB.1) b.pqpkSigB))
    (hex : ∃ e ∈ tr.entries, ∃ b, e.1 = Message.bundle b) :
    true ∈ support (P.sig.verify uk.sigpkB (extractForgery guess tr).1
      (extractForgery guess tr).2) := by
  unfold extractForgery
  split
  · next fs hfs =>
      obtain ⟨e, he, hge⟩ := List.exists_of_findSome?_eq_some hfs
      cases he1 : e.1 with
      | bundle b =>
        rw [he1] at hge
        obtain ⟨hv1, hv2⟩ := hall e he b he1
        cases guess with
        | true => injection hge with hge'; subst hge'; exact hv2
        | false => injection hge with hge'; subst hge'; exact hv1
      | initial im => rw [he1] at hge; simp at hge
      | confirmation c => rw [he1] at hge; simp at hge
  · next hfs =>
      exfalso
      obtain ⟨e, he, b, hb⟩ := hex
      rw [List.findSome?_eq_none_iff] at hfs
      have hcontra := hfs e he
      rw [hb] at hcontra
      simp at hcontra

private lemma uakeIdeal_authBreak_verified [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (guess : Bool) (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S)
    (A : UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK))
    (v : UAKE.ChallengeResult (uakeInitiatorIdeal P msg hasOPK) ×
      (A.State × UAKE.Env (uakeInitiatorIdeal P msg hasOPK) × RecipientIdentity F G SPK SSK S))
    (hv : v ∈ support (UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK) A uk tk))
    (hK0 : v.1.K0.isSome = true) :
    true ∈ support (P.sig.verify uk.sigpkB
      (extractForgery guess v.2.2.1.challenge.transcript).1
      (extractForgery guess v.2.2.1.challenge.transcript).2) := by
  unfold UAKE.challengeSession at hv
  obtain ⟨u0, hu0, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  simp only [uakeInitiatorIdeal_U, initiatorIdeal] at hu0
  obtain rfl := (mem_support_pure_iff' _ _).1 hu0
  simp only [Party.InitResult.opening, Party.InitResult.state, recordOpt] at hv
  obtain ⟨⟨st, env⟩, hrun, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  obtain ⟨k0, hk0, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  obtain rfl := (mem_support_pure_iff' _ _).1 hv
  have hinit : ChallengeBundlesVerify P uk
      (⟨Sum.inl uk, ⟨[]⟩⟩ : Session (InitiatorParameters F G SPK Msg ⊕
        SessionContext G PQPK Msg K ⊕ K) (Message G PQPK CT S C IdC IdK)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp; injection hp with h; exact h.symm
    · intro e he; simp at he
    · intro hcon; exact absurd rfl (hcon uk)
  obtain ⟨ha, hb, hc⟩ := challengeBundlesVerify_run P msg hasOPK uk tk (A.challenge uk none)
    ⟨0, ⟨Sum.inl uk, ⟨[]⟩⟩, false, []⟩ (st, env) hinit hrun
  obtain ⟨SK, hstate⟩ :=
    initiatorIdeal_output_completed P env.challenge.state hk0 (by simpa using hK0)
  exact extractForgery_verify P guess uk env.challenge.transcript hb
    (hc (by rw [hstate]; intro p; simp))

private lemma schemeForger_authBreak_verified [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (guess : Bool) (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S))
    (hcl : cl ∈ support
      ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run))
    (hK0 : cl.1.1.K0.isSome = true) :
    true ∈ support (P.sig.verify uk.sigpkB
      (extractForgery guess cl.1.2.2.1.challenge.transcript).1
      (extractForgery guess cl.1.2.2.1.challenge.transcript).2) := by
  have hmem2 : (crFI P msg hasOPK cl.1.1,
      (cl.1.2.1, envFI P msg hasOPK cl.1.2.2.1, cl.1.2.2.2)) ∈
      support (UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK)
        A.toIdeal uk tk) := by
    rw [← fst_run_challengeSession P msg hasOPK uk tk pk sk hsig A]
    refine (support_map _ _).ge ?_
    refine Set.mem_image_of_mem _ ((support_map _ _).ge ?_)
    exact Set.mem_image_of_mem _ hcl
  have hres := uakeIdeal_authBreak_verified P msg hasOPK guess uk tk A.toIdeal _ hmem2
    (by simpa [crFI] using hK0)
  simpa [envFI] using hres

private lemma schemeForger_authBreak_verified_default [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (guess : Bool) (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
      (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S))
    (hcl : cl ∈ support
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
          (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run))
    (hK0 : cl.1.K0.isSome = true) :
    true ∈ support (P.sig.verify uk.sigpkB
      (extractForgery guess cl.2.2.1.challenge.transcript).1
      (extractForgery guess cl.2.2.1.challenge.transcript).2) := by
  have hmem : (fun r => (r.1, (r.2.1, envSig P msg hasOPK (pk, sk) r.2.2.1,
        (⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩ : RecipientIdentity F G SPK SSK S)))) cl
      ∈ support (Prod.fst <$> (simulateQ
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
            (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
          ⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩)).run) := by
    rw [← fst_run_challengeSession_sigkB P msg hasOPK uk tk (pk, sk) pk sk A]
    exact (support_map _ _).ge (Set.mem_image_of_mem _ hcl)
  rw [support_map] at hmem
  obtain ⟨clr, hclr, hclr_eq⟩ := hmem
  have hres := schemeForger_authBreak_verified P msg hasOPK guess uk
    ⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩ pk sk rfl A clr hclr (by rw [hclr_eq]; exact hK0)
  rw [hclr_eq] at hres
  simpa [envSig] using hres

private lemma schemeForger_authBreak_verified_queryBind [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (guess : Bool) (uk : InitiatorParameters F G SPK Msg)
    (ikB spkB : G × F) (pk : SPK) (sk : SSK)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S))
    (hcl : cl ∈ support
      ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
            (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
          UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
            ⟨ikB, (pk, default), spkB, spkSigB⟩)).run))
    (hK0 : cl.1.1.K0.isSome = true) :
    true ∈ support (P.sig.verify uk.sigpkB
      (extractForgery guess cl.1.2.2.1.challenge.transcript).1
      (extractForgery guess cl.1.2.2.1.challenge.transcript).2) := by
  have h1 : cl.1 ∈ support (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
      (m := ProbComp)).liftTarget
      (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
    (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
        (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
      UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
        ⟨ikB, (pk, default), spkB, spkSigB⟩)).run) :=
    (support_map _ _).ge (Set.mem_image_of_mem _ hcl)
  rw [fst_run_sim_queryBind] at h1
  obtain ⟨σ, hσ, h1⟩ := (mem_support_bind_iff _ _ _).1 h1
  exact schemeForger_authBreak_verified_default P msg hasOPK guess uk
    ⟨ikB, (pk, default), spkB, σ⟩ pk sk A cl.1 h1 hK0

private lemma uakeIdeal_K0_bundle [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S)
    (A : UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK))
    (v : UAKE.ChallengeResult (uakeInitiatorIdeal P msg hasOPK) ×
      (A.State × UAKE.Env (uakeInitiatorIdeal P msg hasOPK) × RecipientIdentity F G SPK SSK S))
    (hv : v ∈ support (UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK) A uk tk))
    (hK0 : v.1.K0.isSome = true) :
    ∃ e ∈ v.2.2.1.challenge.transcript.entries, ∃ b, e.1 = Message.bundle b := by
  unfold UAKE.challengeSession at hv
  obtain ⟨u0, hu0, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  simp only [uakeInitiatorIdeal_U, initiatorIdeal] at hu0
  obtain rfl := (mem_support_pure_iff' _ _).1 hu0
  simp only [Party.InitResult.opening, Party.InitResult.state, recordOpt] at hv
  obtain ⟨⟨st, env⟩, hrun, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  obtain ⟨k0, hk0, hv⟩ := (mem_support_bind_iff _ _ _).1 hv
  obtain rfl := (mem_support_pure_iff' _ _).1 hv
  have hinit : ChallengeBundlesVerify P uk
      (⟨Sum.inl uk, ⟨[]⟩⟩ : Session (InitiatorParameters F G SPK Msg ⊕
        SessionContext G PQPK Msg K ⊕ K) (Message G PQPK CT S C IdC IdK)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp; injection hp with h; exact h.symm
    · intro e he; simp at he
    · intro hcon; exact absurd rfl (hcon uk)
  obtain ⟨ha, hb, hc⟩ := challengeBundlesVerify_run P msg hasOPK uk tk (A.challenge uk none)
    ⟨0, ⟨Sum.inl uk, ⟨[]⟩⟩, false, []⟩ (st, env) hinit hrun
  obtain ⟨SK, hstate⟩ :=
    initiatorIdeal_output_completed P env.challenge.state hk0 (by simpa using hK0)
  exact hc (by rw [hstate]; intro p; simp)

private lemma schemeForger_K0_bundle [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S))
    (hcl : cl ∈ support
      ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run))
    (hK0 : cl.1.1.K0.isSome = true) :
    ∃ e ∈ cl.1.2.2.1.challenge.transcript.entries, ∃ b, e.1 = Message.bundle b := by
  have hmem2 : (crFI P msg hasOPK cl.1.1,
      (cl.1.2.1, envFI P msg hasOPK cl.1.2.2.1, cl.1.2.2.2)) ∈
      support (UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK)
        A.toIdeal uk tk) := by
    rw [← fst_run_challengeSession P msg hasOPK uk tk pk sk hsig A]
    refine (support_map _ _).ge ?_
    refine Set.mem_image_of_mem _ ((support_map _ _).ge ?_)
    exact Set.mem_image_of_mem _ hcl
  have hres := uakeIdeal_K0_bundle P msg hasOPK uk tk A.toIdeal _ hmem2
    (by simpa [crFI] using hK0)
  simpa [envFI] using hres

private lemma schemeForger_K0_bundle_default [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg)
    (tk : RecipientIdentity F G SPK SSK S) (pk : SPK) (sk : SSK)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
      (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S))
    (hcl : cl ∈ support
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
          (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk)).run))
    (hK0 : cl.1.K0.isSome = true) :
    ∃ e ∈ cl.2.2.1.challenge.transcript.entries, ∃ b, e.1 = Message.bundle b := by
  have hmem : (fun r => (r.1, (r.2.1, envSig P msg hasOPK (pk, sk) r.2.2.1,
        (⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩ : RecipientIdentity F G SPK SSK S)))) cl
      ∈ support (Prod.fst <$> (simulateQ
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
            (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
          ⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩)).run) := by
    rw [← fst_run_challengeSession_sigkB P msg hasOPK uk tk (pk, sk) pk sk A]
    exact (support_map _ _).ge (Set.mem_image_of_mem _ hcl)
  rw [support_map] at hmem
  obtain ⟨clr, hclr, hclr_eq⟩ := hmem
  have hres := schemeForger_K0_bundle P msg hasOPK uk
    ⟨tk.ikB, (pk, sk), tk.spkB, tk.spkSigB⟩ pk sk rfl A clr hclr (by rw [hclr_eq]; exact hK0)
  rw [hclr_eq] at hres
  simpa [envSig] using hres

private lemma probOutput_guess_half {E : Type} (p : ProbComp (Bool × E)) (cond : E → Bool) :
    Pr[= true | do
      let b ← $ᵗ Bool
      let x ← p
      if cond x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == b)] = 1 / 2 := by
  have h : Pr[= true | do
        let x ← p; if cond x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == true)]
      + Pr[= true | do
        let x ← p; if cond x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == false)] = 1 := by
    simp only [probOutput_bind_eq_tsum]
    rw [← ENNReal.tsum_add, ← tsum_probOutput_of_liftM_PMF (mx := p)]
    refine tsum_congr fun x => ?_
    rw [← mul_add]
    conv_rhs => rw [← mul_one (Pr[= x | p])]
    congr 1
    cases hc : cond x.2 with
    | true =>
      simp only [if_true, probOutput_uniformSample, Fintype.card_bool, Nat.cast_ofNat]
      exact ENNReal.inv_two_add_inv_two
    | false => cases x.1 <;> simp [probOutput_pure]
  rw [probOutput_bind_uniformBool, h]

private lemma finalize_pingPong_half [SampleableType K] {E : Type}
    (postrun : K → ProbComp (Bool × E)) (condfn : E → Bool) :
    Pr[= true | do
      let b ← $ᵗ Bool
      let SK ← $ᵗ K
      let K1 ← $ᵗ K
      let x ← postrun (if b then K1 else SK)
      if condfn x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == b)] = 1 / 2 := by
  have key : ∀ c : Bool,
      Pr[= true | do
        let SK ← $ᵗ K
        let K1 ← $ᵗ K
        let x ← postrun (if c then K1 else SK)
        if condfn x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == c)]
        = Pr[= true | do
          let k ← $ᵗ K
          let x ← postrun k
          if condfn x.2 then ($ᵗ Bool : ProbComp Bool) else pure (x.1 == c)] := by
    intro c
    cases c with
    | true =>
      simp only [if_true]
      rw [probOutput_bind_const, probFailure_uniformSample]
      simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [probOutput_bind_bind_swap, probOutput_bind_const, probFailure_uniformSample]
      simp
  rw [probOutput_bind_uniformBool, key true, key false]
  have hg := probOutput_guess_half (do let k ← $ᵗ K; postrun k) condfn
  rw [probOutput_bind_uniformBool] at hg
  simp only [bind_assoc] at hg
  exact hg

private lemma probOutput_bind_half_add {γ : Type} (core : ProbComp γ)
    (g g' : γ → ProbComp Bool) (hcore : Pr[⊥ | core] = 0)
    (hg : ∀ c, Pr[= true | g c] = 1 / 2 + Pr[= true | g' c] / 2) :
    Pr[= true | do let c ← core; g c] = 1 / 2 + Pr[= true | do let c ← core; g' c] / 2 := by
  rw [probOutput_bind_eq_tsum core g true, probOutput_bind_eq_tsum core g' true]
  simp only [hg]
  have h1 : (∑' c, Pr[= c | core] * (1 / 2 + Pr[= true | g' c] / 2))
      = (∑' c, Pr[= c | core] * (1 / 2)) + ∑' c, Pr[= c | core] * (Pr[= true | g' c] / 2) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun c => by rw [mul_add]
  rw [h1]
  congr 1
  · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hcore, one_mul]
  · simp only [div_eq_mul_inv, ← mul_assoc]
    rw [ENNReal.tsum_mul_right]

private lemma verify_pure_true_of_mem_support
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (pk : SPK) (m : G ⊕ PQPK) (σ : S) (h : true ∈ support (P.sig.verify pk m σ)) :
    P.sig.verify pk m σ = pure true := by
  obtain ⟨b, hb⟩ := hverifyDet pk m σ
  rw [hb] at h
  obtain rfl := (mem_support_pure_iff' _ _).1 h
  exact hb

private lemma exp_per_env [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (st : A.State) (env : UAKE.Env (uakeInitiatorIdeal P msg hasOPK))
    (tk : RecipientIdentity F G SPK SSK S) :
    Pr[= true | do
      let a ← $ᵗ Bool
      let x ← (initiatorIdeal P).output env.challenge.state
      if x.join.isNone = true then
          UAKE.finalize A.toIdeal (st, env, tk)
            { K0 := x.join, challengeTr := env.challenge.transcript,
              oracleTrs := env.tSessions.map (fun
                s : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => s.transcript) } a none
        else
          if (!UAKE.isPingPong (proto := uakeInitiatorIdeal P msg hasOPK)
                  { K0 := x.join, challengeTr := env.challenge.transcript,
                    oracleTrs := env.tSessions.map (fun
                s : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => s.transcript) }) = true then
            pure true
          else do
            let K1 ← some <$> ($ᵗ K)
            UAKE.finalize A.toIdeal (st, env, tk)
                { K0 := x.join, challengeTr := env.challenge.transcript,
                  oracleTrs := env.tSessions.map (fun
                s : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => s.transcript) } a K1] =
    1 / 2 +
      Pr[= true | do
          let x ← (initiatorIdeal P).output env.challenge.state
          pure (x.join.isSome &&
            !UAKE.isPingPong (proto := uakeInitiatorIdeal P msg hasOPK)
                { K0 := x.join, challengeTr := env.challenge.transcript,
                  oracleTrs := env.tSessions.map (fun
                s : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => s.transcript) })] / 2 := by
  rcases hs : env.challenge.state with p0 | ctx | SK0
  · simp only [initiatorIdeal, pure_bind, Option.join_none, Option.isNone_none, if_true,
      Option.isSome_none, Bool.false_and, probOutput_pure, UAKE.finalize, ite_self]
    rw [show (if (true = false) then (1 : ℝ≥0∞) else 0) / 2 = 0 by simp, add_zero]
    generalize (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk)
      (A.toIdeal.post st none)).run env = pr
    exact probOutput_guess_half pr (fun e => UAKE.fullPingPong e
      { K0 := none, challengeTr := env.challenge.transcript,
        oracleTrs := List.map (fun x ↦ x.transcript) env.tSessions })
  · simp only [initiatorIdeal, pure_bind, Option.join_none, Option.isNone_none, if_true,
      Option.isSome_none, Bool.false_and, probOutput_pure, UAKE.finalize, ite_self]
    rw [show (if (true = false) then (1 : ℝ≥0∞) else 0) / 2 = 0 by simp, add_zero]
    generalize (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk)
      (A.toIdeal.post st none)).run env = pr
    exact probOutput_guess_half pr (fun e => UAKE.fullPingPong e
      { K0 := none, challengeTr := env.challenge.transcript,
        oracleTrs := List.map (fun x ↦ x.transcript) env.tSessions })
  · simp only [initiatorIdeal, bind_assoc, pure_bind, Option.join_some, Option.isNone_some,
      Option.isSome_some, Bool.false_eq_true, if_false, Bool.true_and, UAKE.isPingPong]
    generalize pingPong ((uakeInitiatorIdeal P msg hasOPK).rounds % 2 == 1)
        (List.map (fun t ↦ t.transcript) env.tSessions) env.challenge.transcript = PP
    cases PP
    · simp only [reduceIte, Bool.not_false]
      simp only [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul,
        probOutput_pure, reduceIte, one_div]
      exact (ENNReal.inv_two_add_inv_two).symm
    · simp only [Bool.not_true, reduceCtorEq, if_false]
      simp only [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul,
        probOutput_pure, reduceCtorEq, if_false]
      simp only [UAKE.finalize, bind_map_left]
      have hsome : ∀ (c : Bool) (u v : K),
          (if c = true then some u else some v) = some (if c = true then u else v) := by
        intro c u v; cases c <;> rfl
      simp only [hsome, UAKE.fullPingPong]
      generalize UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk = qi
      set postFn : K → ProbComp (Bool × UAKE.Env (uakeInitiatorIdeal P msg hasOPK)) :=
        fun key => (simulateQ qi (A.toIdeal.post st (some key))).run env with hpf
      simp only [show ∀ k, (simulateQ qi (A.toIdeal.post st (some k))).run env = postFn k
        from fun _ => rfl]
      clear_value postFn
      conv_rhs => rw [show (1 : ℝ≥0∞) / 2 + 0 / 2 = 1 / 2 by simp]
      have hg := finalize_pingPong_half (E := UAKE.Env (uakeInitiatorIdeal P msg hasOPK)) postFn
        (fun d => pingPong ((uakeInitiatorIdeal P msg hasOPK).rounds % 2 == 1)
          ((d.tSessions.filter
              (fun t : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => t.revealed)).map
              (fun t : UAKE.TSession (uakeInitiatorIdeal P msg hasOPK) => t.transcript))
          env.challenge.transcript)
      convert hg using 3

private lemma exp_eq_half_add_authBreak [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    Pr[= true | UAKE.Exp A.toIdeal] = 1 / 2 + idealAuthBreak P msg hasOPK A / 2 := by
  unfold UAKE.Exp idealAuthBreak
  refine probOutput_bind_half_add _ _ _ ?_ ?_
  · simp
  · rintro ⟨uk, tk⟩
    dsimp only
    have hCS : UAKE.challengeSession A.toIdeal uk tk = (do
        let p ← (simulateQ (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk)
                  (A.challenge uk none)).run ⟨0, ⟨Sum.inl uk, ⟨[]⟩⟩, false, []⟩
        let k0 ← (initiatorIdeal P).output p.2.challenge.state
        pure ((⟨k0.join, p.2.challenge.transcript, p.2.tSessions.map (·.transcript)⟩ :
          UAKE.ChallengeResult (uakeInitiatorIdeal P msg hasOPK)),
          (p.1, p.2, tk))) := by
      rfl
    simp only [hCS, bind_assoc, pure_bind]
    clear hCS
    rw [probOutput_bind_bind_swap]
    refine probOutput_bind_half_add _ _ _ (by simp) ?_
    rintro ⟨st, env⟩
    dsimp only
    exact exp_per_env P msg hasOPK A st env tk

private lemma probOutput_reorder4 {α β γ δ : Type}
    (ma : ProbComp α) (mb : ProbComp β) (mc : ProbComp γ) (md : ProbComp δ)
    (f : α → β → γ → δ → ProbComp Bool) :
    Pr[= true | do let a ← ma; let b ← mb; let c ← mc; let d ← md; f a b c d]
      = Pr[= true | do let c ← mc; let a ← ma; let b ← mb; let d ← md; f a b c d] := by
  rw [probOutput_bind_congr' ma true (fun a =>
        probOutput_bind_bind_swap mb mc (fun b c => md >>= fun d => f a b c d) true)]
  rw [probOutput_bind_bind_swap ma mc
        (fun a c => mb >>= fun b => md >>= fun d => f a b c d) true]

noncomputable def forgerChallenge [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    ProbComp ((UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S)) := do
  let ikA ← dhKeygen P.gen
  let ikB ← dhKeygen P.gen
  let sigkB ← P.sig.keygen
  let spkB ← dhKeygen P.gen
  (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle sigkB.1 sigkB.2)
    (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
        (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
      UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger
        ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, (sigkB.1, default), spkB, spkSigB⟩)).run

def authBreakPred [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S)) : Bool :=
  cl.1.1.K0.isSome && !UAKE.isPingPong cl.1.1

def bothQueriedPred [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S)) : Bool :=
  cl.2.wasQueriedWith (extractForgery true cl.1.2.2.1.challenge.transcript).1
      (extractForgery true cl.1.2.2.1.challenge.transcript).2 &&
    cl.2.wasQueriedWith (extractForgery false cl.1.2.2.1.challenge.transcript).1
      (extractForgery false cl.1.2.2.1.challenge.transcript).2

def forgerWin [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (pk : SPK) (g : Bool)
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S)) : ProbComp Bool := do
  let fs := extractForgery g cl.1.2.2.1.challenge.transcript
  let verified ← P.sig.verify pk fs.1 fs.2
  pure (!cl.2.wasQueriedWith fs.1 fs.2 && verified)

noncomputable def forgerChallengeWin [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (g : Bool) : ProbComp Bool := do
  let ikA ← dhKeygen P.gen
  let ikB ← dhKeygen P.gen
  let sigkB ← P.sig.keygen
  let spkB ← dhKeygen P.gen
  let cl ← (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle sigkB.1 sigkB.2)
    (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
        (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
      UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger
        ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, (sigkB.1, default), spkB, spkSigB⟩)).run
  forgerWin P msg hasOPK A sigkB.1 g cl

private lemma freshRun_le [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (pk : SPK)
    (rc : ProbComp ((UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S)))
    (hver : ∀ cl ∈ support rc, cl.1.1.K0.isSome = true → ∀ g,
      P.sig.verify pk (extractForgery g cl.1.2.2.1.challenge.transcript).1
        (extractForgery g cl.1.2.2.1.challenge.transcript).2 = pure true) :
    Pr[= true | rc >>= fun cl =>
        pure (authBreakPred P msg hasOPK A cl && !bothQueriedPred P msg hasOPK A cl)]
      ≤ Pr[= true | rc >>= fun cl => forgerWin P msg hasOPK A pk true cl]
        + Pr[= true | rc >>= fun cl => forgerWin P msg hasOPK A pk false cl] := by
  refine probOutput_bind_congr_le_add fun cl hcl => ?_
  rcases hab : (authBreakPred P msg hasOPK A cl && !bothQueriedPred P msg hasOPK A cl) with _ | _
  · simp
  · simp only [authBreakPred, bothQueriedPred, Bool.and_eq_true, Bool.not_eq_true'] at hab
    obtain ⟨⟨hK0, -⟩, hnb⟩ := hab
    simp only [forgerWin, hver cl hcl hK0, pure_bind, Bool.and_true, probOutput_pure]
    simp only [Bool.and_eq_false_iff] at hnb
    rcases hnb with h | h <;> simp [h]

private lemma idealAuthBreak_eq_authBreakPred [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    idealAuthBreak P msg hasOPK A =
      Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
        pure (authBreakPred P msg hasOPK A cl)] := by
  rw [idealAuthBreak_eq_forger P msg hasOPK A]
  simp only [forgerChallenge, authBreakPred, bind_assoc, bind_map_left]
  rfl

private lemma isQueryBoundP_liftM_probComp {α : Type} (oa : ProbComp α) :
    (liftM oa : OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α).IsQueryBoundP
      (· matches Sum.inr _) 0 := by
  rw [← OracleComp.liftComp_eq_liftM]
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [OracleComp.liftComp_pure]; trivial
  | query_bind t f ih =>
      simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map]
      erw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

private lemma isQueryBoundP_zero_bind {ι : Type} {spec' : OracleSpec ι} {α β : Type}
    {oa : OracleComp spec' α} {ob : α → OracleComp spec' β}
    {p : ι → Prop} [DecidablePred p]
    (h : oa.IsQueryBoundP p 0) (h' : ∀ x ∈ support oa, (ob x).IsQueryBoundP p 0) :
    (oa >>= ob).IsQueryBoundP p 0 :=
  isQueryBoundP_bind h h'

private lemma isQueryBoundP_stateT_liftM {ι : Type} {spec' : OracleSpec ι} {σ α : Type}
    {x : OracleComp spec' α} {p : ι → Prop} [DecidablePred p] {n : ℕ}
    (h : x.IsQueryBoundP p n) (s : σ) :
    ((liftM x : StateT σ (OracleComp spec') α) s).IsQueryBoundP p n :=
  (isQueryBoundP_bind (m := 0) h fun _ _ => isQueryBoundP_pure _ _ _ :
    (x >>= fun a => pure (a, s)).IsQueryBoundP p n)

private lemma isQueryBoundP_recipientForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (idn : RecipientIdentity F G SPK SSK S) :
    ((recipientForger (K := K) P hasOPK).init idn).IsQueryBoundP (· matches Sum.inr _) 1 := by
  simp only [recipientForger]
  refine isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftM_probComp _)
    fun opkB _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftM_probComp _)
    fun pqpkB _ => ?_
  refine isQueryBoundP_bind (n := 1) (m := 0) ?_ fun bundle _ => isQueryBoundP_pure _ _ _
  unfold publishForger
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun u => isQueryBoundP_pure _ _ _⟩

private lemma isQueryBoundP_recipientForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) :
    ((recipientForger (K := K) P hasOPK).step st w).IsQueryBoundP (· matches Sum.inr _) 0 := by
  rcases st with p | k <;> rcases w with b | im | c <;> simp only [recipientForger] <;>
    try exact isQueryBoundP_pure _ _ _
  refine isQueryBoundP_zero_bind (isQueryBoundP_liftM_probComp _) fun r _ => ?_
  rcases r with _ | ctx
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_zero_bind (isQueryBoundP_liftM_probComp _)
      fun c _ => isQueryBoundP_pure _ _ _

private lemma isQueryBoundP_recipientForger_output [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K) :
    ((recipientForger (K := K) P hasOPK).output st).IsQueryBoundP (· matches Sum.inr _) 0 := by
  rcases st with p | k <;> exact isQueryBoundP_pure _ _ _

private lemma isQueryBoundP_initiatorIdealForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) :
    ((initiatorIdealForger P).step st w).IsQueryBoundP (· matches Sum.inr _) 0 := by
  rcases st with p | ctx | k <;> rcases w with b | im | c <;> simp only [initiatorIdealForger] <;>
    try exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_zero_bind (isQueryBoundP_liftM_probComp _) fun r _ => ?_
    rcases r with _ | ⟨im', ctx'⟩ <;> exact isQueryBoundP_pure _ _ _
  · rcases hc : confirm P ctx c with _ | SK <;> exact isQueryBoundP_pure _ _ _

private lemma isQueryBoundP_initiatorIdealForger_output [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K) :
    ((initiatorIdealForger P).output st).IsQueryBoundP (· matches Sum.inr _) 0 := by
  rcases st with p | ctx | k
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_zero_bind (isQueryBoundP_liftM_probComp _)
      fun SK _ => isQueryBoundP_pure _ _ _

private lemma isQueryBoundP_opImpl_op [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK))
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    ((UAKE.opImpl (schemeForger P msg hasOPK) tk op).run s).IsQueryBoundP
      (· matches Sum.inr _) (if op matches .openT then 1 else 0) := by
  cases op with
  | openT =>
      simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact isQueryBoundP_bind (n := 1) (m := 0)
        (isQueryBoundP_stateT_liftM (isQueryBoundP_recipientForger_init P hasOPK tk) s)
        fun r _ => isQueryBoundP_pure _ _ _
  | stepT sid w =>
      simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind]
      cases s.tSessions[sid]? with
      | none => apply isQueryBoundP_pure
      | some tses =>
          rcases htk : tses.key with _ | k
          case some => simp only [htk]; apply isQueryBoundP_pure
          case none =>
            simp only [htk]
            simp only [StateT.run_bind]
            refine isQueryBoundP_zero_bind
              (isQueryBoundP_stateT_liftM
                (isQueryBoundP_recipientForger_step P hasOPK _ _) _) fun r _ => ?_
            rcases r with ⟨⟨st', w', done⟩ | st' | _, s'⟩
            · cases done
              · simp only [Bool.false_eq_true, if_false, StateT.run_bind,
                  StateT.run_set, StateT.run_pure, pure_bind]
                exact isQueryBoundP_zero_bind (isQueryBoundP_pure _ _ _)
                  fun key _ => isQueryBoundP_pure _ _ _
              · simp only [if_true, StateT.run_bind, StateT.run_set, StateT.run_pure,
                  pure_bind]
                exact isQueryBoundP_zero_bind
                  (isQueryBoundP_stateT_liftM
                    (isQueryBoundP_recipientForger_output P hasOPK _) _)
                  fun key _ => isQueryBoundP_pure _ _ _
            · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
              exact isQueryBoundP_zero_bind
                (isQueryBoundP_stateT_liftM
                  (isQueryBoundP_recipientForger_output P hasOPK _) _)
                fun key _ => isQueryBoundP_pure _ _ _
            · apply isQueryBoundP_pure
  | revealT sid =>
      simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind]
      cases s.tSessions[sid]? with
      | none => apply isQueryBoundP_pure
      | some tses =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
          apply isQueryBoundP_pure
  | stepChallenge w =>
      simp only [UAKE.opImpl, StateT.run_bind, StateT.run_get, pure_bind]
      cases hdone : s.challengeDone with
      | true =>
          simp only [if_true, StateT.run_pure]
          apply isQueryBoundP_pure
      | false =>
          simp only [Bool.false_eq_true, if_false, StateT.run_bind]
          refine isQueryBoundP_zero_bind
            (isQueryBoundP_stateT_liftM
              (isQueryBoundP_initiatorIdealForger_step P _ _) _) fun r _ => ?_
          rcases r with ⟨⟨st', w', done⟩ | st' | _, s'⟩ <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] <;>
            exact isQueryBoundP_pure _ _ _

private lemma isQueryBoundP_opImpl_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SPK SSK S)
    (t : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    ((UAKE.oracleImpl (schemeForger P msg hasOPK) tk t).run s).IsQueryBoundP
      (· matches Sum.inr _) (if t matches Sum.inr .openT then 1 else 0) := by
  cases t with
  | inl u =>
      simp only [UAKE.oracleImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        HasQuery.toQueryImpl_apply]
      erw [StateT.run_monadLift]
      exact isQueryBoundP_zero_bind (isQueryBoundP_liftM_probComp _)
        fun a _ => isQueryBoundP_pure _ _ _
  | inr op =>
      cases op with
      | openT => exact isQueryBoundP_opImpl_op P msg hasOPK tk .openT s
      | stepT sid w => exact isQueryBoundP_opImpl_op P msg hasOPK tk (.stepT sid w) s
      | revealT sid => exact isQueryBoundP_opImpl_op P msg hasOPK tk (.revealT sid) s
      | stepChallenge w =>
          exact isQueryBoundP_opImpl_op P msg hasOPK tk (.stepChallenge w) s

private lemma snd_run_eq_empty_of_noInr {α : Type}
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (X : OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) α)
    (hX : X.IsQueryBoundP (· matches Sum.inr _) 0) :
    ∀ z ∈ support ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
        (m := ProbComp)).liftTarget (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp)
        + P.sig.signingOracle pk sk) X).run),
      z.2 = (∅ : QueryLog ((G ⊕ PQPK) →ₒ S)) := by
  revert hX
  induction X using OracleComp.inductionOn with
  | pure x =>
      intro _ z hz
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hz
      rw [hz]
  | query_bind q f ih =>
      intro hX z hz
      rw [isQueryBoundP_query_bind_iff] at hX
      have h1 := hX.1.resolve_right (by omega)
      rcases q with u | v
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, WriterT.run_bind'] at hz
        obtain ⟨pr, hpr, hz2⟩ := (mem_support_bind_iff _ _ _).1 hz
        obtain ⟨z', hz', heq⟩ := mem_support_map_peel _ _ hz2
        have hw1 : pr.2 = ∅ := by
          simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
            HasQuery.toQueryImpl_apply] at hpr
          erw [WriterT.run_liftM] at hpr
          obtain ⟨a, -, heq'⟩ := mem_support_map_peel _ _ hpr
          rw [heq']
        have hz'2 := ih pr.1 (by simpa using hX.2 pr.1) z' hz'
        rw [heq]
        simp [Prod.map, hw1, hz'2]
      · simp at h1

private lemma isQueryBoundP_challengeSession [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg) (tk : RecipientIdentity F G SPK SSK S)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (hA : A.OpensAtMost 0) :
    (UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk tk).IsQueryBoundP
      (· matches Sum.inr _) 0 := by
  unfold UAKE.challengeSession
  refine isQueryBoundP_zero_bind ?_ fun u0 _ => ?_
  · apply isQueryBoundP_pure
  · refine isQueryBoundP_zero_bind ?_ fun se _ => ?_
    · refine IsQueryBoundP.simulateQ_run_StateT_of_step (hA.1 uk _) (fun t s' => ?_) _
      rcases t with u | op
      · exact isQueryBoundP_opImpl_step P msg hasOPK tk (Sum.inl u) s'
      · cases op with
        | openT => exact isQueryBoundP_opImpl_op P msg hasOPK tk .openT s'
        | stepT sid w => exact isQueryBoundP_opImpl_op P msg hasOPK tk (.stepT sid w) s'
        | revealT sid => exact isQueryBoundP_opImpl_op P msg hasOPK tk (.revealT sid) s'
        | stepChallenge w =>
            exact isQueryBoundP_opImpl_op P msg hasOPK tk (.stepChallenge w) s'
    · exact isQueryBoundP_zero_bind (isQueryBoundP_initiatorIdealForger_output P _)
        fun k0 _ => isQueryBoundP_pure _ _ _

private lemma forgerChallenge_log_singleton [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (hq0 : A.OpensAtMost 0) :
    ∀ cl ∈ support (forgerChallenge P msg hasOPK A),
      ∃ (g : G) (σ : S), cl.2 = [⟨Sum.inl g, σ⟩] := by
  intro cl hcl
  simp only [forgerChallenge] at hcl
  rw [mem_support_bind_iff] at hcl
  obtain ⟨ikA, -, hcl⟩ := hcl
  rw [mem_support_bind_iff] at hcl
  obtain ⟨ikB, -, hcl⟩ := hcl
  rw [mem_support_bind_iff] at hcl
  obtain ⟨sigkB, -, hcl⟩ := hcl
  rw [mem_support_bind_iff] at hcl
  obtain ⟨spkB, -, hcl⟩ := hcl
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, WriterT.run_bind'] at hcl
  obtain ⟨pr, hpr, hcl2⟩ := (mem_support_bind_iff _ _ _).1 hcl
  obtain ⟨z', hz', heq⟩ := mem_support_map_peel _ _ hcl2
  have hpr' : pr ∈ support
      ((P.sig.signingOracle sigkB.1 sigkB.2 (EncodeEC spkB.1)).run) := hpr
  rw [run_signingOracle] at hpr'
  obtain ⟨σ, -, hprσ⟩ := mem_support_map_peel _ _ hpr'
  have hz'2 : z'.2 = ∅ := snd_run_eq_empty_of_noInr P sigkB.1 sigkB.2 _
    (isQueryBoundP_challengeSession P msg hasOPK ⟨ikA, ikB.1, sigkB.1, msg⟩
      ⟨ikB, (sigkB.1, default), spkB, pr.1⟩ A hq0) z' hz'
  refine ⟨spkB.1, σ, ?_⟩
  rw [heq, hprσ]
  simp [Prod.map, hz'2, EncodeEC, List.append_nil]

private lemma extractForgery_true_kem [Inhabited G] [Inhabited S]
    (tr : Transcript (Message G PQPK CT S C IdC IdK))
    (hex : ∃ e ∈ tr.entries, ∃ b, e.1 = Message.bundle b) :
    ∃ (b : PreKeyBundle G PQPK S IdC IdK),
      extractForgery true tr = (EncodeKEM b.pqpkB.1, b.pqpkSigB) := by
  unfold extractForgery
  split
  · next fs hfs =>
      obtain ⟨e, he, hge⟩ := List.exists_of_findSome?_eq_some hfs
      cases he1 : e.1 with
      | bundle b =>
        rw [he1] at hge
        injection hge with hge'
        exact ⟨b, by rw [← hge']; simp⟩
      | initial im => rw [he1] at hge; simp at hge
      | confirmation c => rw [he1] at hge; simp at hge
  · next hfs =>
      exfalso
      obtain ⟨e, he, b, hb⟩ := hex
      rw [List.findSome?_eq_none_iff] at hfs
      have hcontra := hfs e he
      rw [hb] at hcontra
      simp at hcontra

private lemma schemeForger_K0_bundle_queryBind [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SPK Msg)
    (ikB spkB : G × F) (pk : SPK) (sk : SSK)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (cl : (UAKE.ChallengeResult (schemeForger P msg hasOPK) ×
        (A.State × UAKE.Env (schemeForger P msg hasOPK) × RecipientIdentity F G SPK SSK S)) ×
      QueryLog ((G ⊕ PQPK) →ₒ S))
    (hcl : cl ∈ support
      ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
            (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
          UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
            ⟨ikB, (pk, default), spkB, spkSigB⟩)).run))
    (hK0 : cl.1.1.K0.isSome = true) :
    ∃ e ∈ cl.1.2.2.1.challenge.transcript.entries, ∃ b, e.1 = Message.bundle b := by
  have h1 : cl.1 ∈ support (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec)
      (m := ProbComp)).liftTarget
      (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
    (liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
        (Sum.inr (EncodeEC spkB.1))) >>= fun spkSigB =>
      UAKE.challengeSession (proto := schemeForger P msg hasOPK) A.toForger uk
        ⟨ikB, (pk, default), spkB, spkSigB⟩)).run) :=
    (support_map _ _).ge (Set.mem_image_of_mem _ hcl)
  rw [fst_run_sim_queryBind] at h1
  obtain ⟨σ, hσ, h1⟩ := (mem_support_bind_iff _ _ _).1 h1
  exact schemeForger_K0_bundle_default P msg hasOPK uk
    ⟨ikB, (pk, default), spkB, σ⟩ pk sk A cl.1 h1 hK0

private lemma idealAuthBreak_partition [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    idealAuthBreak P msg hasOPK A =
      Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
          pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)]
      + Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
          pure (authBreakPred P msg hasOPK A cl && !bothQueriedPred P msg hasOPK A cl)] := by
  rw [idealAuthBreak_eq_authBreakPred P msg hasOPK A]
  exact probOutput_true_and_partition (forgerChallenge P msg hasOPK A)
    (authBreakPred P msg hasOPK A) (bothQueriedPred P msg hasOPK A)

private lemma two_mul_uniformBool (f : Bool → ProbComp Bool) :
    2 * Pr[= true | do let g ← ($ᵗ Bool : ProbComp _); f g]
      = Pr[= true | f true] + Pr[= true | f false] := by
  rw [probOutput_bind_uniformBool, mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

private lemma two_mul_bind_lift {α : Type} (m : ProbComp α)
    (P Q R : α → ProbComp Bool)
    (h : ∀ a, 2 * Pr[= true | P a] = Pr[= true | Q a] + Pr[= true | R a]) :
    2 * Pr[= true | m >>= P] = Pr[= true | m >>= Q] + Pr[= true | m >>= R] := by
  simp only [probOutput_bind_eq_tsum]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by rw [← mul_add, ← h a]; ring

private lemma two_mul_sigForger_strongAdvantage_eq [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    2 * (sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp
      = Pr[= true | forgerChallengeWin P msg hasOPK A true]
        + Pr[= true | forgerChallengeWin P msg hasOPK A false] := by
  rw [sigForger_strongAdvantage_eq P msg hasOPK A,
    ← probOutput_reorder4 (dhKeygen P.gen) (dhKeygen P.gen) (P.sig.keygen) (dhKeygen P.gen)]
  simp only [forgerChallengeWin, forgerWin]
  refine two_mul_bind_lift _ _ _ _ (fun ikA => ?_)
  refine two_mul_bind_lift _ _ _ _ (fun ikB => ?_)
  refine two_mul_bind_lift _ _ _ _ (fun sigkB => ?_)
  refine two_mul_bind_lift _ _ _ _ (fun spkB => ?_)
  exact two_mul_uniformBool _

private lemma idealHop_bound [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εaead : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead) :
    |(Pr[= true | UAKE.Exp A.toIdeal]).toReal - 1 / 2| ≤ εsig + q * εaead := by
  haveI : Inhabited G := ⟨0⟩
  have hdecomp : Pr[= true | UAKE.Exp A.toIdeal]
      = 1 / 2 + idealAuthBreak P msg hasOPK A / 2 :=
    exp_eq_half_add_authBreak P msg hasOPK A
  have hauth : (idealAuthBreak P msg hasOPK A).toReal ≤ 2 * (εsig + q * εaead) := by
    have hbundle : (idealAuthBreak P msg hasOPK A).toReal
        ≤ 2 * ((sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp).toReal
          + 2 * (q * εaead) := by
      have hfresh : Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
            pure (authBreakPred P msg hasOPK A cl && !bothQueriedPred P msg hasOPK A cl)]
          ≤ 2 * (sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp := by
        have hbridge : 2 * (sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp
            = Pr[= true | forgerChallengeWin P msg hasOPK A true]
              + Pr[= true | forgerChallengeWin P msg hasOPK A false] :=
          two_mul_sigForger_strongAdvantage_eq P msg hasOPK A
        rw [hbridge]
        simp only [forgerChallenge, forgerChallengeWin, bind_assoc]
        refine probOutput_bind_congr_le_add fun ikA _ => ?_
        refine probOutput_bind_congr_le_add fun ikB _ => ?_
        refine probOutput_bind_congr_le_add fun sigkB _ => ?_
        refine probOutput_bind_congr_le_add fun spkB _ => ?_
        exact freshRun_le P msg hasOPK A sigkB.1 _ (fun cl hcl hK0 g =>
          verify_pure_true_of_mem_support P hverifyDet _ _ _
            (schemeForger_authBreak_verified_queryBind P msg hasOPK g _ ikB spkB
              sigkB.1 sigkB.2 A cl hcl hK0))
      have hstale : (Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
            pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)]).toReal
          ≤ 2 * (q * εaead) := by
        have hred : Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
              pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)]
            ≤ Pr[= true | AEAD.INT_CTXT_D_Game P.aead (aeadForger P msg hasOPK A)] := by
          have hmono : Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
                pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)]
              ≤ Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
                pure (authBreakPred P msg hasOPK A cl)] := by
            refine probOutput_bind_mono fun cl _ => ?_
            rcases hb : (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)
              with _ | _
            · simp
            · simp only [Bool.and_eq_true] at hb
              simp [hb.1]
          rw [← idealAuthBreak_eq_authBreakPred P msg hasOPK A] at hmono
          refine le_trans hmono ?_
          have hpp : idealAuthBreak P msg hasOPK A
              ≤ Pr[= true | do
                  let x ← (uakeInitiatorIdeal P msg hasOPK).setup
                  let r ← UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK)
                    A.toIdeal x.1 x.2
                  pure r.1.K0.isSome] := by
            unfold idealAuthBreak
            refine probOutput_bind_mono fun x _ => probOutput_bind_mono fun r _ => ?_
            simp only [probOutput_pure]
            cases r.1.K0.isSome <;> cases UAKE.isPingPong r.1 <;> simp
          refine le_trans hpp ?_
          have hA : Pr[= true | do
                let x ← (uakeInitiatorIdeal P msg hasOPK).setup
                let r ← UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK)
                  A.toIdeal x.1 x.2
                pure r.1.K0.isSome]
              = Pr[= true | do
                let k ← ($ᵗ K : ProbComp K)
                let x ← (uakeInitiatorIdealFixed P msg hasOPK k).setup
                let r ← UAKE.challengeSession (proto := uakeInitiatorIdealFixed P msg hasOPK k)
                  (A.toFixed k) x.1 x.2
                pure r.1.K0.isSome] := by
            exact ideal_game_eq_fixed_avg P msg hasOPK A
          have hB : ∀ k : K, Pr[= true | do
                let x ← (uakeInitiatorIdealFixed P msg hasOPK k).setup
                let r ← UAKE.challengeSession (proto := uakeInitiatorIdealFixed P msg hasOPK k)
                  (A.toFixed k) x.1 x.2
                pure r.1.K0.isSome]
              ≤ Pr[= true | do
                let z ← (simulateQ (AEAD.withUnif (AEAD.ctxtDecImpl P.aead k))
                  (aeadForger P msg hasOPK A).run).run ([], false)
                pure z.2.2] := by
            exact fixed_game_le_flag_game P msg hasOPK A
          rw [hA]
          unfold AEAD.INT_CTXT_D_Game
          exact probOutput_bind_mono fun k _ => hB k
        have hq1 : q = 0 → Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
              pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)] = 0 := by
          intro hq0
          rw [probOutput_bind_eq_tsum, ENNReal.tsum_eq_zero]
          intro cl
          by_cases hcl : cl ∈ support (forgerChallenge P msg hasOPK A)
          · rw [probOutput_pure]
            have hf : (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)
                = false := by
              rcases hab : authBreakPred P msg hasOPK A cl with _ | _
              · simp
              · have hbq : bothQueriedPred P msg hasOPK A cl = false := by
                  have hK0 : cl.1.1.K0.isSome = true := by
                    simp only [authBreakPred, Bool.and_eq_true] at hab
                    exact hab.1
                  obtain ⟨g, σ, hlog⟩ :=
                    forgerChallenge_log_singleton P msg hasOPK A (hq0 ▸ hq) cl hcl
                  simp only [forgerChallenge] at hcl
                  rw [mem_support_bind_iff] at hcl
                  obtain ⟨ikA, -, hcl⟩ := hcl
                  rw [mem_support_bind_iff] at hcl
                  obtain ⟨ikB, -, hcl⟩ := hcl
                  rw [mem_support_bind_iff] at hcl
                  obtain ⟨sigkB, -, hcl⟩ := hcl
                  rw [mem_support_bind_iff] at hcl
                  obtain ⟨spkB, -, hcl⟩ := hcl
                  have hex := schemeForger_K0_bundle_queryBind P msg hasOPK
                    ⟨ikA, ikB.1, sigkB.1, msg⟩ ikB spkB sigkB.1 sigkB.2 A cl hcl hK0
                  obtain ⟨b, hb⟩ :=
                    extractForgery_true_kem cl.1.2.2.1.challenge.transcript hex
                  simp only [bothQueriedPred, hb, hlog, EncodeKEM, QueryLog.wasQueriedWith]
                  simp only [List.mem_cons, Sigma.mk.injEq, heq_eq_eq, List.not_mem_nil,
                    or_false, Bool.decide_and, Bool.and_eq_false_imp, Bool.and_eq_true,
                    decide_eq_true_eq, decide_eq_false_iff_not, and_imp]
                  intro h1
                  rw [hb] at h1
                  simp [EncodeKEM] at h1
                simp [hbq]
            simp [hf]
          · rw [probOutput_eq_zero_of_not_mem_support hcl, zero_mul]
        have haead' : AEAD.INT_CTXT_D_Advantage P.aead (aeadForger P msg hasOPK A) ≤ εaead :=
          haead _
        rcases Nat.eq_zero_or_pos q with hq0 | hqpos
        · subst hq0; rw [hq1 rfl]; simp
        · have hev : (Pr[= true | (forgerChallenge P msg hasOPK A) >>= fun cl =>
                pure (authBreakPred P msg hasOPK A cl && bothQueriedPred P msg hasOPK A cl)]).toReal
              ≤ AEAD.INT_CTXT_D_Advantage P.aead (aeadForger P msg hasOPK A) :=
            (ENNReal.toReal_le_toReal probOutput_ne_top probOutput_ne_top).mpr hred
          have hε0 : (0 : ℝ) ≤ εaead := le_trans ENNReal.toReal_nonneg haead'
          have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
          nlinarith [le_trans hev haead', hε0, hq1R]
      have hadvne : (sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp ≠ ⊤ := by
        rw [sigForger_strongAdvantage_eq P msg hasOPK A]; exact probOutput_ne_top
      have hfr := (ENNReal.toReal_le_toReal probOutput_ne_top
        (ENNReal.mul_ne_top (by norm_num) hadvne)).mpr hfresh
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hfr
      rw [idealAuthBreak_partition P msg hasOPK A,
        ENNReal.toReal_add probOutput_ne_top probOutput_ne_top]
      linarith [hstale, hfr]
    calc (idealAuthBreak P msg hasOPK A).toReal
        ≤ 2 * ((sigForger P msg hasOPK A).strongAdvantage ProbCompRuntime.probComp).toReal
            + 2 * (q * εaead) := hbundle
      _ ≤ 2 * εsig + 2 * (q * εaead) := by
          gcongr
          exact hsig (sigForger P msg hasOPK A)
      _ = 2 * (εsig + q * εaead) := by ring
  have hne : idealAuthBreak P msg hasOPK A ≠ ⊤ := probOutput_ne_top
  rw [hdecomp, ENNReal.toReal_add (by simp) (by simp [ENNReal.div_eq_top, hne]),
    ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num
  rw [abs_of_nonneg (by positivity)]
  linarith [hauth]

theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS]
    [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
      just EUF-CMA. This is required to avoid (harmless) LS'17-style
      "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εkem + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (KEM IND-CCA on the challenge KEM key, then `KdfPRF`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εkem + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): with the challenge key uniform, confidentiality
  -- is exactly 1/2, and a non-ping-pong completion needs a forged prekey signature (εsig) or a
  -- forged AEAD confirmation under a uniform key (q·εaead).
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead :=
    idealHop_bound P msg hasOPK hidKEM A q hq εsig εaead hverifyDet hsig haead
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εkem + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εkem + εaead + εkdf) := by ring

theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
      just EUF-CMA. This is required to avoid (harmless) LS'17-style
      "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- MODEL SIMPLIFICATION: We model the KDF as a PRF. Since we key our KDF
      using DH group elements, we must also assume that the KDF is secure when
      keyed with one of these, rather than a random bit string. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (DDH/GapDH on the challenge DH share, then `KdfPRFDH`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εddh + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): identical to the pq case — with the challenge key
  -- uniform, confidentiality is 1/2 and a non-ping-pong completion needs a forged signature or a
  -- forged AEAD confirmation.
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead :=
    idealHop_bound P msg hasOPK hidKEM A q hq εsig εaead hverifyDet hsig haead
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εddh + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εddh + εaead + εkdf) := by ring

end PQXDH
