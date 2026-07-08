/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import PQXDH.AKE.UAKE.Basic
import PQXDH.ToMathlib
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleSpec OracleComp AKE
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
    Party ProbComp (InitiatorParameters F G SS SPK Msg K)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
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
    Party ProbComp (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G SS PQPK PQSK SPK SSK K ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G SS PQPK PQSK SPK SSK K :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB,
        opkB := opkB, pqpkB := pqpkB, kdf := idn.kdf }
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
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SS SPK Msg K)
      (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (RecipientIdentity F G SS SPK SSK K)
      (InitiatorParameters F G SS SPK Msg K)
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
    {p : InitiatorParameters F G SS SPK Msg K} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {r : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSig),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSig),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
    ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
    ∃ ctxt ∈ support (P.aead.encrypt
        (p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
          Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.1
        (p.ikA.1, p.ikB, bundle.pqpkB.1) p.msg),
      r = some (⟨p.ikA.1, ekA.1, cs.1, bundle.spkB.2, bundle.pqpkB.2,
          Option.map Prod.snd bundle.opkB, ctxt⟩,
        ⟨(p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).1,
          (p.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
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
    {p : RecipientParameters F G SS PQPK PQSK SPK SSK K}
    {im : InitialMessage G CT C IdC IdK} {ss : SS} {m₀ : Msg}
    {r : Option (SessionContext G PQPK Msg K)}
    (hid₁ : im.idSPK = P.idEC p.spkB.1)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = Option.map (fun opk => P.idEC opk.1) p.opkB)
    (hdec : ∀ o ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct), o = some ss)
    (hdecr : P.aead.decrypt
        (p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.1
        (im.ikA, p.ikB.1, p.pqpkB.1) im.ctxt = some m₀)
    (hr : r ∈ support (accept P p im)) :
    r = some ⟨(p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).1,
      (p.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
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
    (msg : Msg) {kdf : KeyMaterial G SS → K × K × K}
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.1, sigkB.1, msg, kdf⟩ ⟨ikB, sigkB, spkB, kdf⟩ (3 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, rfl⟩ := hbundle
  simp only [InitResult.opening, InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₁ hb)
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
    (msg : Msg) {kdf : KeyMaterial G SS → K × K × K}
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    {uOut tOut : Option (Option K)}
    (hrun : (uOut, tOut) ∈ support (runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, kdf⟩ ⟨ikA, ikB.1, sigkB.1, msg, kdf⟩ (4 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := by
  simp only [runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, rfl⟩ := hbundle
  simp only [InitResult.opening, InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₁ hb)
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
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact HasEvalPMF.probFailure_eq_zero _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨kdf, ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hrun

theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact HasEvalPMF.probFailure_eq_zero _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff, support_uniformSample,
    Set.mem_univ, true_and, support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨kdf, ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, rfl⟩, hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB hrun

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
  simp only [UAKE.finalize, hKb, ite_self]
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
  rw [← HasEvalPMF.tsum_probOutput_eq_one
    ((simulateQ (withUnif (UAKE.oracleImpl proto tk)) (A.post aSt K1)).run env)]
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

def kdfRoRExp [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS))
    (D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool) (b : Bool) :
    ProbComp Bool := do
  let kdf ← $ᵗ (KeyMaterial G SS → K × K × K)
  let x ← km
  let ks ← if b then pure (kdf x) else do let sk ← $ᵗ K; pure (sk, (kdf x).2)
  D kdf ks

def KdfHidesInput [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS)) (ε : ℝ) : Prop :=
  ∀ D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool,
    |(Pr[= true | kdfRoRExp km D true]).toReal -
      (Pr[= true | kdfRoRExp km D false]).toReal| ≤ ε

private lemma probOutput_bind_if_true_uniformBool {α : Type} (m : ProbComp α) (c : α → Bool) :
    Pr[= true | do let x ← m; if c x then (pure true : ProbComp Bool) else $ᵗ Bool] =
      1 / 2 + Pr[= true | do let x ← m; pure (c x)] / 2 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  conv_rhs => rw [show (1 : ℝ≥0∞) / 2 = (∑' x, Pr[= x | m]) / 2 from by
    rw [HasEvalPMF.tsum_probOutput_eq_one]]
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
    (p : InitiatorParameters F G SS SPK Msg K)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSig
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSig
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, SS) ← P.pqkem.encaps bundle.pqpkB.1
  let DH1 := DH p.ikA.2 bundle.spkB.1
  let DH2 := DH ekA.2 bundle.ikB
  let DH3 := DH ekA.2 bundle.spkB.1
  let DH4 := bundle.opkB.map fun opk => DH ekA.2 opk.1
  let (_SK, KA, KB) := p.kdf (DH1, DH2, DH3, DH4, SS)
  let SK ← $ᵗ K
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1, ekA := ekA.1, ct := CT, idSPK := bundle.spkB.2,
                 idPQPK := bundle.pqpkB.2, idOPK := bundle.opkB.map Prod.snd, ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

def initiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SS SPK Msg K)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
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
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def uakeInitiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SS SPK Msg K)
      (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdeal P
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toIdeal
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
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
    (p : RecipientParameters F G SS PQPK PQSK SPK SSK K) :
    OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)) (PreKeyBundle G PQPK S IdC IdK) := do
  let spkSig ← liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
    (Sum.inr (EncodeEC p.spkB.1)))
  let pqpkSig ← liftM (OracleSpec.query (spec := unifSpec + ((G ⊕ PQPK) →ₒ S))
    (Sum.inr (EncodeKEM p.pqpkB.1)))
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSig := spkSig
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSig := pqpkSig
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

def recipientForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party (OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S)))
      (RecipientIdentity F G SS SPK SSK K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G SS PQPK PQSK SPK SSK K ⊕ K
  init := fun idn => do
    let opkB ← liftM (genOPK P.gen hasOPK)
    let pqpkB ← liftM P.pqkem.keygen
    let p : RecipientParameters F G SS PQPK PQSK SPK SSK K :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB,
        opkB := opkB, pqpkB := pqpkB, kdf := idn.kdf }
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
    (p : RecipientParameters F G SS PQPK PQSK SPK SSK K) (pk : SPK) (sk : SSK) :
    simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      (publishForger P p) =
    (do
      let spkSig ← P.sig.signingOracle pk sk (EncodeEC p.spkB.1)
      let pqpkSig ← P.sig.signingOracle pk sk (EncodeKEM p.pqpkB.1)
      pure { ikB := p.ikB.1
             spkB := (p.spkB.1, P.idEC p.spkB.1)
             spkSig := spkSig
             pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
             pqpkSig := pqpkSig
             opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }) := by
  unfold publishForger
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  rfl

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
  simp [WriterT.run, WriterT.mk, Functor.map_map, Function.comp]

private lemma fst_run_signingOracle
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (pk : SPK) (sk : SSK)
    (msg : G ⊕ PQPK) :
    Prod.fst <$> (P.sig.signingOracle pk sk msg).run = P.sig.sign pk sk msg := by
  have h := QueryImpl.fst_map_run_withLogging (m := ProbComp) (spec := (G ⊕ PQPK) →ₒ S)
    (fun m => P.sig.sign pk sk m)
    (liftM (OracleSpec.query (spec := (G ⊕ PQPK) →ₒ S) msg))
  simpa [SignatureAlg.signingOracle, simulateQ_spec_query] using h

private lemma fst_run_recipientForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (idn : RecipientIdentity F G SS SPK SSK K) (pk : SPK) (sk : SSK)
    (hsig : idn.sigkB = (pk, sk)) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((recipientForger P hasOPK).init idn)).run =
    (recipient P hasOPK).init idn := by
  simp only [recipientForger, recipient, publish, simulateQ_bind, simulateQ_sigImpl_liftM,
    simulateQ_publishForger, simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
    fst_run_liftM, fst_run_signingOracle, hsig]

private lemma fst_run_recipientForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (st : RecipientParameters F G SS PQPK PQSK SPK SSK K ⊕ K)
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
    (st : RecipientParameters F G SS PQPK PQSK SPK SSK K ⊕ K) (pk : SPK) (sk : SSK) :
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
      (InitiatorParameters F G SS SPK Msg K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
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
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

private lemma fst_run_initiatorIdealForger_init [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SS SPK Msg K) (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((initiatorIdealForger P).init p)).run =
    (initiatorIdeal P).init p := by
  simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']

private lemma fst_run_initiatorIdealForger_step [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K)
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
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K)
    (pk : SPK) (sk : SSK) :
    Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
      ((initiatorIdealForger P).output st)).run =
    (initiatorIdeal P).output st := by
  rcases st with p | ctx | SK <;>
    simp only [initiatorIdealForger, initiatorIdeal, simulateQ_pure, WriterT.fst_map_run_pure']

def schemeForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme (OracleComp (unifSpec + ((G ⊕ PQPK) →ₒ S))) K
      (InitiatorParameters F G SS SPK Msg K) (RecipientIdentity F G SS SPK SSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := liftM (setup P msg)
  U := initiatorIdealForger P
  T := recipientForger P hasOPK

def _root_.AKE.UAKE.Adversary.toForger
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (schemeForger P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

def envFI [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (e : UAKE.Env (schemeForger P msg hasOPK)) : UAKE.Env (uakeInitiatorIdeal P msg hasOPK) :=
  { clock := e.clock
    challenge := e.challenge
    challengeDone := e.challengeDone
    tSessions := e.tSessions.map fun t => ⟨t.state, t.transcript, t.key, t.revealed⟩ }

def crFI [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (cr : UAKE.ChallengeResult (schemeForger P msg hasOPK)) :
    UAKE.ChallengeResult (uakeInitiatorIdeal P msg hasOPK) :=
  { K0 := cr.K0, challengeTr := cr.challengeTr, oracleTrs := cr.oracleTrs }

private lemma schemeForger_T [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeForger P msg hasOPK).T = recipientForger P hasOPK := rfl

private lemma uakeInitiatorIdeal_T [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).T = recipient P hasOPK := rfl

private lemma schemeForger_U [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (schemeForger P msg hasOPK).U = initiatorIdealForger P := rfl

private lemma uakeInitiatorIdeal_U [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    (uakeInitiatorIdeal P msg hasOPK).U = initiatorIdeal P := rfl

private lemma fst_run_oracleImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SS SPK SSK K) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (op : UAKE.Op (Message G PQPK CT S C IdC IdK)) (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((UAKE.oracleImpl (schemeForger P msg hasOPK) tk op).run s)).run) =
    (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk op).run (envFI P msg hasOPK s) := by
  cases op with
  | revealT sid =>
    cases hs : s.tSessions[sid]? <;>
      simp [UAKE.oracleImpl, envFI, hs, List.getElem?_map, List.map_set, simulateQ_pure,
        WriterT.fst_map_run_pure']
  | openT =>
    simp only [UAKE.oracleImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_modifyGet, StateT.run_map, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, bind_map_left, schemeForger_T, uakeInitiatorIdeal_T,
      simulateQ_bind, simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
      fst_run_recipientForger_init _ _ _ _ _ hsig, map_bind, map_pure]
    refine bind_congr fun r => ?_
    simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
      Prod.map_apply, id_eq, envFI]
    cases r <;>
      exact congrArg pure (Prod.ext (Prod.ext (List.length_map _).symm rfl)
        (by simp [List.map_append]))
  | stepT sid w =>
    simp only [UAKE.oracleImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_modifyGet, StateT.run_map, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, bind_map_left, schemeForger_T, uakeInitiatorIdeal_T,
      envFI, List.getElem?_map]
    cases hs : s.tSessions[sid]? with
    | none => simp [hs, envFI, Prod.map]
    | some t =>
      cases hk : t.key with
      | some k => simp [hs, hk, envFI, Prod.map]
      | none =>
        simp only [hs, hk, Option.map_some, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
          StateT.run_set, StateT.run_modifyGet, StateT.run_map, StateT.run_pure, monadLift_self,
          bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
          WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
          fst_run_recipientForger_step _ _ _ _ pk sk, map_bind, map_pure]
        refine bind_congr fun sr => ?_
        cases sr with
        | reject =>
          simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
            Prod.map_apply, id_eq, envFI]
        | acceptAndSend st' w' done =>
          cases done with
          | false =>
            simp only [reduceCtorEq, reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
              StateT.run_map, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
              WriterT.fst_map_run_bind', WriterT.fst_map_run_pure', map_bind, map_pure]
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
          | true =>
            simp only [reduceCtorEq, reduceIte, StateT.run_bind, StateT.run_monadLift,
              StateT.run_set, StateT.run_pure, StateT.run_map, monadLift_self, bind_assoc, pure_bind,
              bind_map_left, simulateQ_bind, simulateQ_pure, WriterT.fst_map_run_bind',
              WriterT.fst_map_run_pure', fst_run_recipientForger_output _ _ _ pk sk, map_bind,
              map_pure]
            refine bind_congr fun key => ?_
            exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
        | complete st' =>
          simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
            StateT.run_map, monadLift_self, bind_assoc, pure_bind, bind_map_left, simulateQ_bind,
            simulateQ_pure, WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
            fst_run_recipientForger_output _ _ _ pk sk, map_bind, map_pure]
          refine bind_congr fun key => ?_
          exact congrArg pure (Prod.ext rfl (by simp [List.map_set, envFI]))
  | stepChallenge w =>
    simp only [UAKE.oracleImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
      StateT.run_set, StateT.run_modifyGet, StateT.run_map, StateT.run_pure, monadLift_self,
      bind_assoc, pure_bind, bind_map_left, schemeForger_U, uakeInitiatorIdeal_U, envFI]
    split
    · simp only [StateT.run_pure, simulateQ_pure, WriterT.fst_map_run_pure', map_pure,
        Prod.map_apply, id_eq, envFI]
    · simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_map, StateT.run_pure,
        monadLift_self, bind_assoc, pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
        WriterT.fst_map_run_bind', WriterT.fst_map_run_pure',
        fst_run_initiatorIdealForger_step _ _ _ pk sk, map_bind, map_pure]
      refine bind_congr fun sr => ?_
      cases sr <;>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, StateT.run_map, pure_bind,
          bind_assoc, simulateQ_bind, simulateQ_pure, WriterT.fst_map_run_bind',
          WriterT.fst_map_run_pure', map_bind, map_pure, Prod.map_apply, id_eq, envFI] <;> rfl

private lemma fst_run_withUnif_query [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SS SPK SSK K) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    (q : (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((withUnif (UAKE.oracleImpl (schemeForger P msg hasOPK) tk) q).run s)).run) =
    (withUnif (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk) q).run
      (envFI P msg hasOPK s) := by
  cases q with
  | inr op =>
    simp only [withUnif, QueryImpl.add_apply_inr]
    exact fst_run_oracleImpl P msg hasOPK tk pk sk hsig op s
  | inl u =>
    simp [withUnif, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      HasQuery.toQueryImpl_apply, StateT.run_monadLift, simulateQ_map, simulateQ_sigImpl_liftM,
      Functor.map_map, envFI]

private lemma fst_run_withUnif_oracleImpl [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SS SPK SSK K) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (s : UAKE.Env (schemeForger P msg hasOPK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (withUnif (UAKE.oracleImpl (schemeForger P msg hasOPK) tk)) oa).run s)).run) =
    (simulateQ (withUnif (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk)) oa).run
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
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (tk : RecipientIdentity F G SS SPK SSK K) (pk : SPK) (sk : SSK) (hsig : tk.sigkB = (pk, sk))
    {X : Type}
    (oa : OracleComp (unifSpec + UAKE.oracleSpec K (Message G PQPK CT S C IdC IdK)) X)
    (c : ℕ) (st : InitiatorParameters F G SS SPK Msg K ⊕ SessionContext G PQPK Msg K ⊕ K)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    Prod.map id (envFI P msg hasOPK) <$>
      (Prod.fst <$> (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (WriterT (QueryLog ((G ⊕ PQPK) →ₒ S)) ProbComp) + P.sig.signingOracle pk sk)
        ((simulateQ (withUnif (UAKE.oracleImpl (schemeForger P msg hasOPK) tk)) oa).run
          ⟨c, ⟨st, tr⟩, false, []⟩)).run) =
    (simulateQ (withUnif (UAKE.oracleImpl (uakeInitiatorIdeal P msg hasOPK) tk)) oa).run
      ⟨c, ⟨st, tr⟩, false, []⟩ := by
  have h := fst_run_withUnif_oracleImpl P msg hasOPK tk pk sk hsig oa
    (⟨c, ⟨st, tr⟩, false, []⟩ : UAKE.Env (schemeForger P msg hasOPK))
  simpa [envFI] using h

private lemma fst_run_challengeSession [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (uk : InitiatorParameters F G SS SPK Msg K) (tk : RecipientIdentity F G SS SPK SSK K)
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

def extractForgery [Inhabited G] [Inhabited S] (guess : Bool)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) : (G ⊕ PQPK) × S :=
  match tr.entries.findSome? (fun e => match e.1 with
    | .bundle b =>
        some (if guess then (EncodeKEM b.pqpkB.1, b.pqpkSig) else (EncodeEC b.spkB.1, b.spkSig))
    | _ => none) with
  | some fs => fs
  | none => (EncodeEC default, default)

def sigForger [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [Inhabited G] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : P.sig.unforgeableAdv where
  main := fun pk => do
    let ikA ← liftM (dhKeygen P.gen)
    let ikB ← liftM (dhKeygen P.gen)
    let spkB ← liftM (dhKeygen P.gen)
    let kdf ← liftM (($ᵗ (KeyMaterial G SS → K × K × K)) : ProbComp _)
    let uk : InitiatorParameters F G SS SPK Msg K := ⟨ikA, ikB.1, pk, msg, kdf⟩
    let tk : RecipientIdentity F G SS SPK SSK K := ⟨ikB, (pk, default), spkB, kdf⟩
    let guess ← liftM ($ᵗ Bool)
    let (_, _, env, _) ← UAKE.challengeSession (proto := schemeForger P msg hasOPK)
      A.toForger uk tk
    return extractForgery guess env.challenge.transcript

end SignatureReduction

private lemma probOutput_bind_bind_swap {α β γ : Type}
    (ma : ProbComp α) (mb : ProbComp β) (f : α → β → ProbComp γ) (z : γ) :
    Pr[= z | do let a ← ma; let b ← mb; f a b]
      = Pr[= z | do let b ← mb; let a ← ma; f a b] := by
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

noncomputable def idealAuthBreak [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ≥0∞ :=
  Pr[= true | do
    let x ← (uakeInitiatorIdeal P msg hasOPK).setup
    let r ← UAKE.challengeSession (proto := uakeInitiatorIdeal P msg hasOPK) A.toIdeal x.1 x.2
    pure (r.1.K0.isSome && !UAKE.isPingPong r.1)]

private lemma idealHop_bound [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εaead : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead) :
    |(Pr[= true | UAKE.Exp A.toIdeal]).toReal - 1 / 2| ≤ εsig + q * εaead := by
  haveI : Inhabited G := ⟨0⟩
  have hdecomp : Pr[= true | UAKE.Exp A.toIdeal]
      = 1 / 2 + idealAuthBreak P msg hasOPK A / 2 := by
    sorry
  have hauth : (idealAuthBreak P msg hasOPK A).toReal ≤ 2 * (εsig + q * εaead) := by
    have hbundle : (idealAuthBreak P msg hasOPK A).toReal
        ≤ 2 * ((sigForger P msg hasOPK A).advantage ProbCompRuntime.probComp).toReal
          + 2 * (q * εaead) := by
      sorry
    calc (idealAuthBreak P msg hasOPK A).toReal
        ≤ 2 * ((sigForger P msg hasOPK A).advantage ProbCompRuntime.probComp).toReal
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
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS]
    [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 DH3 : G) (DH4 : Option G),
      KdfHidesInput (K := K)
        (do let ss ← $ᵗ SS; pure (DH1, DH2, DH3, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εkem + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (KEM IND-CCA on the challenge KEM key, then `KdfHidesInput`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εkem + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): with the challenge key uniform, confidentiality
  -- is exactly 1/2, and a non-ping-pong completion needs a forged prekey signature (εsig) or a
  -- forged AEAD confirmation under a uniform key (q·εaead).
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead :=
    idealHop_bound P msg hasOPK hidKEM A q hq εsig εaead hsig haead
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εkem + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εkem + εaead + εkdf) := by ring

theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 : G) (DH4 : Option G) (ss : SS),
      KdfHidesInput (K := K)
        (do let c ← $ᵗ F; pure (DH1, DH2, c • P.gen, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  unfold UAKE.advantage
  set pReal := (Pr[= true | UAKE.Exp A]).toReal with hpReal
  set pIdeal := (Pr[= true | UAKE.Exp A.toIdeal]).toReal with hpIdeal
  -- Hop 1 (DDH/GapDH on the challenge DH share, then `KdfHidesInput`): reprogramming the
  -- challenge session's key material to uniform is undetectable, hybridized over the q sessions.
  have hKeyHop : |pReal - pIdeal| ≤ q * (εddh + εkdf) := by
    sorry
  -- Hop 2 (signature EUF-CMA + AEAD INT-CTXT): identical to the pq case — with the challenge key
  -- uniform, confidentiality is 1/2 and a non-ping-pong completion needs a forged signature or a
  -- forged AEAD confirmation.
  have hIdealHop : |pIdeal - 1 / 2| ≤ εsig + q * εaead :=
    idealHop_bound P msg hasOPK hidKEM A q hq εsig εaead hsig haead
  calc |pReal - 1 / 2|
      ≤ |pReal - pIdeal| + |pIdeal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ q * (εddh + εkdf) + (εsig + q * εaead) := add_le_add hKeyHop hIdealHop
    _ = εsig + q * (εddh + εaead + εkdf) := by ring

end PQXDH
