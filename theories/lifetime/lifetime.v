From lrust.lifetime Require Export lifetime_sig.
From lrust.lifetime.model Require definitions primitive accessors faking borrow
     reborrow creation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Module Export lifetime : lifetime_sig.
  Include definitions.
  Include primitive.
  Include borrow.
  Include faking.
  Include reborrow.
  Include accessors.
  Include creation.
End lifetime.

Section derived.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma bor_acc_cons E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ Q -∗ ▷(▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ} Q ∗ q.[κ].
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_strong with "LFT HP Htok") as (κ') "(#Hκκ' & $ & Hclose)"; first done.
  iIntros "!>*HQ HPQ". iMod ("Hclose" with "*HQ [HPQ]") as "[Hb $]".
  - iNext. iIntros "? _". by iApply "HPQ".
  - iApply (bor_shorten with "Hκκ' Hb").
Qed.

Lemma bor_acc E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_cons with "LFT HP Htok") as "($ & Hclose)"; first done.
  iIntros "!>HP". iMod ("Hclose" with "*HP []") as "[$ $]"; auto.
Qed.

Lemma bor_or E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
Proof.
  iIntros (?) "#LFT H". rewrite uPred.or_alt.
  iMod (bor_exists with "LFT H") as ([]) "H"; auto.
Qed.

Lemma bor_later E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) ={E,E∖↑lftN}▷=∗ &{κ}P.
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[H|[H† Hclose]]"; first done.
  - iDestruct "H" as "[HP  Hclose]". iModIntro. iNext.
    iApply ("Hclose" with "* HP"). by iIntros "!> $".
  - iIntros "!> !>". iMod "Hclose" as "_". by iApply (bor_fake with "LFT").
Qed.

Lemma bor_later_tok E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) -∗ q.[κ] ={E}▷=∗ &{κ}P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose]"; first done.
  iModIntro. iNext. iApply ("Hclose" with "* HP []"). by iIntros "!> $".
Qed.

Lemma bor_iff (P Q : iProp Σ) E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ □ (P ↔ Q) -∗ &{κ}P ={E}=∗ &{κ}Q.
Proof.
  iIntros (?) "#LFT #Heq Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[[HP Hclose]|[H† Hclose]]". done.
  - iApply ("Hclose" with "[HP] []").
      by iApply "Heq". by iIntros "!>HQ!>"; iApply "Heq".
  - iMod "Hclose". by iApply (bor_fake with "LFT").
Qed.

Lemma bor_persistent P `{!PersistentP P} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P ={E}=∗ ▷ P ∨ [†κ].
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic with "LFT Hb") as "[[#HP Hob]|[#H† Hclose]]"; first done.
  - iMod ("Hob" with "HP") as "_". auto.
  - iMod "Hclose" as "_". auto.
Qed.

Lemma bor_persistent_tok P `{!PersistentP P} E κ q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc with "LFT Hb Htok") as "[#HP Hob]"; first done.
  by iMod ("Hob" with "HP") as "[_ $]".
Qed.

Lemma lft_incl_static κ : (κ ⊑ static)%I.
Proof.
  iApply lft_incl_intro. iIntros "!#". iSplitR.
  - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_tok_static. auto.
  - iIntros "Hst". by iDestruct (lft_dead_static with "Hst") as "[]".
Qed.
End derived.
