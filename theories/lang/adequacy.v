From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import auth.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class lrustGpreS Σ := HeapGpreS {
  lrustGpreS_irig :> invGpreS Σ;
  lrustGpreS_heap :> inG Σ (authR heapUR);
  lrustGpreS_heap_freeable :> inG Σ (authR heap_freeableUR)
}.

Definition lrustΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR))].
Global Instance subG_lrustGpreS {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

Definition lrust_adequacy Σ `{!lrustGpreS Σ} e σ φ :
  (∀ `{!lrustGS Σ}, True ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??).
  iMod (own_alloc (● to_heap σ)) as (vγ) "Hvγ".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  set (Hheap := HeapGS _ _ _ vγ fγ).
  iModIntro. iExists (λ σ _, heap_ctx σ), (λ _, True%I). iSplitL.
  { iExists ∅. by iFrame. }
  by iApply (Hwp (LRustGS _ _ Hheap)).
Qed.
