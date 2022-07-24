From iris.proofmode Require Import proofmode tactics.
From iris.bi Require Import bi.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import util lft_contexts type_context programs.
From iris.prelude Require Import options.

Notation "l +ₗ[ ty ] i" := (l%L +ₗ Z.of_nat (i%nat * ty.(ty_size))%nat)
  (format "l  +ₗ[ ty ]  i", at level 50, left associativity) : loc_scope.

Section utils.
  Context `{!typeGS Σ}.

  Fixpoint loc_seq ty l n : vec loc n := 
    match n with
    | O => [#]
    | S n => l ::: loc_seq ty (l +ₗ ty.(ty_size)) n
    end.

  Lemma loc_seq_size_eq : ∀ n l ty1 ty2,
    ty1.(ty_size) = ty2.(ty_size) →
    loc_seq ty1 l n = loc_seq ty2 l n.
  Proof.
    induction n; first by intros.
    intros =>/=. rewrite H (IHn _ ty1 ty2); done.
  Qed.

  Lemma shift_loc_ty_assoc ty l m n :
    l +ₗ[ty] (m + n) = l +ₗ[ty] m +ₗ[ty] n.
  Proof. by rewrite Nat.mul_add_distr_r shift_loc_assoc_nat. Qed.

  Definition array_own ty n tid vl : iProp Σ :=
    ∃ wll : vec _ n, ⌜vl = concat wll⌝ ∗
      ([∗ list] v ∈ wll, ty.(ty_own) tid v)%I.

  Definition array_shr ty n κ tid l : iProp Σ :=
    [∗ list] i ↦ l' ∈ loc_seq ty l n, ty.(ty_shr) κ tid l'.

  Lemma big_sepL_mt_ty_own (ty : type) n tid q l :
    ([∗ list] i ↦ l' ∈ loc_seq ty l n, l' ↦∗{q}: ty.(ty_own) tid) ⊣⊢
    ∃ wll : vec _ n, l ↦∗{q} concat wll ∗
      ([∗ list] v ∈ wll, ty.(ty_own) tid v)%I.
  Proof.
    iSplit; iIntros "H".
    - iInduction n as [|n] "IH" forall (l) =>/=.
      { iExists [#]. by rewrite heap_mapsto_vec_nil /=. }
      iDestruct "H" as "[(%& H↦ & Hty) H]".
      iDestruct ("IH" with "H") as (?) "[H↦s H]". iExists (vl:::wll).
      rewrite heap_mapsto_vec_app.
      iDestruct (ty_size_eq with "Hty") as %->. iFrame.
    - iInduction n as [|n] "IH" forall (l) =>/=; first done.
      iDestruct "H" as (wll) "[H↦ H]".
      inv_vec wll =>/= vl wll.
      iDestruct "H" as "[Hty H]".
      rewrite heap_mapsto_vec_app.
      iDestruct "H↦" as "[H↦ H↦s]".
      iDestruct (ty_size_eq with "Hty") as %->.
      iSplitL "H↦ Hty". { iExists vl. iFrame. }
      iApply "IH". iExists wll. iFrame.
  Qed.

  Lemma array_split_mt ty n tid q l :
    l ↦∗{q}: array_own ty n tid ⊣⊢
    [∗ list] i ↦ l' ∈ loc_seq ty l n, l' ↦∗{q}: ty.(ty_own) tid.
  Proof.
    rewrite big_sepL_mt_ty_own.
    iSplit.
    - iIntros "(%vl & H↦ & %& -> & H)". iExists wll. iFrame.
    - iIntros "(% & H↦ & H)". iExists (concat wll). iFrame.
      iExists wll. by iFrame.
  Qed.

  Lemma array_share ty n E κ l tid q :
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} (l ↦∗: array_own ty n tid) -∗
      q.[κ] ={E}=∗ array_shr ty n κ tid l ∗ q.[κ].
  Proof.
    iIntros (Hlft) "#LFT /= H Hq".
    rewrite array_split_mt. unfold array_shr.
    iInduction n as [|n] "IH" forall (l) =>/=; first by iFrame.
    iMod (bor_sep with "LFT H") as "[Hown H]"; first done.
    iMod (ty.(ty_share) with "LFT Hown Hq") as "[Hshr Hq]"; first done.
    iMod ("IH" with "H Hq") as "[H Hq]".
    by iFrame.
  Qed.

  Lemma array_delay_sharing_nested N κ κ' κ'' l ty n tid:
    ↑lftN ⊆ N →
    lft_ctx -∗ ▷ (κ'' ⊑ κ ⊓ κ') -∗ 
      &{κ'}(&{κ}(l ↦∗: array_own ty n tid)) ={N}=∗
       □ ∀ (F : coPset) (q : Qp),
       ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ (q).[κ''] ={F}[F ∖ ↑shrN]▷=∗ 
       array_shr ty n κ'' tid l ∗ (q).[κ''].
  Proof.
    iIntros (?) "#LFT #Hincl Hbor". rewrite bor_unfold_idx.
    iDestruct "Hbor" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ array_shr ty n κ'' tid l)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !> * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb"; first solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (array_share with "LFT [Hb] Htok") as "[#Hshr $]"; first solve_ndisj.
      { iApply bor_shorten; done. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod fupd_mask_subseteq as "Hclose'"; last iModIntro; first solve_ndisj.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.

  Lemma array_shr_mono ty n κ κ' tid l :
    κ' ⊑ κ -∗ array_shr ty n κ tid l -∗ array_shr ty n κ' tid l.
  Proof.
    unfold array_shr. iIntros "#Hincl H".
    iApply (big_sepL_impl with "H"). iModIntro.
    iIntros (???) "H".
    iApply (ty_shr_mono with "Hincl H").
  Qed.
End utils.

Section array.
  Context `{!typeGS Σ}.

  Program Definition array (ty : type) (n : nat) : type := 
    {|
      ty_size := n * ty.(ty_size);
      ty_own tid vl := array_own ty n tid vl;
      ty_shr κ tid l := array_shr ty n κ tid l
    |}%I.
  Next Obligation.
    induction n; 
      iIntros (tid vl) "H";
      iDestruct "H" as (vl') "[% H]";
      first (iPureIntro; inv_vec vl'=>/=?; by subst). 
    inv_vec vl'=>/=v vl' Happ.
    iDestruct "H" as "[Hv Hvl]".
    iDestruct (ty_size_eq with "Hv") as "%".
    subst. rewrite app_length H.
    iDestruct (IHn with "[Hvl]") as "%"; first (iExists vl'; by iSplitR).
    iPureIntro. lia.
  Qed.
  Next Obligation.
    intros. by apply array_share.
  Qed.
  Next Obligation.
    intros. by apply array_shr_mono.
  Qed.

  Global Instance array_wf ty n `{!TyWf ty} : TyWf (array ty n) :=
    { ty_lfts := ty_lfts ty; ty_wf_E := ty_wf_E ty }.

  Lemma array_type_incl ty1 ty2 n:
    type_incl ty1 ty2 -∗
    type_incl (array ty1 n) (array ty2 n).
  Proof.
    iIntros "(% & #Hown & #Hshr)".
    iSplitL; first (iPureIntro; simpl; by rewrite H).
    iSplit; iModIntro =>/=.
    - unfold array_own. iIntros (tid vl) "(%& %& H)".
      iExists wll. iSplitR; first by iPureIntro.
      iApply (big_sepL_impl with "H").
      iModIntro. iIntros (???). iApply "Hown".
    - unfold array_shr. iIntros (κ tid l) "H".
      apply (loc_seq_size_eq n l) in H. rewrite H.
      iApply (big_sepL_impl with "H").
      iModIntro. iIntros (???). iApply "Hshr".
  Qed.

  Lemma array_type_equal ty1 ty2 n:
    type_equal ty1 ty2 -∗
    type_equal (array ty1 n) (array ty2 n).
  Proof.
    rewrite type_equal_incl.
    iIntros "[H12 H21]".
    rewrite type_equal_incl.
    iPoseProof (array_type_incl with "H12") as "H12".
    iPoseProof (array_type_incl with "H21") as "H21".
    iFrame.
  Qed.

  Global Instance array_mono E L :
    Proper (subtype E L ==> eq ==> subtype E L) array.
  Proof.
    intros ?? Hty ? κ ->. iIntros (??) "HL".
    iDestruct (Hty with "HL") as "#Hty".
    iIntros "!> #HE".
    iApply array_type_incl.
    by iApply "Hty". 
  Qed.

  Global Instance array_proper E L :
    Proper (eqtype E L ==> eq ==> eqtype E L) array.
  Proof. intros ??[]; split; by apply array_mono. Qed.

  Global Instance array_type_ne n: TypeNonExpansive (λ ty, array ty n).
  Proof.
    intros N ?? [Hsize Hown Hshr].
    constructor =>/=; first by rewrite Hsize.
    - destruct N; first done. intros. simpl in *.
      unfold array_own. by do 6 f_equiv.
    - intros. unfold array_shr. 
      apply (loc_seq_size_eq n l) in Hsize. rewrite Hsize.
      by do 3 f_equiv.
  Qed.

  (*
  TODO
  Global Instance array_copy `{!Copy ty} n : Copy (array ty n).
  Proof.
    split; first (by intros; apply _).
    iIntros (κ tid E F l q ? HF) "#LFT Hshr Hna Htok" =>/=.
    unfold array_own. unfold array_shr.
    iInduction n as [|n] "IH" forall (q l F HF)=>/=.
    {
      iExists 1%Qp. rewrite difference_empty_L. iFrame "Hna".
      iSplitR; first (iExists [#]; iModIntro; iNext; rewrite heap_mapsto_vec_nil; iSplit =>//=; iExists [#]; iSplit =>//=).
    iMod (@copy_shr_acc with "LFT Hshr Hna Hq") as (q1) "(Htl & H1 & Hclose1)"; first solve_ndisj.
  Qed.
   *)

  Global Instance array_send ty n :
    Send ty → Send (array ty n).
  Proof.
    iIntros (Hsend tid1 tid2 vl) "(%& %& H)" =>/=.
    iExists wll. iSplitR; first by iPureIntro.
    iApply (big_sepL_impl with "H"). iModIntro.
    iIntros (???) "H". by iApply Hsend.
  Qed.

  Global Instance array_sync ty n :
    Sync ty → Sync (array ty n).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H" =>/=.
    iApply (big_sepL_impl with "H"). iModIntro.
    iIntros (???) "H". by iApply Hsync.
  Qed.
End array.

Notation "[[ τ ; n ]]" := (array τ n) (format "[[ τ ; n ]]") : lrust_type_scope.
