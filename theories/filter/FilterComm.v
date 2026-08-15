From CRIS.filter Require Export CallFilter SysFilter.

Section COMMUTATION.

  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma cfilter_comm bl m:
    SMod.filter (CFilter.msk_filter_out bl) (SMod.filter SFilter.msk_filter_out m)
    = SMod.filter SFilter.msk_filter_out (SMod.filter (CFilter.msk_filter_out bl) m).
  Proof.
    eapply SMod.t_eq; et. s. rewrite -!map_fmap_compose. f_equal.
    extensionality x. destruct x as [[msk [fspo fbd]]|]; ss.
    do 2 f_equal. extensionalities T e.
    rewrite /msk_and /SFilter.msk_filter_out /CFilter.msk_filter_out.
    destruct e; [et|].
    destruct s; [|et].
    destruct c; bsimpl; [|et|et|et].
    destruct msk, bool_decide; et.
  Qed.
  
End COMMUTATION.
