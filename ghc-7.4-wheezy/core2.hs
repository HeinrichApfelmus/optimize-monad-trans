[1 of 2] Compiling Reader           ( Reader.hs, Reader.o )

==================== Tidy Core ====================
Result size = 180

Reader.ask1
  :: forall (m_ac3 :: * -> *) r_ac4.
     Monad m_ac3 =>
     r_ac4 -> m_ac3 r_ac4
[GblId,
 Arity=2,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_ac3::* -> *)
                 (@ r_ac4)
                 ($dMonad_ac5 [Occ=Once] :: Monad m_ac3)
                 (r_aay [Occ=Once] :: r_ac4) ->
                 return @ m_ac3 $dMonad_ac5 @ r_ac4 r_aay}]
Reader.ask1 =
  \ (@ m_ac3::* -> *)
    (@ r_ac4)
    ($dMonad_ac5 :: Monad m_ac3)
    (r_aay :: r_ac4) ->
    return @ m_ac3 $dMonad_ac5 @ r_ac4 r_aay

Reader.ask
  :: forall (m_aaj :: * -> *) r_aak.
     Monad m_aaj =>
     Reader.ReaderT r_aak m_aaj r_aak
[GblId,
 Arity=2,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.ask1 `cast` ...}]
Reader.ask = Reader.ask1 `cast` ...

Reader.runReaderT1
  :: forall r_aaQ (m_aaR :: * -> *) a_aaS.
     Reader.ReaderT r_aaQ m_aaR a_aaS
     -> Reader.ReaderT r_aaQ m_aaR a_aaS
[GblId,
 Arity=1,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT1 =
  \ (@ r_aaQ)
    (@ m_aaR::* -> *)
    (@ a_aaS)
    (ds_dds :: Reader.ReaderT r_aaQ m_aaR a_aaS) ->
    ds_dds

Reader.runReaderT
  :: forall r_aad (m_aae :: * -> *) a_aaf.
     Reader.ReaderT r_aad m_aae a_aaf -> r_aad -> m_aae a_aaf
[GblId[[RecSel]],
 Arity=1,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT = Reader.runReaderT1 `cast` ...

Reader.$fMonadReaderT_$creturn
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     forall a_ac7. a_ac7 -> Reader.ReaderT r_aaH m_aaG a_ac7
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=IF_ARGS [30 0] 50 60}]
Reader.$fMonadReaderT_$creturn =
  \ (@ m_aaG::* -> *)
    (@ r_aaH)
    ($dMonad_acP :: Monad m_aaG)
    (@ a_ad6)
    (a1_aaw :: a_ad6) ->
    let {
      lvl1_sdX [Dmd=Just L] :: m_aaG a_ad6

      lvl1_sdX = return @ m_aaG $dMonad_acP @ a_ad6 a1_aaw } in
    (\ _ -> lvl1_sdX) `cast` ...

Reader.$fMonadReaderT1
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     forall a_acS b_acT.
     Reader.ReaderT r_aaH m_aaG a_acS
     -> (a_acS -> Reader.ReaderT r_aaH m_aaG b_acT)
     -> r_aaH
     -> m_aaG b_acT
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ m_aaG::* -> *)
                 (@ r_aaH)
                 ($dMonad_acP [Occ=Once] :: Monad m_aaG)
                 (@ a_acS)
                 (@ b_acT)
                 (m_aas [Occ=Once] :: Reader.ReaderT r_aaH m_aaG a_acS)
                 (k_aat [Occ=OnceL!] :: a_acS -> Reader.ReaderT r_aaH m_aaG b_acT)
                 (r_aau :: r_aaH) ->
                 >>=
                   @ m_aaG
                   $dMonad_acP
                   @ a_acS
                   @ b_acT
                   ((m_aas `cast` ...) r_aau)
                   (\ (a1_aav [Occ=Once] :: a_acS) ->
                      ((k_aat a1_aav) `cast` ...) r_aau)}]
Reader.$fMonadReaderT1 =
  \ (@ m_aaG::* -> *)
    (@ r_aaH)
    ($dMonad_acP :: Monad m_aaG)
    (@ a_acS)
    (@ b_acT)
    (m_aas :: Reader.ReaderT r_aaH m_aaG a_acS)
    (k_aat :: a_acS -> Reader.ReaderT r_aaH m_aaG b_acT)
    (r_aau :: r_aaH) ->
    >>=
      @ m_aaG
      $dMonad_acP
      @ a_acS
      @ b_acT
      ((m_aas `cast` ...) r_aau)
      (\ (a1_aav :: a_acS) -> ((k_aat a1_aav) `cast` ...) r_aau)

Reader.$fMonadReaderT_$c>>=
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     forall a_acp b_acq.
     Reader.ReaderT r_aaH m_aaG a_acp
     -> (a_acp -> Reader.ReaderT r_aaH m_aaG b_acq)
     -> Reader.ReaderT r_aaH m_aaG b_acq
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadReaderT1 `cast` ...}]
Reader.$fMonadReaderT_$c>>= = Reader.$fMonadReaderT1 `cast` ...

Reader.$fMonadReaderT_$cfail
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     forall a_adr. String -> Reader.ReaderT r_aaH m_aaG a_adr
[GblId,
 Arity=2,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_Xbj::* -> *)
                 (@ r_Xbl)
                 _
                 (@ a_adL)
                 (eta_B1 [Occ=Once] :: [Char]) ->
                 error @ (Reader.ReaderT r_Xbl m_Xbj a_adL) eta_B1}]
Reader.$fMonadReaderT_$cfail =
  \ (@ m_Xbj::* -> *)
    (@ r_Xbl)
    _
    (@ a_adL)
    (eta_B1 :: [Char]) ->
    error @ (Reader.ReaderT r_Xbl m_Xbj a_adL) eta_B1

a_reo
  :: forall (m_Xbk :: * -> *) r_Xbm.
     Monad m_Xbk =>
     forall a_adp b_adq.
     Reader.ReaderT r_Xbm m_Xbk a_adp
     -> Reader.ReaderT r_Xbm m_Xbk b_adq -> r_Xbm -> m_Xbk b_adq

a_reo =
  \ (@ m_Xbk::* -> *)
    (@ r_Xbm)
    ($dMonad_Xdv :: Monad m_Xbk)
    (@ a_adp)
    (@ b_adq)
    (eta_B2 :: Reader.ReaderT r_Xbm m_Xbk a_adp)
    (eta1_B1 :: Reader.ReaderT r_Xbm m_Xbk b_adq)
    (eta2_X2 :: r_Xbm) ->
    let {
      lvl1_sel :: m_Xbk b_adq
      [LclId]
      lvl1_sel = (eta1_B1 `cast` ...) eta2_X2 } in
    >>=
      @ m_Xbk
      $dMonad_Xdv
      @ a_adp
      @ b_adq
      ((eta_B2 `cast` ...) eta2_X2)
      (\ _ -> lvl1_sel)

Reader.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     forall a_adp b_adq.
     Reader.ReaderT r_aaH m_aaG a_adp
     -> Reader.ReaderT r_aaH m_aaG b_adq
     -> Reader.ReaderT r_aaH m_aaG b_adq
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ m_XbR::* -> *)
                 (@ r_XbU)
                 ($dMonad_Xe4 [Occ=Once] :: Monad m_XbR)
                 (@ a_adE)
                 (@ b_adF)
                 (m_adG [Occ=Once] :: Reader.ReaderT r_XbU m_XbR a_adE)
                 (k_adH [Occ=OnceL] :: Reader.ReaderT r_XbU m_XbR b_adF) ->
                 Reader.$fMonadReaderT_$c>>=
                   @ m_XbR @ r_XbU $dMonad_Xe4 @ a_adE @ b_adF m_adG (\ _ -> k_adH)}]
Reader.$fMonadReaderT_$c>> = a_reo `cast` ...

lvl_rep
  :: forall (m_Xbl :: * -> *) r_Xbn a_adL.
     [Char] -> Reader.ReaderT r_Xbn m_Xbl a_adL

lvl_rep =
  \ (@ m_Xbl::* -> *)
    (@ r_Xbn)
    (@ a_adL)
    (eta_XD :: [Char]) ->
    error @ (Reader.ReaderT r_Xbn m_Xbl a_adL) eta_XD

Reader.$fMonadReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall (m_aaG :: * -> *) r_aaH.
     Monad m_aaG =>
     Monad (Reader.ReaderT r_aaH m_aaG)
[GblId[DFunId],
 Arity=1,

 Unf=DFun(arity=3) D:Monad [Reader.$fMonadReaderT_$c>>=,
                                     Reader.$fMonadReaderT_$c>>, Reader.$fMonadReaderT_$creturn,
                                     Reader.$fMonadReaderT_$cfail]]
Reader.$fMonadReaderT =
  \ (@ m_Xbl::* -> *)
    (@ r_Xbn)
    ($dMonad_Xdw :: Monad m_Xbl) ->
    D:Monad
      @ (Reader.ReaderT r_Xbn m_Xbl)
      ((Reader.$fMonadReaderT1 @ m_Xbl @ r_Xbn $dMonad_Xdw) `cast` ...)
      (Reader.$fMonadReaderT_$c>> @ m_Xbl @ r_Xbn $dMonad_Xdw)
      (Reader.$fMonadReaderT_$creturn @ m_Xbl @ r_Xbn $dMonad_Xdw)
      (lvl_rep @ m_Xbl @ r_Xbn)

Reader.$fMonadIOReaderT_$cliftIO
  :: forall (m_aaE :: * -> *) r_aaF.
     Control.Monad.IO.Class.MonadIO m_aaE =>
     forall a_abX.
     IO a_abX -> Reader.ReaderT r_aaF m_aaE a_abX
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=IF_ARGS [30 0] 50 60}]
Reader.$fMonadIOReaderT_$cliftIO =
  \ (@ m_aaE::* -> *)
    (@ r_aaF)
    ($dMonadIO_acD :: Control.Monad.IO.Class.MonadIO m_aaE)
    (@ a_acJ)
    (m_aaz :: IO a_acJ) ->
    let {
      lvl1_se0 [Dmd=Just L] :: m_aaE a_acJ

      lvl1_se0 =
        Control.Monad.IO.Class.liftIO
          @ m_aaE $dMonadIO_acD @ a_acJ m_aaz } in
    (\ _ -> lvl1_se0) `cast` ...

Reader.$fMonadIOReaderT_$c$p1MonadIO
  :: forall (m_aaE :: * -> *) r_aaF.
     Control.Monad.IO.Class.MonadIO m_aaE =>
     Monad (Reader.ReaderT r_aaF m_aaE)
[GblId,
 Arity=1,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ m_aaE::* -> *)
                 (@ r_aaF)
                 ($dMonadIO_acD [Occ=Once]
                    :: Control.Monad.IO.Class.MonadIO m_aaE) ->
                 Reader.$fMonadReaderT
                   @ m_aaE
                   @ r_aaF
                   (Control.Monad.IO.Class.$p1MonadIO @ m_aaE $dMonadIO_acD)}]
Reader.$fMonadIOReaderT_$c$p1MonadIO =
  \ (@ m_aaE::* -> *)
    (@ r_aaF)
    ($dMonadIO_acD :: Control.Monad.IO.Class.MonadIO m_aaE) ->
    Reader.$fMonadReaderT
      @ m_aaE
      @ r_aaF
      (Control.Monad.IO.Class.$p1MonadIO @ m_aaE $dMonadIO_acD)

Reader.$fMonadIOReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall (m_aaE :: * -> *) r_aaF.
     Control.Monad.IO.Class.MonadIO m_aaE =>
     Control.Monad.IO.Class.MonadIO (Reader.ReaderT r_aaF m_aaE)
[GblId[DFunId],
 Arity=1,

 Unf=DFun(arity=3) Control.Monad.IO.Class.D:MonadIO [Reader.$fMonadIOReaderT_$c$p1MonadIO,
                                                     Reader.$fMonadIOReaderT_$cliftIO]]
Reader.$fMonadIOReaderT =
  \ (@ m_aaE::* -> *)
    (@ r_aaF)
    ($dMonadIO_acD :: Control.Monad.IO.Class.MonadIO m_aaE) ->
    Control.Monad.IO.Class.D:MonadIO
      @ (Reader.ReaderT r_aaF m_aaE)
      (Reader.$fMonadIOReaderT_$c$p1MonadIO
         @ m_aaE @ r_aaF $dMonadIO_acD)
      (Reader.$fMonadIOReaderT_$cliftIO @ m_aaE @ r_aaF $dMonadIO_acD)

Reader.$fMonadTransReaderT1
  :: forall r_aaB (m_acy :: * -> *) a_acz.
     Monad m_acy =>
     m_acy a_acz -> r_aaB -> m_acy a_acz
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_aaB)
                 (@ m_acy::* -> *)
                 (@ a_acz)
                 _
                 (m_aaC [Occ=Once] :: m_acy a_acz)
                 _ ->
                 m_aaC}]
Reader.$fMonadTransReaderT1 =
  \ (@ r_aaB)
    (@ m_acy::* -> *)
    (@ a_acz)
    _
    (m_aaC :: m_acy a_acz)
    _ ->
    m_aaC

Reader.$fMonadTransReaderT_$clift
  :: forall r_aaB (m_acw :: * -> *) a_acx.
     Monad m_acw =>
     m_acw a_acx -> Reader.ReaderT r_aaB m_acw a_acx
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadTransReaderT1 `cast` ...}]
Reader.$fMonadTransReaderT_$clift =
  Reader.$fMonadTransReaderT1 `cast` ...

Reader.$fMonadTransReaderT [InlPrag=INLINE (sat-args=0)]
  :: forall r_aaB.
     Control.Monad.Trans.Class.MonadTrans (Reader.ReaderT r_aaB)
[GblId[DFunId(nt)],

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=True)
         Tmpl= Reader.$fMonadTransReaderT_$clift `cast` ...}]
Reader.$fMonadTransReaderT = Reader.$fMonadTransReaderT1 `cast` ...

==================== Asm code ====================
.data
	.align 8
.align 1
.globl __stginit_Reader
.type __stginit_Reader, @object
__stginit_Reader:
.data
	.align 8
.align 1
.globl Reader_ask1_closure
.type Reader_ask1_closure, @object
Reader_ask1_closure:
	.quad	Reader_ask1_info
.text
	.align 8
	.quad	8589934604
	.quad	0
	.quad	15
.globl Reader_ask1_info
.type Reader_ask1_info, @object
Reader_ask1_info:
.LcfV:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcfY
	movq %rsi,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	addq $-16,%rbp
	jmp base_GHCziBase_return_info
.LcfY:
	movl $Reader_ask1_closure,%ebx
	jmp *-8(%r13)
	.size Reader_ask1_info, .-Reader_ask1_info
.data
	.align 8
.align 1
.globl Reader_ask_closure
.type Reader_ask_closure, @object
Reader_ask_closure:
	.quad	Reader_ask_info
.text
	.align 8
	.quad	8589934604
	.quad	0
	.quad	15
.globl Reader_ask_info
.type Reader_ask_info, @object
Reader_ask_info:
.Lcg7:
	jmp Reader_ask1_info
	.size Reader_ask_info, .-Reader_ask_info
.data
	.align 8
.align 1
.globl Reader_runReaderT1_closure
.type Reader_runReaderT1_closure, @object
Reader_runReaderT1_closure:
	.quad	Reader_runReaderT1_info
.text
	.align 8
	.quad	4294967301
	.quad	0
	.quad	15
.globl Reader_runReaderT1_info
.type Reader_runReaderT1_info, @object
Reader_runReaderT1_info:
.Lcgf:
	movq %r14,%rbx
	jmp stg_ap_0_fast
	.size Reader_runReaderT1_info, .-Reader_runReaderT1_info
.data
	.align 8
.align 1
.globl Reader_runReaderT_closure
.type Reader_runReaderT_closure, @object
Reader_runReaderT_closure:
	.quad	Reader_runReaderT_info
.text
	.align 8
	.quad	4294967301
	.quad	0
	.quad	15
.globl Reader_runReaderT_info
.type Reader_runReaderT_info, @object
Reader_runReaderT_info:
.Lcgn:
	jmp Reader_runReaderT1_info
	.size Reader_runReaderT_info, .-Reader_runReaderT_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderTzuzdcreturn_closure
.type Reader_zdfMonadReaderTzuzdcreturn_closure, @object
Reader_zdfMonadReaderTzuzdcreturn_closure:
	.quad	Reader_zdfMonadReaderTzuzdcreturn_info
.text
	.align 8
	.quad	2
	.quad	19
seB_info:
.Lcgz:
	leaq -32(%rbp),%rax
	cmpq %r15,%rax
	jb .LcgB
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 24(%rbx),%rax
	movq %rax,-24(%rbp)
	movq $stg_ap_p_info,-32(%rbp)
	movq 16(%rbx),%r14
	addq $-32,%rbp
	jmp base_GHCziBase_return_info
.LcgB:
	jmp *-16(%r13)
	.size seB_info, .-seB_info
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
sfJ_info:
.LcgJ:
	movq 7(%rbx),%rbx
	jmp stg_ap_0_fast
	.size sfJ_info, .-sfJ_info
.text
	.align 8
	.quad	8589934604
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderTzuzdcreturn_info
.type Reader_zdfMonadReaderTzuzdcreturn_info, @object
Reader_zdfMonadReaderTzuzdcreturn_info:
.LcgN:
	addq $48,%r12
	cmpq 144(%r13),%r12
	ja .LcgR
	movq $seB_info,-40(%r12)
	movq %r14,-24(%r12)
	movq %rsi,-16(%r12)
	movq $sfJ_info,-8(%r12)
	leaq -40(%r12),%rax
	movq %rax,0(%r12)
	leaq -7(%r12),%rbx
	jmp *0(%rbp)
.LcgR:
	movq $48,192(%r13)
.LcgP:
	movl $Reader_zdfMonadReaderTzuzdcreturn_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderTzuzdcreturn_info, .-Reader_zdfMonadReaderTzuzdcreturn_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderT1_closure
.type Reader_zdfMonadReaderT1_closure, @object
Reader_zdfMonadReaderT1_closure:
	.quad	Reader_zdfMonadReaderT1_info
.text
	.align 8
	.quad	4294967301
	.quad	2
	.quad	12
sfK_info:
.Lch3:
	movq 7(%rbx),%rsi
	movq 15(%rbx),%rbx
	jmp stg_ap_pp_fast
	.size sfK_info, .-sfK_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderT1_info
.type Reader_zdfMonadReaderT1_info, @object
Reader_zdfMonadReaderT1_info:
.Lch7:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .Lch9
	addq $56,%r12
	cmpq 144(%r13),%r12
	ja .Lchb
	movq $sfK_info,-48(%r12)
	movq %r8,-40(%r12)
	movq %rdi,-32(%r12)
	movq $stg_ap_2_upd_info,-24(%r12)
	movq %rsi,-8(%r12)
	movq %r8,0(%r12)
	leaq -47(%r12),%rax
	movq %rax,-8(%rbp)
	leaq -24(%r12),%rax
	movq %rax,-16(%rbp)
	movq $stg_ap_pp_info,-24(%rbp)
	addq $-24,%rbp
	jmp base_GHCziBase_zgzgze_info
.Lchb:
	movq $56,192(%r13)
.Lch9:
	movl $Reader_zdfMonadReaderT1_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderT1_info, .-Reader_zdfMonadReaderT1_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderTzuzdczgzgze_closure
.type Reader_zdfMonadReaderTzuzdczgzgze_closure, @object
Reader_zdfMonadReaderTzuzdczgzgze_closure:
	.quad	Reader_zdfMonadReaderTzuzdczgzgze_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderTzuzdczgzgze_info
.type Reader_zdfMonadReaderTzuzdczgzgze_info, @object
Reader_zdfMonadReaderTzuzdczgzgze_info:
.Lchm:
	jmp Reader_zdfMonadReaderT1_info
	.size Reader_zdfMonadReaderTzuzdczgzgze_info, .-Reader_zdfMonadReaderTzuzdczgzgze_info
.section .data
	.align 8
.align 1
Reader_zdfMonadReaderTzuzdcfail_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderTzuzdcfail_closure
.type Reader_zdfMonadReaderTzuzdcfail_closure, @object
Reader_zdfMonadReaderTzuzdcfail_closure:
	.quad	Reader_zdfMonadReaderTzuzdcfail_info
	.quad	0
.text
	.align 8
	.long	Reader_zdfMonadReaderTzuzdcfail_srt-(Reader_zdfMonadReaderTzuzdcfail_info)+0
	.long	0
	.quad	8589934604
	.quad	0
	.quad	4294967311
.globl Reader_zdfMonadReaderTzuzdcfail_info
.type Reader_zdfMonadReaderTzuzdcfail_info, @object
Reader_zdfMonadReaderTzuzdcfail_info:
.Lchv:
	movq %rsi,%r14
	jmp base_GHCziErr_error_info
	.size Reader_zdfMonadReaderTzuzdcfail_info, .-Reader_zdfMonadReaderTzuzdcfail_info
.data
	.align 8
.align 1
reo_closure:
	.quad	reo_info
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
sfM_info:
.LchG:
	movq 7(%rbx),%rbx
	jmp stg_ap_0_fast
	.size sfM_info, .-sfM_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
reo_info:
.LchK:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .LchM
	addq $80,%r12
	cmpq 144(%r13),%r12
	ja .LchO
	movq $stg_ap_2_upd_info,-72(%r12)
	movq %rdi,-56(%r12)
	movq %r8,-48(%r12)
	movq $sfM_info,-40(%r12)
	leaq -72(%r12),%rax
	movq %rax,-32(%r12)
	movq $stg_ap_2_upd_info,-24(%r12)
	movq %rsi,-8(%r12)
	movq %r8,0(%r12)
	leaq -39(%r12),%rax
	movq %rax,-8(%rbp)
	leaq -24(%r12),%rax
	movq %rax,-16(%rbp)
	movq $stg_ap_pp_info,-24(%rbp)
	addq $-24,%rbp
	jmp base_GHCziBase_zgzgze_info
.LchO:
	movq $80,192(%r13)
.LchM:
	movl $reo_closure,%ebx
	jmp *-8(%r13)
	.size reo_info, .-reo_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderTzuzdczgzg_closure
.type Reader_zdfMonadReaderTzuzdczgzg_closure, @object
Reader_zdfMonadReaderTzuzdczgzg_closure:
	.quad	Reader_zdfMonadReaderTzuzdczgzg_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderTzuzdczgzg_info
.type Reader_zdfMonadReaderTzuzdczgzg_info, @object
Reader_zdfMonadReaderTzuzdczgzg_info:
.Lci0:
	jmp reo_info
	.size Reader_zdfMonadReaderTzuzdczgzg_info, .-Reader_zdfMonadReaderTzuzdczgzg_info
.section .data
	.align 8
.align 1
rep_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
rep_closure:
	.quad	rep_info
	.quad	0
.text
	.align 8
	.long	rep_srt-(rep_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
rep_info:
.Lci9:
	jmp base_GHCziErr_error_info
	.size rep_info, .-rep_info
.section .data
	.align 8
.align 1
Reader_zdfMonadReaderT_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderT_closure
.type Reader_zdfMonadReaderT_closure, @object
Reader_zdfMonadReaderT_closure:
	.quad	Reader_zdfMonadReaderT_info
	.quad	0
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
sfG_info:
.Lcil:
	movq %r14,%rsi
	movq 7(%rbx),%r14
	jmp Reader_zdfMonadReaderTzuzdcreturn_info
	.size sfG_info, .-sfG_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
sfH_info:
.Lcir:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderTzuzdczgzg_info
	.size sfH_info, .-sfH_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
sfI_info:
.Lcix:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderT1_info
	.size sfI_info, .-sfI_info
.text
	.align 8
	.long	Reader_zdfMonadReaderT_srt-(Reader_zdfMonadReaderT_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
.globl Reader_zdfMonadReaderT_info
.type Reader_zdfMonadReaderT_info, @object
Reader_zdfMonadReaderT_info:
.LciB:
	addq $88,%r12
	cmpq 144(%r13),%r12
	ja .LciF
	movq $sfG_info,-80(%r12)
	movq %r14,-72(%r12)
	movq $sfH_info,-64(%r12)
	movq %r14,-56(%r12)
	movq $sfI_info,-48(%r12)
	movq %r14,-40(%r12)
	movq $base_GHCziBase_DZCMonad_con_info,-32(%r12)
	leaq -45(%r12),%rax
	movq %rax,-24(%r12)
	leaq -61(%r12),%rax
	movq %rax,-16(%r12)
	leaq -79(%r12),%rax
	movq %rax,-8(%r12)
	movq $rep_closure+1,0(%r12)
	leaq -31(%r12),%rbx
	jmp *0(%rbp)
.LciF:
	movq $88,192(%r13)
.LciD:
	movl $Reader_zdfMonadReaderT_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderT_info, .-Reader_zdfMonadReaderT_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadIOReaderTzuzdcliftIO_closure
.type Reader_zdfMonadIOReaderTzuzdcliftIO_closure, @object
Reader_zdfMonadIOReaderTzuzdcliftIO_closure:
	.quad	Reader_zdfMonadIOReaderTzuzdcliftIO_info
.text
	.align 8
	.quad	2
	.quad	19
sfl_info:
.LciU:
	leaq -32(%rbp),%rax
	cmpq %r15,%rax
	jb .LciW
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 24(%rbx),%rax
	movq %rax,-24(%rbp)
	movq $stg_ap_p_info,-32(%rbp)
	movq 16(%rbx),%r14
	addq $-32,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_liftIO_info
.LciW:
	jmp *-16(%r13)
	.size sfl_info, .-sfl_info
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
sfE_info:
.Lcj4:
	movq 7(%rbx),%rbx
	jmp stg_ap_0_fast
	.size sfE_info, .-sfE_info
.text
	.align 8
	.quad	8589934604
	.quad	0
	.quad	15
.globl Reader_zdfMonadIOReaderTzuzdcliftIO_info
.type Reader_zdfMonadIOReaderTzuzdcliftIO_info, @object
Reader_zdfMonadIOReaderTzuzdcliftIO_info:
.Lcj8:
	addq $48,%r12
	cmpq 144(%r13),%r12
	ja .Lcjc
	movq $sfl_info,-40(%r12)
	movq %r14,-24(%r12)
	movq %rsi,-16(%r12)
	movq $sfE_info,-8(%r12)
	leaq -40(%r12),%rax
	movq %rax,0(%r12)
	leaq -7(%r12),%rbx
	jmp *0(%rbp)
.Lcjc:
	movq $48,192(%r13)
.Lcja:
	movl $Reader_zdfMonadIOReaderTzuzdcliftIO_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadIOReaderTzuzdcliftIO_info, .-Reader_zdfMonadIOReaderTzuzdcliftIO_info
.section .data
	.align 8
.align 1
Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
.globl Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_closure
.type Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_closure, @object
Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_closure:
	.quad	Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
	.quad	0
.text
	.align 8
	.quad	1
	.quad	17
sfF_info:
.Lcjq:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcjs
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_zdp1MonadIO_info
.Lcjs:
	jmp *-16(%r13)
	.size sfF_info, .-sfF_info
.text
	.align 8
	.long	Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_srt-(Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
.globl Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
.type Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info, @object
Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info:
.Lcjx:
	addq $24,%r12
	cmpq 144(%r13),%r12
	ja .LcjB
	movq $sfF_info,-16(%r12)
	movq %r14,0(%r12)
	leaq -16(%r12),%r14
	jmp Reader_zdfMonadReaderT_info
.LcjB:
	movq $24,192(%r13)
.Lcjz:
	movl $Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info, .-Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
.section .data
	.align 8
.align 1
Reader_zdfMonadIOReaderT_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
.globl Reader_zdfMonadIOReaderT_closure
.type Reader_zdfMonadIOReaderT_closure, @object
Reader_zdfMonadIOReaderT_closure:
	.quad	Reader_zdfMonadIOReaderT_info
	.quad	0
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
sfC_info:
.LcjN:
	movq %r14,%rsi
	movq 7(%rbx),%r14
	jmp Reader_zdfMonadIOReaderTzuzdcliftIO_info
	.size sfC_info, .-sfC_info
.text
	.align 8
	.long	Reader_zdfMonadIOReaderT_srt-(sfD_info)+0
	.long	0
	.quad	1
	.quad	4294967313
sfD_info:
.LcjU:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcjW
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
.LcjW:
	jmp *-16(%r13)
	.size sfD_info, .-sfD_info
.text
	.align 8
	.long	Reader_zdfMonadIOReaderT_srt-(Reader_zdfMonadIOReaderT_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
.globl Reader_zdfMonadIOReaderT_info
.type Reader_zdfMonadIOReaderT_info, @object
Reader_zdfMonadIOReaderT_info:
.Lck1:
	addq $64,%r12
	cmpq 144(%r13),%r12
	ja .Lck5
	movq $sfC_info,-56(%r12)
	movq %r14,-48(%r12)
	movq $sfD_info,-40(%r12)
	movq %r14,-24(%r12)
	movq $transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_DZCMonadIO_con_info,-16(%r12)
	leaq -40(%r12),%rax
	movq %rax,-8(%r12)
	leaq -55(%r12),%rax
	movq %rax,0(%r12)
	leaq -15(%r12),%rbx
	jmp *0(%rbp)
.Lck5:
	movq $64,192(%r13)
.Lck3:
	movl $Reader_zdfMonadIOReaderT_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadIOReaderT_info, .-Reader_zdfMonadIOReaderT_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadTransReaderT1_closure
.type Reader_zdfMonadTransReaderT1_closure, @object
Reader_zdfMonadTransReaderT1_closure:
	.quad	Reader_zdfMonadTransReaderT1_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadTransReaderT1_info
.type Reader_zdfMonadTransReaderT1_info, @object
Reader_zdfMonadTransReaderT1_info:
.Lckf:
	movq %rsi,%rbx
	jmp stg_ap_0_fast
	.size Reader_zdfMonadTransReaderT1_info, .-Reader_zdfMonadTransReaderT1_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadTransReaderTzuzdclift_closure
.type Reader_zdfMonadTransReaderTzuzdclift_closure, @object
Reader_zdfMonadTransReaderTzuzdclift_closure:
	.quad	Reader_zdfMonadTransReaderTzuzdclift_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadTransReaderTzuzdclift_info
.type Reader_zdfMonadTransReaderTzuzdclift_info, @object
Reader_zdfMonadTransReaderTzuzdclift_info:
.Lckn:
	jmp Reader_zdfMonadTransReaderT1_info
	.size Reader_zdfMonadTransReaderTzuzdclift_info, .-Reader_zdfMonadTransReaderTzuzdclift_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadTransReaderT_closure
.type Reader_zdfMonadTransReaderT_closure, @object
Reader_zdfMonadTransReaderT_closure:
	.quad	Reader_zdfMonadTransReaderT_info
	.quad	0
	.quad	0
	.quad	0
.text
	.align 8
	.quad	0
	.quad	22
.globl Reader_zdfMonadTransReaderT_info
.type Reader_zdfMonadTransReaderT_info, @object
Reader_zdfMonadTransReaderT_info:
.Lckz:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LckB
	addq $16,%r12
	cmpq 144(%r13),%r12
	ja .LckD
	movq $stg_CAF_BLACKHOLE_info,-8(%r12)
	movq 160(%r13),%rax
	movq %rax,0(%r12)
	movq %r13,%rdi
	movq %rbx,%rsi
	leaq -8(%r12),%rdx
	subq $8,%rsp
	movl $0,%eax
	call newCAF
	addq $8,%rsp
	testq %rax,%rax
	je .LckE
.LckF:
	movq $stg_bh_upd_frame_info,-16(%rbp)
	leaq -8(%r12),%rax
	movq %rax,-8(%rbp)
	movl $Reader_zdfMonadTransReaderT1_closure+3,%ebx
	addq $-16,%rbp
	jmp *0(%rbp)
.LckD:
	movq $16,192(%r13)
.LckB:
	jmp *-16(%r13)
.LckE:
	jmp *(%rbx)
	.size Reader_zdfMonadTransReaderT_info, .-Reader_zdfMonadTransReaderT_info

[2 of 2] Compiling Eval2            ( Eval2.hs, Eval2.o )

==================== Tidy Core ====================
Result size = 76

Eval2.runEval2 :: Int
[GblId,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=IF_ARGS [] 10 110}]
Eval2.runEval2 = I# 0

Eval2.runEval1
  :: forall void_aoT.
     Eval2.Eval void_aoT
     -> State# RealWorld
     -> (# State# RealWorld, Int #)
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=IF_ARGS [0 0] 56 0}]
Eval2.runEval1 =
  \ (@ void_aoT)
    (m_alY :: Eval2.Eval void_aoT)
    (eta_B1 :: State# RealWorld) ->
    case newMutVar#
           @ Int @ RealWorld Eval2.runEval2 eta_B1
    of _ { (# s2#_ar5, var#_ar6 #) ->
    let {
      a_srx :: STRef RealWorld Int

      a_srx =
        STRef @ RealWorld @ Int var#_ar6 } in
    case (((m_alY `cast` ...) (a_srx `cast` ..., a_srx `cast` ...))
          `cast` ...)
           s2#_ar5
    of _ { (# new_s_XrW, _ #) ->
    readMutVar#
      @ RealWorld @ Int var#_ar6 new_s_XrW
    }
    }

Eval2.runEval
  :: forall void_alX.
     Eval2.Eval void_alX -> IO Int
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.runEval = Eval2.runEval1 `cast` ...

Eval2.ask3
  :: (IORef Int, IORef Int)
     -> State# RealWorld
     -> (# State# RealWorld, Eval2.Value #)
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask3 =
  \ (r_aau
       :: (IORef Int, IORef Int))
    (s_arq :: State# RealWorld) ->
    (# s_arq, case r_aau of _ { (x_aqA, ds1_aqB) -> x_aqA } #)

Eval2.ask1 :: Eval2.Eval Eval2.Value
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask1 = Eval2.ask3 `cast` ...

Eval2.ask4
  :: (IORef Int, IORef Int)
     -> State# RealWorld
     -> (# State# RealWorld, Eval2.Value #)
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask4 =
  \ (r_Xb4
       :: (IORef Int, IORef Int))
    (s_arq :: State# RealWorld) ->
    (# s_arq, case r_Xb4 of _ { (ds1_aqI, y_aqJ) -> y_aqJ } #)

Eval2.ask2 :: Eval2.Eval Eval2.Value
[GblId,
 Arity=2,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Eval2.ask2 = Eval2.ask4 `cast` ...

==================== Asm code ====================
.data
	.align 8
.align 1
.globl __stginit_Eval2
.type __stginit_Eval2, @object
__stginit_Eval2:
.data
	.align 8
.align 1
.globl Eval2_runEval2_closure
.type Eval2_runEval2_closure, @object
Eval2_runEval2_closure:
	.quad	ghczmprim_GHCziTypes_Izh_static_info
	.quad	0
.data
	.align 8
.align 1
.globl Eval2_runEval1_closure
.type Eval2_runEval1_closure, @object
Eval2_runEval1_closure:
	.quad	Eval2_runEval1_info
.text
	.align 8
	.quad	1
	.quad	32
ssH_info:
.LcsX:
	movq 8(%rbp),%rax
	movq 8(%rax),%rbx
	addq $16,%rbp
	jmp *0(%rbp)
	.size ssH_info, .-ssH_info
.text
	.align 8
	.quad	1
	.quad	32
ssG_info:
.Lct5:
	addq $40,%r12
	cmpq 144(%r13),%r12
	ja .Lct9
	movq $base_GHCziSTRef_STRef_con_info,-32(%r12)
	movq %rbx,-24(%r12)
	movq $ghczmprim_GHCziTuple_Z2T_con_info,-16(%r12)
	leaq -31(%r12),%rax
	movq %rax,-8(%r12)
	leaq -31(%r12),%rax
	movq %rax,0(%r12)
	movq 8(%rbp),%rax
	movq %rbx,8(%rbp)
	movq %rax,%rbx
	leaq -15(%r12),%r14
	movq $ssH_info,0(%rbp)
	jmp stg_ap_pv_fast
.Lct9:
	movq $40,192(%r13)
.Lct7:
	movq $254,64(%r13)
	jmp stg_gc_ut
	.size ssG_info, .-ssG_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_runEval1_info
.type Eval2_runEval1_info, @object
Eval2_runEval1_info:
.Lcti:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lctk
	movq %r14,-8(%rbp)
	movl $Eval2_runEval2_closure+1,%ebx
	movq $ssG_info,-16(%rbp)
	addq $-16,%rbp
	jmp stg_newMutVarzh
.Lctk:
	movl $Eval2_runEval1_closure,%ebx
	jmp *-8(%r13)
	.size Eval2_runEval1_info, .-Eval2_runEval1_info
.data
	.align 8
.align 1
.globl Eval2_runEval_closure
.type Eval2_runEval_closure, @object
Eval2_runEval_closure:
	.quad	Eval2_runEval_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_runEval_info
.type Eval2_runEval_info, @object
Eval2_runEval_info:
.Lctt:
	jmp Eval2_runEval1_info
	.size Eval2_runEval_info, .-Eval2_runEval_info
.data
	.align 8
.align 1
.globl Eval2_ask3_closure
.type Eval2_ask3_closure, @object
Eval2_ask3_closure:
	.quad	Eval2_ask3_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_ask3_info
.type Eval2_ask3_info, @object
Eval2_ask3_info:
.LctB:
	addq $24,%r12
	cmpq 144(%r13),%r12
	ja .LctG
	movq $stg_sel_0_upd_info,-16(%r12)
	movq %r14,0(%r12)
	leaq -16(%r12),%rbx
	jmp *0(%rbp)
.LctG:
	movq $24,192(%r13)
.LctE:
	movl $Eval2_ask3_closure,%ebx
	jmp *-8(%r13)
	.size Eval2_ask3_info, .-Eval2_ask3_info
.data
	.align 8
.align 1
.globl Eval2_ask1_closure
.type Eval2_ask1_closure, @object
Eval2_ask1_closure:
	.quad	Eval2_ask1_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_ask1_info
.type Eval2_ask1_info, @object
Eval2_ask1_info:
.LctO:
	jmp Eval2_ask3_info
	.size Eval2_ask1_info, .-Eval2_ask1_info
.data
	.align 8
.align 1
.globl Eval2_ask4_closure
.type Eval2_ask4_closure, @object
Eval2_ask4_closure:
	.quad	Eval2_ask4_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_ask4_info
.type Eval2_ask4_info, @object
Eval2_ask4_info:
.LctW:
	addq $24,%r12
	cmpq 144(%r13),%r12
	ja .Lcu1
	movq $stg_sel_1_upd_info,-16(%r12)
	movq %r14,0(%r12)
	leaq -16(%r12),%rbx
	jmp *0(%rbp)
.Lcu1:
	movq $24,192(%r13)
.LctZ:
	movl $Eval2_ask4_closure,%ebx
	jmp *-8(%r13)
	.size Eval2_ask4_info, .-Eval2_ask4_info
.data
	.align 8
.align 1
.globl Eval2_ask2_closure
.type Eval2_ask2_closure, @object
Eval2_ask2_closure:
	.quad	Eval2_ask2_info
.text
	.align 8
	.quad	8589934597
	.quad	0
	.quad	15
.globl Eval2_ask2_info
.type Eval2_ask2_info, @object
Eval2_ask2_info:
.Lcu9:
	jmp Eval2_ask4_info
	.size Eval2_ask2_info, .-Eval2_ask2_info


