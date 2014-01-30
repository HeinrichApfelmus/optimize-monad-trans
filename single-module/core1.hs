[1 of 1] Compiling Reader           ( reader.hs, reader.o )

==================== Tidy Core ====================
Result size = 188

Reader.ask1
  :: forall (m_aeq :: * -> *) r_aer.
     Monad m_aeq =>
     r_aer -> m_aeq r_aer
[GblId,
 Arity=1,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_aeq::* -> *)
                 (@ r_aer)
                 ($dMonad_aes [Occ=Once] :: Monad m_aeq) ->
                 return @ m_aeq $dMonad_aes @ r_aer}]
Reader.ask1 =
  \ (@ m_aeq::* -> *)
    (@ r_aer)
    ($dMonad_aes :: Monad m_aeq) ->
    return @ m_aeq $dMonad_aes @ r_aer

Reader.ask
  :: forall (m_abq :: * -> *) r_abr.
     Monad m_abq =>
     Reader.ReaderT r_abr m_abq r_abr
[GblId,
 Arity=1,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.ask1 `cast` ...}]
Reader.ask = Reader.ask1 `cast` ...

Reader.runReaderT1
  :: forall r_acj (m_ack :: * -> *) a_acl.
     Reader.ReaderT r_acj m_ack a_acl
     -> Reader.ReaderT r_acj m_ack a_acl
[GblId,
 Arity=1,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT1 =
  \ (@ r_acj)
    (@ m_ack::* -> *)
    (@ a_acl)
    (ds_dfX :: Reader.ReaderT r_acj m_ack a_acl) ->
    ds_dfX

Reader.runReaderT
  :: forall r_abj (m_abk :: * -> *) a_abl.
     Reader.ReaderT r_abj m_abk a_abl -> r_abj -> m_abk a_abl
[GblId[[RecSel]],
 Arity=1,

 Unf=Unf{Src=<vanilla>, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)}]
Reader.runReaderT = Reader.runReaderT1 `cast` ...

Reader.$fMonadReaderT1
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_afy. a_afy -> r_abM -> m_abL a_afy
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_abL::* -> *)
                 (@ r_abM)
                 ($dMonad_afh [Occ=Once] :: Monad m_abL)
                 (@ a_afy)
                 (a1_abD [Occ=Once] :: a_afy)
                 _ ->
                 return @ m_abL $dMonad_afh @ a_afy a1_abD}]
Reader.$fMonadReaderT1 =
  \ (@ m_abL::* -> *)
    (@ r_abM)
    ($dMonad_afh :: Monad m_abL)
    (@ a_afy)
    (a1_abD :: a_afy)
    _ ->
    return @ m_abL $dMonad_afh @ a_afy a1_abD

Reader.$fMonadReaderT_$creturn
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_aeu. a_aeu -> Reader.ReaderT r_abM m_abL a_aeu
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadReaderT1 `cast` ...}]
Reader.$fMonadReaderT_$creturn = Reader.$fMonadReaderT1 `cast` ...

Reader.$fMonadReaderT2
  :: forall (m_Xci :: * -> *) r_Xck.
     Monad m_Xci =>
     forall a_afk b_afl.
     Reader.ReaderT r_Xck m_Xci a_afk
     -> (a_afk -> Reader.ReaderT r_Xck m_Xci b_afl)
     -> r_Xck
     -> m_Xci b_afl
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ m_Xci::* -> *)
                 (@ r_Xck)
                 ($dMonad_XfQ [Occ=Once] :: Monad m_Xci)
                 (@ a_afk)
                 (@ b_afl)
                 (m_abz [Occ=Once] :: Reader.ReaderT r_Xck m_Xci a_afk)
                 (k_abA [Occ=OnceL!] :: a_afk -> Reader.ReaderT r_Xck m_Xci b_afl)
                 (r_abB :: r_Xck) ->
                 >>=
                   @ m_Xci
                   $dMonad_XfQ
                   @ a_afk
                   @ b_afl
                   ((m_abz `cast` ...) r_abB)
                   (\ (a1_abC [Occ=Once] :: a_afk) ->
                      ((k_abA a1_abC) `cast` ...) r_abB)}]
Reader.$fMonadReaderT2 =
  \ (@ m_Xci::* -> *)
    (@ r_Xck)
    ($dMonad_XfQ :: Monad m_Xci)
    (@ a_afk)
    (@ b_afl)
    (m_abz :: Reader.ReaderT r_Xck m_Xci a_afk)
    (k_abA :: a_afk -> Reader.ReaderT r_Xck m_Xci b_afl)
    (r_abB :: r_Xck) ->
    >>=
      @ m_Xci
      $dMonad_XfQ
      @ a_afk
      @ b_afl
      ((m_abz `cast` ...) r_abB)
      (\ (a1_abC :: a_afk) -> ((k_abA a1_abC) `cast` ...) r_abB)

Reader.$fMonadReaderT_$c>>=
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_ado b_adp.
     Reader.ReaderT r_abM m_abL a_ado
     -> (a_ado -> Reader.ReaderT r_abM m_abL b_adp)
     -> Reader.ReaderT r_abM m_abL b_adp
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadReaderT2 `cast` ...}]
Reader.$fMonadReaderT_$c>>= = Reader.$fMonadReaderT2 `cast` ...

Reader.$fMonadReaderT_$cfail
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_afU. String -> Reader.ReaderT r_abM m_abL a_afU
[GblId,
 Arity=2,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_Xcr::* -> *)
                 (@ r_Xct)
                 _
                 (@ a_agj)
                 (eta_B1 [Occ=Once] :: [Char]) ->
                 error @ (Reader.ReaderT r_Xct m_Xcr a_agj) eta_B1}]
Reader.$fMonadReaderT_$cfail =
  \ (@ m_Xcr::* -> *)
    (@ r_Xct)
    _
    (@ a_agj)
    (eta_B1 :: [Char]) ->
    error @ (Reader.ReaderT r_Xct m_Xcr a_agj) eta_B1

a_rgJ
  :: forall (m_Xcq :: * -> *) r_Xcs.
     Monad m_Xcq =>
     forall a_aeb b_aec.
     Reader.ReaderT r_Xcs m_Xcq a_aeb
     -> Reader.ReaderT r_Xcs m_Xcq b_aec -> r_Xcs -> m_Xcq b_aec

a_rgJ =
  \ (@ m_Xcq::* -> *)
    (@ r_Xcs)
    ($dMonad_XfY :: Monad m_Xcq)
    (@ a_aeb)
    (@ b_aec)
    (eta_B2 :: Reader.ReaderT r_Xcs m_Xcq a_aeb)
    (eta1_B1 :: Reader.ReaderT r_Xcs m_Xcq b_aec)
    (eta2_X2 :: r_Xcs) ->
    let {
      lvl1_sgE :: m_Xcq b_aec
      [LclId]
      lvl1_sgE = (eta1_B1 `cast` ...) eta2_X2 } in
    >>=
      @ m_Xcq
      $dMonad_XfY
      @ a_aeb
      @ b_aec
      ((eta_B2 `cast` ...) eta2_X2)
      (\ _ -> lvl1_sgE)

Reader.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_aeb b_aec.
     Reader.ReaderT r_abM m_abL a_aeb
     -> Reader.ReaderT r_abM m_abL b_aec
     -> Reader.ReaderT r_abM m_abL b_aec
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ m_Xd0::* -> *)
                 (@ r_Xd3)
                 ($dMonad_XgA [Occ=Once] :: Monad m_Xd0)
                 (@ a_agc)
                 (@ b_agd)
                 (m_age [Occ=Once] :: Reader.ReaderT r_Xd3 m_Xd0 a_agc)
                 (k_agf [Occ=OnceL] :: Reader.ReaderT r_Xd3 m_Xd0 b_agd) ->
                 Reader.$fMonadReaderT_$c>>=
                   @ m_Xd0 @ r_Xd3 $dMonad_XgA @ a_agc @ b_agd m_age (\ _ -> k_agf)}]
Reader.$fMonadReaderT_$c>> = a_rgJ `cast` ...

lvl_rgK
  :: forall (m_Xcp :: * -> *) r_Xcr a_agj.
     [Char] -> Reader.ReaderT r_Xcr m_Xcp a_agj

lvl_rgK =
  \ (@ m_Xcp::* -> *)
    (@ r_Xcr)
    (@ a_agj)
    (eta_B1 :: [Char]) ->
    error @ (Reader.ReaderT r_Xcr m_Xcp a_agj) eta_B1

Reader.$fMonadReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     Monad (Reader.ReaderT r_abM m_abL)
[GblId[DFunId],
 Arity=1,

 Unf=DFun(arity=3) D:Monad [Reader.$fMonadReaderT_$c>>=,
                                     Reader.$fMonadReaderT_$c>>, Reader.$fMonadReaderT_$creturn,
                                     Reader.$fMonadReaderT_$cfail]]
Reader.$fMonadReaderT =
  \ (@ m_Xcp::* -> *)
    (@ r_Xcr)
    ($dMonad_XfX :: Monad m_Xcp) ->
    D:Monad
      @ (Reader.ReaderT r_Xcr m_Xcp)
      ((Reader.$fMonadReaderT2 @ m_Xcp @ r_Xcr $dMonad_XfX) `cast` ...)
      (Reader.$fMonadReaderT_$c>> @ m_Xcp @ r_Xcr $dMonad_XfX)
      ((\ (@ a_afy) (a1_abD :: a_afy) _ ->
          return @ m_Xcp $dMonad_XfX @ a_afy a1_abD)
       `cast` ...)
      (lvl_rgK @ m_Xcp @ r_Xcr)

Reader.$fMonadIOReaderT1
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     forall a_afb. IO a_afb -> r_abK -> m_abJ a_afb
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_abJ::* -> *)
                 (@ r_abK)
                 ($dMonadIO_af5 [Occ=Once] :: Control.Monad.IO.Class.MonadIO m_abJ)
                 (@ a_afb)
                 (m_abE [Occ=Once] :: IO a_afb)
                 _ ->
                 Control.Monad.IO.Class.liftIO @ m_abJ $dMonadIO_af5 @ a_afb m_abE}]
Reader.$fMonadIOReaderT1 =
  \ (@ m_abJ::* -> *)
    (@ r_abK)
    ($dMonadIO_af5 :: Control.Monad.IO.Class.MonadIO m_abJ)
    (@ a_afb)
    (m_abE :: IO a_afb)
    _ ->
    Control.Monad.IO.Class.liftIO @ m_abJ $dMonadIO_af5 @ a_afb m_abE

Reader.$fMonadIOReaderT_$cliftIO
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     forall a_aem.
     IO a_aem -> Reader.ReaderT r_abK m_abJ a_aem
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadIOReaderT1 `cast` ...}]
Reader.$fMonadIOReaderT_$cliftIO =
  Reader.$fMonadIOReaderT1 `cast` ...

Reader.$fMonadIOReaderT_$c$p1MonadIO
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     Monad (Reader.ReaderT r_abK m_abJ)
[GblId,
 Arity=1,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ m_Xcw::* -> *)
                 (@ r_Xcy)
                 ($dMonadIO_XfU [Occ=Once]
                    :: Control.Monad.IO.Class.MonadIO m_Xcw) ->
                 Reader.$fMonadReaderT
                   @ m_Xcw
                   @ r_Xcy
                   (Control.Monad.IO.Class.$p1MonadIO @ m_Xcw $dMonadIO_XfU)}]
Reader.$fMonadIOReaderT_$c$p1MonadIO =
  \ (@ m_Xcw::* -> *)
    (@ r_Xcy)
    ($dMonadIO_XfU :: Control.Monad.IO.Class.MonadIO m_Xcw) ->
    Reader.$fMonadReaderT
      @ m_Xcw
      @ r_Xcy
      (Control.Monad.IO.Class.$p1MonadIO @ m_Xcw $dMonadIO_XfU)

Reader.$fMonadIOReaderT [InlPrag=[ALWAYS] CONLIKE]
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     Control.Monad.IO.Class.MonadIO (Reader.ReaderT r_abK m_abJ)
[GblId[DFunId],
 Arity=1,

 Unf=DFun(arity=3) Control.Monad.IO.Class.D:MonadIO [Reader.$fMonadIOReaderT_$c$p1MonadIO,
                                                     Reader.$fMonadIOReaderT_$cliftIO]]
Reader.$fMonadIOReaderT =
  \ (@ m_Xcx::* -> *)
    (@ r_Xcz)
    ($dMonadIO_XfV :: Control.Monad.IO.Class.MonadIO m_Xcx) ->
    Control.Monad.IO.Class.D:MonadIO
      @ (Reader.ReaderT r_Xcz m_Xcx)
      (Reader.$fMonadIOReaderT_$c$p1MonadIO
         @ m_Xcx @ r_Xcz $dMonadIO_XfV)
      ((\ (@ a_afb) (m_abE :: IO a_afb) _ ->
          Control.Monad.IO.Class.liftIO @ m_Xcx $dMonadIO_XfV @ a_afb m_abE)
       `cast` ...)

Reader.$fMonadTransReaderT1
  :: forall r_abH (m_af0 :: * -> *) a_af1.
     Monad m_af0 =>
     m_af0 a_af1 -> r_abH -> m_af0 a_af1
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_abH)
                 (@ m_af0::* -> *)
                 (@ a_af1)
                 _
                 (m_abI [Occ=Once] :: m_af0 a_af1)
                 _ ->
                 m_abI}]
Reader.$fMonadTransReaderT1 =
  \ (@ r_abH)
    (@ m_af0::* -> *)
    (@ a_af1)
    _
    (m_abI :: m_af0 a_af1)
    _ ->
    m_abI

Reader.$fMonadTransReaderT_$clift
  :: forall r_abH (m_aeB :: * -> *) a_aeC.
     Monad m_aeB =>
     m_aeB a_aeC -> Reader.ReaderT r_abH m_aeB a_aeC
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=0, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= Reader.$fMonadTransReaderT1 `cast` ...}]
Reader.$fMonadTransReaderT_$clift =
  Reader.$fMonadTransReaderT1 `cast` ...

Reader.$fMonadTransReaderT [InlPrag=INLINE (sat-args=0)]
  :: forall r_abH.
     Control.Monad.Trans.Class.MonadTrans (Reader.ReaderT r_abH)
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
	.quad	4294967301
	.quad	0
	.quad	15
.globl Reader_ask1_info
.type Reader_ask1_info, @object
Reader_ask1_info:
.Lcie:
	jmp base_GHCziBase_return_info
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
	.quad	4294967301
	.quad	0
	.quad	15
.globl Reader_ask_info
.type Reader_ask_info, @object
Reader_ask_info:
.Lcil:
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
.Lcis:
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
.Lciz:
	jmp Reader_runReaderT1_info
	.size Reader_runReaderT_info, .-Reader_runReaderT_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderT1_closure
.type Reader_zdfMonadReaderT1_closure, @object
Reader_zdfMonadReaderT1_closure:
	.quad	Reader_zdfMonadReaderT1_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderT1_info
.type Reader_zdfMonadReaderT1_info, @object
Reader_zdfMonadReaderT1_info:
.LciG:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LciJ
	movq %rsi,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	addq $-16,%rbp
	jmp base_GHCziBase_return_info
.LciJ:
	movl $Reader_zdfMonadReaderT1_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderT1_info, .-Reader_zdfMonadReaderT1_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderTzuzdcreturn_closure
.type Reader_zdfMonadReaderTzuzdcreturn_closure, @object
Reader_zdfMonadReaderTzuzdcreturn_closure:
	.quad	Reader_zdfMonadReaderTzuzdcreturn_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderTzuzdcreturn_info
.type Reader_zdfMonadReaderTzuzdcreturn_info, @object
Reader_zdfMonadReaderTzuzdcreturn_info:
.LciR:
	jmp Reader_zdfMonadReaderT1_info
	.size Reader_zdfMonadReaderTzuzdcreturn_info, .-Reader_zdfMonadReaderTzuzdcreturn_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadReaderT2_closure
.type Reader_zdfMonadReaderT2_closure, @object
Reader_zdfMonadReaderT2_closure:
	.quad	Reader_zdfMonadReaderT2_info
.text
	.align 8
	.quad	4294967301
	.quad	2
	.quad	12
si3_info:
.Lcj1:
	movq 7(%rbx),%rsi
	movq 15(%rbx),%rbx
	jmp stg_ap_pp_fast
	.size si3_info, .-si3_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderT2_info
.type Reader_zdfMonadReaderT2_info, @object
Reader_zdfMonadReaderT2_info:
.Lcj4:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcj6
	addq $56,%r12
	cmpq 144(%r13),%r12
	ja .Lcj8
	movq $si3_info,-48(%r12)
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
.Lcj8:
	movq $56,192(%r13)
.Lcj6:
	movl $Reader_zdfMonadReaderT2_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderT2_info, .-Reader_zdfMonadReaderT2_info
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
.Lcji:
	jmp Reader_zdfMonadReaderT2_info
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
.Lcjq:
	movq %rsi,%r14
	jmp base_GHCziErr_error_info
	.size Reader_zdfMonadReaderTzuzdcfail_info, .-Reader_zdfMonadReaderTzuzdcfail_info
.data
	.align 8
.align 1
rgJ_closure:
	.quad	rgJ_info
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
si5_info:
.LcjA:
	movq 7(%rbx),%rbx
	jmp stg_ap_0_fast
	.size si5_info, .-si5_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
rgJ_info:
.LcjD:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .LcjF
	addq $80,%r12
	cmpq 144(%r13),%r12
	ja .LcjH
	movq $stg_ap_2_upd_info,-72(%r12)
	movq %rdi,-56(%r12)
	movq %r8,-48(%r12)
	movq $si5_info,-40(%r12)
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
.LcjH:
	movq $80,192(%r13)
.LcjF:
	movl $rgJ_closure,%ebx
	jmp *-8(%r13)
	.size rgJ_info, .-rgJ_info
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
.LcjS:
	jmp rgJ_info
	.size Reader_zdfMonadReaderTzuzdczgzg_info, .-Reader_zdfMonadReaderTzuzdczgzg_info
.section .data
	.align 8
.align 1
rgK_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
rgK_closure:
	.quad	rgK_info
	.quad	0
.text
	.align 8
	.long	rgK_srt-(rgK_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
rgK_info:
.Lck0:
	jmp base_GHCziErr_error_info
	.size rgK_info, .-rgK_info
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
	.quad	8589934604
	.quad	1
	.quad	10
si0_info:
.Lckb:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcke
	movq %r14,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	movq 6(%rbx),%r14
	addq $-16,%rbp
	jmp base_GHCziBase_return_info
.Lcke:
	jmp *-8(%r13)
	.size si0_info, .-si0_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
si1_info:
.Lckk:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderTzuzdczgzg_info
	.size si1_info, .-si1_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
si2_info:
.Lckp:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderT2_info
	.size si2_info, .-si2_info
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
.Lcks:
	addq $88,%r12
	cmpq 144(%r13),%r12
	ja .Lckw
	movq $si0_info,-80(%r12)
	movq %r14,-72(%r12)
	movq $si1_info,-64(%r12)
	movq %r14,-56(%r12)
	movq $si2_info,-48(%r12)
	movq %r14,-40(%r12)
	movq $base_GHCziBase_DZCMonad_con_info,-32(%r12)
	leaq -45(%r12),%rax
	movq %rax,-24(%r12)
	leaq -61(%r12),%rax
	movq %rax,-16(%r12)
	leaq -78(%r12),%rax
	movq %rax,-8(%r12)
	movq $rgK_closure+1,0(%r12)
	leaq -31(%r12),%rbx
	jmp *0(%rbp)
.Lckw:
	movq $88,192(%r13)
.Lcku:
	movl $Reader_zdfMonadReaderT_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadReaderT_info, .-Reader_zdfMonadReaderT_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadIOReaderT1_closure
.type Reader_zdfMonadIOReaderT1_closure, @object
Reader_zdfMonadIOReaderT1_closure:
	.quad	Reader_zdfMonadIOReaderT1_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadIOReaderT1_info
.type Reader_zdfMonadIOReaderT1_info, @object
Reader_zdfMonadIOReaderT1_info:
.LckG:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LckJ
	movq %rsi,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_liftIO_info
.LckJ:
	movl $Reader_zdfMonadIOReaderT1_closure,%ebx
	jmp *-8(%r13)
	.size Reader_zdfMonadIOReaderT1_info, .-Reader_zdfMonadIOReaderT1_info
.data
	.align 8
.align 1
.globl Reader_zdfMonadIOReaderTzuzdcliftIO_closure
.type Reader_zdfMonadIOReaderTzuzdcliftIO_closure, @object
Reader_zdfMonadIOReaderTzuzdcliftIO_closure:
	.quad	Reader_zdfMonadIOReaderTzuzdcliftIO_info
.text
	.align 8
	.quad	12884901908
	.quad	0
	.quad	15
.globl Reader_zdfMonadIOReaderTzuzdcliftIO_info
.type Reader_zdfMonadIOReaderTzuzdcliftIO_info, @object
Reader_zdfMonadIOReaderTzuzdcliftIO_info:
.LckR:
	jmp Reader_zdfMonadIOReaderT1_info
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
shY_info:
.Lcl3:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcl5
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_zdp1MonadIO_info
.Lcl5:
	jmp *-16(%r13)
	.size shY_info, .-shY_info
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
.Lcl9:
	addq $24,%r12
	cmpq 144(%r13),%r12
	ja .Lcld
	movq $shY_info,-16(%r12)
	movq %r14,0(%r12)
	leaq -16(%r12),%r14
	jmp Reader_zdfMonadReaderT_info
.Lcld:
	movq $24,192(%r13)
.Lclb:
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
	.quad	8589934604
	.quad	1
	.quad	10
shW_info:
.Lclo:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lclr
	movq %r14,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	movq 6(%rbx),%r14
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_liftIO_info
.Lclr:
	jmp *-8(%r13)
	.size shW_info, .-shW_info
.text
	.align 8
	.long	Reader_zdfMonadIOReaderT_srt-(shX_info)+0
	.long	0
	.quad	1
	.quad	4294967313
shX_info:
.Lcly:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LclA
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
.LclA:
	jmp *-16(%r13)
	.size shX_info, .-shX_info
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
.LclE:
	addq $64,%r12
	cmpq 144(%r13),%r12
	ja .LclI
	movq $shW_info,-56(%r12)
	movq %r14,-48(%r12)
	movq $shX_info,-40(%r12)
	movq %r14,-24(%r12)
	movq $transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_DZCMonadIO_con_info,-16(%r12)
	leaq -40(%r12),%rax
	movq %rax,-8(%r12)
	leaq -54(%r12),%rax
	movq %rax,0(%r12)
	leaq -15(%r12),%rbx
	jmp *0(%rbp)
.LclI:
	movq $64,192(%r13)
.LclG:
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
.LclR:
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
.LclY:
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
.Lcm9:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcmb
	addq $16,%r12
	cmpq 144(%r13),%r12
	ja .Lcmd
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
	je .Lcme
.Lcmf:
	movq $stg_bh_upd_frame_info,-16(%rbp)
	leaq -8(%r12),%rax
	movq %rax,-8(%rbp)
	movl $Reader_zdfMonadTransReaderT1_closure+3,%ebx
	addq $-16,%rbp
	jmp *0(%rbp)
.Lcmd:
	movq $16,192(%r13)
.Lcmb:
	jmp *-16(%r13)
.Lcme:
	jmp *(%rbx)
	.size Reader_zdfMonadTransReaderT_info, .-Reader_zdfMonadTransReaderT_info


