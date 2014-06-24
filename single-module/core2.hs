[1 of 1] Compiling Reader           ( reader.hs, reader.o )

==================== Tidy Core ====================
Result size = 188

Reader.ask1
  :: forall (m_agQ :: * -> *) r_agR.
     Monad m_agQ =>
     r_agR -> m_agQ r_agR
[GblId,
 Arity=1,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=1, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_agQ::* -> *)
                 (@ r_agR)
                 ($dMonad_agS [Occ=Once] :: Monad m_agQ) ->
                 return @ m_agQ $dMonad_agS @ r_agR}]
Reader.ask1 =
  \ (@ m_agQ::* -> *)
    (@ r_agR)
    ($dMonad_agS :: Monad m_agQ) ->
    return @ m_agQ $dMonad_agS @ r_agR

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
    (ds_diu :: Reader.ReaderT r_acj m_ack a_acl) ->
    ds_diu

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
     forall a_ai6. a_ai6 -> r_abM -> m_abL a_ai6
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_abL::* -> *)
                 (@ r_abM)
                 ($dMonad_ahP [Occ=Once] :: Monad m_abL)
                 (@ a_ai6)
                 (a1_abD [Occ=Once] :: a_ai6)
                 _ ->
                 return @ m_abL $dMonad_ahP @ a_ai6 a1_abD}]
Reader.$fMonadReaderT1 =
  \ (@ m_abL::* -> *)
    (@ r_abM)
    ($dMonad_ahP :: Monad m_abL)
    (@ a_ai6)
    (a1_abD :: a_ai6)
    _ ->
    return @ m_abL $dMonad_ahP @ a_ai6 a1_abD

Reader.$fMonadReaderT_$creturn
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_agU. a_agU -> Reader.ReaderT r_abM m_abL a_agU
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
     forall a_ahS b_ahT.
     Reader.ReaderT r_Xck m_Xci a_ahS
     -> (a_ahS -> Reader.ReaderT r_Xck m_Xci b_ahT)
     -> r_Xck
     -> m_Xci b_ahT
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=4, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=False)
         Tmpl= \ (@ m_Xci::* -> *)
                 (@ r_Xck)
                 ($dMonad_Xio [Occ=Once] :: Monad m_Xci)
                 (@ a_ahS)
                 (@ b_ahT)
                 (m_abz [Occ=Once] :: Reader.ReaderT r_Xck m_Xci a_ahS)
                 (k_abA [Occ=OnceL!] :: a_ahS -> Reader.ReaderT r_Xck m_Xci b_ahT)
                 (r_abB :: r_Xck) ->
                 >>=
                   @ m_Xci
                   $dMonad_Xio
                   @ a_ahS
                   @ b_ahT
                   ((m_abz `cast` ...) r_abB)
                   (\ (a1_abC [Occ=Once] :: a_ahS) ->
                      ((k_abA a1_abC) `cast` ...) r_abB)}]
Reader.$fMonadReaderT2 =
  \ (@ m_Xci::* -> *)
    (@ r_Xck)
    ($dMonad_Xio :: Monad m_Xci)
    (@ a_ahS)
    (@ b_ahT)
    (m_abz :: Reader.ReaderT r_Xck m_Xci a_ahS)
    (k_abA :: a_ahS -> Reader.ReaderT r_Xck m_Xci b_ahT)
    (r_abB :: r_Xck) ->
    >>=
      @ m_Xci
      $dMonad_Xio
      @ a_ahS
      @ b_ahT
      ((m_abz `cast` ...) r_abB)
      (\ (a1_abC :: a_ahS) -> ((k_abA a1_abC) `cast` ...) r_abB)

Reader.$fMonadReaderT_$c>>=
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_afS b_afT.
     Reader.ReaderT r_abM m_abL a_afS
     -> (a_afS -> Reader.ReaderT r_abM m_abL b_afT)
     -> Reader.ReaderT r_abM m_abL b_afT
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
     forall a_air. String -> Reader.ReaderT r_abM m_abL a_air
[GblId,
 Arity=2,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=2, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_Xcr::* -> *)
                 (@ r_Xct)
                 _
                 (@ a_aiQ)
                 (eta_B1 [Occ=Once] :: [Char]) ->
                 error @ (Reader.ReaderT r_Xct m_Xcr a_aiQ) eta_B1}]
Reader.$fMonadReaderT_$cfail =
  \ (@ m_Xcr::* -> *)
    (@ r_Xct)
    _
    (@ a_aiQ)
    (eta_B1 :: [Char]) ->
    error @ (Reader.ReaderT r_Xct m_Xcr a_aiQ) eta_B1

a_rjf
  :: forall (m_Xcq :: * -> *) r_Xcs.
     Monad m_Xcq =>
     forall a_agB b_agC.
     Reader.ReaderT r_Xcs m_Xcq a_agB
     -> Reader.ReaderT r_Xcs m_Xcq b_agC -> r_Xcs -> m_Xcq b_agC

a_rjf =
  \ (@ m_Xcq::* -> *)
    (@ r_Xcs)
    ($dMonad_Xiw :: Monad m_Xcq)
    (@ a_agB)
    (@ b_agC)
    (eta_B2 :: Reader.ReaderT r_Xcs m_Xcq a_agB)
    (eta1_B1 :: Reader.ReaderT r_Xcs m_Xcq b_agC)
    (eta2_X2 :: r_Xcs) ->
    let {
      lvl1_sjb :: m_Xcq b_agC
      [LclId]
      lvl1_sjb = (eta1_B1 `cast` ...) eta2_X2 } in
    >>=
      @ m_Xcq
      $dMonad_Xiw
      @ a_agB
      @ b_agC
      ((eta_B2 `cast` ...) eta2_X2)
      (\ _ -> lvl1_sjb)

Reader.$fMonadReaderT_$c>> [InlPrag=INLINE (sat-args=2)]
  :: forall (m_abL :: * -> *) r_abM.
     Monad m_abL =>
     forall a_agB b_agC.
     Reader.ReaderT r_abM m_abL a_agB
     -> Reader.ReaderT r_abM m_abL b_agC
     -> Reader.ReaderT r_abM m_abL b_agC
[GblId,
 Arity=4,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=False,boring_ok=False)
         Tmpl= \ (@ m_Xd0::* -> *)
                 (@ r_Xd3)
                 ($dMonad_Xj8 [Occ=Once] :: Monad m_Xd0)
                 (@ a_aiJ)
                 (@ b_aiK)
                 (m_aiL [Occ=Once] :: Reader.ReaderT r_Xd3 m_Xd0 a_aiJ)
                 (k_aiM [Occ=OnceL] :: Reader.ReaderT r_Xd3 m_Xd0 b_aiK) ->
                 Reader.$fMonadReaderT_$c>>=
                   @ m_Xd0 @ r_Xd3 $dMonad_Xj8 @ a_aiJ @ b_aiK m_aiL (\ _ -> k_aiM)}]
Reader.$fMonadReaderT_$c>> = a_rjf `cast` ...

lvl_rjg
  :: forall (m_Xcp :: * -> *) r_Xcr a_aiQ.
     [Char] -> Reader.ReaderT r_Xcr m_Xcp a_aiQ

lvl_rjg =
  \ (@ m_Xcp::* -> *)
    (@ r_Xcr)
    (@ a_aiQ)
    (eta_B1 :: [Char]) ->
    error @ (Reader.ReaderT r_Xcr m_Xcp a_aiQ) eta_B1

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
    ($dMonad_Xiv :: Monad m_Xcp) ->
    D:Monad
      @ (Reader.ReaderT r_Xcr m_Xcp)
      ((Reader.$fMonadReaderT2 @ m_Xcp @ r_Xcr $dMonad_Xiv) `cast` ...)
      (Reader.$fMonadReaderT_$c>> @ m_Xcp @ r_Xcr $dMonad_Xiv)
      ((\ (@ a_ai6) (a1_abD :: a_ai6) _ ->
          return @ m_Xcp $dMonad_Xiv @ a_ai6 a1_abD)
       `cast` ...)
      (lvl_rjg @ m_Xcp @ r_Xcr)

Reader.$fMonadIOReaderT1
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     forall a_ahJ. IO a_ahJ -> r_abK -> m_abJ a_ahJ
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ m_abJ::* -> *)
                 (@ r_abK)
                 ($dMonadIO_ahD [Occ=Once] :: Control.Monad.IO.Class.MonadIO m_abJ)
                 (@ a_ahJ)
                 (m_abE [Occ=Once] :: IO a_ahJ)
                 _ ->
                 Control.Monad.IO.Class.liftIO @ m_abJ $dMonadIO_ahD @ a_ahJ m_abE}]
Reader.$fMonadIOReaderT1 =
  \ (@ m_abJ::* -> *)
    (@ r_abK)
    ($dMonadIO_ahD :: Control.Monad.IO.Class.MonadIO m_abJ)
    (@ a_ahJ)
    (m_abE :: IO a_ahJ)
    _ ->
    Control.Monad.IO.Class.liftIO @ m_abJ $dMonadIO_ahD @ a_ahJ m_abE

Reader.$fMonadIOReaderT_$cliftIO
  :: forall (m_abJ :: * -> *) r_abK.
     Control.Monad.IO.Class.MonadIO m_abJ =>
     forall a_agM.
     IO a_agM -> Reader.ReaderT r_abK m_abJ a_agM
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
                 ($dMonadIO_Xis [Occ=Once]
                    :: Control.Monad.IO.Class.MonadIO m_Xcw) ->
                 Reader.$fMonadReaderT
                   @ m_Xcw
                   @ r_Xcy
                   (Control.Monad.IO.Class.$p1MonadIO @ m_Xcw $dMonadIO_Xis)}]
Reader.$fMonadIOReaderT_$c$p1MonadIO =
  \ (@ m_Xcw::* -> *)
    (@ r_Xcy)
    ($dMonadIO_Xis :: Control.Monad.IO.Class.MonadIO m_Xcw) ->
    Reader.$fMonadReaderT
      @ m_Xcw
      @ r_Xcy
      (Control.Monad.IO.Class.$p1MonadIO @ m_Xcw $dMonadIO_Xis)

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
    ($dMonadIO_Xit :: Control.Monad.IO.Class.MonadIO m_Xcx) ->
    Control.Monad.IO.Class.D:MonadIO
      @ (Reader.ReaderT r_Xcz m_Xcx)
      (Reader.$fMonadIOReaderT_$c$p1MonadIO
         @ m_Xcx @ r_Xcz $dMonadIO_Xit)
      ((\ (@ a_ahJ) (m_abE :: IO a_ahJ) _ ->
          Control.Monad.IO.Class.liftIO @ m_Xcx $dMonadIO_Xit @ a_ahJ m_abE)
       `cast` ...)

Reader.$fMonadTransReaderT1
  :: forall r_abH (m_ahy :: * -> *) a_ahz.
     Monad m_ahy =>
     m_ahy a_ahz -> r_abH -> m_ahy a_ahz
[GblId,
 Arity=3,

 Unf=Unf{Src=InlineStable, TopLvl=True, Arity=3, Value=True,
         ConLike=True, Cheap=True, Expandable=True,
         Guidance=ALWAYS_IF(unsat_ok=True,boring_ok=True)
         Tmpl= \ (@ r_abH)
                 (@ m_ahy::* -> *)
                 (@ a_ahz)
                 _
                 (m_abI [Occ=Once] :: m_ahy a_ahz)
                 _ ->
                 m_abI}]
Reader.$fMonadTransReaderT1 =
  \ (@ r_abH)
    (@ m_ahy::* -> *)
    (@ a_ahz)
    _
    (m_abI :: m_ahy a_ahz)
    _ ->
    m_abI

Reader.$fMonadTransReaderT_$clift
  :: forall r_abH (m_ahw :: * -> *) a_ahx.
     Monad m_ahw =>
     m_ahw a_ahx -> Reader.ReaderT r_abH m_ahw a_ahx
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
.LckK:
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
.LckR:
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
.LckY:
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
.Lcl5:
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
.Lclc:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lclf
	movq %rsi,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	addq $-16,%rbp
	jmp base_GHCziBase_return_info
.Lclf:
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
.Lcln:
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
skz_info:
.Lclx:
	movq 7(%rbx),%rsi
	movq 15(%rbx),%rbx
	jmp stg_ap_pp_fast
	.size skz_info, .-skz_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
.globl Reader_zdfMonadReaderT2_info
.type Reader_zdfMonadReaderT2_info, @object
Reader_zdfMonadReaderT2_info:
.LclA:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .LclC
	addq $56,%r12
	cmpq 144(%r13),%r12
	ja .LclE
	movq $skz_info,-48(%r12)
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
.LclE:
	movq $56,192(%r13)
.LclC:
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
.LclO:
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
.LclW:
	movq %rsi,%r14
	jmp base_GHCziErr_error_info
	.size Reader_zdfMonadReaderTzuzdcfail_info, .-Reader_zdfMonadReaderTzuzdcfail_info
.data
	.align 8
.align 1
rjf_closure:
	.quad	rjf_info
.text
	.align 8
	.quad	4294967301
	.quad	1
	.quad	10
skB_info:
.Lcm6:
	movq 7(%rbx),%rbx
	jmp stg_ap_0_fast
	.size skB_info, .-skB_info
.text
	.align 8
	.quad	17179869205
	.quad	0
	.quad	15
rjf_info:
.Lcm9:
	leaq -24(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcmb
	addq $80,%r12
	cmpq 144(%r13),%r12
	ja .Lcmd
	movq $stg_ap_2_upd_info,-72(%r12)
	movq %rdi,-56(%r12)
	movq %r8,-48(%r12)
	movq $skB_info,-40(%r12)
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
.Lcmd:
	movq $80,192(%r13)
.Lcmb:
	movl $rjf_closure,%ebx
	jmp *-8(%r13)
	.size rjf_info, .-rjf_info
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
.Lcmo:
	jmp rjf_info
	.size Reader_zdfMonadReaderTzuzdczgzg_info, .-Reader_zdfMonadReaderTzuzdczgzg_info
.section .data
	.align 8
.align 1
rjg_srt:
	.quad	base_GHCziErr_error_closure
.data
	.align 8
.align 1
rjg_closure:
	.quad	rjg_info
	.quad	0
.text
	.align 8
	.long	rjg_srt-(rjg_info)+0
	.long	0
	.quad	4294967301
	.quad	0
	.quad	4294967311
rjg_info:
.Lcmw:
	jmp base_GHCziErr_error_info
	.size rjg_info, .-rjg_info
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
skw_info:
.LcmH:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcmK
	movq %r14,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	movq 6(%rbx),%r14
	addq $-16,%rbp
	jmp base_GHCziBase_return_info
.LcmK:
	jmp *-8(%r13)
	.size skw_info, .-skw_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
skx_info:
.LcmQ:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderTzuzdczgzg_info
	.size skx_info, .-skx_info
.text
	.align 8
	.quad	12884901908
	.quad	1
	.quad	10
sky_info:
.LcmV:
	movq %rdi,%r8
	movq %rsi,%rdi
	movq %r14,%rsi
	movq 5(%rbx),%r14
	jmp Reader_zdfMonadReaderT2_info
	.size sky_info, .-sky_info
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
.LcmY:
	addq $88,%r12
	cmpq 144(%r13),%r12
	ja .Lcn2
	movq $skw_info,-80(%r12)
	movq %r14,-72(%r12)
	movq $skx_info,-64(%r12)
	movq %r14,-56(%r12)
	movq $sky_info,-48(%r12)
	movq %r14,-40(%r12)
	movq $base_GHCziBase_DZCMonad_con_info,-32(%r12)
	leaq -45(%r12),%rax
	movq %rax,-24(%r12)
	leaq -61(%r12),%rax
	movq %rax,-16(%r12)
	leaq -78(%r12),%rax
	movq %rax,-8(%r12)
	movq $rjg_closure+1,0(%r12)
	leaq -31(%r12),%rbx
	jmp *0(%rbp)
.Lcn2:
	movq $88,192(%r13)
.Lcn0:
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
.Lcnc:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lcnf
	movq %rsi,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_liftIO_info
.Lcnf:
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
.Lcnn:
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
sku_info:
.Lcnz:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcnB
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_zdp1MonadIO_info
.LcnB:
	jmp *-16(%r13)
	.size sku_info, .-sku_info
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
.LcnF:
	addq $24,%r12
	cmpq 144(%r13),%r12
	ja .LcnJ
	movq $sku_info,-16(%r12)
	movq %r14,0(%r12)
	leaq -16(%r12),%r14
	jmp Reader_zdfMonadReaderT_info
.LcnJ:
	movq $24,192(%r13)
.LcnH:
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
sks_info:
.LcnU:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcnX
	movq %r14,-8(%rbp)
	movq $stg_ap_p_info,-16(%rbp)
	movq 6(%rbx),%r14
	addq $-16,%rbp
	jmp transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_liftIO_info
.LcnX:
	jmp *-8(%r13)
	.size sks_info, .-sks_info
.text
	.align 8
	.long	Reader_zdfMonadIOReaderT_srt-(skt_info)+0
	.long	0
	.quad	1
	.quad	4294967313
skt_info:
.Lco4:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .Lco6
	movq $stg_upd_frame_info,-16(%rbp)
	movq %rbx,-8(%rbp)
	movq 16(%rbx),%r14
	addq $-16,%rbp
	jmp Reader_zdfMonadIOReaderTzuzdczdp1MonadIO_info
.Lco6:
	jmp *-16(%r13)
	.size skt_info, .-skt_info
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
.Lcoa:
	addq $64,%r12
	cmpq 144(%r13),%r12
	ja .Lcoe
	movq $sks_info,-56(%r12)
	movq %r14,-48(%r12)
	movq $skt_info,-40(%r12)
	movq %r14,-24(%r12)
	movq $transformerszm0zi3zi0zi0_ControlziMonadziIOziClass_DZCMonadIO_con_info,-16(%r12)
	leaq -40(%r12),%rax
	movq %rax,-8(%r12)
	leaq -54(%r12),%rax
	movq %rax,0(%r12)
	leaq -15(%r12),%rbx
	jmp *0(%rbp)
.Lcoe:
	movq $64,192(%r13)
.Lcoc:
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
.Lcon:
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
.Lcou:
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
.LcoF:
	leaq -16(%rbp),%rax
	cmpq %r15,%rax
	jb .LcoH
	addq $16,%r12
	cmpq 144(%r13),%r12
	ja .LcoJ
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
	je .LcoK
.LcoL:
	movq $stg_bh_upd_frame_info,-16(%rbp)
	leaq -8(%r12),%rax
	movq %rax,-8(%rbp)
	movl $Reader_zdfMonadTransReaderT1_closure+3,%ebx
	addq $-16,%rbp
	jmp *0(%rbp)
.LcoJ:
	movq $16,192(%r13)
.LcoH:
	jmp *-16(%r13)
.LcoK:
	jmp *(%rbx)
	.size Reader_zdfMonadTransReaderT_info, .-Reader_zdfMonadTransReaderT_info


